use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, OnceLock};

use ndarray::{Axis, IxDyn};
use ort::session::builder::GraphOptimizationLevel;
use ort::session::Session;
use serde::Deserialize;

use super::features::Features;
use super::scorer::Scorer;
use crate::ort_utils::ensure_ort_initialized;

// The ScoringModel uses ort to load an onnx model and uses it to score feature vectors.
pub struct ScoringModel {
    // The ONNX model.
    session: Arc<Session>,

    // The feature names expected by the model input, in order.
    feature_names: Vec<String>,
}

static SCORING_SESSION: OnceLock<Arc<Session>> = OnceLock::new();
static EXTERNAL_SCORING_SESSIONS: OnceLock<Mutex<HashMap<PathBuf, Arc<Session>>>> = OnceLock::new();

pub const EMBEDDED_MODEL_POLICY: &str = "model-20260611-e50-h512-l3";
const MODEL_BYTES: &[u8] = include_bytes!("../../files/models/model-20260611-e50-h512-l3.onnx");
const MODEL_FEATURE_CONTRACT_JSON: &str =
    include_str!("../../files/models/model-20260611-e50-h512-l3.features.json");
const FEATURE_CONTRACT_SCHEMA: &str = "acorn-scorer-feature-contract-v1";

#[derive(Deserialize)]
struct FeatureContract {
    schema: String,
    input_features: Vec<String>,
}

fn make_session(bytes: &[u8]) -> Result<Arc<Session>, Box<dyn Error>> {
    ensure_ort_initialized()?;

    let session = Session::builder()?
        .with_intra_threads(1)?
        .with_inter_threads(1)?
        .with_optimization_level(GraphOptimizationLevel::Level3)?
        .commit_from_memory(bytes)?;
    Ok(Arc::new(session))
}

fn cached_external_session(path: &Path, bytes: &[u8]) -> Result<Arc<Session>, Box<dyn Error>> {
    let key = fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
    let sessions = EXTERNAL_SCORING_SESSIONS.get_or_init(|| Mutex::new(HashMap::new()));

    if let Some(session) = sessions.lock().unwrap().get(&key) {
        return Ok(Arc::clone(session));
    }

    let session = make_session(bytes)?;
    let mut sessions = sessions.lock().unwrap();
    let session = sessions.entry(key).or_insert(session);
    Ok(Arc::clone(session))
}

fn parse_feature_contract(source: &str, json: &str) -> Result<Vec<String>, Box<dyn Error>> {
    let contract: FeatureContract = serde_json::from_str(&json)?;
    if contract.schema != FEATURE_CONTRACT_SCHEMA {
        return Err(format!(
            "unsupported feature contract schema '{}' in {}",
            contract.schema, source
        )
        .into());
    }
    if contract.input_features.is_empty() {
        return Err(format!("feature contract is empty: {}", source).into());
    }

    let mut seen = HashSet::new();
    let probe = Features::default();
    for name in &contract.input_features {
        if !seen.insert(name.as_str()) {
            return Err(format!("duplicate feature name '{}' in {}", name, source).into());
        }
        if probe.feature_value(name).is_none() {
            return Err(format!("unknown feature name '{}' in {}", name, source).into());
        }
    }

    Ok(contract.input_features)
}

fn load_feature_contract(path: &Path) -> Result<Vec<String>, Box<dyn Error>> {
    let json = fs::read_to_string(path)?;
    parse_feature_contract(&path.display().to_string(), &json)
}

impl ScoringModel {
    // Loads the hardcoded model.
    pub fn load() -> Result<Self, Box<dyn Error>> {
        let session = SCORING_SESSION
            .get_or_init(|| make_session(MODEL_BYTES).expect("Failed to initialize ORT session"));
        let feature_names =
            parse_feature_contract(EMBEDDED_MODEL_POLICY, MODEL_FEATURE_CONTRACT_JSON)?;
        Ok(ScoringModel {
            session: Arc::clone(session),
            feature_names,
        })
    }

    pub fn feature_contract_path(model_path: &Path) -> PathBuf {
        model_path.with_extension("features.json")
    }

    // Loads an ONNX model from disk, using the adjacent *.features.json contract
    // to decide which feature columns to feed the model.
    pub fn load_from_path(path: &Path) -> Result<Self, Box<dyn Error>> {
        let bytes = fs::read(path)?;
        let feature_names = load_feature_contract(&Self::feature_contract_path(path))?;
        let session = cached_external_session(path, &bytes)?;
        Ok(ScoringModel {
            session,
            feature_names,
        })
    }
}

impl Scorer for ScoringModel {
    // This assumes that the model is calculating a probability of the positive class,
    // where the positive class is a step that was actually taken in a proof.
    // There's a lot of unwrapping - it would be nice to handle errors more gracefully.
    fn score(&self, features: &Features) -> Result<f32, Box<dyn Error>> {
        let array = features
            .to_array_for_names(&self.feature_names)
            .insert_axis(Axis(0));
        let inputs = ort::inputs![array]?;
        let outputs = self.session.run(inputs)?;
        let extracted = outputs[0].try_extract_tensor::<f32>()?;
        let ix = IxDyn(&[0, 0]);
        if let Some(score) = extracted.get(ix) {
            Ok(*score)
        } else {
            Err("No score at [0, 0]. Maybe the model is the wrong shape?".into())
        }
    }

    fn score_batch(&self, features: &[Features]) -> Result<Vec<f32>, Box<dyn Error>> {
        let array = Features::to_array2_for_names(features, &self.feature_names);
        let inputs = ort::inputs![array]?;
        let outputs = self.session.run(inputs)?;
        let extracted = outputs[0].try_extract_tensor::<f32>()?;
        let scores: Vec<f32> = extracted.iter().copied().collect();
        Ok(scores)
    }
}

#[cfg(test)]
mod tests {
    use crate::kernel::kernel_context::KernelContext;
    use crate::kernel::proof_step::ProofStep;
    use std::fs;

    use super::*;

    #[test]
    fn test_feature_contract_path() {
        let path = Path::new("tmp/models/scorer.onnx");
        assert_eq!(
            ScoringModel::feature_contract_path(path),
            PathBuf::from("tmp/models/scorer.features.json")
        );
    }

    #[test]
    fn test_load_feature_contract_validates_names() {
        let temp = tempfile::TempDir::new().unwrap();
        let good_path = temp.path().join("good.features.json");
        fs::write(
            &good_path,
            r#"{"schema":"acorn-scorer-feature-contract-v1","input_features":["atom_count","depth"]}"#,
        )
        .unwrap();
        assert_eq!(
            load_feature_contract(&good_path).unwrap(),
            vec!["atom_count".to_string(), "depth".to_string()]
        );

        let bad_path = temp.path().join("bad.features.json");
        fs::write(
            &bad_path,
            r#"{"schema":"acorn-scorer-feature-contract-v1","input_features":["not_a_feature"]}"#,
        )
        .unwrap();
        let error = load_feature_contract(&bad_path).unwrap_err().to_string();
        assert!(error.contains("unknown feature name"));
    }

    #[test]
    fn test_embedded_feature_contract_uses_catalog_features() {
        let feature_names =
            parse_feature_contract(EMBEDDED_MODEL_POLICY, MODEL_FEATURE_CONTRACT_JSON).unwrap();
        assert_eq!(feature_names, Features::catalog_feature_names());
    }

    #[test]
    fn test_ort_model_score() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "Bool -> Bool")
            .parse_constants(&["c2", "c3"], "Bool");
        let clause = kctx.parse_clause("g0(c3) = c2", &[]);
        let step = ProofStep::mock_from_clause(clause);
        let features = Features::new(&step);

        let scoring_model = ScoringModel::load().unwrap();
        let ort_score = scoring_model.score(&features).unwrap();
        assert!(ort_score.is_finite());
    }

    #[test]
    fn test_ort_model_batch_score() {
        let mut kctx = KernelContext::new();
        kctx.parse_constant("g0", "(Bool, Bool) -> Bool")
            .parse_constants(&["c1", "c2"], "Bool");

        let clause1 = kctx.parse_clause("g0(c1, c1) = c2", &[]);
        let clause2 = kctx.parse_clause("g0(c1, c1) = g0(c2, c2)", &[]);
        let step1 = ProofStep::mock_from_clause(clause1);
        let step2 = ProofStep::mock_from_clause(clause2);
        let features1 = Features::new(&step1);
        let features2 = Features::new(&step2);
        let scoring_model = ScoringModel::load().unwrap();

        let score1 = scoring_model.score(&features1).unwrap();
        let score2 = scoring_model.score(&features2).unwrap();

        // The scores should be different, even up to floating point error
        assert!((score1 - score2).abs() > 1e-6);

        // Recalculate the scores in a batch
        let scores = scoring_model.score_batch(&[features1, features2]).unwrap();
        assert_eq!(scores.len(), 2);
        assert!((scores[0] - score1).abs() < 1e-6);
        assert!((scores[1] - score2).abs() < 1e-6);
    }
}

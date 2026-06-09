use std::collections::HashSet;
use std::fs::{self, File};
use std::io::{self, BufWriter, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use serde::Serialize;

use crate::kernel::proof_step::{ProofStep, ShallowStatus, Truthiness};
use crate::prover::features::Features;
use crate::prover::score::Score;
use crate::prover::Outcome;

pub const TRACE_SCHEMA: &str = "acorn-activated-step-trace-v2";
pub const TRACE_FEATURE_VECTOR: [&str; 9] = [
    "is_contradiction",
    "atom_count",
    "is_counterfactual",
    "is_hypothetical",
    "is_factual",
    "is_assumption",
    "is_negated_goal",
    "proof_size",
    "depth",
];

#[derive(Clone, Debug, Serialize)]
pub struct TraceMetadata {
    pub schema: &'static str,
    pub feature_vector: &'static [&'static str],
}

#[derive(Clone, Debug)]
struct TraceActivatedStep {
    activation_index: usize,
    passive_id: usize,
    active_id: Option<usize>,
    queue_score: f32,
    queue_contradiction: bool,
    queue_shallow_status: String,
    queue_is_shallow: bool,
    rule: String,
    truthiness: String,
    feature_vector: Vec<f32>,
}

impl TraceActivatedStep {
    fn new(
        activation_index: usize,
        passive_id: usize,
        active_id: Option<usize>,
        score: &Score,
        step: &ProofStep,
    ) -> Self {
        let features = Features::new(step);
        Self {
            activation_index,
            passive_id,
            active_id,
            queue_score: score.raw_score(),
            queue_contradiction: score.prioritizes_contradiction(),
            queue_shallow_status: shallow_status_name(score.ordered_shallow_status()).to_string(),
            queue_is_shallow: score.is_shallow(),
            rule: step.rule.name().to_string(),
            truthiness: truthiness_name(step.truthiness).to_string(),
            feature_vector: features.to_floats().to_vec(),
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct SearchTrace {
    activated_steps: Vec<TraceActivatedStep>,
}

impl SearchTrace {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn record_activation(
        &mut self,
        passive_id: usize,
        active_id: Option<usize>,
        score: &Score,
        step: &ProofStep,
    ) {
        self.activated_steps.push(TraceActivatedStep::new(
            self.activated_steps.len(),
            passive_id,
            active_id,
            score,
            step,
        ));
    }

    pub fn records(
        &self,
        meta: TraceSearchMeta,
        outcome: Outcome,
        useful_active_ids: &HashSet<usize>,
    ) -> Vec<TraceActivatedStepRecord> {
        let outcome = outcome.to_string();
        self.activated_steps
            .iter()
            .map(|step| {
                let used_in_final_proof = step
                    .active_id
                    .is_some_and(|active_id| useful_active_ids.contains(&active_id))
                    || step.active_id.is_none();
                TraceActivatedStepRecord {
                    schema: TRACE_SCHEMA,
                    search: meta.clone(),
                    outcome: outcome.clone(),
                    activation_index: step.activation_index,
                    passive_id: step.passive_id,
                    active_id: step.active_id,
                    used_in_final_proof,
                    queue_score: step.queue_score,
                    queue_contradiction: step.queue_contradiction,
                    queue_shallow_status: step.queue_shallow_status.clone(),
                    queue_is_shallow: step.queue_is_shallow,
                    rule: step.rule.clone(),
                    truthiness: step.truthiness.clone(),
                    feature_vector: step.feature_vector.clone(),
                }
            })
            .collect()
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct TraceSearchMeta {
    pub module: String,
    pub goal: String,
    pub goal_first_line: u32,
    pub goal_last_line: u32,
    pub skip: Option<usize>,
    pub policy: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct TraceActivatedStepRecord {
    pub schema: &'static str,
    #[serde(flatten)]
    pub search: TraceSearchMeta,
    pub outcome: String,
    pub activation_index: usize,
    pub passive_id: usize,
    pub active_id: Option<usize>,
    pub used_in_final_proof: bool,
    pub queue_score: f32,
    pub queue_contradiction: bool,
    pub queue_shallow_status: String,
    pub queue_is_shallow: bool,
    pub rule: String,
    pub truthiness: String,
    pub feature_vector: Vec<f32>,
}

#[derive(Clone)]
pub struct SearchTraceWriter {
    inner: Arc<Mutex<BufWriter<File>>>,
}

impl SearchTraceWriter {
    pub fn create(path: &Path) -> io::Result<Self> {
        if let Some(parent) = path.parent() {
            if !parent.as_os_str().is_empty() {
                fs::create_dir_all(parent)?;
            }
        }
        write_metadata_file(&trace_metadata_path(path))?;
        let file = File::create(path)?;
        Ok(Self {
            inner: Arc::new(Mutex::new(BufWriter::new(file))),
        })
    }

    pub fn write_records(&self, records: &[TraceActivatedStepRecord]) -> io::Result<usize> {
        if records.is_empty() {
            return Ok(0);
        }
        let mut writer = self.inner.lock().expect("search trace writer poisoned");
        for record in records {
            serde_json::to_writer(&mut *writer, record)?;
            writer.write_all(b"\n")?;
        }
        Ok(records.len())
    }

    pub fn flush(&self) -> io::Result<()> {
        self.inner
            .lock()
            .expect("search trace writer poisoned")
            .flush()
    }
}

fn write_metadata_file(path: &Path) -> io::Result<()> {
    let file = File::create(path)?;
    serde_json::to_writer_pretty(
        file,
        &TraceMetadata {
            schema: TRACE_SCHEMA,
            feature_vector: &TRACE_FEATURE_VECTOR,
        },
    )
    .map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
    Ok(())
}

pub fn trace_metadata_path(trace_path: &Path) -> PathBuf {
    if trace_path
        .extension()
        .is_some_and(|extension| extension == "jsonl")
    {
        if let Some(stem) = trace_path.file_stem() {
            let mut file_name = stem.to_os_string();
            file_name.push(".meta.json");
            return trace_path.with_file_name(file_name);
        }
    }
    trace_path.with_extension("meta.json")
}

pub fn shallow_status_name(status: ShallowStatus) -> &'static str {
    match status {
        ShallowStatus::Deep => "deep",
        ShallowStatus::Spent => "spent",
        ShallowStatus::Unspent => "unspent",
        ShallowStatus::Contradiction => "contradiction",
    }
}

pub fn truthiness_name(truthiness: Truthiness) -> &'static str {
    match truthiness {
        Truthiness::Factual => "factual",
        Truthiness::Hypothetical => "hypothetical",
        Truthiness::Counterfactual => "counterfactual",
    }
}

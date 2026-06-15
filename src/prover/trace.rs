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
            feature_vector: features.to_catalog_floats(),
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
        useful_active_ids: Option<&HashSet<usize>>,
    ) -> Vec<TraceActivatedStepRecord> {
        let outcome = outcome.to_string();
        self.activated_steps
            .iter()
            .map(|step| {
                let used_in_final_proof = useful_active_ids.is_some_and(|ids| {
                    step.active_id
                        .is_some_and(|active_id| ids.contains(&active_id))
                        || step.active_id.is_none()
                });
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
    pub goal_bucket: u8,
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
    inner: Arc<Mutex<TraceWriterState>>,
}

impl SearchTraceWriter {
    pub fn create(path: &Path) -> io::Result<Self> {
        Self::create_with_shard_rows(path, None)
    }

    pub fn create_with_shard_rows(path: &Path, shard_rows: Option<usize>) -> io::Result<Self> {
        validate_trace_path(path)?;
        if shard_rows == Some(0) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "trace shard rows must be positive",
            ));
        }
        Ok(Self {
            inner: Arc::new(Mutex::new(TraceWriterState::new(path, shard_rows)?)),
        })
    }

    pub fn write_records(&self, records: &[TraceActivatedStepRecord]) -> io::Result<usize> {
        if records.is_empty() {
            return Ok(0);
        }
        let mut writer = self.inner.lock().expect("search trace writer poisoned");
        for record in records {
            writer.write_record(record)?;
        }
        Ok(records.len())
    }

    pub fn flush(&self) -> io::Result<()> {
        let mut writer = self.inner.lock().expect("search trace writer poisoned");
        writer.finish()
    }
}

struct TraceWriterState {
    base_path: PathBuf,
    shard_rows: Option<usize>,
    shard_index: usize,
    records_in_shard: usize,
    output: TraceOutput,
}

impl TraceWriterState {
    fn new(path: &Path, shard_rows: Option<usize>) -> io::Result<Self> {
        let output_path = if shard_rows.is_some() {
            trace_shard_path(path, 0)
        } else {
            path.to_path_buf()
        };
        Ok(Self {
            base_path: path.to_path_buf(),
            shard_rows,
            shard_index: 0,
            records_in_shard: 0,
            output: open_trace_output(&output_path)?,
        })
    }

    fn write_record(&mut self, record: &TraceActivatedStepRecord) -> io::Result<()> {
        self.rotate_if_needed()?;
        serde_json::to_writer(&mut self.output, record)?;
        self.output.write_all(b"\n")?;
        self.records_in_shard += 1;
        Ok(())
    }

    fn rotate_if_needed(&mut self) -> io::Result<()> {
        let Some(shard_rows) = self.shard_rows else {
            return Ok(());
        };
        if self.records_in_shard < shard_rows {
            return Ok(());
        }
        self.output.finish()?;
        self.shard_index += 1;
        self.records_in_shard = 0;
        let output_path = trace_shard_path(&self.base_path, self.shard_index);
        self.output = open_trace_output(&output_path)?;
        Ok(())
    }

    fn finish(&mut self) -> io::Result<()> {
        self.output.finish()
    }
}

enum TraceOutput {
    Zstd(Option<zstd::stream::write::Encoder<'static, BufWriter<File>>>),
}

impl TraceOutput {
    fn new(file: File) -> Self {
        let writer = BufWriter::new(file);
        Self::Zstd(Some(
            zstd::stream::write::Encoder::new(writer, 3).expect("zstd encoder should initialize"),
        ))
    }

    fn finish(&mut self) -> io::Result<()> {
        match self {
            Self::Zstd(writer) => {
                if let Some(writer) = writer.take() {
                    let mut inner = writer.finish()?;
                    inner.flush()
                } else {
                    Ok(())
                }
            }
        }
    }
}

impl Write for TraceOutput {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        match self {
            Self::Zstd(writer) => writer
                .as_mut()
                .expect("cannot write after zstd trace output finished")
                .write(buf),
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        match self {
            Self::Zstd(writer) => writer.as_mut().map_or(Ok(()), |writer| writer.flush()),
        }
    }
}

fn open_trace_output(path: &Path) -> io::Result<TraceOutput> {
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent)?;
        }
    }
    write_metadata_file(&trace_metadata_path(path))?;
    let file = File::create(path)?;
    Ok(TraceOutput::new(file))
}

pub fn trace_shard_path(trace_path: &Path, shard_index: usize) -> PathBuf {
    if let Some(file_name) = trace_path.file_name().and_then(|name| name.to_str()) {
        if let Some(base) = file_name.strip_suffix(".jsonl.zst") {
            return trace_path.with_file_name(format!("{base}-{shard_index:06}.jsonl.zst"));
        }
    }
    trace_path.with_file_name(format!("trace-{shard_index:06}.jsonl.zst"))
}

fn validate_trace_path(path: &Path) -> io::Result<()> {
    if path
        .file_name()
        .and_then(|name| name.to_str())
        .is_some_and(|name| name.ends_with(".jsonl.zst"))
    {
        Ok(())
    } else {
        Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "trace path must end in .jsonl.zst",
        ))
    }
}

fn write_metadata_file(path: &Path) -> io::Result<()> {
    let file = File::create(path)?;
    serde_json::to_writer_pretty(
        file,
        &TraceMetadata {
            schema: TRACE_SCHEMA,
            feature_vector: Features::catalog_feature_names(),
        },
    )
    .map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
    Ok(())
}

pub fn trace_metadata_path(trace_path: &Path) -> PathBuf {
    if let Some(file_name) = trace_path.file_name().and_then(|name| name.to_str()) {
        if let Some(base) = file_name.strip_suffix(".jsonl.zst") {
            return trace_path.with_file_name(format!("{}.meta.json", base));
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

#[cfg(test)]
mod tests {
    use std::fs::File;
    use std::io::Read;

    use tempfile::TempDir;

    use super::*;

    fn record(index: usize) -> TraceActivatedStepRecord {
        TraceActivatedStepRecord {
            schema: TRACE_SCHEMA,
            search: TraceSearchMeta {
                module: "m".to_string(),
                goal: "g".to_string(),
                goal_bucket: 0,
                goal_first_line: 1,
                goal_last_line: 1,
                skip: Some(0),
                policy: "model-20260611-e50-h512-l3".to_string(),
            },
            outcome: "success".to_string(),
            activation_index: index,
            passive_id: index,
            active_id: Some(index),
            used_in_final_proof: index == 0,
            queue_score: 0.0,
            queue_contradiction: false,
            queue_shallow_status: "deep".to_string(),
            queue_is_shallow: false,
            rule: "assumption".to_string(),
            truthiness: "factual".to_string(),
            feature_vector: vec![1.0, 2.0],
        }
    }

    fn read_zstd_lines(path: &Path) -> Vec<String> {
        let file = File::open(path).unwrap();
        let mut text = String::new();
        zstd::stream::read::Decoder::new(file)
            .unwrap()
            .read_to_string(&mut text)
            .unwrap();
        text.lines().map(|line| line.to_string()).collect()
    }

    #[test]
    fn trace_writer_rejects_non_zstd_paths() {
        let temp = TempDir::new().unwrap();
        let path = temp.path().join("trace.jsonl");
        let error = match SearchTraceWriter::create(&path) {
            Ok(_) => panic!("non-zstd trace path should be rejected"),
            Err(error) => error,
        };
        assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
    }

    #[test]
    fn trace_writer_rotates_zstd_shards() {
        let temp = TempDir::new().unwrap();
        let path = temp.path().join("trace.jsonl.zst");
        let writer = SearchTraceWriter::create_with_shard_rows(&path, Some(2)).unwrap();
        writer
            .write_records(&[record(0), record(1), record(2), record(3), record(4)])
            .unwrap();
        writer.flush().unwrap();

        let first = temp.path().join("trace-000000.jsonl.zst");
        let second = temp.path().join("trace-000001.jsonl.zst");
        let third = temp.path().join("trace-000002.jsonl.zst");
        assert_eq!(read_zstd_lines(&first).len(), 2);
        assert_eq!(read_zstd_lines(&second).len(), 2);
        assert_eq!(read_zstd_lines(&third).len(), 1);
        assert!(trace_metadata_path(&first).exists());
        assert!(trace_metadata_path(&second).exists());
        assert!(trace_metadata_path(&third).exists());
        assert!(!path.exists());
    }
}

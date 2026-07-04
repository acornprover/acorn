use super::*;
use crate::module::LoadState;
use crate::module::ModuleId;
use crate::processor::Processor;
use crate::project::Project;
use crate::prover::proof::ConcreteRationale;
use std::borrow::Cow;
use tempfile::tempdir;

/// Unwrap a parsed test step that is expected to be a claim.
fn expect_claim(step: CertificateStep) -> Claim {
    let CertificateStep::Claim(claim) = step else {
        panic!("expected certificate claim step");
    };
    claim
}

fn trace_input_codes_from_concrete_steps(
    concrete_steps: &[ConcreteStep],
    kernel_context: &KernelContext,
    bindings: &BindingMap,
) -> Result<Vec<String>, CodeGenError> {
    Certificate::trace_inputs_from_concrete_steps_for_test(concrete_steps, kernel_context, bindings)
}

fn replay_certificate_step_for_test(
    checker: &mut crate::kernel::checker::Checker,
    step: &CertificateStep,
    kernel_context: &KernelContext,
) -> Result<(), CodeGenError> {
    use crate::kernel::checker::StepReason;

    match step {
        CertificateStep::Claim(claim) => {
            claim
                .validate_checker_payload(kernel_context)
                .map_err(CodeGenError::GeneratedBadCode)?;
            let generic_clause = claim.normalized_generic_clause();
            let clause = claim
                .normalized_specialized_clause(kernel_context)
                .map_err(CodeGenError::GeneratedBadCode)?;
            checker
                .check_clause(&generic_clause, kernel_context)
                .or_else(|| checker.check_clause(&clause, kernel_context))
                .ok_or_else(|| {
                    CodeGenError::GeneratedBadCode(format!(
                        "claim is not obviously true in test replay: {}",
                        clause
                    ))
                })?;
            checker.insert_clause(&generic_clause, StepReason::PreviousClaim, kernel_context);
            checker.insert_clause(&clause, StepReason::PreviousClaim, kernel_context);
        }
        CertificateStep::Satisfy(step) => {
            let mut validation_context = kernel_context.clone();
            step.validate_checker_payload(&mut validation_context)
                .map_err(CodeGenError::GeneratedBadCode)?;
            let generic_clause = step.justification.normalized_generic_clause();
            let justification_clause = step
                .justification
                .normalized_specialized_clause(kernel_context)
                .map_err(CodeGenError::GeneratedBadCode)?;
            checker
                .check_clause(&generic_clause, kernel_context)
                .or_else(|| checker.check_clause(&justification_clause, kernel_context))
                .ok_or_else(|| {
                    CodeGenError::GeneratedBadCode(format!(
                        "witness declaration is not obviously true in test replay: {}",
                        justification_clause
                    ))
                })?;
            checker.insert_clause(
                &generic_clause,
                StepReason::WitnessDeclaration,
                kernel_context,
            );
            checker.insert_clause(
                &justification_clause,
                StepReason::WitnessDeclaration,
                kernel_context,
            );
            if let Some(specialized_clause) = &step.specialized_clause {
                checker.insert_clause(
                    specialized_clause,
                    StepReason::WitnessDeclaration,
                    kernel_context,
                );
            }
            for clause in &step.witness_clauses {
                checker.insert_clause(clause, StepReason::WitnessDeclaration, kernel_context);
            }
        }
    }
    Ok(())
}

fn prepared_step_for_test(step: CertificateStep) -> PreparedCertificateStep {
    PreparedCertificateStep::new(step)
}

fn prepared_steps_for_test(steps: Vec<CertificateStep>) -> Vec<PreparedCertificateStep> {
    steps.into_iter().map(prepared_step_for_test).collect()
}

#[test]
fn test_save_load_cycle() {
    // Create a temporary directory for testing
    let temp_dir = tempdir().unwrap();
    let file_path = temp_dir.path().join("test_certs.jsonl");

    fn cert_with_proof(goal: String, proof: Vec<String>) -> Certificate {
        let trace = crate::certificate_trace::ProofTrace {
            steps: proof
                .iter()
                .cloned()
                .map(crate::certificate_trace::TraceStep::claim)
                .collect(),
        };
        Certificate::new(goal, trace)
    }

    // Create some test certificates
    let cert1 = cert_with_proof(
        "goal1".to_string(),
        vec!["step1".to_string(), "step2".to_string()],
    );
    let cert2 = cert_with_proof(
        "goal2".to_string(),
        vec![
            "step3".to_string(),
            "step4".to_string(),
            "step5".to_string(),
        ],
    );
    let cert3 = cert_with_proof(
        "goal3".to_string(),
        vec![], // Trivial proof with no steps
    );

    // Create original certificate store
    let original = CertificateStore {
        certs: vec![cert1, cert2, cert3],
    };

    // Save to file
    original.save(&file_path).unwrap();

    // Load from file
    let loaded = CertificateStore::load(&file_path).unwrap();

    // Check that we got the same data back
    assert_eq!(original.certs.len(), loaded.certs.len());

    for (orig, load) in original.certs.iter().zip(loaded.certs.iter()) {
        assert_eq!(orig.goal, load.goal);
        assert_eq!(orig.proof, load.proof);
        assert_eq!(orig.proof_step_count(), load.proof_step_count());
    }

    // Clean up is automatic when temp_dir goes out of scope
}

fn setup_claim_codec_env(code: &str) -> (Project, BindingMap, KernelContext) {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", code);

    let module_id = project
        .load_module_by_name("main")
        .expect("module should load");
    let (bindings, kernel_context) = {
        let module = match project.get_module_by_id(module_id) {
            LoadState::Ok(module) => module,
            LoadState::Error(e) => panic!("module loading error: {}", e),
            _ => panic!("unexpected module load state"),
        };
        (
            module.bindings().clone(),
            module.export.final_kernel_context.clone(),
        )
    };

    (project, bindings, kernel_context)
}

fn setup_selected_goal_env(code: &str, line: u32) -> (Project, BindingMap, KernelContext) {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", code);

    let module_id = project
        .load_module_by_name("main")
        .expect("module should load");
    let (bindings, kernel_context) = {
        match project.get_module_by_id(module_id) {
            LoadState::Ok(_) => {}
            LoadState::Error(e) => panic!("module loading error: {}", e),
            _ => panic!("unexpected module load state"),
        }
        let internal_line = line - 1;
        let lowered = project
            .get_lowered_module(module_id)
            .expect("selected module should be lowered");
        let (_, entry) = lowered
            .goals()
            .find(|(_, entry)| {
                let goal = &entry.lowered_goal.goal;
                goal.first_line <= internal_line && internal_line <= goal.last_line
            })
            .expect("selected line should have a lowered goal");
        (
            entry.bindings.clone(),
            entry.lowered_goal.kernel_context.clone(),
        )
    };

    (project, bindings, kernel_context)
}

fn witness_body_equating_ambient_bool() -> crate::kernel::term::Term {
    use crate::kernel::atom::Atom;
    use crate::kernel::term::Term;

    Term::and(
        Term::eq(
            Term::bool_type(),
            Term::new_variable(0),
            Term::atom(Atom::BoundVariable(0)),
        ),
        Term::new_true(),
    )
}

fn bool_exists_source_clause(body: crate::kernel::term::Term) -> crate::kernel::clause::Clause {
    use crate::kernel::clause::Clause;
    use crate::kernel::literal::Literal;
    use crate::kernel::local_context::LocalContext;
    use crate::kernel::term::Term;

    Clause::new(
        vec![Literal::positive(Term::exists(Term::bool_type(), body))],
        &LocalContext::from_types(vec![Term::bool_type()]),
    )
}

fn open_named_witness(
    source_clause: &crate::kernel::clause::Clause,
) -> (
    KernelContext,
    crate::prover::synthetic::WitnessRegistry,
    crate::prover::synthetic::WitnessOpening,
) {
    use crate::module::ModuleId;
    use crate::prover::synthetic::WitnessRegistry;

    let mut kernel_context = KernelContext::new();
    let exists_reduction = source_clause
        .positive_exists_reduction(&kernel_context)
        .expect("expected positive exists reduction");
    let mut witness_registry = WitnessRegistry::new();
    let opening = witness_registry.open_positive_exists(
        &mut kernel_context,
        ModuleId::default(),
        source_clause,
        &exists_reduction,
    );
    (kernel_context, witness_registry, opening)
}

fn implying_claim_for_equating_bool_witness() -> (crate::kernel::clause::Clause, Claim) {
    use crate::kernel::literal::Literal;
    use crate::kernel::local_context::LocalContext;
    use crate::kernel::term::Term;

    let clause = crate::kernel::clause::Clause::new(
        vec![Literal::positive(Term::not(Term::forall(
            Term::bool_type(),
            Term::not(witness_body_equating_ambient_bool()),
        )))],
        &LocalContext::from_types(vec![Term::bool_type()]),
    );
    let claim =
        Claim::new(clause.clone(), VariableMap::new()).expect("candidate claim should normalize");
    (clause, claim)
}

fn nested_bool_exists_clause(kernel_context: &mut KernelContext) -> crate::kernel::clause::Clause {
    use crate::kernel::atom::Atom;
    use crate::kernel::clause::Clause;
    use crate::kernel::literal::Literal;
    use crate::kernel::local_context::LocalContext;
    use crate::kernel::symbol::Symbol;
    use crate::kernel::term::Term;

    let predicate_local_id = add_test_scoped_constant(
        kernel_context,
        ModuleId::default(),
        "pred",
        kernel_context.parse_type("Bool -> Bool -> Bool"),
    );
    let predicate = Term::atom(Atom::Symbol(Symbol::ScopedConstant(predicate_local_id)));
    Clause::new(
        vec![Literal::positive(Term::exists(
            Term::bool_type(),
            predicate.apply(&[Term::new_variable(0), Term::atom(Atom::BoundVariable(0))]),
        ))],
        &LocalContext::from_types(vec![Term::bool_type()]),
    )
}

fn double_bool_exists_self_neq_clause() -> crate::kernel::clause::Clause {
    use crate::kernel::atom::Atom;
    use crate::kernel::clause::Clause;
    use crate::kernel::literal::Literal;
    use crate::kernel::local_context::LocalContext;
    use crate::kernel::term::Term;

    Clause::new(
        vec![Literal::positive(Term::exists(
            Term::bool_type(),
            Term::exists(
                Term::bool_type(),
                Term::not(Term::eq(
                    Term::bool_type(),
                    Term::atom(Atom::BoundVariable(0)),
                    Term::atom(Atom::BoundVariable(0)),
                )),
            ),
        ))],
        &LocalContext::empty(),
    )
}

fn add_test_scoped_constant(
    kernel_context: &mut KernelContext,
    module_id: ModuleId,
    name: &str,
    constant_type: crate::kernel::term::Term,
) -> crate::kernel::atom::AtomId {
    use crate::elaborator::names::ConstantName;
    use crate::kernel::symbol::Symbol;
    use crate::kernel::symbol_table::NewConstantType;

    let symbol = kernel_context.symbol_table.add_constant(
        ConstantName::unqualified(module_id, name),
        NewConstantType::Local,
        constant_type,
    );
    let Symbol::ScopedConstant(local_id) = symbol else {
        panic!("test constant should be a scoped constant");
    };
    local_id
}

fn claim_specializing_local_to_scoped_constant(
    clause: &crate::kernel::clause::Clause,
    local_id: crate::kernel::atom::AtomId,
) -> Claim {
    use crate::kernel::atom::Atom;
    use crate::kernel::symbol::Symbol;
    use crate::kernel::term::Term;

    let mut var_map = VariableMap::new();
    var_map.set(
        0,
        Term::atom(Atom::Symbol(Symbol::ScopedConstant(local_id))),
    );
    Claim::new(clause.clone(), var_map).expect("specialized claim should normalize")
}

#[test]
fn test_claim_with_args_roundtrip_single_argument() {
    let code = r#"
        theorem goal {
            true = true
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);
    let kernel = &kernel_context;

    let clause = kernel.parse_clause("x0 = true", &["Bool"]);
    let mut var_map = VariableMap::new();
    var_map.set(0, Term::new_true());
    let claim = Claim::new(clause, var_map).expect("claim should normalize");

    let serialized = Certificate::serialize_claim_with_args(&claim, &kernel_context, &bindings)
        .expect("serialization should succeed");
    assert_eq!(serialized, "function(x0: Bool) { x0 }(true)");

    let roundtrip =
        Certificate::deserialize_claim_with_args(&serialized, &project, &bindings, &kernel_context)
            .expect("deserialization should succeed");
    assert_eq!(roundtrip, claim);
}

#[test]
fn test_claim_with_args_roundtrip_multiple_arguments() {
    let code = r#"
        theorem goal {
            true = false
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);
    let kernel = &kernel_context;

    let clause = kernel.parse_clause("x0 = x1 or x0 = true", &["Bool", "Bool"]);
    let mut var_map = VariableMap::new();
    var_map.set(0, Term::new_false());
    var_map.set(1, Term::new_true());
    let claim = Claim::new(clause, var_map).expect("claim should normalize");

    let serialized = Certificate::serialize_claim_with_args(&claim, &kernel_context, &bindings)
        .expect("serialization should succeed");
    let roundtrip =
        Certificate::deserialize_claim_with_args(&serialized, &project, &bindings, &kernel_context)
            .expect("deserialization should succeed");
    assert_eq!(roundtrip, claim);
}

#[test]
fn test_claim_with_args_roundtrip_boolean_false_argument() {
    let code = r#"
        theorem goal {
            false = false
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);
    let kernel = &kernel_context;

    let clause = kernel.parse_clause("x0", &["Bool"]);
    let mut var_map = VariableMap::new();
    var_map.set(0, Term::new_false());
    let claim = Claim::new(clause, var_map).expect("claim should normalize");

    let serialized = Certificate::serialize_claim_with_args(&claim, &kernel_context, &bindings)
        .expect("serialization should succeed");
    let roundtrip =
        Certificate::deserialize_claim_with_args(&serialized, &project, &bindings, &kernel_context)
            .expect("deserialization should succeed");
    assert_eq!(roundtrip, claim);
}

#[test]
fn test_claim_with_args_supports_type_parameter_locals() {
    let code = r#"
        theorem goal {
            true
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);
    let kernel = &kernel_context;

    let clause = kernel.parse_clause("x1 = x1", &["Type", "x0"]);
    let mut var_map = VariableMap::new();
    var_map.set(0, Term::bool_type());
    var_map.set(1, Term::new_true());
    let claim = Claim::new(clause.clone(), var_map.clone()).expect("claim should normalize");

    let serialized = Certificate::serialize_claim_with_args(&claim, &kernel_context, &bindings)
        .expect("serialization with type locals should succeed");
    assert_eq!(serialized, "function[T0](x0: T0) { x0 = x0 }[Bool](true)");

    let parsed =
        Certificate::deserialize_claim_with_args(&serialized, &project, &bindings, &kernel_context)
            .expect("deserialization should succeed");
    assert_eq!(parsed, claim);
}

#[test]
fn test_deserialize_claim_with_args_rejects_non_function_shape() {
    let code = r#"
        let bar: Bool -> Bool = axiom

        theorem goal {
            bar(true)
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);

    let err =
        Certificate::deserialize_claim_with_args("bar(true)", &project, &bindings, &kernel_context)
            .expect_err("non-function claim should be rejected");
    let msg = err.to_string();
    assert!(msg.contains("function(...) { ... }(...)"));
}

#[test]
fn test_parse_code_line_accepts_claim_with_args_shape() {
    let code = r#"
        theorem goal {
            false = false
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);
    let kernel = &kernel_context;

    let mut expected_var_map = VariableMap::new();
    expected_var_map.set(0, Term::new_false());
    let expected = Claim::new(kernel.parse_clause("x0", &["Bool"]), expected_var_map)
        .expect("claim should normalize");

    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
    let step = Certificate::parse_code_line(
        "function(x0: Bool) { x0 }(false)",
        &project,
        &mut bindings_cow,
        &mut kernel_context_cow,
    )
    .expect("claim-with-args parsing should succeed");

    let claim = expect_claim(step);
    assert_eq!(claim, expected);
}

#[test]
fn test_parse_code_line_rejects_local_proof_let_claim() {
    let code = r#"
        type Empty: axiom

        theorem goal {
            true
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);
    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Borrowed(&kernel_context);

    let err = Certificate::parse_code_line(
        r#"
        true and if true {
            let x: Empty satisfy {
                true
            }
            x = x
        } else {
            true
        }
        "#,
        &project,
        &mut bindings_cow,
        &mut kernel_context_cow,
    )
    .expect_err("certificate claims should not allow proof-requiring local lets");

    assert!(
        err.to_string().contains("local lets that require proofs"),
        "unexpected error: {}",
        err
    );
}

#[test]
fn test_parse_code_line_rejects_local_proof_let_in_claim_with_args_body() {
    let code = r#"
        type Empty: axiom

        theorem goal {
            true
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);
    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Borrowed(&kernel_context);

    let err = Certificate::parse_code_line(
        r#"
        function(b: Bool) {
            if b {
                let x: Empty satisfy {
                    true
                }
                x = x
            } else {
                true
            }
        }(true)
        "#,
        &project,
        &mut bindings_cow,
        &mut kernel_context_cow,
    )
    .expect_err("claim-with-args bodies should reject proof-requiring local lets");

    assert!(
        err.to_string().contains("local lets that require proofs"),
        "unexpected error: {}",
        err
    );
}

#[test]
fn test_parse_code_line_rejects_local_proof_let_in_claim_with_args_argument() {
    let code = r#"
        type Empty: axiom

        theorem goal {
            true
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);
    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Borrowed(&kernel_context);

    let err = Certificate::parse_code_line(
        r#"
        function(b: Bool) {
            b
        }(if true {
            let x: Empty satisfy {
                true
            }
            x = x
        } else {
            true
        })
        "#,
        &project,
        &mut bindings_cow,
        &mut kernel_context_cow,
    )
    .expect_err("claim-with-args arguments should reject proof-requiring local lets");

    assert!(
        err.to_string().contains("local lets that require proofs"),
        "unexpected error: {}",
        err
    );
}

#[test]
fn test_emit_named_function_witness_does_not_synthesize_justification_claim() {
    use crate::kernel::checker::{Checker, StepReason};
    use crate::kernel::term::Term;

    let source_clause = bool_exists_source_clause(Term::not(Term::eq(
        Term::bool_type(),
        Term::atom(crate::kernel::atom::Atom::BoundVariable(0)),
        Term::new_variable(0),
    )));
    let (kernel_context, witness_registry, opening) = open_named_witness(&source_clause);

    let ordered_steps = vec![CertificateStep::Claim(
        Claim::new(opening.reduction.clause.clone(), VariableMap::new())
            .expect("specialized witness clause should become a claim"),
    )];
    let emitted =
        Certificate::emit_named_witnesses(ordered_steps, &witness_registry, &kernel_context)
            .expect("named witness emission should succeed");

    assert!(
        matches!(emitted.first(), Some(CertificateStep::Satisfy(_))),
        "expected the witness declaration before any claim that mentions it"
    );
    assert_eq!(
        emitted
            .iter()
            .filter(|step| matches!(step, CertificateStep::Satisfy(_)))
            .count(),
        1,
        "expected exactly one witness declaration"
    );
    assert!(
        !emitted.iter().any(|step| {
            let CertificateStep::Claim(claim) = step else {
                return false;
            };
            claim
                .normalized_specialized_clause(&kernel_context)
                .is_ok_and(|clause| clause == source_clause.normalized())
        }),
        "the emitted proof should not reintroduce the witness existential as a standalone claim"
    );

    let mut checker = Checker::new();
    checker.insert_clause(
        &source_clause.normalized(),
        StepReason::Testing,
        &kernel_context,
    );
    for step in &emitted {
        replay_certificate_step_for_test(&mut checker, step, &kernel_context)
            .expect("synthetic witness step should check");
    }
    assert!(
        !checker.has_contradiction(),
        "synthetic witness setup should not close a proof by itself"
    );
}

#[test]
fn test_named_function_witness_can_match_implying_claim() {
    use crate::kernel::checker::{Checker, StepReason};
    let source_clause = bool_exists_source_clause(witness_body_equating_ambient_bool());
    let (kernel_context, witness_registry, _opening) = open_named_witness(&source_clause);
    let (&local_id, _) = witness_registry
        .iter()
        .next()
        .expect("expected one named witness");

    let (candidate_clause, candidate_claim) = implying_claim_for_equating_bool_witness();

    let mut checker = Checker::new();
    checker.insert_clause(
        &candidate_clause.normalized(),
        StepReason::Testing,
        &kernel_context,
    );
    assert!(
        checker
            .check_clause(&source_clause.normalized(), &kernel_context)
            .is_some(),
        "candidate claim should imply the witness existential"
    );

    let emitter = super::WitnessEmitter::new(
        prepared_steps_for_test(vec![CertificateStep::Claim(candidate_claim)]),
        &witness_registry,
        kernel_context.clone(),
        ModuleId::default(),
        &HashSet::new(),
    )
    .expect("witness emitter should build");
    assert_eq!(emitter.anchor_indices.get(&local_id), Some(&0));
}

#[test]
fn test_named_function_witness_can_anchor_to_first_of_duplicate_claims() {
    let source_clause = bool_exists_source_clause(witness_body_equating_ambient_bool());
    let (kernel_context, witness_registry, _opening) = open_named_witness(&source_clause);
    let (&local_id, _) = witness_registry
        .iter()
        .next()
        .expect("expected one named witness");

    let (_candidate_clause, candidate_claim) = implying_claim_for_equating_bool_witness();

    let emitter = super::WitnessEmitter::new(
        prepared_steps_for_test(vec![
            CertificateStep::Claim(candidate_claim.clone()),
            CertificateStep::Claim(candidate_claim),
        ]),
        &witness_registry,
        kernel_context,
        ModuleId::default(),
        &HashSet::new(),
    )
    .expect("duplicate matching claims should still anchor successfully");

    assert_eq!(emitter.anchor_indices.get(&local_id), Some(&0));
}

#[test]
fn test_emit_named_function_witness_keeps_explicit_specialized_claim() {
    let source_clause = bool_exists_source_clause(witness_body_equating_ambient_bool());
    let (kernel_context, witness_registry, _opening) = open_named_witness(&source_clause);
    let (_local_id, witness) = witness_registry
        .iter()
        .next()
        .expect("expected one named witness");

    let (_candidate_clause, candidate_claim) = implying_claim_for_equating_bool_witness();
    let specialized_claim = Claim::new(witness.specialized_clause.clone(), VariableMap::new())
        .expect("specialized witness clause should normalize");

    let emitted = Certificate::emit_named_witnesses(
        vec![
            CertificateStep::Claim(candidate_claim),
            CertificateStep::Claim(specialized_claim),
        ],
        &witness_registry,
        &kernel_context,
    )
    .expect("named witness emission should succeed");

    assert_eq!(
        emitted.len(),
        3,
        "the implying claim is kept, then the witness declaration and specialized claim remain"
    );
    assert!(
        matches!(emitted.first(), Some(CertificateStep::Claim(_))),
        "expected the implying claim to remain before the witness declaration"
    );
    assert!(
        matches!(emitted.get(1), Some(CertificateStep::Satisfy(_))),
        "expected the witness declaration to be anchored after the implying claim"
    );
    assert!(
        matches!(emitted.get(2), Some(CertificateStep::Claim(_))),
        "expected the specialized claim to remain after the witness declaration"
    );
}

#[test]
fn test_named_function_witness_does_not_anchor_to_claim_that_mentions_it() {
    let source_clause = bool_exists_source_clause(witness_body_equating_ambient_bool());
    let (kernel_context, witness_registry, _opening) = open_named_witness(&source_clause);
    let (&symbol, _) = witness_registry
        .iter()
        .next()
        .expect("expected one named witness");
    let Symbol::ScopedConstant(local_id) = symbol else {
        panic!("expected a scoped witness symbol");
    };
    let claim = claim_specializing_local_to_scoped_constant(&source_clause, local_id);

    let emitted = Certificate::emit_named_witnesses(
        vec![CertificateStep::Claim(claim.clone())],
        &witness_registry,
        &kernel_context,
    )
    .expect("self-referential witness claim should emit without cycling");

    assert!(
        matches!(emitted.first(), Some(CertificateStep::Satisfy(_))),
        "expected a standalone witness declaration before the claim"
    );
    assert_eq!(
        emitted.get(1),
        Some(&CertificateStep::Claim(claim)),
        "expected the original claim to remain after the witness declaration"
    );
}

#[test]
fn test_named_function_witness_uses_fresh_result_binder_name() {
    let source_clause = bool_exists_source_clause(witness_body_equating_ambient_bool());
    let (kernel_context, witness_registry, _opening) = open_named_witness(&source_clause);
    let (_local_id, witness) = witness_registry
        .iter()
        .next()
        .expect("expected one named witness");
    let justification = Claim::new(source_clause.normalized(), VariableMap::new())
        .expect("justification should normalize");

    let step = Certificate::witness_entry_to_step(witness, justification, &kernel_context)
        .expect("witness step should build");

    assert_eq!(step.return_name.as_deref(), Some("w0_result"));
}

#[test]
fn test_emitted_witness_names_are_compact_even_if_internal_ids_are_sparse() {
    use crate::code_generator::CodeGenerator;
    use crate::kernel::atom::Atom;
    use crate::kernel::symbol::Symbol;
    use crate::prover::synthetic::WitnessRegistry;

    let (_project, bindings, _) = setup_claim_codec_env(
        r#"
        theorem goal {
            true
        }
    "#,
    );
    let module_id = bindings.module_id();
    let source_clause = bool_exists_source_clause(witness_body_equating_ambient_bool());
    let mut kernel_context = KernelContext::new();
    let exists_reduction = source_clause
        .positive_exists_reduction(&kernel_context)
        .expect("expected positive exists reduction");
    let mut witness_registry = WitnessRegistry::new();
    let mut last_symbol = None;

    for _ in 0..34 {
        let opening = witness_registry.open_positive_exists(
            &mut kernel_context,
            module_id,
            &source_clause,
            &exists_reduction,
        );
        last_symbol = opening.term.iter_atoms().find_map(|atom| match atom {
            Atom::Symbol(symbol @ Symbol::ScopedConstant(_)) => Some(*symbol),
            _ => None,
        });
    }
    let last_symbol = last_symbol.expect("expected a final witness symbol");
    let (_candidate_clause, candidate_claim) = implying_claim_for_equating_bool_witness();
    let witness = witness_registry
        .get(last_symbol)
        .expect("expected the last witness to remain registered");
    let specialized_claim = Claim::new(witness.specialized_clause.clone(), VariableMap::new())
        .expect("specialized witness clause should normalize");

    let (emitted, updated_kernel_context) = Certificate::emit_named_witnesses_with_context(
        prepared_steps_for_test(vec![
            CertificateStep::Claim(candidate_claim),
            CertificateStep::Claim(specialized_claim),
        ]),
        &witness_registry,
        kernel_context,
        module_id,
        &HashSet::new(),
    )
    .expect("named witness emission should succeed");

    let mut generator = CodeGenerator::new_for_certificate(&bindings);
    let proof: Vec<_> = emitted
        .iter()
        .map(|step| {
            Certificate::serialize_certificate_step(
                &step.step,
                &mut generator,
                &updated_kernel_context,
                &bindings,
            )
            .expect("certificate step should serialize")
        })
        .collect();

    assert_eq!(
        updated_kernel_context
            .symbol_table
            .name_for_symbol(last_symbol)
            .to_string(),
        "w0"
    );
    assert!(
        emitted
            .first()
            .is_some_and(|step| matches!(step.step, CertificateStep::Claim(_))),
        "expected the implying claim to justify anchored witness declarations"
    );
    let first_witness_index = proof
        .iter()
        .position(|line| line.starts_with("let w0"))
        .expect("expected a compact witness declaration");
    assert!(
        first_witness_index > 0,
        "expected compact witness declaration after its justifying claim"
    );
    assert!(
        proof[first_witness_index].starts_with("let w0"),
        "expected compact witness declaration, got {proof:?}"
    );
    assert!(
        proof
            .iter()
            .skip(first_witness_index + 1)
            .any(|line| line.contains("w0")),
        "expected later claims to use the compact witness name, got {proof:?}"
    );
    assert!(
        proof.iter().all(|line| !line.contains("w33")),
        "expected sparse internal witness names to stay out of the emitted proof: {proof:?}"
    );
}

#[test]
fn test_named_function_witness_replays_exact_open_clause() {
    let source_clause = bool_exists_source_clause(witness_body_equating_ambient_bool());
    let (kernel_context, witness_registry, _opening) = open_named_witness(&source_clause);
    let (_local_id, witness) = witness_registry
        .iter()
        .next()
        .expect("expected one named witness");
    let justification = Claim::new(source_clause.normalized(), VariableMap::new())
        .expect("justification should normalize");

    let step = Certificate::witness_entry_to_step(witness, justification, &kernel_context)
        .expect("witness step should build");

    assert_eq!(step.witness_clauses.len(), 1);
    assert_eq!(step.witness_clauses[0].get_local_context().len(), 1);
    assert!(
        !format!("{}", step.witness_clauses[0]).contains("forall"),
        "function witness replay should keep an open clause, not a closed forall"
    );
}

#[test]
fn test_named_function_witness_certificate_roundtrips_without_extra_satisfy_step() {
    use crate::code_generator::CodeGenerator;
    use crate::prover::synthetic::WitnessRegistry;

    let (project, bindings, _) = setup_claim_codec_env(
        r#"
        theorem goal {
            true
        }
    "#,
    );
    let source_clause = bool_exists_source_clause(witness_body_equating_ambient_bool());
    let pre_kernel_context = KernelContext::new();
    let mut post_kernel_context = pre_kernel_context.clone();
    let exists_reduction = source_clause
        .positive_exists_reduction(&post_kernel_context)
        .expect("expected positive exists reduction");
    let mut witness_registry = WitnessRegistry::new();
    witness_registry.open_positive_exists(
        &mut post_kernel_context,
        bindings.module_id(),
        &source_clause,
        &exists_reduction,
    );
    let (_candidate_clause, candidate_claim) = implying_claim_for_equating_bool_witness();

    let (emitted, updated_kernel_context) = Certificate::emit_named_witnesses_with_context(
        prepared_steps_for_test(vec![CertificateStep::Claim(candidate_claim)]),
        &witness_registry,
        post_kernel_context,
        bindings.module_id(),
        &HashSet::new(),
    )
    .expect("named witness emission should succeed");

    assert_eq!(
        emitted
            .iter()
            .filter(|step| matches!(step.step, CertificateStep::Satisfy(_)))
            .count(),
        1,
        "expected exactly one witness declaration after compaction"
    );

    let mut generator = CodeGenerator::new_for_certificate(&bindings);
    let proof: Vec<_> = emitted
        .iter()
        .map(|step| {
            Certificate::serialize_certificate_step(
                &step.step,
                &mut generator,
                &updated_kernel_context,
                &bindings,
            )
            .expect("certificate step should serialize")
        })
        .collect();

    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Owned(pre_kernel_context);
    let reparsed: Vec<_> = proof
        .iter()
        .map(|line| {
            Certificate::parse_code_line(line, &project, &mut bindings_cow, &mut kernel_context_cow)
                .expect("serialized witness proof should parse")
        })
        .collect();

    assert_eq!(reparsed.len(), emitted.len());
    assert_eq!(
        reparsed
            .iter()
            .filter(|step| matches!(step, CertificateStep::Satisfy(_)))
            .count(),
        1,
        "roundtrip should not synthesize an extra witness declaration"
    );
    assert!(matches!(reparsed.first(), Some(CertificateStep::Claim(_))));
    assert!(matches!(reparsed.get(1), Some(CertificateStep::Satisfy(_))));
}

#[test]
fn test_emit_named_witnesses_opens_specialized_positive_exists_claim() {
    use crate::prover::synthetic::WitnessRegistry;

    let mut kernel_context = KernelContext::new();
    let parent_local_id = add_test_scoped_constant(
        &mut kernel_context,
        ModuleId::default(),
        "parent",
        Term::bool_type(),
    );
    let clause = nested_bool_exists_clause(&mut kernel_context);
    let claim = claim_specializing_local_to_scoped_constant(&clause, parent_local_id);

    let emitted = Certificate::emit_named_witnesses(
        vec![CertificateStep::Claim(claim.clone())],
        &WitnessRegistry::new(),
        &kernel_context,
    )
    .expect("specialized positive exists claim should emit a synthetic witness");

    assert_eq!(
        emitted.len(),
        2,
        "expected the original claim followed by one synthetic witness step"
    );

    assert_eq!(emitted[0], CertificateStep::Claim(claim.clone()));

    let CertificateStep::Satisfy(step) = &emitted[1] else {
        panic!("expected a synthetic witness step");
    };
    assert_eq!(step.justification, claim);
    assert!(step.return_name.is_none());
    CertificateStep::Satisfy(step.clone())
        .validate_normalized_shape(&kernel_context)
        .expect("synthetic witness step should keep normalized witness clauses");
}

#[test]
fn test_emit_named_witnesses_opens_nested_positive_exists_claims() {
    use crate::kernel::checker::{Checker, StepReason};
    use crate::prover::synthetic::WitnessRegistry;

    let source_clause = double_bool_exists_self_neq_clause();
    let mut kernel_context = KernelContext::new();
    let reduction = source_clause
        .positive_exists_reduction(&kernel_context)
        .expect("outer exists should be reducible");
    let mut witness_registry = WitnessRegistry::new();
    witness_registry.open_positive_exists(
        &mut kernel_context,
        ModuleId::default(),
        &source_clause,
        &reduction,
    );
    let claim = Claim::new(source_clause.clone(), VariableMap::new())
        .expect("source claim should normalize");

    let (emitted, updated_kernel_context) = Certificate::emit_named_witnesses_with_context(
        prepared_steps_for_test(vec![CertificateStep::Claim(claim)]),
        &witness_registry,
        kernel_context,
        ModuleId::default(),
        &HashSet::new(),
    )
    .expect("named witness emission should succeed");

    assert_eq!(
        emitted
            .iter()
            .filter(|step| matches!(step.step, CertificateStep::Satisfy(_)))
            .count(),
        2,
        "nested positive exists should emit one witness per binder"
    );

    let mut checker = Checker::new();
    checker.insert_clause(
        &source_clause.normalized(),
        StepReason::Testing,
        &updated_kernel_context,
    );
    for step in &emitted {
        replay_certificate_step_for_test(&mut checker, &step.step, &updated_kernel_context)
            .expect("nested synthetic witness step should check");
        if checker.has_contradiction() {
            break;
        }
    }
    assert!(
        checker.has_contradiction(),
        "nested synthetic witnesses should expose the contradiction"
    );
}

#[test]
fn test_specialized_positive_exists_step_uses_emitter_module_id() {
    use crate::prover::synthetic::WitnessRegistry;

    let module_id = ModuleId(7);
    let mut kernel_context = KernelContext::new();
    let parent_local_id =
        add_test_scoped_constant(&mut kernel_context, module_id, "parent", Term::bool_type());
    let clause = nested_bool_exists_clause(&mut kernel_context);
    let claim = claim_specializing_local_to_scoped_constant(&clause, parent_local_id);
    let witness_registry = WitnessRegistry::new();

    let mut emitter = super::WitnessEmitter::new(
        prepared_steps_for_test(vec![CertificateStep::Claim(claim.clone())]),
        &witness_registry,
        kernel_context,
        module_id,
        &HashSet::new(),
    )
    .expect("witness emitter should build");

    let (synthetic_local_id, returned_parent_local_id, step) = emitter
        .specialized_positive_exists_step(&claim)
        .expect("opening a specialized positive exists should succeed")
        .expect("expected a synthetic witness step");

    assert_eq!(
        returned_parent_local_id,
        Symbol::ScopedConstant(parent_local_id)
    );
    assert_eq!(step.justification, claim);

    let synthetic_witness = emitter
        .synthetic_witness_registry
        .get(synthetic_local_id)
        .expect("synthetic witness should be registered");
    assert_eq!(synthetic_witness.name.module_id(), module_id);
}

#[test]
fn test_synthetic_witness_preserves_unused_binder_contradiction() {
    use crate::kernel::checker::{Checker, StepReason};
    use crate::kernel::literal::Literal;
    use crate::kernel::local_context::LocalContext;
    use crate::prover::synthetic::WitnessRegistry;

    let mut kernel_context = KernelContext::new();
    let parent_local_id = add_test_scoped_constant(
        &mut kernel_context,
        ModuleId::default(),
        "parent",
        Term::bool_type(),
    );

    let conjunction = Term::and(Term::new_variable(0), Term::new_true());
    let negated_clause = crate::kernel::clause::Clause::new(
        vec![Literal::positive(Term::not(conjunction.clone()))],
        &LocalContext::from_types(vec![Term::bool_type()]),
    );
    let exists_clause = crate::kernel::clause::Clause::new(
        vec![Literal::positive(Term::exists(
            Term::bool_type(),
            conjunction,
        ))],
        &LocalContext::from_types(vec![Term::bool_type()]),
    );

    let negated_claim =
        claim_specializing_local_to_scoped_constant(&negated_clause, parent_local_id);
    let exists_claim = claim_specializing_local_to_scoped_constant(&exists_clause, parent_local_id);

    let (emitted, updated_kernel_context) = Certificate::emit_named_witnesses_with_context(
        prepared_steps_for_test(vec![
            CertificateStep::Claim(negated_claim),
            CertificateStep::Claim(exists_claim),
        ]),
        &WitnessRegistry::new(),
        kernel_context,
        ModuleId::default(),
        &HashSet::new(),
    )
    .expect("named witness emission should succeed");

    let mut checker = Checker::new();
    checker.insert_clause(
        &negated_clause.normalized(),
        StepReason::Testing,
        &updated_kernel_context,
    );
    checker.insert_clause(
        &exists_clause.normalized(),
        StepReason::Testing,
        &updated_kernel_context,
    );
    for step in &emitted {
        replay_certificate_step_for_test(&mut checker, &step.step, &updated_kernel_context)
            .expect("synthetic witness step should check");
        if checker.has_contradiction() {
            break;
        }
    }
    assert!(
        checker.has_contradiction(),
        "synthetic witness should preserve the contradiction when the existential binder is unused"
    );
}

#[test]
fn test_parse_code_line_preserves_higher_order_inequality_claim_with_args() {
    let code = r#"
        type Foo: axiom
        let a: Foo = axiom
        let f: Foo -> Foo = axiom
        let g: Foo -> (Foo -> Foo) = axiom

        theorem goal {
            true
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);
    let line = "function(x0: Foo) { g(x0) != f }(a)";

    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
    let step =
        Certificate::parse_code_line(line, &project, &mut bindings_cow, &mut kernel_context_cow)
            .expect("higher-order claim-with-args parsing should succeed");

    let claim = expect_claim(step);
    assert_eq!(claim.var_map().len(), 1);

    let serialized = Certificate::serialize_claim_with_args(&claim, &kernel_context, &bindings)
        .expect("serialization should preserve higher-order inequality literal");
    assert_eq!(serialized, line);
}

#[test]
fn test_parse_code_line_canonicalizes_nested_inequality_in_claim_with_args() {
    let code = r#"
        inductive Foo {
            a
            b
            c
        }

        let contains: (Foo, Foo) -> Bool = axiom
        let has_non: (Foo, Foo) -> Bool = axiom

        theorem goal {
            true
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);
    let line = "function(x0: Foo, x1: Foo, x2: Foo) { not (contains(x0, x1) and x2 != x1) or has_non(x0, x2) }(Foo.c, Foo.a, Foo.b)";

    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
    let step =
        Certificate::parse_code_line(line, &project, &mut bindings_cow, &mut kernel_context_cow)
            .expect("claim-with-args parsing should succeed");

    let claim = expect_claim(step);
    let mut generator = CodeGenerator::new_for_certificate(&bindings);
    let generic_value =
        kernel_context.quote_clause(&claim.normalized_generic_clause(), None, None, false);
    let generic_code = generator
        .value_to_code(&generic_value)
        .expect("normalized generic clause should serialize");
    assert!(
        generic_code.contains("x1 != x2"),
        "unexpected generic clause: {generic_code}"
    );
    assert!(
        !generic_code.contains("x2 != x1"),
        "generic clause should keep the canonical inequality order: {generic_code}"
    );

    let serialized = Certificate::serialize_claim_with_args(&claim, &kernel_context, &bindings)
        .expect("serialization should preserve the canonical nested inequality order");
    assert!(
        serialized.contains("x1 != x2"),
        "unexpected serialization: {serialized}"
    );
    assert!(
        !serialized.contains("x2 != x1"),
        "serialization should not revert the canonical inequality order: {serialized}"
    );
}

#[test]
fn test_deserialize_claim_with_args_preserves_single_not_if_literal() {
    let code = r#"
        type Nat: axiom
        let suc: Nat -> Nat = axiom
        let zero: Nat = axiom
        let a: Nat = axiom

        theorem goal {
            true
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);
    let line = "function(x0: Nat) { not if a = zero { x0 = zero } else { suc(x0) = a } }(choose(k0: Nat) { a = suc(k0) })";

    let err = Certificate::deserialize_claim_with_args(line, &project, &bindings, &kernel_context)
        .expect_err("choose should be rejected in claim-with-args deserialization");
    assert!(
        err.to_string()
            .contains("choose expressions are not supported"),
        "unexpected error: {}",
        err
    );
}

#[test]
fn test_parse_code_line_accepts_claim_with_type_args_shape() {
    let code = r#"
        theorem goal {
            true
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);
    let kernel = &kernel_context;

    let mut expected_var_map = VariableMap::new();
    expected_var_map.set(0, Term::bool_type());
    expected_var_map.set(1, Term::new_true());
    let expected = Claim::new(
        kernel.parse_clause("x1 = x1", &["Type", "x0"]),
        expected_var_map,
    )
    .expect("claim should normalize");

    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
    let step = Certificate::parse_code_line(
        "function[T0](x0: T0) { x0 = x0 }[Bool](true)",
        &project,
        &mut bindings_cow,
        &mut kernel_context_cow,
    )
    .expect("claim-with-type-args parsing should succeed");

    let claim = expect_claim(step);
    assert_eq!(claim, expected);
}

#[test]
fn test_parse_code_line_accepts_claim_with_type_args_only_shape() {
    let code = r#"
        let foo[T]: Bool = axiom

        theorem goal {
            foo[Bool]
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);

    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
    let step = Certificate::parse_code_line(
        "function[T0] { foo[T0] }",
        &project,
        &mut bindings_cow,
        &mut kernel_context_cow,
    )
    .expect("type-only claim-with-args parsing should succeed");

    let claim = expect_claim(step);
    assert_eq!(claim.var_map().len(), 0);

    let serialized = Certificate::serialize_claim_with_args(&claim, &kernel_context, &bindings)
        .expect("serialization should succeed");
    assert_eq!(serialized, "function[T0] { foo[T0] }");
    let roundtrip =
        Certificate::deserialize_claim_with_args(&serialized, &project, &bindings, &kernel_context)
            .expect("deserialization should succeed");
    assert_eq!(roundtrip, claim);
}

#[test]
fn test_parse_code_line_accepts_type_args_only_shape_with_concrete_application() {
    let code = r#"
        let foo[T]: Bool = axiom

        theorem goal {
            foo[Bool]
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);

    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
    let step = Certificate::parse_code_line(
        "function[T0] { foo[T0] }[Bool]",
        &project,
        &mut bindings_cow,
        &mut kernel_context_cow,
    )
    .expect("concrete type-only claim-with-args parsing should succeed");

    let claim = expect_claim(step);
    assert_eq!(claim.var_map().len(), 1);
    assert_eq!(claim.var_map().get_mapping(0), Some(Term::bool_type_ref()));
    let serialized = Certificate::serialize_claim_with_args(&claim, &kernel_context, &bindings)
        .expect("serialization should succeed");
    assert_eq!(serialized, "function[T0] { foo[T0] }[Bool]");
    let roundtrip =
        Certificate::deserialize_claim_with_args(&serialized, &project, &bindings, &kernel_context)
            .expect("deserialization should succeed");
    assert_eq!(roundtrip, claim);
}

#[test]
fn test_claim_with_typeclass_only_params_omits_trailing_type_args() {
    let code = r#"
        typeclass T: FiniteGroup {
            unit: T
        }

        let g0[T]: Bool -> Bool = axiom
        let g1[T]: T -> Bool = axiom

        theorem goal {
            true
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);
    let line = "function[T0: FiniteGroup] { g1(g0[T0](false)) }";

    let claim =
        Certificate::deserialize_claim_with_args(line, &project, &bindings, &kernel_context)
            .expect("typeclass-only claim should deserialize");
    assert_eq!(claim.var_map().len(), 0);

    let serialized = Certificate::serialize_claim_with_args(&claim, &kernel_context, &bindings)
        .expect("typeclass-only claim should serialize");
    assert_eq!(serialized, line);

    let roundtrip =
        Certificate::deserialize_claim_with_args(&serialized, &project, &bindings, &kernel_context)
            .expect("typeclass-only claim should roundtrip");
    assert_eq!(roundtrip, claim);
}

#[test]
fn test_serialize_claim_with_args_avoids_colliding_lambda_arg_names() {
    let code = r#"
        let x0: Bool = axiom
        let x1: Bool = axiom

        theorem goal {
            true
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);
    let kernel = &kernel_context;

    let clause = kernel.parse_clause("x0 or x1 or x2", &["Bool", "Bool", "Bool"]);
    let mut var_map = VariableMap::new();
    var_map.set(0, Term::new_true());
    var_map.set(1, Term::new_false());
    var_map.set(2, Term::new_true());
    let claim = Claim::new(clause, var_map).expect("claim should normalize");

    let serialized = Certificate::serialize_claim_with_args(&claim, &kernel_context, &bindings)
        .expect("serialization should succeed");
    assert!(!serialized.contains("function(x0: Bool"));

    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
    let parsed = Certificate::parse_code_line(
        &serialized,
        &project,
        &mut bindings_cow,
        &mut kernel_context_cow,
    )
    .expect("serialized line should parse even when x0/x1 are already bound");

    let roundtrip_claim = expect_claim(parsed);
    assert_eq!(roundtrip_claim, claim);
}

#[test]
fn test_parsed_claim_matches_definition_clause() {
    use crate::kernel::checker::{Checker, StepReason};
    use crate::kernel::proof_step::Rule;

    let code = r#"
        type Nat: axiom
        let a: Nat = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        let h: Nat -> Bool = axiom
        define fimp(x: Nat) -> Bool { f(x) implies (g(x) and h(x)) }

        theorem goal {
            true
        }
    "#;
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", code);

    let module_id = project
        .load_module_by_name("main")
        .expect("module should load");
    match project.get_module_by_id(module_id) {
        LoadState::Ok(_) => {}
        LoadState::Error(e) => panic!("module loading error: {}", e),
        _ => panic!("unexpected module load state"),
    }
    let lowered = project
        .get_lowered_module(module_id)
        .expect("lowered module should be available");
    let (goal_id, entry) = lowered
        .goal_by_name("goal")
        .expect("lowered goal should be available");
    let normalized_facts = lowered
        .visible_facts_for_goal(goal_id)
        .expect("lowered facts should be available");
    let bindings = entry.bindings.clone();
    let kernel_context = lowered.final_kernel_context.clone();

    let mut checker = Checker::new();
    for normalized in normalized_facts {
        for step in &normalized.steps {
            let Rule::Assumption(info) = &step.rule else {
                panic!("expected lowered fact assumptions");
            };
            checker.insert_clause(
                &step.clause,
                StepReason::Assumption(info.source.clone()),
                &normalized.kernel_context,
            );
        }
    }

    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
    let step = Certificate::parse_code_line(
        "function(x0: Nat) { f(x0) and (not g(x0) or not h(x0)) or fimp(x0) }(a)",
        &project,
        &mut bindings_cow,
        &mut kernel_context_cow,
    )
    .expect("claim-with-args parsing should succeed");

    let claim = expect_claim(step);
    let specialized = claim
        .normalized_specialized_clause(kernel_context_cow.as_ref())
        .expect("claim specialization should succeed");
    assert!(
        checker
            .check_clause(claim.clause(), kernel_context_cow.as_ref())
            .or_else(|| checker.check_clause(&specialized, kernel_context_cow.as_ref()))
            .is_some(),
        "parsed claim should match one of the normalized definition clauses"
    );
}

#[test]
fn test_parse_code_line_plain_claim_still_works() {
    let code = r#"
        let bar: Bool -> Bool = axiom

        theorem goal {
            bar(true)
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);

    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
    let step = Certificate::parse_code_line(
        "bar(true)",
        &project,
        &mut bindings_cow,
        &mut kernel_context_cow,
    )
    .expect("plain claim parsing should succeed");

    let claim = expect_claim(step);
    assert_eq!(claim.var_map().len(), 0);
}

#[test]
fn test_parse_code_line_preserves_plain_negated_exists_literal() {
    let code = r#"
        theorem goal {
            true
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);

    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
    let step = Certificate::parse_code_line(
        "not exists(k0: Bool, k1: Bool) { k0 = k1 }",
        &project,
        &mut bindings_cow,
        &mut kernel_context_cow,
    )
    .expect("plain negated exists claim should parse");

    let claim = expect_claim(step);
    assert_eq!(claim.clause().get_local_context().len(), 0);
    assert_eq!(claim.var_map().len(), 0);
    assert_eq!(
        claim.clause().to_string(),
        "not exists(Bool => exists(Bool => eq(Bool, b0, b1)))"
    );
}

#[test]
fn test_parse_code_line_keeps_plain_non_cnf_literal_shape() {
    let code = r#"
        let a: Bool = axiom
        let b: Bool = axiom

        theorem goal {
            true
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);

    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
    let step = Certificate::parse_code_line(
        "not (a and b)",
        &project,
        &mut bindings_cow,
        &mut kernel_context_cow,
    )
    .expect("plain non-CNF claim should parse");

    let claim = expect_claim(step);
    assert_eq!(
        claim.clause().literals.len(),
        1,
        "plain claim should stay as one literal"
    );
    assert!(
        !claim.clause().literals[0].positive,
        "plain claim should remain a negative literal"
    );
    let (head, args) = claim.clause().literals[0]
        .left
        .as_ref()
        .split_application_multi()
        .expect("negative literal should remain an application term");
    assert_eq!(
        *head.get_head_atom(),
        crate::kernel::atom::Atom::Symbol(crate::kernel::symbol::Symbol::And),
        "plain claim should not be CNF-rewritten into separate disjuncts"
    );
    assert_eq!(
        args.len(),
        2,
        "conjunction literal should keep both operands"
    );
}

#[test]
fn test_parse_code_line_canonicalizes_plain_claim_equality() {
    let code = r#"
        theorem goal {
            true
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);

    let mut lhs_bindings = Cow::Borrowed(&bindings);
    let mut lhs_kernel_context = Cow::Borrowed(&kernel_context);
    let lhs = Certificate::parse_code_line(
        "true = false",
        &project,
        &mut lhs_bindings,
        &mut lhs_kernel_context,
    )
    .expect("left equality should parse");

    let mut rhs_bindings = Cow::Borrowed(&bindings);
    let mut rhs_kernel_context = Cow::Borrowed(&kernel_context);
    let rhs = Certificate::parse_code_line(
        "false = true",
        &project,
        &mut rhs_bindings,
        &mut rhs_kernel_context,
    )
    .expect("right equality should parse");

    let lhs_claim = expect_claim(lhs);
    let rhs_claim = expect_claim(rhs);
    assert_eq!(lhs_claim, rhs_claim);
}

#[test]
fn test_deserialize_claim_with_args_normalizes_value_argument_term() {
    let code = r#"
        theorem goal {
            true
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);

    let claim = Certificate::deserialize_claim_with_args(
        "function(x0: Bool) { x0 }(not not false)",
        &project,
        &bindings,
        &kernel_context,
    )
    .expect("claim-with-args deserialization should succeed");

    assert_eq!(claim.var_map().get_mapping(0), Some(&Term::new_false()));
}

#[test]
fn test_parse_code_line_handles_choose_claim_shape() {
    let code = r#"
        theorem goal {
            true = true
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);

    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
    let result = Certificate::parse_code_line(
        "choose(x0: Bool) { x0 } = true",
        &project,
        &mut bindings_cow,
        &mut kernel_context_cow,
    );

    let err = result.expect_err("choose claims should be rejected");
    assert!(
        err.to_string()
            .contains("choose expressions are not supported"),
        "unexpected error: {}",
        err
    );
}

#[test]
fn test_parse_code_line_handles_closed_binder_claims_with_choose() {
    let code = r#"
        let identity: Bool -> Bool = axiom

        theorem goal {
            true
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);

    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
    let result = Certificate::parse_code_line(
        "identity(choose(k0: Bool) { forall(x0: Bool) { not identity(x0) = k0 } }) = choose(k1: Bool) { forall(x1: Bool) { not identity(x1) = k1 } }",
        &project,
        &mut bindings_cow,
        &mut kernel_context_cow,
    );

    let err = result.expect_err("choose in closed binder-heavy claims should be rejected");
    assert!(
        err.to_string()
            .contains("choose expressions are not supported"),
        "unexpected error: {}",
        err
    );
}

#[test]
fn test_checker_rejects_unjustified_choose_claim() {
    let code = r#"
        theorem goal {
            true
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);

    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
    let result = Certificate::parse_code_line(
        "choose(x0: Bool) { x0 } = true",
        &project,
        &mut bindings_cow,
        &mut kernel_context_cow,
    );

    let err = result.expect_err("choose claims should be rejected before checking");
    assert!(
        err.to_string()
            .contains("choose expressions are not supported"),
        "unexpected error: {}",
        err
    );
}

#[test]
fn test_check_cert_accepts_lambda_valued_claim_argument() {
    use crate::prover::{Outcome, ProverMode};

    let code = r#"
        type Nat: axiom
        let rel: (Nat, Nat) -> Bool = axiom

        define is_transitive[T](f: (T, T) -> Bool) -> Bool {
            forall(x: T, y: T, z: T) {
                f(x, y) and f(y, z) implies f(x, z)
            }
        }

        axiom rel_trans(x: Nat, y: Nat, z: Nat) {
            rel(x, y) and rel(y, z) implies rel(x, z)
        }

        theorem goal {
            is_transitive(function(a: Nat, b: Nat) { rel(a, b) })
        } by {
            forall(x: Nat, y: Nat, z: Nat) {
                rel_trans(x, y, z)
            }
        }
    "#;

    let (mut processor, bindings, normalized_goal) = Processor::test_goal(code);
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", code);

    let outcome = processor.search(
        ProverMode::Interactive {
            timeout_secs: 5.0,
            activation_limit: 100_000,
        },
        &normalized_goal.kernel_context,
    );
    assert_eq!(outcome, Outcome::Success);

    let cert = processor
        .make_cert(
            &bindings,
            &normalized_goal.kernel_context,
            &project,
            Some(&normalized_goal),
            false,
        )
        .expect("lambda-valued cert should be finalized");
    let proof = cert
        .proof
        .steps
        .iter()
        .map(|step| &step.claim)
        .collect::<Vec<_>>();
    assert!(
        proof
            .iter()
            .any(|line| line.contains("is_transitive") && line.contains("}[Nat](rel)")),
        "expected a proof step to normalize the lambda-valued claim argument: {proof:?}"
    );

    processor
        .check_cert(
            &cert,
            Some(&normalized_goal),
            &normalized_goal.kernel_context,
            &project,
            &bindings,
        )
        .expect("lambda-valued claim argument should verify");
}

#[test]
fn test_parse_code_line_accepts_variable_witness_declaration() {
    let code = r#"
        theorem goal {
            true
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);

    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
    let step = Certificate::parse_code_line(
        "let w0: Bool satisfy { true }",
        &project,
        &mut bindings_cow,
        &mut kernel_context_cow,
    )
    .expect("trivial witness declaration should parse");

    let CertificateStep::Satisfy(step) = step else {
        panic!("expected satisfy step");
    };
    assert_eq!(step.name, "w0");
    assert_eq!(step.arguments.len(), 0);
    assert!(step.return_name.is_none());
    let justification_clause = step
        .justification
        .normalized_specialized_clause(&kernel_context)
        .expect("witness justification should normalize");
    assert_eq!(justification_clause.literals.len(), 1);
    assert!(justification_clause.literals[0]
        .left
        .as_ref()
        .split_exists()
        .is_some());
    assert!(step.witness_clauses.is_empty());
}

#[test]
fn test_from_concrete_steps_uses_claim_with_args_serialization() {
    let code = r#"
        theorem goal {
            false = false
        }
    "#;
    let (_project, bindings, kernel_context) = setup_claim_codec_env(code);
    let kernel = &kernel_context;
    let generic = kernel.parse_clause("x0", &["Bool"]);

    let mut var_map = VariableMap::new();
    var_map.set(0, Term::new_false());
    let concrete_steps = vec![ConcreteStep {
        rationale: ConcreteRationale::Direct,
        generic: generic.clone(),
        var_maps: vec![(var_map, generic.get_local_context().clone())],
        preserve_open: false,
    }];

    let proof = trace_input_codes_from_concrete_steps(&concrete_steps, &kernel_context, &bindings)
        .expect("certificate source lines should be generated");
    assert_eq!(proof.len(), 1);
    assert_eq!(proof[0], "function(x0: Bool) { x0 }(false)");
}

#[test]
fn test_from_concrete_steps_preserves_open_identity_step() {
    let code = r#"
        theorem goal {
            true
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);
    let kernel = &kernel_context;
    let generic = kernel.parse_clause("x0 = x0", &["Bool"]);

    let concrete_steps = vec![ConcreteStep {
        rationale: ConcreteRationale::Direct,
        generic: generic.clone(),
        var_maps: vec![(VariableMap::new(), generic.get_local_context().clone())],
        preserve_open: true,
    }];

    let proof = trace_input_codes_from_concrete_steps(&concrete_steps, &kernel_context, &bindings)
        .expect("certificate source lines should be generated");
    assert_eq!(proof.len(), 1);
    assert!(
        proof[0].contains("forall(x0: Bool)"),
        "open identity step should remain generic: {:?}",
        proof
    );
    assert!(
        !proof[0].contains("function("),
        "open identity step should not be materialized with an inhabitant: {:?}",
        proof
    );

    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
    let step = Certificate::parse_code_line(
        &proof[0],
        &project,
        &mut bindings_cow,
        &mut kernel_context_cow,
    )
    .expect("open identity step should parse");
    let claim = expect_claim(step);
    assert_eq!(claim.var_map().len(), 0);
}

#[test]
fn test_from_concrete_steps_serializes_plain_claim_when_no_local_context() {
    let code = r#"
        theorem goal {
            false
        }
    "#;
    let (_project, bindings, kernel_context) = setup_claim_codec_env(code);
    let kernel = &kernel_context;
    let generic = kernel.parse_clause("false", &[]);

    let concrete_steps = vec![ConcreteStep {
        rationale: ConcreteRationale::Direct,
        generic,
        var_maps: vec![(
            VariableMap::new(),
            crate::kernel::local_context::LocalContext::empty(),
        )],
        preserve_open: false,
    }];

    let proof = trace_input_codes_from_concrete_steps(&concrete_steps, &kernel_context, &bindings)
        .expect("certificate source lines should be generated");
    assert_eq!(proof.len(), 1);
    assert_eq!(proof[0], "false = true");
}

#[test]
fn test_from_concrete_steps_wraps_plain_claims_that_parse_as_statements() {
    use crate::kernel::atom::Atom;
    use crate::kernel::literal::Literal;

    let code = r#"
        theorem goal {
            true
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);
    let generic = Clause::from_literals_unnormalized(
        vec![Literal::positive(Term::and(
            Term::forall(Term::bool_type(), Term::atom(Atom::BoundVariable(0))),
            Term::new_false(),
        ))],
        &LocalContext::empty(),
    );

    let concrete_steps = vec![ConcreteStep {
        rationale: ConcreteRationale::Direct,
        generic,
        var_maps: vec![(
            VariableMap::new(),
            crate::kernel::local_context::LocalContext::empty(),
        )],
        preserve_open: false,
    }];

    let proof = trace_input_codes_from_concrete_steps(&concrete_steps, &kernel_context, &bindings)
        .expect("certificate source lines should be generated");
    assert_eq!(proof.len(), 1);
    assert!(
        proof[0].starts_with('('),
        "ambiguous binder-led claim should be parenthesized: {:?}",
        proof
    );

    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
    let step = Certificate::parse_code_line(
        &proof[0],
        &project,
        &mut bindings_cow,
        &mut kernel_context_cow,
    )
    .expect("parenthesized binder-led claim should parse");
    let claim = expect_claim(step);
    assert_eq!(claim.var_map().len(), 0);
}

#[test]
fn test_from_concrete_steps_rejects_out_of_scope_claim_map() {
    let code = r#"
        theorem goal {
            true
        }
    "#;
    let (_project, bindings, kernel_context) = setup_claim_codec_env(code);
    let kernel = &kernel_context;
    let generic = kernel.parse_clause("x0 = x0", &["Bool"]);

    let mut bad_map = VariableMap::new();
    bad_map.set(0, Term::new_variable(2));
    let replacement_context = LocalContext::from_types(vec![Term::bool_type()]);
    let concrete_steps = vec![ConcreteStep {
        rationale: ConcreteRationale::Direct,
        generic,
        var_maps: vec![(bad_map, replacement_context)],
        preserve_open: false,
    }];

    let err = trace_input_codes_from_concrete_steps(&concrete_steps, &kernel_context, &bindings)
        .expect_err("out-of-scope var maps should fail certificate generation");
    assert!(
        err.to_string().contains("out-of-scope term"),
        "unexpected error: {}",
        err
    );
}

#[test]
fn test_from_concrete_steps_infers_type_arg_from_value_mapping() {
    let code = r#"
        theorem goal {
            true
        }
    "#;
    let (_project, bindings, kernel_context) = setup_claim_codec_env(code);
    let kernel = &kernel_context;
    let generic = kernel.parse_clause("x1 = x1", &["Type", "x0"]);

    let mut var_map = VariableMap::new();
    var_map.set(0, Term::new_variable(0));
    var_map.set(1, Term::new_true());
    let replacement_context = LocalContext::from_types(vec![Term::type_sort(), Term::bool_type()]);
    let concrete_steps = vec![ConcreteStep {
        rationale: ConcreteRationale::Direct,
        generic: generic.clone(),
        var_maps: vec![(var_map, replacement_context)],
        preserve_open: false,
    }];

    let proof = trace_input_codes_from_concrete_steps(&concrete_steps, &kernel_context, &bindings)
        .expect("certificate source lines should be generated");
    assert_eq!(proof.len(), 1);
    assert_eq!(proof[0], "function[T0](x0: T0) { x0 = x0 }[Bool](true)");
}

#[test]
fn test_from_concrete_steps_preserves_surviving_replacement_type_local_kind() {
    use crate::elaborator::names::ConstantName;
    use crate::kernel::atom::Atom;
    use crate::kernel::clause::Clause;
    use crate::kernel::literal::Literal;
    use crate::kernel::local_context::LocalContext;
    use crate::kernel::term::Term;
    use crate::kernel::variable_map::VariableMap;
    use crate::prover::proof::ConcreteStep;

    let code = r#"
        typeclass T: FiniteGroup {
            unit: T
        }

        let g0[T]: Bool -> Bool = axiom
        let g1[T]: T -> Bool = axiom

        theorem goal {
            true
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);

    let module_id = bindings.module_id();
    let g0 = kernel_context
        .symbol_table
        .get_symbol(&ConstantName::Unqualified(module_id, "g0".to_string()))
        .expect("g0 should be bound in the mock module");
    let g1 = kernel_context
        .symbol_table
        .get_symbol(&ConstantName::Unqualified(module_id, "g1".to_string()))
        .expect("g1 should be bound in the mock module");
    let finite_group = kernel_context
        .type_store
        .get_typeclass_id_by_name("FiniteGroup")
        .expect("FiniteGroup should be registered");

    let generic = Clause::new(
        vec![Literal::positive(Term::new(
            Atom::Symbol(g1),
            vec![Term::new_variable(0), Term::new_variable(1)],
        ))],
        &LocalContext::from_types(vec![Term::type_sort(), Term::new_variable(0)]),
    );
    let replacement_context = LocalContext::from_types(vec![Term::typeclass(finite_group)]);

    let mut var_map = VariableMap::new();
    var_map.set(0, Term::bool_type());
    var_map.set(
        1,
        Term::new(
            Atom::Symbol(g0),
            vec![Term::new_variable(0), Term::new_false()],
        ),
    );
    let expected_clause = var_map.specialize_clause_with_replacement_context_and_compact_vars(
        &generic,
        &replacement_context,
        &kernel_context,
    );

    let proof = trace_input_codes_from_concrete_steps(
        &[ConcreteStep {
            rationale: ConcreteRationale::Direct,
            generic,
            var_maps: vec![(var_map, replacement_context.clone())],
            preserve_open: false,
        }],
        &kernel_context,
        &bindings,
    )
    .expect("certificate source lines should be generated");
    assert_eq!(proof.len(), 1);

    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Borrowed(&kernel_context);
    let step = Certificate::parse_code_line(
        &proof[0],
        &project,
        &mut bindings_cow,
        &mut kernel_context_cow,
    )
    .expect("generated claim should parse back");
    let claim = expect_claim(step);
    claim
        .validate_normalized_shape(kernel_context_cow.as_ref())
        .expect("parsed claim should already be normalized");

    assert_eq!(
        claim.clause().get_local_context().get_var_type(1),
        replacement_context.get_var_type(0),
        "parsed claim should preserve the replacement-context typeclass kind"
    );
    assert_eq!(
        claim
            .specialized_clause_for_display(kernel_context_cow.as_ref())
            .expect("parsed claim should specialize"),
        expected_clause,
        "roundtripped claim should still replay to the concrete clause"
    );
}

#[test]
fn test_from_concrete_steps_serializes_partial_logical_builtin_in_claim_map() {
    let code = r#"
        theorem goal {
            true
        }
    "#;
    let (_project, bindings, kernel_context) = setup_claim_codec_env(code);
    let kernel = &kernel_context;
    let generic = kernel.parse_clause("x1(x3, x2)", &["Type", "x0 -> x0 -> Bool", "x0", "x0"]);

    let mut var_map = VariableMap::new();
    var_map.set(0, Term::bool_type());
    var_map.set(1, kernel.parse_term("eq(Bool)"));
    var_map.set(2, Term::new_false());
    var_map.set(3, Term::new_true());
    let concrete_steps = vec![ConcreteStep {
        rationale: ConcreteRationale::Direct,
        generic,
        var_maps: vec![(var_map, LocalContext::empty())],
        preserve_open: false,
    }];

    let proof = trace_input_codes_from_concrete_steps(&concrete_steps, &kernel_context, &bindings)
        .expect("certificate source lines should be generated");
    assert_eq!(
        proof,
        vec![
            "function[T0](x0: (T0, T0) -> Bool, x1: T0, x2: T0) { x0(x1, x2) }[Bool]((=), false, true)"
        ]
    );
}

#[test]
fn test_from_concrete_steps_roundtrips_partial_builtin_used_as_value() {
    let code = r#"
        theorem goal {
            true
        }
    "#;
    let (project, bindings, kernel_context) = setup_claim_codec_env(code);
    let kernel = &kernel_context;
    let generic = kernel.parse_clause(
        "x0(x1) = x1(false, true)",
        &["(Bool -> Bool -> Bool) -> Bool", "Bool -> Bool -> Bool"],
    );

    let mut var_map = VariableMap::new();
    let predicate_type = kernel.type_store.to_type_term_with_vars(
        &crate::elaborator::acorn_type::AcornType::functional(
            vec![
                crate::elaborator::acorn_type::AcornType::Bool,
                crate::elaborator::acorn_type::AcornType::Bool,
            ],
            crate::elaborator::acorn_type::AcornType::Bool,
        ),
        None,
    );
    let predicate = Term::atom(Atom::BoundVariable(0));
    let predicate_application = predicate.apply(&[Term::new_false(), Term::new_true()]);
    var_map.set(0, Term::lambda(predicate_type, predicate_application));
    var_map.set(1, kernel.parse_term("eq(Bool)"));

    let concrete_steps = vec![ConcreteStep {
        rationale: ConcreteRationale::Direct,
        generic,
        var_maps: vec![(var_map, LocalContext::empty())],
        preserve_open: false,
    }];

    let proof = trace_input_codes_from_concrete_steps(&concrete_steps, &kernel_context, &bindings)
        .expect("certificate source lines should be generated");
    assert_eq!(proof.len(), 1);
    assert!(
        proof[0].contains("(=)"),
        "expected partial eq to serialize as an operator ref, got: {}",
        proof[0]
    );

    let reparsed =
        Certificate::deserialize_claim_with_args(&proof[0], &project, &bindings, &kernel_context)
            .expect("serialized claim should parse back");
    let expected_claim = Claim::new(
        concrete_steps[0].generic.clone(),
        concrete_steps[0].var_maps[0].0.clone(),
    )
    .expect("expected claim should normalize");
    let expected_clause = expected_claim
        .normalized_specialized_clause(&kernel_context)
        .expect("expected claim should specialize");
    let reparsed_clause = reparsed
        .normalized_specialized_clause(&kernel_context)
        .expect("reparsed claim should specialize");
    assert_eq!(reparsed_clause, expected_clause);
}

#[test]
fn test_claim_with_args_roundtrip_with_selected_goal_locals() {
    let code = "let f: Bool -> Bool = axiom\n\
let a: Bool = axiom\n\
\n\
theorem goal(k: Bool) {\n\
k = k\n\
} by {\n\
let (d: Bool) satisfy { d = d }\n\
false\n\
}\n";
    let (project, bindings, kernel_context) = setup_selected_goal_env(code, 8);
    let line = "function(x0: Bool, x1: Bool) { f(x0) != f(x1) or (a = x1 and a = x0) }(d, k)";

    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Owned(kernel_context);
    let step =
        Certificate::parse_code_line(line, &project, &mut bindings_cow, &mut kernel_context_cow)
            .expect("claim-with-args line should parse in a goal with local bindings");
    let parsed = expect_claim(step);
    assert_eq!(parsed.var_map().len(), 2);

    let serialized =
        Certificate::serialize_claim_with_args(&parsed, kernel_context_cow.as_ref(), &bindings)
            .expect("parsed claim should serialize again");
    let reparsed = Certificate::parse_code_line(
        &serialized,
        &project,
        &mut bindings_cow,
        &mut kernel_context_cow,
    )
    .expect("serialized claim should parse again");
    let reparsed = expect_claim(reparsed);
    assert_eq!(reparsed, parsed);

    let mut checker = Checker::new();
    checker.insert_clause(
        parsed.clause(),
        StepReason::Testing,
        kernel_context_cow.as_ref(),
    );
    assert!(
        checker
            .check_clause(parsed.clause(), kernel_context_cow.as_ref())
            .is_some(),
        "generic claim should be accepted once inserted"
    );
}

// Regression test for the cert failure at number_theory/dirichlet.ac
// cofactor_image_list_is_unique (2026-07-03, "failed to emit source while writing
// boolean-reduction step"). Replays the certificate input sequence the prover
// generated for that goal, in a miniature vocabulary: the proof unfolds a
// higher-order predicate into a conditional with conjunct hypotheses, then peels
// the hypotheses by unit resolution under the negated goal. Those counterfactual
// intermediates are provable by boolean-reduction reasoning over the eagerly
// saturated closure but are not exact closure members, so claim emission must
// fall back to BrIntro steps; without that fallback the deferrals cascade until
// a later boolean-reduction step hard-fails emitting its source.
#[test]
fn test_trace_writer_serializes_eager_reduction_claims() {
    use crate::certificate_trace::{CertificateTraceInput, ProofTrace};

    let code = r#"
        type Num: axiom
        type Lst: axiom
        let zero: Num = axiom
        let lt: (Num, Num) -> Bool = axiom
        let dl: Num -> Lst = axiom
        let uniq: Lst -> Bool = axiom
        let mem: (Lst, Num) -> Bool = axiom
        let divides: (Num, Num) -> Bool = axiom
        let conc: Lst -> Bool = axiom

        define pred(n: Num) -> (Lst -> Bool) {
            function(l: Lst) {
                uniq(l) and forall(d: Num) { mem(l, d) implies divides(d, n) } and lt(zero, n)
                    implies conc(l)
            }
        }

        axiom pred_thm(n: Num, l: Lst) { pred(n)(l) }
        axiom dl_uniq(n: Num) { uniq(dl(n)) }
        axiom dl_div(n: Num, d: Num) { mem(dl(n), d) implies divides(d, n) }

        theorem goal(n: Num) { lt(zero, n) implies conc(dl(n)) }
    "#;

    let (processor, bindings, normalized_goal) = Processor::test_goal(code);
    let project = Project::new_mock();
    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kctx_cow = Cow::Owned(normalized_goal.kernel_context.clone());

    // The definitional unfolding, used as the boolean-reduction source of step 1.
    let unfold_line = "pred(n)(dl(n)) = (uniq(dl(n)) and forall(d: Num) { mem(dl(n), d) implies divides(d, n) } and lt(zero, n) implies conc(dl(n)))";
    let unfold_step =
        Certificate::parse_code_line(unfold_line, &project, &mut bindings_cow, &mut kctx_cow)
            .expect("unfold line should parse");
    let unfold_clause = expect_claim(unfold_step)
        .normalized_specialized_clause(&kctx_cow)
        .expect("unfold clause");

    let lines = [
        "not (uniq(dl(n)) and forall(x0: Num) { not mem(dl(n), x0) or divides(x0, n) } and lt(zero, n) and not conc(dl(n))) or not pred(n)(dl(n))",
        "not (uniq(dl(n)) and forall(x1: Num) { not mem(dl(n), x1) or divides(x1, n) } and lt(zero, n)) or not pred(n)(dl(n))",
        "not (uniq(dl(n)) and forall(x2: Num) { not mem(dl(n), x2) or divides(x2, n) }) or not pred(n)(dl(n))",
        "not forall(x3: Num) { not mem(dl(n), x3) or divides(x3, n) } or not uniq(dl(n))",
        "not uniq(dl(n)) or exists(k0: Num) { mem(dl(n), k0) and not divides(k0, n) }",
        "exists(k1: Num) { mem(dl(n), k1) and not divides(k1, n) }",
        "let w0: Num satisfy { mem(dl(n), w0) and not divides(w0, n) }",
        "mem(dl(n), w0) and not divides(w0, n)",
        "not divides(w0, n)",
        "mem(dl(n), w0)",
        "function(x0: Num) { not mem(dl(n), x0) or divides(x0, n) }(w0)",
        "not mem(dl(n), w0)",
    ];

    let mut steps = Vec::new();
    for line in &lines {
        let step = Certificate::parse_code_line(line, &project, &mut bindings_cow, &mut kctx_cow)
            .unwrap_or_else(|err| panic!("line should parse: {} ({})", line, err));
        steps.push((step, line.to_string()));
    }

    let claim_clause = |index: usize, steps: &[(CertificateStep, String)]| {
        let CertificateStep::Claim(claim) = &steps[index].0 else {
            panic!("expected claim at index {}", index);
        };
        claim
            .normalized_specialized_clause(&kctx_cow)
            .expect("claim clause")
    };

    let source_s4 = claim_clause(3, &steps);
    let source_s8 = claim_clause(7, &steps);

    let mut inputs = Vec::new();
    for (index, (step, line)) in steps.into_iter().enumerate() {
        let source = match index {
            0 => Some(unfold_clause.clone()),
            4 => Some(source_s4.clone()),
            8 | 9 => Some(source_s8.clone()),
            _ => None,
        };
        inputs.push(CertificateTraceInput {
            step,
            code: line,
            boolean_reduction_source: source,
        });
    }

    let mut checker = processor.checker().clone();
    checker
        .insert_lowered_goal(&normalized_goal)
        .expect("goal should insert");
    // The by-block context facts, as the dirichlet proof had them: the unfold
    // equation instance, the established hypotheses, and the applied predicate.
    // The forall hypothesis is only available in opened clause form, the way the
    // real by-block produced it: generic over d, never as a term-level equality.
    let mut context_facts = Vec::new();
    {
        let step = Certificate::parse_code_line(
            "function(x0: Num) { not mem(dl(n), x0) or divides(x0, n) }(zero)",
            &project,
            &mut bindings_cow,
            &mut kctx_cow,
        )
        .expect("opened forall fact should parse");
        context_facts.push(expect_claim(step).normalized_generic_clause());
    }
    for fact_line in [unfold_line, "uniq(dl(n))", "pred(n)(dl(n))"] {
        let step =
            Certificate::parse_code_line(fact_line, &project, &mut bindings_cow, &mut kctx_cow)
                .unwrap_or_else(|err| panic!("fact should parse: {} ({})", fact_line, err));
        let claim = expect_claim(step);
        context_facts.push(claim.normalized_generic_clause());
        context_facts.push(
            claim
                .normalized_specialized_clause(&kctx_cow)
                .expect("fact clause"),
        );
    }
    for fact in &context_facts {
        checker.insert_clause(fact, crate::kernel::checker::StepReason::Testing, &kctx_cow);
    }
    // The writer re-parses satisfy lines itself, so it needs pristine contexts,
    // not the ones the test used to pre-parse the inputs.
    let result = ProofTrace::from_certificate_steps_checked(
        &inputs,
        checker,
        &project,
        Cow::Borrowed(&bindings),
        Cow::Owned(normalized_goal.kernel_context.clone()),
    );
    let trace = match result {
        Ok(trace) => trace,
        Err(err) => panic!("trace write failed: {}", err),
    };

    // The written trace must also replay through the trace checker, with the same
    // starting knowledge the writer had.
    let mut replay_checker = processor.checker().clone();
    replay_checker
        .insert_lowered_goal(&normalized_goal)
        .expect("goal should insert for replay");
    for fact in &context_facts {
        replay_checker.insert_clause(
            fact,
            crate::kernel::checker::StepReason::Testing,
            &normalized_goal.kernel_context,
        );
    }
    trace
        .check_with_usage(
            replay_checker,
            &project,
            Cow::Borrowed(&bindings),
            Cow::Owned(normalized_goal.kernel_context.clone()),
        )
        .expect("written trace should replay");
}

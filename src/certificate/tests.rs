use super::*;
use crate::module::LoadState;
use crate::processor::Processor;
use std::borrow::Cow;
use tempfile::tempdir;

/// Unwrap a parsed test step that is expected to be a claim.
fn expect_claim(step: CertificateStep) -> Claim {
    let CertificateStep::Claim(claim) = step else {
        panic!("expected certificate claim step");
    };
    claim
}

#[test]
fn test_save_load_cycle() {
    // Create a temporary directory for testing
    let temp_dir = tempdir().unwrap();
    let file_path = temp_dir.path().join("test_certs.jsonl");

    // Create some test certificates
    let cert1 = Certificate::new(
        "goal1".to_string(),
        vec!["step1".to_string(), "step2".to_string()],
    );
    let cert2 = Certificate::new(
        "goal2".to_string(),
        vec![
            "step3".to_string(),
            "step4".to_string(),
            "step5".to_string(),
        ],
    );
    let cert3 = Certificate::new(
        "goal3".to_string(),
        vec![], // Trivial proof with no steps
    );
    let cert4 = Certificate::placeholder(
        "goal4".to_string(), // No proof exists for this goal
    );

    // Create original certificate store
    let original = CertificateStore {
        certs: vec![cert1, cert2, cert3, cert4],
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
    }

    // Test has_proof() helper on loaded certificates
    assert!(loaded.certs[0].has_proof());
    assert!(loaded.certs[1].has_proof());
    assert!(loaded.certs[2].has_proof());
    assert!(!loaded.certs[3].has_proof());

    // Clean up is automatic when temp_dir goes out of scope
}

fn setup_claim_codec_env(code: &str) -> (Project, BindingMap, KernelContext) {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", code);

    let module_id = project
        .load_module_by_name("main")
        .expect("module should load");
    let (bindings, kernel_context) = {
        let env = match project.get_module_by_id(module_id) {
            LoadState::Ok(env) => env,
            LoadState::Error(e) => panic!("module loading error: {}", e),
            _ => panic!("unexpected module load state"),
        };
        let kernel_context = env
            .kernel_context
            .clone()
            .expect("environment should have a kernel context");
        (env.bindings.clone(), kernel_context)
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
        let env = match project.get_module_by_id(module_id) {
            LoadState::Ok(env) => env,
            LoadState::Error(e) => panic!("module loading error: {}", e),
            _ => panic!("unexpected module load state"),
        };
        let node_path = env
            .path_for_line(line - 1)
            .expect("selected line should resolve to a node path");
        let cursor = crate::elaborator::node::NodeCursor::from_path(env, &node_path);
        let normalized_goal = cursor
            .lowered_goal()
            .expect("selected line should have a lowered goal");
        (
            cursor.bindings().clone(),
            normalized_goal.kernel_context.clone(),
        )
    };

    (project, bindings, kernel_context)
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

    if cfg!(feature = "nwit") {
        let err =
            Certificate::deserialize_claim_with_args(line, &project, &bindings, &kernel_context)
                .expect_err("nwit should reject choose in claim-with-args deserialization");
        assert!(
            err.to_string()
                .contains("choose expressions are not allowed here"),
            "unexpected error: {}",
            err
        );
        return;
    }

    let claim =
        Certificate::deserialize_claim_with_args(line, &project, &bindings, &kernel_context)
            .expect("deserialization should preserve a single not-if literal");

    assert_eq!(claim.clause().get_local_context().len(), 1);
    assert_eq!(claim.var_map().len(), 1);

    let serialized = Certificate::serialize_claim_with_args(&claim, &kernel_context, &bindings)
        .expect("serialization should succeed");
    assert!(serialized.contains("not if"));
    let reparsed =
        Certificate::deserialize_claim_with_args(&serialized, &project, &bindings, &kernel_context)
            .expect("serialized claim should deserialize again");
    assert_eq!(reparsed, claim);
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
    let env = match project.get_module_by_id(module_id) {
        LoadState::Ok(env) => env,
        LoadState::Error(e) => panic!("module loading error: {}", e),
        _ => panic!("unexpected module load state"),
    };
    let cursor = env.get_node_by_goal_name("goal");
    let normalized_facts = cursor
        .visible_lowered_facts()
        .expect("lowered facts should be available");
    let bindings = cursor
        .goal_env()
        .expect("goal env should be available")
        .bindings
        .clone();
    let kernel_context = env
        .kernel_context
        .clone()
        .expect("environment should have a kernel context");

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

    if cfg!(feature = "nwit") {
        let err = match result {
            Ok(_) => panic!("nwit should reject choose claims"),
            Err(err) => err,
        };
        assert!(
            err.to_string()
                .contains("choose expressions are not allowed here"),
            "unexpected error: {}",
            err
        );
        return;
    }

    let step = result.expect("choose claim parsing should succeed for certificate parsing");

    let claim = expect_claim(step);
    assert_eq!(claim.var_map().len(), 0);
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

    if cfg!(feature = "nwit") {
        let err = match result {
            Ok(_) => panic!("nwit should reject choose in closed binder-heavy claims"),
            Err(err) => err,
        };
        assert!(
            err.to_string()
                .contains("choose expressions are not allowed here"),
            "unexpected error: {}",
            err
        );
        return;
    }

    let step = result.expect("closed binder-heavy claim should parse");

    let claim = expect_claim(step);
    assert_eq!(claim.var_map().len(), 0);
    assert!(claim.clause().get_local_context().is_empty());
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

    if cfg!(feature = "nwit") {
        let err = match result {
            Ok(_) => panic!("nwit should reject choose claims before checking"),
            Err(err) => err,
        };
        assert!(
            err.to_string()
                .contains("choose expressions are not allowed here"),
            "unexpected error: {}",
            err
        );
        return;
    }

    let step = result.expect("choose claim parsing should succeed for certificate parsing");

    let mut checker = Checker::new();
    let err = checker
        .check_cert_steps(&[step], None, &kernel_context)
        .expect_err("arbitrary choose claim should not be accepted");
    assert!(
        err.to_string().contains("not obviously true"),
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
        .prover()
        .make_cert(&bindings, &normalized_goal.kernel_context, false)
        .expect("lambda-valued cert should be generated");
    let proof = cert.proof.as_ref().expect("proof should exist");
    assert!(
        proof
            .iter()
            .any(|line| { line.contains("is_transitive") && line.contains("}[Nat](function(") }),
        "expected a proof step to preserve the lambda-valued claim argument: {proof:?}"
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
        generic: generic.clone(),
        var_maps: vec![(var_map, generic.get_local_context().clone())],
    }];

    let cert = Certificate::from_concrete_steps(
        "goal".to_string(),
        &concrete_steps,
        &kernel_context,
        &bindings,
    )
    .expect("certificate generation should succeed");
    let proof = cert.proof.expect("proof should exist");
    assert_eq!(proof.len(), 1);
    assert_eq!(proof[0], "function(x0: Bool) { x0 }(false)");
}

#[cfg(not(feature = "nwit"))]
#[test]
fn test_from_concrete_steps_handles_binder_claim_args() {
    let code = r#"
        theorem goal {
            true
        }
    "#;
    let (_project, bindings, kernel_context) = setup_claim_codec_env(code);
    let kernel = &kernel_context;
    let generic = kernel.parse_clause("x0", &["Bool"]);

    let mut var_map = VariableMap::new();
    var_map.set(
        0,
        Term::choose(
            Term::bool_type(),
            Term::lambda(Term::bool_type(), Term::atom(Atom::BoundVariable(0))),
        ),
    );
    let concrete_steps = vec![ConcreteStep {
        generic: generic.clone(),
        var_maps: vec![(var_map, generic.get_local_context().clone())],
    }];

    let result = Certificate::from_concrete_steps(
        "goal".to_string(),
        &concrete_steps,
        &kernel_context,
        &bindings,
    );

    if cfg!(feature = "nwit") {
        let err = result.expect_err("nwit should reject choose during certificate generation");
        assert!(
            err.to_string()
                .contains("choose expressions are not supported with feature \"nwit\""),
            "unexpected error: {}",
            err
        );
        return;
    }

    let cert = result.expect("certificate generation should succeed");
    let proof = cert.proof.expect("proof should exist");
    assert_eq!(proof.len(), 1);
    assert_eq!(
        proof[0],
        "function(x0: Bool) { x0 }(choose(k0: Bool) { k0 })"
    );
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
        generic,
        var_maps: vec![(
            VariableMap::new(),
            crate::kernel::local_context::LocalContext::empty(),
        )],
    }];

    let cert = Certificate::from_concrete_steps(
        "goal".to_string(),
        &concrete_steps,
        &kernel_context,
        &bindings,
    )
    .expect("certificate generation should succeed");
    let proof = cert.proof.expect("proof should exist");
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
        generic,
        var_maps: vec![(
            VariableMap::new(),
            crate::kernel::local_context::LocalContext::empty(),
        )],
    }];

    let cert = Certificate::from_concrete_steps(
        "goal".to_string(),
        &concrete_steps,
        &kernel_context,
        &bindings,
    )
    .expect("certificate generation should succeed");
    let proof = cert.proof.expect("proof should exist");
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
    bad_map.set(0, Term::new_variable(1));
    let replacement_context = LocalContext::from_types(vec![Term::bool_type(), Term::type_sort()]);
    let concrete_steps = vec![ConcreteStep {
        generic,
        var_maps: vec![(bad_map, replacement_context)],
    }];

    let err = Certificate::from_concrete_steps(
        "goal".to_string(),
        &concrete_steps,
        &kernel_context,
        &bindings,
    )
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
        generic: generic.clone(),
        var_maps: vec![(var_map, replacement_context)],
    }];

    let cert = Certificate::from_concrete_steps(
        "goal".to_string(),
        &concrete_steps,
        &kernel_context,
        &bindings,
    )
    .expect("certificate generation should succeed");
    let proof = cert.proof.expect("proof should exist");
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

    let cert = Certificate::from_concrete_steps(
        "goal".to_string(),
        &[ConcreteStep {
            generic,
            var_maps: vec![(var_map, replacement_context.clone())],
        }],
        &kernel_context,
        &bindings,
    )
    .expect("certificate generation should succeed");
    let proof = cert.proof.expect("proof should exist");
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
        claim.clause().get_local_context().get_var_type(0),
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
        generic,
        var_maps: vec![(var_map, LocalContext::empty())],
    }];

    let cert = Certificate::from_concrete_steps(
        "goal".to_string(),
        &concrete_steps,
        &kernel_context,
        &bindings,
    )
    .expect("certificate generation should succeed");
    let proof = cert.proof.expect("proof should exist");
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
        generic,
        var_maps: vec![(var_map, LocalContext::empty())],
    }];

    let cert = Certificate::from_concrete_steps(
        "goal".to_string(),
        &concrete_steps,
        &kernel_context,
        &bindings,
    )
    .expect("certificate generation should succeed");
    let proof = cert.proof.expect("proof should exist");
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

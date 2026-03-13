use crate::certificate::Certificate;
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::names::DefinedName;
use crate::elaborator::to_term::lower_value_to_term_existing;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::proof_step::{ProofStep, Rule, Truthiness};
use crate::kernel::term::Term;
use crate::kernel::term_normalization::normalize_term;
use crate::kernel::variable_map::VariableMap;
use crate::module::{LoadState, ModuleId};
use crate::project::Project;
use crate::prover::active_set::ActiveSet;
use crate::prover::proof::ConcreteStep;
use crate::prover::synthetic::WitnessRegistry;
use std::borrow::Cow;

// Add new normalization regressions by appending a row to the case tables below.
// Each row is intentionally small: a mock module snippet for term/clause/cert tests,
// or a pair of kernel clauses for prover-step generation.

struct DefinitionCase {
    name: &'static str,
    code: &'static str,
}

struct CertLineCase {
    name: &'static str,
    code: &'static str,
    line: &'static str,
}

struct ClaimRoundtripCase {
    name: &'static str,
    code: &'static str,
    build: fn(&KernelContext) -> crate::kernel::certificate_step::Claim,
}

struct ProverClauseInput {
    clause: &'static str,
    var_types: &'static [&'static str],
    truthiness: Truthiness,
}

#[derive(Clone, Copy)]
enum ExpectedRule {
    Resolution,
    Rewrite,
    EqualityFactoring,
    Injectivity,
    Extensionality,
}

struct ProverPairCase {
    name: &'static str,
    setup: fn(&mut KernelContext),
    left: ProverClauseInput,
    right: ProverClauseInput,
    expected_rules: &'static [ExpectedRule],
}

const TERM_CASES: &[DefinitionCase] = &[
    DefinitionCase {
        name: "double_negation_and_equality_ordering",
        code: r#"
            let target: Bool = not not (true = false)
        "#,
    },
    DefinitionCase {
        name: "beta_reduction_through_lambda_application",
        code: r#"
            let target: Bool =
                function(x: Bool) {
                    not not x
                }(false)
        "#,
    },
    DefinitionCase {
        name: "nested_function_beta_reduction",
        code: r#"
            type Nat: axiom
            let zero: Nat = axiom

            let target: Nat =
                function(f: Nat -> Nat) {
                    f(zero)
                }(function(x: Nat) { x })
        "#,
    },
];

const CLAUSE_CASES: &[DefinitionCase] = &[
    DefinitionCase {
        name: "forall_or_clause",
        code: r#"
            let target: Bool = forall(x: Bool) { x = true or x = false }
        "#,
    },
    DefinitionCase {
        name: "higher_order_inequality_literal",
        code: r#"
            type Foo: axiom
            let a: Foo = axiom
            let f: Foo -> Foo = axiom
            let g: Foo -> (Foo -> Foo) = axiom

            let target: Bool = forall(x: Foo) { g(x) != f }
        "#,
    },
    DefinitionCase {
        name: "literal_subterm_normalization",
        code: r#"
            type Nat: axiom
            let zero: Nat = axiom
            let suc: Nat -> Nat = axiom

            let target: Bool = forall(x: Nat) {
                not not (suc(x) != zero) or zero = x
            }
        "#,
    },
];

const CERT_LINE_CASES: &[CertLineCase] = &[
    CertLineCase {
        name: "plain_equality_claim",
        code: r#"
            theorem goal {
                true
            }
        "#,
        line: "true = false",
    },
    CertLineCase {
        name: "claim_with_normalized_argument_term",
        code: r#"
            theorem goal {
                true
            }
        "#,
        line: "function(x0: Bool) { x0 }(not not false)",
    },
    CertLineCase {
        name: "claim_with_type_and_value_args",
        code: r#"
            theorem goal {
                true
            }
        "#,
        line: "function[T0](x0: T0) { x0 = x0 }[Bool](true)",
    },
    CertLineCase {
        name: "higher_order_inequality_claim",
        code: r#"
            type Foo: axiom
            let a: Foo = axiom
            let f: Foo -> Foo = axiom
            let g: Foo -> (Foo -> Foo) = axiom

            theorem goal {
                true
            }
        "#,
        line: "function(x0: Foo) { g(x0) != f }(a)",
    },
];

fn build_claim_with_dependent_value_arg(
    kernel_context: &KernelContext,
) -> crate::kernel::certificate_step::Claim {
    let clause = kernel_context.parse_clause("x0 = x1", &["Bool", "Bool"]);
    let mut var_map = VariableMap::new();
    var_map.set(0, Term::new_false());
    var_map.set(1, Term::new_variable(0));
    crate::kernel::certificate_step::Claim::new(clause, var_map).expect("claim should normalize")
}

const CLAIM_ROUNDTRIP_CASES: &[ClaimRoundtripCase] = &[ClaimRoundtripCase {
    name: "dependent_value_arg",
    code: r#"
        theorem goal {
            true
        }
    "#,
    build: build_claim_with_dependent_value_arg,
}];

fn setup_bool_resolution(kernel_context: &mut KernelContext) {
    kernel_context.parse_constants(&["c0", "c1", "c2"], "Bool");
}

fn setup_bool_rewrite(kernel_context: &mut KernelContext) {
    kernel_context
        .parse_constant("g0", "(Bool, Bool) -> Bool")
        .parse_constants(&["c1", "c2", "c3", "c4"], "Bool");
}

fn setup_factoring(kernel_context: &mut KernelContext) {
    kernel_context.parse_datatype("Foo");
    kernel_context.parse_constants(&["c0", "c1"], "Foo");
}

fn setup_injectivity(kernel_context: &mut KernelContext) {
    kernel_context
        .parse_constant("g0", "(Bool, Bool) -> Bool")
        .parse_constants(&["c0", "c1", "c2"], "Bool");
}

fn setup_extensionality(kernel_context: &mut KernelContext) {
    kernel_context.parse_constants(&["g0", "g1"], "Bool -> Bool");
}

const PROVER_PAIR_CASES: &[ProverPairCase] = &[
    ProverPairCase {
        name: "pairwise_resolution",
        setup: setup_bool_resolution,
        left: ProverClauseInput {
            clause: "c0 = c1",
            var_types: &[],
            truthiness: Truthiness::Factual,
        },
        right: ProverClauseInput {
            clause: "c0 != c1 or c2",
            var_types: &[],
            truthiness: Truthiness::Counterfactual,
        },
        expected_rules: &[ExpectedRule::Resolution],
    },
    ProverPairCase {
        name: "pairwise_rewrite",
        setup: setup_bool_rewrite,
        left: ProverClauseInput {
            clause: "c1 = c3",
            var_types: &[],
            truthiness: Truthiness::Factual,
        },
        right: ProverClauseInput {
            clause: "g0(c3, c4) = c2",
            var_types: &[],
            truthiness: Truthiness::Counterfactual,
        },
        expected_rules: &[ExpectedRule::Rewrite],
    },
    ProverPairCase {
        name: "self_equality_factoring",
        setup: setup_factoring,
        left: ProverClauseInput {
            clause: "x0 = c0 or x1 = c0",
            var_types: &["Foo", "Foo"],
            truthiness: Truthiness::Factual,
        },
        right: ProverClauseInput {
            clause: "c1 = c1",
            var_types: &[],
            truthiness: Truthiness::Counterfactual,
        },
        expected_rules: &[ExpectedRule::EqualityFactoring],
    },
    ProverPairCase {
        name: "self_injectivity",
        setup: setup_injectivity,
        left: ProverClauseInput {
            clause: "g0(c0, x0) != g0(c1, x0) or c2",
            var_types: &["Bool"],
            truthiness: Truthiness::Factual,
        },
        right: ProverClauseInput {
            clause: "c0 = c0",
            var_types: &[],
            truthiness: Truthiness::Counterfactual,
        },
        expected_rules: &[ExpectedRule::Injectivity],
    },
    ProverPairCase {
        name: "self_extensionality",
        setup: setup_extensionality,
        left: ProverClauseInput {
            clause: "g0(x0) = g1(x0)",
            var_types: &["Bool"],
            truthiness: Truthiness::Factual,
        },
        right: ProverClauseInput {
            clause: "g0(true) = g1(true)",
            var_types: &[],
            truthiness: Truthiness::Counterfactual,
        },
        expected_rules: &[ExpectedRule::Extensionality],
    },
];

fn assert_term_is_already_normalized(term: &Term, case_name: &str, label: &str) {
    assert_eq!(
        *term,
        normalize_term(term),
        "{label} should already be term-normalized for case `{case_name}`"
    );
}

fn assert_clause_is_already_normalized(
    clause: &crate::kernel::clause::Clause,
    case_name: &str,
    label: &str,
) {
    assert_eq!(
        *clause,
        clause.normalized(),
        "{label} should already be clause-normalized for case `{case_name}`"
    );
}

fn assert_claim_is_already_normalized(
    claim: &crate::kernel::certificate_step::Claim,
    kernel_context: &KernelContext,
    case_name: &str,
    label: &str,
) {
    assert_eq!(
        claim.clause().clone(),
        claim.clause().normalized_preserving_locals(),
        "{label} generic clause should preserve normalized local slots for case `{case_name}`"
    );
    for (var_id, term) in claim.var_map().iter() {
        assert_term_is_already_normalized(term, case_name, &format!("{label} claim arg x{var_id}"));
    }

    let specialized = claim
        .normalized_specialized_clause(kernel_context)
        .expect("claim specialization should succeed");
    assert_clause_is_already_normalized(
        &specialized,
        case_name,
        &format!("{label} specialized clause"),
    );
}

fn load_mock_module(code: &str) -> (Project, BindingMap, KernelContext) {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", code);

    let module_id = project
        .load_module_by_name("main")
        .expect("module should load");
    let (bindings, kernel_context) = match project.get_module_by_id(module_id) {
        LoadState::Ok(env) => (
            env.bindings.clone(),
            env.kernel_context
                .clone()
                .expect("environment should have a kernel context"),
        ),
        LoadState::Error(error) => panic!("module loading error: {}", error),
        _ => panic!("unexpected module load state"),
    };

    (project, bindings, kernel_context)
}

fn load_target_value(code: &str) -> (KernelContext, AcornValue) {
    let (_project, bindings, kernel_context) = load_mock_module(code);
    let target_name = DefinedName::unqualified(bindings.module_id(), "target");
    let value = bindings
        .get_definition(&target_name)
        .cloned()
        .expect("expected a `target` definition");
    (kernel_context, value)
}

fn load_target_term(code: &str) -> (KernelContext, Term) {
    let (mut kernel_context, value) = load_target_value(code);
    value.validate().expect("target value should validate");
    let term = lower_value_to_term_existing(&mut kernel_context, &value, None)
        .expect("target should lower to a term");
    (kernel_context, term)
}

fn load_target_clause(code: &str) -> (KernelContext, AcornValue) {
    load_target_value(code)
}

fn parse_claim_line(
    code: &str,
    line: &str,
) -> (
    Project,
    BindingMap,
    KernelContext,
    crate::kernel::certificate_step::Claim,
) {
    let (project, bindings, kernel_context) = load_mock_module(code);
    let mut bindings_cow = Cow::Borrowed(&bindings);
    let mut kernel_context_cow = Cow::Owned(kernel_context.clone());
    let step =
        Certificate::parse_code_line(line, &project, &mut bindings_cow, &mut kernel_context_cow)
            .expect("certificate line should parse");
    let crate::kernel::certificate_step::CertificateStep::Claim(claim) = step else {
        panic!("expected a claim line");
    };
    (project, bindings, kernel_context, claim)
}

fn serialize_claim_line(
    claim: &crate::kernel::certificate_step::Claim,
    bindings: &BindingMap,
    kernel_context: &KernelContext,
) -> String {
    let concrete_steps = vec![ConcreteStep {
        generic: claim.clause().clone(),
        var_maps: vec![(
            claim.var_map().clone(),
            claim.clause().get_local_context().clone(),
        )],
    }];
    let cert = Certificate::from_concrete_steps(
        "goal".to_string(),
        &concrete_steps,
        kernel_context,
        bindings,
    )
    .expect("claim should serialize through certificate generation");
    let mut proof = cert
        .proof
        .expect("claim certificate should have one proof line");
    assert_eq!(proof.len(), 1, "expected one serialized proof line");
    proof.pop().unwrap()
}

fn step_from_input(input: &ProverClauseInput, kernel_context: &KernelContext) -> ProofStep {
    let clause = kernel_context.parse_clause(input.clause, input.var_types);
    let mut step = ProofStep::mock_from_clause(clause);
    step.truthiness = input.truthiness;
    step
}

fn generated_steps_for_pair(case: &ProverPairCase) -> Vec<ProofStep> {
    let mut all_steps = vec![];
    for order in [[&case.left, &case.right], [&case.right, &case.left]] {
        let mut kernel_context = KernelContext::new();
        (case.setup)(&mut kernel_context);
        let mut active_set = ActiveSet::new();
        let mut witness_registry = WitnessRegistry::new();

        let first = step_from_input(order[0], &kernel_context);
        let second = step_from_input(order[1], &kernel_context);

        let (_, first_outputs) = active_set.activate(
            first,
            &mut kernel_context,
            &mut witness_registry,
            ModuleId::default(),
        );
        all_steps.extend(first_outputs);

        let (_, second_outputs) = active_set.activate(
            second,
            &mut kernel_context,
            &mut witness_registry,
            ModuleId::default(),
        );
        all_steps.extend(second_outputs);
    }
    all_steps
}

fn step_matches_rule(step: &ProofStep, expected: ExpectedRule) -> bool {
    matches!(
        (&step.rule, expected),
        (Rule::Resolution(_), ExpectedRule::Resolution)
            | (Rule::Rewrite(_), ExpectedRule::Rewrite)
            | (Rule::EqualityFactoring(_), ExpectedRule::EqualityFactoring)
            | (Rule::Injectivity(_), ExpectedRule::Injectivity)
            | (Rule::Extensionality(_), ExpectedRule::Extensionality)
    )
}

#[test]
fn test_term_normalization_cases() {
    for case in TERM_CASES {
        let (kernel_context, term) = load_target_term(case.code);
        let normalized = normalize_term(&term);
        assert_term_is_already_normalized(&normalized, case.name, "normalized term");

        let quoted =
            kernel_context.quote_term_with_context(&normalized, &LocalContext::empty(), false);
        quoted
            .validate()
            .expect("quoted normalized term should validate");

        let mut roundtrip_context = kernel_context.clone();
        let lowered_again = lower_value_to_term_existing(&mut roundtrip_context, &quoted, None)
            .expect("quoted normalized term should lower again");
        assert_term_is_already_normalized(&lowered_again, case.name, "roundtripped term");
        assert_eq!(
            normalized, lowered_again,
            "quoted normalized term should roundtrip exactly for case `{}`",
            case.name
        );
    }
}

#[test]
fn test_clause_normalization_cases() {
    use crate::kernel::symbol_table::NewConstantType;

    for case in CLAUSE_CASES {
        let (mut kernel_context, value) = load_target_clause(case.code);
        value
            .validate()
            .expect("target clause value should validate");
        let clause = kernel_context
            .lower_clause(&value, NewConstantType::Local, None)
            .expect("target should lower to a clause");

        assert_clause_is_already_normalized(&clause, case.name, "lowered clause");

        let quoted = kernel_context.quote_clause(&clause, None, None, false);
        quoted.validate().expect("quoted clause should validate");
        let lowered_again = kernel_context
            .lower_clause(&quoted, NewConstantType::Local, None)
            .expect("quoted clause should lower again");
        assert_clause_is_already_normalized(&lowered_again, case.name, "roundtripped clause");
        assert_eq!(
            clause, lowered_again,
            "normalized clause should satisfy quote/lower roundtrip for case `{}`",
            case.name
        );
    }
}

#[test]
fn test_cert_line_normalization_cases() {
    for case in CERT_LINE_CASES {
        let (_project, bindings, kernel_context, claim) = parse_claim_line(case.code, case.line);
        assert_claim_is_already_normalized(&claim, &kernel_context, case.name, "parsed");

        let serialized = serialize_claim_line(&claim, &bindings, &kernel_context);
        let (_project2, _bindings2, _kernel2, reparsed) = parse_claim_line(case.code, &serialized);
        assert_claim_is_already_normalized(&reparsed, &kernel_context, case.name, "reparsed");
        assert_eq!(
            claim, reparsed,
            "serialized claim should parse back to the same canonical claim for case `{}`",
            case.name
        );

        let serialized_again = serialize_claim_line(&reparsed, &bindings, &kernel_context);
        assert_eq!(
            serialized, serialized_again,
            "claim serialization should be idempotent for case `{}`",
            case.name
        );
    }
}

#[test]
fn test_claim_roundtrip_normalization_cases() {
    for case in CLAIM_ROUNDTRIP_CASES {
        let (_project, bindings, kernel_context) = load_mock_module(case.code);
        let claim = (case.build)(&kernel_context);
        assert_claim_is_already_normalized(&claim, &kernel_context, case.name, "constructed");

        let serialized = serialize_claim_line(&claim, &bindings, &kernel_context);
        let (_project2, _bindings2, _kernel2, reparsed) = parse_claim_line(case.code, &serialized);
        assert_claim_is_already_normalized(&reparsed, &kernel_context, case.name, "reparsed");
        assert_eq!(
            reparsed, claim,
            "claim serialization should preserve canonical claim for case `{}`",
            case.name,
        );
    }
}

#[test]
fn test_prover_generated_steps_are_normalized() {
    for case in PROVER_PAIR_CASES {
        let generated = generated_steps_for_pair(case);
        assert!(
            !generated.is_empty(),
            "expected prover pair case `{}` to generate at least one step",
            case.name
        );

        for expected_rule in case.expected_rules {
            assert!(
                generated
                    .iter()
                    .any(|step| step_matches_rule(step, *expected_rule)),
                "expected prover pair case `{}` to exercise its target rule",
                case.name
            );
        }

        for step in &generated {
            assert_eq!(
                step.clause,
                step.clause.normalized_preserving_locals(),
                "generated step from case `{}` should have a normalized clause: {}",
                case.name,
                step.clause
            );
        }
    }
}

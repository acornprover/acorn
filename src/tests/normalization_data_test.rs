use crate::certificate::Certificate;
use crate::elaborator::acorn_type::{AcornType, TypeParam};
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::names::ConstantName;
use crate::elaborator::names::DefinedName;
use crate::elaborator::to_term::{
    lower_value_to_term_existing, lower_value_to_term_existing_preserving_alias_spelling,
};
use crate::kernel::atom::Atom;
use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::proof_step::{ProofStep, ProofStepId, Rule, Truthiness};
use crate::kernel::symbol_table::NewConstantType;
use crate::kernel::term::Term;
use crate::kernel::term_normalization::normalize_term;
use crate::kernel::variable_map::VariableMap;
use crate::module::{LoadState, ModuleId};
use crate::project::Project;
use crate::prover::active_set::ActiveSet;
use crate::prover::proof::{ConcreteStep, Proof};
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
    build: fn(&Project, &BindingMap, &KernelContext) -> crate::kernel::certificate_step::Claim,
}

struct KernelTermRoundtripCase {
    name: &'static str,
    build: fn(&mut KernelContext) -> Term,
}

struct KernelClauseRoundtripCase {
    name: &'static str,
    build: fn(&mut KernelContext) -> crate::kernel::clause::Clause,
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

struct ProofReconstructionCase {
    name: &'static str,
    build: fn(&mut KernelContext) -> (Vec<(ProofStepId, ProofStep)>, Vec<Clause>),
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
    DefinitionCase {
        name: "eta_reduction_of_partial_application",
        code: r#"
            type Nat: axiom
            type Val: axiom
            let f: (Nat, Nat) -> Val = axiom
            let i: Nat = axiom

            let target: Nat -> Val =
                function(j: Nat) {
                    f(i, j)
                }
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
        name: "plain_quantified_higher_order_inequality",
        code: r#"
            type Foo: axiom
            let f: Foo -> Foo = axiom
            let g: Foo -> (Foo -> Foo) = axiom

            theorem goal {
                true
            }
        "#,
        line: "(forall(x0: Foo) { g(x0) != f })",
    },
    CertLineCase {
        name: "plain_false_claim",
        code: r#"
            theorem goal {
                true
            }
        "#,
        line: "false",
    },
    CertLineCase {
        name: "plain_negated_exists_claim",
        code: r#"
            theorem goal {
                true
            }
        "#,
        line: "not exists(k0: Bool, k1: Bool) { k0 = k1 }",
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
    _project: &Project,
    _bindings: &BindingMap,
    kernel_context: &KernelContext,
) -> crate::kernel::certificate_step::Claim {
    let clause = kernel_context.parse_clause("x0 = x1", &["Bool", "Bool"]);
    let mut var_map = VariableMap::new();
    var_map.set(0, Term::new_false());
    var_map.set(1, Term::new_variable(0));
    crate::kernel::certificate_step::Claim::new(clause, var_map).expect("claim should normalize")
}

fn build_claim_with_unmapped_bool_local(
    _project: &Project,
    _bindings: &BindingMap,
    kernel_context: &KernelContext,
) -> crate::kernel::certificate_step::Claim {
    let clause = kernel_context.parse_clause("x0 = x0", &["Bool"]);
    crate::kernel::certificate_step::Claim::new(clause, VariableMap::new())
        .expect("claim should normalize")
}

fn build_claim_with_unmapped_negated_bool_local(
    _project: &Project,
    _bindings: &BindingMap,
    kernel_context: &KernelContext,
) -> crate::kernel::certificate_step::Claim {
    let clause = kernel_context.parse_clause("x0 != true", &["Bool"]);
    crate::kernel::certificate_step::Claim::new(clause, VariableMap::new())
        .expect("claim should normalize")
}

fn build_claim_with_unmapped_type_local(
    project: &Project,
    bindings: &BindingMap,
    kernel_context: &KernelContext,
) -> crate::kernel::certificate_step::Claim {
    Certificate::deserialize_claim_with_args(
        "function[T0] { foo[T0] }",
        project,
        bindings,
        kernel_context,
    )
    .expect("claim should deserialize")
}

fn build_claim_with_concrete_type_local(
    project: &Project,
    bindings: &BindingMap,
    kernel_context: &KernelContext,
) -> crate::kernel::certificate_step::Claim {
    Certificate::deserialize_claim_with_args(
        "function[T0] { foo[T0] }[Bool]",
        project,
        bindings,
        kernel_context,
    )
    .expect("claim should deserialize")
}

fn build_claim_with_type_param_and_capturing_lambda_arg(
    project: &Project,
    bindings: &BindingMap,
    kernel_context: &KernelContext,
) -> crate::kernel::certificate_step::Claim {
    Certificate::deserialize_claim_with_args(
        "function[T0](x0: T0, x1: T0 -> Bool) { x1(x0) }[Bool](true, function(y0: Bool) { y0 = x0 })",
        project,
        bindings,
        kernel_context,
    )
    .expect("claim should deserialize")
}

const CLAIM_ROUNDTRIP_CASES: &[ClaimRoundtripCase] = &[
    ClaimRoundtripCase {
        name: "dependent_value_arg",
        code: r#"
            theorem goal {
                true
            }
        "#,
        build: build_claim_with_dependent_value_arg,
    },
    ClaimRoundtripCase {
        name: "unmapped_bool_local",
        code: r#"
            theorem goal {
                true
            }
        "#,
        build: build_claim_with_unmapped_bool_local,
    },
    ClaimRoundtripCase {
        name: "unmapped_negated_bool_local",
        code: r#"
            theorem goal {
                true
            }
        "#,
        build: build_claim_with_unmapped_negated_bool_local,
    },
    ClaimRoundtripCase {
        name: "unmapped_type_local",
        code: r#"
            let foo[T]: Bool = axiom

            theorem goal {
                foo[Bool]
            }
        "#,
        build: build_claim_with_unmapped_type_local,
    },
    ClaimRoundtripCase {
        name: "concrete_type_local",
        code: r#"
            let foo[T]: Bool = axiom

            theorem goal {
                foo[Bool]
            }
        "#,
        build: build_claim_with_concrete_type_local,
    },
    ClaimRoundtripCase {
        name: "type_param_lambda_arg_captures_prior_local",
        code: r#"
            theorem goal {
                true
            }
        "#,
        build: build_claim_with_type_param_and_capturing_lambda_arg,
    },
];

const KERNEL_TERM_ROUNDTRIP_CASES: &[KernelTermRoundtripCase] = &[];

/// Builds a normalized clause whose preserved type parameter sits in a non-prefix slot, which
/// exercises the sparse-local roundtrip bug seen in `finite_set`.
fn build_clause_with_nonprefix_type_param(
    kernel_context: &mut KernelContext,
) -> crate::kernel::clause::Clause {
    let (_project, bindings, loaded_context) = load_mock_module(
        r#"
            type Foo: axiom
            type Bar: axiom

            structure Box[T] {
                value: T
            }

            let g0[U]: (Bar, Foo) -> Bool = axiom
            let g1[T]: (T, Bar) -> Box[T] = axiom
            let g2[T]: (T, T, Foo) -> Bool = axiom

            theorem goal {
                true
            }
        "#,
    );
    *kernel_context = loaded_context;
    let module_id = bindings.module_id();

    let g0 = kernel_context
        .symbol_table
        .get_symbol(&ConstantName::unqualified(module_id, "g0"))
        .expect("g0 should be registered");
    let g1 = kernel_context
        .symbol_table
        .get_symbol(&ConstantName::unqualified(module_id, "g1"))
        .expect("g1 should be registered");
    let g2 = kernel_context
        .symbol_table
        .get_symbol(&ConstantName::unqualified(module_id, "g2"))
        .expect("g2 should be registered");
    let g0_type = kernel_context
        .symbol_table
        .get_symbol_type(g0, &kernel_context.type_store);
    let (_, g0_after_type) = g0_type
        .as_ref()
        .split_pi()
        .expect("g0 should take a leading type argument");
    let (bar_type, g0_after_bar) = g0_after_type
        .split_pi()
        .expect("g0 should take a Bar argument");
    let (foo_type, _) = g0_after_bar
        .split_pi()
        .expect("g0 should take a Foo argument");

    // x0 is a value local of fixed type Foo, but x1 is a preserved type parameter
    // that appears later in the local context. This mirrors the finite_set panic:
    // quote/lower must preserve the sparse local ordering exactly even when an inline
    // boolean literal nests polymorphic applications under eq/and/not.
    let context = LocalContext::from_types(vec![
        foo_type.to_owned(),
        Term::type_sort(),
        kernel_context.parse_type("x1"),
        kernel_context.parse_type("x1"),
        bar_type.to_owned(),
    ]);
    let x0 = Term::new_variable(0);
    let x1 = Term::new_variable(1);
    let x2 = Term::new_variable(2);
    let x3 = Term::new_variable(3);
    let x4 = Term::new_variable(4);

    let left = Term::atom(Atom::Symbol(g0)).apply(&[foo_type.to_owned(), x4.clone(), x0.clone()]);
    let right_left = Term::atom(Atom::Symbol(g1)).apply(&[x1.clone(), x2.clone(), x4.clone()]);
    let right_right = Term::atom(Atom::Symbol(g1)).apply(&[x1.clone(), x3.clone(), x4.clone()]);
    let boxed_eq_type = right_left
        .checked_type_with_context(&context, kernel_context)
        .expect("g1 application should have a type");
    let boxed_eq = Term::eq(boxed_eq_type, right_left, right_right);
    let guard = Term::and(left, Term::not(boxed_eq));
    let conclusion = Term::atom(Atom::Symbol(g2)).apply(&[x1, x2, x3, x0]);

    crate::kernel::clause::Clause::from_literals_unnormalized(
        vec![Literal::negative(guard), Literal::positive(conclusion)],
        &context,
    )
    .normalized_preserving_locals()
}

/// Builds the fully-peeled polymorphic equality that extensionality can emit so normalization
/// tests cover bare generic heads without value arguments.
fn build_clause_with_bare_polymorphic_constant_equality(
    kernel_context: &mut KernelContext,
) -> crate::kernel::clause::Clause {
    let (_project, bindings, loaded_context) = load_mock_module(
        r#"
            let f[T]: T -> T = axiom
            let g[T]: T -> T = axiom

            theorem goal {
                true
            }
        "#,
    );
    *kernel_context = loaded_context;
    let module_id = bindings.module_id();

    let f = kernel_context
        .symbol_table
        .get_symbol(&ConstantName::unqualified(module_id, "f"))
        .expect("f should be registered");
    let g = kernel_context
        .symbol_table
        .get_symbol(&ConstantName::unqualified(module_id, "g"))
        .expect("g should be registered");

    crate::kernel::clause::Clause::from_literals_unnormalized(
        vec![Literal::equals(
            Term::atom(Atom::Symbol(f)),
            Term::atom(Atom::Symbol(g)),
        )],
        &LocalContext::empty(),
    )
    .normalized_preserving_locals()
}

/// Builds a clause with a partially applied builtin `and` under another binder so quote/lower
/// validation checks the partial-builtin path instead of only full applications.
fn build_clause_with_partial_and_under_outer_binder(
    kernel_context: &mut KernelContext,
) -> crate::kernel::clause::Clause {
    let (_project, bindings, loaded_context) = load_mock_module(
        r#"
            let g[T]: (T, T -> Bool) -> Bool = axiom

            theorem goal {
                true
            }
        "#,
    );
    *kernel_context = loaded_context;
    let module_id = bindings.module_id();
    let g = kernel_context
        .symbol_table
        .get_symbol(&ConstantName::unqualified(module_id, "g"))
        .expect("g should be registered");
    let x0 = Term::new_variable(0);
    let partial_and = Term::atom(Atom::Symbol(crate::kernel::symbol::Symbol::And))
        .apply(std::slice::from_ref(&x0));

    crate::kernel::clause::Clause::from_literals_unnormalized(
        vec![Literal::positive(Term::atom(Atom::Symbol(g)).apply(&[
            Term::bool_type(),
            x0,
            partial_and,
        ]))],
        &LocalContext::from_types(vec![Term::bool_type()]),
    )
    .normalized_preserving_locals()
}

fn build_clause_with_head_lambda_application(
    _kernel_context: &mut KernelContext,
) -> crate::kernel::clause::Clause {
    let applied_lambda = Term::lambda(Term::bool_type(), Term::atom(Atom::BoundVariable(0)))
        .apply(&[Term::new_variable(0)]);

    crate::kernel::clause::Clause::from_literals_unnormalized(
        vec![Literal::positive(applied_lambda)],
        &LocalContext::from_types(vec![Term::bool_type()]),
    )
    .normalized_preserving_locals()
}

/// Builds a clause whose local context still carries an unused trailing variable while a bare
/// logical builtin is passed as a value. This mirrors a reverse-reprove validate panic where the
/// quote path synthesized lambda variables past the actually visible outer binders.
fn build_clause_with_unused_trailing_local_and_bare_and_value(
    kernel_context: &mut KernelContext,
) -> crate::kernel::clause::Clause {
    add_named_global_constant(
        kernel_context,
        "g0",
        "Bool -> ((Bool, Bool) -> Bool) -> Bool",
    );
    let g0 = kernel_context
        .symbol_table
        .get_symbol(&ConstantName::unqualified(ModuleId(0), "g0"))
        .expect("g0 should be registered");
    let x0 = Term::new_variable(0);
    let bare_and = Term::atom(Atom::Symbol(crate::kernel::symbol::Symbol::And));

    crate::kernel::clause::Clause::from_literals_unnormalized(
        vec![Literal::positive(
            Term::atom(Atom::Symbol(g0)).apply(&[x0, bare_and]),
        )],
        &LocalContext::from_types(vec![Term::bool_type(), Term::bool_type()]),
    )
    .normalized_preserving_locals()
}

fn build_clause_with_false_disjunct_literal(
    kernel_context: &mut KernelContext,
) -> crate::kernel::clause::Clause {
    add_named_global_constant(kernel_context, "g0", "Bool -> Bool");
    let g0 = kernel_context
        .symbol_table
        .get_symbol(&ConstantName::unqualified(ModuleId(0), "g0"))
        .expect("g0 should be registered");

    crate::kernel::clause::Clause::from_literals_unnormalized(
        vec![
            Literal::negative(Term::atom(Atom::Symbol(g0)).apply(&[Term::new_variable(0)])),
            Literal::positive(Term::new_false()),
        ],
        &LocalContext::from_types(vec![Term::bool_type()]),
    )
    .normalized_preserving_locals()
}

fn build_clause_with_single_false_literal(
    _kernel_context: &mut KernelContext,
) -> crate::kernel::clause::Clause {
    crate::kernel::clause::Clause::from_literals_unnormalized(
        vec![Literal::positive(Term::new_false())],
        &LocalContext::empty(),
    )
    .normalized_preserving_locals()
}

const KERNEL_CLAUSE_ROUNDTRIP_CASES: &[KernelClauseRoundtripCase] = &[
    KernelClauseRoundtripCase {
        name: "false_disjunct_literal",
        build: build_clause_with_false_disjunct_literal,
    },
    KernelClauseRoundtripCase {
        name: "single_false_literal",
        build: build_clause_with_single_false_literal,
    },
    KernelClauseRoundtripCase {
        name: "partial_and_argument_under_outer_binder",
        build: build_clause_with_partial_and_under_outer_binder,
    },
    KernelClauseRoundtripCase {
        name: "bare_and_value_with_unused_trailing_local",
        build: build_clause_with_unused_trailing_local_and_bare_and_value,
    },
    KernelClauseRoundtripCase {
        name: "bare_polymorphic_constant_equality",
        build: build_clause_with_bare_polymorphic_constant_equality,
    },
    KernelClauseRoundtripCase {
        name: "nonprefix_type_param_local",
        build: build_clause_with_nonprefix_type_param,
    },
    KernelClauseRoundtripCase {
        name: "head_lambda_application",
        build: build_clause_with_head_lambda_application,
    },
];

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

fn build_passive_contradiction_inhabited_instance_case(
    kernel_context: &mut KernelContext,
) -> (Vec<(ProofStepId, ProofStep)>, Vec<Clause>) {
    kernel_context.parse_constant("g0", "Bool -> Bool");

    let positive = ProofStep::mock_from_clause(kernel_context.parse_clause("g0(x0)", &["Bool"]));
    let negative =
        ProofStep::mock_from_clause(kernel_context.parse_clause("not g0(x0)", &["Bool"]));
    let final_step = ProofStep::passive_contradiction(&[positive.clone(), negative.clone()]);
    let witness = kernel_context
        .find_inhabitant(&Term::bool_type(), None)
        .expect("Bool should be inhabited");

    (
        vec![
            (ProofStepId::Passive(0), positive),
            (ProofStepId::Passive(1), negative),
            (ProofStepId::Final, final_step),
        ],
        vec![
            Clause::new(
                vec![Literal::positive(
                    kernel_context.parse_term("g0").apply(&[witness.clone()]),
                )],
                &LocalContext::empty(),
            ),
            Clause::new(
                vec![Literal::negative(
                    kernel_context.parse_term("g0").apply(&[witness]),
                )],
                &LocalContext::empty(),
            ),
        ],
    )
}

const PROOF_RECONSTRUCTION_CASES: &[ProofReconstructionCase] = &[ProofReconstructionCase {
    name: "passive_contradiction_inhabited_instance",
    build: build_passive_contradiction_inhabited_instance_case,
}];

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

fn add_named_global_constant(kernel_context: &mut KernelContext, name: &str, type_str: &str) {
    let constant_name = ConstantName::unqualified(ModuleId(0), name);
    let type_term = kernel_context.parse_type(type_str);
    kernel_context
        .symbol_table
        .add_constant(constant_name, NewConstantType::Global, type_term);
}

fn add_named_local_constant(kernel_context: &mut KernelContext, name: &str, type_str: &str) {
    let constant_name = ConstantName::unqualified(ModuleId(0), name);
    let type_term = kernel_context.parse_type(type_str);
    kernel_context
        .symbol_table
        .add_constant(constant_name, NewConstantType::Local, type_term);
}

fn add_named_polymorphic_global_constant(
    kernel_context: &mut KernelContext,
    name: &str,
    binders: &str,
    body: &str,
    type_param_names: &[&str],
) {
    let constant_name = ConstantName::unqualified(ModuleId(0), name);
    let type_term = kernel_context.parse_pi(binders, body);
    let generated_generic_type = kernel_context
        .type_store
        .type_term_to_acorn_type(&type_term);
    let renamings: Vec<(String, AcornType)> = type_param_names
        .iter()
        .enumerate()
        .map(|(i, name)| {
            (
                format!("T{}", i),
                AcornType::Variable(TypeParam {
                    name: (*name).to_string(),
                    typeclass: None,
                }),
            )
        })
        .collect();
    let generic_type = generated_generic_type.instantiate(&renamings);
    kernel_context.symbol_table.add_constant(
        constant_name.clone(),
        NewConstantType::Global,
        type_term,
    );
    kernel_context.symbol_table.set_polymorphic_info(
        constant_name,
        generic_type,
        type_param_names
            .iter()
            .map(|name| name.to_string())
            .collect(),
    );
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
    if claim.clause().get_local_context().is_empty() {
        let concrete_steps = vec![ConcreteStep {
            generic: claim.clause().clone(),
            var_maps: vec![(
                claim.var_map().clone(),
                crate::kernel::local_context::LocalContext::empty(),
            )],
        }];
        let cert = Certificate::from_concrete_steps(
            "goal".to_string(),
            &concrete_steps,
            kernel_context,
            bindings,
        )
        .expect("claim should serialize through concrete-step generation");
        let mut proof = cert
            .proof
            .expect("claim certificate should have one proof line");
        assert_eq!(proof.len(), 1, "expected one serialized proof line");
        return proof.pop().unwrap();
    }

    Certificate::serialize_claim_step_for_test(claim, kernel_context, bindings)
        .expect("claim should serialize through claim-step serialization")
}

fn serialize_claim_with_args_line(
    claim: &crate::kernel::certificate_step::Claim,
    bindings: &BindingMap,
    kernel_context: &KernelContext,
) -> String {
    Certificate::serialize_claim_with_args(claim, kernel_context, bindings)
        .expect("claim should serialize through direct claim codec")
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
fn test_kernel_term_roundtrip_cases() {
    for case in KERNEL_TERM_ROUNDTRIP_CASES {
        let mut kernel_context = KernelContext::new();
        let term = (case.build)(&mut kernel_context);
        assert_term_is_already_normalized(&term, case.name, "constructed term");

        let quoted = kernel_context.quote_term_with_context(&term, &LocalContext::empty(), false);
        quoted
            .validate()
            .expect("quoted kernel term should validate");

        let roundtripped = lower_value_to_term_existing_preserving_alias_spelling(
            &mut kernel_context,
            &quoted,
            None,
        )
        .expect("quoted kernel term should lower again");
        assert_term_is_already_normalized(&roundtripped, case.name, "roundtripped term");
        assert_eq!(
            term, roundtripped,
            "quoted kernel term should roundtrip exactly for case `{}`",
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
        let (project, bindings, kernel_context) = load_mock_module(case.code);
        let claim = (case.build)(&project, &bindings, &kernel_context);
        assert_claim_is_already_normalized(&claim, &kernel_context, case.name, "constructed");

        let serialized = serialize_claim_with_args_line(&claim, &bindings, &kernel_context);
        let (_project2, _bindings2, _kernel2, reparsed) = parse_claim_line(case.code, &serialized);
        assert_claim_is_already_normalized(&reparsed, &kernel_context, case.name, "reparsed");
        assert_eq!(
            reparsed, claim,
            "claim serialization should preserve canonical claim for case `{}`",
            case.name,
        );

        let serialized_again =
            serialize_claim_with_args_line(&reparsed, &bindings, &kernel_context);
        assert_eq!(
            serialized, serialized_again,
            "claim roundtrip serialization should be idempotent for case `{}`",
            case.name
        );
    }
}

#[test]
/// Verifies the exact normalized `(clause, locals)` roundtrip contract on hand-built kernel
/// clauses that previously only showed up during project-wide check/reprove runs.
fn test_kernel_clause_roundtrip_cases() {
    for case in KERNEL_CLAUSE_ROUNDTRIP_CASES {
        let mut kernel_context = KernelContext::new();
        let clause = (case.build)(&mut kernel_context);
        assert_eq!(
            clause,
            clause.normalized_preserving_locals(),
            "constructed clause should already be normalized-preserving-locals for case `{}`",
            case.name
        );
        kernel_context
            .validate_clause_roundtrip(&clause)
            .expect("kernel clause should satisfy quote/lower roundtrip");
    }
}

#[cfg(feature = "kfc")]
#[test]
fn test_kernel_clause_roundtrip_closed_singleton_positive_forall_literal() {
    let mut kernel_context = KernelContext::new();
    add_named_global_constant(&mut kernel_context, "g0", "Bool -> Bool");

    let clause = Clause::from_literals_unnormalized(
        vec![Literal::positive(Term::forall(
            Term::bool_type(),
            kernel_context
                .parse_term("g0")
                .apply(&[Term::atom(Atom::BoundVariable(0))]),
        ))],
        &LocalContext::empty(),
    )
    .normalized_preserving_locals();

    assert_eq!(
        clause,
        clause.normalized_preserving_locals(),
        "constructed closed singleton forall clause should be internally normalized before the roundtrip check"
    );
    kernel_context.validate_clause_roundtrip(&clause).expect(
        "closed singleton positive forall literal should satisfy the normalized clause quote/lower roundtrip",
    );
}

#[cfg(feature = "kfc")]
#[test]
fn test_kfc_clause_lowering_distinguishes_bare_and_eq_true_forall() {
    use crate::kernel::symbol_table::NewConstantType;

    let (mut kernel_context, bare_value) = load_target_clause(
        r#"
            let g0: Bool -> Bool = axiom
            let target: Bool = forall(x: Bool) { g0(x) }
        "#,
    );
    let bare_clause = kernel_context
        .lower_clause(&bare_value, NewConstantType::Local, None)
        .expect("bare forall should lower to a clause");
    assert_eq!(bare_clause.context.len(), 1);
    assert_eq!(bare_clause.literals.len(), 1);
    assert!(
        !matches!(
            bare_clause.literals[0].left.as_ref().decompose(),
            crate::kernel::term::Decomposition::ForAll(_, _)
        ),
        "bare forall should open into the clause context"
    );

    let (mut kernel_context, eq_true_value) = load_target_clause(
        r#"
            let g0: Bool -> Bool = axiom
            let target: Bool = forall(x: Bool) { g0(x) } = true
        "#,
    );
    let eq_true_clause = kernel_context
        .lower_clause(&eq_true_value, NewConstantType::Local, None)
        .expect("forall = true should lower to a clause");
    assert_eq!(eq_true_clause.context.len(), 0);
    assert_eq!(eq_true_clause.literals.len(), 1);
    assert!(
        matches!(
            eq_true_clause.literals[0].left.as_ref().decompose(),
            crate::kernel::term::Decomposition::ForAll(_, _)
        ),
        "forall = true should remain a closed literal-headed forall term"
    );
}

#[cfg(feature = "kfc")]
#[test]
fn test_kernel_clause_roundtrip_open_clause_with_closed_inner_forall_literal() {
    let mut kernel_context = KernelContext::new();
    add_named_global_constant(&mut kernel_context, "g0", "(Bool, Bool) -> Bool");
    let g0 = kernel_context
        .symbol_table
        .get_symbol(&ConstantName::unqualified(ModuleId(0), "g0"))
        .expect("g0 should be registered");
    let outer_x = Term::new_variable(0);
    let inner_x = Term::atom(Atom::BoundVariable(0));
    let inner_body = Term::atom(Atom::Symbol(crate::kernel::symbol::Symbol::Not))
        .apply(&[Term::atom(Atom::Symbol(g0)).apply(&[outer_x, inner_x])]);
    let clause = Clause::from_literals_unnormalized(
        vec![Literal::positive(Term::forall(
            Term::bool_type(),
            inner_body,
        ))],
        &LocalContext::from_types(vec![Term::bool_type()]),
    )
    .normalized_preserving_locals();

    assert_eq!(
        clause,
        clause.normalized_preserving_locals(),
        "constructed clause should already be normalized-preserving-locals before the roundtrip check"
    );
    kernel_context.validate_clause_roundtrip(&clause).expect(
        "an open outer clause with a closed inner forall literal should satisfy the normalized clause quote/lower roundtrip",
    );
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

#[test]
fn test_proof_reconstruction_normalization_cases() {
    for case in PROOF_RECONSTRUCTION_CASES {
        let mut kernel_context = KernelContext::new();
        let (steps, expected_clauses) = (case.build)(&mut kernel_context);

        let mut proof = Proof::new(&kernel_context);
        for (id, step) in &steps {
            proof.add_step(*id, step);
        }

        let concrete_proof = proof
            .make_concrete_proof("goal".to_string())
            .expect("proof reconstruction should succeed");
        assert!(
            !concrete_proof.claims.is_empty(),
            "expected proof reconstruction case `{}` to produce at least one claim",
            case.name
        );

        for clause in &concrete_proof.claims {
            assert_clause_is_already_normalized(clause, case.name, "reconstructed clause");
        }

        for expected_clause in &expected_clauses {
            assert!(
                concrete_proof.claims.contains(expected_clause),
                "expected proof reconstruction case `{}` to include concrete clause {}\nactual clauses:\n{}",
                case.name,
                expected_clause,
                concrete_proof
                    .claims
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join("\n")
            );
        }
    }
}

#[test]
fn test_internal_clause_roundtrip_parametric_bool_symbolic_shape() {
    let mut kernel_context = KernelContext::new();
    kernel_context.parse_type_constructor("Box", 1);
    add_named_polymorphic_global_constant(
        &mut kernel_context,
        "g0",
        "T: Type",
        "Box[T] -> T -> Bool",
        &["T"],
    );
    add_named_polymorphic_global_constant(
        &mut kernel_context,
        "g1",
        "T: Type",
        "Box[T] -> T -> Box[T]",
        &["T"],
    );
    add_named_local_constant(&mut kernel_context, "c0", "Bool");
    add_named_local_constant(&mut kernel_context, "c1", "Bool");

    let clause = kernel_context
        .parse_clause(
            "not g0(Bool, x0, c0) or g0(Bool, g1(Bool, x0, c1), c0)",
            &["Box[Bool]"],
        )
        .normalized_preserving_locals();
    assert_clause_is_already_normalized(
        &clause,
        "parametric_bool_symbolic_shape",
        "internal clause",
    );
    kernel_context.validate_clause_roundtrip(&clause).expect(
        "quoted parametric symbolic clause should lower back to the same normalized clause",
    );
}

#[test]
fn test_extensionality_roundtrip_parametric_constructor_head() {
    let mut kernel_context = KernelContext::new();
    kernel_context.parse_type_constructor("Box", 1);
    add_named_polymorphic_global_constant(
        &mut kernel_context,
        "g0",
        "T: Type",
        "T -> Box[T]",
        &["T"],
    );
    add_named_global_constant(&mut kernel_context, "g1", "Bool -> Box[Bool]");

    let clause = kernel_context.parse_clause("g0(Bool, x0) = g1(x0)", &["Bool"]);
    let literals = clause
        .find_extensionality(&kernel_context)
        .expect("expected parametric constructor clause to admit extensionality");
    let clause = crate::kernel::clause::Clause::new(literals, clause.get_local_context())
        .normalized_preserving_locals();
    assert_clause_is_already_normalized(
        &clause,
        "parametric_constructor_head",
        "extensionality clause",
    );
    kernel_context
        .validate_clause_roundtrip(&clause)
        .expect("quoted extensionality clause should lower back to the same normalized clause");
}

use std::collections::HashSet;

use ndarray::{Array1, Array2, Axis};

use crate::elaborator::source::SourceType;
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::proof_step::{ProofStep, Rule, ShallowStatus, Truthiness};
use crate::kernel::symbol::Symbol;

// Features of a proof step that can be used to score it.
// This is like a feature vector but in struct rather than vector form.
// Try to only use bools, i32s, and f32s.
pub struct Features {
    pub is_contradiction: bool,
    pub is_shallow: bool,
    pub shallow_status: ShallowStatus,

    // Features from the clause
    pub atom_count: i32,
    pub literal_count: i32,
    pub positive_literal_count: i32,
    pub negative_literal_count: i32,
    pub signed_literal_count: i32,
    pub equality_literal_count: i32,
    pub context_variable_count: i32,
    pub context_type_sort_count: i32,
    pub context_typeclass_count: i32,
    pub distinct_free_variable_count: i32,
    pub free_variable_atom_count: i32,
    pub bound_variable_atom_count: i32,
    pub scoped_constant_atom_count: i32,
    pub global_constant_atom_count: i32,
    pub type_atom_count: i32,
    pub typeclass_atom_count: i32,
    pub bool_value_atom_count: i32,
    pub logical_symbol_atom_count: i32,
    pub has_any_variable: bool,
    pub has_scoped_constant: bool,

    // Features from truthiness
    pub is_counterfactual: bool,
    pub is_hypothetical: bool,
    pub is_factual: bool,

    // Features from the rule
    pub is_assumption: bool,
    pub is_negated_goal: bool,
    pub is_generated: bool,
    pub rule_premise_count: i32,
    pub rule_is_direct_assumption: bool,
    pub rule_is_resolution: bool,
    pub rule_is_rewrite: bool,
    pub rule_is_specialization: bool,
    pub rule_is_equality_factoring: bool,
    pub rule_is_equality_resolution: bool,
    pub rule_is_injectivity: bool,
    pub rule_is_boolean_reduction: bool,
    pub rule_is_extensionality: bool,
    pub rule_is_multiple_rewrite: bool,
    pub rule_is_passive_contradiction: bool,
    pub rule_is_simplification: bool,
    pub source_is_axiom: bool,
    pub source_is_theorem: bool,
    pub source_is_lemma: bool,
    pub source_is_anonymous: bool,
    pub source_is_type_definition: bool,
    pub source_is_constant_definition: bool,
    pub source_is_extends: bool,
    pub source_is_instance: bool,
    pub source_is_premise: bool,
    pub source_is_negated_goal: bool,
    pub source_is_block_goal: bool,
    pub source_is_importable: bool,
    pub source_depth: i32,

    // Features from the search process
    pub proof_size: i32,
    pub depth: i32,
}

impl Default for Features {
    fn default() -> Self {
        Features {
            is_contradiction: false,
            is_shallow: false,
            shallow_status: ShallowStatus::Deep,
            atom_count: 0,
            literal_count: 0,
            positive_literal_count: 0,
            negative_literal_count: 0,
            signed_literal_count: 0,
            equality_literal_count: 0,
            context_variable_count: 0,
            context_type_sort_count: 0,
            context_typeclass_count: 0,
            distinct_free_variable_count: 0,
            free_variable_atom_count: 0,
            bound_variable_atom_count: 0,
            scoped_constant_atom_count: 0,
            global_constant_atom_count: 0,
            type_atom_count: 0,
            typeclass_atom_count: 0,
            bool_value_atom_count: 0,
            logical_symbol_atom_count: 0,
            has_any_variable: false,
            has_scoped_constant: false,
            is_counterfactual: false,
            is_hypothetical: false,
            is_factual: false,
            is_assumption: false,
            is_negated_goal: false,
            is_generated: false,
            rule_premise_count: 0,
            rule_is_direct_assumption: false,
            rule_is_resolution: false,
            rule_is_rewrite: false,
            rule_is_specialization: false,
            rule_is_equality_factoring: false,
            rule_is_equality_resolution: false,
            rule_is_injectivity: false,
            rule_is_boolean_reduction: false,
            rule_is_extensionality: false,
            rule_is_multiple_rewrite: false,
            rule_is_passive_contradiction: false,
            rule_is_simplification: false,
            source_is_axiom: false,
            source_is_theorem: false,
            source_is_lemma: false,
            source_is_anonymous: false,
            source_is_type_definition: false,
            source_is_constant_definition: false,
            source_is_extends: false,
            source_is_instance: false,
            source_is_premise: false,
            source_is_negated_goal: false,
            source_is_block_goal: false,
            source_is_importable: false,
            source_depth: 0,
            proof_size: 0,
            depth: 0,
        }
    }
}

pub const FEATURE_CATALOG_NAMES: [&str; 60] = [
    "is_contradiction",
    "atom_count",
    "is_counterfactual",
    "is_hypothetical",
    "is_factual",
    "is_assumption",
    "is_negated_goal",
    "proof_size",
    "depth",
    "is_shallow",
    "shallow_status_deep",
    "shallow_status_spent",
    "shallow_status_unspent",
    "shallow_status_contradiction",
    "literal_count",
    "positive_literal_count",
    "negative_literal_count",
    "signed_literal_count",
    "equality_literal_count",
    "context_variable_count",
    "context_type_sort_count",
    "context_typeclass_count",
    "distinct_free_variable_count",
    "free_variable_atom_count",
    "bound_variable_atom_count",
    "scoped_constant_atom_count",
    "global_constant_atom_count",
    "type_atom_count",
    "typeclass_atom_count",
    "bool_value_atom_count",
    "logical_symbol_atom_count",
    "has_any_variable",
    "has_scoped_constant",
    "is_generated",
    "rule_premise_count",
    "rule_is_direct_assumption",
    "rule_is_resolution",
    "rule_is_rewrite",
    "rule_is_specialization",
    "rule_is_equality_factoring",
    "rule_is_equality_resolution",
    "rule_is_injectivity",
    "rule_is_boolean_reduction",
    "rule_is_extensionality",
    "rule_is_multiple_rewrite",
    "rule_is_passive_contradiction",
    "rule_is_simplification",
    "source_is_axiom",
    "source_is_theorem",
    "source_is_lemma",
    "source_is_anonymous",
    "source_is_type_definition",
    "source_is_constant_definition",
    "source_is_extends",
    "source_is_instance",
    "source_is_premise",
    "source_is_negated_goal",
    "source_is_block_goal",
    "source_is_importable",
    "source_depth",
];

struct AtomCounts {
    distinct_free_variables: HashSet<AtomId>,
    free_variables: i32,
    bound_variables: i32,
    scoped_constants: i32,
    global_constants: i32,
    types: i32,
    typeclasses: i32,
    bool_values: i32,
    logical_symbols: i32,
}

impl AtomCounts {
    fn new(step: &ProofStep) -> Self {
        let mut counts = AtomCounts {
            distinct_free_variables: HashSet::new(),
            free_variables: 0,
            bound_variables: 0,
            scoped_constants: 0,
            global_constants: 0,
            types: 0,
            typeclasses: 0,
            bool_values: 0,
            logical_symbols: 0,
        };
        for atom in step.clause.iter_atoms() {
            counts.record(atom);
        }
        counts
    }

    fn record(&mut self, atom: &Atom) {
        match atom {
            Atom::FreeVariable(id) => {
                self.distinct_free_variables.insert(*id);
                self.free_variables += 1;
            }
            Atom::BoundVariable(_) => {
                self.bound_variables += 1;
            }
            Atom::Symbol(symbol) => match symbol {
                Symbol::ScopedConstant(_) => self.scoped_constants += 1,
                Symbol::GlobalConstant(_, _) => self.global_constants += 1,
                Symbol::Bool | Symbol::Type0 | Symbol::Type(_) => self.types += 1,
                Symbol::Typeclass(_) => self.typeclasses += 1,
                Symbol::True | Symbol::False => self.bool_values += 1,
                Symbol::Not | Symbol::And | Symbol::Or | Symbol::Eq | Symbol::Ite => {
                    self.logical_symbols += 1;
                }
            },
        }
    }
}

#[derive(Default)]
struct SourceFeatures {
    is_axiom: bool,
    is_theorem: bool,
    is_lemma: bool,
    is_anonymous: bool,
    is_type_definition: bool,
    is_constant_definition: bool,
    is_extends: bool,
    is_instance: bool,
    is_premise: bool,
    is_negated_goal: bool,
    is_block_goal: bool,
    is_importable: bool,
    depth: i32,
}

impl SourceFeatures {
    fn new(rule: &Rule) -> Self {
        let Rule::Assumption(info) = rule else {
            return Self::default();
        };
        let mut features = SourceFeatures {
            is_importable: info.source.importable,
            depth: info.source.depth as i32,
            ..Self::default()
        };
        match &info.source.source_type {
            SourceType::Axiom(_) => features.is_axiom = true,
            SourceType::Theorem(_) => features.is_theorem = true,
            SourceType::Lemma(_) => features.is_lemma = true,
            SourceType::Anonymous => features.is_anonymous = true,
            SourceType::TypeDefinition(_, _) => features.is_type_definition = true,
            SourceType::ConstantDefinition(_, _) => features.is_constant_definition = true,
            SourceType::Extends(_) => features.is_extends = true,
            SourceType::Instance(_, _) => features.is_instance = true,
            SourceType::Premise => features.is_premise = true,
            SourceType::NegatedGoal => features.is_negated_goal = true,
            SourceType::BlockGoal => features.is_block_goal = true,
        }
        features
    }
}

impl Features {
    pub fn new(step: &ProofStep) -> Self {
        let literal_count = step.clause.literals.len() as i32;
        let positive_literal_count = step
            .clause
            .literals
            .iter()
            .filter(|literal| literal.positive)
            .count() as i32;
        let signed_literal_count = step
            .clause
            .literals
            .iter()
            .filter(|literal| literal.is_signed_term())
            .count() as i32;
        let atom_counts = AtomCounts::new(step);
        let context_type_sort_count = step
            .clause
            .context
            .get_var_types()
            .iter()
            .filter(|var_type| {
                var_type
                    .as_ref()
                    .is_some_and(|term| term.as_ref().is_type0())
            })
            .count() as i32;
        let context_typeclass_count = step
            .clause
            .context
            .get_var_types()
            .iter()
            .filter(|var_type| {
                var_type
                    .as_ref()
                    .is_some_and(|term| term.as_ref().as_typeclass().is_some())
            })
            .count() as i32;
        let source = SourceFeatures::new(&step.rule);
        Features {
            is_contradiction: step.clause.is_impossible(),
            is_shallow: step.is_shallow(),
            shallow_status: step.shallow_status,
            atom_count: step.clause.atom_count() as i32,
            literal_count,
            positive_literal_count,
            negative_literal_count: literal_count - positive_literal_count,
            signed_literal_count,
            equality_literal_count: literal_count - signed_literal_count,
            context_variable_count: step.clause.context.len() as i32,
            context_type_sort_count,
            context_typeclass_count,
            distinct_free_variable_count: atom_counts.distinct_free_variables.len() as i32,
            free_variable_atom_count: atom_counts.free_variables,
            bound_variable_atom_count: atom_counts.bound_variables,
            scoped_constant_atom_count: atom_counts.scoped_constants,
            global_constant_atom_count: atom_counts.global_constants,
            type_atom_count: atom_counts.types,
            typeclass_atom_count: atom_counts.typeclasses,
            bool_value_atom_count: atom_counts.bool_values,
            logical_symbol_atom_count: atom_counts.logical_symbols,
            has_any_variable: step.clause.has_any_variable(),
            has_scoped_constant: step.clause.has_scoped_constant(),
            is_counterfactual: step.truthiness == Truthiness::Counterfactual,
            is_hypothetical: step.truthiness == Truthiness::Hypothetical,
            is_factual: step.truthiness == Truthiness::Factual,
            is_assumption: step.rule.is_underlying_assumption(),
            is_negated_goal: step.rule.is_underlying_negated_goal(),
            is_generated: !matches!(step.rule, Rule::Assumption(_)),
            rule_premise_count: rule_premise_count(&step.rule),
            rule_is_direct_assumption: matches!(step.rule, Rule::Assumption(_)),
            rule_is_resolution: matches!(step.rule, Rule::Resolution(_)),
            rule_is_rewrite: matches!(step.rule, Rule::Rewrite(_)),
            rule_is_specialization: matches!(step.rule, Rule::Specialization(_)),
            rule_is_equality_factoring: matches!(step.rule, Rule::EqualityFactoring(_)),
            rule_is_equality_resolution: matches!(step.rule, Rule::EqualityResolution(_)),
            rule_is_injectivity: matches!(step.rule, Rule::Injectivity(_)),
            rule_is_boolean_reduction: matches!(step.rule, Rule::BooleanReduction(_)),
            rule_is_extensionality: matches!(step.rule, Rule::Extensionality(_)),
            rule_is_multiple_rewrite: matches!(step.rule, Rule::MultipleRewrite(_)),
            rule_is_passive_contradiction: matches!(step.rule, Rule::PassiveContradiction(_)),
            rule_is_simplification: matches!(step.rule, Rule::Simplification(_)),
            source_is_axiom: source.is_axiom,
            source_is_theorem: source.is_theorem,
            source_is_lemma: source.is_lemma,
            source_is_anonymous: source.is_anonymous,
            source_is_type_definition: source.is_type_definition,
            source_is_constant_definition: source.is_constant_definition,
            source_is_extends: source.is_extends,
            source_is_instance: source.is_instance,
            source_is_premise: source.is_premise,
            source_is_negated_goal: source.is_negated_goal,
            source_is_block_goal: source.is_block_goal,
            source_is_importable: source.is_importable,
            source_depth: source.depth,
            proof_size: step.proof_size as i32,
            depth: step.depth as i32,
        }
    }

    pub fn catalog_feature_names() -> &'static [&'static str] {
        &FEATURE_CATALOG_NAMES
    }

    pub fn feature_value(&self, name: &str) -> Option<f32> {
        Some(match name {
            "is_contradiction" => bool_float(self.is_contradiction),
            "atom_count" => self.atom_count as f32,
            "is_counterfactual" => bool_float(self.is_counterfactual),
            "is_hypothetical" => bool_float(self.is_hypothetical),
            "is_factual" => bool_float(self.is_factual),
            "is_assumption" => bool_float(self.is_assumption),
            "is_negated_goal" => bool_float(self.is_negated_goal),
            "proof_size" => self.proof_size as f32,
            "depth" => self.depth as f32,
            "is_shallow" => bool_float(self.is_shallow),
            "shallow_status_deep" => bool_float(self.shallow_status == ShallowStatus::Deep),
            "shallow_status_spent" => bool_float(self.shallow_status == ShallowStatus::Spent),
            "shallow_status_unspent" => bool_float(self.shallow_status == ShallowStatus::Unspent),
            "shallow_status_contradiction" => {
                bool_float(self.shallow_status == ShallowStatus::Contradiction)
            }
            "literal_count" => self.literal_count as f32,
            "positive_literal_count" => self.positive_literal_count as f32,
            "negative_literal_count" => self.negative_literal_count as f32,
            "signed_literal_count" => self.signed_literal_count as f32,
            "equality_literal_count" => self.equality_literal_count as f32,
            "context_variable_count" => self.context_variable_count as f32,
            "context_type_sort_count" => self.context_type_sort_count as f32,
            "context_typeclass_count" => self.context_typeclass_count as f32,
            "distinct_free_variable_count" => self.distinct_free_variable_count as f32,
            "free_variable_atom_count" => self.free_variable_atom_count as f32,
            "bound_variable_atom_count" => self.bound_variable_atom_count as f32,
            "scoped_constant_atom_count" => self.scoped_constant_atom_count as f32,
            "global_constant_atom_count" => self.global_constant_atom_count as f32,
            "type_atom_count" => self.type_atom_count as f32,
            "typeclass_atom_count" => self.typeclass_atom_count as f32,
            "bool_value_atom_count" => self.bool_value_atom_count as f32,
            "logical_symbol_atom_count" => self.logical_symbol_atom_count as f32,
            "has_any_variable" => bool_float(self.has_any_variable),
            "has_scoped_constant" => bool_float(self.has_scoped_constant),
            "is_generated" => bool_float(self.is_generated),
            "rule_premise_count" => self.rule_premise_count as f32,
            "rule_is_direct_assumption" => bool_float(self.rule_is_direct_assumption),
            "rule_is_resolution" => bool_float(self.rule_is_resolution),
            "rule_is_rewrite" => bool_float(self.rule_is_rewrite),
            "rule_is_specialization" => bool_float(self.rule_is_specialization),
            "rule_is_equality_factoring" => bool_float(self.rule_is_equality_factoring),
            "rule_is_equality_resolution" => bool_float(self.rule_is_equality_resolution),
            "rule_is_injectivity" => bool_float(self.rule_is_injectivity),
            "rule_is_boolean_reduction" => bool_float(self.rule_is_boolean_reduction),
            "rule_is_extensionality" => bool_float(self.rule_is_extensionality),
            "rule_is_multiple_rewrite" => bool_float(self.rule_is_multiple_rewrite),
            "rule_is_passive_contradiction" => bool_float(self.rule_is_passive_contradiction),
            "rule_is_simplification" => bool_float(self.rule_is_simplification),
            "source_is_axiom" => bool_float(self.source_is_axiom),
            "source_is_theorem" => bool_float(self.source_is_theorem),
            "source_is_lemma" => bool_float(self.source_is_lemma),
            "source_is_anonymous" => bool_float(self.source_is_anonymous),
            "source_is_type_definition" => bool_float(self.source_is_type_definition),
            "source_is_constant_definition" => bool_float(self.source_is_constant_definition),
            "source_is_extends" => bool_float(self.source_is_extends),
            "source_is_instance" => bool_float(self.source_is_instance),
            "source_is_premise" => bool_float(self.source_is_premise),
            "source_is_negated_goal" => bool_float(self.source_is_negated_goal),
            "source_is_block_goal" => bool_float(self.source_is_block_goal),
            "source_is_importable" => bool_float(self.source_is_importable),
            "source_depth" => self.source_depth as f32,
            _ => return None,
        })
    }

    pub fn to_named_floats<S: AsRef<str>>(&self, names: &[S]) -> Vec<f32> {
        names
            .iter()
            .map(|name| {
                let name = name.as_ref();
                self.feature_value(name)
                    .unwrap_or_else(|| panic!("unknown feature name '{}'", name))
            })
            .collect()
    }

    pub fn to_catalog_floats(&self) -> Vec<f32> {
        self.to_named_floats(Self::catalog_feature_names())
    }

    pub fn to_array_for_names<S: AsRef<str>>(&self, names: &[S]) -> Array1<f32> {
        Array1::from(self.to_named_floats(names))
    }

    pub fn to_array2_for_names<S: AsRef<str>>(
        features_slice: &[Features],
        names: &[S],
    ) -> Array2<f32> {
        let num_rows = features_slice.len();
        assert_ne!(num_rows, 0);

        let mut array2 = Array2::zeros((num_rows, names.len()));

        // Fill the Array2 with the feature vectors
        for (i, features) in features_slice.iter().enumerate() {
            let feature_row = features.to_array_for_names(names);
            array2.index_axis_mut(Axis(0), i).assign(&feature_row);
        }

        array2
    }
}

fn bool_float(value: bool) -> f32 {
    value as i8 as f32
}

fn rule_premise_count(rule: &Rule) -> i32 {
    match rule {
        Rule::Assumption(_) => 0,
        Rule::Resolution(_) | Rule::Rewrite(_) => 2,
        Rule::Specialization(_)
        | Rule::EqualityFactoring(_)
        | Rule::EqualityResolution(_)
        | Rule::Injectivity(_)
        | Rule::Extensionality(_) => 1,
        Rule::BooleanReduction(info) => 1 + info.inhabitance_source_ids.len() as i32,
        Rule::MultipleRewrite(info) => {
            1 + info.active_ids.len() as i32 + info.passive_ids.len() as i32
        }
        Rule::PassiveContradiction(n) => *n as i32,
        Rule::Simplification(info) => info.simplifying_ids.len() as i32,
    }
}

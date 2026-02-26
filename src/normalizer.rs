use std::collections::HashMap;
use std::sync::Arc;

use crate::builder::BuildError;
use crate::elaborator::acorn_type::{AcornType, TypeParam};
use crate::elaborator::acorn_value::ConstantInstance;
use crate::elaborator::acorn_value::{AcornValue, BinaryOp, MatchCase};
use crate::elaborator::fact::Fact;
use crate::elaborator::goal::Goal;
use crate::elaborator::names::ConstantName;
use crate::elaborator::potential_value::PotentialValue;
use crate::elaborator::proposition::Proposition;
use crate::elaborator::source::Source;
use crate::elaborator::to_term::build_type_var_map;
use crate::elaborator::to_term::elaborate_value_to_term;
use crate::elaborator::to_term::elaborate_value_to_term_existing;
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::clause::Clause;
use crate::kernel::clausifier::Clausifier;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::proof_step::{ProofStep, Truthiness};
use crate::kernel::symbol::Symbol;
use crate::kernel::symbol_table::NewConstantType;
use crate::kernel::synthetic::SyntheticDefinition;
use crate::kernel::term::Term;
use crate::module::ModuleId;
use tracing::trace;

/// A fact that has been normalized into proof steps.
#[derive(Clone)]
pub struct NormalizedFact {
    pub steps: Vec<ProofStep>,
    pub kernel_context: KernelContext,
}

/// A goal that has been normalized into proof steps.
/// Includes the normalizer state after normalizing this goal.
#[derive(Clone)]
pub struct NormalizedGoal {
    pub goal: Goal,
    pub steps: Vec<ProofStep>,
    /// The kernel context state after normalizing this goal (with negated goal added).
    pub kernel_context: KernelContext,
}

#[derive(Clone)]
pub struct Normalizer {
    /// The kernel context containing kernel stores.
    pub(crate) kernel_context: KernelContext,
}

impl Normalizer {
    pub fn new() -> Normalizer {
        Self::from_kernel_context(KernelContext::new())
    }

    pub fn from_kernel_context(kernel_context: KernelContext) -> Normalizer {
        Normalizer { kernel_context }
    }

    pub fn into_kernel_context(self) -> KernelContext {
        self.kernel_context
    }

    pub fn get_synthetic_type(&self, module_id: ModuleId, local_id: AtomId) -> AcornType {
        let symbol = Symbol::Synthetic(module_id, local_id);
        let type_term = self.kernel_context.symbol_table.get_type(symbol);
        self.kernel_context
            .type_store
            .type_term_to_acorn_type(type_term)
    }

    /// Returns all synthetic atom IDs that have been defined.
    #[cfg(test)]
    pub fn get_synthetic_ids(&self) -> Vec<(ModuleId, AtomId)> {
        self.kernel_context.synthetic_registry.get_ids()
    }

    pub fn kernel_context(&self) -> &KernelContext {
        &self.kernel_context
    }

    pub fn kernel_context_mut(&mut self) -> &mut KernelContext {
        &mut self.kernel_context
    }

    /// Registers an arbitrary type with the type store.
    /// This is needed for certificate checking where type parameters defined
    /// in a let...satisfy statement need to be available for subsequent steps.
    pub fn register_arbitrary_type(&mut self, param: &TypeParam) {
        let arb_type = AcornType::Arbitrary(param.clone());
        self.kernel_context.type_store.add_type(&arb_type);

        // If the type param has a typeclass constraint, ensure the typeclass is registered.
        if let Some(typeclass) = &param.typeclass {
            self.kernel_context.type_store.add_typeclass(typeclass);
        }
    }

    /// Gets a synthetic definition for a value, if one exists.
    /// The value should be of the form "exists ___ (forall x and forall y and ...)".
    /// The type_var_map is used for polymorphic normalization.
    pub fn get_synthetic_definition(
        &mut self,
        value: &AcornValue,
        type_var_map: Option<&HashMap<String, (AtomId, Term)>>,
    ) -> Option<&Arc<SyntheticDefinition>> {
        let (num_definitions, alt_value, quant_types) = match value {
            AcornValue::Exists(quants, subvalue) => (
                quants.len(),
                AcornValue::ForAll(quants.clone(), subvalue.clone()),
                quants.clone(),
            ),
            _ => (0, value.clone(), vec![]),
        };

        let term =
            elaborate_value_to_term_existing(&mut self.kernel_context, &alt_value, type_var_map)
                .ok()?;
        let mut view =
            Clausifier::new_mut(&mut self.kernel_context, type_var_map.cloned(), ModuleId(0));
        let Ok(uninstantiated) = view.clausify_term_to_denormalized_clauses(&term) else {
            return None;
        };

        // Skip the type variables when replacing existentials
        let num_type_vars = type_var_map.map_or(0, |m| m.len());

        // Convert quantifier types to type terms, including polymorphic wrapper if applicable
        // Get type variable kinds in sorted order (same as make_skolem_terms)
        let type_var_kinds: Vec<Term> = if let Some(tvm) = type_var_map {
            let mut entries: Vec<_> = tvm.values().collect();
            entries.sort_by_key(|(id, _)| *id);
            entries.iter().map(|(_, kind)| kind.clone()).collect()
        } else {
            vec![]
        };

        let num_type_params = type_var_kinds.len() as u16;
        let synthetic_types: Vec<Term> = quant_types
            .iter()
            .map(|t| {
                // First convert the base type
                let mut type_term = self
                    .kernel_context
                    .type_store
                    .to_type_term_with_vars(t, type_var_map);
                // Convert FreeVariables to BoundVariables (same as make_skolem_terms)
                type_term = type_term.convert_free_to_bound(num_type_params);
                // Wrap with Pi types for each type variable
                for kind in type_var_kinds.iter().rev() {
                    type_term = Term::pi(kind.clone(), type_term);
                }
                type_term
            })
            .collect();

        let clauses: Vec<Clause> = uninstantiated
            .iter()
            .map(|c| c.instantiate_invalid_synthetics_with_skip(num_definitions, num_type_vars))
            .collect();

        self.kernel_context.synthetic_registry.lookup_by_key(
            &type_var_kinds,
            &synthetic_types,
            &clauses,
        )
    }

    pub fn add_scoped_constant(
        &mut self,
        cname: ConstantName,
        acorn_type: &AcornType,
        type_var_map: Option<&HashMap<String, (AtomId, Term)>>,
    ) -> Atom {
        let type_term = self
            .kernel_context
            .type_store
            .to_type_term_with_vars(acorn_type, type_var_map);
        Atom::Symbol(self.kernel_context.symbol_table.add_constant(
            cname,
            NewConstantType::Local,
            type_term,
        ))
    }

    /// Merges another Normalizer into this one.
    /// Used to combine normalized state from dependencies.
    pub fn merge(&mut self, other: &Normalizer) {
        self.kernel_context.merge(&other.kernel_context);
    }

    /// Merges another Normalizer into this one, excluding scoped constants.
    /// This is intended for merging import state only.
    pub fn merge_imports(&mut self, other: &Normalizer) {
        self.kernel_context.merge_imports(&other.kernel_context);
    }
}

impl Normalizer {
    /// Normalize a term-level proposition into clauses.
    ///
    /// This is the term-native backend for proposition normalization.
    fn normalize_term(
        &mut self,
        term: &Term,
        _ctype: NewConstantType,
        source: &Source,
        type_var_map: Option<HashMap<String, (AtomId, Term)>>,
    ) -> Result<Vec<Clause>, String> {
        term.validate();

        let mut skolem_ids = vec![];
        let mut mut_view = Clausifier::new_mut(
            &mut self.kernel_context,
            type_var_map.clone(),
            source.module_id,
        );
        let clauses = mut_view.clausify_term(term, &mut skolem_ids)?;

        // For any of the created ids that have not been defined yet, the output
        // clauses will be their definition.
        let mut output = vec![];
        let mut undefined_ids = vec![];
        for id in skolem_ids {
            if let Some(def) = self.kernel_context.synthetic_registry.get(&id) {
                for clause in &def.clauses {
                    output.push(clause.clone());
                }
            } else {
                undefined_ids.push(id);
            }
        }

        if !undefined_ids.is_empty() {
            // We have to define the skolem atoms that were declared during skolemization.
            let type_vars: Vec<Term> = if let Some(ref tvm) = type_var_map {
                let mut entries: Vec<_> = tvm.values().collect();
                entries.sort_by_key(|(id, _)| *id);
                entries.iter().map(|(_, kind)| kind.clone()).collect()
            } else {
                vec![]
            };

            let synthetic_types: Vec<Term> = undefined_ids
                .iter()
                .map(|&(m, i)| {
                    self.kernel_context
                        .symbol_table
                        .get_type(Symbol::Synthetic(m, i))
                        .clone()
                })
                .collect();

            self.kernel_context.define_synthetic_atoms(
                undefined_ids,
                type_vars,
                synthetic_types,
                clauses.clone(),
                Some(source.clone()),
            )?;
        }

        output.extend(clauses.into_iter());
        Ok(output)
    }

    /// Converts a value proposition to CNF clauses via:
    /// `AcornValue --elaborate--> Term --normalize_term--> Vec<Clause>`.
    fn normalize_value(
        &mut self,
        value: &AcornValue,
        ctype: NewConstantType,
        source: &Source,
        type_var_map: Option<HashMap<String, (AtomId, Term)>>,
    ) -> Result<Vec<Clause>, String> {
        if let Err(e) = value.validate() {
            return Err(format!(
                "validation error: {} while normalizing: {}",
                e, value
            ));
        }
        assert!(value.is_bool_type());

        let term = elaborate_value_to_term(
            &mut self.kernel_context,
            value,
            ctype,
            type_var_map.as_ref(),
        )?;
        self.normalize_term(&term, ctype, source, type_var_map)
    }

    /// A single fact can turn into a bunch of proof steps.
    pub fn normalize_fact(&mut self, fact: &Fact) -> Result<NormalizedFact, BuildError> {
        let mut steps = vec![];

        // Register typeclass relationships in TypeStore
        match fact {
            Fact::Instance(datatype, typeclass, _) => {
                let acorn_type = AcornType::Data(datatype.clone(), vec![]);
                let typeclass_id = self.kernel_context.type_store.add_typeclass(typeclass);
                self.kernel_context
                    .type_store
                    .add_type_instance(&acorn_type, typeclass_id);
            }
            Fact::Extends(typeclass, base_set, provides_inhabitants, _) => {
                let tc_id = self.kernel_context.type_store.add_typeclass(typeclass);
                for base in base_set {
                    let base_id = self.kernel_context.type_store.add_typeclass(base);
                    self.kernel_context
                        .type_store
                        .add_typeclass_extends(tc_id, base_id);
                }
                // If the typeclass has a constant of the instance type (e.g., point: P),
                // mark it as providing inhabitants.
                if *provides_inhabitants {
                    self.kernel_context
                        .symbol_table
                        .mark_typeclass_inhabited(tc_id);
                }
            }
            _ => {}
        }

        let range = fact.source().range;

        {
            // We keep track of type params to build the type_var_map
            let propositions: Vec<(AcornValue, Vec<TypeParam>, Source)> = match fact {
                Fact::Proposition(prop) => {
                    vec![(prop.value.clone(), prop.params.clone(), prop.source.clone())]
                }
                Fact::Definition(potential, definition, source) => {
                    let (params, constant) = match potential {
                        PotentialValue::Unresolved(u) => {
                            (u.params.clone(), u.clone().to_generic_value())
                        }
                        PotentialValue::Resolved(c) => (vec![], c.clone()),
                    };
                    let claim = constant.inflate_function_definition(definition.clone());
                    let prop = Proposition::new(claim, params, source.clone());
                    vec![(prop.value, prop.params, prop.source)]
                }
                Fact::Extends(..) | Fact::Instance(..) => {
                    // These don't produce propositions
                    vec![]
                }
            };

            for (value, type_params, source) in propositions {
                let type_var_map = build_type_var_map(&mut self.kernel_context, &type_params);

                let type_var_map_opt = if type_var_map.is_empty() {
                    None
                } else {
                    Some(type_var_map)
                };
                let ctype = if source.truthiness() == Truthiness::Factual {
                    NewConstantType::Global
                } else {
                    NewConstantType::Local
                };
                let clauses = self
                    .normalize_value(&value, ctype, &source, type_var_map_opt.clone())
                    .map_err(|msg| BuildError::new(range, msg))?;
                for clause in &clauses {
                    trace!(clause = %clause, "normalized to clause");
                }
                for clause in clauses {
                    clause.validate(&self.kernel_context);
                    let step = ProofStep::assumption(&source, clause);
                    steps.push(step);
                }
            }
        }

        Ok(NormalizedFact {
            steps,
            kernel_context: self.kernel_context.clone(),
        })
    }

    /// Normalizes a goal into proof steps that include both positive versions
    /// of the hypotheses and negated versions of the conclusion.
    pub fn normalize_goal(&mut self, goal: &Goal) -> Result<NormalizedGoal, BuildError> {
        let prop = &goal.proposition;

        let (hypo, counterfactual) = prop.value.clone().negate_goal();
        let mut steps = vec![];
        if let Some(hypo) = hypo {
            // Preserve type parameters when creating hypothesis fact
            let hypo_prop = Proposition::new(hypo, prop.params.clone(), prop.source.clone());
            let fact = Fact::Proposition(Arc::new(hypo_prop));
            steps.extend(self.normalize_fact(&fact)?.steps);
        }
        // Preserve type parameters when creating counterfactual fact
        let counterfactual_prop = Proposition::new(
            counterfactual,
            prop.params.clone(),
            prop.source.as_negated_goal(),
        );
        let fact = Fact::Proposition(Arc::new(counterfactual_prop));
        steps.extend(self.normalize_fact(&fact)?.steps);

        Ok(NormalizedGoal {
            goal: goal.clone(),
            steps,
            kernel_context: self.kernel_context.clone(),
        })
    }

    /// If arbitrary names are provided, any free variables of the keyed types are converted
    /// to constants.
    /// If var_remapping is provided, variable indices are remapped (used when type variables
    /// are filtered out of forall quantifiers).
    /// If type_var_id_to_name is provided, FreeVariable type variables use proper names.
    fn denormalize_atom(
        &self,
        atom_type: &Term,
        atom: &Atom,
        local_context: &LocalContext,
        arbitrary_names: Option<&HashMap<Term, ConstantName>>,
        var_remapping: Option<&[Option<u16>]>,
        type_param_names: Option<&[String]>,
        type_var_id_to_name: Option<&HashMap<AtomId, String>>,
        instantiate_type_vars: bool,
    ) -> AcornValue {
        let acorn_type = if atom_type.as_ref().is_atomic() {
            if let Atom::FreeVariable(var_id) = atom_type.as_ref().get_head_atom() {
                let typeclass = local_context
                    .get_var_type(*var_id as usize)
                    .and_then(|t| t.as_ref().as_typeclass())
                    .and_then(|tc_id| self.kernel_context.type_store.get_typeclass_by_id(tc_id))
                    .cloned();
                let name = type_var_id_to_name
                    .and_then(|m| m.get(var_id))
                    .cloned()
                    .unwrap_or_else(|| format!("T{}", var_id));
                AcornType::Variable(TypeParam { name, typeclass })
            } else if let Some(name_map) = type_var_id_to_name {
                self.kernel_context
                    .type_store
                    .type_term_to_acorn_type_with_var_names(atom_type, name_map)
            } else {
                self.kernel_context
                    .type_store
                    .type_term_to_acorn_type_with_context(
                        atom_type,
                        local_context,
                        instantiate_type_vars,
                    )
            }
        } else if let Some(name_map) = type_var_id_to_name {
            self.kernel_context
                .type_store
                .type_term_to_acorn_type_with_var_names(atom_type, name_map)
        } else {
            self.kernel_context
                .type_store
                .type_term_to_acorn_type_with_context(
                    atom_type,
                    local_context,
                    instantiate_type_vars,
                )
        };
        match atom {
            Atom::Symbol(Symbol::True) => AcornValue::Bool(true),
            Atom::Symbol(Symbol::False) => AcornValue::Bool(false),
            Atom::Symbol(Symbol::Not)
            | Atom::Symbol(Symbol::And)
            | Atom::Symbol(Symbol::Or)
            | Atom::Symbol(Symbol::Eq)
            | Atom::Symbol(Symbol::Ite) => {
                panic!("logical symbols should be handled in denormalize_term")
            }
            Atom::Symbol(Symbol::GlobalConstant(m, i)) => {
                let name = self
                    .kernel_context
                    .symbol_table
                    .name_for_global_id(*m, *i)
                    .clone();
                // Look up stored polymorphic info
                if let Some(poly_info) =
                    self.kernel_context.symbol_table.get_polymorphic_info(&name)
                {
                    AcornValue::constant(
                        name,
                        vec![],
                        poly_info.generic_type.clone(),
                        poly_info.generic_type.clone(),
                        poly_info.type_param_names.clone(),
                    )
                } else {
                    // Non-polymorphic constant
                    AcornValue::constant(name, vec![], acorn_type.clone(), acorn_type, vec![])
                }
            }
            Atom::Symbol(Symbol::ScopedConstant(i)) => {
                let name = self
                    .kernel_context
                    .symbol_table
                    .name_for_local_id(*i)
                    .clone();
                // Look up stored polymorphic info
                if let Some(poly_info) =
                    self.kernel_context.symbol_table.get_polymorphic_info(&name)
                {
                    AcornValue::constant(
                        name,
                        vec![],
                        poly_info.generic_type.clone(),
                        poly_info.generic_type.clone(),
                        poly_info.type_param_names.clone(),
                    )
                } else {
                    // Non-polymorphic constant
                    AcornValue::constant(name, vec![], acorn_type.clone(), acorn_type, vec![])
                }
            }
            Atom::FreeVariable(i) => {
                if let Some(map) = arbitrary_names {
                    if let Some(name) = map.get(atom_type) {
                        // Non-generic: generic_type equals instance_type
                        return AcornValue::constant(
                            name.clone(),
                            vec![],
                            acorn_type.clone(),
                            acorn_type,
                            vec![],
                        );
                    }
                }
                // Apply remapping if provided. A mapped `None` means this variable should have
                // been eliminated (e.g., type-level variable), so seeing it in a value position
                // indicates a denormalization bug.
                let new_i = if let Some(mapping) = var_remapping {
                    match mapping.get(*i as usize) {
                        Some(Some(mapped)) => *mapped,
                        Some(None) => panic!(
                            "denormalize_atom saw excluded variable x{} in value position",
                            i
                        ),
                        None => *i,
                    }
                } else {
                    *i
                };
                AcornValue::Variable(new_i, acorn_type)
            }
            Atom::Symbol(Symbol::Synthetic(m, i)) => {
                let symbol = Symbol::Synthetic(*m, *i);
                let type_term = self.kernel_context.symbol_table.get_type(symbol);
                let acorn_type = if let Some(name_map) = type_var_id_to_name {
                    self.kernel_context
                        .type_store
                        .type_term_to_acorn_type_with_var_names(type_term, name_map)
                } else {
                    self.kernel_context
                        .type_store
                        .type_term_to_acorn_type(type_term)
                };
                let name = ConstantName::Synthetic(*m, *i);

                // In polymorphic mode, check if the type has leading type parameter Pis
                // (Pi types where the input is TypeSort or a Typeclass)
                {
                    let num_type_params = type_term.as_ref().count_type_params();
                    if num_type_params > 0 {
                        // This is a polymorphic synthetic - use provided names or generate defaults
                        let names: Vec<String> = if let Some(provided) = type_param_names {
                            // Use the provided names (computed by code_generator)
                            provided[..num_type_params].to_vec()
                        } else {
                            // Fallback to "X{i}" - intentionally different from "T{i}" so tests
                            // will fail if proper names aren't being passed when they should be
                            (0..num_type_params).map(|i| format!("X{}", i)).collect()
                        };
                        return AcornValue::constant(
                            name,
                            vec![],
                            acorn_type.clone(),
                            acorn_type,
                            names,
                        );
                    }
                }

                // Non-polymorphic: generic_type equals instance_type
                AcornValue::constant(name, vec![], acorn_type.clone(), acorn_type, vec![])
            }
            Atom::Symbol(Symbol::Type(_))
            | Atom::Symbol(Symbol::Empty)
            | Atom::Symbol(Symbol::Bool)
            | Atom::Symbol(Symbol::Type0) => {
                panic!(
                    "Type symbols should not appear in open terms (atom={:?}, atom_type={})",
                    atom, atom_type
                )
            }
            Atom::Symbol(Symbol::Typeclass(_)) => {
                panic!("Typeclass atoms should not appear in open terms")
            }
            Atom::BoundVariable(_) => {
                panic!("BoundVariable atoms should not appear in denormalize_atom")
            }
        }
    }

    fn apply_type_args_to_constant(
        constant: &ConstantInstance,
        type_args: &[AcornType],
    ) -> AcornValue {
        if type_args.is_empty() {
            return AcornValue::Constant(constant.clone());
        }
        let params_to_apply = constant.type_param_names.len().min(type_args.len());
        let params: Vec<AcornType> = type_args.iter().take(params_to_apply).cloned().collect();
        let named_params: Vec<_> = constant
            .type_param_names
            .iter()
            .take(params_to_apply)
            .zip(params.iter())
            .map(|(name, ty)| (name.clone(), ty.clone()))
            .collect();
        let instance_type = constant.generic_type.instantiate(&named_params);
        AcornValue::Constant(ConstantInstance {
            name: constant.name.clone(),
            params,
            instance_type,
            generic_type: constant.generic_type.clone(),
            type_param_names: constant.type_param_names.clone(),
        })
    }

    fn instantiate_symbol_for_match(
        &self,
        symbol: Symbol,
        type_args: &[AcornType],
    ) -> Option<AcornValue> {
        let name = match symbol {
            Symbol::GlobalConstant(module_id, atom_id) => self
                .kernel_context
                .symbol_table
                .name_for_global_id(module_id, atom_id)
                .clone(),
            Symbol::ScopedConstant(atom_id) => self
                .kernel_context
                .symbol_table
                .name_for_local_id(atom_id)
                .clone(),
            _ => return None,
        };

        if let Some(poly) = self.kernel_context.symbol_table.get_polymorphic_info(&name) {
            let params_to_apply = poly.type_param_names.len().min(type_args.len());
            let params: Vec<AcornType> = type_args.iter().take(params_to_apply).cloned().collect();
            let named_params: Vec<_> = poly
                .type_param_names
                .iter()
                .take(params_to_apply)
                .zip(params.iter())
                .map(|(param_name, ty)| (param_name.clone(), ty.clone()))
                .collect();
            let instance_type = poly.generic_type.instantiate(&named_params);
            return Some(AcornValue::constant(
                name.clone(),
                params,
                instance_type,
                poly.generic_type.clone(),
                poly.type_param_names.clone(),
            ));
        }

        let symbol_type = self
            .kernel_context
            .symbol_table
            .get_symbol_type(symbol, &self.kernel_context.type_store);
        let acorn_type = self
            .kernel_context
            .type_store
            .type_term_to_acorn_type(&symbol_type);
        Some(AcornValue::constant(
            name.clone(),
            vec![],
            acorn_type.clone(),
            acorn_type,
            vec![],
        ))
    }

    fn maybe_reconstruct_match(
        &self,
        head: &AcornValue,
        type_args: &[AcornType],
        value_args: &[AcornValue],
        local_context: &LocalContext,
        var_remapping: Option<&[Option<u16>]>,
    ) -> Option<AcornValue> {
        let AcornValue::Constant(constant) = head else {
            return None;
        };
        let match_symbol = self
            .kernel_context
            .symbol_table
            .get_symbol(&constant.name)?;
        let info = self
            .kernel_context
            .symbol_table
            .get_match_eliminator_info(match_symbol)?;
        if value_args.len() != info.constructor_symbols.len() + 1 {
            return None;
        }

        let scrutinee = value_args[0].clone();
        let constructor_total = u16::try_from(info.constructor_symbols.len()).ok()?;
        let first_new_var_id = local_context.len() as AtomId;
        let mut cases = vec![];

        for (constructor_index, (constructor_symbol, branch_value)) in info
            .constructor_symbols
            .iter()
            .zip(value_args.iter().skip(1))
            .enumerate()
        {
            let (new_vars, result) = match branch_value.clone() {
                AcornValue::Lambda(args, body) => (args, *body),
                other => (vec![], other),
            };

            let constructor = self.instantiate_symbol_for_match(*constructor_symbol, type_args)?;
            let pattern = if new_vars.is_empty() {
                constructor
            } else {
                let mut pattern_args = vec![];
                for (i, var_type) in new_vars.iter().enumerate() {
                    let original_var_id = first_new_var_id + i as AtomId;
                    let remapped_id = var_remapping
                        .and_then(|mapping| mapping.get(original_var_id as usize))
                        .and_then(|mapped| *mapped)
                        .unwrap_or(original_var_id);
                    pattern_args.push(AcornValue::Variable(remapped_id, var_type.clone()));
                }
                AcornValue::apply(constructor, pattern_args)
            };

            cases.push(MatchCase {
                new_vars,
                pattern,
                result,
                constructor_index: constructor_index as u16,
                constructor_total,
            });
        }

        Some(AcornValue::Match(Box::new(scrutinee), cases))
    }

    /// If arbitrary names are provided, any free variables of the keyed types are converted
    /// to constants.
    /// If var_remapping is provided, variable indices are remapped.
    /// If type_param_names is provided, it's used for polymorphic synthetic atoms.
    /// If type_var_id_to_name is provided, FreeVariable type arguments use proper names.
    /// If instantiate_type_vars is true, FreeVariable type atoms become concrete types.
    fn denormalize_term(
        &self,
        term: &Term,
        local_context: &LocalContext,
        arbitrary_names: Option<&HashMap<Term, ConstantName>>,
        var_remapping: Option<&[Option<u16>]>,
        type_param_names: Option<&[String]>,
        type_var_id_to_name: Option<&HashMap<AtomId, String>>,
        instantiate_type_vars: bool,
    ) -> AcornValue {
        fn reduce_head_lambda_application(term: &Term) -> Option<Term> {
            use crate::kernel::term::Decomposition;

            match term.as_ref().decompose() {
                Decomposition::Application(func, arg) => match func.decompose() {
                    Decomposition::Lambda(_, body) => Some(
                        body.to_owned()
                            .substitute_bound(0, &arg.to_owned())
                            .shift_bound(0, -1),
                    ),
                    _ => reduce_head_lambda_application(&func.to_owned())
                        .map(|reduced_func| reduced_func.apply(&[arg.to_owned()])),
                },
                _ => None,
            }
        }

        if let Some(reduced) = reduce_head_lambda_application(term) {
            return self.denormalize_term(
                &reduced,
                local_context,
                arbitrary_names,
                var_remapping,
                type_param_names,
                type_var_id_to_name,
                instantiate_type_vars,
            );
        }

        match term.as_ref().decompose() {
            crate::kernel::term::Decomposition::Lambda(input, body) => {
                let input_term = input.to_owned();
                let input_type = self
                    .kernel_context
                    .type_store
                    .type_term_to_acorn_type_with_context(
                        &input_term,
                        local_context,
                        instantiate_type_vars,
                    );

                let mut next_context = local_context.clone();
                let fresh_var = next_context.push_type(input_term) as AtomId;
                let opened_body = body
                    .to_owned()
                    .substitute_bound(0, &Term::new_variable(fresh_var))
                    .shift_bound(0, -1);
                let body_value = self.denormalize_term(
                    &opened_body,
                    &next_context,
                    arbitrary_names,
                    var_remapping,
                    type_param_names,
                    type_var_id_to_name,
                    instantiate_type_vars,
                );
                return match body_value {
                    AcornValue::Lambda(mut args, body) => {
                        args.insert(0, input_type);
                        AcornValue::Lambda(args, body)
                    }
                    other => AcornValue::Lambda(vec![input_type], Box::new(other)),
                };
            }
            crate::kernel::term::Decomposition::ForAll(binder_type, body) => {
                let binder_type_term = binder_type.to_owned();
                let binder_acorn_type = self
                    .kernel_context
                    .type_store
                    .type_term_to_acorn_type_with_context(
                        &binder_type_term,
                        local_context,
                        instantiate_type_vars,
                    );

                let mut next_context = local_context.clone();
                let fresh_var = next_context.push_type(binder_type_term) as AtomId;
                let opened_body = body
                    .to_owned()
                    .substitute_bound(0, &Term::new_variable(fresh_var))
                    .shift_bound(0, -1);
                let body_value = self.denormalize_term(
                    &opened_body,
                    &next_context,
                    arbitrary_names,
                    var_remapping,
                    type_param_names,
                    type_var_id_to_name,
                    instantiate_type_vars,
                );
                return match body_value {
                    AcornValue::ForAll(mut quants, body) => {
                        quants.insert(0, binder_acorn_type);
                        AcornValue::ForAll(quants, body)
                    }
                    other => AcornValue::ForAll(vec![binder_acorn_type], Box::new(other)),
                };
            }
            crate::kernel::term::Decomposition::Exists(binder_type, body) => {
                let binder_type_term = binder_type.to_owned();
                let binder_acorn_type = self
                    .kernel_context
                    .type_store
                    .type_term_to_acorn_type_with_context(
                        &binder_type_term,
                        local_context,
                        instantiate_type_vars,
                    );

                let mut next_context = local_context.clone();
                let fresh_var = next_context.push_type(binder_type_term) as AtomId;
                let opened_body = body
                    .to_owned()
                    .substitute_bound(0, &Term::new_variable(fresh_var))
                    .shift_bound(0, -1);
                let body_value = self.denormalize_term(
                    &opened_body,
                    &next_context,
                    arbitrary_names,
                    var_remapping,
                    type_param_names,
                    type_var_id_to_name,
                    instantiate_type_vars,
                );
                return match body_value {
                    AcornValue::Exists(mut quants, body) => {
                        quants.insert(0, binder_acorn_type);
                        AcornValue::Exists(quants, body)
                    }
                    other => AcornValue::Exists(vec![binder_acorn_type], Box::new(other)),
                };
            }
            crate::kernel::term::Decomposition::Atom(_)
            | crate::kernel::term::Decomposition::Application(_, _)
            | crate::kernel::term::Decomposition::Pi(_, _) => {}
        }

        let logical_head_symbol = match term.get_head_atom() {
            Atom::Symbol(Symbol::Not) => Some(Symbol::Not),
            Atom::Symbol(Symbol::And) => Some(Symbol::And),
            Atom::Symbol(Symbol::Or) => Some(Symbol::Or),
            Atom::Symbol(Symbol::Eq) => Some(Symbol::Eq),
            Atom::Symbol(Symbol::Ite) => Some(Symbol::Ite),
            _ => None,
        };

        // Get the type of the head atom
        let head_type = match term.get_head_atom() {
            Atom::FreeVariable(i) => local_context
                .get_var_type(*i as usize)
                .cloned()
                .expect("Variable should have type in LocalContext"),
            Atom::Symbol(Symbol::Typeclass(_)) => {
                panic!("Typeclass atoms should not appear as head of terms")
            }
            Atom::Symbol(symbol) => self
                .kernel_context
                .symbol_table
                .get_symbol_type(*symbol, &self.kernel_context.type_store),
            Atom::BoundVariable(_) => {
                panic!("BoundVariable atoms should not appear as head of terms")
            }
        };

        // Type arguments appear as terms. Skip them in denormalization.
        // TypeSort is for unconstrained type params, Typeclass is for constrained type params.
        if head_type.as_ref().is_type_param_kind() {
            // This is a type argument - don't try to denormalize it as a value
            // Return a placeholder that won't be used (the caller should handle type args specially)
            return AcornValue::Bool(true);
        }

        let head = logical_head_symbol.map_or_else(
            || {
                Some(self.denormalize_atom(
                    &head_type,
                    &term.get_head_atom(),
                    local_context,
                    arbitrary_names,
                    var_remapping,
                    type_param_names,
                    type_var_id_to_name,
                    instantiate_type_vars,
                ))
            },
            |_| None,
        );

        // Type arguments appear as the first few arguments.
        // We need to:
        // 1. Extract type arguments and convert them to AcornTypes
        // 2. Update the head constant with those type parameters
        // 3. Apply only the value arguments

        let mut type_args: Vec<AcornType> = vec![];
        let mut value_args: Vec<AcornValue> = vec![];
        let mut remaining_head_type = head_type.clone();

        fn is_syntactic_type_term(term: &Term, local_context: &LocalContext) -> bool {
            fn go(term: crate::kernel::term::TermRef<'_>, local_context: &LocalContext) -> bool {
                use crate::kernel::term::Decomposition;
                match term.decompose() {
                    Decomposition::Atom(atom) => match atom {
                        Atom::Symbol(Symbol::Type(_))
                        | Atom::Symbol(Symbol::Bool)
                        | Atom::Symbol(Symbol::Empty)
                        | Atom::Symbol(Symbol::Type0)
                        | Atom::Symbol(Symbol::Typeclass(_)) => true,
                        Atom::FreeVariable(i) => local_context
                            .get_var_type(*i as usize)
                            .is_some_and(|t| t.as_ref().is_type_param_kind()),
                        Atom::BoundVariable(_) => true,
                        _ => false,
                    },
                    Decomposition::Application(func, arg) => {
                        go(func, local_context) && go(arg, local_context)
                    }
                    Decomposition::Pi(_, _) => true,
                    Decomposition::Lambda(_, _)
                    | Decomposition::ForAll(_, _)
                    | Decomposition::Exists(_, _) => false,
                }
            }
            go(term.as_ref(), local_context)
        }

        fn is_syntactic_kind_term(term: &Term) -> bool {
            fn go(term: crate::kernel::term::TermRef<'_>) -> bool {
                use crate::kernel::term::Decomposition;
                match term.decompose() {
                    Decomposition::Atom(atom) => matches!(
                        atom,
                        Atom::Symbol(Symbol::Type0) | Atom::Symbol(Symbol::Typeclass(_))
                    ),
                    Decomposition::Pi(input, output) => go(input) && go(output),
                    Decomposition::Application(_, _)
                    | Decomposition::Lambda(_, _)
                    | Decomposition::ForAll(_, _)
                    | Decomposition::Exists(_, _) => false,
                }
            }
            go(term.as_ref())
        }

        for arg in term.args().iter() {
            // Classify arguments from the function type spine instead of arg.get_type_with_context().
            // This avoids panicking on lambda arguments (their type is not inferable this late).
            let expected_input_type = remaining_head_type
                .as_ref()
                .split_pi()
                .map(|(input, _)| input.to_owned());
            let is_type_arg = expected_input_type
                .as_ref()
                .is_some_and(is_syntactic_kind_term)
                && is_syntactic_type_term(arg, local_context);

            if is_type_arg {
                // This is a type argument - convert it to an AcornType
                // Extract the typeclass constraint from the expected input kind.
                let typeclass = expected_input_type
                    .as_ref()
                    .and_then(|input| input.as_ref().as_typeclass())
                    .and_then(|tc_id| self.kernel_context.type_store.get_typeclass_by_id(tc_id))
                    .cloned();
                // If it's a FreeVariable and we have a name mapping, use the proper name
                let acorn_type = if let Some(var_id) = arg.as_ref().atomic_variable() {
                    if let Some(name) = type_var_id_to_name.and_then(|m| m.get(&var_id)) {
                        AcornType::Variable(TypeParam {
                            name: name.clone(),
                            typeclass,
                        })
                    } else {
                        self.kernel_context
                            .type_store
                            .type_term_to_acorn_type_with_context(
                                arg,
                                local_context,
                                instantiate_type_vars,
                            )
                    }
                } else {
                    self.kernel_context
                        .type_store
                        .type_term_to_acorn_type_with_context(
                            arg,
                            local_context,
                            instantiate_type_vars,
                        )
                };
                type_args.push(acorn_type);
            } else {
                // This is a value argument
                value_args.push(self.denormalize_term(
                    arg,
                    local_context,
                    arbitrary_names,
                    var_remapping,
                    type_param_names,
                    type_var_id_to_name,
                    instantiate_type_vars,
                ));
            }

            if let Some(next_type) = remaining_head_type.type_apply_with_arg(arg) {
                remaining_head_type = next_type;
            }
        }

        if let Some(symbol) = logical_head_symbol {
            match symbol {
                Symbol::Not => {
                    if !type_args.is_empty() || value_args.len() != 1 {
                        panic!("malformed not term during denormalization: {}", term);
                    }
                    return AcornValue::Not(Box::new(value_args.into_iter().next().unwrap()));
                }
                Symbol::And => {
                    if !type_args.is_empty() || value_args.len() != 2 {
                        panic!("malformed and term during denormalization: {}", term);
                    }
                    let mut args = value_args.into_iter();
                    return AcornValue::and(args.next().unwrap(), args.next().unwrap());
                }
                Symbol::Or => {
                    if !type_args.is_empty() || value_args.len() != 2 {
                        panic!("malformed or term during denormalization: {}", term);
                    }
                    let mut args = value_args.into_iter();
                    return AcornValue::or(args.next().unwrap(), args.next().unwrap());
                }
                Symbol::Eq => {
                    // Eq may carry one explicit type argument in term form.
                    if type_args.len() > 1 || value_args.len() != 2 {
                        panic!("malformed eq term during denormalization: {}", term);
                    }
                    let mut args = value_args.into_iter();
                    return AcornValue::equals(args.next().unwrap(), args.next().unwrap());
                }
                Symbol::Ite => {
                    // Ite may carry one explicit type argument in term form.
                    if type_args.len() > 1 || value_args.len() != 3 {
                        panic!("malformed ite term during denormalization: {}", term);
                    }
                    let mut args = value_args.into_iter();
                    return AcornValue::IfThenElse(
                        Box::new(args.next().unwrap()),
                        Box::new(args.next().unwrap()),
                        Box::new(args.next().unwrap()),
                    );
                }
                _ => unreachable!("unexpected logical symbol: {}", symbol),
            }
        }

        let head = head.expect("non-logical terms should have a denormalized head");

        if let Some(match_value) = self.maybe_reconstruct_match(
            &head,
            &type_args,
            &value_args,
            local_context,
            var_remapping,
        ) {
            return match_value;
        }

        let head = match head {
            AcornValue::Constant(c) => Self::apply_type_args_to_constant(&c, &type_args),
            other => other,
        };

        AcornValue::apply(head, value_args)
    }

    /// If arbitrary names are provided, any free variables of the keyed types are converted
    /// to constants.
    /// If var_remapping is provided, variable indices are remapped.
    /// If type_var_id_to_name is provided, FreeVariable type arguments use proper names.
    /// If instantiate_type_vars is true, FreeVariable type atoms become concrete types.
    fn denormalize_literal(
        &self,
        literal: &Literal,
        local_context: &LocalContext,
        arbitrary_names: Option<&HashMap<Term, ConstantName>>,
        var_remapping: Option<&[Option<u16>]>,
        type_param_names: Option<&[String]>,
        type_var_id_to_name: Option<&HashMap<AtomId, String>>,
        instantiate_type_vars: bool,
    ) -> AcornValue {
        let left = self.denormalize_term(
            &literal.left,
            local_context,
            arbitrary_names,
            var_remapping,
            type_param_names,
            type_var_id_to_name,
            instantiate_type_vars,
        );
        if literal.right.is_true() {
            if literal.positive {
                return left;
            } else {
                return AcornValue::Not(Box::new(left));
            }
        }
        let right = self.denormalize_term(
            &literal.right,
            local_context,
            arbitrary_names,
            var_remapping,
            type_param_names,
            type_var_id_to_name,
            instantiate_type_vars,
        );
        if literal.positive {
            AcornValue::equals(left, right)
        } else {
            AcornValue::not_equals(left, right)
        }
    }

    /// Converts backwards, from a clause to a value.
    /// The resulting value may have synthetic atoms in it.
    /// If arbitrary names are provided, any free variables of the keyed types are converted
    /// to constants.
    /// If type_vars is provided, those variable indices are treated as type-level variables
    /// and excluded from the forall quantifier (their indices are remapped in the body).
    /// If type_param_names is provided, it's used for naming polymorphic synthetic type params.
    /// If instantiate_type_vars is true, FreeVariable type atoms become concrete types.
    /// Any remaining free variables are enclosed in a "forall" quantifier.
    pub fn denormalize(
        &self,
        clause: &Clause,
        arbitrary_names: Option<&HashMap<Term, ConstantName>>,
        type_param_names: Option<&[String]>,
        instantiate_type_vars: bool,
    ) -> AcornValue {
        if clause.literals.is_empty() {
            return AcornValue::Bool(false);
        }
        let local_context = clause.get_local_context();

        // Find the number of variables actually used in the clause.
        // The local_context may have more variables than are used.
        let num_vars = clause
            .literals
            .iter()
            .filter_map(|lit| {
                let left_max = lit.left.max_variable();
                let right_max = lit.right.max_variable();
                match (left_max, right_max) {
                    (Some(l), Some(r)) => Some(l.max(r)),
                    (Some(l), None) => Some(l),
                    (None, Some(r)) => Some(r),
                    (None, None) => None,
                }
            })
            .max()
            .map(|max| (max + 1) as usize)
            .unwrap_or(0);

        let var_types_raw = local_context.get_var_types();

        // Build variable remapping: for each original index, what's its new index?
        // Type variables, arbitrary variables, and Empty placeholder variables
        // get None (excluded from forall).
        let mut var_remapping: Vec<Option<u16>> = Vec::new();
        let mut new_index: u16 = 0;
        for i in 0..num_vars {
            let type_term = &var_types_raw[i];
            // A variable is a type variable if its kind is Type0 (unconstrained) or Typeclass (constrained)
            let is_type_var = type_term.as_ref().is_type_param_kind();
            let is_arbitrary = arbitrary_names
                .map(|m| m.contains_key(type_term))
                .unwrap_or(false);
            let is_empty_placeholder = type_term.as_ref().is_empty_type();

            if is_type_var || is_arbitrary || is_empty_placeholder {
                var_remapping.push(None);
            } else {
                var_remapping.push(Some(new_index));
                new_index += 1;
            }
        }

        // Denormalize literals with the remapping
        let var_remapping_ref = if var_remapping.iter().any(|x| x.is_none()) {
            Some(var_remapping.as_slice())
        } else {
            None // No remapping needed if all variables are kept
        };

        let mut denormalized_literals = vec![];
        for literal in &clause.literals {
            denormalized_literals.push(self.denormalize_literal(
                literal,
                local_context,
                arbitrary_names,
                var_remapping_ref,
                type_param_names,
                None, // No type var id to name mapping needed for public denormalize
                instantiate_type_vars,
            ));
        }
        let disjunction = AcornValue::reduce(BinaryOp::Or, denormalized_literals);

        // Build var_types for the forall quantifier (only non-excluded variables)
        let var_types: Vec<AcornType> = var_types_raw
            .iter()
            .take(num_vars)
            .enumerate()
            .filter(|(i, _)| var_remapping.get(*i).copied().flatten().is_some())
            .map(|(_, type_term)| {
                self.kernel_context
                    .type_store
                    .type_term_to_acorn_type(type_term)
            })
            .collect();

        AcornValue::forall(var_types, disjunction)
    }

    /// Convert a type Term to AcornType, looking up typeclass constraints from LocalContext.
    /// If `instantiate_type_vars` is true, FreeVariable type atoms become concrete types.
    pub fn denormalize_type_with_context(
        &self,
        type_term: Term,
        local_context: &LocalContext,
        instantiate_type_vars: bool,
    ) -> AcornType {
        self.kernel_context
            .type_store
            .type_term_to_acorn_type_with_context(&type_term, local_context, instantiate_type_vars)
    }

    /// Converts a single term to an AcornValue using the provided LocalContext.
    /// This is equivalent to the term-level work done by `denormalize(...)`,
    /// but avoids wrapping the term into a synthetic clause first.
    pub fn denormalize_term_with_context(
        &self,
        term: &Term,
        local_context: &LocalContext,
        instantiate_type_vars: bool,
    ) -> AcornValue {
        self.denormalize_term(
            term,
            local_context,
            None,
            None,
            None,
            None,
            instantiate_type_vars,
        )
    }

    /// Converts a single term to an AcornValue using the provided LocalContext.
    /// If `arbitrary_names` is provided, matching free variables are converted to constants.
    pub fn denormalize_term_with_context_and_arbitrary(
        &self,
        term: &Term,
        local_context: &LocalContext,
        arbitrary_names: Option<&HashMap<Term, ConstantName>>,
        instantiate_type_vars: bool,
    ) -> AcornValue {
        self.denormalize_term(
            term,
            local_context,
            arbitrary_names,
            None,
            None,
            None,
            instantiate_type_vars,
        )
    }

    /// Given a list of (module_id, atom_id) for synthetic atoms that we need to define, find a set
    /// of SyntheticInfo that covers them.
    /// The output may have synthetic atoms that aren't used in the input.
    /// The input doesn't have to be in order and may contain duplicates.
    pub fn find_covering_synthetic_info(
        &self,
        ids: &[(ModuleId, AtomId)],
    ) -> Vec<Arc<SyntheticDefinition>> {
        self.kernel_context
            .synthetic_registry
            .find_covering_info(ids)
    }

    pub fn atom_str(&self, atom: &Atom) -> String {
        self.kernel_context.atom_str(atom)
    }

    /// When you denormalize and renormalize a clause, you should get the same thing.
    #[cfg(test)]
    fn check_denormalize_renormalize(&mut self, clause: &Clause) {
        let denormalized = self.denormalize(clause, None, None, false);
        if let Err(e) = denormalized.validate() {
            eprintln!("DEBUG: clause = {}", clause);
            eprintln!("DEBUG: clause context = {:?}", clause.get_local_context());
            eprintln!("DEBUG: denormalized = {}", denormalized);
            panic!("denormalized clause should validate: {:?}", e);
        }
        let renormalized = self
            .normalize_value(&denormalized, NewConstantType::Local, &Source::mock(), None)
            .unwrap();
        if renormalized.len() != 1 {
            // For functional equalities, we know this check doesn't work.
            // So we skip it.
            return;
        }
        if clause != &renormalized[0] {
            println!("original clause: {}", clause);
            println!("original context: {:?}", clause.get_local_context());
            println!("denormalized: {}", denormalized);
            println!("renormalized: {}", renormalized[0]);
            println!(
                "renormalized context: {:?}",
                renormalized[0].get_local_context()
            );
            if clause.get_local_context() == renormalized[0].get_local_context() {
                // Contexts match but clauses don't - might be variable ordering in literals
                for (i, (orig_lit, renorm_lit)) in clause
                    .literals
                    .iter()
                    .zip(renormalized[0].literals.iter())
                    .enumerate()
                {
                    if orig_lit != renorm_lit {
                        println!("literal {} differs: {} vs {}", i, orig_lit, renorm_lit);
                    }
                }
            }
            panic!("renormalized clause does not match original");
        }
    }

    #[cfg(test)]
    fn check_value(&mut self, value: &AcornValue, expected: &[&str]) {
        use crate::kernel::display::DisplayClause;

        let actual = self
            .normalize_value(value, NewConstantType::Local, &Source::mock(), None)
            .unwrap();
        if actual.len() != expected.len() {
            panic!(
                "expected {} clauses, got {}:\n{}",
                expected.len(),
                actual.len(),
                actual
                    .iter()
                    .map(|c| DisplayClause {
                        clause: c,
                        context: &self.kernel_context,
                    }
                    .to_string())
                    .collect::<Vec<String>>()
                    .join("\n")
            );
        }
        for (i, clause) in actual.iter().enumerate() {
            self.check_denormalize_renormalize(clause);
            let c = DisplayClause {
                clause,
                context: &self.kernel_context,
            };
            let a = c.to_string();
            if a != expected[i] {
                panic!("expected clause {} to be:\n{}\ngot:\n{}", i, expected[i], a);
            }
        }
    }

    /// Checks a theorem. Just for testing purposes.
    #[cfg(test)]
    pub fn check(
        &mut self,
        env: &crate::elaborator::environment::Environment,
        name: &str,
        expected: &[&str],
    ) {
        for node in &env.nodes {
            if let Some((theorem_name, value)) = node.as_theorem() {
                if theorem_name == name {
                    self.check_value(&value, expected);
                    return;
                }
            }
        }
        panic!("no theorem named {}", name);
    }

    /// Returns all normalized clauses from the environment. Just for testing purposes.
    #[cfg(test)]
    pub fn get_all_clauses(
        &mut self,
        env: &crate::elaborator::environment::Environment,
    ) -> Vec<crate::kernel::clause::Clause> {
        let mut clauses = vec![];
        for node in &env.nodes {
            if let Some(fact) = node.get_fact() {
                if let Ok(normalized) = self.normalize_fact(&fact) {
                    for step in normalized.steps {
                        clauses.push(step.clause);
                    }
                }
            }
        }
        clauses
    }
}

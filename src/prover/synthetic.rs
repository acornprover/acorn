use std::collections::HashMap;

use crate::elaborator::acorn_type::{AcornType, TypeParam};
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::names::ConstantName;
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::clause::{Clause, NormalizedClauseTrace, PositiveExistsReduction};
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::local_context::LocalContext;
use crate::kernel::symbol::Symbol;
use crate::kernel::symbol_table::NewConstantType;
use crate::kernel::term::Term;
use crate::module::ModuleId;

#[derive(Clone)]
pub struct WitnessEntry {
    /// The scoped constant introduced for this witness, such as `w0` or `w0(x0)`.
    pub symbol: Symbol,
    /// The source-level constant name used when emitting a certificate step.
    pub name: ConstantName,
    /// The theorem/proof locals that were in scope when the witness was opened.
    pub ambient_context: LocalContext,
    /// The binder type of the existential that introduced this witness.
    pub return_type: Term,
    /// The existential body before substituting the witness term for its bound variable.
    pub body: Term,
    /// The normalized clause whose top-level existential was opened.
    pub general_clause: Clause,
    /// The exact clause produced by substituting the witness term during proof search.
    pub specialized_clause: Clause,
}

impl WitnessEntry {
    /// Collect any previously declared witnesses that appear in this witness's types or body.
    pub fn referenced_symbols(&self) -> Vec<Symbol> {
        let mut symbols = vec![];
        for term in self
            .ambient_context
            .get_var_types()
            .iter()
            .flatten()
            .chain(std::iter::once(&self.return_type))
            .chain(std::iter::once(&self.body))
        {
            for atom in term.iter_atoms() {
                if let Atom::Symbol(
                    symbol @ (Symbol::ScopedConstant(_) | Symbol::GlobalConstant(..)),
                ) = atom
                {
                    symbols.push(*symbol);
                }
            }
        }
        symbols.sort();
        symbols.dedup();
        symbols
    }
}

pub struct WitnessOpening {
    pub term: Term,
    pub reduction: NormalizedClauseTrace,
}

#[derive(Clone, Default)]
pub struct WitnessRegistry {
    by_symbol: HashMap<Symbol, WitnessEntry>,
    next_name_index: u32,
}

impl WitnessRegistry {
    /// Create an empty witness registry for one prover run.
    pub fn new() -> Self {
        Self::default()
    }

    /// Look up witness metadata by the symbol used in proof clauses.
    pub fn get(&self, symbol: Symbol) -> Option<&WitnessEntry> {
        self.by_symbol.get(&symbol)
    }

    /// Look up witness metadata by a scoped constant id used in proof clauses.
    pub fn get_local(&self, local_id: AtomId) -> Option<&WitnessEntry> {
        self.get(Symbol::ScopedConstant(local_id))
    }

    /// Iterate over every prover-generated witness recorded for this proof search.
    pub fn iter(&self) -> impl Iterator<Item = (&Symbol, &WitnessEntry)> {
        self.by_symbol.iter()
    }

    pub fn merge_from(&mut self, other: &WitnessRegistry) {
        self.by_symbol.extend(
            other
                .by_symbol
                .iter()
                .map(|(symbol, entry)| (*symbol, entry.clone())),
        );
        self.next_name_index = self.next_name_index.max(other.next_name_index);
    }

    fn insert_existing_positive_exists(
        &mut self,
        kernel_context: &KernelContext,
        symbol: Symbol,
        clause: &Clause,
        reduction: &PositiveExistsReduction,
    ) -> Result<Clause, String> {
        let ambient_context = clause.get_local_context();
        let name = kernel_context
            .symbol_table
            .try_name_for_symbol(symbol)
            .cloned()
            .ok_or_else(|| {
                format!(
                    "synthetic witness symbol {:?} has no registered name",
                    symbol
                )
            })?;
        let witness = witness_application(symbol, ambient_context);
        let reduced = clause.instantiate_positive_exists_reduction(reduction, witness);
        self.by_symbol.insert(
            symbol,
            WitnessEntry {
                symbol,
                name,
                ambient_context: ambient_context.clone(),
                return_type: reduction.binder_type.clone(),
                body: reduction.body.clone(),
                general_clause: clause.normalized(),
                specialized_clause: reduced.clause.clone(),
            },
        );
        Ok(reduced.clause.normalized())
    }

    /// Register existing synthetic constants as witnesses for a nested positive existential.
    pub fn register_existing_positive_exists_chain(
        &mut self,
        kernel_context: &KernelContext,
        mut clause: Clause,
        symbols: &[Symbol],
    ) -> Result<(), String> {
        for symbol in symbols {
            let reduction = clause
                .positive_exists_witness_reduction(kernel_context)
                .ok_or_else(|| {
                    format!(
                        "synthetic witness symbol {:?} did not correspond to a positive existential",
                        symbol
                    )
                })?;
            clause =
                self.insert_existing_positive_exists(kernel_context, *symbol, &clause, &reduction)?;
        }
        Ok(())
    }

    /// Open a top-level positive existential by introducing a named witness.
    pub fn open_positive_exists(
        &mut self,
        kernel_context: &mut KernelContext,
        module_id: ModuleId,
        clause: &Clause,
        reduction: &PositiveExistsReduction,
    ) -> WitnessOpening {
        let clause_context = clause.get_local_context();

        // Witness signatures, polymorphic registration, and quoting all assume
        // type parameters form a leading prefix, but clause contexts can
        // interleave type and value variables. Hoist type params first; the
        // witness's own indexing (its type, its stored body/return type, and
        // its application argument order) uses the hoisted order, while the
        // application's arguments still name the clause's original variables.
        let mut hoisted_order: Vec<AtomId> = Vec::with_capacity(clause_context.len());
        for var_id in 0..clause_context.len() {
            let is_type_param = clause_context
                .get_var_type(var_id)
                .is_some_and(|var_type| var_type.as_ref().is_type_param_kind());
            if is_type_param {
                hoisted_order.push(var_id as AtomId);
            }
        }
        for var_id in 0..clause_context.len() {
            if !hoisted_order.contains(&(var_id as AtomId)) {
                hoisted_order.push(var_id as AtomId);
            }
        }
        let hoisted_context = clause_context.remap(&hoisted_order);
        let hoisted_return_type = reduction.binder_type.renumber_variables(&hoisted_order);
        let hoisted_body = reduction.body.renumber_variables(&hoisted_order);
        let ambient_context = &hoisted_context;

        let name = self.next_name(kernel_context, module_id);
        let symbol_type = witness_symbol_type(ambient_context, &hoisted_return_type);
        let symbol = kernel_context.symbol_table.add_constant(
            name.clone(),
            NewConstantType::Local,
            symbol_type,
        );
        let (type_params, _arguments, generic_type) =
            witness_signature(kernel_context, ambient_context, &hoisted_return_type);
        kernel_context.type_store.add_type(&generic_type);
        for param in &type_params {
            if let Some(typeclass) = &param.typeclass {
                kernel_context.type_store.add_typeclass(typeclass);
            }
        }
        if !type_params.is_empty() {
            kernel_context.symbol_table.set_polymorphic_info(
                name.clone(),
                generic_type,
                type_params.into_iter().map(|param| param.name).collect(),
                vec![],
            );
        }

        // Apply the witness to the clause's variables in hoisted order, so the
        // application matches the witness's type-params-first signature while
        // still naming the clause's original variables.
        let witness_args: Vec<Term> = hoisted_order
            .iter()
            .map(|&var_id| Term::new_variable(var_id))
            .collect();
        let witness = Term::atom(Atom::Symbol(symbol)).apply(&witness_args);
        let reduced = clause.instantiate_positive_exists_reduction(reduction, witness.clone());

        self.by_symbol.insert(
            symbol,
            WitnessEntry {
                symbol,
                name,
                ambient_context: hoisted_context.clone(),
                return_type: hoisted_return_type,
                body: hoisted_body,
                general_clause: clause.normalized(),
                specialized_clause: reduced.clause.clone(),
            },
        );

        WitnessOpening {
            term: witness,
            reduction: reduced,
        }
    }

    /// Pick the next unused `wN` name for a generated witness in this module.
    fn next_name(&mut self, kernel_context: &KernelContext, module_id: ModuleId) -> ConstantName {
        loop {
            let name = format!("w{}", self.next_name_index);
            self.next_name_index += 1;
            let constant_name = ConstantName::unqualified(module_id, &name);
            if kernel_context
                .symbol_table
                .get_symbol(&constant_name)
                .is_none()
            {
                return constant_name;
            }
        }
    }
}

/// Apply a witness symbol to all currently in-scope theorem locals.
pub fn witness_application(symbol: Symbol, ambient_context: &LocalContext) -> Term {
    let args: Vec<Term> = (0..ambient_context.len())
        .map(|var_id| Term::new_variable(var_id as AtomId))
        .collect();
    Term::atom(Atom::Symbol(symbol)).apply(&args)
}

/// Build the dependent function type for a witness after abstracting ambient theorem locals.
pub fn witness_symbol_type(ambient_context: &LocalContext, return_type: &Term) -> Term {
    let ambient_len = ambient_context.len() as u16;
    let mut result = return_type.convert_free_to_bound(ambient_len);
    for var_id in (0..ambient_context.len()).rev() {
        let input = ambient_context
            .get_var_type(var_id)
            .expect("witness ambient context should be dense")
            .convert_free_to_bound(var_id as u16);
        result = Term::pi(input, result);
    }
    result
}

/// Recover the source-level type parameters, arguments, and generic type for a witness symbol.
pub fn witness_signature(
    kernel_context: &KernelContext,
    ambient_context: &LocalContext,
    return_type: &Term,
) -> (Vec<TypeParam>, Vec<(String, AcornType)>, AcornType) {
    let num_type_params = ambient_context
        .get_var_types()
        .iter()
        .take_while(|var_type| {
            var_type
                .as_ref()
                .is_some_and(|term| term.as_ref().is_type_param_kind())
        })
        .count();
    let type_params: Vec<TypeParam> = (0..num_type_params)
        .map(|var_id| {
            let var_type = ambient_context
                .get_var_type(var_id)
                .expect("witness type parameter should exist");
            TypeParam {
                name: format!("T{}", var_id),
                typeclass: var_type
                    .as_ref()
                    .as_typeclass()
                    .map(|tc_id| kernel_context.type_store.get_typeclass(tc_id).clone()),
            }
        })
        .collect();
    // Source-level witness functions do not take leading type-parameter locals as value
    // arguments. Drop those slots so dependent value references use source argument indices.
    let type_param_placeholders = vec![AcornValue::Bool(true); num_type_params];
    let remove_type_param_locals = |acorn_type: AcornType| {
        acorn_type.bind_values(0, ambient_context.len() as AtomId, &type_param_placeholders)
    };

    let arguments: Vec<(String, AcornType)> = (num_type_params..ambient_context.len())
        .map(|var_id| {
            let arg_type = ambient_context
                .get_var_type(var_id)
                .expect("witness argument type should exist")
                .clone();
            (
                format!("x{}", var_id - num_type_params),
                remove_type_param_locals(kernel_context.quote_type_with_context(
                    arg_type,
                    ambient_context,
                    false,
                )),
            )
        })
        .collect();
    let result_type = remove_type_param_locals(kernel_context.quote_type_with_context(
        return_type.clone(),
        ambient_context,
        false,
    ));
    let generic_type = if arguments.is_empty() {
        result_type.clone()
    } else {
        AcornType::functional(
            arguments
                .iter()
                .map(|(_, arg_type)| arg_type.clone())
                .collect(),
            result_type,
        )
    };
    (type_params, arguments, generic_type)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::elaborator::acorn_type::{Datatype, DependentTypeArg, Typeclass};

    #[test]
    fn witness_signature_removes_type_param_slots_from_dependent_argument_types() {
        let mut kernel_context = KernelContext::new();
        let typeclass = Typeclass {
            module_id: ModuleId(0),
            name: "TopologicalSpace".to_string(),
        };
        let typeclass_id = kernel_context.type_store.add_typeclass(&typeclass);

        let set_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Set".to_string(),
        };
        kernel_context
            .type_store
            .add_type(&AcornType::Data(set_datatype.clone(), vec![]));
        kernel_context
            .type_store
            .set_datatype_arity(&set_datatype, 1);

        let subspace_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Subspace".to_string(),
        };
        let t_param = TypeParam {
            name: "T".to_string(),
            typeclass: Some(typeclass.clone()),
        };
        let t_type = AcornType::Variable(t_param);
        let set_t = AcornType::Data(set_datatype.clone(), vec![t_type.clone()]);
        kernel_context.type_store.add_type(&AcornType::Family(
            subspace_datatype.clone(),
            vec![
                DependentTypeArg::Type(t_type.clone()),
                DependentTypeArg::Value(AcornValue::Variable(0, set_t.clone())),
            ],
        ));

        let set_id = kernel_context
            .type_store
            .get_ground_id_by_name("Set")
            .expect("Set should be registered");
        let subspace_id = kernel_context
            .type_store
            .get_ground_id_by_name("Subspace")
            .expect("Subspace should be registered");
        let t_var = Term::new_variable(0);
        let a_var = Term::new_variable(1);
        let set_head = Term::ground_type(set_id);
        let subspace_head = Term::ground_type(subspace_id);
        let set_t_term = Term::type_application(set_head.clone(), vec![t_var.clone()]);
        let subspace_t_a_term = Term::type_application(subspace_head, vec![t_var.clone(), a_var]);
        let set_subspace_t_a_term =
            Term::type_application(set_head.clone(), vec![subspace_t_a_term]);

        let mut ambient_context = LocalContext::empty();
        ambient_context.push_type(Term::typeclass(typeclass_id));
        ambient_context.push_type(set_t_term.clone());
        ambient_context.push_type(set_subspace_t_a_term);

        let (type_params, arguments, generic_type) =
            witness_signature(&kernel_context, &ambient_context, &set_t_term);

        assert_eq!(
            type_params,
            vec![TypeParam {
                name: "T0".to_string(),
                typeclass: Some(typeclass),
            }]
        );
        assert_eq!(arguments.len(), 2);
        assert_eq!(arguments[0].0, "x0");
        assert_eq!(arguments[1].0, "x1");

        let AcornType::Data(datatype, params) = &arguments[1].1 else {
            panic!("second argument should be a Set");
        };
        assert_eq!(datatype.name, "Set");
        let [AcornType::Family(datatype, subspace_args)] = params.as_slice() else {
            panic!("second argument should contain Subspace[T, x0]");
        };
        assert_eq!(datatype.name, "Subspace");
        let [DependentTypeArg::Type(AcornType::Variable(param)), DependentTypeArg::Value(AcornValue::Variable(var_id, _))] =
            subspace_args.as_slice()
        else {
            panic!("Subspace arguments should be the type parameter and the first source value argument");
        };
        assert_eq!(param.name, "T0");
        assert_eq!(var_id, &0);
        assert_eq!(
            generic_type.to_string(),
            "(Set[TopologicalSpace], Set[Subspace[TopologicalSpace, x0]]) -> Set[TopologicalSpace]"
        );
    }
}

#[cfg(test)]
mod interleaved_tests {
    use super::*;
    use crate::kernel::clause::Clause;
    use crate::kernel::literal::Literal;
    use crate::kernel::term::Term;
    use crate::module::ModuleId;

    #[test]
    fn test_open_positive_exists_with_interleaved_type_params() {
        // Deep searches produce clauses whose type variables are not a leading
        // prefix of the local context (e.g. [x0: Type, x1: x0, x2: Type]).
        // Opening a positive exists there must produce a witness application
        // that survives roundtrip validation. A validate-mode 30s eval found
        // witness terms like w43[T0*](x1, x0) coming out with mismatched
        // signatures because witness_signature assumed leading type params.
        let mut kctx = KernelContext::new();

        // Single literal: exists(y: x0) { x1 = x1 and x3 = x3 and y = x1 }
        // with x0, x2: Type, x1: x0, x3: x2. Occurrence order puts value var
        // x1 before type var x2, so the normalized ambient context interleaves
        // type and value variables.
        let eq01 = Term::eq(
            Term::new_variable(0),
            Term::new_variable(1),
            Term::new_variable(1),
        );
        let eq23 = Term::eq(
            Term::new_variable(2),
            Term::new_variable(3),
            Term::new_variable(3),
        );
        let eq_bound = Term::eq(
            Term::new_variable(0),
            Term::atom(crate::kernel::atom::Atom::BoundVariable(0)),
            Term::new_variable(1),
        );
        let body = Term::and(Term::and(eq01, eq23), eq_bound);
        let exists_term = Term::exists(Term::new_variable(0), body);

        let context = kctx.parse_local(&["Type", "x0", "Type", "x2"]);
        let clause = Clause::new(vec![Literal::positive(exists_term)], &context);
        eprintln!(
            "clause: {} context {:?}",
            clause,
            clause.get_local_context().get_var_types()
        );

        let reduction = clause
            .positive_exists_reduction(&kctx)
            .expect("expected positive exists reduction");
        let mut registry = WitnessRegistry::new();
        let opening =
            registry.open_positive_exists(&mut kctx, ModuleId::default(), &clause, &reduction);
        eprintln!("reduced: {}", opening.reduction.clause);
        kctx.validate_clause_roundtrip(&opening.reduction.clause)
            .expect("reduced clause should roundtrip");
    }
}

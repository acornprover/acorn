use std::collections::HashMap;

use crate::elaborator::acorn_type::{AcornType, TypeParam};
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
    pub fn referenced_scoped_constants(&self) -> Vec<AtomId> {
        let mut ids = vec![];
        for term in self
            .ambient_context
            .get_var_types()
            .iter()
            .flatten()
            .chain(std::iter::once(&self.return_type))
            .chain(std::iter::once(&self.body))
        {
            for atom in term.iter_atoms() {
                if let Atom::Symbol(Symbol::ScopedConstant(local_id)) = atom {
                    ids.push(*local_id);
                }
            }
        }
        ids.sort();
        ids.dedup();
        ids
    }
}

pub struct WitnessOpening {
    pub term: Term,
    pub reduction: NormalizedClauseTrace,
}

#[derive(Clone, Default)]
pub struct WitnessRegistry {
    by_local_id: HashMap<AtomId, WitnessEntry>,
    next_name_index: u32,
}

impl WitnessRegistry {
    /// Create an empty witness registry for one prover run.
    pub fn new() -> Self {
        Self::default()
    }

    /// Look up witness metadata by the scoped constant id used in proof clauses.
    pub fn get(&self, local_id: AtomId) -> Option<&WitnessEntry> {
        self.by_local_id.get(&local_id)
    }

    /// Iterate over every prover-generated witness recorded for this proof search.
    pub fn iter(&self) -> impl Iterator<Item = (&AtomId, &WitnessEntry)> {
        self.by_local_id.iter()
    }

    /// Open a top-level positive existential by introducing a named witness.
    pub fn open_positive_exists(
        &mut self,
        kernel_context: &mut KernelContext,
        module_id: ModuleId,
        clause: &Clause,
        reduction: &PositiveExistsReduction,
    ) -> WitnessOpening {
        let ambient_context = clause.get_local_context();
        let name = self.next_name(kernel_context, module_id);
        let symbol_type = witness_symbol_type(ambient_context, &reduction.binder_type);
        let symbol = kernel_context.symbol_table.add_constant(
            name.clone(),
            NewConstantType::Local,
            symbol_type,
        );
        let (type_params, _arguments, generic_type) =
            witness_signature(kernel_context, ambient_context, &reduction.binder_type);
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
            );
        }

        let witness = witness_application(symbol, ambient_context);
        let reduced = clause.instantiate_positive_exists_reduction(reduction, witness.clone());

        let Symbol::ScopedConstant(local_id) = symbol else {
            panic!("named witness must be a scoped constant");
        };
        self.by_local_id.insert(
            local_id,
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

    let arguments: Vec<(String, AcornType)> = (num_type_params..ambient_context.len())
        .map(|var_id| {
            let arg_type = ambient_context
                .get_var_type(var_id)
                .expect("witness argument type should exist")
                .clone();
            (
                format!("x{}", var_id - num_type_params),
                kernel_context.quote_type_with_context(arg_type, ambient_context, false),
            )
        })
        .collect();
    let result_type =
        kernel_context.quote_type_with_context(return_type.clone(), ambient_context, false);
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

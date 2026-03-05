use std::collections::HashMap;

use crate::elaborator::acorn_type::{AcornType, TypeParam};
use crate::elaborator::acorn_value::{AcornValue, BinaryOp, ConstantInstance, MatchCase};
use crate::elaborator::names::ConstantName;
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::symbol::Symbol;
use crate::kernel::term::Term;

/// Bridge for converting kernel terms/clauses back into Acorn surface values/types.
pub struct TermBridge<'a> {
    kernel_context: &'a KernelContext,
}

impl<'a> TermBridge<'a> {
    pub fn new(kernel_context: &'a KernelContext) -> Self {
        Self { kernel_context }
    }

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
            | Atom::Symbol(Symbol::Ite)
            | Atom::Symbol(Symbol::Choose) => {
                panic!("logical symbols should be handled in denormalize_term")
            }
            Atom::Symbol(Symbol::GlobalConstant(m, i)) => {
                let name = self
                    .kernel_context
                    .symbol_table
                    .name_for_global_id(*m, *i)
                    .clone();
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
                    AcornValue::constant(name, vec![], acorn_type.clone(), acorn_type, vec![])
                }
            }
            Atom::Symbol(Symbol::ScopedConstant(i)) => {
                let name = self
                    .kernel_context
                    .symbol_table
                    .name_for_local_id(*i)
                    .clone();
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
                    AcornValue::constant(name, vec![], acorn_type.clone(), acorn_type, vec![])
                }
            }
            Atom::FreeVariable(i) => {
                if let Some(map) = arbitrary_names {
                    if let Some(name) = map.get(atom_type) {
                        return AcornValue::constant(
                            name.clone(),
                            vec![],
                            acorn_type.clone(),
                            acorn_type,
                            vec![],
                        );
                    }
                }
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

                {
                    let num_type_params = type_term.as_ref().count_type_params();
                    if num_type_params > 0 {
                        let names: Vec<String> = if let Some(provided) = type_param_names {
                            provided[..num_type_params].to_vec()
                        } else {
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
                let next_var_remapping_storage = var_remapping.map(|mapping| {
                    let mut extended = mapping.to_vec();
                    if extended.len() <= fresh_var as usize {
                        extended.resize(fresh_var as usize + 1, None);
                    }
                    let next_index = extended
                        .iter()
                        .filter_map(|x| *x)
                        .max()
                        .map_or(0, |m| m + 1);
                    extended[fresh_var as usize] = Some(next_index);
                    extended
                });
                let next_var_remapping = next_var_remapping_storage.as_deref();
                let opened_body = body
                    .to_owned()
                    .substitute_bound(0, &Term::new_variable(fresh_var))
                    .shift_bound(0, -1);
                let body_value = self.denormalize_term(
                    &opened_body,
                    &next_context,
                    arbitrary_names,
                    next_var_remapping,
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
                let next_var_remapping_storage = var_remapping.map(|mapping| {
                    let mut extended = mapping.to_vec();
                    if extended.len() <= fresh_var as usize {
                        extended.resize(fresh_var as usize + 1, None);
                    }
                    let next_index = extended
                        .iter()
                        .filter_map(|x| *x)
                        .max()
                        .map_or(0, |m| m + 1);
                    extended[fresh_var as usize] = Some(next_index);
                    extended
                });
                let next_var_remapping = next_var_remapping_storage.as_deref();
                let opened_body = body
                    .to_owned()
                    .substitute_bound(0, &Term::new_variable(fresh_var))
                    .shift_bound(0, -1);
                let body_value = self.denormalize_term(
                    &opened_body,
                    &next_context,
                    arbitrary_names,
                    next_var_remapping,
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
                let next_var_remapping_storage = var_remapping.map(|mapping| {
                    let mut extended = mapping.to_vec();
                    if extended.len() <= fresh_var as usize {
                        extended.resize(fresh_var as usize + 1, None);
                    }
                    let next_index = extended
                        .iter()
                        .filter_map(|x| *x)
                        .max()
                        .map_or(0, |m| m + 1);
                    extended[fresh_var as usize] = Some(next_index);
                    extended
                });
                let next_var_remapping = next_var_remapping_storage.as_deref();
                let opened_body = body
                    .to_owned()
                    .substitute_bound(0, &Term::new_variable(fresh_var))
                    .shift_bound(0, -1);
                let body_value = self.denormalize_term(
                    &opened_body,
                    &next_context,
                    arbitrary_names,
                    next_var_remapping,
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
            Atom::Symbol(Symbol::Choose) => Some(Symbol::Choose),
            _ => None,
        };

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

        if head_type.as_ref().is_type_param_kind() {
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
            let expected_input_type = remaining_head_type
                .as_ref()
                .split_pi()
                .map(|(input, _)| input.to_owned());
            let is_type_arg = expected_input_type
                .as_ref()
                .is_some_and(is_syntactic_kind_term)
                && is_syntactic_type_term(arg, local_context);

            if is_type_arg {
                let typeclass = expected_input_type
                    .as_ref()
                    .and_then(|input| input.as_ref().as_typeclass())
                    .and_then(|tc_id| self.kernel_context.type_store.get_typeclass_by_id(tc_id))
                    .cloned();
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
                    if type_args.len() > 1 || value_args.len() != 2 {
                        panic!("malformed eq term during denormalization: {}", term);
                    }
                    let mut args = value_args.into_iter();
                    return AcornValue::equals(args.next().unwrap(), args.next().unwrap());
                }
                Symbol::Ite => {
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
                Symbol::Choose => {
                    if type_args.len() != 1 || value_args.len() != 1 {
                        panic!("malformed choose term during denormalization: {}", term);
                    }
                    let choice_type = type_args.into_iter().next().unwrap();
                    let predicate = value_args.into_iter().next().unwrap();
                    let AcornValue::Lambda(arg_types, body) = predicate else {
                        panic!(
                            "malformed choose predicate during denormalization (expected lambda): {}",
                            term
                        );
                    };
                    if arg_types.len() != 1 || arg_types[0] != choice_type {
                        panic!(
                            "malformed choose predicate binder type during denormalization: {}",
                            term
                        );
                    }
                    return AcornValue::choose(choice_type, *body);
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

        let mut var_remapping: Vec<Option<u16>> = Vec::new();
        let mut new_index: u16 = 0;
        for i in 0..num_vars {
            let type_term = &var_types_raw[i];
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

        let var_remapping_ref = if var_remapping.iter().any(|x| x.is_none()) {
            Some(var_remapping.as_slice())
        } else {
            None
        };

        let mut denormalized_literals = vec![];
        for literal in &clause.literals {
            denormalized_literals.push(self.denormalize_literal(
                literal,
                local_context,
                arbitrary_names,
                var_remapping_ref,
                type_param_names,
                None,
                instantiate_type_vars,
            ));
        }
        let disjunction = AcornValue::reduce(BinaryOp::Or, denormalized_literals);

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

    pub fn atom_str(&self, atom: &Atom) -> String {
        self.kernel_context.atom_str(atom)
    }
}

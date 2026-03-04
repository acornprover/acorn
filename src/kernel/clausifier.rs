use std::collections::HashMap;

use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::clause::Clause;
use crate::kernel::cnf::Cnf;
use crate::kernel::extended_term::ExtendedTerm;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::local_context::LocalContext;
use crate::kernel::symbol::Symbol;
use crate::kernel::term::Term;
use crate::module::ModuleId;

// Represents a binding for a variable on the stack during normalization.
// Each binding corresponds to a variable in the output clause.
enum TermBinding {
    Bound(Term),
    Free(Term),
}

impl TermBinding {
    /// Get the underlying term regardless of binding type
    fn term(&self) -> &Term {
        match self {
            TermBinding::Bound(t) | TermBinding::Free(t) => t,
        }
    }
}

/// Inner enum for Clausifier to support both ref and mut access to kernel state.
enum ClausifierContext<'a> {
    Ref(&'a KernelContext),
    Mut(&'a mut KernelContext),
}

/// A Clausifier holds state for a single clausification operation.
/// It combines a reference to the KernelContext with operation-scoped state like
/// type_var_map. This lets us share methods between mutable and non-mutable kernel
/// access while keeping per-operation state separate from persistent kernel state.
pub struct Clausifier<'a> {
    inner: ClausifierContext<'a>,

    /// Type variable mapping for polymorphic normalization.
    /// Maps type parameter names to (variable id, kind).
    /// This is set for the duration of normalizing a single polymorphic fact/goal.
    type_var_map: Option<HashMap<String, (AtomId, Term)>>,

    /// The module ID for which we're normalizing. Synthetics created during
    /// normalization will be scoped to this module.
    module_id: ModuleId,
}

impl<'a> Clausifier<'a> {
    /// Create a new Clausifier with immutable access.
    /// Uses ModuleId(0) as a placeholder since immutable contexts don't create synthetics.
    pub fn new_ref(
        kernel_context: &'a KernelContext,
        type_var_map: Option<HashMap<String, (AtomId, Term)>>,
    ) -> Self {
        Clausifier {
            inner: ClausifierContext::Ref(kernel_context),
            type_var_map,
            module_id: ModuleId(0),
        }
    }

    /// Create a new Clausifier with mutable access.
    /// The module_id determines which module synthetics will be scoped to.
    pub fn new_mut(
        kernel_context: &'a mut KernelContext,
        type_var_map: Option<HashMap<String, (AtomId, Term)>>,
        module_id: ModuleId,
    ) -> Self {
        Clausifier {
            inner: ClausifierContext::Mut(kernel_context),
            type_var_map,
            module_id,
        }
    }

    fn as_ref(&self) -> &KernelContext {
        match &self.inner {
            ClausifierContext::Ref(kernel_context) => kernel_context,
            ClausifierContext::Mut(kernel_context) => kernel_context,
        }
    }

    fn as_mut(&mut self) -> Result<&mut KernelContext, String> {
        match &mut self.inner {
            ClausifierContext::Ref(_) => Err("Cannot mutate a Clausifier::Ref".to_string()),
            ClausifierContext::Mut(kernel_context) => Ok(kernel_context),
        }
    }

    fn module_id(&self) -> ModuleId {
        self.module_id
    }

    fn symbol_table(&self) -> &crate::kernel::symbol_table::SymbolTable {
        &self.kernel_context().symbol_table
    }

    fn kernel_context(&self) -> &KernelContext {
        self.as_ref()
    }

    /// Get the type variable map for polymorphic normalization.
    /// Maps type parameter names to (variable id, kind).
    /// In non-polymorphic mode, this always returns None.
    fn type_var_map(&self) -> Option<&HashMap<String, (AtomId, Term)>> {
        self.type_var_map.as_ref()
    }

    /// Get the kinds of type variables in sorted order by their IDs.
    /// Returns the types (e.g., Type) that each type variable has.
    /// Empty in non-polymorphic mode.
    fn get_type_var_kinds(&self) -> Vec<Term> {
        if let Some(type_var_map) = &self.type_var_map {
            let mut entries: Vec<_> = type_var_map.values().collect();
            entries.sort_by_key(|(id, _)| *id);
            entries.iter().map(|(_, kind)| kind.clone()).collect()
        } else {
            vec![]
        }
    }

    /// Term-native normalization path.
    ///
    /// This normalizes an elaborated kernel `Term` directly to clauses.
    pub fn clausify_term(
        &mut self,
        term: &Term,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
    ) -> Result<Vec<Clause>, String> {
        let mut stack = vec![];
        let mut local_context = LocalContext::empty();

        let (mut next_var_id, num_type_params) = if let Some(type_var_map) = self.type_var_map() {
            let mut entries: Vec<_> = type_var_map.values().collect();
            entries.sort_by_key(|(id, _)| *id);
            for (_, var_type) in entries {
                local_context.push_type(var_type.clone());
            }
            (type_var_map.len() as AtomId, type_var_map.len())
        } else {
            (0, 0)
        };

        let cnf = self.term_to_cnf(
            term,
            false,
            &mut stack,
            &mut next_var_id,
            synthesized,
            &mut local_context,
        )?;
        let clauses = cnf.into_clauses_with_pinned(&local_context, num_type_params);

        if self.has_uninhabited_existential_witness(synthesized, &clauses) {
            return Err("exists over a potentially uninhabited type".to_string());
        }

        if self.has_uninhabited_dropped_variable(&local_context, &clauses, num_type_params) {
            return Ok(vec![]);
        }

        Ok(clauses)
    }
    /// If `term` is exactly `symbol(arg1, ..., argN)`, return those arguments.
    ///
    /// We require full application so callers can rely on fixed arity for builtins.
    fn split_symbol_application(
        &self,
        term: &Term,
        symbol: Symbol,
        arity: usize,
    ) -> Option<Vec<Term>> {
        let (head, args) = term.as_ref().split_application_multi()?;
        if args.len() != arity {
            return None;
        }
        match head.get_head_atom() {
            Atom::Symbol(s) if *s == symbol => Some(args),
            _ => None,
        }
    }

    /// If `term` is a lowered datatype eliminator application (`Type.match`),
    /// return `(type_args, scrutinee, cases)` in constructor order.
    fn split_match_eliminator_application(
        &self,
        term: &Term,
    ) -> Option<(Vec<Term>, Term, Vec<(Symbol, Term)>)> {
        let (head, args) = term.as_ref().split_application_multi()?;
        let Atom::Symbol(match_symbol) = head.get_head_atom() else {
            return None;
        };
        let info = self
            .symbol_table()
            .get_match_eliminator_info(*match_symbol)?;
        let match_type = self.symbol_table().get_type(*match_symbol);
        let num_type_args = match_type.as_ref().count_type_params();
        let num_cases = info.constructor_symbols.len();
        if args.len() != num_type_args + 1 + num_cases {
            return None;
        }

        let type_args = args[..num_type_args].to_vec();
        let scrutinee = args[num_type_args].clone();
        let mut cases = Vec::with_capacity(num_cases);
        for (ctor, case_term) in info
            .constructor_symbols
            .iter()
            .zip(args[(num_type_args + 1)..].iter())
        {
            cases.push((*ctor, case_term.clone()));
        }
        Some((type_args, scrutinee, cases))
    }

    /// Open a binder body by replacing bound variable 0 with `replacement`.
    ///
    /// This is the de Bruijn "open" operation: substitute first, then shift down.
    fn open_binder_body(&self, body: &Term, replacement: &Term) -> Term {
        body.substitute_bound(0, replacement).shift_bound(0, -1)
    }

    /// Apply arguments by instantiating leading binders (lambda/forall/exists)
    /// before falling back to ordinary term application.
    ///
    /// Returns `(applied_term, consumed_count)` where `consumed_count` is the
    /// number of arguments consumed by binder instantiation.
    fn instantiate_binder_prefix(&self, function: &Term, args: &[Term]) -> (Term, usize) {
        let mut current = function.clone();
        let mut consumed = 0usize;
        while consumed < args.len() {
            match current.as_ref().decompose() {
                crate::kernel::term::Decomposition::Lambda(_, body)
                | crate::kernel::term::Decomposition::ForAll(_, body)
                | crate::kernel::term::Decomposition::Exists(_, body) => {
                    current = self.open_binder_body(&body.to_owned(), &args[consumed]);
                    consumed += 1;
                }
                _ => break,
            }
        }
        if consumed < args.len() {
            current = current.apply(&args[consumed..]);
        }
        (current, consumed)
    }

    /// Abstract a specific free variable into a new outer binder.
    ///
    /// This both:
    /// 1. Replaces `FreeVariable(var_id)` with `BoundVariable(depth)`, and
    /// 2. Shifts existing bound variables to make room for that new binder.
    fn abstract_free_var_as_bound_at_depth(&self, term: &Term, var_id: AtomId, depth: u16) -> Term {
        match term.as_ref().decompose() {
            crate::kernel::term::Decomposition::Atom(atom) => match atom {
                Atom::FreeVariable(i) if *i == var_id => Term::atom(Atom::BoundVariable(depth)),
                Atom::BoundVariable(i) if *i >= depth => Term::atom(Atom::BoundVariable(*i + 1)),
                _ => term.clone(),
            },
            crate::kernel::term::Decomposition::Application(func, arg) => {
                let new_func =
                    self.abstract_free_var_as_bound_at_depth(&func.to_owned(), var_id, depth);
                let new_arg =
                    self.abstract_free_var_as_bound_at_depth(&arg.to_owned(), var_id, depth);
                new_func.apply(&[new_arg])
            }
            crate::kernel::term::Decomposition::Pi(input, output) => {
                let new_input =
                    self.abstract_free_var_as_bound_at_depth(&input.to_owned(), var_id, depth);
                let new_output =
                    self.abstract_free_var_as_bound_at_depth(&output.to_owned(), var_id, depth + 1);
                Term::pi(new_input, new_output)
            }
            crate::kernel::term::Decomposition::Lambda(input, body) => {
                let new_input =
                    self.abstract_free_var_as_bound_at_depth(&input.to_owned(), var_id, depth);
                let new_body =
                    self.abstract_free_var_as_bound_at_depth(&body.to_owned(), var_id, depth + 1);
                Term::lambda(new_input, new_body)
            }
            crate::kernel::term::Decomposition::ForAll(binder_type, body) => {
                let new_binder_type = self.abstract_free_var_as_bound_at_depth(
                    &binder_type.to_owned(),
                    var_id,
                    depth,
                );
                let new_body =
                    self.abstract_free_var_as_bound_at_depth(&body.to_owned(), var_id, depth + 1);
                Term::forall(new_binder_type, new_body)
            }
            crate::kernel::term::Decomposition::Exists(binder_type, body) => {
                let new_binder_type = self.abstract_free_var_as_bound_at_depth(
                    &binder_type.to_owned(),
                    var_id,
                    depth,
                );
                let new_body =
                    self.abstract_free_var_as_bound_at_depth(&body.to_owned(), var_id, depth + 1);
                Term::exists(new_binder_type, new_body)
            }
        }
    }

    /// Like `Term::get_type_with_context`, but supports lambda terms.
    ///
    /// Lambda type computation opens one binder at a time with a fresh free variable,
    /// computes the body type recursively, then abstracts that variable back into a Pi.
    fn term_type_for_normalization(&self, term: &Term, context: &LocalContext) -> Term {
        if let Some((input, body)) = term.as_ref().split_lambda() {
            let input_type = input.to_owned();
            let fresh_var = context.len() as AtomId;
            let mut nested_context = context.clone();
            nested_context.push_type(input_type.clone());
            let opened_body =
                self.open_binder_body(&body.to_owned(), &Term::new_variable(fresh_var));
            let body_type = self.term_type_for_normalization(&opened_body, &nested_context);
            let output_type = self.abstract_free_var_as_bound_at_depth(&body_type, fresh_var, 0);
            Term::pi(input_type, output_type)
        } else {
            term.get_type_with_context(context, self.kernel_context())
        }
    }
    /// Term-native CNF conversion.
    ///
    /// This converts an elaborated kernel `Term` into CNF.
    /// `true` is `[]`, `false` is `[[]]`, and we intentionally leave tautologies
    /// and redundancy for later clause normalization.
    ///
    /// The `stack` plays the same role as in value normalization:
    /// `TermBinding::Free` tracks forall-introduced variables and
    /// `TermBinding::Bound` tracks existential/skolem substitutions.
    fn term_to_cnf(
        &mut self,
        term: &Term,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        match term.as_ref().decompose() {
            crate::kernel::term::Decomposition::ForAll(binder_type, body) => {
                if !negate {
                    self.forall_term_to_cnf(
                        &binder_type.to_owned(),
                        &body.to_owned(),
                        false,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )
                } else {
                    self.exists_term_to_cnf(
                        &binder_type.to_owned(),
                        &body.to_owned(),
                        true,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )
                }
            }
            crate::kernel::term::Decomposition::Exists(binder_type, body) => {
                if !negate {
                    self.exists_term_to_cnf(
                        &binder_type.to_owned(),
                        &body.to_owned(),
                        false,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )
                } else {
                    self.forall_term_to_cnf(
                        &binder_type.to_owned(),
                        &body.to_owned(),
                        true,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )
                }
            }
            _ => {
                // Builtin logical atoms are recognized by head symbol + arity.
                if let Some(args) = self.split_symbol_application(term, Symbol::Not, 1) {
                    return self.term_to_cnf(&args[0], !negate, stack, next_var_id, synth, context);
                }
                if let Some(args) = self.split_symbol_application(term, Symbol::And, 2) {
                    if !negate {
                        return self.term_and_to_cnf(
                            &args[0],
                            &args[1],
                            false,
                            false,
                            stack,
                            next_var_id,
                            synth,
                            context,
                        );
                    }
                    return self.term_or_to_cnf(
                        &args[0],
                        &args[1],
                        true,
                        true,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    );
                }
                if let Some(args) = self.split_symbol_application(term, Symbol::Or, 2) {
                    // Keep an or-expression inline if it has an and-child, instead of
                    // distributing `or` over that conjunction.
                    let left_is_and = self
                        .split_symbol_application(&args[0], Symbol::And, 2)
                        .is_some();
                    let right_is_and = self
                        .split_symbol_application(&args[1], Symbol::And, 2)
                        .is_some();
                    if left_is_and || right_is_and {
                        let simple_term =
                            self.term_to_simple_term(term, stack, next_var_id, synth, context)?;
                        let literal = Literal::from_signed_term(simple_term, !negate);
                        return Ok(Cnf::from_literal(literal));
                    }

                    if !negate {
                        return self.term_or_to_cnf(
                            &args[0],
                            &args[1],
                            false,
                            false,
                            stack,
                            next_var_id,
                            synth,
                            context,
                        );
                    }
                    return self.term_and_to_cnf(
                        &args[0],
                        &args[1],
                        true,
                        true,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    );
                }
                if let Some(args) = self.split_symbol_application(term, Symbol::Eq, 3) {
                    return self.term_eq_to_cnf(
                        &args[1],
                        &args[2],
                        negate,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    );
                }
                #[cfg(feature = "iite")]
                if self
                    .split_symbol_application(term, Symbol::Ite, 4)
                    .is_some()
                {
                    let inline_ite =
                        self.term_to_simple_term(term, stack, next_var_id, synth, context)?;
                    let literal = Literal::from_signed_term(inline_ite, !negate);
                    return Ok(Cnf::from_literal(literal));
                }

                #[cfg(not(feature = "iite"))]
                if let Some(args) = self.split_symbol_application(term, Symbol::Ite, 4) {
                    let cond_cnf =
                        self.term_to_cnf(&args[1], false, stack, next_var_id, synth, context)?;
                    let Some(cond_lit) = cond_cnf.to_literal() else {
                        return Err("term 'ite' condition is too complicated".to_string());
                    };
                    let then_cnf =
                        self.term_to_cnf(&args[2], negate, stack, next_var_id, synth, context)?;
                    let else_cnf =
                        self.term_to_cnf(&args[3], negate, stack, next_var_id, synth, context)?;
                    return Ok(Cnf::cnf_if(cond_lit, then_cnf, else_cnf));
                }

                if let Some((function, args)) = term.as_ref().split_application_multi() {
                    match function.as_ref().decompose() {
                        crate::kernel::term::Decomposition::Lambda(_, _)
                        | crate::kernel::term::Decomposition::ForAll(_, _)
                        | crate::kernel::term::Decomposition::Exists(_, _) => {
                            let (applied, consumed) =
                                self.instantiate_binder_prefix(&function.to_owned(), &args);
                            for arg in args.iter().take(consumed) {
                                stack.push(TermBinding::Bound(arg.clone()));
                            }
                            let answer = self.term_to_cnf(
                                &applied,
                                negate,
                                stack,
                                next_var_id,
                                synth,
                                context,
                            );
                            stack.truncate(stack.len().saturating_sub(consumed));
                            return answer;
                        }
                        _ => {}
                    }
                }

                if term == &Term::new_true() {
                    return if negate {
                        Ok(Cnf::false_value())
                    } else {
                        Ok(Cnf::true_value())
                    };
                }
                if term == &Term::new_false() {
                    return if negate {
                        Ok(Cnf::true_value())
                    } else {
                        Ok(Cnf::false_value())
                    };
                }

                // Everything else must normalize to a single signed literal.
                let simple_term =
                    self.term_to_simple_term(term, stack, next_var_id, synth, context)?;
                let literal = Literal::from_signed_term(simple_term, !negate);
                Ok(Cnf::from_literal(literal))
            }
        }
    }

    fn forall_term_to_cnf(
        &mut self,
        binder_type: &Term,
        body: &Term,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        let var_id = *next_var_id;
        *next_var_id += 1;
        context.push_type(binder_type.clone());
        let var = Term::new_variable(var_id);
        stack.push(TermBinding::Free(var.clone()));
        let opened_body = self.open_binder_body(body, &var);
        let result = self.term_to_cnf(
            &opened_body,
            negate,
            stack,
            next_var_id,
            synthesized,
            context,
        )?;
        stack.pop();
        Ok(result)
    }

    fn exists_term_to_cnf(
        &mut self,
        binder_type: &Term,
        body: &Term,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        let skolem_terms = self.make_skolem_terms_from_type_terms(
            std::slice::from_ref(binder_type),
            stack,
            synthesized,
            context,
        )?;
        let skolem_term = skolem_terms.into_iter().next().unwrap();
        stack.push(TermBinding::Bound(skolem_term.clone()));
        let opened_body = self.open_binder_body(body, &skolem_term);
        let result = self.term_to_cnf(
            &opened_body,
            negate,
            stack,
            next_var_id,
            synthesized,
            context,
        )?;
        stack.pop();
        Ok(result)
    }

    fn make_skolem_terms_from_type_terms(
        &mut self,
        skolem_type_terms: &[Term],
        stack: &Vec<TermBinding>,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
        context: &LocalContext,
    ) -> Result<Vec<Term>, String> {
        let mut args = vec![];
        let mut arg_type_terms: Vec<Term> = vec![];
        let mut seen_vars = std::collections::HashSet::new();

        if let Some(type_var_map) = self.type_var_map() {
            let mut entries: Vec<_> = type_var_map.values().collect();
            entries.sort_by_key(|(id, _)| *id);
            for (var_id, var_type) in entries {
                let var_term = Term::new_variable(*var_id);
                args.push(var_term);
                arg_type_terms.push(var_type.clone());
                seen_vars.insert(*var_id);
            }
        }

        for binding in stack.iter() {
            for (var_id, closed_type) in binding.term().collect_vars(context) {
                if seen_vars.insert(var_id) {
                    let var_term = Term::new_variable(var_id);
                    args.push(var_term);
                    arg_type_terms.push(closed_type);
                }
            }
        }

        let num_type_params = self.type_var_map().map_or(0, |m| m.len()) as u16;
        let mut non_type_param_index = 0u16;
        let arg_type_terms: Vec<Term> = arg_type_terms
            .into_iter()
            .map(|t| {
                if t.as_ref().is_type_param_kind() {
                    t
                } else {
                    let depth = non_type_param_index;
                    non_type_param_index += 1;
                    t.convert_free_to_bound_with_depth(num_type_params, depth)
                }
            })
            .collect();

        let mut output = vec![];
        for t in skolem_type_terms {
            let non_type_param_args = arg_type_terms.len() - num_type_params as usize;
            let result_type_term =
                t.convert_free_to_bound_with_depth(num_type_params, non_type_param_args as u16);

            let mut skolem_type_term = result_type_term;
            for arg_type in arg_type_terms.iter().rev() {
                skolem_type_term = Term::pi(arg_type.clone(), skolem_type_term);
            }

            let module_id = self.module_id();
            let skolem_id = self
                .as_mut()?
                .declare_synthetic_atom_with_type_term(module_id, skolem_type_term)?;
            synthesized.push(skolem_id);
            let (m, i) = skolem_id;
            let skolem_atom = Atom::Symbol(Symbol::Synthetic(m, i));
            let skolem_term = Term::new(skolem_atom, args.clone());
            output.push(skolem_term);
        }
        Ok(output)
    }

    fn make_skolem_term_from_type_term(
        &mut self,
        skolem_type_term: &Term,
        stack: &Vec<TermBinding>,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
        context: &LocalContext,
    ) -> Result<Term, String> {
        let mut terms = self.make_skolem_terms_from_type_terms(
            std::slice::from_ref(skolem_type_term),
            stack,
            synthesized,
            context,
        )?;
        Ok(terms.pop().unwrap())
    }

    fn term_and_to_cnf(
        &mut self,
        left: &Term,
        right: &Term,
        negate_left: bool,
        negate_right: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        let left = self.term_to_cnf(left, negate_left, stack, next_var_id, synthesized, context)?;
        let right = self.term_to_cnf(
            right,
            negate_right,
            stack,
            next_var_id,
            synthesized,
            context,
        )?;
        Ok(left.and(right))
    }

    fn term_or_to_cnf(
        &mut self,
        left: &Term,
        right: &Term,
        negate_left: bool,
        negate_right: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        let left = self.term_to_cnf(left, negate_left, stack, next_var_id, synthesized, context)?;
        let right = self.term_to_cnf(
            right,
            negate_right,
            stack,
            next_var_id,
            synthesized,
            context,
        )?;
        Ok(left.or(right))
    }

    fn try_simple_term_to_term(&self, term: &Term) -> Result<Option<Term>, String> {
        match self.try_simple_term_to_signed_term(term)? {
            Some((t, true)) => Ok(Some(t)),
            Some((_t, false)) => Ok(None),
            None => Ok(None),
        }
    }

    fn try_simple_term_to_signed_term(&self, term: &Term) -> Result<Option<(Term, bool)>, String> {
        if let Some(args) = self.split_symbol_application(term, Symbol::Not, 1) {
            return match self.try_simple_term_to_signed_term(&args[0])? {
                None => Ok(None),
                Some((t, sign)) => Ok(Some((t, !sign))),
            };
        }

        match term.as_ref().decompose() {
            crate::kernel::term::Decomposition::ForAll(_, _)
            | crate::kernel::term::Decomposition::Exists(_, _)
            | crate::kernel::term::Decomposition::Lambda(_, _) => Ok(None),
            _ => {
                if term == &Term::new_true() {
                    return Ok(Some((Term::new_true(), true)));
                }
                if term == &Term::new_false() {
                    return Ok(Some((Term::new_true(), false)));
                }

                if self
                    .split_symbol_application(term, Symbol::And, 2)
                    .is_some()
                    || self.split_symbol_application(term, Symbol::Or, 2).is_some()
                    || self.split_symbol_application(term, Symbol::Eq, 3).is_some()
                    || self
                        .split_symbol_application(term, Symbol::Ite, 4)
                        .is_some()
                {
                    return Ok(None);
                }

                if let Some((function, arg_terms)) = term.as_ref().split_application_multi() {
                    let function = function.to_owned();
                    let func_term = match self.try_simple_term_to_term(&function)? {
                        Some(t) => t,
                        None => return Ok(None),
                    };
                    let head = *func_term.get_head_atom();
                    let mut args = func_term.args().to_vec();
                    for arg in arg_terms {
                        let arg_term = match self.try_simple_term_to_term(&arg)? {
                            Some(t) => t,
                            None => return Ok(None),
                        };
                        args.push(arg_term);
                    }
                    return Ok(Some((Term::new(head, args), true)));
                }

                Ok(Some((term.clone(), true)))
            }
        }
    }

    fn apply_term_to_cnf(
        &mut self,
        function: &Term,
        args: Vec<ExtendedTerm>,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synthesized: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        match function.as_ref().decompose() {
            crate::kernel::term::Decomposition::Lambda(_, _)
            | crate::kernel::term::Decomposition::ForAll(_, _)
            | crate::kernel::term::Decomposition::Exists(_, _) => {
                let mut arg_terms = Vec::with_capacity(args.len());
                for arg in args {
                    arg_terms.push(arg.to_term()?);
                }
                let (applied, consumed) = self.instantiate_binder_prefix(function, &arg_terms);
                for arg in arg_terms.iter().take(consumed) {
                    stack.push(TermBinding::Bound(arg.clone()));
                }
                let answer =
                    self.term_to_cnf(&applied, negate, stack, next_var_id, synthesized, context);
                stack.truncate(stack.len().saturating_sub(consumed));
                return answer;
            }
            _ => {}
        }

        let extended = self.apply_term_to_extended_term(
            function,
            args,
            stack,
            next_var_id,
            synthesized,
            context,
        )?;
        match extended {
            ExtendedTerm::Term(term) => {
                let literal = Literal::from_signed_term(term, !negate);
                Ok(Cnf::from_literal(literal))
            }
            _ => Err("unhandled case: non-term application".to_string()),
        }
    }

    /// Convert `left = right` (or `!=` when `negate`) to CNF.
    ///
    /// For function-typed terms, this performs extensional reasoning by applying
    /// either fresh variables (`forall`-style) or skolems (`exists`-style) to both
    /// sides, then reducing to equality on results.
    fn term_eq_to_cnf(
        &mut self,
        left: &Term,
        right: &Term,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        if let Some((type_args, scrutinee, cases)) = self.split_match_eliminator_application(right)
        {
            let datatype_type_args = type_args[..type_args.len().saturating_sub(1)].to_vec();
            let mut answer = Cnf::true_value();
            for (constructor_symbol, case_term) in &cases {
                let mut constructor_args = datatype_type_args.clone();
                let mut case_value = case_term.clone();
                let stack_len = stack.len();

                while let Some((input, body)) = case_value.as_ref().split_lambda() {
                    let input_type = input.to_owned();
                    let var_id = *next_var_id;
                    *next_var_id += 1;
                    context.push_type(input_type.clone());
                    let var = Term::new_variable(var_id);
                    constructor_args.push(var.clone());
                    stack.push(TermBinding::Free(var.clone()));
                    case_value = self.open_binder_body(&body.to_owned(), &var);
                }

                let pattern = Term::new(Atom::Symbol(*constructor_symbol), constructor_args);
                let condition = self.term_eq_to_cnf(
                    &scrutinee,
                    &pattern,
                    false,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?;
                let conclusion = self.term_eq_to_cnf(
                    left,
                    &case_value,
                    negate,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?;
                answer = answer.and(condition.negate().or(conclusion));

                stack.truncate(stack_len);
            }
            return Ok(answer);
        }

        if let Some((type_args, scrutinee, cases)) = self.split_match_eliminator_application(left) {
            let datatype_type_args = type_args[..type_args.len().saturating_sub(1)].to_vec();
            let mut answer = Cnf::true_value();
            for (constructor_symbol, case_term) in &cases {
                let mut constructor_args = datatype_type_args.clone();
                let mut case_value = case_term.clone();
                let stack_len = stack.len();

                while let Some((input, body)) = case_value.as_ref().split_lambda() {
                    let input_type = input.to_owned();
                    let var_id = *next_var_id;
                    *next_var_id += 1;
                    context.push_type(input_type.clone());
                    let var = Term::new_variable(var_id);
                    constructor_args.push(var.clone());
                    stack.push(TermBinding::Free(var.clone()));
                    case_value = self.open_binder_body(&body.to_owned(), &var);
                }

                let pattern = Term::new(Atom::Symbol(*constructor_symbol), constructor_args);
                let condition = self.term_eq_to_cnf(
                    &scrutinee,
                    &pattern,
                    false,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?;
                let conclusion = self.term_eq_to_cnf(
                    right,
                    &case_value,
                    negate,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?;
                answer = answer.and(condition.negate().or(conclusion));

                stack.truncate(stack_len);
            }
            return Ok(answer);
        }

        let left_type = self.term_type_for_normalization(left, context);
        let mut fn_arg_types = vec![];
        let mut result_type = left_type.clone();
        while let Some((input, output)) = result_type.as_ref().split_pi() {
            fn_arg_types.push(input.to_owned());
            result_type = output.to_owned();
        }

        if !fn_arg_types.is_empty() {
            if result_type == Term::bool_type() {
                if negate {
                    // f != g for Bool-valued functions:
                    // skolemize an argument tuple and assert result disagreement.
                    let arg_terms = self.make_skolem_terms_from_type_terms(
                        &fn_arg_types,
                        stack,
                        synth,
                        context,
                    )?;
                    let args: Vec<_> = arg_terms.iter().cloned().map(ExtendedTerm::Term).collect();
                    let left_pos = self.apply_term_to_cnf(
                        left,
                        args.clone(),
                        false,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )?;
                    let left_neg = self.apply_term_to_cnf(
                        left,
                        args.clone(),
                        true,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )?;
                    let right_pos = self.apply_term_to_cnf(
                        right,
                        args.clone(),
                        false,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )?;
                    let right_neg = self.apply_term_to_cnf(
                        right,
                        args,
                        true,
                        stack,
                        next_var_id,
                        synth,
                        context,
                    )?;

                    if let Some((left_term, left_sign)) = left_pos.match_negated(&left_neg) {
                        if let Some((right_term, right_sign)) = right_pos.match_negated(&right_neg)
                        {
                            let positive = left_sign != right_sign;
                            let literal =
                                Literal::new(positive, left_term.clone(), right_term.clone());
                            return Ok(Cnf::from_literal(literal));
                        }
                    }

                    let some = left_pos.or(right_pos);
                    let not_both = left_neg.or(right_neg);
                    return Ok(not_both.and(some));
                }

                // f = g for Bool-valued functions:
                // introduce fresh universally-quantified arguments.
                let mut args = vec![];
                for arg_type_term in &fn_arg_types {
                    let var_id = *next_var_id;
                    *next_var_id += 1;
                    context.push_type(arg_type_term.clone());
                    args.push(ExtendedTerm::Term(Term::new_variable(var_id)));
                }
                let left_pos = self.apply_term_to_cnf(
                    left,
                    args.clone(),
                    false,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?;
                let left_neg = self.apply_term_to_cnf(
                    left,
                    args.clone(),
                    true,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?;
                let right_pos = self.apply_term_to_cnf(
                    right,
                    args.clone(),
                    false,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?;
                let right_neg =
                    self.apply_term_to_cnf(right, args, true, stack, next_var_id, synth, context)?;

                if let Some((left_term, left_sign)) = left_pos.match_negated(&left_neg) {
                    if let Some((right_term, right_sign)) = right_pos.match_negated(&right_neg) {
                        let positive = left_sign == right_sign;
                        let literal = Literal::new(positive, left_term.clone(), right_term.clone());
                        return Ok(Cnf::from_literal(literal));
                    }
                }

                let l_imp_r = left_neg.or(right_pos);
                let r_imp_l = left_pos.or(right_neg);
                return Ok(l_imp_r.and(r_imp_l));
            }

            let left = self.term_to_extended_term(left, stack, next_var_id, synth, context)?;
            let right = self.term_to_extended_term(right, stack, next_var_id, synth, context)?;
            if negate {
                let args =
                    self.make_skolem_terms_from_type_terms(&fn_arg_types, stack, synth, context)?;
                return left.apply(&args).eq_to_cnf(right.apply(&args), true);
            }

            let mut args = vec![];
            for arg_type_term in &fn_arg_types {
                let var_id = *next_var_id;
                *next_var_id += 1;
                context.push_type(arg_type_term.clone());
                args.push(Term::new_variable(var_id));
            }
            return left.apply(&args).eq_to_cnf(right.apply(&args), false);
        }

        if left_type == Term::bool_type() {
            if let Some((left_term, left_sign)) = self.try_simple_term_to_signed_term(left)? {
                if let Some((right_term, right_sign)) =
                    self.try_simple_term_to_signed_term(right)?
                {
                    let positive = (left_sign == right_sign) ^ negate;
                    let literal = Literal::new(positive, left_term, right_term);
                    return Ok(Cnf::from_literal(literal));
                }
            }

            if negate {
                let some = self.term_or_to_cnf(
                    left,
                    right,
                    true,
                    true,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?;
                let not_both = self.term_or_to_cnf(
                    left,
                    right,
                    false,
                    false,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?;
                return Ok(some.and(not_both));
            }

            let l_imp_r =
                self.term_or_to_cnf(left, right, true, false, stack, next_var_id, synth, context)?;
            let r_imp_l =
                self.term_or_to_cnf(left, right, false, true, stack, next_var_id, synth, context)?;
            return Ok(l_imp_r.and(r_imp_l));
        }

        let left = self.term_to_extended_term(left, stack, next_var_id, synth, context)?;
        let right = self.term_to_extended_term(right, stack, next_var_id, synth, context)?;
        left.eq_to_cnf(right, negate)
    }

    /// Introduce (or reuse) a synthetic term that stands for `value` at `value_type`.
    ///
    /// This is the bridge from rich term structure to a simple atom that later CNF steps can
    /// refer to. We create a fresh synthetic application `s(...)`, define it with `s = value`,
    /// and register the definition in the synthetic registry so equivalent definitions can be
    /// deduplicated.
    fn synthesize_term_from_term(
        &mut self,
        value: &Term,
        value_type: &Term,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Term, String> {
        let skolem_term =
            self.make_skolem_term_from_type_term(value_type, stack, synth, context)?;
        let skolem_id = if let Atom::Symbol(Symbol::Synthetic(m, id)) = *skolem_term.get_head_atom()
        {
            (m, id)
        } else {
            return Err("internal error: skolem term is not synthetic".to_string());
        };

        let synthetic_type = self
            .kernel_context()
            .symbol_table
            .get_type(Symbol::Synthetic(skolem_id.0, skolem_id.1))
            .clone();

        let type_vars = self.get_type_var_kinds();
        let synthetic_types = vec![synthetic_type.clone()];

        let definition_cnf = self.term_eq_to_cnf(
            &skolem_term,
            value,
            false,
            stack,
            next_var_id,
            synth,
            context,
        )?;
        let num_type_vars = type_vars.len();
        let clauses = definition_cnf
            .clone()
            .into_clauses_with_pinned(context, num_type_vars);
        let key_clauses: Vec<Clause> = clauses
            .iter()
            .map(|c| c.invalidate_synthetics(&[skolem_id]))
            .collect();

        if let Some(existing_def) = self.kernel_context().synthetic_registry.lookup_by_key(
            &type_vars,
            &synthetic_types,
            &key_clauses,
        ) {
            let (existing_m, existing_id) = existing_def.atoms[0];
            let existing_atom = Atom::Symbol(Symbol::Synthetic(existing_m, existing_id));
            Ok(Term::new(existing_atom, skolem_term.args().to_vec()))
        } else {
            let clauses = definition_cnf.into_clauses_with_pinned(context, num_type_vars);
            self.as_mut()?.define_synthetic_atoms(
                vec![skolem_id],
                type_vars,
                vec![synthetic_type],
                clauses,
                None,
            )?;
            Ok(skolem_term)
        }
    }

    fn arg_term_to_extended(
        &mut self,
        term: &Term,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<ExtendedTerm, String> {
        if term.as_ref().is_lambda() {
            let lambda_type = self.term_type_for_normalization(term, context);
            let skolem_term = self.synthesize_term_from_term(
                term,
                &lambda_type,
                stack,
                next_var_id,
                synth,
                context,
            )?;
            return Ok(ExtendedTerm::Term(skolem_term));
        }

        // For boolean arguments, synthesize non-simple formulas
        // (and/or/eq/not/forall/exists/match/etc) into atoms.
        let term_type = self.term_type_for_normalization(term, context);
        if term_type == Term::bool_type() && self.try_simple_term_to_term(term)?.is_none() {
            // Keep complex booleans inline as terms.
            return Ok(ExtendedTerm::Term(term.clone()));
        }

        self.term_to_extended_term(term, stack, next_var_id, synth, context)
    }

    /// Apply `function` to `args`, pushing a single conditional outward when possible.
    ///
    /// This preserves the old normalization behavior where
    /// `f(if c then a else b, d)` becomes `if c then f(a, d) else f(b, d)`.
    fn apply_term_to_extended_term(
        &mut self,
        function: &Term,
        args: Vec<ExtendedTerm>,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<ExtendedTerm, String> {
        if function.as_ref().is_lambda() {
            let func_ext =
                self.term_to_extended_term(function, stack, next_var_id, synth, context)?;
            let mut arg_terms = vec![];
            for arg in args {
                arg_terms.push(self.extended_term_to_term(arg, context, synth)?);
            }
            return Ok(func_ext.apply(&arg_terms));
        }

        let mut cond: Option<Literal> = None;
        let mut spine1 = vec![];
        let mut spine2 = vec![];

        match self.term_to_extended_term(function, stack, next_var_id, synth, context)? {
            ExtendedTerm::Term(t) => {
                spine1.push(t);
            }
            ExtendedTerm::If(sub_cond, sub_then, sub_else) => {
                cond = Some(sub_cond);
                spine1.push(sub_then);
                spine2.push(sub_else);
            }
            ExtendedTerm::Lambda(_, _) => {
                return Err("unhandled case: secret lambda".to_string());
            }
        }

        for arg in args {
            match arg {
                ExtendedTerm::Term(t) => {
                    if !spine2.is_empty() {
                        spine2.push(t.clone());
                    }
                    spine1.push(t);
                }
                ExtendedTerm::If(sub_cond, sub_then, sub_else) => {
                    if !spine2.is_empty() {
                        return Err("unhandled case: multiple ite args".to_string());
                    }
                    cond = Some(sub_cond);
                    spine2.extend(spine1.iter().cloned());
                    spine1.push(sub_then);
                    spine2.push(sub_else);
                }
                ExtendedTerm::Lambda(_, _) => {
                    return Err("unhandled case: lambda arg".to_string());
                }
            }
        }

        match cond {
            Some(cond) => {
                assert_eq!(spine1.len(), spine2.len());
                let then_term = Term::from_spine(spine1);
                let else_term = Term::from_spine(spine2);
                Ok(ExtendedTerm::If(cond, then_term, else_term))
            }
            None => {
                assert!(spine2.is_empty());
                Ok(ExtendedTerm::Term(Term::from_spine(spine1)))
            }
        }
    }

    /// Convert a term into `ExtendedTerm`, introducing synthetic atoms as needed.
    ///
    /// `ExtendedTerm::If` is used as an intermediate form to avoid losing branching
    /// structure before we synthesize a simple term.
    fn term_to_extended_term(
        &mut self,
        term: &Term,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<ExtendedTerm, String> {
        if let Some(args) = self.split_symbol_application(term, Symbol::Ite, 4) {
            #[cfg(feature = "iite")]
            let cond_lit = Literal::from_signed_term(args[1].clone(), true);

            #[cfg(not(feature = "iite"))]
            let cond_cnf = self.term_to_cnf(&args[1], false, stack, next_var_id, synth, context)?;
            #[cfg(not(feature = "iite"))]
            let cond_lit = if cond_cnf.is_literal() {
                cond_cnf.to_literal().unwrap()
            } else {
                self.synthesize_literal_from_cnf(cond_cnf, stack, synth, context)?
            };
            let then_ext =
                self.term_to_extended_term(&args[2], stack, next_var_id, synth, context)?;
            let then_branch = self.extended_term_to_term(then_ext, context, synth)?;
            let else_ext =
                self.term_to_extended_term(&args[3], stack, next_var_id, synth, context)?;
            let else_branch = self.extended_term_to_term(else_ext, context, synth)?;
            return Ok(ExtendedTerm::If(cond_lit, then_branch, else_branch));
        }

        if let Some((function, arg_terms)) = term.as_ref().split_application_multi() {
            let mut arg_exts = vec![];
            for arg in arg_terms {
                arg_exts.push(self.arg_term_to_extended(
                    &arg,
                    stack,
                    next_var_id,
                    synth,
                    context,
                )?);
            }
            return self.apply_term_to_extended_term(
                &function,
                arg_exts,
                stack,
                next_var_id,
                synth,
                context,
            );
        }

        match term.as_ref().decompose() {
            crate::kernel::term::Decomposition::Lambda(_, _) => {
                let mut args = vec![];
                let mut current = term.clone();
                while let Some((input, body)) = current.as_ref().split_lambda() {
                    let input_type = input.to_owned();
                    let var_id = *next_var_id;
                    *next_var_id += 1;
                    context.push_type(input_type.clone());
                    let var = Term::new_variable(var_id);
                    args.push((var_id, input_type));
                    stack.push(TermBinding::Free(var.clone()));
                    current = self.open_binder_body(&body.to_owned(), &var);
                }

                let body_ext =
                    self.term_to_extended_term(&current, stack, next_var_id, synth, context)?;
                let body_term = self.extended_term_to_term(body_ext, context, synth)?;

                for _ in 0..args.len() {
                    stack.pop();
                }
                Ok(ExtendedTerm::Lambda(args, body_term))
            }
            crate::kernel::term::Decomposition::ForAll(_, _)
            | crate::kernel::term::Decomposition::Exists(_, _) => {
                Err(format!("quantifier in unexpected term position: {}", term))
            }
            _ => {
                if term == &Term::new_false() {
                    return Err("false literal in unexpected position".to_string());
                }
                if term == &Term::new_true() {
                    return Ok(ExtendedTerm::Term(Term::new_true()));
                }

                let term_type = self.term_type_for_normalization(term, context);
                if term_type == Term::bool_type() {
                    if let Some(simple) = self.try_simple_term_to_term(term)? {
                        return Ok(ExtendedTerm::Term(simple));
                    }
                    // Keep complex booleans inline as terms.
                    Ok(ExtendedTerm::Term(term.clone()))
                } else {
                    Ok(ExtendedTerm::Term(term.clone()))
                }
            }
        }
    }

    fn term_to_simple_term(
        &mut self,
        term: &Term,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        synth: &mut Vec<(ModuleId, AtomId)>,
        context: &mut LocalContext,
    ) -> Result<Term, String> {
        if let Some(simple) = self.try_simple_term_to_term(term)? {
            return Ok(simple);
        }
        let ext = self.term_to_extended_term(term, stack, next_var_id, synth, context)?;
        self.extended_term_to_term(ext, context, synth)
    }

    /// Checks if any forall variables dropped during normalization have uninhabited types.
    /// This is specifically for detecting vacuous quantification over unconstrained type parameters.
    ///
    /// For example, `forall(x: T) { P }` where T is an unconstrained type parameter and x
    /// doesn't appear in P. If T is empty, this is vacuously true; if T is inhabited, it's
    /// equivalent to P. We can't represent this ambiguity in CNF, so we return empty clauses.
    fn has_uninhabited_dropped_variable(
        &self,
        original_context: &LocalContext,
        clauses: &[Clause],
        skip_vars: usize,
    ) -> bool {
        use std::collections::HashSet;

        // Collect all types that appear in ANY clause's context.
        let mut all_clause_types: HashSet<&Term> = HashSet::new();
        for clause in clauses {
            let clause_ctx = clause.get_local_context();
            for i in 0..clause_ctx.len() {
                if let Some(var_type) = clause_ctx.get_var_type(i) {
                    all_clause_types.insert(var_type);
                }
            }
        }

        // Build a context for the type parameters (first skip_vars entries)
        let mut type_param_context = LocalContext::empty();
        for i in 0..skip_vars {
            if let Some(t) = original_context.get_var_type(i) {
                type_param_context.push_type(t.clone());
            }
        }

        // Check each variable type in the original context, skipping type parameters
        for var_id in skip_vars..original_context.len() {
            if let Some(var_type) = original_context.get_var_type(var_id) {
                // If this type doesn't appear in ANY clause context, variables of this type were dropped
                if !all_clause_types.contains(var_type) {
                    // Check if this type is provably inhabited
                    if !self
                        .kernel_context()
                        .provably_inhabited(var_type, Some(&type_param_context))
                    {
                        return true;
                    }
                }
            }
        }

        false
    }

    /// Checks if any existential witnesses were created for uninhabited types.
    /// This prevents unsound definitions where we assert existence over empty types.
    /// For example: `let inhabited[T]: Bool = exists(x: T) { true }` would create a witness
    /// for type T, but T might be empty, making the exists claim invalid.
    ///
    /// This function only checks witnesses that don't appear in any clause. The rationale is:
    /// - If a witness IS used in clauses (like `exists(x: T) { P(x) }`), then the clause P(x)
    ///   provides some constraint on the witness, and we allow it.
    /// - If a witness is NOT used (like `exists(x: T) { true }`), we're purely asserting
    ///   inhabitedness of T with no justification, which is unsound if T is empty.
    ///
    /// Note: The `synthesized` list includes all synthetics (existential witnesses, Tseitin
    /// abbreviations, etc.), but the "unused" filter effectively isolates the problematic
    /// existential cases since definition-style synthetics are always used in their defining clauses.
    fn has_uninhabited_existential_witness(
        &self,
        synthesized: &[(ModuleId, AtomId)],
        clauses: &[Clause],
    ) -> bool {
        use std::collections::HashSet;

        // Collect all synthetic atoms that appear in any clause
        let mut used_synthetics: HashSet<(ModuleId, AtomId)> = HashSet::new();
        for clause in clauses {
            for lit in &clause.literals {
                for atom in lit.left.iter_atoms() {
                    if let &Atom::Symbol(Symbol::Synthetic(m, id)) = atom {
                        used_synthetics.insert((m, id));
                    }
                }
                for atom in lit.right.iter_atoms() {
                    if let &Atom::Symbol(Symbol::Synthetic(m, id)) = atom {
                        used_synthetics.insert((m, id));
                    }
                }
            }
        }

        // Check each synthesized atom
        for &(module_id, local_id) in synthesized {
            // If this synthetic appears in clauses, it's constrained by something, so skip
            if used_synthetics.contains(&(module_id, local_id)) {
                continue;
            }

            // Get the synthetic's type
            let synth_type = self
                .kernel_context()
                .symbol_table
                .get_type(Symbol::Synthetic(module_id, local_id));

            // Get the result type by stripping off type parameter Pis only.
            // Type parameter Pis have TypeSort (or Typeclass) as the input type.
            // For example, a witness with type Pi(Type, b0) represents
            // "for any type T, return a value of type T".
            // We DON'T strip function type Pis like Pi(Nat, Bool) because those
            // represent function types, not type parameters.
            let mut result_type = synth_type.as_ref();
            let mut stripped_types = Vec::new();
            while let Some((input_type, body)) = result_type.split_pi() {
                // Only strip if this is a type parameter (input is Type/TypeSort or Typeclass)
                if !input_type.is_type_param_kind() {
                    break;
                }
                stripped_types.push(input_type.to_owned());
                result_type = body;
            }

            // Build context with types in reverse order (innermost first) to match de Bruijn indices
            let mut type_param_context = LocalContext::empty();
            for t in stripped_types.into_iter().rev() {
                type_param_context.push_type(t);
            }

            // The result term keeps its original bound variable indices
            let result_term = result_type.to_owned();

            let is_inhabited = self
                .kernel_context()
                .provably_inhabited(&result_term, Some(&type_param_context));
            if !is_inhabited {
                return true;
            }
        }

        false
    }

    /// This returns clauses that are denormalized in the sense that they sort literals,
    /// but don't filter out redundant or tautological literals.
    /// This is the format that the Checker uses.
    /// If you call normalize() on the clause afterwards, you should get the normalized one.
    pub fn clausify_term_to_denormalized_clauses(
        &mut self,
        term: &Term,
    ) -> Result<Vec<Clause>, String> {
        let mut output = vec![];
        let mut context = LocalContext::empty();

        // In polymorphic mode, pre-allocate space for type variables
        // This ensures value variable IDs don't collide with type variable IDs
        let mut next_var_id = if let Some(type_var_map) = self.type_var_map() {
            // Pre-populate local_context with the type of each type variable.
            let mut entries: Vec<_> = type_var_map.values().collect();
            entries.sort_by_key(|(id, _)| *id);
            for (_, var_type) in entries {
                context.push_type(var_type.clone());
            }
            type_var_map.len() as AtomId
        } else {
            0
        };

        let cnf = self.term_to_cnf(
            term,
            false,
            &mut vec![],
            &mut next_var_id,
            &mut vec![],
            &mut context,
        )?;
        for mut literals in cnf.into_iter() {
            literals.sort();
            output.push(Clause::from_literals_unnormalized(literals, &context));
        }
        Ok(output)
    }

    /// Convert a term expression into a simple kernel term.
    ///
    /// This only succeeds for terms that are representable in simple-term form.
    pub fn clausify_term_to_simple_term(&mut self, term: &Term) -> Result<Term, String> {
        match self.try_simple_term_to_signed_term(term)? {
            Some((term, true)) => Ok(term),
            // `false` is represented as `not true` in signed-term form.
            Some((term, false)) if term == Term::new_true() => Ok(Term::new_false()),
            Some(_) | None => {
                // We may keep boolean formulas inline (e.g. `and(a, b)`).
                // Allow those to pass through claim reconstruction as raw terms.
                if !term.has_any_variable()
                    && self.term_type_for_normalization(term, &LocalContext::empty())
                        == Term::bool_type()
                {
                    return Ok(term.clone());
                }
                Err(format!(
                    "term '{}' cannot be represented as a simple term",
                    term
                ))
            }
        }
    }

    /// Synthesizes a literal from a CNF by creating a new synthetic boolean atom
    /// and adding clauses that define it to be equivalent to the CNF.
    /// This uses a Tseitin-style transformation: for CNF C and new atom s,
    /// we add clauses for s <-> C, which is (s -> C) and (C -> s).
    #[cfg(not(feature = "iite"))]
    fn synthesize_literal_from_cnf(
        &mut self,
        cnf: Cnf,
        stack: &Vec<TermBinding>,
        synth: &mut Vec<(ModuleId, AtomId)>,
        context: &LocalContext,
    ) -> Result<Literal, String> {
        // Create a new synthetic boolean atom with the appropriate function type
        // based on free variables in the stack.
        // Keep types as Terms to avoid round-trip conversion through AcornType,
        // which would lose the original type parameter names.
        let mut arg_type_terms = vec![];
        let mut args = vec![];
        let mut seen_vars = std::collections::HashSet::new();

        for binding in stack.iter() {
            // Use collect_vars with the context to get variable types
            for (var_id, closed_type) in binding.term().collect_vars(context) {
                if seen_vars.insert(var_id) {
                    let var_term = Term::new_variable(var_id);
                    args.push(var_term);
                    arg_type_terms.push(closed_type);
                }
            }
        }

        // Build the function type as a Term: arg1 -> arg2 -> ... -> Bool
        let mut type_term = Term::bool_type();
        for arg_type in arg_type_terms.iter().rev() {
            type_term = Term::pi(arg_type.clone(), type_term);
        }

        // Add the atom type to the symbol table and declare the synthetic atom
        let module_id = self.module_id();
        let atom_id = self
            .as_mut()?
            .declare_synthetic_atom_with_type_term(module_id, type_term)?;
        synth.push(atom_id);

        // Get the synthetic type from the symbol table
        let (m, i) = atom_id;
        let synthetic_type = self
            .kernel_context()
            .symbol_table
            .get_type(Symbol::Synthetic(m, i))
            .clone();

        let atom = Atom::Symbol(Symbol::Synthetic(m, i));
        let synth_term = Term::new(atom, args);
        let synth_lit = Literal::from_signed_term(synth_term.clone(), true);

        // Create defining CNF for: s <-> C
        // This is (s -> C) and (C -> s)
        // Which is (not s or C) and (not C or s)

        // For (not s or C): add not_s to each clause in C
        let not_s_implies_c = Cnf::from_literal(synth_lit.negate()).or(cnf.clone());

        // For (C -> s): which is (not C or s)
        let c_implies_s = cnf.negate().or(Cnf::from_literal(synth_lit.clone()));

        let defining_cnf = not_s_implies_c.and(c_implies_s);

        // Add the definition
        let type_vars = self.get_type_var_kinds();
        let num_type_vars = type_vars.len();
        let clauses = defining_cnf.into_clauses_with_pinned(context, num_type_vars);
        self.as_mut()?.define_synthetic_atoms(
            vec![atom_id],
            type_vars,
            vec![synthetic_type],
            clauses,
            None,
        )?;

        Ok(synth_lit)
    }

    /// Converts an ExtendedTerm to a simple Term.
    /// If the ExtendedTerm is an If expression, synthesizes a new atom for it.
    /// The local_context provides variable type information.
    fn extended_term_to_term(
        &mut self,
        ext_term: ExtendedTerm,
        local_context: &LocalContext,
        synth: &mut Vec<(ModuleId, AtomId)>,
    ) -> Result<Term, String> {
        #[cfg(feature = "iite")]
        let _ = synth;
        match ext_term {
            ExtendedTerm::Term(t) => Ok(t),
            ExtendedTerm::If(cond_lit, then_term, else_term) => {
                // Optimization: if both branches are the same, just return that term
                if then_term == else_term {
                    return Ok(then_term);
                }

                #[cfg(feature = "iite")]
                {
                    let result_type_term =
                        self.term_type_for_normalization(&then_term, local_context);
                    let cond_term = self.literal_to_bool_term(&cond_lit, local_context);
                    Ok(Term::atom(Atom::Symbol(Symbol::Ite)).apply(&[
                        result_type_term,
                        cond_term,
                        then_term,
                        else_term,
                    ]))
                }

                #[cfg(not(feature = "iite"))]
                {
                    // We need to synthesize a new atom that represents this if-expression
                    // The defining clauses will be:
                    // For atom s representing "if cond then then_term else else_term":
                    // (cond -> s = then_term) and (not cond -> s = else_term)
                    // Which is (not cond or s = then_term) and (cond or s = else_term)

                    // Determine the type of the result (should be same as then_term and else_term)
                    // Keep types as Terms to avoid round-trip conversion through AcornType,
                    // which would lose the original type parameter names.
                    let result_type_term =
                        self.term_type_for_normalization(&then_term, local_context);

                    // Create a new synthetic atom with the appropriate function type
                    // based on free variables in the if-expression
                    let mut arg_type_terms = vec![];
                    let mut args = vec![];
                    let mut seen_vars = std::collections::HashSet::new();

                    // In polymorphic mode, include type parameters as arguments.
                    // This matches how make_skolem_terms handles polymorphic synthetics.
                    if let Some(type_var_map) = self.type_var_map() {
                        let mut entries: Vec<_> = type_var_map.values().collect();
                        entries.sort_by_key(|(id, _)| *id);
                        for (var_id, var_type) in entries {
                            let var_term = Term::new_variable(*var_id);
                            args.push(var_term);
                            // Type variables have their kind (TypeSort or typeclass) as their type in the Pi
                            arg_type_terms.push(var_type.clone());
                            seen_vars.insert(*var_id);
                        }
                    }

                    // Collect free variables from the condition literal
                    // Skip type parameters (TypeSort or Typeclass) - they're not value arguments
                    for (var_id, closed_type) in cond_lit.left.collect_vars(local_context) {
                        if closed_type.as_ref().is_type_param_kind() {
                            continue;
                        }
                        if seen_vars.insert(var_id) {
                            let var_term = Term::new_variable(var_id);
                            args.push(var_term);
                            arg_type_terms.push(closed_type);
                        }
                    }
                    for (var_id, closed_type) in cond_lit.right.collect_vars(local_context) {
                        if closed_type.as_ref().is_type_param_kind() {
                            continue;
                        }
                        if seen_vars.insert(var_id) {
                            let var_term = Term::new_variable(var_id);
                            args.push(var_term);
                            arg_type_terms.push(closed_type);
                        }
                    }

                    // Collect free variables from the then branch
                    for (var_id, closed_type) in then_term.collect_vars(local_context) {
                        if closed_type.as_ref().is_type_param_kind() {
                            continue;
                        }
                        if seen_vars.insert(var_id) {
                            let var_term = Term::new_variable(var_id);
                            args.push(var_term);
                            arg_type_terms.push(closed_type);
                        }
                    }

                    // Collect free variables from the else branch
                    for (var_id, closed_type) in else_term.collect_vars(local_context) {
                        if closed_type.as_ref().is_type_param_kind() {
                            continue;
                        }
                        if seen_vars.insert(var_id) {
                            let var_term = Term::new_variable(var_id);
                            args.push(var_term);
                            arg_type_terms.push(closed_type);
                        }
                    }

                    // Convert FreeVariables in types to BoundVariables for the Pi structure.
                    // This is needed because symbol types use BoundVariable for parameters.
                    // Type parameter kinds (TypeSort/Typeclass) don't need conversion.
                    let num_type_params = self.type_var_map().map_or(0, |m| m.len()) as u16;
                    let mut non_type_param_index = 0u16;
                    let arg_type_terms: Vec<Term> = arg_type_terms
                        .into_iter()
                        .map(|t| {
                            if t.as_ref().is_type_param_kind() {
                                t // Type parameter kinds don't need conversion
                            } else {
                                let depth = non_type_param_index;
                                non_type_param_index += 1;
                                t.convert_free_to_bound_with_depth(num_type_params, depth)
                            }
                        })
                        .collect();
                    let non_type_param_args = arg_type_terms.len() - num_type_params as usize;
                    let result_type_term = result_type_term.convert_free_to_bound_with_depth(
                        num_type_params,
                        non_type_param_args as u16,
                    );

                    // Build the function type as a Term: arg1 -> arg2 -> ... -> result_type
                    let mut type_term = result_type_term.clone();
                    for arg_type in arg_type_terms.iter().rev() {
                        type_term = Term::pi(arg_type.clone(), type_term);
                    }

                    // Add the atom type to the symbol table and declare the synthetic atom
                    let module_id = self.module_id();
                    let atom_id = self
                        .as_mut()?
                        .declare_synthetic_atom_with_type_term(module_id, type_term)?;
                    synth.push(atom_id);

                    // Get the synthetic type from the symbol table
                    let (m, i) = atom_id;
                    let synthetic_type = self
                        .kernel_context()
                        .symbol_table
                        .get_type(Symbol::Synthetic(m, i))
                        .clone();

                    let atom = Atom::Symbol(Symbol::Synthetic(m, i));
                    let synth_term = Term::new(atom, args);

                    // Create defining CNF for the if-expression
                    // (not cond or synth_term = then_term) and (cond or synth_term = else_term)

                    // First clause: not cond or synth_term = then_term
                    let then_eq = Literal::new(true, synth_term.clone(), then_term.clone());
                    let first_clause =
                        Cnf::from_literal(cond_lit.negate()).or(Cnf::from_literal(then_eq));

                    // Second clause: cond or synth_term = else_term
                    let else_eq = Literal::new(true, synth_term.clone(), else_term.clone());
                    let second_clause =
                        Cnf::from_literal(cond_lit.clone()).or(Cnf::from_literal(else_eq));

                    let defining_cnf = first_clause.and(second_clause);

                    // Add the definition
                    let type_vars = self.get_type_var_kinds();
                    let num_type_vars = type_vars.len();
                    let clauses =
                        defining_cnf.into_clauses_with_pinned(local_context, num_type_vars);
                    self.as_mut()?.define_synthetic_atoms(
                        vec![atom_id],
                        type_vars,
                        vec![synthetic_type],
                        clauses,
                        None,
                    )?;

                    Ok(synth_term)
                }
            }
            ExtendedTerm::Lambda(_, t) => {
                Err(format!("cannot convert lambda {} to simple term", t))
            }
        }
    }

    #[cfg(feature = "iite")]
    fn literal_to_bool_term(&self, literal: &Literal, local_context: &LocalContext) -> Term {
        if literal.is_signed_term() {
            if literal.positive {
                literal.left.clone()
            } else {
                Term::not(literal.left.clone())
            }
        } else {
            let eq_type = self.term_type_for_normalization(&literal.left, local_context);
            let eq_term = Term::eq(eq_type, literal.left.clone(), literal.right.clone());
            if literal.positive {
                eq_term
            } else {
                Term::not(eq_term)
            }
        }
    }
}

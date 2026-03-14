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

// Represents a binding for a variable on the stack during normalization.
// Each binding corresponds to a variable in the output clause.
enum TermBinding {
    Bound,
    Free,
}

/// A Clausifier holds state for a single clausification operation.
/// It combines mutable kernel access with operation-scoped state like `type_var_map`.
struct Clausifier<'a> {
    kernel_context: &'a mut KernelContext,

    /// Type variable mapping for polymorphic normalization.
    /// Maps type parameter names to (variable id, kind).
    /// This is set for the duration of normalizing a single polymorphic fact/goal.
    type_var_map: Option<HashMap<String, (AtomId, Term)>>,
}

/// How a normalized top-level term should be lowered into initial clauses.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TermLoweringMode {
    /// Lower clause-shaped boolean structure at the top level.
    ClausifyShallowly,

    /// Preserve the normalized term as a single top-level literal clause.
    PreserveAsLiteral,
}

impl<'a> Clausifier<'a> {
    /// Create a new Clausifier with mutable access.
    fn new_mut(
        kernel_context: &'a mut KernelContext,
        type_var_map: Option<HashMap<String, (AtomId, Term)>>,
    ) -> Self {
        Clausifier {
            kernel_context,
            type_var_map,
        }
    }

    /// Lower a normalized term into initial clause form using the selected top-level policy.
    fn lower_normalized_term_to_clauses(
        &mut self,
        term: &Term,
        mode: TermLoweringMode,
    ) -> Result<Vec<Clause>, String> {
        #[cfg(feature = "nocnf")]
        {
            let _ = mode;
            self.clausify_term_to_single_clause(term)
        }
        #[cfg(not(feature = "nocnf"))]
        {
            match mode {
                TermLoweringMode::ClausifyShallowly => self.shallow_clausify_term(term),
                TermLoweringMode::PreserveAsLiteral => self.preserve_term_as_clause(term),
            }
        }
    }

    fn symbol_table(&self) -> &crate::kernel::symbol_table::SymbolTable {
        &self.kernel_context.symbol_table
    }

    fn kernel_context(&self) -> &KernelContext {
        self.kernel_context
    }

    /// Get the type variable map for polymorphic normalization.
    /// Maps type parameter names to (variable id, kind).
    /// In non-polymorphic mode, this always returns None.
    fn type_var_map(&self) -> Option<&HashMap<String, (AtomId, Term)>> {
        self.type_var_map.as_ref()
    }

    fn initial_clause_context(&self) -> (LocalContext, AtomId, usize) {
        let mut context = LocalContext::empty();
        let pinned = if let Some(type_var_map) = self.type_var_map() {
            let mut entries: Vec<_> = type_var_map.values().collect();
            entries.sort_by_key(|(id, _)| *id);
            for (_, var_type) in entries {
                context.push_type(var_type.clone());
            }
            type_var_map.len()
        } else {
            0
        };
        (context, pinned as AtomId, pinned)
    }

    /// Builds the sparse local context expected by exact clause roundtrips, keeping preserved
    /// type parameters in their original slots instead of repacking them densely.
    fn initial_exact_clause_context(&self) -> (LocalContext, AtomId) {
        let mut context = LocalContext::empty();
        if let Some(type_var_map) = self.type_var_map() {
            let mut entries: Vec<_> = type_var_map.values().collect();
            entries.sort_by_key(|(id, _)| *id);
            for (var_id, var_type) in entries {
                context.set_type(*var_id as usize, var_type.clone());
            }
        }
        (context, 0)
    }

    /// Reserves the next unused local id in a sparse context so newly opened binders do not
    /// overwrite preserved type-variable slots during exact clausification.
    fn allocate_next_open_local_slot(
        &self,
        context: &mut LocalContext,
        next_var_id: &mut AtomId,
        var_type: Term,
    ) -> AtomId {
        let mut var_id = *next_var_id as usize;
        while context.get_var_type(var_id).is_some() {
            var_id += 1;
        }
        context.set_type(var_id, var_type);
        *next_var_id = (var_id + 1) as AtomId;
        var_id as AtomId
    }

    fn open_leading_foralls_as_free_vars(
        &self,
        term: &Term,
        context: &mut LocalContext,
        next_var_id: &mut AtomId,
    ) -> Term {
        let mut body = term.clone();
        while let Some((binder_type, binder_body)) = body.as_ref().split_forall() {
            let var_id = *next_var_id;
            *next_var_id += 1;
            context.push_type(binder_type.to_owned());
            body = self.open_binder_body(&binder_body.to_owned(), &Term::new_variable(var_id));
        }
        body
    }

    /// Opens leading foralls without compacting local ids, which keeps quote/clausify/lower
    /// roundtrips stable when type parameters already occupy non-prefix slots.
    fn open_leading_foralls_preserving_local_slots(
        &self,
        term: &Term,
        context: &mut LocalContext,
        next_var_id: &mut AtomId,
    ) -> Term {
        let mut body = term.clone();
        while let Some((binder_type, binder_body)) = body.as_ref().split_forall() {
            let var_id =
                self.allocate_next_open_local_slot(context, next_var_id, binder_type.to_owned());
            body = self.open_binder_body(&binder_body.to_owned(), &Term::new_variable(var_id));
        }
        body
    }

    fn literal_from_shallow_term(
        &mut self,
        term: &Term,
        positive: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        context: &mut LocalContext,
    ) -> Result<Literal, String> {
        let cnf = self.term_to_cnf(term, !positive, stack, next_var_id, context)?;
        if let Some(literal) = cnf.to_literal() {
            return Ok(literal);
        }

        let term = self.term_to_inline_term(term, stack, next_var_id, context)?;
        Ok(Literal::from_signed_term(term, positive))
    }

    fn shallow_term_to_disjunctive_literals(
        &mut self,
        term: &Term,
        positive: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        context: &mut LocalContext,
    ) -> Result<Vec<Literal>, String> {
        if let Some(args) = self.split_symbol_application(term, Symbol::Not, 1) {
            return self.shallow_term_to_disjunctive_literals(
                &args[0],
                !positive,
                stack,
                next_var_id,
                context,
            );
        }

        if positive {
            if let Some(args) = self.split_symbol_application(term, Symbol::Or, 2) {
                let mut left = self.shallow_term_to_disjunctive_literals(
                    &args[0],
                    true,
                    stack,
                    next_var_id,
                    context,
                )?;
                left.extend(self.shallow_term_to_disjunctive_literals(
                    &args[1],
                    true,
                    stack,
                    next_var_id,
                    context,
                )?);
                return Ok(left);
            }
        } else if let Some(args) = self.split_symbol_application(term, Symbol::And, 2) {
            let mut left = self.shallow_term_to_disjunctive_literals(
                &args[0],
                false,
                stack,
                next_var_id,
                context,
            )?;
            left.extend(self.shallow_term_to_disjunctive_literals(
                &args[1],
                false,
                stack,
                next_var_id,
                context,
            )?);
            return Ok(left);
        }

        Ok(vec![self.literal_from_shallow_term(
            term,
            positive,
            stack,
            next_var_id,
            context,
        )?])
    }

    fn shallow_term_to_clauses(
        &mut self,
        term: &Term,
        positive: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        context: &mut LocalContext,
        pinned: usize,
    ) -> Result<Vec<Clause>, String> {
        if let Some(args) = self.split_symbol_application(term, Symbol::Not, 1) {
            return self.shallow_term_to_clauses(
                &args[0],
                !positive,
                stack,
                next_var_id,
                context,
                pinned,
            );
        }

        if positive {
            if let Some(args) = self.split_symbol_application(term, Symbol::And, 2) {
                let mut left = self.shallow_term_to_clauses(
                    &args[0],
                    true,
                    stack,
                    next_var_id,
                    context,
                    pinned,
                )?;
                left.extend(self.shallow_term_to_clauses(
                    &args[1],
                    true,
                    stack,
                    next_var_id,
                    context,
                    pinned,
                )?);
                return Ok(left);
            }
            if self.split_symbol_application(term, Symbol::Or, 2).is_some() {
                let literals = self.shallow_term_to_disjunctive_literals(
                    term,
                    true,
                    stack,
                    next_var_id,
                    context,
                )?;
                let clause = Clause::new_with_pinned_vars(literals, context, pinned);
                return if clause.is_tautology() {
                    Ok(vec![])
                } else {
                    Ok(vec![clause])
                };
            }
        } else if let Some(args) = self.split_symbol_application(term, Symbol::Or, 2) {
            let mut left =
                self.shallow_term_to_clauses(&args[0], false, stack, next_var_id, context, pinned)?;
            left.extend(self.shallow_term_to_clauses(
                &args[1],
                false,
                stack,
                next_var_id,
                context,
                pinned,
            )?);
            return Ok(left);
        } else if self
            .split_symbol_application(term, Symbol::And, 2)
            .is_some()
        {
            let literals = self.shallow_term_to_disjunctive_literals(
                term,
                false,
                stack,
                next_var_id,
                context,
            )?;
            let clause = Clause::new_with_pinned_vars(literals, context, pinned);
            return if clause.is_tautology() {
                Ok(vec![])
            } else {
                Ok(vec![clause])
            };
        }

        Ok(self
            .term_to_cnf(term, !positive, stack, next_var_id, context)?
            .into_clauses_with_pinned(context, pinned))
    }

    fn shallow_clausify_term(&mut self, term: &Term) -> Result<Vec<Clause>, String> {
        let (mut context, mut next_var_id, pinned) = self.initial_clause_context();
        let mut stack = vec![];
        let opened = self.open_leading_foralls_as_free_vars(term, &mut context, &mut next_var_id);
        self.shallow_term_to_clauses(
            &opened,
            true,
            &mut stack,
            &mut next_var_id,
            &mut context,
            pinned,
        )
    }

    /// Clausify a term into exactly one initial clause shape.
    ///
    /// Leading foralls are opened as free variables. At the top level we collect only
    /// disjunctive literals, so formulas like `a or b` or `not (a and b)` become one
    /// clause, while formulas that are not clause-shaped stay inline as one signed literal.
    #[cfg_attr(not(feature = "nocnf"), allow(dead_code))]
    fn clausify_term_to_single_clause(&mut self, term: &Term) -> Result<Vec<Clause>, String> {
        let (mut context, mut next_var_id, pinned) = self.initial_clause_context();
        let mut stack = vec![];
        let opened = self.open_leading_foralls_as_free_vars(term, &mut context, &mut next_var_id);
        if let Some(args) = self.split_symbol_application(&opened, Symbol::Eq, 3) {
            if self.split_match_eliminator_application(&args[1]).is_some()
                || self.split_match_eliminator_application(&args[2]).is_some()
            {
                // Match eliminator equalities still rely on the old equality-to-CNF lowering
                // to produce constructor-guarded case clauses.
                return self.shallow_clausify_term(term);
            }
        }
        let literals = self.shallow_term_to_disjunctive_literals(
            &opened,
            true,
            &mut stack,
            &mut next_var_id,
            &mut context,
        )?;
        let clause = Clause::new_with_pinned_vars(literals, &context, pinned);
        if clause.is_tautology() {
            Ok(vec![])
        } else {
            Ok(vec![clause])
        }
    }

    fn preserve_term_as_clause(&mut self, term: &Term) -> Result<Vec<Clause>, String> {
        let (mut context, mut next_var_id, pinned) = self.initial_clause_context();
        let mut stack = vec![];
        let literal =
            self.literal_from_shallow_term(term, true, &mut stack, &mut next_var_id, &mut context)?;
        let clause = Clause::new_with_pinned_vars(vec![literal], &context, pinned);
        let clauses = if clause.is_tautology() {
            vec![]
        } else {
            vec![clause]
        };
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
    /// `TermBinding::Bound` tracks instantiated binder arguments.
    fn term_to_cnf(
        &mut self,
        term: &Term,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
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
                        context,
                    )
                } else {
                    // Keep negated universals inline so later boolean reductions can
                    // open them via exists/choose without introducing witnesses here.
                    let literal = Literal::from_signed_term(term.clone(), false);
                    Ok(Cnf::from_literal(literal))
                }
            }
            crate::kernel::term::Decomposition::Exists(_, _) => {
                if !negate {
                    // Keep positive existential formulas inline as signed terms.
                    // This avoids introducing choose-style witnesses during clausification.
                    let literal = Literal::from_signed_term(term.clone(), true);
                    Ok(Cnf::from_literal(literal))
                } else {
                    // Preserve negated existentials inline so they can meet positive
                    // existential conclusions in the indexed resolution path.
                    let literal = Literal::from_signed_term(term.clone(), false);
                    Ok(Cnf::from_literal(literal))
                }
            }
            _ => {
                // Builtin logical atoms are recognized by head symbol + arity.
                if let Some(args) = self.split_symbol_application(term, Symbol::Not, 1) {
                    return self.term_to_cnf(&args[0], !negate, stack, next_var_id, context);
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
                        let inline_term =
                            self.term_to_inline_term(term, stack, next_var_id, context)?;
                        let literal = Literal::from_signed_term(inline_term, !negate);
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
                        context,
                    );
                }
                if let Some(args) = self.split_symbol_application(term, Symbol::Ite, 4) {
                    let cond_cnf =
                        self.term_to_cnf(&args[1], false, stack, next_var_id, context)?;
                    let Some(cond_lit) = cond_cnf.to_literal() else {
                        return Err("term 'ite' condition is too complicated".to_string());
                    };
                    let then_cnf =
                        self.term_to_cnf(&args[2], negate, stack, next_var_id, context)?;
                    let else_cnf =
                        self.term_to_cnf(&args[3], negate, stack, next_var_id, context)?;
                    return Ok(Cnf::cnf_if(cond_lit, then_cnf, else_cnf));
                }

                if let Some((function, args)) = term.as_ref().split_application_multi() {
                    match function.as_ref().decompose() {
                        crate::kernel::term::Decomposition::Lambda(_, _)
                        | crate::kernel::term::Decomposition::ForAll(_, _)
                        | crate::kernel::term::Decomposition::Exists(_, _) => {
                            let (applied, consumed) =
                                self.instantiate_binder_prefix(&function.to_owned(), &args);
                            for _ in args.iter().take(consumed) {
                                stack.push(TermBinding::Bound);
                            }
                            let answer =
                                self.term_to_cnf(&applied, negate, stack, next_var_id, context);
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
                let inline_term = self.term_to_inline_term(term, stack, next_var_id, context)?;
                let literal = Literal::from_signed_term(inline_term, !negate);
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
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        let var_id = *next_var_id;
        *next_var_id += 1;
        context.push_type(binder_type.clone());
        let var = Term::new_variable(var_id);
        stack.push(TermBinding::Free);
        let opened_body = self.open_binder_body(body, &var);
        let result = self.term_to_cnf(&opened_body, negate, stack, next_var_id, context)?;
        stack.pop();
        Ok(result)
    }

    fn term_and_to_cnf(
        &mut self,
        left: &Term,
        right: &Term,
        negate_left: bool,
        negate_right: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        let left = self.term_to_cnf(left, negate_left, stack, next_var_id, context)?;
        let right = self.term_to_cnf(right, negate_right, stack, next_var_id, context)?;
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
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        let left = self.term_to_cnf(left, negate_left, stack, next_var_id, context)?;
        let right = self.term_to_cnf(right, negate_right, stack, next_var_id, context)?;
        Ok(left.or(right))
    }

    fn try_inline_term_to_term(&self, term: &Term) -> Result<Option<Term>, String> {
        match self.try_inline_term_to_signed_term(term)? {
            Some((t, true)) => Ok(Some(t)),
            Some((_t, false)) => Ok(None),
            None => Ok(None),
        }
    }

    fn try_inline_term_to_signed_term(&self, term: &Term) -> Result<Option<(Term, bool)>, String> {
        if let Some(args) = self.split_symbol_application(term, Symbol::Not, 1) {
            return match self.try_inline_term_to_signed_term(&args[0])? {
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
                    let func_term = match self.try_inline_term_to_term(&function)? {
                        Some(t) => t,
                        None => return Ok(None),
                    };
                    let head = *func_term.get_head_atom();
                    let mut args = func_term.args().to_vec();
                    for arg in arg_terms {
                        let arg_term = match self.try_inline_term_to_term(&arg)? {
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
        context: &mut LocalContext,
    ) -> Result<Cnf, String> {
        match function.as_ref().decompose() {
            crate::kernel::term::Decomposition::Lambda(_, _)
            | crate::kernel::term::Decomposition::ForAll(_, _)
            | crate::kernel::term::Decomposition::Exists(_, _) => {
                let mut arg_terms = Vec::with_capacity(args.len());
                for arg in args {
                    arg_terms.push(self.extended_term_to_term(arg, context)?);
                }
                let (applied, consumed) = self.instantiate_binder_prefix(function, &arg_terms);
                for _ in arg_terms.iter().take(consumed) {
                    stack.push(TermBinding::Bound);
                }
                let answer = self.term_to_cnf(&applied, negate, stack, next_var_id, context);
                stack.truncate(stack.len().saturating_sub(consumed));
                return answer;
            }
            _ => {}
        }

        let extended =
            self.apply_term_to_extended_term(function, args, stack, next_var_id, context)?;
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
    /// fresh variables to both sides, then reducing to equality on results.
    /// Negated higher-order equalities stay as direct literals.
    fn term_eq_to_cnf(
        &mut self,
        left: &Term,
        right: &Term,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
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
                    stack.push(TermBinding::Free);
                    case_value = self.open_binder_body(&body.to_owned(), &var);
                }

                let pattern = Term::new(Atom::Symbol(*constructor_symbol), constructor_args);
                let condition =
                    self.term_eq_to_cnf(&scrutinee, &pattern, false, stack, next_var_id, context)?;
                let conclusion =
                    self.term_eq_to_cnf(left, &case_value, negate, stack, next_var_id, context)?;
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
                    stack.push(TermBinding::Free);
                    case_value = self.open_binder_body(&body.to_owned(), &var);
                }

                let pattern = Term::new(Atom::Symbol(*constructor_symbol), constructor_args);
                let condition =
                    self.term_eq_to_cnf(&scrutinee, &pattern, false, stack, next_var_id, context)?;
                let conclusion =
                    self.term_eq_to_cnf(right, &case_value, negate, stack, next_var_id, context)?;
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
            if negate {
                let left = self.term_to_extended_term(left, stack, next_var_id, context)?;
                let right = self.term_to_extended_term(right, stack, next_var_id, context)?;
                let left = self.extended_term_to_term(left, context)?;
                let right = self.extended_term_to_term(right, context)?;
                return Ok(Cnf::from_literal(Literal::new(false, left, right)));
            }

            if result_type == Term::bool_type() {
                // f = g for Bool-valued functions:
                // introduce fresh universally-quantified arguments.
                let mut args = vec![];
                for arg_type_term in &fn_arg_types {
                    let var_id = *next_var_id;
                    *next_var_id += 1;
                    context.push_type(arg_type_term.clone());
                    args.push(ExtendedTerm::Term(Term::new_variable(var_id)));
                }
                let left_pos =
                    self.apply_term_to_cnf(left, args.clone(), false, stack, next_var_id, context)?;
                let left_neg =
                    self.apply_term_to_cnf(left, args.clone(), true, stack, next_var_id, context)?;
                let right_pos = self.apply_term_to_cnf(
                    right,
                    args.clone(),
                    false,
                    stack,
                    next_var_id,
                    context,
                )?;
                let right_neg =
                    self.apply_term_to_cnf(right, args, true, stack, next_var_id, context)?;

                let result = if let Some((left_term, left_sign)) = left_pos.match_negated(&left_neg)
                {
                    if let Some((right_term, right_sign)) = right_pos.match_negated(&right_neg) {
                        let positive = left_sign == right_sign;
                        let literal = Literal::new(positive, left_term.clone(), right_term.clone());
                        Cnf::from_literal(literal)
                    } else {
                        let l_imp_r = left_neg.or(right_pos);
                        let r_imp_l = left_pos.or(right_neg);
                        l_imp_r.and(r_imp_l)
                    }
                } else {
                    let l_imp_r = left_neg.or(right_pos);
                    let r_imp_l = left_pos.or(right_neg);
                    l_imp_r.and(r_imp_l)
                };
                return Ok(result);
            }

            let left = self.term_to_extended_term(left, stack, next_var_id, context)?;
            let right = self.term_to_extended_term(right, stack, next_var_id, context)?;

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
            if let Some((left_term, left_sign)) = self.try_inline_term_to_signed_term(left)? {
                if let Some((right_term, right_sign)) =
                    self.try_inline_term_to_signed_term(right)?
                {
                    let positive = (left_sign == right_sign) ^ negate;
                    let literal = Literal::new(positive, left_term, right_term);
                    return Ok(Cnf::from_literal(literal));
                }
            }

            if negate {
                let some =
                    self.term_or_to_cnf(left, right, true, true, stack, next_var_id, context)?;
                let not_both =
                    self.term_or_to_cnf(left, right, false, false, stack, next_var_id, context)?;
                return Ok(some.and(not_both));
            }

            let l_imp_r =
                self.term_or_to_cnf(left, right, true, false, stack, next_var_id, context)?;
            let r_imp_l =
                self.term_or_to_cnf(left, right, false, true, stack, next_var_id, context)?;
            return Ok(l_imp_r.and(r_imp_l));
        }

        let left = self.term_to_extended_term(left, stack, next_var_id, context)?;
        let right = self.term_to_extended_term(right, stack, next_var_id, context)?;
        left.eq_to_cnf(right, negate)
    }

    fn arg_term_to_extended(
        &mut self,
        term: &Term,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        context: &mut LocalContext,
    ) -> Result<ExtendedTerm, String> {
        if term.as_ref().is_lambda() {
            return self.term_to_extended_term(term, stack, next_var_id, context);
        }

        // Keep complex boolean arguments inline instead of forcing atomization.
        let term_type = self.term_type_for_normalization(term, context);
        if term_type == Term::bool_type() && self.try_inline_term_to_term(term)?.is_none() {
            // Keep complex booleans inline as terms.
            return Ok(ExtendedTerm::Term(term.clone()));
        }

        self.term_to_extended_term(term, stack, next_var_id, context)
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
        context: &mut LocalContext,
    ) -> Result<ExtendedTerm, String> {
        if function.as_ref().is_lambda() {
            let func_ext = self.term_to_extended_term(function, stack, next_var_id, context)?;
            let mut arg_terms = vec![];
            for arg in args {
                arg_terms.push(self.extended_term_to_term(arg, context)?);
            }
            return Ok(func_ext.apply(&arg_terms));
        }

        let mut cond: Option<Literal> = None;
        let mut spine1 = vec![];
        let mut spine2 = vec![];

        match self.term_to_extended_term(function, stack, next_var_id, context)? {
            ExtendedTerm::Term(t) => {
                spine1.push(t);
            }
            ExtendedTerm::If(sub_cond, sub_then, sub_else) => {
                cond = Some(sub_cond);
                spine1.push(sub_then);
                spine2.push(sub_else);
            }
            lambda @ ExtendedTerm::Lambda(_, _) => {
                let lambda_term = self.extended_term_to_term(lambda, context)?;
                spine1.push(lambda_term);
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
                lambda @ ExtendedTerm::Lambda(_, _) => {
                    let lambda_term = self.extended_term_to_term(lambda, context)?;
                    if !spine2.is_empty() {
                        spine2.push(lambda_term.clone());
                    }
                    spine1.push(lambda_term);
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

    /// Convert a term into `ExtendedTerm`, preserving conditionals and lambdas.
    ///
    /// `ExtendedTerm::If` is used as an intermediate form to avoid losing branching
    /// structure before we rebuild a kernel term.
    fn term_to_extended_term(
        &mut self,
        term: &Term,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        context: &mut LocalContext,
    ) -> Result<ExtendedTerm, String> {
        if let Some(args) = self.split_symbol_application(term, Symbol::Ite, 4) {
            let then_ext = self.term_to_extended_term(&args[2], stack, next_var_id, context)?;
            let then_branch = self.extended_term_to_term(then_ext, context)?;
            let else_ext = self.term_to_extended_term(&args[3], stack, next_var_id, context)?;
            let else_branch = self.extended_term_to_term(else_ext, context)?;
            let result_type = self.term_type_for_normalization(&then_branch, context);
            let ite_term = Term::atom(Atom::Symbol(Symbol::Ite)).apply(&[
                result_type,
                args[1].clone(),
                then_branch,
                else_branch,
            ]);
            return Ok(ExtendedTerm::Term(ite_term));
        }

        if let Some((function, arg_terms)) = term.as_ref().split_application_multi() {
            let mut arg_exts = vec![];
            for arg in arg_terms {
                arg_exts.push(self.arg_term_to_extended(&arg, stack, next_var_id, context)?);
            }
            return self.apply_term_to_extended_term(
                &function,
                arg_exts,
                stack,
                next_var_id,
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
                    stack.push(TermBinding::Free);
                    current = self.open_binder_body(&body.to_owned(), &var);
                }

                let body_ext = self.term_to_extended_term(&current, stack, next_var_id, context)?;
                let body_term = self.extended_term_to_term(body_ext, context)?;

                for _ in 0..args.len() {
                    stack.pop();
                }
                Ok(ExtendedTerm::Lambda(args, body_term))
            }
            crate::kernel::term::Decomposition::ForAll(_, _)
            | crate::kernel::term::Decomposition::Exists(_, _) => {
                // Quantifiers can legitimately appear as boolean subterms inside
                // higher-order arguments (for example choose predicates).
                // Keep them inline as terms in these positions.
                Ok(ExtendedTerm::Term(term.clone()))
            }
            _ => {
                if term == &Term::new_true() {
                    return Ok(ExtendedTerm::Term(Term::new_true()));
                }
                if term == &Term::new_false() {
                    return Ok(ExtendedTerm::Term(Term::new_false()));
                }

                let term_type = self.term_type_for_normalization(term, context);
                if term_type == Term::bool_type() {
                    if let Some(inline_term) = self.try_inline_term_to_term(term)? {
                        return Ok(ExtendedTerm::Term(inline_term));
                    }
                    // Keep complex booleans inline as terms.
                    Ok(ExtendedTerm::Term(term.clone()))
                } else {
                    Ok(ExtendedTerm::Term(term.clone()))
                }
            }
        }
    }

    fn term_to_inline_term(
        &mut self,
        term: &Term,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        context: &mut LocalContext,
    ) -> Result<Term, String> {
        if let Some(inline_term) = self.try_inline_term_to_term(term)? {
            return Ok(inline_term);
        }
        let ext = self.term_to_extended_term(term, stack, next_var_id, context)?;
        self.extended_term_to_term(ext, context)
    }

    /// Lower a normalized clause-shaped term into pre-normalized clauses.
    ///
    /// This keeps the full clause structure intact: literals are sorted and the clause context
    /// is built, but tautologies are preserved and variable IDs are not yet canonicalized.
    fn term_to_pre_normalized_clauses(&mut self, term: &Term) -> Result<Vec<Clause>, String> {
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

        let cnf = self.term_to_cnf(term, false, &mut vec![], &mut next_var_id, &mut context)?;
        for mut literals in cnf.into_iter() {
            literals.sort();
            output.push(Clause::from_literals_unnormalized(literals, &context));
        }
        Ok(output)
    }

    /// Lower a normalized clause-shaped term into exactly one normalized clause.
    fn lower_normalized_term_to_clause(&mut self, term: &Term) -> Result<Clause, String> {
        let (mut context, mut next_var_id) = self.initial_exact_clause_context();
        let opened =
            self.open_leading_foralls_preserving_local_slots(term, &mut context, &mut next_var_id);
        let literals = self.exact_clause_literals_from_term(&opened)?;
        Ok(Clause::from_literals_unnormalized(literals, &context).normalized_preserving_locals())
    }

    /// Interpret a normalized term as the exact disjunction shape used by quoted clauses.
    fn exact_clause_literals_from_term(&self, term: &Term) -> Result<Vec<Literal>, String> {
        if term == &Term::new_false() {
            return Ok(vec![]);
        }
        if let Some(args) = self.split_symbol_application(term, Symbol::Or, 2) {
            let mut left = self.exact_clause_literals_from_term(&args[0])?;
            left.extend(self.exact_clause_literals_from_term(&args[1])?);
            return Ok(left);
        }
        Ok(vec![self.exact_clause_literal_from_term(term)])
    }

    /// Interpret one quoted-clause disjunct as exactly one literal.
    fn exact_clause_literal_from_term(&self, term: &Term) -> Literal {
        if let Some(args) = self.split_symbol_application(term, Symbol::Not, 1) {
            if let Some(eq_args) = self.split_symbol_application(&args[0], Symbol::Eq, 3) {
                return Literal::not_equals(eq_args[1].clone(), eq_args[2].clone());
            }
            return Literal::negative(args[0].clone());
        }
        if let Some(args) = self.split_symbol_application(term, Symbol::Eq, 3) {
            return Literal::equals(args[1].clone(), args[2].clone());
        }
        Literal::positive(term.clone())
    }

    /// Convert a term expression into the checker's inline single-term form.
    ///
    /// This only succeeds for terms that are representable without introducing clause structure.
    fn term_to_checker_inline_term(&mut self, term: &Term) -> Result<Term, String> {
        match self.try_inline_term_to_signed_term(term)? {
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
                    "term cannot be represented as a checker inline term (has_free_var={}, has_bound_var={})",
                    term.has_free_variable(),
                    term.has_bound_variable()
                ))
            }
        }
    }

    /// Convert a claim argument term for `claim_with_args` parsing.
    ///
    /// Prefer inline checker-term encoding when available (to preserve existing certificate shape),
    /// but allow richer closed terms (for example lambdas) so cert parsing can round-trip
    /// generated witnesses.
    fn term_to_claim_arg_shape(&mut self, term: &Term) -> Result<Term, String> {
        match self.term_to_checker_inline_term(term) {
            Ok(inline_term) => Ok(inline_term),
            Err(_) if !term.has_free_variable() => Ok(term.clone()),
            Err(e) => Err(e),
        }
    }

    /// Converts an ExtendedTerm to a simple Term.
    /// The local_context provides variable type information.
    fn extended_term_to_term(
        &mut self,
        ext_term: ExtendedTerm,
        local_context: &LocalContext,
    ) -> Result<Term, String> {
        match ext_term {
            ExtendedTerm::Term(t) => Ok(t),
            ExtendedTerm::If(cond_lit, then_term, else_term) => {
                // Optimization: if both branches are the same, just return that term
                if then_term == else_term {
                    return Ok(then_term);
                }

                let result_type_term = self.term_type_for_normalization(&then_term, local_context);
                let cond_term = self.literal_to_bool_term(&cond_lit, local_context);
                Ok(Term::atom(Atom::Symbol(Symbol::Ite)).apply(&[
                    result_type_term,
                    cond_term,
                    then_term,
                    else_term,
                ]))
            }
            ExtendedTerm::Lambda(args, body) => {
                let mut out = body;
                // Rebuild de Bruijn binders from the lambda's free-variable form.
                for (depth, (var_id, _)) in args.iter().rev().enumerate() {
                    out = self.abstract_free_var_as_bound_at_depth(&out, *var_id, depth as u16);
                }
                for (_, input_type) in args.into_iter().rev() {
                    out = Term::lambda(input_type, out);
                }
                // Ensure the reconstructed lambda is typeable under this context.
                let _ = self.term_type_for_normalization(&out, local_context);
                Ok(out)
            }
        }
    }

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

impl KernelContext {
    /// Kernel-owned entry point for lowering an already-normalized top-level term to clauses.
    pub fn lower_normalized_term_to_clauses(
        &mut self,
        term: &Term,
        type_var_map: Option<HashMap<String, (AtomId, Term)>>,
        mode: TermLoweringMode,
    ) -> Result<Vec<Clause>, String> {
        let mut view = Clausifier::new_mut(self, type_var_map);
        view.lower_normalized_term_to_clauses(term, mode)
    }

    /// Kernel-owned entry point for converting a term to the checker's pre-normalized clause form.
    pub fn term_to_checker_clauses(
        &mut self,
        term: &Term,
        type_var_map: Option<HashMap<String, (AtomId, Term)>>,
    ) -> Result<Vec<Clause>, String> {
        let mut view = Clausifier::new_mut(self, type_var_map);
        view.term_to_pre_normalized_clauses(term)
    }

    /// Kernel-owned entry point for lowering an already-normalized clause-shaped term to
    /// exactly one normalized clause.
    pub fn lower_normalized_term_to_clause(
        &mut self,
        term: &Term,
        type_var_map: Option<HashMap<String, (AtomId, Term)>>,
    ) -> Result<Clause, String> {
        let mut view = Clausifier::new_mut(self, type_var_map);
        view.lower_normalized_term_to_clause(term)
    }

    /// Kernel-owned entry point for converting a term to the checker's single-term inline form.
    pub fn term_to_checker_term(
        &mut self,
        term: &Term,
        type_var_map: Option<HashMap<String, (AtomId, Term)>>,
    ) -> Result<Term, String> {
        let mut view = Clausifier::new_mut(self, type_var_map);
        view.term_to_checker_inline_term(term)
    }

    /// Kernel-owned entry point for converting a term to claim-argument form.
    pub fn term_to_claim_arg(&mut self, term: &Term) -> Result<Term, String> {
        let mut view = Clausifier::new_mut(self, None);
        view.term_to_claim_arg_shape(term)
    }
}

#[cfg(test)]
mod tests {
    use super::{Clausifier, TermLoweringMode};
    use crate::kernel::atom::Atom;
    use crate::kernel::clause::Clause;
    use crate::kernel::kernel_context::KernelContext;
    use crate::kernel::literal::Literal;
    use crate::kernel::local_context::LocalContext;
    use crate::kernel::symbol_table::NewConstantType;
    use crate::kernel::term::{Decomposition, Term};

    #[test]
    fn test_negated_forall_clausification_stays_inline_without_opening_witness() {
        let mut kernel_context = KernelContext::new();
        kernel_context.parse_constant("g0", "Bool -> Bool");

        let forall_term = Term::forall(
            Term::bool_type(),
            kernel_context
                .parse_term("g0")
                .apply(&[Term::atom(Atom::BoundVariable(0))]),
        );
        let clauses = {
            let mut view = Clausifier::new_mut(&mut kernel_context, None);
            view.term_to_pre_normalized_clauses(&Term::not(forall_term))
                .expect("negated forall should clausify")
        };

        assert_eq!(
            clauses.len(),
            1,
            "expected a single clause for negated forall"
        );
        assert_eq!(clauses[0].literals.len(), 1, "expected a single literal");
        assert!(
            !clauses[0].literals[0].positive,
            "expected negated forall to remain a negative literal: {:?}",
            clauses[0].literals[0]
        );
        assert!(
            matches!(
                clauses[0].literals[0].left.as_ref().decompose(),
                Decomposition::ForAll(_, _)
            ),
            "expected literal to keep the forall term inline: {:?}",
            clauses[0].literals[0]
        );
    }

    #[test]
    fn test_lower_normalized_term_to_clauses_respects_mode() {
        let mut kernel_context = KernelContext::new();
        kernel_context.parse_constants(&["c0", "c1"], "Bool");
        let term = Term::or(
            kernel_context.parse_term("c0"),
            kernel_context.parse_term("c1"),
        );

        let preserved = kernel_context
            .lower_normalized_term_to_clauses(&term, None, TermLoweringMode::PreserveAsLiteral)
            .expect("preserve-mode lowering should succeed");
        assert_eq!(preserved.len(), 1);
        if cfg!(feature = "nocnf") {
            assert_eq!(preserved[0].literals.len(), 2);
        } else {
            assert_eq!(preserved[0].literals.len(), 1);
        }

        let clausified = kernel_context
            .lower_normalized_term_to_clauses(&term, None, TermLoweringMode::ClausifyShallowly)
            .expect("shallow clausification should succeed");
        assert_eq!(clausified.len(), 1);
        assert_eq!(clausified[0].literals.len(), 2);
    }

    #[test]
    fn test_lower_normalized_term_to_clause_preserves_boolean_formula_literal_shape() {
        let mut kernel_context = KernelContext::new();
        kernel_context.parse_constants(&["c0", "c1", "c2"], "Bool");
        let term = Term::or(
            Term::and(
                kernel_context.parse_term("c0"),
                kernel_context.parse_term("c1"),
            ),
            kernel_context.parse_term("c2"),
        );

        let clause = kernel_context
            .lower_normalized_term_to_clause(&term, None)
            .expect("exact clause lowering should succeed");

        let expected = Clause::new(
            vec![
                Literal::positive(Term::and(
                    kernel_context.parse_term("c0"),
                    kernel_context.parse_term("c1"),
                )),
                Literal::positive(kernel_context.parse_term("c2")),
            ],
            &LocalContext::empty(),
        );
        assert_eq!(clause, expected);
    }

    #[test]
    fn test_lower_normalized_term_to_clause_preserves_if_literal_shape() {
        let mut kernel_context = KernelContext::new();
        kernel_context.parse_constants(&["c0", "c1", "c2", "c3"], "Bool");
        let ite = kernel_context.parse_term("ite(Bool, c0, c1, c2)");
        let term = Term::or(ite.clone(), kernel_context.parse_term("c3"));

        let clause = kernel_context
            .lower_normalized_term_to_clause(&term, None)
            .expect("exact clause lowering should succeed");

        let expected = Clause::new(
            vec![
                Literal::positive(ite),
                Literal::positive(kernel_context.parse_term("c3")),
            ],
            &LocalContext::empty(),
        );
        assert_eq!(clause, expected);
    }

    #[test]
    fn test_lower_normalized_term_to_clause_preserves_existing_value_local_slots() {
        let mut kernel_context = KernelContext::new();
        let local_context = LocalContext::from_types(vec![
            Term::bool_type(),
            Term::bool_type(),
            Term::bool_type(),
        ]);
        let x1 = Term::new_variable(1);
        let x2 = Term::new_variable(2);
        let clause = Clause::from_literals_unnormalized(
            vec![
                Literal::negative(Term::and(
                    x2.clone(),
                    Term::not(Term::eq(Term::bool_type(), x1.clone(), x2.clone())),
                )),
                Literal::positive(x1.clone()),
            ],
            &local_context,
        )
        .normalized_preserving_locals();

        let quoted = kernel_context.quote_clause(&clause, None, None, false);
        let lowered = kernel_context
            .lower_clause(&quoted, NewConstantType::Local, None)
            .expect("exact clause lowering should preserve local slot order");

        assert_eq!(lowered, clause);
    }

    #[test]
    fn test_lower_normalized_term_to_clause_preserves_nested_equality_order() {
        let mut kernel_context = KernelContext::new();
        let local_context = LocalContext::from_types(vec![
            Term::bool_type(),
            Term::bool_type(),
            Term::bool_type(),
        ]);
        let x1 = Term::new_variable(1);
        let x2 = Term::new_variable(2);
        let clause = Clause::from_literals_unnormalized(
            vec![
                Literal::negative(Term::and(
                    x1.clone(),
                    Term::not(Term::eq(Term::bool_type(), x2.clone(), x1.clone())),
                )),
                Literal::positive(x2.clone()),
            ],
            &local_context,
        )
        .normalized_preserving_locals();

        let quoted = kernel_context.quote_clause(&clause, None, None, false);
        let lowered = kernel_context
            .lower_clause(&quoted, NewConstantType::Local, None)
            .expect("exact clause lowering should preserve nested equality order");

        assert_eq!(lowered, clause);
    }
}

use std::collections::HashMap;

use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::clause::Clause;
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

type ClauseLiterals = Vec<Vec<Literal>>;

fn clauses_true() -> ClauseLiterals {
    vec![]
}

fn clauses_false() -> ClauseLiterals {
    vec![vec![]]
}

fn clauses_from_literal(literal: Literal) -> ClauseLiterals {
    if literal.is_true_value() {
        clauses_true()
    } else if literal.is_false_value() {
        clauses_false()
    } else {
        vec![vec![literal]]
    }
}

fn clauses_and(mut left: ClauseLiterals, right: ClauseLiterals) -> ClauseLiterals {
    left.extend(right);
    left
}

fn clauses_and_all(formulas: impl Iterator<Item = ClauseLiterals>) -> ClauseLiterals {
    let mut result = clauses_true();
    for formula in formulas {
        result = clauses_and(result, formula);
    }
    result
}

fn clauses_or(left: ClauseLiterals, right: ClauseLiterals) -> ClauseLiterals {
    let mut result = vec![];
    for left_clause in &left {
        for right_clause in &right {
            let mut combined = left_clause.clone();
            combined.extend(right_clause.clone());
            result.push(combined);
        }
    }
    result
}

fn clauses_or_all(formulas: impl Iterator<Item = ClauseLiterals>) -> ClauseLiterals {
    let mut result = clauses_false();
    for formula in formulas {
        result = clauses_or(result, formula);
    }
    result
}

fn negate_clauses(clauses: &ClauseLiterals) -> ClauseLiterals {
    clauses_or_all(
        clauses.iter().map(|clause| {
            clauses_and_all(clause.iter().map(|lit| clauses_from_literal(lit.negate())))
        }),
    )
}

fn clauses_to_literal(clauses: ClauseLiterals) -> Option<Literal> {
    if clauses.is_empty() {
        Some(Literal::true_value())
    } else if clauses.len() == 1 && clauses[0].is_empty() {
        Some(Literal::false_value())
    } else if clauses.len() == 1 && clauses[0].len() == 1 {
        Some(
            clauses
                .into_iter()
                .next()
                .unwrap()
                .into_iter()
                .next()
                .unwrap(),
        )
    } else {
        None
    }
}

fn clauses_as_signed_term(clauses: &ClauseLiterals) -> Option<(&Term, bool)> {
    if clauses.len() != 1 || clauses[0].len() != 1 {
        return None;
    }
    let literal = &clauses[0][0];
    if literal.is_signed_term() {
        Some((&literal.left, literal.positive))
    } else {
        None
    }
}

fn clauses_match_negated<'a>(
    clauses: &'a ClauseLiterals,
    other: &'a ClauseLiterals,
) -> Option<(&'a Term, bool)> {
    let (term, sign) = clauses_as_signed_term(clauses)?;
    let (other_term, other_sign) = clauses_as_signed_term(other)?;
    if term == other_term && sign != other_sign {
        Some((term, sign))
    } else {
        None
    }
}

fn clauses_into_clauses_with_pinned(
    clauses: ClauseLiterals,
    local_context: &LocalContext,
    pinned: usize,
) -> Vec<Clause> {
    clauses
        .into_iter()
        .filter(|literals| !literals.iter().any(|l| l.is_tautology()))
        .map(|literals| Clause::new_with_pinned_vars(literals, local_context, pinned))
        .collect()
}

fn clause_set_if(
    condition: Literal,
    then_clauses: ClauseLiterals,
    else_clauses: ClauseLiterals,
) -> ClauseLiterals {
    let not_condition = clauses_from_literal(condition.negate());
    let condition = clauses_from_literal(condition);
    let then_implication = clauses_or(not_condition, then_clauses);
    let else_implication = clauses_or(condition, else_clauses);
    clauses_and(then_implication, else_implication)
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

    /// Lower a normalized term into initial clause form using the default single-clause policy.
    fn lower_normalized_term_to_clauses(&mut self, term: &Term) -> Result<Vec<Clause>, String> {
        self.clausify_term_to_single_clause(term)
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
        if let Some(literal) =
            self.try_term_to_single_literal(term, positive, stack, next_var_id, context)?
        {
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
            .term_to_clause_set(term, !positive, stack, next_var_id, context)
            .map(|clauses| clauses_into_clauses_with_pinned(clauses, context, pinned))?)
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
    fn clausify_term_to_single_clause(&mut self, term: &Term) -> Result<Vec<Clause>, String> {
        let (mut context, mut next_var_id, pinned) = self.initial_clause_context();
        let mut stack = vec![];
        let opened = self.open_leading_foralls_as_free_vars(term, &mut context, &mut next_var_id);
        if let Some(args) = self.split_symbol_application(&opened, Symbol::Eq, 3) {
            if self.split_match_eliminator_application(&args[1]).is_some()
                || self.split_match_eliminator_application(&args[2]).is_some()
            {
                // Match eliminator equalities still rely on the old guarded-case clause-set lowering
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

    /// Build the constructor pattern for a match case and instantiate the case
    /// term with fresh field variables.
    ///
    /// This works whether the case term is still an explicit lambda tower or has
    /// already been eta-reduced to a function term.
    fn instantiate_match_case(
        &self,
        constructor_symbol: Symbol,
        datatype_type_args: &[Term],
        case_term: &Term,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        context: &mut LocalContext,
    ) -> Result<(Term, Term), String> {
        let mut constructor_type = self.symbol_table().get_type(constructor_symbol).clone();
        for type_arg in datatype_type_args {
            let Some((input, output)) = constructor_type.as_ref().split_pi() else {
                return Err(format!(
                    "constructor {constructor_symbol:?} is missing match type parameters"
                ));
            };
            if !input.is_type_param_kind() {
                return Err(format!(
                    "constructor {constructor_symbol:?} expected a value argument before all match type parameters were instantiated"
                ));
            }
            constructor_type = self.open_binder_body(&output.to_owned(), type_arg);
        }

        let mut constructor_args = datatype_type_args.to_vec();
        let mut field_args = Vec::new();
        while let Some((input, output)) = constructor_type.as_ref().split_pi() {
            if input.is_type_param_kind() {
                return Err(format!(
                    "constructor {constructor_symbol:?} unexpectedly requires extra type parameters during match clausification"
                ));
            }
            let input_type = input.to_owned();
            let var_id = *next_var_id;
            *next_var_id += 1;
            context.push_type(input_type.clone());
            let var = Term::new_variable(var_id);
            constructor_args.push(var.clone());
            field_args.push(var.clone());
            stack.push(TermBinding::Free);
            constructor_type = self.open_binder_body(&output.to_owned(), &var);
        }

        let pattern = Term::new(Atom::Symbol(constructor_symbol), constructor_args);
        let (case_value, _) = self.instantiate_binder_prefix(case_term, &field_args);
        Ok((pattern, case_value))
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
    /// Convert an elaborated kernel `Term` into a raw set of literal clauses.
    ///
    /// `true` is `[]`, `false` is `[[]]`, and we intentionally leave tautologies and
    /// redundancy for later clause normalization.
    ///
    /// The `stack` plays the same role as in value normalization:
    /// `TermBinding::Free` tracks forall-introduced variables and
    /// `TermBinding::Bound` tracks instantiated binder arguments.
    fn term_to_clause_set(
        &mut self,
        term: &Term,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        context: &mut LocalContext,
    ) -> Result<ClauseLiterals, String> {
        match term.as_ref().decompose() {
            crate::kernel::term::Decomposition::ForAll(_, _) => {
                if !negate {
                    // Only leading universals should open into the clause context during
                    // proposition lowering. Non-leading positive universals stay inline so
                    // they can still match their surface negated form during proof search.
                    let literal = Literal::from_signed_term(term.clone(), true);
                    Ok(clauses_from_literal(literal))
                } else {
                    // Keep negated universals inline so later boolean reductions can
                    // open them via existential structure without introducing witnesses here.
                    let literal = Literal::from_signed_term(term.clone(), false);
                    Ok(clauses_from_literal(literal))
                }
            }
            crate::kernel::term::Decomposition::Exists(_, _) => {
                if !negate {
                    // Keep positive existential formulas inline as signed terms.
                    // This avoids introducing witness terms during clausification.
                    let literal = Literal::from_signed_term(term.clone(), true);
                    Ok(clauses_from_literal(literal))
                } else {
                    // Preserve negated existentials inline so they can meet positive
                    // existential conclusions in the indexed resolution path.
                    let literal = Literal::from_signed_term(term.clone(), false);
                    Ok(clauses_from_literal(literal))
                }
            }
            _ => {
                // Builtin logical atoms are recognized by head symbol + arity.
                if let Some(args) = self.split_symbol_application(term, Symbol::Not, 1) {
                    return self.term_to_clause_set(&args[0], !negate, stack, next_var_id, context);
                }
                if let Some(args) = self.split_symbol_application(term, Symbol::And, 2) {
                    if !negate {
                        return self.term_and_to_clause_set(
                            &args[0],
                            &args[1],
                            false,
                            false,
                            stack,
                            next_var_id,
                            context,
                        );
                    }
                    return self.term_or_to_clause_set(
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
                        return Ok(clauses_from_literal(literal));
                    }

                    if !negate {
                        return self.term_or_to_clause_set(
                            &args[0],
                            &args[1],
                            false,
                            false,
                            stack,
                            next_var_id,
                            context,
                        );
                    }
                    return self.term_and_to_clause_set(
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
                    return self.term_eq_to_clause_set(
                        &args[1],
                        &args[2],
                        negate,
                        stack,
                        next_var_id,
                        context,
                    );
                }
                if let Some(args) = self.split_symbol_application(term, Symbol::Ite, 4) {
                    let cond_clauses =
                        self.term_to_clause_set(&args[1], false, stack, next_var_id, context)?;
                    let Some(cond_lit) = clauses_to_literal(cond_clauses) else {
                        return Err("term 'ite' condition is too complicated".to_string());
                    };
                    let then_clauses =
                        self.term_to_clause_set(&args[2], negate, stack, next_var_id, context)?;
                    let else_clauses =
                        self.term_to_clause_set(&args[3], negate, stack, next_var_id, context)?;
                    return Ok(clause_set_if(cond_lit, then_clauses, else_clauses));
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
                            let answer = self.term_to_clause_set(
                                &applied,
                                negate,
                                stack,
                                next_var_id,
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
                        Ok(clauses_false())
                    } else {
                        Ok(clauses_true())
                    };
                }
                if term == &Term::new_false() {
                    return if negate {
                        Ok(clauses_true())
                    } else {
                        Ok(clauses_false())
                    };
                }

                // Everything else must normalize to a single signed literal.
                let inline_term = self.term_to_inline_term(term, stack, next_var_id, context)?;
                let literal = Literal::from_signed_term(inline_term, !negate);
                Ok(clauses_from_literal(literal))
            }
        }
    }

    fn term_and_to_clause_set(
        &mut self,
        left: &Term,
        right: &Term,
        negate_left: bool,
        negate_right: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        context: &mut LocalContext,
    ) -> Result<ClauseLiterals, String> {
        let left = self.term_to_clause_set(left, negate_left, stack, next_var_id, context)?;
        let right = self.term_to_clause_set(right, negate_right, stack, next_var_id, context)?;
        Ok(clauses_and(left, right))
    }

    fn term_or_to_clause_set(
        &mut self,
        left: &Term,
        right: &Term,
        negate_left: bool,
        negate_right: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        context: &mut LocalContext,
    ) -> Result<ClauseLiterals, String> {
        let left = self.term_to_clause_set(left, negate_left, stack, next_var_id, context)?;
        let right = self.term_to_clause_set(right, negate_right, stack, next_var_id, context)?;
        Ok(clauses_or(left, right))
    }

    fn try_inline_term_to_term(&self, term: &Term) -> Result<Option<Term>, String> {
        match self.try_inline_term_to_signed_term(term)? {
            Some((t, true)) => Ok(Some(t)),
            Some((_t, false)) => Ok(None),
            None => Ok(None),
        }
    }

    /// Try to lower a top-level boolean term directly to one literal, without going through the
    /// general clause-set expansion path.
    ///
    /// This keeps ordinary proposition lowering shallow: either we recognize one literal
    /// directly, or we leave the boolean formula inline as a signed term.
    fn try_term_to_single_literal(
        &mut self,
        term: &Term,
        positive: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        context: &mut LocalContext,
    ) -> Result<Option<Literal>, String> {
        let Some(args) = self.split_symbol_application(term, Symbol::Eq, 3) else {
            return Ok(None);
        };

        // Equality against match eliminators is the remaining case that still genuinely wants
        // multi-clause guarded-case output. Keep those on the explicit clause-set path.
        if self.split_match_eliminator_application(&args[1]).is_some()
            || self.split_match_eliminator_application(&args[2]).is_some()
        {
            return Ok(None);
        }

        let left = &args[1];
        let right = &args[2];
        let left_type = self.term_type_for_normalization(left, context);
        let mut fn_arg_types = vec![];
        let mut result_type = left_type.clone();
        while let Some((input, output)) = result_type.as_ref().split_pi() {
            fn_arg_types.push(input.to_owned());
            result_type = output.to_owned();
        }

        if !fn_arg_types.is_empty() {
            if positive {
                let left = self.term_to_extended_term(left, stack, next_var_id, context)?;
                let right = self.term_to_extended_term(right, stack, next_var_id, context)?;
                let mut args = vec![];
                for arg_type_term in &fn_arg_types {
                    let var_id = *next_var_id;
                    *next_var_id += 1;
                    context.push_type(arg_type_term.clone());
                    args.push(Term::new_variable(var_id));
                }
                let left = self.extended_term_to_term(left.apply(&args), context)?;
                let right = self.extended_term_to_term(right.apply(&args), context)?;
                if result_type == Term::bool_type() {
                    if let Some(literal) =
                        self.bool_equality_to_single_literal(&left, &right, true)?
                    {
                        return Ok(Some(literal));
                    }
                }
                return Ok(Some(Literal::equals(left, right)));
            }

            let left = self.term_to_extended_term(left, stack, next_var_id, context)?;
            let right = self.term_to_extended_term(right, stack, next_var_id, context)?;
            let left = self.extended_term_to_term(left, context)?;
            let right = self.extended_term_to_term(right, context)?;
            return Ok(Some(Literal::not_equals(left, right)));
        }

        if left_type == Term::bool_type() {
            if let Some(literal) = self.bool_equality_to_single_literal(left, right, positive)? {
                return Ok(Some(literal));
            }
        }

        Ok(Some(Literal::new(positive, left.clone(), right.clone())))
    }

    fn bool_equality_to_single_literal(
        &self,
        left: &Term,
        right: &Term,
        positive: bool,
    ) -> Result<Option<Literal>, String> {
        let Some((left_term, left_sign)) = self.try_inline_term_to_signed_term(left)? else {
            return Ok(None);
        };
        let Some((right_term, right_sign)) = self.try_inline_term_to_signed_term(right)? else {
            return Ok(None);
        };
        let literal_positive = (left_sign == right_sign) == positive;
        Ok(Some(Literal::new(literal_positive, left_term, right_term)))
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

    fn apply_term_to_clause_set(
        &mut self,
        function: &Term,
        args: Vec<ExtendedTerm>,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        context: &mut LocalContext,
    ) -> Result<ClauseLiterals, String> {
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
                let answer = self.term_to_clause_set(&applied, negate, stack, next_var_id, context);
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
                Ok(clauses_from_literal(literal))
            }
            _ => Err("unhandled case: non-term application".to_string()),
        }
    }

    /// Convert `left = right` (or `!=` when `negate`) to a raw set of literal clauses.
    ///
    /// For function-typed terms, this performs extensional reasoning by applying
    /// fresh variables to both sides, then reducing to equality on results.
    /// Negated higher-order equalities stay as direct literals.
    fn term_eq_to_clause_set(
        &mut self,
        left: &Term,
        right: &Term,
        negate: bool,
        stack: &mut Vec<TermBinding>,
        next_var_id: &mut AtomId,
        context: &mut LocalContext,
    ) -> Result<ClauseLiterals, String> {
        if let Some((type_args, scrutinee, cases)) = self.split_match_eliminator_application(right)
        {
            let datatype_type_args = type_args[..type_args.len().saturating_sub(1)].to_vec();
            let mut answer = clauses_true();
            for (constructor_symbol, case_term) in &cases {
                let stack_len = stack.len();
                let (pattern, case_value) = self.instantiate_match_case(
                    *constructor_symbol,
                    &datatype_type_args,
                    case_term,
                    stack,
                    next_var_id,
                    context,
                )?;
                let condition = self.term_eq_to_clause_set(
                    &scrutinee,
                    &pattern,
                    false,
                    stack,
                    next_var_id,
                    context,
                )?;
                let conclusion = self.term_eq_to_clause_set(
                    left,
                    &case_value,
                    negate,
                    stack,
                    next_var_id,
                    context,
                )?;
                answer = clauses_and(answer, clauses_or(negate_clauses(&condition), conclusion));

                stack.truncate(stack_len);
            }
            return Ok(answer);
        }

        if let Some((type_args, scrutinee, cases)) = self.split_match_eliminator_application(left) {
            let datatype_type_args = type_args[..type_args.len().saturating_sub(1)].to_vec();
            let mut answer = clauses_true();
            for (constructor_symbol, case_term) in &cases {
                let stack_len = stack.len();
                let (pattern, case_value) = self.instantiate_match_case(
                    *constructor_symbol,
                    &datatype_type_args,
                    case_term,
                    stack,
                    next_var_id,
                    context,
                )?;
                let condition = self.term_eq_to_clause_set(
                    &scrutinee,
                    &pattern,
                    false,
                    stack,
                    next_var_id,
                    context,
                )?;
                let conclusion = self.term_eq_to_clause_set(
                    right,
                    &case_value,
                    negate,
                    stack,
                    next_var_id,
                    context,
                )?;
                answer = clauses_and(answer, clauses_or(negate_clauses(&condition), conclusion));

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
                return Ok(clauses_from_literal(Literal::new(false, left, right)));
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
                let left_pos = self.apply_term_to_clause_set(
                    left,
                    args.clone(),
                    false,
                    stack,
                    next_var_id,
                    context,
                )?;
                let left_neg = self.apply_term_to_clause_set(
                    left,
                    args.clone(),
                    true,
                    stack,
                    next_var_id,
                    context,
                )?;
                let right_pos = self.apply_term_to_clause_set(
                    right,
                    args.clone(),
                    false,
                    stack,
                    next_var_id,
                    context,
                )?;
                let right_neg =
                    self.apply_term_to_clause_set(right, args, true, stack, next_var_id, context)?;

                let result = if let Some((left_term, left_sign)) =
                    clauses_match_negated(&left_pos, &left_neg)
                {
                    if let Some((right_term, right_sign)) =
                        clauses_match_negated(&right_pos, &right_neg)
                    {
                        let positive = left_sign == right_sign;
                        let literal = Literal::new(positive, left_term.clone(), right_term.clone());
                        clauses_from_literal(literal)
                    } else {
                        let l_imp_r = clauses_or(left_neg, right_pos);
                        let r_imp_l = clauses_or(left_pos, right_neg);
                        clauses_and(l_imp_r, r_imp_l)
                    }
                } else {
                    let l_imp_r = clauses_or(left_neg, right_pos);
                    let r_imp_l = clauses_or(left_pos, right_neg);
                    clauses_and(l_imp_r, r_imp_l)
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
            return left
                .apply(&args)
                .eq_to_clause_set(right.apply(&args), false);
        }

        if left_type == Term::bool_type() {
            if let Some((left_term, left_sign)) = self.try_inline_term_to_signed_term(left)? {
                if let Some((right_term, right_sign)) =
                    self.try_inline_term_to_signed_term(right)?
                {
                    let positive = (left_sign == right_sign) ^ negate;
                    let literal = Literal::new(positive, left_term, right_term);
                    return Ok(clauses_from_literal(literal));
                }
            }

            if negate {
                let some = self.term_or_to_clause_set(
                    left,
                    right,
                    true,
                    true,
                    stack,
                    next_var_id,
                    context,
                )?;
                let not_both = self.term_or_to_clause_set(
                    left,
                    right,
                    false,
                    false,
                    stack,
                    next_var_id,
                    context,
                )?;
                return Ok(clauses_and(some, not_both));
            }

            let l_imp_r =
                self.term_or_to_clause_set(left, right, true, false, stack, next_var_id, context)?;
            let r_imp_l =
                self.term_or_to_clause_set(left, right, false, true, stack, next_var_id, context)?;
            return Ok(clauses_and(l_imp_r, r_imp_l));
        }

        let left = self.term_to_extended_term(left, stack, next_var_id, context)?;
        let right = self.term_to_extended_term(right, stack, next_var_id, context)?;
        left.eq_to_clause_set(right, negate)
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
                // higher-order arguments.
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

    /// Lower a normalized clause-shaped term into exactly one normalized clause.
    fn lower_normalized_term_to_clause_with_opening_policy(
        &mut self,
        term: &Term,
        open_leading_foralls: bool,
    ) -> Result<Clause, String> {
        let (mut context, mut next_var_id) = self.initial_exact_clause_context();
        let opened = if open_leading_foralls {
            self.open_leading_foralls_preserving_local_slots(term, &mut context, &mut next_var_id)
        } else {
            term.clone()
        };
        if opened == Term::new_false() {
            return Ok(Clause {
                literals: vec![],
                context,
            });
        }
        let literals = self.exact_clause_literals_from_term(&opened)?;
        Ok(Clause::from_literals_unnormalized(literals, &context).normalized_preserving_locals())
    }

    fn lower_normalized_term_to_clause(&mut self, term: &Term) -> Result<Clause, String> {
        self.lower_normalized_term_to_clause_with_opening_policy(term, true)
    }

    /// Interpret a normalized term as the exact disjunction shape used by quoted clauses.
    fn exact_clause_literals_from_term(&self, term: &Term) -> Result<Vec<Literal>, String> {
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

    /// Convert a term expression into the inline body form used by a single literal.
    ///
    /// This only succeeds for terms that are representable without introducing clause structure.
    fn term_to_inline_literal_body(&mut self, term: &Term) -> Result<Term, String> {
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
                    "term cannot be represented as an inline literal body (has_free_var={}, has_bound_var={})",
                    term.has_free_variable(),
                    term.has_bound_variable()
                ))
            }
        }
    }

    /// Convert a claim argument term for `claim_with_args` parsing.
    ///
    /// Prefer inline literal-body encoding when available (to preserve existing certificate
    /// shape), but allow richer terms when inline encoding is unavailable so cert parsing can
    /// round-trip generated witnesses, including lambdas that still refer to other claim locals.
    fn term_to_claim_arg_shape(&mut self, term: &Term) -> Result<Term, String> {
        match self.term_to_inline_literal_body(term) {
            Ok(inline_term) => Ok(inline_term),
            Err(_) => Ok(term.clone()),
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
    ) -> Result<Vec<Clause>, String> {
        let mut view = Clausifier::new_mut(self, type_var_map);
        view.lower_normalized_term_to_clauses(term)
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

    /// Kernel-owned entry point for lowering an already-normalized clause-shaped term while
    /// preserving a leading `forall` literal instead of opening it into the clause context.
    pub fn lower_normalized_term_to_clause_preserving_leading_foralls(
        &mut self,
        term: &Term,
        type_var_map: Option<HashMap<String, (AtomId, Term)>>,
    ) -> Result<Clause, String> {
        let mut view = Clausifier::new_mut(self, type_var_map);
        view.lower_normalized_term_to_clause_with_opening_policy(term, false)
    }

    /// Kernel-owned entry point for converting a term to the inline body form of a single
    /// literal.
    pub fn term_to_inline_literal_body(
        &mut self,
        term: &Term,
        type_var_map: Option<HashMap<String, (AtomId, Term)>>,
    ) -> Result<Term, String> {
        let mut view = Clausifier::new_mut(self, type_var_map);
        view.term_to_inline_literal_body(term)
    }

    /// Kernel-owned entry point for converting a term to claim-argument form.
    pub fn term_to_claim_arg(&mut self, term: &Term) -> Result<Term, String> {
        let mut view = Clausifier::new_mut(self, None);
        view.term_to_claim_arg_shape(term)
    }
}

#[cfg(test)]
mod tests {
    use crate::elaborator::acorn_type::{AcornType, Datatype};
    use crate::elaborator::acorn_value::{AcornValue, FunctionApplication, MatchCase};
    use crate::elaborator::names::ConstantName;
    use crate::elaborator::to_term::lower_value_to_term;
    use crate::kernel::atom::Atom;
    use crate::kernel::clause::Clause;
    use crate::kernel::kernel_context::KernelContext;
    use crate::kernel::literal::Literal;
    use crate::kernel::local_context::LocalContext;
    use crate::kernel::symbol_table::NewConstantType;
    use crate::kernel::term::{Decomposition, Term};
    use crate::kernel::term_normalization::normalize_term;
    use crate::module::ModuleId;

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
        let clauses = kernel_context
            .lower_normalized_term_to_clauses(&Term::not(forall_term), None)
            .expect("negated forall should clausify");

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
    fn test_leading_positive_forall_opens_into_clause_context() {
        let mut kernel_context = KernelContext::new();
        kernel_context.parse_constant("g0", "Bool -> Bool");

        let term = Term::forall(
            Term::bool_type(),
            kernel_context
                .parse_term("g0")
                .apply(&[Term::atom(Atom::BoundVariable(0))]),
        );
        let clauses = kernel_context
            .lower_normalized_term_to_clauses(&term, None)
            .expect("leading forall should clausify");

        assert_eq!(clauses.len(), 1, "expected a single clause");
        assert_eq!(clauses[0].context.len(), 1, "expected opened forall binder");
        assert_eq!(clauses[0].literals.len(), 1, "expected a single literal");
        assert_eq!(
            clauses[0].literals[0],
            Literal::positive(
                kernel_context
                    .parse_term("g0")
                    .apply(&[Term::new_variable(0)])
            ),
            "expected leading forall body to open into the clause context"
        );
    }

    #[test]
    fn test_nonleading_positive_forall_stays_inline_in_clause_literal() {
        let mut kernel_context = KernelContext::new();
        kernel_context.parse_constants(&["c0"], "Bool");
        kernel_context.parse_constant("g0", "Bool -> Bool");

        let forall_term = Term::forall(
            Term::bool_type(),
            kernel_context
                .parse_term("g0")
                .apply(&[Term::atom(Atom::BoundVariable(0))]),
        );
        let term = Term::or(
            Term::not(kernel_context.parse_term("c0")),
            forall_term.clone(),
        );
        let clauses = kernel_context
            .lower_normalized_term_to_clauses(&term, None)
            .expect("non-leading forall should clausify");

        assert_eq!(clauses.len(), 1, "expected a single clause");
        assert_eq!(
            clauses[0].context.len(),
            0,
            "expected non-leading forall to stay out of the clause context"
        );
        assert_eq!(
            clauses[0].literals.len(),
            2,
            "expected two disjunctive literals"
        );
        assert!(
            clauses[0].literals.iter().any(|literal| literal.positive
                && matches!(
                    literal.left.as_ref().decompose(),
                    Decomposition::ForAll(_, _)
                )),
            "expected a positive inline forall literal: {:?}",
            clauses[0]
        );
        assert!(
            clauses[0]
                .literals
                .iter()
                .any(|literal| !literal.positive && literal.left == kernel_context.parse_term("c0")),
            "expected the negated boolean disjunct to remain alongside the inline forall: {:?}",
            clauses[0]
        );
        assert!(
            clauses[0]
                .literals
                .iter()
                .any(|literal| literal.positive && literal.left == forall_term),
            "expected the original forall term to remain intact: {:?}",
            clauses[0]
        );
    }

    #[test]
    fn test_lower_normalized_term_to_clauses_uses_single_clause_policy() {
        let mut kernel_context = KernelContext::new();
        kernel_context.parse_constants(&["c0", "c1"], "Bool");
        let term = Term::or(
            kernel_context.parse_term("c0"),
            kernel_context.parse_term("c1"),
        );

        let clauses = kernel_context
            .lower_normalized_term_to_clauses(&term, None)
            .expect("term lowering should succeed");
        assert_eq!(clauses.len(), 1);
        assert_eq!(clauses[0].literals.len(), 2);
    }

    #[test]
    fn test_boolean_equality_with_negated_side_canonicalizes_to_inequality_literal() {
        let mut kernel_context = KernelContext::new();
        kernel_context.parse_constants(&["c0", "c1"], "Bool");
        let term = Term::eq(
            Term::bool_type(),
            Term::not(kernel_context.parse_term("c0")),
            kernel_context.parse_term("c1"),
        );

        let clauses = kernel_context
            .lower_normalized_term_to_clauses(&term, None)
            .expect("boolean equality should clausify");

        assert_eq!(clauses.len(), 1, "expected a single clause");
        assert_eq!(clauses[0].literals.len(), 1, "expected a single literal");
        assert_eq!(
            clauses[0].literals[0],
            Literal::not_equals(kernel_context.parse_term("c0"), kernel_context.parse_term("c1")),
            "expected boolean equality with negated side to collapse to a canonical inequality literal"
        );
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

    #[test]
    fn test_match_clausification_accepts_eta_reduced_case_functions() {
        let mut kernel_context = KernelContext::new();

        let nat = Datatype {
            module_id: ModuleId(0),
            name: "Nat".to_string(),
        };
        let int = Datatype {
            module_id: ModuleId(0),
            name: "Int".to_string(),
        };
        let nat_type = AcornType::Data(nat.clone(), vec![]);
        let int_type = AcornType::Data(int.clone(), vec![]);

        let zero_name = ConstantName::datatype_attr(ModuleId(0), nat.clone(), "zero");
        let succ_name = ConstantName::datatype_attr(ModuleId(0), nat, "succ");
        let from_nat_name = ConstantName::datatype_attr(ModuleId(0), int.clone(), "from_nat");
        let neg_suc_name = ConstantName::datatype_attr(ModuleId(0), int, "neg_suc");

        let zero = AcornValue::constant(
            zero_name,
            vec![],
            nat_type.clone(),
            nat_type.clone(),
            vec![],
            vec![],
        );
        let succ = AcornValue::constant(
            succ_name,
            vec![],
            AcornType::functional(vec![nat_type.clone()], nat_type.clone()),
            AcornType::functional(vec![nat_type.clone()], nat_type.clone()),
            vec![],
            vec![],
        );
        let from_nat = AcornValue::constant(
            from_nat_name,
            vec![],
            AcornType::functional(vec![nat_type.clone()], int_type.clone()),
            AcornType::functional(vec![nat_type.clone()], int_type.clone()),
            vec![],
            vec![],
        );
        let neg_suc = AcornValue::constant(
            neg_suc_name,
            vec![],
            AcornType::functional(vec![nat_type.clone()], int_type.clone()),
            AcornType::functional(vec![nat_type.clone()], int_type.clone()),
            vec![],
            vec![],
        );

        let match_value = AcornValue::Match(
            Box::new(zero.clone()),
            vec![
                MatchCase {
                    new_vars: vec![],
                    pattern: zero.clone(),
                    result: AcornValue::Application(FunctionApplication {
                        function: Box::new(from_nat.clone()),
                        args: vec![zero.clone()],
                    }),
                    constructor_index: 0,
                    constructor_total: 2,
                },
                MatchCase {
                    new_vars: vec![nat_type.clone()],
                    pattern: AcornValue::Application(FunctionApplication {
                        function: Box::new(succ),
                        args: vec![AcornValue::Variable(0, nat_type.clone())],
                    }),
                    result: AcornValue::Application(FunctionApplication {
                        function: Box::new(neg_suc),
                        args: vec![AcornValue::Variable(0, nat_type.clone())],
                    }),
                    constructor_index: 1,
                    constructor_total: 2,
                },
            ],
        );

        {
            let symbol_table = &mut kernel_context.symbol_table;
            let type_store = &mut kernel_context.type_store;
            symbol_table.add_from(&match_value, NewConstantType::Global, type_store);
        }

        let lowered = lower_value_to_term(
            &mut kernel_context,
            &match_value,
            NewConstantType::Local,
            None,
        )
        .expect("match lowering should succeed");
        let normalized = normalize_term(&lowered);
        let (_, args) = normalized
            .as_ref()
            .split_application_multi()
            .expect("normalized match should stay an application");
        assert!(
            args[3].as_ref().split_lambda().is_none(),
            "eta normalization should remove the forwarding constructor lambda: {normalized:?}"
        );

        let int_term = kernel_context
            .type_store
            .get_type_term(&int_type)
            .expect("Int should be registered")
            .clone();
        let a_name = ConstantName::unqualified(ModuleId(0), "a");
        let a_symbol = kernel_context.symbol_table.add_constant(
            a_name,
            NewConstantType::Global,
            int_term.clone(),
        );
        let equality = Term::eq(int_term, Term::atom(Atom::Symbol(a_symbol)), normalized);
        let clauses = kernel_context
            .lower_normalized_term_to_clauses(&equality, None)
            .expect("clausification should accept eta-reduced match branches");

        assert!(!clauses.is_empty(), "match equality should produce clauses");
        for clause in &clauses {
            clause.validate(&kernel_context);
        }
    }
}

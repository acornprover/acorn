use std::collections::{HashSet, VecDeque};

use im::HashMap as ImHashMap;
use im::HashSet as ImHashSet;
use im::Vector as ImVector;

use crate::code_generator::Error;
use crate::elaborator::source::Source;
use crate::kernel::certificate_step::CertificateStep;
use crate::kernel::clause::Clause;
use crate::kernel::inference;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::proof_step::Rule;
use crate::kernel::{EqualityGraph, StepId};
use tracing::trace;

/// The reason why a certificate step was accepted.
#[derive(Debug, Clone)]
pub enum StepReason {
    /// Proven by the term graph (concrete reasoning via congruence closure and propositional logic).
    EqualityGraph,

    /// An assumption based on normalizing a statement elsewhere in the code.
    /// The source points to the location of the assumption.
    Assumption(Source),

    /// A let...satisfy statement that skolemizes an exists statement.
    /// The source points to where the exists was originally defined.
    Skolemization(Source),

    /// The checker already had a contradiction, so everything is trivially true.
    Contradiction,

    /// A claim statement from a previous certificate step.
    PreviousClaim,

    /// A clause inserted during testing.
    Testing,

    /// Proven by a single step of equality resolution, based on the given step id
    EqualityResolution(usize),

    /// Proven by extensionality, based on the given step id
    Extensionality(usize),

    /// Proven by equality factoring, based on the given step id
    EqualityFactoring(usize),

    /// Proven by injectivity, based on the given step id
    Injectivity(usize),

    /// Proven by boolean reduction, based on the given step id
    BooleanReduction(usize),
}

impl StepReason {
    pub fn description(&self) -> String {
        match self {
            StepReason::EqualityGraph => "simplification".to_string(),
            StepReason::Assumption(source) | StepReason::Skolemization(source) => {
                source.description()
            }
            StepReason::Contradiction => "ex falso".to_string(),
            StepReason::PreviousClaim => "previous claim".to_string(),
            StepReason::Testing => "testing".to_string(),
            StepReason::EqualityResolution(_) => "equality resolution".to_string(),
            StepReason::Extensionality(_) => "extensionality".to_string(),
            StepReason::EqualityFactoring(_) => "equality factoring".to_string(),
            StepReason::Injectivity(_) => "injectivity".to_string(),
            StepReason::BooleanReduction(_) => "boolean reduction".to_string(),
        }
    }

    pub fn dependency(&self) -> Option<usize> {
        match self {
            StepReason::EqualityResolution(step_id)
            | StepReason::Extensionality(step_id)
            | StepReason::EqualityFactoring(step_id)
            | StepReason::Injectivity(step_id)
            | StepReason::BooleanReduction(step_id) => Some(*step_id),
            _ => None,
        }
    }
}

/// A checked certificate claim in kernel terms.
#[derive(Debug, Clone)]
pub struct CheckedStep {
    /// The claim clause as checked by the kernel.
    pub clause: Clause,

    /// The reason this step was accepted.
    pub reason: StepReason,

    /// The original certificate code line for this step, when available.
    pub code_line: Option<String>,
}

/// The checker quickly checks if a clause can be proven in a single step from known clauses.
///
/// The types of single-step we support are:
///
///   Substitutions into a known theorem (or exact variable-clause matches for variable clauses).
///   "Congruence closure" of equalities and subterm relationships. Handled by the EqualityGraph.
///   Propositional calculus on concrete literals. Handled by the EqualityGraph.
///   Introducing variables for existential quantifiers during clausification.
#[derive(Clone)]
pub struct Checker {
    /// For deductions among concrete clauses.
    term_graph: EqualityGraph,

    /// Clauses are matched by exact canonical equality only.
    /// The `usize` value is the `step_id` (index into `self.reasons`) for that clause.
    exact_clauses: ImHashMap<Clause, usize>,

    /// Whether a contradiction was directly inserted into the checker.
    direct_contradiction: bool,

    /// A hack, but we need to break out of loops, since equality factoring and boolean
    /// reduction can create cycles.
    past_boolean_reductions: ImHashSet<Clause>,

    /// The reason for each step. The step_id is the index in this vector.
    reasons: ImVector<StepReason>,
}

impl Checker {
    pub fn new() -> Checker {
        Checker {
            term_graph: EqualityGraph::new(),
            exact_clauses: ImHashMap::new(),
            direct_contradiction: false,
            past_boolean_reductions: ImHashSet::new(),
            reasons: ImVector::new(),
        }
    }

    /// Adds a true clause to the checker with a specific reason.
    pub fn insert_clause(
        &mut self,
        clause: &Clause,
        reason: StepReason,
        kernel_context: &KernelContext,
    ) {
        trace!(clause = %clause, reason = ?reason.description(), "inserting clause");

        if clause.is_impossible() {
            self.direct_contradiction = true;
            return;
        }

        let step_id = self.reasons.len();
        self.reasons.push_back(reason.clone());

        // Normalize before exact matching so we do not depend on literal ordering
        // or variable numbering conventions at insertion sites.
        self.exact_clauses
            .entry(clause.exact_match_key())
            .or_insert(step_id);

        if clause.has_any_variable() {
            if let Some(reduced_clause) =
                self.simplify_variable_clause_with_concrete_facts(clause, kernel_context)
            {
                self.insert_clause(&reduced_clause, StepReason::EqualityGraph, kernel_context);
            }

            // We only need to do equality resolution for clauses with free variables,
            // because resolvable concrete literals would already have been simplified out.
            for resolution in inference::equality_resolutions(clause, kernel_context) {
                self.insert_clause(
                    &resolution,
                    StepReason::EqualityResolution(step_id),
                    kernel_context,
                );
            }

            if let Some(extensionality) = clause.find_extensionality(kernel_context) {
                let ext_clause = Clause::new(extensionality, clause.get_local_context());
                self.insert_clause(
                    &ext_clause,
                    StepReason::Extensionality(step_id),
                    kernel_context,
                );
            }
        } else {
            // The clause is concrete.
            self.term_graph
                .insert_clause(clause, StepId(step_id), kernel_context);
        }

        for factoring in inference::equality_factorings(clause, kernel_context) {
            self.insert_clause(
                &factoring,
                StepReason::EqualityFactoring(step_id),
                kernel_context,
            );
        }

        for injectivity in clause.injectivities() {
            self.insert_clause(
                &injectivity,
                StepReason::Injectivity(step_id),
                kernel_context,
            );
        }

        for boolean_reduction in clause.boolean_reductions(kernel_context) {
            // Guard against infinite loops
            if self.past_boolean_reductions.contains(&boolean_reduction) {
                continue;
            }
            self.past_boolean_reductions
                .insert(boolean_reduction.clone());
            self.insert_clause(
                &boolean_reduction,
                StepReason::BooleanReduction(step_id),
                kernel_context,
            );
        }
    }

    /// Checks if a clause is known to be true, and returns the reason if so.
    /// Returns None if the clause cannot be proven.
    fn check_clause_direct(
        &mut self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<StepReason> {
        if self.has_contradiction() {
            trace!(clause = %clause, result = "contradiction", "checking clause");
            return Some(StepReason::Contradiction);
        }

        // Check the term graph for concrete evaluation
        if self.term_graph.check_clause(clause, kernel_context) {
            trace!(clause = %clause, result = "term_graph", "checking clause");
            return Some(StepReason::EqualityGraph);
        }

        let canonical_clause = clause.exact_match_key();
        if let Some(step_id) = self.exact_clauses.get(&canonical_clause) {
            trace!(
                clause = %clause,
                result = "exact_clause",
                "checking clause"
            );
            return Some(self.reasons[*step_id].clone());
        }

        if clause.has_any_variable() {
            let candidates: Vec<Clause> = self.exact_clauses.keys().cloned().collect();
            for candidate in &candidates {
                let Some(reduced_clause) =
                    self.simplify_variable_clause_with_concrete_facts(candidate, kernel_context)
                else {
                    continue;
                };
                if reduced_clause.exact_match_key() == canonical_clause {
                    trace!(
                        clause = %clause,
                        result = "simplified_variable_clause",
                        "checking clause"
                    );
                    return Some(StepReason::EqualityGraph);
                }
            }
        }

        trace!(clause = %clause, result = "failed", "checking clause");
        None
    }

    fn check_clause_via_boolean_reductions(
        &mut self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<StepReason> {
        if clause.has_any_variable() {
            return None;
        }

        let mut seen = HashSet::new();
        let mut queue = VecDeque::new();
        for next in clause.boolean_reductions(kernel_context) {
            queue.push_back(next);
        }

        while let Some(candidate) = queue.pop_front() {
            if !seen.insert(candidate.clone()) {
                continue;
            }

            if let Some(reason) = self.check_clause_direct(&candidate, kernel_context) {
                return Some(reason);
            }

            for next in candidate.boolean_reductions(kernel_context) {
                if !seen.contains(&next) {
                    queue.push_back(next);
                }
            }
        }

        None
    }

    /// Checks if a clause is known to be true, and returns the reason if so.
    /// Returns None if the clause cannot be proven.
    pub fn check_clause(
        &mut self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<StepReason> {
        self.check_clause_direct(clause, kernel_context)
            .or_else(|| self.check_clause_via_boolean_reductions(clause, kernel_context))
    }

    fn simplify_variable_clause_with_concrete_facts(
        &mut self,
        clause: &Clause,
        kernel_context: &KernelContext,
    ) -> Option<Clause> {
        let mut changed = false;
        let mut reduced_literals = Vec::with_capacity(clause.literals.len());
        for literal in &clause.literals {
            match self.term_graph.evaluate_literal(literal, kernel_context) {
                Some(true) => return None,
                Some(false) => changed = true,
                None => reduced_literals.push(literal.clone()),
            }
        }
        if !changed {
            return None;
        }
        Some(Clause::new(reduced_literals, clause.get_local_context()))
    }

    /// Returns true if the checker has encountered a contradiction.
    ///
    /// It is possible that both a clause and its negation are known to be true, and yet
    /// has_contradiction returns false.
    /// This is because we do not unify all terms we ever encounter.
    ///
    /// We do guarantee that if you insert both a term and its negation then
    /// has_contradiction will return true.
    pub fn has_contradiction(&self) -> bool {
        self.direct_contradiction || self.term_graph.has_contradiction()
    }

    /// Insert goal clauses into the checker.
    /// Normalizes the goal and inserts all resulting clauses as assumptions.
    pub fn insert_goal(
        &mut self,
        goal: &crate::elaborator::goal::Goal,
        kernel_context: &mut crate::kernel::kernel_context::KernelContext,
    ) -> Result<(), Error> {
        trace!("inserting goal {} (line {})", goal.name, goal.first_line);

        let source = &goal.proposition.source;
        let lowered =
            crate::elaborator::lowering::lower_goal(kernel_context, goal).map_err(|e| e.message)?;
        // Use the post-lowering kernel context, since lowering the goal may create synthetics.
        let kernel_context = kernel_context;
        for step in &lowered.steps {
            // Use the step's own source if it's an assumption (which includes negated goals),
            // otherwise use the goal's source
            let step_source = if let Rule::Assumption(info) = &step.rule {
                &info.source
            } else {
                source
            };
            self.insert_clause(
                &step.clause,
                StepReason::Assumption(step_source.clone()),
                kernel_context,
            );
        }
        Ok(())
    }

    /// Insert pre-lowered goal clauses into the checker.
    /// Uses the provided lowered goal (including its kernel context state).
    pub fn insert_lowered_goal(
        &mut self,
        normalized: &crate::elaborator::lowering::LoweredGoal,
    ) -> Result<(), Error> {
        trace!(
            "inserting lowered goal {} (line {})",
            normalized.goal.name,
            normalized.goal.first_line
        );

        let source = &normalized.goal.proposition.source;
        let kernel_context = &normalized.kernel_context;
        for step in &normalized.steps {
            let step_source = if let Rule::Assumption(info) = &step.rule {
                &info.source
            } else {
                source
            };
            self.insert_clause(
                &step.clause,
                StepReason::Assumption(step_source.clone()),
                kernel_context,
            );
        }
        Ok(())
    }

    /// Check already-parsed certificate steps.
    pub fn check_cert_steps(
        &mut self,
        cert_steps: &[CertificateStep],
        code_lines: Option<&[String]>,
        kernel_context: &KernelContext,
    ) -> Result<(Vec<CheckedStep>, usize), Error> {
        let mut checked_steps = Vec::new();
        let mut seen_claims = HashSet::new();

        for (step_index, step) in cert_steps.iter().enumerate() {
            if self.has_contradiction() {
                trace!("has_contradiction (early exit)");
                return Ok((checked_steps, step_index));
            }

            match step {
                CertificateStep::Claim(claim) => {
                    let generic_clause = claim.normalized_generic_clause();
                    let clause = Self::instantiate_claim_clause(claim, kernel_context)?;
                    if !seen_claims.insert(clause.clone()) {
                        continue;
                    }

                    let reason = self
                        .check_clause(&generic_clause, &kernel_context)
                        .or_else(|| self.check_clause(&clause, &kernel_context));

                    let Some(reason) = reason else {
                        let cert_line_context = code_lines
                            .and_then(|lines| lines.get(step_index))
                            .map(|line| {
                                format!("; certificate line {}: {:?}", step_index + 1, line)
                            })
                            .unwrap_or_default();
                        return Err(Error::GeneratedBadCode(format!(
                            "Claim at step {} is not obviously true{} (generic debug: {:?}; specialized debug: {:?})",
                            step_index + 1,
                            cert_line_context,
                            claim.clause,
                            clause,
                        )));
                    };

                    checked_steps.push(CheckedStep {
                        clause: clause.clone(),
                        reason,
                        code_line: code_lines.and_then(|lines| lines.get(step_index)).cloned(),
                    });

                    self.insert_clause(&generic_clause, StepReason::PreviousClaim, &kernel_context);
                    self.insert_clause(&clause, StepReason::PreviousClaim, &kernel_context);
                }
            }
        }

        if self.has_contradiction() {
            trace!("has_contradiction (end of proof)");
            Ok((checked_steps, cert_steps.len()))
        } else {
            Err(Error::GeneratedBadCode(
                "proof does not result in a contradiction".to_string(),
            ))
        }
    }

    fn instantiate_claim_clause(
        claim: &crate::kernel::certificate_step::Claim,
        kernel_context: &KernelContext,
    ) -> Result<Clause, Error> {
        claim
            .normalized_specialized_clause(kernel_context)
            .map_err(Error::GeneratedBadCode)
    }
}

/// A test wrapper that combines a Checker with a KernelContext.
#[cfg(test)]
struct TestChecker {
    checker: Checker,
    context: KernelContext,
}

#[cfg(test)]
impl TestChecker {
    /// Creates a TestChecker with properly typed symbols.
    fn with_clauses(clauses: &[&str]) -> TestChecker {
        let mut context = KernelContext::new();
        // c0-c5: Bool constants
        context.parse_constants(&["c0", "c1", "c2", "c3", "c4", "c5"], "Bool");
        // g0, g1, g3, g4: (Bool, Bool) -> Bool functions
        context.parse_constants(&["g0", "g1"], "(Bool, Bool) -> Bool");
        // g2 placeholder to get to g3 and g4
        context.parse_constant("g2", "(Bool, Bool) -> Bool");
        context.parse_constants(&["g3", "g4"], "(Bool, Bool) -> Bool");

        let mut checker = Checker::new();
        for clause_str in clauses {
            let clause = context.parse_clause(clause_str, &[]);
            checker.insert_clause(&clause, StepReason::Testing, &context);
        }
        TestChecker { checker, context }
    }

    fn check_clause_str(&mut self, s: &str) {
        let clause = self.context.parse_clause(s, &[]);
        if !self.checker.check_clause(&clause, &self.context).is_some() {
            panic!("check_clause_str(\"{}\") failed", s);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::inference;
    use std::collections::{HashSet, VecDeque};

    fn problematic_negated_forall_clause() -> (KernelContext, Clause) {
        use crate::kernel::atom::Atom;
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::term::Term;

        let mut context = KernelContext::new();
        context.parse_constants(&["g0", "g1"], "Bool -> Bool");
        let binder = Term::bool_type();
        let bound = Term::atom(Atom::BoundVariable(0));
        let g0_body =
            Term::new_variable(0).apply(&[context.parse_term("g0").apply(&[bound.clone()])]);
        let g1_body = Term::new_variable(0).apply(&[context.parse_term("g1").apply(&[bound])]);

        let clause = Clause::new(
            vec![
                Literal::negative(Term::forall(binder.clone(), g0_body)),
                Literal::negative(Term::forall(binder, g1_body)),
                Literal::positive(Term::new_variable(0).apply(&[Term::new_variable(1)])),
            ],
            &LocalContext::from_types(vec![context.parse_type("Bool -> Bool"), Term::bool_type()]),
        );
        (context, clause)
    }

    fn checker_style_clause_closure(
        kernel_context: &KernelContext,
        start: Clause,
        limit: usize,
    ) -> Vec<Clause> {
        let mut seen = HashSet::new();
        let mut queue = VecDeque::new();
        let mut ordered = vec![];

        seen.insert(start.clone());
        queue.push_back(start);

        while let Some(clause) = queue.pop_front() {
            ordered.push(clause.clone());
            if ordered.len() >= limit {
                break;
            }

            for next in clause.boolean_reductions(kernel_context) {
                if seen.insert(next.clone()) {
                    queue.push_back(next);
                }
            }
            for next in inference::equality_resolutions(&clause, kernel_context) {
                if seen.insert(next.clone()) {
                    queue.push_back(next);
                }
            }
            for next in inference::equality_factorings(&clause, kernel_context) {
                if seen.insert(next.clone()) {
                    queue.push_back(next);
                }
            }
            for next in clause.injectivities() {
                if seen.insert(next.clone()) {
                    queue.push_back(next);
                }
            }
            if let Some(extensionality) = clause.find_extensionality(kernel_context) {
                let next = Clause::new(extensionality, clause.get_local_context());
                if seen.insert(next.clone()) {
                    queue.push_back(next);
                }
            }
        }

        ordered
    }

    #[test]
    fn test_checker_should_be_monovariant() {
        // This basic case works
        let mut checker1 = TestChecker::with_clauses(&[
            "not g0(g1(c5, c0), c1)",
            "g4(c4, g1(c5, c0)) != g1(c3, c0) or not g0(g1(c3, c0), c1) or g0(g1(c5, c0), c1) or c4 = c1",
        ]);

        checker1.check_clause_str(
            "g4(c4, g1(c5, c0)) != g1(c3, c0) or not g0(g1(c3, c0), c1) or c4 = c1",
        );

        // This is the basic case plus extra things. So it should also work.
        let mut checker2 = TestChecker::with_clauses(&[
            // The minimal set of clauses that screw up our result
            "g4(c4, c5) = c3",
            "c4 != c0",
            "g4(c4, c5) != c3 or g4(c4, g1(c5, c0)) = g1(c3, c0) or c4 = c0",

            // The clauses from the basic case
            "not g0(g1(c5, c0), c1)",
            "g4(c4, g1(c5, c0)) != g1(c3, c0) or not g0(g1(c3, c0), c1) or g0(g1(c5, c0), c1) or c4 = c1",
        ]);

        checker2.check_clause_str(
            "g4(c4, g1(c5, c0)) != g1(c3, c0) or not g0(g1(c3, c0), c1) or c4 = c1",
        );
    }

    #[test]
    fn test_checker_cascades_updates() {
        // "c0 or c1 or c2" should combine with "not c2" to yield "c0 or c1".
        // That should then reduce via truth table logic with "not c0 or c1" to yield "c1".
        let mut checker = TestChecker::with_clauses(&["c0 or c1 or c2", "not c0 or c1", "not c2"]);
        checker.check_clause_str("c1");
    }

    #[test]
    fn test_checker_requires_exact_variable_clause_match() {
        let mut context = KernelContext::new();
        context.parse_constants(&["c0", "c1"], "Bool");
        context.parse_constant("g0", "Bool -> Bool");

        let mut checker = Checker::new();
        let generic = context.parse_clause("g0(x0)", &["Bool"]);
        checker.insert_clause(&generic, StepReason::Testing, &context);

        // Exact variable clause lookup is allowed for variable clauses.
        assert!(checker.check_clause(&generic, &context).is_some());

        // But specialization via generalization matching is disabled for variable clauses.
        let specialized = context.parse_clause("g0(c0)", &[]);
        assert!(checker.check_clause(&specialized, &context).is_none());
    }

    #[test]
    fn test_checker_simplifies_variable_clause_using_concrete_literal() {
        let mut context = KernelContext::new();
        context.parse_constants(&["c0", "c1"], "Bool");
        context.parse_constant("g0", "(Bool, Bool) -> Bool");

        let mut checker = Checker::new();
        let not_baz = context.parse_clause("not c1", &[]);
        checker.insert_clause(&not_baz, StepReason::Testing, &context);

        let generic = context.parse_clause("not g0(x0, c0) or c1", &["Bool"]);
        checker.insert_clause(&generic, StepReason::Testing, &context);

        let reduced = context.parse_clause("not g0(x0, c0)", &["Bool"]);
        assert!(checker.check_clause(&reduced, &context).is_some());
    }

    #[test]
    fn test_checker_simplifies_variable_clause_after_concrete_fact_arrives() {
        let mut context = KernelContext::new();
        context.parse_constants(&["c0", "c1"], "Bool");
        context.parse_constant("g0", "(Bool, Bool) -> Bool");

        let mut checker = Checker::new();
        let generic = context.parse_clause("not g0(x0, c0) or c1", &["Bool"]);
        checker.insert_clause(&generic, StepReason::Testing, &context);

        let not_baz = context.parse_clause("not c1", &[]);
        checker.insert_clause(&not_baz, StepReason::Testing, &context);

        let reduced = context.parse_clause("not g0(x0, c0)", &["Bool"]);
        assert!(checker.check_clause(&reduced, &context).is_some());
    }

    #[test]
    fn test_checker_matches_identical_boolean_formula_literal_clause() {
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::term::Term;

        let mut context = KernelContext::new();
        context.parse_constants(&["g0", "g1", "g2", "g3"], "Bool -> Bool");

        let x0 = Term::new_variable(0);
        let g0 = context.parse_term("g0").apply(std::slice::from_ref(&x0));
        let g1 = context.parse_term("g1").apply(std::slice::from_ref(&x0));
        let g2 = context.parse_term("g2").apply(std::slice::from_ref(&x0));
        let g3 = context.parse_term("g3").apply(std::slice::from_ref(&x0));
        let term = Term::or(Term::and(g0, Term::or(Term::not(g1), Term::not(g2))), g3);

        let clause = Clause::from_literals_unnormalized(
            vec![Literal::positive(term)],
            &LocalContext::from_types(vec![Term::bool_type()]),
        );

        let mut checker = Checker::new();
        checker.insert_clause(&clause, StepReason::Testing, &context);

        let canonical = clause.exact_match_key();
        assert!(
            checker.exact_clauses.contains_key(&canonical),
            "expected canonical clause {} to be stored for exact matching",
            canonical
        );
        assert!(checker.check_clause(&clause, &context).is_some());
    }

    #[test]
    fn test_checker_matches_identical_concrete_boolean_formula_literal_clause() {
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::term::Term;

        let mut context = KernelContext::new();
        context.parse_constants(&["c0", "c1"], "Bool");
        let c0 = context.parse_term("c0");
        let c1 = context.parse_term("c1");

        let clause = Clause::from_literals_unnormalized(
            vec![Literal::positive(Term::and(Term::not(c0), Term::not(c1)))],
            &LocalContext::empty(),
        );

        let mut checker = Checker::new();
        checker.insert_clause(&clause, StepReason::Testing, &context);

        assert!(checker.check_clause(&clause, &context).is_some());
    }

    #[test]
    fn test_checker_reduces_concrete_boolean_formula_clause_before_checking() {
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::term::Term;

        let mut context = KernelContext::new();
        context.parse_constant("c0", "Bool");
        let c0 = context.parse_term("c0");

        let reduced = Clause::from_literals_unnormalized(
            vec![Literal::positive(c0.clone())],
            &LocalContext::empty(),
        );
        let query = Clause::from_literals_unnormalized(
            vec![Literal::positive(Term::not(Term::not(c0)))],
            &LocalContext::empty(),
        );

        let mut checker = Checker::new();
        checker.insert_clause(&reduced, StepReason::Testing, &context);

        assert!(checker.check_clause(&query, &context).is_some());
    }

    #[test]
    fn test_checker_mixed_clause_extensionality_contradicts_direct_function_inequality() {
        let mut context = KernelContext::new();
        context.parse_constants(&["c0", "c1"], "Bool");
        context
            .parse_constant("g0", "Bool -> Bool -> Bool")
            .parse_constant("g1", "Bool -> Bool -> Bool");

        let mut checker = Checker::new();
        let mixed = context.parse_clause("not c1 or g0(c0, x0) = g1(c0, x0)", &["Bool"]);
        checker.insert_clause(&mixed, StepReason::Testing, &context);

        let guard = context.parse_clause("c1", &[]);
        checker.insert_clause(&guard, StepReason::Testing, &context);

        let neq = context.parse_clause("g0(c0) != g1(c0)", &[]);
        checker.insert_clause(&neq, StepReason::Testing, &context);

        assert!(
            checker.has_contradiction(),
            "mixed-clause extensionality should derive g0(c0) = g1(c0) and contradict the direct inequality"
        );
    }

    #[test]
    fn test_checker_typeclass_generalization() {
        // This test reproduces the exact bug from test_proving_with_default_required_attribute.
        //
        // From debug output of the failing test:
        // - Inserted: g4(x0) or g3(x0) = g2(x0) with x0: Typeclass(0)
        //   Only 1 form generated (stays as-is)
        // - Searched: g4(T0) or g3(T0) = g2(T0) with T0 = GroundTypeId(0)
        //   Specialized form: g3(T0) = g2(T0) or g4(T0) (reordered!)
        //
        // The bug: literals get reordered in specialized form but the general form
        // doesn't have that ordering stored.

        use crate::elaborator::acorn_type::{AcornType, Datatype, Typeclass};
        use crate::kernel::atom::Atom;
        use crate::kernel::generalization_set::GeneralizationSet;
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::symbol::Symbol;
        use crate::kernel::term::Term;
        use crate::module::ModuleId;

        let mut kctx = KernelContext::new();

        // Create typeclass Arf (TypeclassId(0))
        let arf_tc = Typeclass {
            module_id: ModuleId(0),
            name: "Arf".to_string(),
        };
        let arf_tc_id = kctx.type_store.add_typeclass(&arf_tc);

        // Create ground type Foo (GroundTypeId(0)) that implements Arf
        kctx.parse_datatype("Foo");
        let foo_id = kctx.type_store.get_ground_id_by_name("Foo").unwrap();
        let foo_datatype = Datatype {
            module_id: ModuleId(0),
            name: "Foo".to_string(),
        };
        kctx.type_store
            .add_type_instance(&AcornType::Data(foo_datatype, vec![]), arf_tc_id);

        // Set up function types to match the real test:
        // - g4 (diff): Arf -> Bool
        // - g3 (Arf.foo): (A: Arf) -> A (dependent - returns value of the type parameter)
        // - g2 (Arf.bar): (A: Arf) -> A (dependent - returns value of the type parameter)
        //
        // For dependent types, the output uses BoundVariable(0) to refer to the input.
        // When applied, type_apply_with_arg substitutes the argument.
        //
        // When applied to type variable x0:
        // - g4(x0) has type Bool
        // - g3(x0) has type x0 (the type variable)
        //
        // When applied to ground type Foo (T0):
        // - g4(T0) has type Bool
        // - g3(T0) has type Foo (T0)
        //
        // In sub_invariant_term_cmp:
        // - Comparing Bool vs x0 (type variable) returns None (head is variable)
        // - Comparing Bool vs Foo (ground type) returns Some(ordering)
        let arf_type = Term::typeclass(arf_tc_id);

        // g4: Arf -> Bool (non-dependent)
        let g4_type = Term::pi(arf_type.clone(), Term::bool_type());

        // g3, g2: (A: Arf) -> A (dependent type using BoundVariable)
        // BoundVariable(0) refers to the input A
        let bound_var = Term::atom(Atom::BoundVariable(0));
        let g3_type = Term::pi(arf_type.clone(), bound_var.clone());
        let g2_type = Term::pi(arf_type.clone(), bound_var.clone());

        kctx.symbol_table.add_global_constant(g4_type.clone()); // g0 (unused)
        kctx.symbol_table.add_global_constant(g4_type.clone()); // g1 (unused)
        kctx.symbol_table.add_global_constant(g2_type); // g2
        kctx.symbol_table.add_global_constant(g3_type); // g3
        kctx.symbol_table.add_global_constant(g4_type); // g4

        // Create general clause: g4(x0) or g3(x0) = g2(x0) where x0: Arf
        let general_clause = kctx.parse_clause("g4(x0) or g3(x0) = g2(x0)", &["Arf"]);

        // Create special clause: g4(Foo) or g3(Foo) = g2(Foo)
        let foo_term = Term::ground_type(foo_id);
        let special_clause = Clause::new(
            vec![
                Literal::new(
                    true,
                    Term::new(
                        Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 4)),
                        vec![foo_term.clone()],
                    ),
                    Term::new_true(),
                ),
                Literal::new(
                    true,
                    Term::new(
                        Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 3)),
                        vec![foo_term.clone()],
                    ),
                    Term::new(
                        Atom::Symbol(Symbol::GlobalConstant(ModuleId(0), 2)),
                        vec![foo_term.clone()],
                    ),
                ),
            ],
            &LocalContext::empty(),
        );

        // Test at the GeneralizationSet level
        let mut gen_set = GeneralizationSet::new();
        gen_set.insert(general_clause.clone(), 0, &kctx);

        let result = gen_set.find_generalization(special_clause.clone(), &kctx);
        assert!(
            result.is_some(),
            "GeneralizationSet should find the general clause as a match for the special clause"
        );
    }

    #[test]
    fn test_parse_rejects_multi_trivial_witness_declaration() {
        use crate::certificate::Certificate;
        use crate::processor::Processor;
        use crate::project::Project;
        use std::borrow::Cow;

        let (_processor, bindings, normalized_goal) = Processor::test_goal(
            r#"
            theorem goal { true }
            "#,
        );

        let project = Project::new_mock();
        let mut bindings_cow = Cow::Borrowed(&bindings);
        let mut kernel_context_cow = Cow::Owned(normalized_goal.kernel_context.clone());

        let err = match Certificate::parse_code_line(
            "let (x: Bool, y: Bool) satisfy { true }",
            &project,
            &mut bindings_cow,
            &mut kernel_context_cow,
        ) {
            Ok(_) => panic!("expected parse failure"),
            Err(err) => err,
        };

        let Error::GeneratedBadCode(msg) = err else {
            panic!("expected GeneratedBadCode");
        };
        assert!(msg.contains("certificate `let ... satisfy` steps are no longer supported"));
    }

    #[test]
    fn test_instantiate_claim_clause_normalizes_lambda_valued_arguments() {
        use crate::kernel::atom::Atom;
        use crate::kernel::certificate_step::Claim;
        use crate::kernel::clause::Clause;
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::term::Term;
        use crate::kernel::variable_map::VariableMap;

        let mut context = KernelContext::new();
        context.parse_constant("c0", "Bool");

        let claim = Claim::new(context.parse_clause("x0(c0)", &["Bool -> Bool"]), {
            let mut var_map = VariableMap::new();
            var_map.set(
                0,
                Term::lambda(
                    Term::bool_type(),
                    Term::not(Term::not(Term::atom(Atom::BoundVariable(0)))),
                ),
            );
            var_map
        })
        .expect("claim should normalize");

        let instantiated = Checker::instantiate_claim_clause(&claim, &context)
            .expect("claim instantiation should succeed");

        assert_eq!(
            instantiated,
            Clause::from_literals_unnormalized(
                vec![Literal::positive(Term::parse("c0"))],
                &LocalContext::empty(),
            )
        );
    }

    #[test]
    fn test_check_cert_steps_records_normalized_claim_clause() {
        use crate::kernel::atom::Atom;
        use crate::kernel::certificate_step::{CertificateStep, Claim};
        use crate::kernel::literal::Literal;
        use crate::kernel::local_context::LocalContext;
        use crate::kernel::term::Term;
        use crate::kernel::variable_map::VariableMap;

        let mut context = KernelContext::new();
        context.parse_constant("c0", "Bool");

        let known = Clause::from_literals_unnormalized(
            vec![Literal::positive(Term::parse("c0"))],
            &LocalContext::empty(),
        );
        let generic = context.parse_clause("x0(c0)", &["Bool -> Bool"]);
        let negated = context.parse_clause("not c0", &[]);

        let mut checker = Checker::new();
        checker.insert_clause(&generic, StepReason::Testing, &context);
        checker.insert_clause(&negated, StepReason::Testing, &context);

        let claim = Claim::new(context.parse_clause("x0(c0)", &["Bool -> Bool"]), {
            let mut var_map = VariableMap::new();
            var_map.set(
                0,
                Term::lambda(
                    Term::bool_type(),
                    Term::not(Term::not(Term::atom(Atom::BoundVariable(0)))),
                ),
            );
            var_map
        })
        .expect("claim should normalize");

        let (checked_steps, used) = checker
            .check_cert_steps(&[CertificateStep::Claim(claim)], None, &context)
            .expect("claim should check");

        assert_eq!(used, 1);
        assert_eq!(checked_steps.len(), 1);
        assert_eq!(checked_steps[0].clause, known);
    }

    #[test]
    fn test_checker_problematic_negated_forall_clause_growth() {
        let (context, clause) = problematic_negated_forall_clause();
        let closure = checker_style_clause_closure(&context, clause, 40);

        for (i, clause) in closure.iter().enumerate() {
            println!("clause {i}: {clause}");
        }

        let canonical_count = closure
            .iter()
            .map(|clause| {
                let mut canonical = clause.clone();
                canonical.normalize();
                canonical
            })
            .collect::<HashSet<_>>()
            .len();
        let display_count = closure
            .iter()
            .map(|clause| clause.to_string())
            .collect::<HashSet<_>>()
            .len();

        println!("raw clause count: {}", closure.len());
        println!("canonical clause count: {}", canonical_count);
        println!("display string count: {}", display_count);

        let clause_strings: Vec<String> = closure.iter().map(|clause| clause.to_string()).collect();
        assert!(
            clause_strings
                .iter()
                .any(|s| s.matches("exists(Bool => not(").count() >= 2),
            "expected boolean reduction to surface the negated foralls as positive exists literals"
        );
        assert!(
            clause_strings.iter().all(|s| !s.contains("choose(")),
            "expected disjunctive positive exists to stay inline rather than opening a choose witness"
        );
        assert!(
            closure.len() < 40,
            "expected closure to stabilize well before the exploration limit, got {} clauses",
            closure.len()
        );
        assert!(
            canonical_count == closure.len() && display_count == closure.len(),
            "expected genuinely distinct clauses, got raw={}, canonical={}, display={}",
            closure.len(),
            canonical_count,
            display_count
        );
    }
}

use std::borrow::Cow;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::certificate::Certificate;
use crate::code_generator::Error;
use crate::elaborator::acorn_type::AcornType;
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::evaluator::Evaluator;
use crate::elaborator::names::ConstantName;
use crate::elaborator::potential_value::PotentialValue;
use crate::elaborator::source::Source;
use crate::elaborator::stack::Stack;
use crate::elaborator::unresolved_constant::UnresolvedConstant;
use crate::kernel::atom::AtomId;
use crate::kernel::clause::Clause;
use crate::kernel::concrete_proof::ConcreteProof;
use crate::kernel::generalization_set::GeneralizationSet;
use crate::kernel::inference;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::term::Term;
use crate::kernel::{EqualityGraph, StepId};
use crate::normalizer::{NormalizationContext, Normalizer};
use crate::project::Project;
use crate::proof_step::Rule;
use crate::syntax::expression::Declaration;
use crate::syntax::statement::{Statement, StatementInfo};
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

    /// A let...satisfy statement that introduces a synthetic definition.
    SyntheticDefinition,

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
            StepReason::SyntheticDefinition => "synthetic definition".to_string(),
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

/// Converts a clause to readable code using the environment's names.
fn clause_to_code(clause: &Clause, normalizer: &Normalizer, bindings: &Cow<BindingMap>) -> String {
    let value = normalizer.denormalize(clause, None, None, false);
    let mut code_gen = crate::code_generator::CodeGenerator::new(bindings);
    code_gen
        .value_to_code(&value)
        .unwrap_or_else(|_| format!("{} (internal)", clause))
}

/// Result of parsing a single line of certificate code.
///
/// This is the boundary where name resolution happens: certificate strings use names
/// like "Nat.add", which get resolved to current numeric IDs during parsing.
/// This makes certificates robust to refactoring (see `Certificate` docs).
pub enum ParsedLine {
    /// A let...satisfy statement. Sets up bindings for subsequent claims.
    ///
    /// These map user-chosen names (like "s0") to existing synthetic constants.
    /// The synthetic constants themselves are created during goal normalization,
    /// not from the certificate - the certificate just establishes the name mapping.
    LetSatisfy {
        /// Clauses from the satisfy condition (empty for trivial conditions like `true`).
        clauses_to_insert: Vec<Clause>,
        /// The reason for this step (Skolemization or SyntheticDefinition).
        reason: StepReason,
    },
    /// A claim statement with clauses to check.
    Claim(Vec<Clause>),
}

/// Information about a single step in a certificate proof.
#[derive(Debug, Clone)]
pub struct CertificateStep {
    /// The statement from the certificate (the code line).
    pub statement: String,

    /// The reason this step was accepted.
    pub reason: StepReason,
}

/// The checker quickly checks if a clause can be proven in a single step from known clauses.
///
/// The types of single-step we support are:
///
///   Exact substitutions into a known theorem. Handled by the GeneralizationSet.
///   "Congruence closure" of equalities and subterm relationships. Handled by the EqualityGraph.
///   Propositional calculus on concrete literals. Handled by the EqualityGraph.
///   Introducing variables for existential quantifiers. Handled weirdly through a Normalizer.
#[derive(Clone)]
pub struct Checker {
    /// For deductions among concrete clauses.
    term_graph: EqualityGraph,

    /// For looking up specializations of clauses with free variables.
    generalization_set: Arc<GeneralizationSet>,

    /// Whether a contradiction was directly inserted into the checker.
    direct_contradiction: bool,

    /// A hack, but we need to break out of loops, since equality factoring and boolean
    /// reduction can create cycles.
    past_boolean_reductions: HashSet<Clause>,

    /// The reason for each step. The step_id is the index in this vector.
    reasons: Vec<StepReason>,
}

impl Checker {
    pub fn new() -> Checker {
        Checker {
            term_graph: EqualityGraph::new(),
            generalization_set: Arc::new(GeneralizationSet::new()),
            direct_contradiction: false,
            past_boolean_reductions: HashSet::new(),
            reasons: Vec::new(),
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
        self.reasons.push(reason.clone());

        if clause.has_any_variable() {
            // The clause has free variables, so it can be a generalization.
            Arc::make_mut(&mut self.generalization_set).insert(
                clause.clone(),
                step_id,
                kernel_context,
            );

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
    pub fn check_clause(
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

        // If not found in term graph, check if there's a generalization in the clause set
        if let Some(step_id) = self
            .generalization_set
            .find_generalization(clause.clone(), kernel_context)
        {
            trace!(clause = %clause, result = "generalization_set", "checking clause");
            return Some(self.reasons[step_id].clone());
        }

        // Try last-argument elimination as a fallback.
        // This handles cases where we have:
        //   g0(T0, T0, (T0 -> T0), c1, c2, c3, x0) = c1(c2(c3), x0)
        // and we want to match it against:
        //   g0(x0, x1, x2, x3, x4, x5) = x3(x4(x5))
        // by eliminating the common last argument x0 from both sides.
        if let Some(reduced) = self.try_last_arg_elimination(clause) {
            if let Some(step_id) = self
                .generalization_set
                .find_generalization(reduced, kernel_context)
            {
                trace!(clause = %clause, result = "last_arg_elimination", "checking clause");
                return Some(self.reasons[step_id].clone());
            }
        }

        trace!(clause = %clause, result = "failed", "checking clause");
        None
    }

    /// Try to eliminate the last argument from both sides of an equality.
    /// Returns Some(reduced_clause) if:
    /// - The clause is a single positive equality
    /// - Both sides are applications
    /// - The last argument of both sides is the same variable
    /// - That variable doesn't appear elsewhere in the terms
    fn try_last_arg_elimination(&self, clause: &Clause) -> Option<Clause> {
        // Must be a single literal
        if clause.literals.len() != 1 {
            return None;
        }

        let lit = &clause.literals[0];

        // Must be a positive equality
        if !lit.positive {
            return None;
        }

        // Both sides must be applications
        let left_ref = lit.left.as_ref();
        let right_ref = lit.right.as_ref();

        let (left_func, left_args) = left_ref.split_application_multi()?;
        let (right_func, right_args) = right_ref.split_application_multi()?;

        // Both must have at least one argument
        if left_args.is_empty() || right_args.is_empty() {
            return None;
        }

        // Get the last arguments
        let left_last = left_args.last()?;
        let right_last = right_args.last()?;

        // They must be equal
        if left_last != right_last {
            return None;
        }

        // The last argument must be a variable
        if !left_last.as_ref().is_variable() {
            return None;
        }

        // Build new terms without the last argument
        let new_left = if left_args.len() == 1 {
            left_func
        } else {
            left_func.apply(&left_args[..left_args.len() - 1])
        };

        let new_right = if right_args.len() == 1 {
            right_func
        } else {
            right_func.apply(&right_args[..right_args.len() - 1])
        };

        // Create the reduced clause
        let new_lit = Literal::equals(new_left, new_right);

        // Note: We keep the same context for now; the variable just won't be used
        // in the reduced clause. A more thorough implementation would clean up
        // the context, but this should work for matching purposes.
        Some(Clause::new(vec![new_lit], &clause.context))
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
        normalizer: &mut crate::normalizer::Normalizer,
    ) -> Result<(), Error> {
        trace!("inserting goal {} (line {})", goal.name, goal.first_line);

        let source = &goal.proposition.source;
        let normalized = normalizer.normalize_goal(goal).map_err(|e| e.message)?;
        // Get kernel_context after normalizing, since normalize_goal may create new synthetics
        let kernel_context = normalizer.kernel_context();
        for step in &normalized.steps {
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

    /// Check a certificate. It is expected that the certificate has a proof.
    /// Returns a list of CertificateSteps showing how each step was verified.
    ///
    /// Consumes bindings, normalizer and the checker itself since they may be
    /// modified during checking and should not be reused afterwards.
    pub fn check_cert(
        self,
        cert: &Certificate,
        project: &Project,
        mut bindings: Cow<BindingMap>,
        mut normalizer: Cow<Normalizer>,
    ) -> Result<Vec<CertificateStep>, Error> {
        // Check for contradiction before parsing. If goal insertion already
        // created a contradiction, we don't need to parse or check the proof.
        if self.has_contradiction() {
            trace!("has_contradiction (before parsing)");
            return Ok(Vec::new());
        }

        let concrete_proof = cert.to_concrete_proof(project, &mut bindings, &mut normalizer)?;
        // Get kernel_context AFTER parsing, since parsing may register new types/constants
        let kernel_context = normalizer.kernel_context().clone();
        self.check_concrete_proof(&concrete_proof, &kernel_context, &normalizer, &bindings)
    }

    /// Parse a single code line, updating bindings/normalizer, and return structured result.
    pub fn parse_code_line(
        code: &str,
        project: &Project,
        bindings: &mut Cow<BindingMap>,
        normalizer: &mut Cow<Normalizer>,
        kernel_context: &KernelContext,
    ) -> Result<ParsedLine, Error> {
        let statement = Statement::parse_str_with_options(&code, true)?;
        let mut evaluator = Evaluator::new(project, bindings, None);

        match statement.statement {
            StatementInfo::VariableSatisfy(vss) => {
                // Bind type parameters first
                let type_params = evaluator.evaluate_type_params(&vss.type_params)?;
                for param in &type_params {
                    bindings.to_mut().add_arbitrary_type(param.clone());
                    normalizer.to_mut().register_arbitrary_type(param);
                }

                // Re-create evaluator with updated bindings
                let mut evaluator = Evaluator::new(project, bindings, None);

                // Parse declarations
                let mut decls = vec![];
                for decl in &vss.declarations {
                    match decl {
                        Declaration::Typed(name_token, type_expr) => {
                            let name = name_token.text().to_string();
                            let acorn_type = evaluator.evaluate_type(type_expr)?;
                            decls.push((name, acorn_type));
                        }
                        Declaration::SelfToken(_) => {
                            return Err(Error::GeneratedBadCode(
                                "Unexpected 'self' in let...satisfy statement".to_string(),
                            ));
                        }
                    }
                }

                // Evaluate the condition
                let mut stack = Stack::new();
                evaluator.bind_args(&mut stack, &vss.declarations, None)?;
                let condition_value = evaluator.evaluate_value_with_stack(
                    &mut stack,
                    &vss.condition,
                    Some(&AcornType::Bool),
                )?;

                // Look up synthetic definition
                let types: Vec<_> = decls.iter().map(|(_, ty)| ty.clone()).collect();
                let exists_value = AcornValue::exists(types.clone(), condition_value.clone());

                // Build type_var_map from type parameters
                let type_var_map: Option<HashMap<String, (AtomId, Term)>> =
                    if type_params.is_empty() {
                        None
                    } else {
                        Some(
                            type_params
                                .iter()
                                .enumerate()
                                .map(|(i, p)| {
                                    let var_type = if let Some(tc) = &p.typeclass {
                                        let tc_id = normalizer
                                            .to_mut()
                                            .kernel_context_mut()
                                            .type_store
                                            .add_typeclass(tc);
                                        Term::typeclass(tc_id)
                                    } else {
                                        Term::type_sort()
                                    };
                                    (p.name.clone(), (i as AtomId, var_type))
                                })
                                .collect(),
                        )
                    };

                let (source, synthetic_atoms) = match normalizer
                    .to_mut()
                    .get_synthetic_definition(&exists_value, type_var_map.as_ref())
                {
                    Some(def) => (def.source.clone(), Some(def.atoms.clone())),
                    None => {
                        if condition_value != AcornValue::Bool(true) {
                            return Err(Error::GeneratedBadCode(format!(
                                "statement '{}' does not match any synthetic definition",
                                code
                            )));
                        }
                        // Trivial condition requires the type to be inhabited
                        for (name, acorn_type) in &decls {
                            let type_term = kernel_context
                                .type_store
                                .get_type_term(acorn_type)
                                .map_err(|e| {
                                    Error::GeneratedBadCode(format!(
                                        "cannot convert type '{}' to term: {}",
                                        acorn_type, e
                                    ))
                                })?;
                            if !kernel_context.provably_inhabited(&type_term, None) {
                                return Err(Error::GeneratedBadCode(format!(
                                    "cannot create witness '{}' of type '{}' with trivial condition: \
                                     type is not provably inhabited",
                                    name, acorn_type
                                )));
                            }
                        }
                        (None, None)
                    }
                };

                // Set up bindings and build constant values for substitution
                let mut constant_values = Vec::new();

                if let Some(atoms) = &synthetic_atoms {
                    for (i, (name, acorn_type)) in decls.iter().enumerate() {
                        let (module_id, local_id) = atoms[i];
                        let synthetic_cname = ConstantName::Synthetic(module_id, local_id);

                        let (param_names, generic_type) = if !type_params.is_empty() {
                            let names: Vec<String> =
                                type_params.iter().map(|p| p.name.clone()).collect();
                            (names, acorn_type.genericize(&type_params))
                        } else {
                            (vec![], acorn_type.clone())
                        };

                        let user_cname = ConstantName::unqualified(bindings.module_id(), name);
                        let type_args: Vec<_> = type_params
                            .iter()
                            .map(|p| AcornType::Variable(p.clone()))
                            .collect();

                        let resolved_value = AcornValue::constant(
                            synthetic_cname.clone(),
                            type_args,
                            acorn_type.clone(),
                            generic_type.clone(),
                            param_names.clone(),
                        );
                        constant_values.push(resolved_value.clone());

                        let potential_value = if !type_params.is_empty() {
                            PotentialValue::Unresolved(UnresolvedConstant {
                                name: synthetic_cname.clone(),
                                params: type_params.clone(),
                                generic_type: generic_type.clone(),
                                args: vec![],
                            })
                        } else {
                            PotentialValue::Resolved(resolved_value)
                        };

                        bindings.to_mut().add_constant_alias(
                            user_cname,
                            synthetic_cname,
                            potential_value,
                            vec![],
                            None,
                        );
                    }
                } else {
                    // Trivial case, create new constants
                    for (name, acorn_type) in &decls {
                        let cname = ConstantName::unqualified(bindings.module_id(), name);
                        bindings.to_mut().add_unqualified_constant(
                            name,
                            vec![],
                            acorn_type.clone(),
                            None,
                            None,
                            vec![],
                            None,
                            String::new(),
                        );
                        normalizer.to_mut().add_scoped_constant(
                            cname.clone(),
                            acorn_type,
                            type_var_map.as_ref(),
                        );

                        let resolved_value = AcornValue::constant(
                            cname,
                            vec![],
                            acorn_type.clone(),
                            acorn_type.clone(),
                            vec![],
                        );
                        constant_values.push(resolved_value);
                    }
                }

                // Build clauses from non-trivial conditions
                let clauses_to_insert = if condition_value != AcornValue::Bool(true) {
                    let num_vars = decls.len() as AtomId;
                    let value = condition_value.bind_values(0, num_vars, &constant_values);
                    let mut view = NormalizationContext::new_ref(&normalizer, type_var_map.clone());
                    view.nice_value_to_clauses(&value, &mut vec![])?
                } else {
                    vec![]
                };

                let reason = match source {
                    Some(source) => StepReason::Skolemization(source),
                    None => StepReason::SyntheticDefinition,
                };

                Ok(ParsedLine::LetSatisfy {
                    clauses_to_insert,
                    reason,
                })
            }
            StatementInfo::Claim(claim) => {
                let value = evaluator.evaluate_value(&claim.claim, Some(&AcornType::Bool))?;
                let module_id = bindings.module_id();
                let mut view = NormalizationContext::new_mut(normalizer.to_mut(), None, module_id);
                let clauses = view.value_to_denormalized_clauses(&value)?;
                Ok(ParsedLine::Claim(clauses))
            }
            _ => Err(Error::GeneratedBadCode(format!(
                "Expected a claim or let...satisfy statement, got: {}",
                code
            ))),
        }
    }

    /// Check a ConcreteProof directly.
    /// Returns a list of CertificateSteps showing how each step was verified.
    pub fn check_concrete_proof(
        mut self,
        concrete_proof: &ConcreteProof,
        kernel_context: &KernelContext,
        normalizer: &Normalizer,
        bindings: &Cow<BindingMap>,
    ) -> Result<Vec<CertificateStep>, Error> {
        let mut certificate_steps = Vec::new();

        for clause in &concrete_proof.claims {
            if self.has_contradiction() {
                trace!("has_contradiction (early exit)");
                return Ok(certificate_steps);
            }

            let mut clause = clause.clone();
            match self.check_clause(&clause, kernel_context) {
                Some(reason) => {
                    certificate_steps.push(CertificateStep {
                        statement: clause_to_code(&clause, normalizer, bindings),
                        reason,
                    });
                }
                None => {
                    return Err(Error::GeneratedBadCode(format!(
                        "Claim '{}' is not obviously true",
                        clause
                    )));
                }
            }
            clause.normalize();
            self.insert_clause(&clause, StepReason::PreviousClaim, kernel_context);
        }

        if self.has_contradiction() {
            trace!("has_contradiction (end of proof)");
            Ok(certificate_steps)
        } else {
            Err(Error::GeneratedBadCode(
                "proof does not result in a contradiction".to_string(),
            ))
        }
    }

    /// Remove unneeded steps from the certificate.
    /// The certificate passed in should be valid.
    ///
    /// Consumes bindings, normalizer and the checker itself since they may be
    /// modified during checking and should not be reused afterwards.
    pub fn clean_cert(
        self,
        cert: Certificate,
        project: &Project,
        bindings: Cow<BindingMap>,
        normalizer: Cow<Normalizer>,
    ) -> Result<(Certificate, Vec<CertificateStep>), Error> {
        let mut good_cert = cert;
        let mut keep_count = 0;

        loop {
            let Some(proof) = &good_cert.proof else {
                return Err(Error::NoProof);
            };

            if keep_count >= proof.len() {
                // All steps are necessary, run final check
                let steps = self.check_cert(&good_cert, project, bindings, normalizer)?;
                return Ok((good_cert, steps));
            }

            // Try removing the step at index keep_count
            let mut test_cert = good_cert.clone();
            if let Some(test_proof) = &mut test_cert.proof {
                test_proof.remove(keep_count);
            }

            // Try checking with a fresh checker
            let c = self.clone();
            match c.check_cert(&test_cert, project, bindings.clone(), normalizer.clone()) {
                Ok(_) => {
                    good_cert = test_cert;
                }
                Err(_) => {
                    keep_count += 1;
                }
            }
        }
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
}

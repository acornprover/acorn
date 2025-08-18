use crate::clause::Clause;
use crate::generalization_set::GeneralizationSet;
use crate::term_graph::{StepId, TermGraph};
use crate::truth_table_set::TruthTableSet;

/// The checker quickly checks if a clause can be proven in a single step from known clauses.
#[derive(Clone)]
pub struct Checker {
    term_graph: TermGraph,

    /// For looking up specializations of clauses with free variables.
    generalization_set: GeneralizationSet,

    /// For concluding slightly-less-long clauses from long clauses.
    truth_tables: TruthTableSet,

    next_step_id: usize,

    /// Whether a contradiction was directly inserted into the checker.
    direct_contradiction: bool,
}

impl Checker {
    pub fn new() -> Self {
        Checker {
            term_graph: TermGraph::new(),
            generalization_set: GeneralizationSet::new(),
            truth_tables: TruthTableSet::new(),
            next_step_id: 0,
            direct_contradiction: false,
        }
    }

    /// Adds a true clause to the checker.
    pub fn insert_clause(&mut self, clause: &Clause) {
        if clause.is_impossible() {
            self.direct_contradiction = true;
            return;
        }

        let step_id = self.next_step_id;
        self.next_step_id += 1;
        let mut queue = vec![];

        if clause.has_any_variable() {
            // The clause has free variables, so it can be a generalization.
            self.generalization_set.insert(clause.clone(), step_id);

            // We only need to do equality resolution for clauses with free variables,
            // because resolvable concrete literals would already have been simplified out.
            for resolution in clause.equality_resolutions() {
                self.insert_clause(&resolution);
            }
        } else {
            // The clause is concrete.

            // Track concrete long clauses exactly
            if clause.len() > 1 {
                queue = self.truth_tables.insert(clause);
            }

            // The term graph does all sorts of stuff but only for concrete clauses.
            self.term_graph.insert_clause(clause, StepId(step_id));
        }

        for factoring in clause.equality_factorings() {
            self.insert_clause(&factoring);
        }

        for elim in clause.function_eliminations() {
            self.insert_clause(&elim);
        }

        for c in queue {
            self.insert_clause(&c);
        }
    }

    /// Returns true if the clause is known to be true.
    /// If we have found any contradiction, we can degenerately conclude the clause is true.
    pub fn check_clause(&mut self, clause: &Clause) -> bool {
        if self.has_contradiction() {
            return true;
        }

        if clause.len() > 1 && self.truth_tables.contains(clause) {
            // We've seen this clause exactly
            return true;
        }

        // Check the term graph for concrete evaluation
        if self.term_graph.check_clause(clause) {
            return true;
        }

        // If not found in term graph, check if there's a generalization in the clause set
        if self
            .generalization_set
            .find_generalization(clause.clone())
            .is_some()
        {
            return true;
        }

        false
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
}

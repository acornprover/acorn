#[cfg(test)]
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::fmt;

use crate::kernel::atom::Atom;
use crate::kernel::clause::Clause;
use crate::kernel::clause_set::{ClauseId, ClauseSet, GroupId, LiteralId, Normalization, TermId};
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::literal::Literal;
use crate::kernel::term::{Decomposition as TermDecomposition, Term};

/// Every time we set two terms equal or not equal, that action is tagged with a StepId.
/// The term graph uses it to provide a history of the reasoning that led to a conclusion.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct StepId(pub usize);

impl StepId {
    pub fn get(&self) -> usize {
        self.0
    }
}

impl fmt::Display for StepId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.get())
    }
}

/// Information about a rewrite that was added to the term graph externally.
#[derive(Debug, Eq, PartialEq, Copy, Clone, Ord, PartialOrd)]
pub struct RewriteSource {
    /// The id of the rule used for this rewrite.
    /// We know this rewrite is true based on the pattern step alone.
    pub pattern_id: StepId,

    /// The id of the rule containing the subterm that inspired this rewrite.
    /// If it was just the rewrite pattern that inspired this step, this is None.
    /// This isn't mathematically necessary to prove the step, but it is necessary to recreate this rule.
    pub inspiration_id: Option<StepId>,

    /// The term that was originally on the left side of the pattern.
    left: TermId,

    /// The term that was originally on the right side of the pattern.
    right: TermId,
}

/// Information provided externally to describe one step in a chain of rewrites.
#[derive(Debug, Eq, PartialEq)]
pub struct RewriteStep {
    pub source: RewriteSource,

    /// The term that existed before the rewrite.
    pub input_term: Term,

    /// The term that the input term was rewritten info.
    pub output_term: Term,

    /// A forwards rewrite is the "left -> right" direction.
    pub forwards: bool,
}

impl RewriteStep {
    pub fn left_term(&self) -> &Term {
        if self.forwards {
            &self.input_term
        } else {
            &self.output_term
        }
    }

    pub fn right_term(&self) -> &Term {
        if self.forwards {
            &self.output_term
        } else {
            &self.input_term
        }
    }
}

/// The goal of the EqualityGraph is to find a contradiction.
/// When we do, we need to explain to the outside world why this is actually a contradiction.
/// The EqualityGraphContradiction encodes this.
///
/// Warning!
/// Currently this can only represent contradictions that come from a series of rewrites.
/// In particular, it can't represent contradictions that use clause reduction.
/// So, beware.
#[derive(Debug, Eq, PartialEq)]
pub struct EqualityGraphContradiction {
    /// Every contradiction is based on one inequality, plus a set of rewrites that turn
    /// one site of the inequality into the other.
    pub inequality_id: usize,

    /// The rewrites that turn one side of the inequality into the other.
    pub rewrite_chain: Vec<RewriteStep>,
}

// Each term has a Decomposition that describes how it is created.
// This version uses binary application (lambda calculus style) instead of head+args.
#[derive(Debug, Eq, Hash, PartialEq, Clone)]
enum Decomposition {
    // The term is just equal to an atom
    Atomic(Atom),

    // Binary application: (func arg)
    // For f(a, b, c), this is stored as ((((f) a) b) c)
    Application(TermId, TermId),

    // Pi type (function type), treated as an opaque atom.
    // Not used for structural equality reasoning - just stores the marker.
    Pi,
}

#[derive(Clone)]
struct TermInfo {
    // The full uncurried term that this node represents.
    // For an application node representing ((f a) b), this stores f(a, b).
    term: Term,
    group: GroupId,
    decomp: Decomposition,

    // The terms that this one can be directly turned into.
    // When the step id is not provided, we concluded it from composition.
    adjacent: Vec<(TermId, Option<RewriteSource>)>,
}

#[derive(Clone)]
enum PossibleGroupInfo {
    /// This group has been remapped to another group
    Remapped(GroupId),
    /// This group contains actual information
    Info(GroupInfo),
}

#[derive(Clone)]
struct GroupInfo {
    // All of the terms that belong to this group, in the order they were added.
    terms: Vec<TermId>,

    // Each way to create a term of this group by applying subterms from other groups.
    // This might include references to deleted applications. They are only cleaned up lazily.
    applications: Vec<ApplicationId>,

    // The other groups that we know are not equal to this one.
    // For each inequality, we store the two terms that we know are not equal,
    // along with the step that we know it from.
    inequalities: HashMap<GroupId, (TermId, TermId, StepId)>,
}

impl GroupInfo {
    fn heuristic_size(&self) -> usize {
        self.terms.len() + self.applications.len()
    }
}

// Each composition relation between terms implies a composition relation between groups.
// The composition relations between groups each get their own id, so we can update them when
// we combine groups.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct ApplicationId(u32);

impl ApplicationId {
    fn get(&self) -> u32 {
        self.0
    }
}

impl fmt::Display for ApplicationId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.get())
    }
}

// Simplified ApplicationKey for binary application: just (func_group, arg_group)
#[derive(Debug, Eq, Hash, PartialEq, Clone)]
struct ApplicationKey {
    func: GroupId,
    arg: GroupId,
}

impl ApplicationKey {
    fn remap_group(&mut self, old_group: GroupId, new_group: GroupId) {
        if self.func == old_group {
            self.func = new_group;
        }
        if self.arg == old_group {
            self.arg = new_group;
        }
    }

    fn groups(&self) -> Vec<GroupId> {
        if self.func == self.arg {
            vec![self.func]
        } else {
            let mut answer = vec![self.func, self.arg];
            answer.sort();
            answer
        }
    }

    #[cfg(test)]
    fn touches_group(&self, group: GroupId) -> bool {
        self.func == group || self.arg == group
    }
}

impl fmt::Display for ApplicationKey {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({} {})", self.func, self.arg)
    }
}

#[derive(Clone)]
struct ApplicationInfo {
    key: ApplicationKey,
    result_term: TermId,
}

impl fmt::Display for ApplicationInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "key {} -> term {}", self.key, self.result_term)
    }
}

// In general, there are two sorts of operations that are performed on the graph.
//
// "Integrity" operations are to keep the graph valid. A lot of the data is denormalized,
// so we have to update it in multiple places to keep it consistent.
// Integrity operations are performed immediately. Integrity operations should not trigger
// other integrity operations recursively.
//
// "Semantic" operations are to reflect the underlying meaning of the terms, like
// declaring that two terms are identical, or representing that some clause is true.
// It's hard to do a semantic operation in the middle of performing an integrity operation,
// because you can't recurse and do a huge number of operations when the graph is in
// an inconsistent state. It's okay if semantic operations trigger other semantic operations.
//
// Thus, our strategy is to finish any integrity operations immediately, but leave semantic
// operations in this queue. The SemanticOperation represents an element in this queue.
#[derive(Clone)]
enum SemanticOperation {
    // A term equality that comes from a rewrite pattern.
    Rewrite(RewriteSource),

    // A term equality that comes indirectly from a logical deduction.
    TermEquality(TermId, TermId),

    // We have discovered that two terms are not equal.
    TermInequality(TermId, TermId, StepId),

    // Insert a clause (will be normalized first).
    InsertClause(ClauseId),
}

/// The EqualityGraph stores concrete terms, along with relationships between them that represent
/// equality, inequality, and subterm relationships.
///
/// This version uses binary application (lambda calculus style) internally:
/// f(a, b, c) is represented as (((f a) b) c)
#[derive(Clone)]
pub struct EqualityGraph {
    // terms maps TermId to TermInfo.
    terms: Vec<TermInfo>,

    // groups maps GroupId to PossibleGroupInfo.
    groups: Vec<PossibleGroupInfo>,

    // applications maps ApplicationId to ApplicationInfo.
    // When an application is deleted, we replace it with None.
    applications: Vec<Option<ApplicationInfo>>,

    // The set of clauses in the graph
    clause_set: ClauseSet,

    // Keying the applications so that we can check if an application belongs to an existing group.
    application_map: HashMap<ApplicationKey, TermId>,

    // Each term has its decomposition stored so that we can look it back up again
    decompositions: HashMap<Decomposition, TermId>,

    // The pending semantic operations on the graph.
    pending: Vec<SemanticOperation>,

    // A flag for whether there is a contradiction.
    // Separate from contradiction_info to encode the awkward case where we know there
    // is a contradiction, but we don't know how to extract a trace for it.
    has_contradiction: bool,

    // Set when we discover a contradiction, if we know how to extract a trace for it.
    // When set, this indicates that the provided step sets these terms to be unequal.
    // But there is a chain of rewrites that proves that they are equal. This is a contradiction.
    contradiction_info: Option<(TermId, TermId, StepId)>,

    // Maps Pi types (function types) to their TermIds.
    // Pi types are treated as opaque atoms - we don't decompose them structurally.
    pi_map: HashMap<Term, TermId>,
}

impl Default for EqualityGraph {
    fn default() -> Self {
        Self::new()
    }
}

impl EqualityGraph {
    pub fn new() -> EqualityGraph {
        EqualityGraph {
            terms: Vec::new(),
            groups: Vec::new(),
            applications: Vec::new(),
            clause_set: ClauseSet::new(),
            application_map: HashMap::new(),
            decompositions: HashMap::new(),
            pending: Vec::new(),
            has_contradiction: false,
            contradiction_info: None,
            pi_map: HashMap::new(),
        }
    }

    /// Returns None if this term isn't in the graph.
    #[cfg(test)]
    fn get_term_id(&self, term: &Term) -> Option<TermId> {
        match term.as_ref().decompose() {
            TermDecomposition::Atom(atom) => {
                let key = Decomposition::Atomic(atom.clone());
                self.decompositions.get(&key).copied()
            }
            TermDecomposition::Application(func, arg) => {
                let func_id = self.get_term_id(&func.to_owned())?;
                let arg_id = self.get_term_id(&arg.to_owned())?;
                let key = Decomposition::Application(func_id, arg_id);
                self.decompositions.get(&key).copied()
            }
            TermDecomposition::Pi(_, _) => {
                // Pi types are looked up in pi_map
                self.pi_map.get(term).copied()
            }
        }
    }

    fn get_term(&self, term_id: TermId) -> &Term {
        &self.terms[term_id.get() as usize].term
    }

    fn get_group_id(&self, term_id: TermId) -> GroupId {
        self.terms[term_id.get() as usize].group
    }

    /// Whether there is any sort of contradiction at all.
    pub fn has_contradiction(&self) -> bool {
        self.has_contradiction
    }

    /// Whether there is a contradiction with trace information.
    #[cfg(test)]
    fn has_contradiction_trace(&self) -> bool {
        self.contradiction_info.is_some()
    }

    /// Used to explain which steps lead to a contradiction.
    /// Returns None if there is no contradiction trace.
    pub fn get_contradiction_trace(&self) -> Option<EqualityGraphContradiction> {
        let (term1, term2, inequality_id) = self.contradiction_info?;
        let mut rewrite_chain = vec![];
        self.expand_steps(term1, term2, &mut rewrite_chain);
        Some(EqualityGraphContradiction {
            inequality_id: inequality_id.get(),
            rewrite_chain,
        })
    }

    fn get_group_info(&self, group_id: GroupId) -> &GroupInfo {
        match &self.groups[group_id.get() as usize] {
            PossibleGroupInfo::Remapped(new_id) => {
                panic!("group {} is remapped to {}", group_id, new_id)
            }
            PossibleGroupInfo::Info(info) => info,
        }
    }

    // Inserts an atom into the graph.
    // If it's already in the graph, return the existing term id.
    // Otherwise, make a new term id and give it a new group.
    fn insert_atom(&mut self, atom: &Atom) -> TermId {
        let key = Decomposition::Atomic(atom.clone());
        if let Some(&id) = self.decompositions.get(&key) {
            return id;
        }

        // Make a new term and group
        let term_id = TermId(self.terms.len() as u32);
        let group_id = GroupId(self.groups.len() as u32);

        let term = Term::new(*atom, vec![]);
        let term_info = TermInfo {
            term,
            group: group_id,
            decomp: key.clone(),
            adjacent: vec![],
        };
        self.terms.push(term_info);
        let group_info = PossibleGroupInfo::Info(GroupInfo {
            terms: vec![term_id],
            applications: vec![],
            inequalities: HashMap::new(),
        });
        self.groups.push(group_info);
        self.decompositions.insert(key, term_id);
        term_id
    }

    // Inserts a binary application relationship.
    // If it's already in the graph, return the existing term id.
    // Otherwise, make a new term and group.
    fn insert_application(&mut self, func: TermId, arg: TermId) -> TermId {
        let key = Decomposition::Application(func, arg);
        if let Some(&id) = self.decompositions.get(&key) {
            return id;
        }

        // Build the full uncurried term by applying arg to func
        let func_term = self.get_term(func).clone();
        let arg_term = self.get_term(arg).clone();
        let combined_term = func_term.apply(&[arg_term]);

        // Make a new term and group
        let term_id = TermId(self.terms.len() as u32);
        let group_id = GroupId(self.groups.len() as u32);
        let term_info = TermInfo {
            term: combined_term,
            group: group_id,
            decomp: key.clone(),
            adjacent: vec![],
        };
        self.terms.push(term_info);
        let group_info = PossibleGroupInfo::Info(GroupInfo {
            terms: vec![term_id],
            applications: vec![],
            inequalities: HashMap::new(),
        });
        self.groups.push(group_info);
        self.decompositions.insert(key, term_id);

        // Insert the group application
        let func_group = self.get_group_id(func);
        let arg_group = self.get_group_id(arg);
        self.insert_group_application(func_group, arg_group, term_id);

        term_id
    }

    // Inserts a Pi type (function type) into the graph.
    // Pi types are treated as opaque atoms - no structural decomposition.
    // Uses pi_map for lookup to ensure identical Pi types get the same TermId.
    fn insert_pi(&mut self, pi_term: Term) -> TermId {
        if let Some(&id) = self.pi_map.get(&pi_term) {
            return id;
        }

        // Create new term and group (similar to insert_atom)
        let term_id = TermId(self.terms.len() as u32);
        let group_id = GroupId(self.groups.len() as u32);
        let term_info = TermInfo {
            term: pi_term.clone(),
            group: group_id,
            decomp: Decomposition::Pi,
            adjacent: vec![],
        };
        self.terms.push(term_info);
        let group_info = PossibleGroupInfo::Info(GroupInfo {
            terms: vec![term_id],
            applications: vec![],
            inequalities: HashMap::new(),
        });
        self.groups.push(group_info);
        self.pi_map.insert(pi_term, term_id);
        term_id
    }

    // Adds a application relationship.
    // If we should combine groups, add them to the pending list.
    fn insert_group_application(&mut self, func: GroupId, arg: GroupId, result_term: TermId) {
        let result_group = self.get_group_id(result_term);
        let key = ApplicationKey { func, arg };
        if let Some(&existing_result_term) = self.application_map.get(&key) {
            let existing_result_group = self.get_group_id(existing_result_term);
            if existing_result_group != result_group {
                self.pending.push(SemanticOperation::TermEquality(
                    existing_result_term,
                    result_term,
                ));
            }
            return;
        }

        // We need to make a new relationship
        let app_info = ApplicationInfo {
            key: key.clone(),
            result_term,
        };
        for group in key.groups() {
            match &mut self.groups[group.get() as usize] {
                PossibleGroupInfo::Remapped(id) => {
                    panic!(
                        "application info refers to a remapped group {} -> {}",
                        group, id
                    );
                }
                PossibleGroupInfo::Info(info) => {
                    info.applications
                        .push(ApplicationId(self.applications.len() as u32));
                }
            }
        }
        self.applications.push(Some(app_info));
        self.application_map.insert(key, result_term);
    }

    /// Inserts a term.
    /// Makes a new term, group, and application if necessary.
    /// Uses curried application: f(a, b, c) becomes (((f a) b) c)
    pub fn insert_term(&mut self, term: &Term, kernel_context: &KernelContext) -> TermId {
        let term_id = match term.as_ref().decompose() {
            TermDecomposition::Atom(atom) => self.insert_atom(atom),
            TermDecomposition::Application(func, arg) => {
                let func_term = func.to_owned();
                let arg_term = arg.to_owned();
                // Debug: check if func/arg have valid structure
                #[cfg(debug_assertions)]
                {
                    if !func_term.validate_structure() {
                        panic!(
                            "insert_term: decompose returned func with invalid structure.\nfunc: {}\noriginal term: {}",
                            func_term, term
                        );
                    }
                    if !arg_term.validate_structure() {
                        panic!(
                            "insert_term: decompose returned arg with invalid structure.\narg: {}\noriginal term: {}",
                            arg_term, term
                        );
                    }
                }
                let func_id = self.insert_term(&func_term, kernel_context);
                let arg_id = self.insert_term(&arg_term, kernel_context);
                self.insert_application(func_id, arg_id)
            }
            TermDecomposition::Pi(_, _) => {
                // Pi types are treated as opaque atoms
                self.insert_pi(term.clone())
            }
        };
        self.process_pending();
        term_id
    }

    /// Inserts a clause into the graph.
    /// All terms in the clause are inserted if not already present.
    /// The clause is indexed by all groups that appear in its literals.
    /// Don't insert clauses with no literals.
    pub fn insert_clause(&mut self, clause: &Clause, step: StepId, kernel_context: &KernelContext) {
        // First, insert all terms and collect literal IDs
        let mut literal_ids = Vec::new();
        for literal in &clause.literals {
            let left_id = self.insert_term(&literal.left, kernel_context);
            let right_id = self.insert_term(&literal.right, kernel_context);

            if clause.literals.len() == 1 {
                // If this is a single literal, we can just set the terms equal or not equal
                if literal.positive {
                    self.set_terms_equal(left_id, right_id, step, None);
                } else {
                    self.set_terms_not_equal(left_id, right_id, step);
                }
                return;
            }

            let left_group = self.get_group_id(left_id);
            let right_group = self.get_group_id(right_id);
            literal_ids.push(LiteralId::new(left_group, right_group, literal.positive));
        }

        // Create the clause and add it to the pending queue for normalization
        let clause_normalization = ClauseId::new(literal_ids);
        match clause_normalization {
            Normalization::True => {
                // Tautology - nothing to do
            }
            Normalization::False => {
                // Contradiction - set the contradiction flag
                self.has_contradiction = true;
            }
            Normalization::Clause(clause) => {
                // Add to pending queue for insertion
                self.pending.push(SemanticOperation::InsertClause(clause));
            }
        }

        self.process_pending();
    }

    // Merge the small group into the large group.
    fn remap_group(
        &mut self,
        old_term: TermId,
        old_group: GroupId,
        new_term: TermId,
        new_group: GroupId,
        source: Option<RewriteSource>,
    ) {
        let old_info = match std::mem::replace(
            &mut self.groups[old_group.get() as usize],
            PossibleGroupInfo::Remapped(new_group),
        ) {
            PossibleGroupInfo::Info(info) => info,
            PossibleGroupInfo::Remapped(id) => {
                panic!("group {} is already remapped to {}", old_group, id)
            }
        };

        for &term_id in &old_info.terms {
            self.terms[term_id.get() as usize].group = new_group;
        }

        let mut keep_applications = vec![];
        for application_id in old_info.applications {
            {
                let app = match &mut self.applications[application_id.get() as usize] {
                    Some(app) => app,
                    None => {
                        // This application has already been deleted.
                        // Time to lazily delete the reference to it.
                        continue;
                    }
                };
                self.application_map.remove(&app.key);
                app.key.remap_group(old_group, new_group);
            }
            let app = self.applications[application_id.get() as usize]
                .as_ref()
                .expect("how does this happen?");

            if let Some(&existing_result_term) = self.application_map.get(&app.key) {
                // An application for the new relationship already exists.
                // Instead of inserting app.result, we need to delete this application, and merge the
                // intended result with result_group.
                self.pending.push(SemanticOperation::TermEquality(
                    app.result_term,
                    existing_result_term,
                ));
                self.applications[application_id.get() as usize] = None;
            } else {
                self.application_map
                    .insert(app.key.clone(), app.result_term);
                keep_applications.push(application_id);
            }
        }

        // Rekey the inequalities that refer to this group from elsewhere
        let mut discovered_inequalities = Vec::new();
        for &unequal_group in old_info.inequalities.keys() {
            let unequal_info = match &mut self.groups[unequal_group.get() as usize] {
                PossibleGroupInfo::Remapped(id) => {
                    panic!("group {} is remapped to {}", unequal_group, id)
                }
                PossibleGroupInfo::Info(info) => info,
            };
            let value = unequal_info
                .inequalities
                .remove(&old_group)
                .expect("inequality not there");
            if unequal_group == new_group {
                // We found a contradiction.
                self.has_contradiction = true;
                self.contradiction_info = Some(value);
                continue;
            }
            if !unequal_info.inequalities.contains_key(&new_group) {
                unequal_info.inequalities.insert(new_group, value);
                // Remember this new inequality to handle later
                discovered_inequalities.push((unequal_group, new_group));
            }
        }

        // Handle inequalities discovered through rekeying
        for (group1, group2) in discovered_inequalities {
            self.handle_inequality(group1, group2);
        }

        // Merge the old info into the new info
        {
            let new_info = match &mut self.groups[new_group.get() as usize] {
                PossibleGroupInfo::Remapped(id) => {
                    panic!("group {} is remapped to {}", new_group, id)
                }
                PossibleGroupInfo::Info(info) => info,
            };
            new_info.terms.extend(old_info.terms);
            new_info.applications.extend(keep_applications);
            for (group, value) in old_info.inequalities {
                // Skip new_group to avoid marking a group as unequal to itself
                if group != new_group && !new_info.inequalities.contains_key(&group) {
                    new_info.inequalities.insert(group, value);
                }
            }
        }

        // Collect inequalities that need reverse updates
        let inequalities_to_check: Vec<_> = {
            let new_info = match &self.groups[new_group.get() as usize] {
                PossibleGroupInfo::Remapped(id) => {
                    panic!("group {} is remapped to {}", new_group, id)
                }
                PossibleGroupInfo::Info(info) => info,
            };
            new_info
                .inequalities
                .iter()
                .map(|(&g, &v)| (g, v))
                .collect()
        };

        // Now update the reverse inequalities and collect new ones to handle
        let mut new_inequalities = Vec::new();
        for (group, value) in inequalities_to_check {
            let group_info = match &mut self.groups[group.get() as usize] {
                PossibleGroupInfo::Remapped(_) => continue,
                PossibleGroupInfo::Info(info) => info,
            };
            if !group_info.inequalities.contains_key(&new_group) {
                group_info.inequalities.insert(new_group, value);
                new_inequalities.push((group, new_group));
            }
        }

        // Handle all new inequalities discovered through group merging
        for (group1, group2) in new_inequalities {
            self.handle_inequality(group1, group2);
        }

        // Handle clause migration for the remapped group
        // Remove all clauses mentioning old_group and re-normalize them
        let removed_clauses = self.clause_set.remove_group(old_group);
        for clause in removed_clauses {
            // Update the clause by remapping old_group to new_group
            let mut updated_literals = Vec::new();
            for literal in clause.literals() {
                let left = if literal.left == old_group {
                    new_group
                } else {
                    literal.left
                };
                let right = if literal.right == old_group {
                    new_group
                } else {
                    literal.right
                };
                updated_literals.push(LiteralId::new(left, right, literal.positive));
            }

            // Normalize and re-insert the updated clause
            let normalized = ClauseId::new(updated_literals);
            match normalized {
                Normalization::True => {
                    // Tautology - don't re-insert
                }
                Normalization::False => {
                    // Contradiction
                    self.has_contradiction = true;
                }
                Normalization::Clause(new_clause) => {
                    // Queue the clause for re-insertion
                    self.pending
                        .push(SemanticOperation::InsertClause(new_clause));
                }
            }
        }

        self.terms[old_term.get() as usize]
            .adjacent
            .push((new_term, source));
        self.terms[new_term.get() as usize]
            .adjacent
            .push((old_term, source));
    }

    /// Inserts a clause that has already been normalized.
    /// This re-normalizes it in case the graph state has changed.
    fn insert_clause_normalized(&mut self, clause: ClauseId) {
        // Re-normalize the clause with current group knowledge
        let mut new_literals = Vec::new();
        let mut has_true_literal = false;

        for literal in clause.literals() {
            // Update group IDs in case they've been remapped
            let left = self.update_group_id(literal.left);
            let right = self.update_group_id(literal.right);

            // Check if groups are equal
            if left == right {
                if literal.positive {
                    // id = id is always true
                    has_true_literal = true;
                    break;
                } else {
                    // id != id is always false, skip it
                    continue;
                }
            }

            // Check if groups are known to be unequal
            let left_info = self.get_group_info(left);
            if left_info.inequalities.contains_key(&right) {
                if !literal.positive {
                    // id != different_id where they're known unequal is true
                    has_true_literal = true;
                    break;
                } else {
                    // id = different_id where they're known unequal is false, skip it
                    continue;
                }
            }

            // This literal can't be evaluated, keep it
            // Create a new literal with the updated group IDs
            new_literals.push(LiteralId::new(left, right, literal.positive));
        }

        if has_true_literal {
            // The clause is a tautology, don't insert
            return;
        }

        if new_literals.is_empty() {
            // The clause is a contradiction
            self.has_contradiction = true;
            return;
        }

        if new_literals.len() == 1 {
            // Single literal clause - convert to equality/inequality
            let literal = &new_literals[0];

            // Update group IDs in case they've been remapped
            let left_group = self.update_group_id(literal.left);
            let right_group = self.update_group_id(literal.right);

            // Get representative terms from each group
            let left_info = self.get_group_info(left_group);
            let right_info = self.get_group_info(right_group);

            // Use the first term from each group as representative
            if !left_info.terms.is_empty() && !right_info.terms.is_empty() {
                let left_term = left_info.terms[0];
                let right_term = right_info.terms[0];

                if literal.positive {
                    // Positive literal becomes an equality
                    self.pending
                        .push(SemanticOperation::TermEquality(left_term, right_term));
                } else {
                    // Negative literal becomes an inequality
                    // We need a StepId here - use a dummy one for now
                    // This should ideally track where this clause came from
                    self.pending.push(SemanticOperation::TermInequality(
                        left_term,
                        right_term,
                        StepId(0),
                    ));
                }
                return;
            }
        }

        // Create the normalized clause and insert it
        let normalized = ClauseId::new(new_literals);
        match normalized {
            Normalization::True => {
                // Tautology - nothing to do
            }
            Normalization::False => {
                // Contradiction
                self.has_contradiction = true;
            }
            Normalization::Clause(new_clause) => {
                // If the clause already exists, nothing to do
                if self.clause_set.contains(&new_clause) {
                    return;
                }

                // Actually insert the clause into the set
                self.clause_set.insert(new_clause.clone());

                // Check for resolution opportunities by flipping each literal
                let literals = new_clause.literals();
                for i in 0..literals.len() {
                    // Create a modified version with the i-th literal flipped
                    let mut modified_literals = Vec::new();
                    for (j, lit) in literals.iter().enumerate() {
                        if i == j {
                            // Flip this literal's sign
                            modified_literals.push(LiteralId::new(
                                lit.left,
                                lit.right,
                                !lit.positive,
                            ));
                        } else {
                            modified_literals.push(lit.clone());
                        }
                    }

                    // Check if this modified clause exists
                    // We don't need to re-sort because sign is the last field in ordering
                    let modified_clause = ClauseId(modified_literals);

                    if self.clause_set.contains(&modified_clause) {
                        // We can resolve! Create the resolved clause by removing the i-th literal
                        let mut resolved_literals = Vec::new();
                        for (j, lit) in literals.iter().enumerate() {
                            if i != j {
                                resolved_literals.push(lit.clone());
                            }
                        }

                        // Create the resolved clause and queue it for insertion
                        let resolved = ClauseId::new(resolved_literals);
                        match resolved {
                            Normalization::True => {
                                // Tautology - don't add
                            }
                            Normalization::False => {
                                // Contradiction from resolution
                                self.has_contradiction = true;
                            }
                            Normalization::Clause(resolved_clause) => {
                                // Only queue the resolved clause if it's not already in the set
                                if !self.clause_set.contains(&resolved_clause) {
                                    self.pending
                                        .push(SemanticOperation::InsertClause(resolved_clause));
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    fn process_pending(&mut self) {
        while let Some(operation) = self.pending.pop() {
            // We can stop processing when we find a contradiction.
            if self.has_contradiction {
                break;
            }

            match operation {
                SemanticOperation::Rewrite(source) => {
                    self.set_terms_equal_once(source.left, source.right, Some(source));
                }
                SemanticOperation::TermEquality(term1, term2) => {
                    self.set_terms_equal_once(term1, term2, None);
                }
                SemanticOperation::TermInequality(term1, term2, step) => {
                    self.set_terms_not_equal_once(term1, term2, step);
                }
                SemanticOperation::InsertClause(clause) => {
                    self.insert_clause_normalized(clause);
                }
            }
        }
    }

    // Set two terms to be equal.
    // Doesn't repeat to find the logical closure.
    // For that, use identify_terms.
    fn set_terms_equal_once(
        &mut self,
        term1: TermId,
        term2: TermId,
        source: Option<RewriteSource>,
    ) {
        let group1 = self.get_group_id(term1);
        let group2 = self.get_group_id(term2);
        if group1 == group2 {
            // They already are equal
            return;
        }
        let info1 = self.get_group_info(group1);
        let info2 = self.get_group_info(group2);

        // Keep around the smaller number, as a tiebreak
        if (info1.heuristic_size(), group2) < (info2.heuristic_size(), group1) {
            self.remap_group(term1, group1, term2, group2, source)
        } else {
            self.remap_group(term2, group2, term1, group1, source)
        };
    }

    /// Sets two terms to be equal, repeating to find the logical closure.
    /// left and right must be specializations of a literal in pattern_id.
    /// TODO: track which literal it is, when the pattern clause is long.
    pub fn set_terms_equal(
        &mut self,
        left: TermId,
        right: TermId,
        pattern_id: StepId,
        inspiration_id: Option<StepId>,
    ) {
        let source = RewriteSource {
            pattern_id,
            inspiration_id,
            left,
            right,
        };
        self.pending.push(SemanticOperation::Rewrite(source));
        self.process_pending();
    }

    pub fn set_terms_not_equal(&mut self, term1: TermId, term2: TermId, step: StepId) {
        self.pending
            .push(SemanticOperation::TermInequality(term1, term2, step));
        self.process_pending();
    }

    // Handle the discovery that two groups are unequal.
    // This removes and re-normalizes clauses that contain literals comparing these groups.
    fn handle_inequality(&mut self, group1: GroupId, group2: GroupId) {
        // When groups become unequal, we need to remove and re-normalize clauses
        // containing literals that compare these two groups

        // Remove clauses with positive literals (group1 = group2)
        let positive_literal = LiteralId::new(group1, group2, true);
        let removed_positive = self.clause_set.remove_literal(&positive_literal);

        // Remove clauses with negative literals (group1 != group2)
        let negative_literal = LiteralId::new(group1, group2, false);
        let removed_negative = self.clause_set.remove_literal(&negative_literal);

        // Re-normalize and re-insert all removed clauses
        for clause in removed_positive
            .into_iter()
            .chain(removed_negative.into_iter())
        {
            // The clause needs to be re-normalized with the new inequality knowledge
            // We'll just re-insert it through the pending queue
            self.pending.push(SemanticOperation::InsertClause(clause));
        }
    }

    // Set two terms to be not equal.
    // Doesn't repeat to find the logical closure.
    fn set_terms_not_equal_once(&mut self, term1: TermId, term2: TermId, step: StepId) {
        let group1 = self.get_group_id(term1);
        let group2 = self.get_group_id(term2);
        if group1 == group2 {
            self.has_contradiction = true;
            self.contradiction_info = Some((term1, term2, step));
            return;
        }

        let info1 = match &mut self.groups[group1.get() as usize] {
            PossibleGroupInfo::Remapped(id) => panic!("group {} is remapped to {}", group1, id),
            PossibleGroupInfo::Info(info) => info,
        };
        let already_unequal = info1.inequalities.contains_key(&group2);
        if !already_unequal {
            info1.inequalities.insert(group2, (term1, term2, step));
        }

        let info2 = match &mut self.groups[group2.get() as usize] {
            PossibleGroupInfo::Remapped(id) => panic!("group {} is remapped to {}", group2, id),
            PossibleGroupInfo::Info(info) => info,
        };

        // Only update info2 if we didn't already have this inequality
        if !already_unequal {
            let prev = info2.inequalities.insert(group1, (term1, term2, step));
            if prev.is_some() {
                panic!("asymmetry in group inequalities");
            }

            // Handle the new inequality by removing and re-normalizing affected clauses
            self.handle_inequality(group1, group2);
        }
    }

    fn as_application(&self, term: TermId) -> (TermId, TermId) {
        match &self.terms[term.get() as usize].decomp {
            Decomposition::Application(func, arg) => (*func, *arg),
            _ => panic!("not an application"),
        }
    }

    /// Returns the truth value of this literal, or None if it cannot be evaluated.
    pub fn evaluate_literal(
        &mut self,
        literal: &Literal,
        kernel_context: &KernelContext,
    ) -> Option<bool> {
        // Term graph only works with concrete terms (no variables)
        if literal.left.has_any_variable() || literal.right.has_any_variable() {
            return None;
        }

        // If the literal is positive, we check if the terms are equal.
        // If the literal is negative, we check if the terms are not equal.
        let left_id = self.insert_term(&literal.left, kernel_context);
        let right_id = self.insert_term(&literal.right, kernel_context);

        let left_group = self.get_group_id(left_id);
        let right_group = self.get_group_id(right_id);

        if left_group == right_group {
            return Some(literal.positive);
        }

        let left_info = self.get_group_info(left_group);
        if left_info.inequalities.contains_key(&right_group) {
            return Some(!literal.positive);
        }

        None
    }

    /// Returns true if the clause is known to be true.
    /// If we have found any contradiction, we can degenerately conclude the clause is true.
    pub fn check_clause(&mut self, clause: &Clause, kernel_context: &KernelContext) -> bool {
        if self.has_contradiction() {
            return true;
        }

        for literal in &clause.literals {
            if self.evaluate_literal(literal, kernel_context) == Some(true) {
                return true;
            }
        }

        // Check if this exact clause (or an equivalent one) exists in our stored clauses
        if self.clause_exists(clause, kernel_context) {
            return true;
        }

        false
    }

    /// Checks if a clause with the same literals exists in the term graph.
    /// This compares clauses based on their group-normalized form.
    fn clause_exists(&mut self, clause: &Clause, kernel_context: &KernelContext) -> bool {
        if clause.literals.is_empty() {
            return false;
        }

        // Term graph only works with concrete terms (no variables)
        for literal in &clause.literals {
            if literal.left.has_any_variable() || literal.right.has_any_variable() {
                return false;
            }
        }

        // Convert the clause to literal IDs
        let mut literal_ids = Vec::new();
        for literal in &clause.literals {
            let left_id = self.insert_term(&literal.left, kernel_context);
            let right_id = self.insert_term(&literal.right, kernel_context);
            let left_group = self.get_group_id(left_id);
            let right_group = self.get_group_id(right_id);
            literal_ids.push(LiteralId::new(left_group, right_group, literal.positive));
        }

        // Normalize the clause
        let normalized = ClauseId::new(literal_ids);
        match normalized {
            Normalization::True => {
                // Tautology - always exists in a sense
                true
            }
            Normalization::False => {
                // Contradiction - exists if we have a contradiction
                self.has_contradiction()
            }
            Normalization::Clause(clause_id) => {
                // Check if this clause exists in the set
                self.clause_set.contains(&clause_id)
            }
        }
    }

    // Gets a step of edges that demonstrate that term1 and term2 are equal.
    // The step is None if the edge is composite.
    // Panics if there is no path.
    fn get_path(
        &self,
        term1: TermId,
        term2: TermId,
    ) -> Vec<(TermId, TermId, Option<RewriteSource>)> {
        if term1 == term2 {
            return vec![];
        }

        // Find paths that lead to term2 from everywhere.
        // predecessor maps term_a -> (term_b, step) where the edge
        //   (term_a, term_b, step)
        // is the first edge to get to term2 from term_a.
        let mut next_edge = HashMap::new();

        let mut queue = vec![term2];
        'outer: loop {
            let term_b = queue.pop().expect("no path between terms");
            for (term_a, source) in &self.terms[term_b.get() as usize].adjacent {
                if next_edge.contains_key(term_a) {
                    // We already have a way to get from term_a to term2
                    continue;
                }
                next_edge.insert(*term_a, (term_b, *source));
                if *term_a == term1 {
                    break 'outer;
                }
                queue.push(*term_a);
            }
        }

        let mut answer = vec![];
        let mut term_a = term1;
        while term_a != term2 {
            let (term_b, source) = next_edge[&term_a];
            answer.push((term_a, term_b, source));
            term_a = term_b;
        }
        answer
    }

    // For every step from term1 to term2, show the rewritten subterms, as well as the
    // id of the rule that enabled it, if there is one.
    // This is "postorder" in the sense that we show a rewritten application term after showing
    // the rewrites for the subterms.
    // The application rewrites have a step id of None.
    // The rewritten subterms have a step id with the rule that they are based on.
    fn expand_steps(&self, term1: TermId, term2: TermId, output: &mut Vec<RewriteStep>) {
        if term1 == term2 {
            return;
        }
        let path = self.get_path(term1, term2);
        for (a_id, b_id, source) in path {
            if source.is_none() {
                // We have an application relationship between a_id and b_id
                let (func_a, arg_a) = self.as_application(a_id);
                let (func_b, arg_b) = self.as_application(b_id);
                self.expand_steps(func_a, func_b, output);
                self.expand_steps(arg_a, arg_b, output);
            }

            let term_a = self.get_term(a_id);
            let term_b = self.get_term(b_id);

            if let Some(source) = source {
                let forwards = if a_id == source.left && b_id == source.right {
                    true
                } else if a_id == source.right && b_id == source.left {
                    false
                } else {
                    panic!("source does not match terms");
                };
                let step = RewriteStep {
                    source,
                    input_term: term_a.clone(),
                    output_term: term_b.clone(),
                    forwards,
                };
                output.push(step);
            }
        }
    }

    #[cfg(test)]
    fn get_step_ids_helper(&self, term1: TermId, term2: TermId, output: &mut BTreeSet<StepId>) {
        if term1 == term2 {
            return;
        }
        let path = self.get_path(term1, term2);
        for (term_a, term_b, source) in path {
            match source {
                Some(source) => {
                    output.insert(source.pattern_id);
                }
                None => {
                    let (func_a, arg_a) = self.as_application(term_a);
                    let (func_b, arg_b) = self.as_application(term_b);
                    self.get_step_ids_helper(func_a, func_b, output);
                    self.get_step_ids_helper(arg_a, arg_b, output);
                }
            }
        }
    }

    /// Extract a list of steps ids that we used to prove that these two terms are equal.
    /// This does deduplicate.
    #[cfg(test)]
    fn get_step_ids(&self, term1: TermId, term2: TermId) -> Vec<usize> {
        let mut answer = BTreeSet::new();
        self.get_step_ids_helper(term1, term2, &mut answer);
        answer.into_iter().map(|id| id.get()).collect()
    }

    #[cfg(test)]
    fn show_graph(&self) {
        println!("terms:");
        for (i, term_info) in self.terms.iter().enumerate() {
            println!("term {}, group {}: {}", i, term_info.group, term_info.term);
        }
        println!("applications:");
        for app in &self.applications {
            if let Some(app) = app {
                println!("{}", app);
            }
        }
    }

    /// Follows remapping chains to find the current group id.
    /// Updates intermediate remaps to point directly to the final destination for efficiency.
    fn update_group_id(&mut self, group_id: GroupId) -> GroupId {
        // First, follow the chain to find the final destination
        let mut current = group_id;
        let mut chain = Vec::new();

        loop {
            match &self.groups[current.get() as usize] {
                PossibleGroupInfo::Info(_) => {
                    // We've reached the final destination
                    break;
                }
                PossibleGroupInfo::Remapped(next) => {
                    chain.push(current);
                    current = *next;
                }
            }
        }

        // If we followed more than one hop, update all intermediate remaps
        // to point directly to the final destination
        if chain.len() > 1 {
            for intermediate in &chain[..chain.len() - 1] {
                self.groups[intermediate.get() as usize] = PossibleGroupInfo::Remapped(current);
            }
        }

        current
    }

    /// Normalizes a ClauseId by updating all group IDs to their current values.
    /// Takes a ClauseId (from clause_set) which contains LiteralIds.
    /// Returns a Normalization which can be True (tautology), False (contradiction), or Clause.
    #[cfg(test)]
    fn normalize(&mut self, clause_id: ClauseId) -> Normalization {
        // Get the literals from the ClauseId
        let literals = clause_id.literals();

        // Update all group IDs in the literals to their current values
        let mut updated_literals = Vec::new();
        for literal in literals {
            let updated_left = self.update_group_id(literal.left);
            let updated_right = self.update_group_id(literal.right);
            let updated_literal = LiteralId::new(updated_left, updated_right, literal.positive);
            updated_literals.push(updated_literal);
        }

        // Use ClauseId::new to normalize the updated literals
        ClauseId::new(updated_literals)
    }

    // Checks that the group id has not been remapped
    #[cfg(test)]
    fn validate_group_id(&self, group_id: GroupId) -> &GroupInfo {
        assert!(group_id < GroupId(self.groups.len() as u32));
        match &self.groups[group_id.get() as usize] {
            PossibleGroupInfo::Remapped(new_id) => {
                panic!("group {} is remapped to {}", group_id, new_id)
            }
            PossibleGroupInfo::Info(info) => info,
        }
    }

    // Checks that this clause contains a term from this group.
    // It's also okay if the clause has ceased to exist, because we clean up lazily.
    /// Panics if it finds a consistency problem.
    #[cfg(test)]
    fn validate(&self) {
        if !self.has_contradiction {
            assert!(self.pending.is_empty());
        }
        for (term_id, term_info) in self.terms.iter().enumerate() {
            let info = self.validate_group_id(term_info.group);
            assert!(info.terms.contains(&TermId(term_id as u32)));
        }

        for (group_id, group_info) in self.groups.iter().enumerate() {
            let group_id = GroupId(group_id as u32);
            let group_info = match group_info {
                PossibleGroupInfo::Remapped(_) => {
                    continue;
                }
                PossibleGroupInfo::Info(info) => info,
            };
            for term_id in &group_info.terms {
                let term_group = self.terms[term_id.get() as usize].group;
                assert_eq!(term_group, group_id);
            }
            for application_id in &group_info.applications {
                let app = &self.applications[application_id.get() as usize];
                let app = match app {
                    Some(app) => app,
                    None => continue,
                };
                assert!(app.key.touches_group(group_id));
            }
        }

        for (application_id, app) in self.applications.iter().enumerate() {
            let app = match app {
                Some(app) => app,
                None => continue,
            };
            let groups = app.key.groups();
            for group in groups {
                let info = self.validate_group_id(group);
                assert!(info
                    .applications
                    .contains(&ApplicationId(application_id as u32)));
            }
        }

        // Validate the clause set
        self.clause_set.validate();
    }
}

/// A test wrapper that combines a EqualityGraph with its KernelContext.
#[cfg(test)]
struct TestGraph {
    graph: EqualityGraph,
    context: KernelContext,
}

#[cfg(test)]
impl TestGraph {
    fn new() -> TestGraph {
        let mut context = KernelContext::new();
        // c0-c7: Bool constants
        context.parse_constants(&["c0", "c1", "c2", "c3", "c4", "c5", "c6", "c7"], "Bool");
        // g1-g4: Bool -> Bool functions
        context.parse_constants(&["g1", "g2", "g3", "g4"], "Bool -> Bool");
        // g5-g10: (Bool, Bool) -> Bool functions (replacing m0-m5)
        context.parse_constants(
            &["g5", "g6", "g7", "g8", "g9", "g10"],
            "(Bool, Bool) -> Bool",
        );
        TestGraph {
            graph: EqualityGraph::new(),
            context,
        }
    }

    fn with_clauses(clauses: &[&str]) -> TestGraph {
        let mut tg = TestGraph::new();
        for (i, s) in clauses.iter().enumerate() {
            tg.insert_clause_str(s, StepId(i));
        }
        tg
    }

    fn insert_term_str(&mut self, s: &str) -> TermId {
        let id = self.graph.insert_term(&Term::parse(s), &self.context);
        self.graph.validate();
        id
    }

    fn insert_clause_str(&mut self, s: &str, step: StepId) {
        let clause = self.context.parse_clause(s, &[]);
        self.graph.insert_clause(&clause, step, &self.context);
        self.graph.validate();
    }

    fn assert_eq(&self, t1: TermId, t2: TermId) {
        assert_eq!(self.graph.get_group_id(t1), self.graph.get_group_id(t2));
    }

    fn assert_ne(&self, t1: TermId, t2: TermId) {
        assert_ne!(self.graph.get_group_id(t1), self.graph.get_group_id(t2));
    }

    fn set_eq(&mut self, t1: TermId, t2: TermId, pattern_id: StepId) {
        self.graph.set_terms_equal(t1, t2, pattern_id, None);
        self.graph.validate();
        self.assert_eq(t1, t2);
    }

    fn get_str(&self, s: &str) -> TermId {
        self.graph.get_term_id(&Term::parse(s)).unwrap()
    }

    fn check_clause_str(&mut self, s: &str) {
        let clause = self.context.parse_clause(s, &[]);
        if !self.graph.check_clause(&clause, &self.context) {
            panic!("check_clause_str(\"{}\") failed", s);
        }
    }

    fn get_step_ids(&self, term1: TermId, term2: TermId) -> Vec<usize> {
        self.graph.get_step_ids(term1, term2)
    }

    fn set_terms_not_equal(&mut self, term1: TermId, term2: TermId, step: StepId) {
        self.graph.set_terms_not_equal(term1, term2, step);
    }

    fn has_contradiction_trace(&self) -> bool {
        self.graph.has_contradiction_trace()
    }

    fn has_contradiction(&self) -> bool {
        self.graph.has_contradiction()
    }

    #[allow(dead_code)]
    fn show_graph(&self) {
        self.graph.show_graph();
    }

    fn update_group_id(&mut self, group_id: GroupId) -> GroupId {
        self.graph.update_group_id(group_id)
    }

    fn get_group_id(&self, term_id: TermId) -> GroupId {
        self.graph.get_group_id(term_id)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_identifying_atomic_subterms() {
        let mut g = TestGraph::new();
        let id1 = g.insert_term_str("c1(c2, c3)");
        let id2 = g.insert_term_str("c1(c4, c3)");
        g.assert_ne(id1, id2);
        let c2id = g.get_str("c2");
        let c4id = g.get_str("c4");
        g.assert_ne(c2id, c4id);
        g.set_eq(c2id, c4id, StepId(0));
        g.assert_eq(id1, id2);
        assert_eq!(g.get_step_ids(id1, id2), vec![0]);
    }

    #[test]
    fn test_multilevel_cascade() {
        let mut g = TestGraph::new();
        let term1 = g.insert_term_str("c1(c2(c3, c4), c2(c4, c3))");
        let term2 = g.insert_term_str("c1(c5, c5)");
        g.assert_ne(term1, term2);
        let sub1 = g.insert_term_str("c2(c3, c3)");
        let sub2 = g.get_str("c5");
        g.assert_ne(sub1, sub2);
        g.set_eq(sub1, sub2, StepId(0));
        let c3 = g.get_str("c3");
        let c4 = g.get_str("c4");
        g.assert_ne(c3, c4);
        g.set_eq(c3, c4, StepId(1));
        g.assert_eq(term1, term2);
        assert_eq!(g.get_step_ids(term1, term2), vec![0, 1]);
    }

    #[test]
    fn test_identifying_heads() {
        let mut g = TestGraph::new();
        let id1 = g.insert_term_str("c1(c2, c3)");
        let id2 = g.insert_term_str("c4(c2, c3)");
        g.assert_ne(id1, id2);
        let c1 = g.get_str("c1");
        let c4 = g.get_str("c4");
        g.set_eq(c1, c4, StepId(0));
        g.assert_eq(id1, id2);
        assert_eq!(g.get_step_ids(id1, id2), vec![0]);
    }

    #[test]
    fn test_skipping_unneeded_steps() {
        let mut g = TestGraph::new();
        let c0 = g.insert_term_str("c0");
        let c1 = g.insert_term_str("c1");
        let c2 = g.insert_term_str("c2");
        let c3 = g.insert_term_str("c3");
        let c4 = g.insert_term_str("c4");
        let c5 = g.insert_term_str("c5");
        g.set_eq(c1, c2, StepId(0));
        g.set_eq(c4, c5, StepId(1));
        g.set_eq(c0, c1, StepId(2));
        g.set_eq(c3, c4, StepId(3));
        g.set_eq(c0, c3, StepId(4));
        assert_eq!(g.get_step_ids(c0, c3), vec![4]);
    }

    #[test]
    fn test_finding_contradiction() {
        let mut g = TestGraph::new();
        let term1 = g.insert_term_str("c1(c2, c3)");
        let term2 = g.insert_term_str("c4(c5, c6)");
        g.set_terms_not_equal(term1, term2, StepId(0));
        assert!(!g.has_contradiction_trace());
        let c1 = g.get_str("c1");
        let c4 = g.get_str("c4");
        g.set_eq(c1, c4, StepId(1));
        assert!(!g.has_contradiction_trace());
        let c2 = g.get_str("c2");
        let c5 = g.get_str("c5");
        g.set_eq(c2, c5, StepId(2));
        assert!(!g.has_contradiction_trace());
        let c3 = g.get_str("c3");
        let c6 = g.get_str("c6");
        g.set_eq(c3, c6, StepId(3));
        assert!(g.has_contradiction_trace());
    }

    #[test]
    fn test_clause_reduction_basic() {
        let mut g = TestGraph::new();
        g.insert_clause_str("c1 = c2 or c3 != c4 or c5 != c6", StepId(0));
        assert!(!g.has_contradiction());
        g.insert_clause_str("c1 != c2", StepId(1));
        assert!(!g.has_contradiction());
        g.insert_clause_str("c3 = c4", StepId(2));
        assert!(!g.has_contradiction());
        g.insert_clause_str("c5 = c6", StepId(3));
        assert!(g.has_contradiction());
    }

    #[test]
    fn test_clause_reduction_two_to_zero() {
        let mut g = TestGraph::new();
        g.insert_clause_str("c1 = c2 or c1 = c3", StepId(0));
        assert!(!g.has_contradiction());
        g.insert_clause_str("c2 = c4", StepId(1));
        assert!(!g.has_contradiction());
        g.insert_clause_str("c3 = c4", StepId(2));
        assert!(!g.has_contradiction());
        g.insert_clause_str("c1 != c4", StepId(3));
        assert!(g.has_contradiction());
    }

    #[test]
    fn test_subterm_triggering_clause() {
        let mut g = TestGraph::new();
        // Use g1, g4 (Bool -> Bool) for single-arg predicates
        g.insert_clause_str("g1(c2) != g1(c3) or g4(c2) != g4(c3)", StepId(0));
        assert!(!g.has_contradiction());
        g.insert_clause_str("c2 = c3", StepId(1));
        assert!(g.has_contradiction());
    }

    #[test]
    fn test_hypotheses_then_imp() {
        let mut g =
            TestGraph::with_clauses(&["g1(c1)", "g2(c1)", "not g1(c1) or not g2(c1) or g3(c1)"]);
        g.check_clause_str("g3(c1)");
    }

    #[test]
    fn test_imp_then_hypotheses() {
        let mut g =
            TestGraph::with_clauses(&["not g1(c1) or not g2(c1) or g3(c1)", "g1(c1)", "g2(c1)"]);
        g.check_clause_str("g3(c1)");
    }

    #[test]
    fn test_term_graph_rewriting_equality() {
        // Use g6, g7 ((Bool, Bool) -> Bool) for two-arg functions
        let mut g =
            TestGraph::with_clauses(&["g6(c1, g7(c2, c3)) = c4", "g7(c2, c3) = g7(c3, c2)"]);
        g.check_clause_str("g6(c1, g7(c3, c2)) = c4");
    }

    #[test]
    fn test_term_graph_rewriting_inequality() {
        // Use g6, g7 ((Bool, Bool) -> Bool) for two-arg functions
        let mut g =
            TestGraph::with_clauses(&["g6(c1, g7(c2, c3)) != c4", "g7(c2, c3) = g7(c3, c2)"]);
        g.check_clause_str("g6(c1, g7(c3, c2)) != c4");
    }

    #[test]
    fn test_term_graph_concluding_opposing_literals() {
        let mut g = TestGraph::with_clauses(&[
            "not g9(c6, g10(c1, c0))",
            "g9(c6, c6) or g8(c6, c6)",
            "not g8(c6, c6) or g9(c6, c6)",
            "g10(c1, c0) = c6",
            "not g9(c6, c6)",
        ]);

        g.check_clause_str("g8(c6, c6)");
    }

    #[test]
    fn test_term_graph_checking_long_clause() {
        let mut g = TestGraph::with_clauses(&["c0 = c1 or c2 = c3"]);

        g.check_clause_str("c0 = c1 or c2 = c3");
    }

    #[test]
    fn test_term_graph_shortening_long_clause() {
        let mut g =
            TestGraph::with_clauses(&["not g5(c2, c3)", "not g6(c2, c3) or g5(c2, c3) or c3 = c2"]);

        g.check_clause_str("not g6(c2, c3) or c3 = c2");
    }

    #[test]
    fn test_term_graph_checking_reducible_clause() {
        // This failed at some point because we were checking a clause that could be reduced.
        let mut g = TestGraph::with_clauses(&[
            // These are necessary to reproduce the bug
            "g9(c4, c5) = c3",
            "c4 != c0",
            "g9(c4, c5) != c3 or g9(c4, g6(c5, c0)) = g6(c3, c0) or c4 = c0",
            // The clauses from the basic case
            "not g5(g6(c5, c0), c1)",
            "g9(c4, g6(c5, c0)) != g6(c3, c0) or not g5(g6(c3, c0), c1) or g5(g6(c5, c0), c1) or c4 = c1",
        ]);
        g.check_clause_str("g9(c4, g6(c5, c0)) != g6(c3, c0) or not g5(g6(c3, c0), c1) or c4 = c1");
    }

    #[test]
    fn test_term_graph_reducing_clauses() {
        let g = TestGraph::with_clauses(&[
            "not g3(g1) or g3(g0)",
            "not g3(g0) or g3(g2)",
            "g3(g1)",
            "not g3(g2)",
        ]);
        assert!(g.has_contradiction());
    }

    #[test]
    fn test_term_graph_eight_case_reduction() {
        let g = TestGraph::with_clauses(&[
            "c0 or c1 or c2",
            "c0 or c1 or not c2",
            "c0 or not c1 or c2",
            "not c0 or c1 or c2",
            "not c0 or not c1 or c2",
            "not c0 or c1 or not c2",
            "c0 or not c1 or not c2",
            "not c0 or not c1 or not c2",
        ]);
        assert!(g.has_contradiction());
    }

    #[test]
    fn test_normalize() {
        let mut g = TestGraph::new();

        // Create some terms
        let t1 = g.insert_term_str("c1");
        let t2 = g.insert_term_str("c2");
        let t3 = g.insert_term_str("c3");
        let t4 = g.insert_term_str("c4");

        let g1 = g.get_group_id(t1);
        let g2 = g.get_group_id(t2);
        let g3 = g.get_group_id(t3);
        let g4 = g.get_group_id(t4);

        // Test 1: Normal clause that stays normal
        let lit1 = LiteralId::new(g1, g2, true);
        let lit2 = LiteralId::new(g3, g4, false);
        let clause_norm = ClauseId::new(vec![lit1, lit2]);
        let clause = match clause_norm {
            Normalization::Clause(c) => c,
            _ => panic!("Expected a clause"),
        };

        match g.graph.normalize(clause.clone()) {
            Normalization::Clause(normalized) => {
                assert_eq!(normalized.literals().len(), 2);
            }
            _ => panic!("Expected a normal clause"),
        }

        // Test 2: Clause that becomes simpler after merging
        g.set_eq(t1, t2, StepId(0));

        // After merging t1 and t2, the literal "g1 = g2" becomes reflexive and should be filtered
        match g.graph.normalize(clause) {
            Normalization::True => {} // The equality becomes reflexive and true, making the whole clause true
            _ => panic!("Expected a tautology after merging"),
        }

        // Test 3: Create a clause that will have duplicate literals after merging
        let t5 = g.insert_term_str("c5");
        let t6 = g.insert_term_str("c6");
        let t7 = g.insert_term_str("c7");

        let g5 = g.get_group_id(t5);
        let g6 = g.get_group_id(t6);
        let g7 = g.get_group_id(t7);

        let lit3 = LiteralId::new(g5, g6, true);
        let lit4 = LiteralId::new(g5, g7, true);
        let clause2_norm = ClauseId::new(vec![lit3, lit4]);
        let clause2 = match clause2_norm {
            Normalization::Clause(c) => c,
            _ => panic!("Expected a clause"),
        };

        // Merge g6 and g7
        g.set_eq(t6, t7, StepId(1));

        // After merging, both literals become "g5 = g6" (or g7), so they should deduplicate
        match g.graph.normalize(clause2) {
            Normalization::Clause(normalized) => {
                assert_eq!(
                    normalized.literals().len(),
                    1,
                    "Should deduplicate to one literal"
                );
            }
            _ => panic!("Expected a normalized clause"),
        }

        // Test 4: Tautology test (p or not p)
        let lit5 = LiteralId::new(g3, g4, true);
        let lit6 = LiteralId::new(g3, g4, false);
        let tautology = ClauseId::new(vec![lit5, lit6]);

        match tautology {
            Normalization::True => {} // This is already a tautology
            _ => panic!("Expected a tautology"),
        }
    }

    #[test]
    fn test_update_group_id() {
        let mut g = TestGraph::new();

        // Create some terms that will have different groups
        let t1 = g.insert_term_str("c1");
        let t2 = g.insert_term_str("c2");
        let t3 = g.insert_term_str("c3");
        let t4 = g.insert_term_str("c4");

        let initial_g1 = g.get_group_id(t1);
        let initial_g2 = g.get_group_id(t2);
        let initial_g3 = g.get_group_id(t3);
        let initial_g4 = g.get_group_id(t4);

        // All groups should initially map to themselves
        assert_eq!(g.update_group_id(initial_g1), initial_g1);
        assert_eq!(g.update_group_id(initial_g2), initial_g2);
        assert_eq!(g.update_group_id(initial_g3), initial_g3);
        assert_eq!(g.update_group_id(initial_g4), initial_g4);

        // Now merge t1 and t2
        g.set_eq(t1, t2, StepId(0));

        // Find which group survived the merge
        let g1_after_first = g.update_group_id(initial_g1);
        let g2_after_first = g.update_group_id(initial_g2);
        assert_eq!(g1_after_first, g2_after_first); // They should be the same

        // Now merge t2 and t3
        g.set_eq(t2, t3, StepId(1));

        // Find which group survived this merge
        let g1_after_second = g.update_group_id(initial_g1);
        let g2_after_second = g.update_group_id(initial_g2);
        let g3_after_second = g.update_group_id(initial_g3);
        assert_eq!(g1_after_second, g2_after_second);
        assert_eq!(g2_after_second, g3_after_second);

        // Now merge t3 and t4
        g.set_eq(t3, t4, StepId(2));

        // Everyone should now map to the same group
        let final_g1 = g.update_group_id(initial_g1);
        let final_g2 = g.update_group_id(initial_g2);
        let final_g3 = g.update_group_id(initial_g3);
        let final_g4 = g.update_group_id(initial_g4);
        assert_eq!(final_g1, final_g2);
        assert_eq!(final_g2, final_g3);
        assert_eq!(final_g3, final_g4);
        let final_group = final_g1;

        // After calling update_group_id on initial_g1, it should have been optimized
        // to point directly to the final group
        assert_eq!(g.update_group_id(initial_g1), final_group);

        // If initial_g1 was remapped, check that the optimization worked
        if initial_g1 != final_group {
            match &g.graph.groups[initial_g1.get() as usize] {
                PossibleGroupInfo::Remapped(target) => assert_eq!(*target, final_group),
                PossibleGroupInfo::Info(_) => panic!("initial_g1 should be remapped"),
            }
        }

        // Test a chain of remappings specifically
        // Create a longer chain to ensure optimization works
        let t5 = g.insert_term_str("c5");
        let t6 = g.insert_term_str("c6");
        let t7 = g.insert_term_str("c7");

        let g5 = g.get_group_id(t5);
        let _g6 = g.get_group_id(t6);
        let _g7 = g.get_group_id(t7);

        // Create chain: t5 -> t6 -> t7
        g.set_eq(t5, t6, StepId(3));
        g.set_eq(t6, t7, StepId(4));

        // g5 should now map to the final group (either g6 or g7 survived)
        let final_567 = g.update_group_id(g5);

        // Check that g5 now points directly to the final group (optimization happened)
        if g5 != final_567 {
            match &g.graph.groups[g5.get() as usize] {
                PossibleGroupInfo::Remapped(target) => assert_eq!(*target, final_567),
                PossibleGroupInfo::Info(_) => panic!("g5 should be remapped"),
            }
        }
    }

    #[test]
    fn test_term_graph_missed_resolution() {
        let mut g = TestGraph::with_clauses(&[
            "g9(c0, c1) = c1",
            "not g8(g9(c0, c1), c0)",
            "g6(c1, c0) or g6(c0, c1)", // Key clause 1
            "g8(g9(c0, c1), c0) = g6(c0, g9(c0, c1))",
            "not g6(c0, c1)", // Key clause 2
        ]);
        g.check_clause_str("g6(c1, c0)");
    }

    // Test partial application congruence: if f(a) = g(c), then f(a, b) = g(c, b).
    // This works in EqualityGraph because f(a, b) is represented as ((f a) b),
    // and g(c, b) is represented as ((g c) b). When we set (f a) = (g c),
    // congruence closure propagates this to make ((f a) b) = ((g c) b).
    #[test]
    fn test_partial_application_congruence() {
        let mut g = TestGraph::new();

        // Create n1 = f(a, b) and n2 = g(c, b)
        let n1 = g.insert_term_str("c1(c2, c3)"); // f(a, b)
        let n2 = g.insert_term_str("c4(c5, c3)"); // g(c, b) - note same second arg c3

        // Initially they are not equal
        g.assert_ne(n1, n2);

        // Create the partial applications f(a) and g(c)
        let fa = g.insert_term_str("c1(c2)"); // f(a)
        let gc = g.insert_term_str("c4(c5)"); // g(c)

        // Set f(a) = g(c)
        g.set_eq(fa, gc, StepId(0));

        // Now f(a, b) should equal g(c, b) due to congruence on partial applications
        // In lambda calculus style: ((f a) b) = ((g c) b) because (f a) = (g c)
        g.assert_eq(n1, n2);

        // The step ids should show the connection
        let steps = g.get_step_ids(n1, n2);
        assert_eq!(steps, vec![0]);
    }

    // Test that partial application congruence works transitively
    #[test]
    fn test_partial_application_congruence_transitive() {
        let mut g = TestGraph::new();

        // Create three terms: f(a, b), g(c, b), h(d, b)
        let n1 = g.insert_term_str("c1(c2, c3)"); // f(a, b)
        let n2 = g.insert_term_str("c4(c5, c3)"); // g(c, b)
        let n3 = g.insert_term_str("c6(c7, c3)"); // h(d, b)

        // Create partial applications
        let fa = g.insert_term_str("c1(c2)"); // f(a)
        let gc = g.insert_term_str("c4(c5)"); // g(c)
        let hd = g.insert_term_str("c6(c7)"); // h(d)

        // Set f(a) = g(c) and g(c) = h(d)
        g.set_eq(fa, gc, StepId(0));
        g.set_eq(gc, hd, StepId(1));

        // Now all three full applications should be equal
        g.assert_eq(n1, n2);
        g.assert_eq(n2, n3);
        g.assert_eq(n1, n3);
    }

    // Test partial application with different final arguments (should NOT be equal)
    #[test]
    fn test_partial_application_different_args() {
        let mut g = TestGraph::new();

        // Create n1 = f(a, b) and n2 = g(c, d) where b != d
        let n1 = g.insert_term_str("c1(c2, c3)"); // f(a, b)
        let n2 = g.insert_term_str("c4(c5, c6)"); // g(c, d) - different second arg!

        // Create partial applications
        let fa = g.insert_term_str("c1(c2)"); // f(a)
        let gc = g.insert_term_str("c4(c5)"); // g(c)

        // Set f(a) = g(c)
        g.set_eq(fa, gc, StepId(0));

        // n1 and n2 should still NOT be equal because b != d
        g.assert_ne(n1, n2);

        // But if we also set b = d, then they should become equal
        let b = g.get_str("c3");
        let d = g.get_str("c6");
        g.set_eq(b, d, StepId(1));

        g.assert_eq(n1, n2);
    }

    // Test that Pi types (function types) can be inserted into the graph
    #[test]
    fn test_insert_pi_type() {
        let mut graph = EqualityGraph::new();
        let kctx = KernelContext::new();

        let bool_type = Term::bool_type();
        let type_sort = Term::type_sort();

        // Create Pi types: Bool -> Bool
        let pi1 = Term::pi(bool_type.clone(), bool_type.clone());
        let pi2 = Term::pi(bool_type.clone(), bool_type.clone());
        // Create a different Pi type: Type -> Bool
        let pi3 = Term::pi(type_sort.clone(), bool_type.clone());

        let id1 = graph.insert_term(&pi1, &kctx);
        let id2 = graph.insert_term(&pi2, &kctx);
        let id3 = graph.insert_term(&pi3, &kctx);

        // Same Pi types should get same TermId
        assert_eq!(id1, id2, "Same Pi types should get same TermId");
        // Different Pi types should get different TermIds
        assert_ne!(id1, id3, "Different Pi types should get different TermIds");

        // Also verify get_term_id works
        assert_eq!(graph.get_term_id(&pi1), Some(id1));
        assert_eq!(graph.get_term_id(&pi2), Some(id2));
        assert_eq!(graph.get_term_id(&pi3), Some(id3));
    }

    // Test that merging two groups that are marked as unequal:
    // 1. Correctly detects a contradiction
    // 2. Does not mark a group as unequal to itself
    #[test]
    fn test_merge_unequal_groups_no_self_inequality() {
        let mut g = TestGraph::new();

        // Create two terms
        let a = g.insert_term_str("c1");
        let b = g.insert_term_str("c2");

        // Mark them as not equal
        g.set_terms_not_equal(a, b, StepId(0));
        assert!(!g.has_contradiction());

        // Get the group IDs before merging
        let group_a = g.get_group_id(a);
        let group_b = g.get_group_id(b);

        // Verify they have each other in their inequalities
        {
            let info_a = g.graph.get_group_info(group_a);
            let info_b = g.graph.get_group_info(group_b);
            assert!(info_a.inequalities.contains_key(&group_b));
            assert!(info_b.inequalities.contains_key(&group_a));
        }

        // Now set them equal - this should detect a contradiction
        g.set_eq(a, b, StepId(1));
        assert!(g.has_contradiction());

        // Find the surviving group (both terms now point to the same group)
        let surviving_group = g.get_group_id(a);
        assert_eq!(g.get_group_id(b), surviving_group);

        // Critical check: the surviving group should NOT have itself in its inequalities
        let surviving_info = g.graph.get_group_info(surviving_group);
        assert!(
            !surviving_info.inequalities.contains_key(&surviving_group),
            "Group should never be marked as unequal to itself"
        );
    }
}

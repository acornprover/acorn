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

    // Opaque term marker for terms not structurally decomposed by the e-graph.
    // Currently includes Pi types and Lambda values.
    Opaque,
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
// "Integrity" operations are to keep the graph valid. A lot of the data is duplicated,
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

    // Maps opaque terms to their TermIds.
    // Opaque terms are treated as atoms - we don't decompose them structurally.
    opaque_map: HashMap<Term, TermId>,
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
            opaque_map: HashMap::new(),
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
                // Pi types are treated as opaque terms
                self.opaque_map.get(term).copied()
            }
            TermDecomposition::Lambda(_, _) => {
                // Lambda terms are currently treated as opaque terms.
                self.opaque_map.get(term).copied()
            }
            TermDecomposition::ForAll(_, _) => {
                // Quantified formulas are currently treated as opaque terms.
                self.opaque_map.get(term).copied()
            }
            TermDecomposition::Exists(_, _) => {
                // Quantified formulas are currently treated as opaque terms.
                self.opaque_map.get(term).copied()
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

    // Inserts an opaque term into the graph.
    // Opaque terms are treated as atoms - no structural decomposition.
    // Uses opaque_map for lookup to ensure identical opaque terms get the same TermId.
    fn insert_opaque_term(&mut self, opaque_term: Term) -> TermId {
        if let Some(&id) = self.opaque_map.get(&opaque_term) {
            return id;
        }

        // Create new term and group (similar to insert_atom)
        let term_id = TermId(self.terms.len() as u32);
        let group_id = GroupId(self.groups.len() as u32);
        let term_info = TermInfo {
            term: opaque_term.clone(),
            group: group_id,
            decomp: Decomposition::Opaque,
            adjacent: vec![],
        };
        self.terms.push(term_info);
        let group_info = PossibleGroupInfo::Info(GroupInfo {
            terms: vec![term_id],
            applications: vec![],
            inequalities: HashMap::new(),
        });
        self.groups.push(group_info);
        self.opaque_map.insert(opaque_term, term_id);
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
                self.insert_opaque_term(term.clone())
            }
            TermDecomposition::Lambda(_, _) => {
                // Lambda terms are currently treated as opaque atoms.
                self.insert_opaque_term(term.clone())
            }
            TermDecomposition::ForAll(_, _) => {
                // Quantified formulas are currently treated as opaque atoms.
                self.insert_opaque_term(term.clone())
            }
            TermDecomposition::Exists(_, _) => {
                // Quantified formulas are currently treated as opaque atoms.
                self.insert_opaque_term(term.clone())
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

#[cfg(test)]
mod tests;

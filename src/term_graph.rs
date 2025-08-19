use std::collections::{BTreeSet, HashMap};
use std::fmt;
use std::hash::Hash;

use crate::atom::Atom;
use crate::clause::Clause;
use crate::clause_set::{ClauseId, ClauseSet, GroupId, LiteralId, Normalization, TermId};
use crate::literal::Literal;
use crate::term::Term;

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

/// The goal of the TermGraph is to find a contradiction.
/// When we do, we need to explain to the outside world why this is actually a contradiction.
/// The TermGraphContradiction encodes this.
///
/// Warning!
/// Currently this can only represent contradictions that come from a series of rewrites.
/// In particular, it can't represent contradictions that use clause reduction.
/// So, beware.
#[derive(Debug, Eq, PartialEq)]
pub struct TermGraphContradiction {
    /// Every contradiction is based on one inequality, plus a set of rewrites that turn
    /// one site of the inequality into the other.
    pub inequality_id: usize,

    /// The rewrites that turn one side of the inequality into the other.
    pub rewrite_chain: Vec<RewriteStep>,
}

// Each term has a Decomposition that describes how it is created.
#[derive(Debug, Eq, Hash, PartialEq, Clone)]
enum Decomposition {
    // The term is just equal to an atom
    Atomic(Atom),

    // Head and args
    Compound(TermId, Vec<TermId>),
}

#[derive(Clone)]
struct TermInfo {
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

    // Each way to create a term of this group by composing subterms from other groups.
    // This might include references to deleted compounds. They are only cleaned up lazily.
    compounds: Vec<CompoundId>,

    // The other groups that we know are not equal to this one.
    // For each inequality, we store the two terms that we know are not equal,
    // along with the step that we know it from.
    inequalities: HashMap<GroupId, (TermId, TermId, StepId)>,
}

impl GroupInfo {
    fn heuristic_size(&self) -> usize {
        self.terms.len() + self.compounds.len()
    }
}

// Each composition relation between terms implies a composition relation between groups.
// The composition relations between groups each get their own id, so we can update them when
// we combine groups.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct CompoundId(u32);

impl CompoundId {
    fn get(&self) -> u32 {
        self.0
    }
}

impl fmt::Display for CompoundId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.get())
    }
}

#[derive(Debug, Eq, Hash, PartialEq, Clone)]
struct CompoundKey {
    head: GroupId,
    args: Vec<GroupId>,
}

impl CompoundKey {
    fn remap_group(&mut self, small_group: GroupId, large_group: GroupId) {
        if self.head == small_group {
            self.head = large_group;
        }
        for arg in &mut self.args {
            if *arg == small_group {
                *arg = large_group;
            }
        }
    }

    fn groups(&self) -> Vec<GroupId> {
        let mut answer = vec![self.head];
        answer.extend(self.args.iter().copied());
        answer.sort();
        answer.dedup();
        answer
    }

    fn touches_group(&self, group: GroupId) -> bool {
        if self.head == group {
            return true;
        }
        self.args.contains(&group)
    }
}

impl fmt::Display for CompoundKey {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.head)?;
        if !self.args.is_empty() {
            write!(f, "(")?;
            for (i, arg) in self.args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", arg)?;
            }
            write!(f, ")")?;
        }
        Ok(())
    }
}

#[derive(Clone)]
struct CompoundInfo {
    key: CompoundKey,
    result_term: TermId,
}

impl fmt::Display for CompoundInfo {
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

/// The TermGraph stores concrete terms, along with relationships between them that represent
/// equality, inequality, and subterm relationships.
#[derive(Clone)]
pub struct TermGraph {
    // terms maps TermId to TermInfo.
    terms: Vec<TermInfo>,

    // groups maps GroupId to PossibleGroupInfo.
    groups: Vec<PossibleGroupInfo>,

    // compounds maps CompoundId to CompoundInfo.
    // When a compound is deleted, we replace it with None.
    compounds: Vec<Option<CompoundInfo>>,

    // The set of clauses in the graph
    clause_set: ClauseSet,

    // Keying the compounds so that we can check if a composition belongs to an existing group.
    compound_map: HashMap<CompoundKey, TermId>,

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
}

impl TermGraph {
    pub fn new() -> TermGraph {
        TermGraph {
            terms: Vec::new(),
            groups: Vec::new(),
            compounds: Vec::new(),
            clause_set: ClauseSet::new(),
            compound_map: HashMap::new(),
            decompositions: HashMap::new(),
            pending: Vec::new(),
            has_contradiction: false,
            contradiction_info: None,
        }
    }

    /// Returns None if this term isn't in the graph.
    pub fn get_term_id(&self, term: &Term) -> Option<TermId> {
        // Look up the head
        let head_key = Decomposition::Atomic(term.head.clone());
        let head_id = *self.decompositions.get(&head_key)?;

        if term.args.is_empty() {
            return Some(head_id);
        }

        // Look up the args
        let mut arg_ids = Vec::new();
        for arg in &term.args {
            arg_ids.push(self.get_term_id(arg)?);
        }

        let compound_key = Decomposition::Compound(head_id, arg_ids);
        self.decompositions.get(&compound_key).copied()
    }

    pub fn get_term(&self, term_id: TermId) -> &Term {
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
    pub fn has_contradiction_trace(&self) -> bool {
        self.contradiction_info.is_some()
    }

    /// Used to explain which steps lead to a contradiction.
    /// Returns None if there is no contradiction trace.
    pub fn get_contradiction_trace(&self) -> Option<TermGraphContradiction> {
        let (term1, term2, inequality_id) = self.contradiction_info?;
        let mut rewrite_chain = vec![];
        self.expand_steps(term1, term2, &mut rewrite_chain);
        Some(TermGraphContradiction {
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

    // Inserts the head of the provided term as an atom.
    // If it's already in the graph, return the existing term id.
    // Otherwise, make a new term id and give it a new group.
    fn insert_head(&mut self, term: &Term) -> TermId {
        let key = Decomposition::Atomic(term.head.clone());
        if let Some(&id) = self.decompositions.get(&key) {
            return id;
        }

        // Make a new term and group
        let term_id = TermId(self.terms.len() as u32);
        let group_id = GroupId(self.groups.len() as u32);

        let head = Term {
            term_type: term.head_type,
            head_type: term.head_type,
            head: term.head.clone(),
            args: vec![],
        };
        let term_info = TermInfo {
            term: head,
            group: group_id,
            decomp: key.clone(),
            adjacent: vec![],
        };
        self.terms.push(term_info);
        let group_info = PossibleGroupInfo::Info(GroupInfo {
            terms: vec![term_id],
            compounds: vec![],
            inequalities: HashMap::new(),
        });
        self.groups.push(group_info);
        self.decompositions.insert(key, term_id);
        term_id
    }

    // Inserts a term composition relationship.
    // If it's already in the graph, return the existing term id.
    // Otherwise, make a new term and group.
    fn insert_term_compound(&mut self, term: &Term, head: TermId, args: Vec<TermId>) -> TermId {
        let key = Decomposition::Compound(head, args);
        if let Some(&id) = self.decompositions.get(&key) {
            return id;
        }

        // Make a new term and group
        let term_id = TermId(self.terms.len() as u32);
        let group_id = GroupId(self.groups.len() as u32);
        let term_info = TermInfo {
            term: term.clone(),
            group: group_id,
            decomp: key.clone(),
            adjacent: vec![],
        };
        self.terms.push(term_info);
        let group_info = PossibleGroupInfo::Info(GroupInfo {
            terms: vec![term_id],
            compounds: vec![],
            inequalities: HashMap::new(),
        });
        self.groups.push(group_info);
        self.decompositions.insert(key, term_id);
        term_id
    }

    // Adds a group composition relationship.
    // If we should combine groups, add them to the pending list.
    fn insert_group_compound(&mut self, head: GroupId, args: Vec<GroupId>, result_term: TermId) {
        let result_group = self.get_group_id(result_term);
        let key = CompoundKey { head, args };
        if let Some(&existing_result_term) = self.compound_map.get(&key) {
            let existing_result_group = self.get_group_id(existing_result_term);
            if existing_result_group != result_group {
                self.pending.push(SemanticOperation::TermEquality(
                    existing_result_term,
                    result_term,
                ));
            }
            return;
        }

        // We need to make a new relatinoship
        let compound_info = CompoundInfo {
            key: key.clone(),
            result_term,
        };
        for group in key.groups() {
            match &mut self.groups[group.get() as usize] {
                PossibleGroupInfo::Remapped(id) => {
                    panic!(
                        "compound info refers to a remapped group {} -> {}",
                        group, id
                    );
                }
                PossibleGroupInfo::Info(info) => {
                    info.compounds.push(CompoundId(self.compounds.len() as u32));
                }
            }
        }
        self.compounds.push(Some(compound_info));
        self.compound_map.insert(key, result_term);
        return;
    }

    /// Inserts a term.
    /// Makes a new term, group, and compound if necessary.
    pub fn insert_term(&mut self, term: &Term) -> TermId {
        let head_term_id = self.insert_head(term);
        if term.args.is_empty() {
            return head_term_id;
        }
        let head_group_id = self.get_group_id(head_term_id);

        let mut arg_term_ids = vec![];
        let mut arg_group_ids = vec![];
        for arg in &term.args {
            let arg_term_id = self.insert_term(arg);
            arg_term_ids.push(arg_term_id);
            let arg_group_id = self.get_group_id(arg_term_id);
            arg_group_ids.push(arg_group_id);
        }

        let result_term_id = self.insert_term_compound(term, head_term_id, arg_term_ids);
        self.insert_group_compound(head_group_id, arg_group_ids, result_term_id);
        self.process_pending();
        result_term_id
    }

    /// Inserts a clause into the graph.
    /// All terms in the clause are inserted if not already present.
    /// The clause is indexed by all groups that appear in its literals.
    /// Don't insert clauses with no literals.
    pub fn insert_clause(&mut self, clause: &Clause, step: StepId) {
        // First, insert all terms and collect literal IDs
        let mut literal_ids = Vec::new();
        for literal in &clause.literals {
            let left_id = self.insert_term(&literal.left);
            let right_id = self.insert_term(&literal.right);

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

        let mut keep_compounds = vec![];
        for compound_id in old_info.compounds {
            {
                let compound = match &mut self.compounds[compound_id.get() as usize] {
                    Some(compound) => compound,
                    None => {
                        // This compound has already been deleted.
                        // Time to lazily delete the reference to it.
                        continue;
                    }
                };
                self.compound_map.remove(&compound.key);
                compound.key.remap_group(old_group, new_group);
            }
            let compound = self.compounds[compound_id.get() as usize]
                .as_ref()
                .expect("how does this happen?");

            if let Some(&existing_result_term) = self.compound_map.get(&compound.key) {
                // An compound for the new relationship already exists.
                // Instead of inserting compound.result, we need to delete this compound, and merge the
                // intended result with result_group.
                self.pending.push(SemanticOperation::TermEquality(
                    compound.result_term,
                    existing_result_term,
                ));
                self.compounds[compound_id.get() as usize] = None;
            } else {
                self.compound_map
                    .insert(compound.key.clone(), compound.result_term);
                keep_compounds.push(compound_id);
            }
        }

        // Rekey the inequalities that refer to this group from elsewhere
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
            }
            if !unequal_info.inequalities.contains_key(&new_group) {
                unequal_info.inequalities.insert(new_group, value);
            }
        }

        // Merge the old info into the new info
        let new_info = match &mut self.groups[new_group.get() as usize] {
            PossibleGroupInfo::Remapped(id) => panic!("group {} is remapped to {}", new_group, id),
            PossibleGroupInfo::Info(info) => info,
        };
        new_info.terms.extend(old_info.terms);
        new_info.compounds.extend(keep_compounds);
        for (group, value) in old_info.inequalities {
            if !new_info.inequalities.contains_key(&group) {
                new_info.inequalities.insert(group, value);
            }
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
                    self.pending.push(SemanticOperation::TermEquality(left_term, right_term));
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
                // Actually insert the clause into the set
                self.clause_set.insert(new_clause);
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
    }

    fn as_compound(&self, term: TermId) -> (TermId, &Vec<TermId>) {
        match &self.terms[term.get() as usize].decomp {
            Decomposition::Compound(head, args) => (*head, args),
            _ => panic!("not a compound"),
        }
    }

    /// Returns the truth value of this literal, or None if it cannot be evaluated.
    pub fn evaluate_literal(&mut self, literal: &Literal) -> Option<bool> {
        // If the literal is positive, we check if the terms are equal.
        // If the literal is negative, we check if the terms are not equal.
        let left_id = self.insert_term(&literal.left);
        let right_id = self.insert_term(&literal.right);

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
    pub fn check_clause(&mut self, clause: &Clause) -> bool {
        if self.has_contradiction() {
            return true;
        }

        for literal in &clause.literals {
            if self.evaluate_literal(literal) == Some(true) {
                return true;
            }
        }

        // Check if this exact clause (or an equivalent one) exists in our stored clauses
        if self.clause_exists(clause) {
            return true;
        }

        false
    }

    /// Checks if a clause with the same literals exists in the term graph.
    /// This compares clauses based on their group-normalized form.
    fn clause_exists(&mut self, clause: &Clause) -> bool {
        if clause.literals.is_empty() {
            return false;
        }

        // Convert the clause to literal IDs
        let mut literal_ids = Vec::new();
        for literal in &clause.literals {
            let left_id = self.insert_term(&literal.left);
            let right_id = self.insert_term(&literal.right);
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
    // This is "postorder" in the sense that we show a rewritten compound term after showing
    // the rewrites for the subterms.
    // The compound rewrites have a step id of None.
    // The rewritten subterms have a step id with the rule that they are based on.
    fn expand_steps(&self, term1: TermId, term2: TermId, output: &mut Vec<RewriteStep>) {
        if term1 == term2 {
            return;
        }
        let path = self.get_path(term1, term2);
        for (a_id, b_id, source) in path {
            if source.is_none() {
                // We have a compound relationship between a_id and b_id
                let (head_a, args_a) = self.as_compound(a_id);
                let (head_b, args_b) = self.as_compound(b_id);
                assert_eq!(args_a.len(), args_b.len());
                self.expand_steps(head_a, head_b, output);
                for (arg_a, arg_b) in args_a.iter().zip(args_b.iter()) {
                    self.expand_steps(*arg_a, *arg_b, output);
                }
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
                    let (head_a, args_a) = self.as_compound(term_a);
                    let (head_b, args_b) = self.as_compound(term_b);
                    assert_eq!(args_a.len(), args_b.len());
                    self.get_step_ids_helper(head_a, head_b, output);
                    for (arg_a, arg_b) in args_a.iter().zip(args_b.iter()) {
                        self.get_step_ids_helper(*arg_a, *arg_b, output);
                    }
                }
            }
        }
    }

    /// Extract a list of steps ids that we used to prove that these two terms are equal.
    /// This does deduplicate.
    pub fn get_step_ids(&self, term1: TermId, term2: TermId) -> Vec<usize> {
        let mut answer = BTreeSet::new();
        self.get_step_ids_helper(term1, term2, &mut answer);
        answer.into_iter().map(|id| id.get()).collect()
    }

    pub fn show_graph(&self) {
        println!("terms:");
        for (i, term_info) in self.terms.iter().enumerate() {
            println!("term {}, group {}: {}", i, term_info.group, term_info.term);
        }
        println!("compounds:");
        for compound in &self.compounds {
            if let Some(compound) = compound {
                println!("{}", compound);
            }
        }
    }

    /// Follows remapping chains to find the current group id.
    /// Updates intermediate remaps to point directly to the final destination for efficiency.
    pub fn update_group_id(&mut self, group_id: GroupId) -> GroupId {
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
    pub fn normalize(&mut self, clause_id: ClauseId) -> Normalization {
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
    pub fn validate(&self) {
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
            for compound_id in &group_info.compounds {
                let compound = &self.compounds[compound_id.get() as usize];
                let compound = match compound {
                    Some(compound) => compound,
                    None => continue,
                };
                assert!(compound.key.touches_group(group_id));
            }
        }

        for (compound_id, compound) in self.compounds.iter().enumerate() {
            let compound = match compound {
                Some(compound) => compound,
                None => continue,
            };
            let groups = compound.key.groups();
            for group in groups {
                let info = self.validate_group_id(group);
                assert!(info.compounds.contains(&CompoundId(compound_id as u32)));
            }
        }

        // Validate the clause set
        self.clause_set.validate();
    }
}

// Methods for testing.
impl TermGraph {
    #[cfg(test)]
    fn insert_term_str(&mut self, s: &str) -> TermId {
        let id = self.insert_term(&Term::parse(s));
        self.validate();
        id
    }

    #[cfg(test)]
    fn insert_clause_str(&mut self, s: &str, step: StepId) {
        let clause = Clause::parse(s);
        self.insert_clause(&clause, step);
        self.validate();
    }

    #[cfg(test)]
    fn assert_eq(&self, t1: TermId, t2: TermId) {
        assert_eq!(self.get_group_id(t1), self.get_group_id(t2));
    }

    #[cfg(test)]
    fn with_clauses(clauses: &[&str]) -> TermGraph {
        let mut g = TermGraph::new();
        for (i, s) in clauses.iter().enumerate() {
            g.insert_clause_str(s, StepId(i));
        }
        g
    }

    #[cfg(test)]
    fn set_eq(&mut self, t1: TermId, t2: TermId, pattern_id: StepId) {
        self.set_terms_equal(t1, t2, pattern_id, None);
        self.validate();
        self.assert_eq(t1, t2);
    }

    #[cfg(test)]
    fn assert_ne(&self, t1: TermId, t2: TermId) {
        assert_ne!(self.get_group_id(t1), self.get_group_id(t2));
    }

    #[cfg(test)]
    fn get_str(&self, s: &str) -> TermId {
        self.get_term_id(&Term::parse(s)).unwrap()
    }

    #[cfg(test)]
    fn check_clause_str(&mut self, s: &str) {
        let clause = Clause::parse(s);
        if !self.check_clause(&clause) {
            panic!("check_clause_str(\"{}\") failed", s);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_identifying_atomic_subterms() {
        let mut g = TermGraph::new();
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
        let mut g = TermGraph::new();
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
        let mut g = TermGraph::new();
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
        let mut g = TermGraph::new();
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
        g.show_graph();
        assert_eq!(g.get_step_ids(c0, c3), vec![4]);
    }

    #[test]
    fn test_finding_contradiction() {
        let mut g = TermGraph::new();
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
        let mut g = TermGraph::new();
        g.insert_clause_str("c1 = c2 or c3 != c4 or c5 != c6", StepId(0));
        assert!(!g.has_contradiction);
        g.insert_clause_str("c1 != c2", StepId(1));
        assert!(!g.has_contradiction);
        g.insert_clause_str("c3 = c4", StepId(2));
        assert!(!g.has_contradiction);
        g.insert_clause_str("c5 = c6", StepId(3));
        assert!(g.has_contradiction);
    }

    #[test]
    fn test_clause_reduction_two_to_zero() {
        let mut g = TermGraph::new();
        g.insert_clause_str("c1 = c2 or c1 = c3", StepId(0));
        assert!(!g.has_contradiction);
        g.insert_clause_str("c2 = c4", StepId(1));
        assert!(!g.has_contradiction);
        g.insert_clause_str("c3 = c4", StepId(2));
        assert!(!g.has_contradiction);
        g.insert_clause_str("c1 != c4", StepId(3));
        assert!(g.has_contradiction);
    }

    #[test]
    fn test_subterm_triggering_clause() {
        let mut g = TermGraph::new();
        g.insert_clause_str("c1(c2) != c1(c3) or c4(c2) != c4(c3)", StepId(0));
        assert!(!g.has_contradiction);
        g.insert_clause_str("c2 = c3", StepId(1));
        assert!(g.has_contradiction);
    }

    #[test]
    fn test_hypotheses_then_imp() {
        let mut g =
            TermGraph::with_clauses(&["g1(c1)", "g2(c1)", "not g1(c1) or not g2(c1) or g3(c1)"]);
        g.check_clause_str("g3(c1)");
    }

    #[test]
    fn test_imp_then_hypotheses() {
        let mut g =
            TermGraph::with_clauses(&["not g1(c1) or not g2(c1) or g3(c1)", "g1(c1)", "g2(c1)"]);
        g.check_clause_str("g3(c1)");
    }

    #[test]
    fn test_term_graph_rewriting_equality() {
        let mut g =
            TermGraph::with_clauses(&["g1(c1, g2(c2, c3)) = c4", "g2(c2, c3) = g2(c3, c2)"]);
        g.check_clause_str("g1(c1, g2(c3, c2)) = c4");
    }

    #[test]
    fn test_term_graph_rewriting_inequality() {
        let mut g =
            TermGraph::with_clauses(&["g1(c1, g2(c2, c3)) != c4", "g2(c2, c3) = g2(c3, c2)"]);
        g.check_clause_str("g1(c1, g2(c3, c2)) != c4");
    }

    #[test]
    fn test_term_graph_concluding_opposing_literals() {
        let mut g = TermGraph::with_clauses(&[
            "not g4(g6, g5(c1, g0))",
            "g4(g6, g6) or g3(g6, g6)",
            "not g3(g6, g6) or g4(g6, g6)",
            "g5(c1, g0) = g6",
            "not g4(g6, g6)",
        ]);

        g.check_clause_str("g3(g6, g6)");
    }

    #[test]
    fn test_term_graph_checking_long_clause() {
        let mut g = TermGraph::with_clauses(&["g0 = g1 or g2 = g3"]);

        g.check_clause_str("g0 = g1 or g2 = g3");
    }

    #[test]
    fn test_term_graph_shortening_long_clause() {
        let mut g =
            TermGraph::with_clauses(&["not g0(c2, c3)", "not g1(c2, c3) or g0(c2, c3) or c3 = c2"]);

        g.check_clause_str("not g1(c2, c3) or c3 = c2");
    }

    #[test]
    fn test_term_graph_checking_reducible_clause() {
        // This failed at some point because we were checking a clause that could be reduced.
        let mut g = TermGraph::with_clauses(&[
            // These are necessary to reproduce the bug
            "m4(c4, c5) = c3",
            "c4 != c0",
            "m4(c4, c5) != c3 or m4(c4, m1(c5, c0)) = m1(c3, c0) or c4 = c0",
            // The clauses from the basic case
            "not m0(m1(c5, c0), c1)",
            "m4(c4, m1(c5, c0)) != m1(c3, c0) or not m0(m1(c3, c0), c1) or m0(m1(c5, c0), c1) or c4 = c1",
        ]);
        g.check_clause_str("m4(c4, m1(c5, c0)) != m1(c3, c0) or not m0(m1(c3, c0), c1) or c4 = c1");
    }

    #[test]
    fn test_term_graph_reducing_clauses() {
        let g = TermGraph::with_clauses(&[
            "not g3(g1) or g3(g0)",
            "not g3(g0) or g3(g2)",
            "g3(g1)",
            "not g3(g2)",
        ]);
        assert!(g.has_contradiction);
    }

    #[test]
    fn test_normalize() {
        let mut g = TermGraph::new();

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

        match g.normalize(clause.clone()) {
            Normalization::Clause(normalized) => {
                assert_eq!(normalized.literals().len(), 2);
            }
            _ => panic!("Expected a normal clause"),
        }

        // Test 2: Clause that becomes simpler after merging
        g.set_eq(t1, t2, StepId(0));

        // After merging t1 and t2, the literal "g1 = g2" becomes reflexive and should be filtered
        match g.normalize(clause) {
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
        match g.normalize(clause2) {
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
        let mut g = TermGraph::new();

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
            match &g.groups[initial_g1.get() as usize] {
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
            match &g.groups[g5.get() as usize] {
                PossibleGroupInfo::Remapped(target) => assert_eq!(*target, final_567),
                PossibleGroupInfo::Info(_) => panic!("g5 should be remapped"),
            }
        }
    }
}

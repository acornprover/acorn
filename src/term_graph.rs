use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt;
use std::hash::Hash;

use crate::atom::Atom;
use crate::clause::Clause;
use crate::clause_set::{GroupId, TermId};
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
        write!(f, "{}", self.0)
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

    // The clauses that are related to this group.
    // Keyed by the group that is on the other side of the literal from this one.
    clauses: HashMap<GroupId, HashSet<ClauseId>>,
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

impl fmt::Display for CompoundId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
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

// We represent literals based on their terms.
// This isn't quite enough to have good tracking information, so we might need to expand on this.
#[derive(Clone)]
struct LiteralInfo {
    positive: bool,
    left: TermId,
    right: TermId,
}

#[derive(Clone)]
struct ClauseInfo {
    // The literals that make up the clause.
    literals: Vec<LiteralInfo>,

    // The step in which we added this clause to the graph.
    step: StepId,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
struct ClauseId(usize);

impl fmt::Display for ClauseId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
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

    // We have discovered that a clause can be reduced.
    ClauseReduction(ClauseId),
}

/// The TermGraph stores concrete terms, along with relationships between them that represent
/// equality, inequality, and subterm relationships.
#[derive(Clone)]
pub struct TermGraph {
    // terms maps TermId to TermInfo.
    terms: Vec<TermInfo>,

    // groups maps GroupId to GroupInfo.
    groups: Vec<Option<GroupInfo>>,

    // compounds maps CompoundId to CompoundInfo.
    // When a compound is deleted, we replace it with None.
    compounds: Vec<Option<CompoundInfo>>,

    // clauses maps ClauseId to ClauseInfo.
    // When a clause is eliminated, we replace it with None.
    clauses: Vec<Option<ClauseInfo>>,

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
            clauses: Vec::new(),
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
        &self.terms[term_id.0 as usize].term
    }

    fn get_group_id(&self, term_id: TermId) -> GroupId {
        self.terms[term_id.0 as usize].group
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
        match &self.groups[group_id.0 as usize] {
            None => panic!("group is remapped"),
            Some(info) => info,
        }
    }

    fn get_clause_info(&self, clause_id: ClauseId) -> &Option<ClauseInfo> {
        &self.clauses[clause_id.0]
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
        let group_info = Some(GroupInfo {
            terms: vec![term_id],
            compounds: vec![],
            inequalities: HashMap::new(),
            clauses: HashMap::new(),
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
        let group_info = Some(GroupInfo {
            terms: vec![term_id],
            compounds: vec![],
            inequalities: HashMap::new(),
            clauses: HashMap::new(),
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
            match &mut self.groups[group.0 as usize] {
                None => {
                    panic!("compound info refers to a remapped group");
                }
                Some(info) => {
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
        // First, insert all terms and collect their IDs
        let mut literal_infos = Vec::new();
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
            literal_infos.push(LiteralInfo {
                positive: literal.positive,
                left: left_id,
                right: right_id,
            });
        }

        // Create the clause info
        let clause_info = ClauseInfo {
            literals: literal_infos.clone(),
            step,
        };

        // Add the clause to the clauses vector
        let clause_id = ClauseId(self.clauses.len());
        self.clauses.push(Some(clause_info));

        // Check if any literal can already be evaluated
        let mut needs_reduction = false;
        for literal_info in &literal_infos {
            let left_group = self.get_group_id(literal_info.left);
            let right_group = self.get_group_id(literal_info.right);

            // Check if the literal can be evaluated
            if left_group == right_group {
                // The terms are equal
                needs_reduction = true;
            } else {
                let left_group_info = self.get_group_info(left_group);
                if left_group_info.inequalities.contains_key(&right_group) {
                    // The terms are known to be not equal
                    needs_reduction = true;
                }
            }
        }

        // For each literal, add the clause to both groups involved
        for literal_info in &literal_infos {
            let left_group = self.get_group_id(literal_info.left);
            let right_group = self.get_group_id(literal_info.right);

            // Add to left group's clauses, indexed by right group
            if let Some(left_group_info) = &mut self.groups[left_group.0 as usize] {
                left_group_info
                    .clauses
                    .entry(right_group)
                    .or_insert_with(HashSet::new)
                    .insert(clause_id);
            }

            // Add to right group's clauses, indexed by left group
            if let Some(right_group_info) = &mut self.groups[right_group.0 as usize] {
                right_group_info
                    .clauses
                    .entry(left_group)
                    .or_insert_with(HashSet::new)
                    .insert(clause_id);
            }
        }

        // If any literal can be evaluated, schedule a reduction
        if needs_reduction {
            self.pending
                .push(SemanticOperation::ClauseReduction(clause_id));
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
        let old_info = self.groups[old_group.0 as usize]
            .take()
            .expect("group is remapped");

        for &term_id in &old_info.terms {
            self.terms[term_id.0 as usize].group = new_group;
        }

        let mut keep_compounds = vec![];
        for compound_id in old_info.compounds {
            {
                let compound = match &mut self.compounds[compound_id.0 as usize] {
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
            let compound = self.compounds[compound_id.0 as usize]
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
                self.compounds[compound_id.0 as usize] = None;
            } else {
                self.compound_map
                    .insert(compound.key.clone(), compound.result_term);
                keep_compounds.push(compound_id);
            }
        }

        // Rekey the inequalities that refer to this group from elsewhere
        for &unequal_group in old_info.inequalities.keys() {
            let unequal_info = self.groups[unequal_group.0 as usize]
                .as_mut()
                .expect("group is remapped");
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
        let new_info = self.groups[new_group.0 as usize]
            .as_mut()
            .expect("group is remapped");
        new_info.terms.extend(old_info.terms);
        new_info.compounds.extend(keep_compounds);
        for (group, value) in old_info.inequalities {
            if !new_info.inequalities.contains_key(&group) {
                new_info.inequalities.insert(group, value);
            }
        }

        // First, merge clauses from old_group into new_group.
        // Track which other groups need updates
        let mut other_groups_to_update = Vec::new();
        for (other_group, clause_ids) in old_info.clauses {
            let key_group = if other_group == old_group {
                // Self-referential: old_group -> old_group becomes new_group -> new_group
                new_group
            } else {
                // Track that this other group needs to be updated
                if other_group != new_group {
                    other_groups_to_update.push(other_group);
                }
                other_group
            };

            // If key_group == new_group, these clauses now compare a group to itself
            // and need reduction
            if key_group == new_group {
                for &clause_id in &clause_ids {
                    self.pending
                        .push(SemanticOperation::ClauseReduction(clause_id));
                }
            } else if new_info.inequalities.contains_key(&key_group) {
                // The new group already has an inequality with this other group,
                // so these clauses might be reducible now
                for &clause_id in &clause_ids {
                    self.pending
                        .push(SemanticOperation::ClauseReduction(clause_id));
                }
            }

            new_info
                .clauses
                .entry(key_group)
                .or_insert_with(HashSet::new)
                .extend(clause_ids);
        }

        // Now update the other groups to point to new_group instead of old_group
        // Also collect the clauses to add reciprocal indexing to new_group
        let mut reciprocal_updates = Vec::new();
        for other_group in other_groups_to_update {
            if let Some(other_info) = self.groups[other_group.0 as usize].as_mut() {
                if let Some(clauses) = other_info.clauses.remove(&old_group) {
                    // If other_group == new_group, these clauses now compare a group to itself
                    if other_group == new_group {
                        for &clause_id in &clauses {
                            self.pending
                                .push(SemanticOperation::ClauseReduction(clause_id));
                        }
                    } else {
                        // Store for reciprocal update
                        reciprocal_updates.push((other_group, clauses.clone()));
                    }

                    other_info
                        .clauses
                        .entry(new_group)
                        .or_insert_with(HashSet::new)
                        .extend(clauses);
                }
            }
        }

        // Add reciprocal indexing to new_group
        for (other_group, clause_ids) in reciprocal_updates {
            let new_info = self.groups[new_group.0 as usize]
                .as_mut()
                .expect("group is remapped");
            new_info
                .clauses
                .entry(other_group)
                .or_insert_with(HashSet::new)
                .extend(clause_ids);
        }

        // Also need to remove old_group from new_group's clauses if it exists
        // Do this after the loop to avoid borrow checker issues
        let new_info = self.groups[new_group.0 as usize]
            .as_mut()
            .expect("group is remapped");
        if let Some(clauses) = new_info.clauses.remove(&old_group) {
            // These clauses now compare a group to itself and need reduction
            for &clause_id in &clauses {
                self.pending
                    .push(SemanticOperation::ClauseReduction(clause_id));
            }
        }

        self.terms[old_term.0 as usize]
            .adjacent
            .push((new_term, source));
        self.terms[new_term.0 as usize]
            .adjacent
            .push((old_term, source));
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
                SemanticOperation::ClauseReduction(clause_id) => {
                    self.reduce_clause(clause_id);
                }
            }
        }
    }

    /// Reduces a clause by checking if any of its literals can be evaluated.
    fn reduce_clause(&mut self, clause_id: ClauseId) {
        // Taking the clause info. Don't forget to put it back.
        let Some(mut clause_info) = self.clauses[clause_id.0].take() else {
            return;
        };

        // Track which groups were involved before reduction
        let mut old_groups = HashSet::new();
        for literal in &clause_info.literals {
            old_groups.insert(self.get_group_id(literal.left));
            old_groups.insert(self.get_group_id(literal.right));
        }

        let mut literals = vec![];
        std::mem::swap(&mut clause_info.literals, &mut literals);
        for literal in literals {
            let left_group = self.get_group_id(literal.left);
            let right_group = self.get_group_id(literal.right);
            let sides_equal = if left_group == right_group {
                true
            } else {
                let left_info = self.get_group_info(left_group);
                if left_info.inequalities.contains_key(&right_group) {
                    false
                } else {
                    // We can't evaluate this literal. Put it back.
                    clause_info.literals.push(literal);
                    continue;
                }
            };
            if literal.positive == sides_equal {
                // This literal is true, so the whole clause is redundant.
                // Remove clause from all group pairs
                let group_pairs: Vec<(GroupId, GroupId)> = old_groups
                    .iter()
                    .flat_map(|&g1| old_groups.iter().map(move |&g2| (g1, g2)))
                    .filter(|(g1, g2)| g1 != g2)
                    .collect();

                for (group1, group2) in group_pairs {
                    if let Some(group_info) = self.groups[group1.0 as usize].as_mut() {
                        if let Some(clause_ids) = group_info.clauses.get_mut(&group2) {
                            clause_ids.remove(&clause_id);
                        }
                    }
                }
                return;
            }
        }

        if clause_info.literals.len() >= 2 {
            // Track which groups are involved after reduction
            let mut new_groups = HashSet::new();
            for literal in &clause_info.literals {
                new_groups.insert(self.get_group_id(literal.left));
                new_groups.insert(self.get_group_id(literal.right));
            }

            // Remove clause from groups that are no longer involved
            for &removed_group in old_groups.difference(&new_groups) {
                // We need to remove this clause from the indexing between removed_group and all other groups

                // Remove from removed_group's indexing of all groups
                if let Some(group_info) = self.groups[removed_group.0 as usize].as_mut() {
                    // For each group that removed_group indexes clauses by
                    let groups_to_clean: Vec<GroupId> =
                        group_info.clauses.keys().copied().collect();
                    for other_group in groups_to_clean {
                        if let Some(clause_ids) = group_info.clauses.get_mut(&other_group) {
                            clause_ids.remove(&clause_id);
                        }
                    }
                }

                // Also remove from all other groups' indexing of removed_group
                for i in 0..self.groups.len() {
                    if let Some(group_info) = self.groups[i].as_mut() {
                        if let Some(clause_ids) = group_info.clauses.get_mut(&removed_group) {
                            clause_ids.remove(&clause_id);
                        }
                    }
                }
            }

            // This clause is still valid. Put it back.
            self.clauses[clause_id.0] = Some(clause_info.clone());

            // Re-index the clause with its current groups
            for literal in &clause_info.literals {
                let left_group = self.get_group_id(literal.left);
                let right_group = self.get_group_id(literal.right);

                // Add to left group's clauses, indexed by right group
                if let Some(left_group_info) = &mut self.groups[left_group.0 as usize] {
                    left_group_info
                        .clauses
                        .entry(right_group)
                        .or_insert_with(HashSet::new)
                        .insert(clause_id);
                }

                // Add to right group's clauses, indexed by left group
                if let Some(right_group_info) = &mut self.groups[right_group.0 as usize] {
                    right_group_info
                        .clauses
                        .entry(left_group)
                        .or_insert_with(HashSet::new)
                        .insert(clause_id);
                }
            }

            return;
        }

        // This clause is toast, but now what?

        // Remove clause from all group pairs since it's being deleted
        let group_pairs: Vec<(GroupId, GroupId)> = old_groups
            .iter()
            .flat_map(|&g1| old_groups.iter().map(move |&g2| (g1, g2)))
            .filter(|(g1, g2)| g1 != g2)
            .collect();

        for (group1, group2) in group_pairs {
            if let Some(group_info) = self.groups[group1.0 as usize].as_mut() {
                if let Some(clause_ids) = group_info.clauses.get_mut(&group2) {
                    clause_ids.remove(&clause_id);
                }
            }
        }

        if clause_info.literals.len() == 1 {
            let literal = &clause_info.literals[0];
            if literal.positive {
                let source = RewriteSource {
                    pattern_id: clause_info.step,
                    inspiration_id: None,
                    left: literal.left,
                    right: literal.right,
                };
                self.pending.push(SemanticOperation::Rewrite(source));
            } else {
                self.pending.push(SemanticOperation::TermInequality(
                    literal.left,
                    literal.right,
                    clause_info.step,
                ));
            }
        } else {
            // No literals.
            self.has_contradiction = true;
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

        let info1 = &mut self.groups[group1.0 as usize]
            .as_mut()
            .expect("group is remapped");
        let already_unequal = info1.inequalities.contains_key(&group2);
        if !already_unequal {
            info1.inequalities.insert(group2, (term1, term2, step));
        }

        // Trigger reduction for clauses that involve both groups
        if let Some(clause_ids) = info1.clauses.get(&group2) {
            for &clause_id in clause_ids {
                self.pending
                    .push(SemanticOperation::ClauseReduction(clause_id));
            }
        }

        let info2 = &mut self.groups[group2.0 as usize]
            .as_mut()
            .expect("group is remapped");

        // Only update info2 if we didn't already have this inequality
        if !already_unequal {
            // Check clauses from the other direction too
            if let Some(clause_ids) = info2.clauses.get(&group1) {
                // Trigger reduction on these clauses too
                for &clause_id in clause_ids {
                    self.pending
                        .push(SemanticOperation::ClauseReduction(clause_id));
                }
            }

            let prev = info2.inequalities.insert(group1, (term1, term2, step));
            if prev.is_some() {
                panic!("asymmetry in group inequalities");
            }
        }
    }

    fn as_compound(&self, term: TermId) -> (TermId, &Vec<TermId>) {
        match &self.terms[term.0 as usize].decomp {
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

        // First, convert the clause to check into group-normalized form, skipping false literals
        let mut check_literals = Vec::new();
        let mut groups_involved = HashSet::new();
        for literal in &clause.literals {
            let left_id = self.insert_term(&literal.left);
            let right_id = self.insert_term(&literal.right);
            let left_group = self.get_group_id(left_id);
            let right_group = self.get_group_id(right_id);

            // Figure out whether the sides are equal, if possible
            let sides_equal = if left_group == right_group {
                Some(true)
            } else {
                let left_info = self.get_group_info(left_group);
                if left_info.inequalities.contains_key(&right_group) {
                    Some(false)
                } else {
                    None
                }
            };

            // If the literal evaluates to false, skip it
            if Some(!literal.positive) == sides_equal {
                continue;
            }

            // Otherwise include it
            groups_involved.insert(left_group);
            groups_involved.insert(right_group);
            check_literals.push((literal.positive, left_group, right_group));
        }

        // Sort literals for canonical comparison
        check_literals.sort();

        if check_literals.is_empty() {
            // If literals are false, the clause itself is false
            return self.has_contradiction();
        }

        // Use the clause indexing to find potentially matching clauses
        // We only need to check clauses that involve the same groups
        let mut candidate_clauses: HashSet<ClauseId> = HashSet::new();

        // Get clauses from the first group's index
        let first_group = *groups_involved.iter().next().unwrap();
        if let Some(group_info) = &self.groups[first_group.0 as usize] {
            for (other_group, clause_ids) in &group_info.clauses {
                if groups_involved.contains(other_group) {
                    candidate_clauses.extend(clause_ids);
                }
            }
        }

        // Now check only the candidate clauses
        for &clause_id in &candidate_clauses {
            let Some(info) = &self.clauses[clause_id.0] else {
                continue;
            };

            // Convert stored clause to same normalized form
            let mut stored_literals = Vec::new();
            for literal in &info.literals {
                let left_group = self.get_group_id(literal.left);
                let right_group = self.get_group_id(literal.right);
                stored_literals.push((literal.positive, left_group, right_group));
            }
            stored_literals.sort();

            // Check if they match
            if check_literals == stored_literals {
                return true;
            }
        }

        false
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
            for (term_a, source) in &self.terms[term_b.0 as usize].adjacent {
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
        answer.into_iter().map(|id| id.0).collect()
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

    // Checks that the group id has not been remapped
    fn validate_group_id(&self, group_id: GroupId) -> &GroupInfo {
        assert!(group_id < GroupId(self.groups.len() as u32));
        match &self.groups[group_id.0 as usize] {
            None => {
                panic!("group {} is remapped", group_id)
            }
            Some(info) => info,
        }
    }

    // Checks that this clause contains a term from this group.
    // It's also okay if the clause has ceased to exist, because we clean up lazily.
    fn check_clause_has_group(&self, clause_id: ClauseId, group_id: GroupId) {
        let Some(clause_info) = self.get_clause_info(clause_id) else {
            return;
        };
        for literal in &clause_info.literals {
            let left_group = self.get_group_id(literal.left);
            let right_group = self.get_group_id(literal.right);
            if left_group == group_id || right_group == group_id {
                return; // Found a term from the group
            }
        }
        panic!(
            "clause {} does not contain a term from group {}",
            clause_id, group_id
        );
    }

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
                None => {
                    continue;
                }
                Some(info) => info,
            };
            for term_id in &group_info.terms {
                let term_group = self.terms[term_id.0 as usize].group;
                assert_eq!(term_group, group_id);
            }
            for compound_id in &group_info.compounds {
                let compound = &self.compounds[compound_id.0 as usize];
                let compound = match compound {
                    Some(compound) => compound,
                    None => continue,
                };
                assert!(compound.key.touches_group(group_id));
            }

            for (other_group_id, clause_ids) in &group_info.clauses {
                // The same clause ids should be stored in both direction
                let other_info = self.validate_group_id(*other_group_id);
                let alt_clause_ids = other_info.clauses.get(&group_id).unwrap();
                assert_eq!(clause_ids, alt_clause_ids);

                for clause_id in clause_ids {
                    self.check_clause_has_group(*clause_id, group_id);
                }
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

        for (clause_id, clause_info) in self.clauses.iter().enumerate() {
            let clause_id = ClauseId(clause_id);
            let Some(clause_info) = clause_info else {
                continue;
            };
            assert!(clause_info.literals.len() > 1);
            for literal in &clause_info.literals {
                let left_group = self.get_group_id(literal.left);
                let right_group = self.get_group_id(literal.right);

                let left_info = self.validate_group_id(left_group);
                let clause_ids = left_info.clauses.get(&right_group).unwrap();
                assert!(clause_ids.contains(&clause_id));

                let right_info = self.validate_group_id(right_group);
                let clause_ids = right_info.clauses.get(&left_group).unwrap();
                assert!(clause_ids.contains(&clause_id));
            }
        }
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
}

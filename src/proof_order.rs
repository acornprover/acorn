use std::collections::{BTreeSet, HashMap, HashSet};

use crate::kernel::clause::Clause;

/// Return a stable topological order that moves support clauses before later dependent clauses.
///
/// This is used before certificate serialization, where replay is easier if late unit supports are
/// emitted before claims that need them. `None` means either no support edges were found, the graph
/// was cyclic, or the existing order was already suitable.
pub(crate) fn unit_support_order(clauses: &[Clause]) -> Option<Vec<usize>> {
    let mut positive_units = HashMap::new();
    for (index, clause) in clauses.iter().enumerate() {
        if clause.literals.len() == 1 && clause.literals[0].positive {
            positive_units
                .entry(clause.literals[0].clone())
                .or_insert_with(Vec::new)
                .push(index);
        }
    }

    let mut edges = vec![vec![]; clauses.len()];
    let mut indegree = vec![0usize; clauses.len()];
    let mut seen_edges = HashSet::new();
    for (dependent_index, clause) in clauses.iter().enumerate() {
        if clause.literals.len() <= 1 {
            continue;
        }
        for literal in &clause.literals {
            if literal.positive {
                continue;
            }
            let support_literal = literal.negate();
            let Some(support_indices) = positive_units.get(&support_literal) else {
                continue;
            };
            for &support_index in support_indices {
                if support_index <= dependent_index {
                    continue;
                }
                if seen_edges.insert((support_index, dependent_index)) {
                    edges[support_index].push(dependent_index);
                    indegree[dependent_index] += 1;
                }
            }
        }
    }
    for (dependent_index, clause) in clauses.iter().enumerate() {
        if clause.literals.len() != 1 {
            continue;
        }
        let dependent_literal = &clause.literals[0];
        for (support_index, support_clause) in clauses.iter().enumerate() {
            if support_index <= dependent_index || support_clause.literals.len() <= 1 {
                continue;
            }
            if !support_clause
                .literals
                .iter()
                .any(|literal| literal == dependent_literal)
            {
                continue;
            }
            if seen_edges.insert((support_index, dependent_index)) {
                edges[support_index].push(dependent_index);
                indegree[dependent_index] += 1;
            }
        }
    }
    if seen_edges.is_empty() {
        return None;
    }

    let mut ready = BTreeSet::new();
    for (index, degree) in indegree.iter().enumerate() {
        if *degree == 0 {
            ready.insert(index);
        }
    }

    let mut ordered_indices = Vec::with_capacity(clauses.len());
    while let Some(index) = ready.pop_first() {
        ordered_indices.push(index);
        for &dependent in &edges[index] {
            indegree[dependent] -= 1;
            if indegree[dependent] == 0 {
                ready.insert(dependent);
            }
        }
    }

    if ordered_indices.len() != clauses.len() {
        return None;
    }
    if ordered_indices
        .iter()
        .enumerate()
        .all(|(new_index, old_index)| new_index == *old_index)
    {
        return None;
    }

    Some(ordered_indices)
}

use crate::atom::{Atom, AtomId};
use crate::clause::Clause;
use crate::literal::Literal;
use crate::term::{Term, TypeId};
use std::fmt;

// A VariableMap maintains a mapping from variables to terms, allowing us to turn a more general term
// into a more specific one by substituting variables.
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct VariableMap {
    map: Vec<Option<Term>>,
}

impl VariableMap {
    pub fn new() -> VariableMap {
        VariableMap { map: Vec::new() }
    }

    /// Returns the maximum variable index in any of the mapped terms, or None if there are no variables.
    pub fn max_output_variable(&self) -> Option<AtomId> {
        let mut max: Option<AtomId> = None;
        for opt_term in &self.map {
            if let Some(term) = opt_term {
                if let Some(term_max) = term.max_variable() {
                    max = Some(match max {
                        None => term_max,
                        Some(current_max) => current_max.max(term_max),
                    });
                }
            }
        }
        max
    }

    pub fn get_mapping(&self, i: AtomId) -> Option<&Term> {
        let i = i as usize;
        if i >= self.map.len() {
            None
        } else {
            self.map[i].as_ref()
        }
    }

    pub fn match_var(&mut self, var_id: AtomId, special_term: &Term) -> bool {
        let var_id = var_id as usize;
        if var_id >= self.map.len() {
            self.map.resize(var_id + 1, None);
        }
        match &self.map[var_id] {
            None => {
                self.map[var_id] = Some(special_term.clone());
                true
            }
            Some(general_term) => general_term == special_term,
        }
    }

    fn match_atoms(&mut self, atom_type: TypeId, general: &Atom, special: &Atom) -> bool {
        if let Atom::Variable(i) = general {
            self.match_var(*i, &Term::atom(atom_type, *special))
        } else {
            general == special
        }
    }

    pub fn match_terms(&mut self, general: &Term, special: &Term) -> bool {
        if general.get_term_type() != special.get_term_type() {
            return false;
        }

        // Handle the case where a general variable is being mapped to the whole term
        if let Some(i) = general.atomic_variable() {
            return self.match_var(i, special);
        }

        // These checks mean we won't catch higher-order functions whose head types don't match.
        if general.head_type != special.head_type {
            return false;
        }
        if general.args.len() != special.args.len() {
            return false;
        }

        if !self.match_atoms(general.head_type, &general.head, &special.head) {
            return false;
        }

        for (g, s) in general.args.iter().zip(special.args.iter()) {
            if !self.match_terms(g, s) {
                return false;
            }
        }
        true
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn get(&self, i: usize) -> Option<&Term> {
        self.map.get(i).and_then(|opt| opt.as_ref())
    }

    pub fn set(&mut self, i: AtomId, term: Term) {
        let i = i as usize;
        if i >= self.map.len() {
            self.map.resize(i + 1, None);
        }
        self.map[i] = Some(term);
    }

    pub fn has_mapping(&self, i: AtomId) -> bool {
        let i = i as usize;
        i < self.map.len() && self.map[i].is_some()
    }

    pub fn iter(&self) -> impl Iterator<Item = (usize, &Term)> {
        self.map
            .iter()
            .enumerate()
            .filter_map(|(i, opt)| opt.as_ref().map(|term| (i, term)))
    }

    pub fn apply_to_all<F>(&mut self, mut f: F)
    where
        F: FnMut(&Term) -> Term,
    {
        for opt in &mut self.map {
            if let Some(term) = opt {
                *term = f(term);
            }
        }
    }

    pub fn push_none(&mut self) {
        self.map.push(None);
    }

    /// This does not normalize.
    /// Unmapped variables are kept as-is.
    fn specialize_term(&self, term: &Term) -> Term {
        // First apply to the head
        let mut answer = match &term.head {
            Atom::Variable(i) => {
                // Check if we have a mapping for this variable
                if let Some(replacement) = self.get_mapping(*i) {
                    // Expand the head to a full term.
                    // Its term type isn't correct, though.
                    Term::new(
                        term.get_term_type(),
                        replacement.head_type,
                        replacement.head,
                        replacement.args.clone(),
                    )
                } else {
                    // Keep the variable as-is if unmapped
                    Term::new(term.get_term_type(), term.head_type, term.head, Vec::new())
                }
            }
            head => Term::new(term.get_term_type(), term.head_type, *head, Vec::new()),
        };

        // Recurse on the arguments
        for arg in &term.args {
            answer.push_arg(self.specialize_term(arg));
        }

        answer
    }

    /// This does not normalize.
    /// Unmapped variables are kept as-is.
    fn specialize_literal(&self, literal: &Literal) -> Literal {
        Literal::new(
            literal.positive,
            self.specialize_term(&literal.left),
            self.specialize_term(&literal.right),
        )
    }

    /// This does not normalize.
    /// Unmapped variables are kept as-is.
    pub fn specialize_clause(&self, clause: &Clause) -> Clause {
        let literals = clause
            .literals
            .iter()
            .map(|lit| self.specialize_literal(lit))
            .collect();
        Clause { literals }
    }

    pub fn output_has_any_variable(&self) -> bool {
        for term in &self.map {
            if let Some(term) = term {
                if term.has_any_variable() {
                    return true;
                }
            }
        }
        false
    }
}

impl fmt::Display for VariableMap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        let mut first = true;
        for (i, term) in self.iter() {
            if !first {
                write!(f, ", ")?;
            }
            write!(f, "x{} -> {}", i, term)?;
            first = false;
        }
        write!(f, ")")
    }
}

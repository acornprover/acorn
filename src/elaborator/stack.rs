use std::collections::HashMap;

use crate::elaborator::acorn_type::AcornType;
use crate::kernel::atom::AtomId;

/// A representation of the variables on the stack.
///
/// This uses "de Bruijn levels" (not "de Bruijn indices"). The difference:
/// - De Bruijn indices: Variable(0) is the innermost/most-recent binder
/// - De Bruijn levels: Variable(0) is the outermost/first binder (what we use)
///
/// When a new variable is inserted, it gets index = current stack length.
/// So the first variable inserted gets index 0, the second gets index 1, etc.
/// This means when you add a wrapper binder around an expression, all existing
/// variable references need to be shifted up (see insert_stack in acorn_value.rs).
pub struct Stack {
    /// Maps the name of the variable to their level and their type.
    vars: HashMap<String, (AtomId, AcornType)>,
}

impl Stack {
    pub fn new() -> Self {
        Stack {
            vars: HashMap::new(),
        }
    }

    pub fn names(&self) -> Vec<&str> {
        let mut answer: Vec<&str> = vec![""; self.vars.len()];
        for (name, (i, _)) in &self.vars {
            answer[*i as usize] = name;
        }
        answer
    }

    pub fn insert(&mut self, name: String, acorn_type: AcornType) -> AtomId {
        let i = self.vars.len() as AtomId;
        self.vars.insert(name, (i, acorn_type));
        i
    }

    pub fn len(&self) -> usize {
        self.vars.len()
    }

    pub fn remove(&mut self, name: &str) {
        self.vars.remove(name);
    }

    pub fn remove_all(&mut self, names: &[String]) {
        for name in names {
            self.remove(name);
        }
    }

    /// Returns the depth and type of the variable with this name.
    pub fn get(&self, name: &str) -> Option<&(AtomId, AcornType)> {
        self.vars.get(name)
    }
}

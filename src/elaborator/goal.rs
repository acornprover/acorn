use std::fmt;
use std::sync::Arc;

use crate::code_generator::CodeGenerator;
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::environment::Environment;
use crate::elaborator::proposition::Proposition;
use crate::module::ModuleId;

// A goal along with some information related to it.
#[derive(Clone, Debug)]
pub struct Goal {
    pub module_id: ModuleId,

    // A normalized form of the goal.
    pub name: String,

    // The proposition to be proved.
    pub proposition: Arc<Proposition>,

    // An optional theorem-alias form for this goal, e.g. `thm(args...)`.
    // This is used for internal theorem-block goals, where proving the theorem body
    // can also be viewed as refuting the theorem alias directly.
    pub theorem_alias: Option<AcornValue>,

    // Whether it's okay if we discover an inconsistency in the provided facts.
    // If it's not okay, we warn the user.
    pub inconsistency_okay: bool,

    // This range includes the entire proof block for this goal, if there is one.
    pub first_line: u32,
    pub last_line: u32,
}

impl fmt::Display for Goal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.proposition)
    }
}

impl Goal {
    /// Creates a new Goal with the given parameters.
    fn new(
        env: &Environment,
        prop: Arc<Proposition>,
        theorem_alias: Option<AcornValue>,
        first_line: u32,
        last_line: u32,
    ) -> Result<Goal, String> {
        if !prop.params.is_empty() {
            return Err(format!(
                "goals must be concrete, but this goal still has type parameters: {}",
                prop
            ));
        }
        if prop.value.has_generic() {
            return Err(format!(
                "goals must be concrete, but this goal still has generic type variables: {}",
                prop.value
            ));
        }

        let name = if let Some(name) = prop.theorem_name() {
            name.to_string()
        } else {
            CodeGenerator::new(&env.bindings)
                .value_to_code(&prop.value)
                .map_err(|e| e.to_string())?
        };

        Ok(Goal {
            module_id: env.module_id,
            name,
            proposition: prop,
            theorem_alias,
            inconsistency_okay: env.includes_explicit_false || env.will_include_explicit_false,
            first_line,
            last_line,
        })
    }

    /// Creates a Goal for a block that has a goal.
    pub fn block(env: &Environment, prop: Arc<Proposition>) -> Result<Goal, String> {
        let first_line = env.first_line;
        let last_line = env.last_line();
        Self::new(env, prop, None, first_line, last_line)
    }

    /// Creates a Goal for a proposition that is inside a block (or standalone).
    pub fn interior(
        env: &Environment,
        prop: Arc<Proposition>,
        theorem_alias: Option<AcornValue>,
    ) -> Result<Goal, String> {
        let first_line = prop.source.range.start.line;
        let last_line = prop.source.range.end.line;
        Self::new(env, prop, theorem_alias, first_line, last_line)
    }
}

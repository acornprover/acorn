use std::{fmt, path::PathBuf};

use serde::{Deserialize, Serialize};

use crate::elaborator::environment::Environment;
use crate::elaborator::error;

// The code in one file is exposed to other Acorn code as a "module".
// You could have two different types both named "MyStruct" but defined in different places.
// Each name is uniquely identified not just by its string name, but also by the module it's defined in.
// When you look at the AcornType object, they should have each have a different ModuleId.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize, Default,
)]
pub struct ModuleId(pub u16);

impl ModuleId {
    /// The prelude module always gets ID 0.
    /// Note: Default::default() also returns ModuleId(0), which equals PRELUDE.
    pub const PRELUDE: ModuleId = ModuleId(0);

    pub const fn get(&self) -> u16 {
        self.0
    }
}

impl fmt::Display for ModuleId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.get())
    }
}

pub struct Module {
    // The way the user can refer to this module.
    pub descriptor: ModuleDescriptor,

    // The state of the module, whether it's been loaded or not.
    pub state: LoadState,

    // A simple blake3 hash of just the file contents.
    // None before the module is loaded.
    pub hash: Option<blake3::Hash>,
}

impl Module {
    pub fn anonymous() -> Module {
        Module {
            descriptor: ModuleDescriptor::Anonymous,
            state: LoadState::None,
            hash: None,
        }
    }

    // New modules start in the Loading state.
    pub fn new(descriptor: ModuleDescriptor) -> Module {
        Module {
            descriptor,
            state: LoadState::Loading,
            hash: None,
        }
    }

    // Pre-registered modules start in the Registered state.
    // They have an assigned ID but haven't been loaded yet.
    pub fn new_registered(descriptor: ModuleDescriptor) -> Module {
        Module {
            descriptor,
            state: LoadState::Registered,
            hash: None,
        }
    }

    pub fn load_error(&mut self, error: error::Error) {
        self.state = LoadState::Error(error);
    }

    // Called when a module load succeeds.
    pub fn load_ok(&mut self, env: Environment, content_hash: blake3::Hash) {
        self.state = LoadState::Ok(env);
        self.hash = Some(content_hash);
    }

    pub fn name(&self) -> Option<String> {
        match &self.descriptor {
            ModuleDescriptor::Name(parts) => Some(parts.join(".")),
            _ => None,
        }
    }
}

// The LoadState describes the state of a module, loaded or not or in progress.
pub enum LoadState {
    // There is no such module, not even an id for it
    None,

    // The module has been assigned an ID but hasn't been loaded yet.
    // Used during pre-registration to ensure stable ModuleIds.
    Registered,

    // The module is in the process of being loaded.
    Loading,

    // The module has been loaded, but there is an error in its code
    Error(error::Error),

    // The module has been loaded successfully and we have its environment
    Ok(Environment),
}

// A Descriptor expresses the different ways that a module user can specify a module.
#[derive(Debug, PartialEq, Eq, Hash, Clone, PartialOrd, Ord)]
pub enum ModuleDescriptor {
    // Anything that can't be referred to
    Anonymous,

    // An import chain like foo.bar.baz
    // This sort of module can be either loaded by a project, or referred to in code.
    Name(Vec<String>),

    // A filename.
    // This sort of module can be loaded by a project, but not referred to in code.
    File(PathBuf),
}

impl ModuleDescriptor {
    /// Helper to create a Name descriptor by splitting a string on dots
    pub fn name(s: &str) -> Self {
        ModuleDescriptor::Name(s.split('.').map(|part| part.to_string()).collect())
    }

    /// Returns true if this is a top-level module that can be imported with just "import x".
    /// These are Name descriptors with a single part.
    pub fn is_top_level(&self) -> bool {
        match self {
            ModuleDescriptor::Name(parts) => parts.len() == 1,
            _ => false,
        }
    }

    /// Returns true if this module has an authoritative name for the given type or typeclass name.
    /// A module is authoritative if its name (stripped of underscores) matches
    /// the lowercased type or typeclass name.
    pub fn is_authoritative_name(&self, name: &str) -> bool {
        match self {
            ModuleDescriptor::Name(parts) => {
                let cleaned_module = parts.join("").replace('_', "");
                let cleaned_name = name.to_lowercase();
                cleaned_module == cleaned_name
            }
            _ => false,
        }
    }
}

impl fmt::Display for ModuleDescriptor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            ModuleDescriptor::Anonymous => write!(f, "<anonymous>"),
            ModuleDescriptor::Name(parts) => write!(f, "{}", parts.join(".")),
            ModuleDescriptor::File(path) => write!(f, "{}", path.display()),
        }
    }
}

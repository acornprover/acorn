use std::fmt;

use tower_lsp::lsp_types::Range;

use crate::module::ModuleId;
use crate::token::Token;

// Errors that happen during compilation.
// We will want to report these along with a location in the source code.
#[derive(Debug)]
pub struct CompilationError {
    // The range of tokens the error occurred at.
    first_token: Token,
    last_token: Token,

    message: String,

    // When you try to import a module that itself had a compilation error, that is an "indirect error".
    // We may or may not want to report these.
    pub indirect: bool,

    // When this is not None, it's a circular import error, when importing the given module.
    // Sort of like an indirect error, but there's no single canonical location.
    // We generally want to report these, they are just hard to describe.
    pub circular: Option<ModuleId>,
}

impl fmt::Display for CompilationError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:\n", self.message)?;
        write!(f, "{}\n", self.first_token.line)?;
        for (i, _) in self.first_token.line.char_indices() {
            let i = i as u32;
            if i < self.first_token.start {
                // This is before the area to highlight.
                write!(f, " ")?;
            } else if self.first_token.line_number == self.last_token.line_number
                && i >= self.last_token.start + self.last_token.len
            {
                // This is after the area to highlight.
                break;
            } else {
                // This is the area to highlight.
                write!(f, "^")?;
            }
        }
        if self.first_token.start as usize >= self.first_token.line.len() {
            // The error is at the end of the line.
            write!(f, "^")?;
        }
        Ok(())
    }
}

impl CompilationError {
    pub fn new(first_token: &Token, last_token: &Token, message: &str) -> Self {
        CompilationError {
            first_token: first_token.clone(),
            last_token: last_token.clone(),
            message: message.to_string(),
            indirect: false,
            circular: None,
        }
    }

    pub fn indirect(first_token: &Token, last_token: &Token, message: &str) -> Self {
        CompilationError {
            first_token: first_token.clone(),
            last_token: last_token.clone(),
            message: message.to_string(),
            indirect: true,
            circular: None,
        }
    }

    pub fn circular(
        module_id: ModuleId,
        first_token: &Token,
        last_token: &Token,
        message: &str,
    ) -> Self {
        CompilationError {
            first_token: first_token.clone(),
            last_token: last_token.clone(),
            message: message.to_string(),
            indirect: false,
            circular: Some(module_id),
        }
    }

    pub fn range(&self) -> Range {
        Range::new(self.first_token.range().start, self.last_token.range().end)
    }
}

pub type Result<T> = std::result::Result<T, CompilationError>;

pub trait ErrorSource {
    fn error(&self, message: &str) -> CompilationError;
}

pub struct PanicOnError;

impl ErrorSource for PanicOnError {
    fn error(&self, message: &str) -> CompilationError {
        panic!("{}", message)
    }
}

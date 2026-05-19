use tower_lsp::lsp_types::Range;

use crate::elaborator::error::{Error, ErrorContext, Result};
use crate::syntax::expression::{Declaration, Expression, Terminator, TypeParamExpr};
use crate::syntax::token::{Token, TokenIter, TokenType};

use ::pretty::{DocAllocator, DocBuilder, Pretty};
use std::fmt;

const PRINT_WIDTH: usize = 60;

mod ast;
mod parse;
mod pretty;

pub use ast::*;

pub(crate) fn parse_body_after_left_brace(
    left_brace: Token,
    tokens: &mut TokenIter,
) -> Result<Body> {
    let (statements, right_brace) = parse::parse_block(tokens, false)?;
    Ok(Body {
        left_brace,
        statements,
        right_brace,
    })
}

use std::collections::BTreeMap;
use std::iter::Peekable;
use std::sync::Arc;
use std::vec::IntoIter;
use std::{fmt, sync::OnceLock};
use tower_lsp::lsp_types::{Position, Range, SemanticTokenType};

use crate::compilation::{CompilationError, ErrorSource, Result};

#[derive(Copy, Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum TokenType {
    Identifier,
    Invalid,
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    LeftBracket,
    RightBracket,
    NewLine,
    Comma,
    Colon,
    Dot,
    RightArrow,
    Not,
    Or,
    And,
    Iff,
    Equals,
    NotEquals,
    GreaterThan,
    LessThan,
    GreaterThanOrEquals,
    LessThanOrEquals,
    Plus,
    Minus,
    Let,
    Axiom,
    Define,
    Theorem,
    Type,
    ForAll,
    Exists,
    If,
    By,
    Function,
    Structure,
    Import,
    True,
    False,
    Else,
    Class,
    Attributes,
    Asterisk,
    Percent,
    Slash,
    Numeral,
    Numerals,
    From,
    Solve,
    Problem,
    Satisfy,
    SelfToken,
    Inductive,
    Match,
    Todo,
    Constraint,
    Implies,
    Typeclass,
    Instance,
    Extends,
    DocComment,
    Lib,
}

// Add a new token here if there's an alphabetical name for it.
pub fn keyword_map() -> &'static BTreeMap<&'static str, TokenType> {
    static KEYWORD_MAP: OnceLock<BTreeMap<&'static str, TokenType>> = OnceLock::new();
    KEYWORD_MAP.get_or_init(|| {
        BTreeMap::from([
            ("let", TokenType::Let),
            ("axiom", TokenType::Axiom),
            ("define", TokenType::Define),
            ("theorem", TokenType::Theorem),
            ("type", TokenType::Type),
            ("forall", TokenType::ForAll),
            ("exists", TokenType::Exists),
            ("if", TokenType::If),
            ("by", TokenType::By),
            ("function", TokenType::Function),
            ("structure", TokenType::Structure),
            ("import", TokenType::Import),
            ("true", TokenType::True),
            ("false", TokenType::False),
            ("else", TokenType::Else),
            ("class", TokenType::Class),
            ("attributes", TokenType::Attributes),
            ("numerals", TokenType::Numerals),
            ("from", TokenType::From),
            ("solve", TokenType::Solve),
            ("problem", TokenType::Problem),
            ("satisfy", TokenType::Satisfy),
            ("and", TokenType::And),
            ("or", TokenType::Or),
            ("not", TokenType::Not),
            ("self", TokenType::SelfToken),
            ("inductive", TokenType::Inductive),
            ("match", TokenType::Match),
            ("todo", TokenType::Todo),
            ("constraint", TokenType::Constraint),
            ("implies", TokenType::Implies),
            ("typeclass", TokenType::Typeclass),
            ("instance", TokenType::Instance),
            ("extends", TokenType::Extends),
            ("iff", TokenType::Iff),
            ("lib", TokenType::Lib),
        ])
    })
}

// This doesn't handle "Bool".
pub fn keywords_with_prefix(prefix: &str) -> impl Iterator<Item = &str> {
    keyword_map()
        .range(prefix..)
        .take_while(move |(key, _)| key.starts_with(prefix))
        .map(|(key, _)| *key)
}

// The token types that we export via the language server protocol
pub const LSP_TOKEN_TYPES: &[SemanticTokenType] = &[
    SemanticTokenType::VARIABLE,
    SemanticTokenType::COMMENT,
    SemanticTokenType::KEYWORD,
    SemanticTokenType::OPERATOR,
    SemanticTokenType::NUMBER,
];

// Infix operators are represented by a "magic method", where you implement a method
// with that name, and then the infix operator with this token can be used to invoke that method.
// The term "magic method", along with this general idea, are from Python.
const INFIX_MAGIC_METHODS: &[(&str, TokenType)] = &[
    ("gt", TokenType::GreaterThan),
    ("lt", TokenType::LessThan),
    ("gte", TokenType::GreaterThanOrEquals),
    ("lte", TokenType::LessThanOrEquals),
    ("add", TokenType::Plus),
    ("sub", TokenType::Minus),
    ("mul", TokenType::Asterisk),
    ("mod", TokenType::Percent),
    ("div", TokenType::Slash),
];

// Prefix operators.
const PREFIX_MAGIC_METHODS: &[(&str, TokenType)] = &[("neg", TokenType::Minus)];

impl TokenType {
    pub fn is_unary(&self) -> bool {
        match self {
            TokenType::Not => true,
            TokenType::Minus => true,
            _ => false,
        }
    }

    pub fn is_binary(&self) -> bool {
        match self {
            TokenType::Plus => true,
            TokenType::Minus => true,
            TokenType::RightArrow => true,
            TokenType::Or => true,
            TokenType::And => true,
            TokenType::Iff => true,
            TokenType::Equals => true,
            TokenType::NotEquals => true,
            TokenType::GreaterThan => true,
            TokenType::LessThan => true,
            TokenType::GreaterThanOrEquals => true,
            TokenType::LessThanOrEquals => true,
            TokenType::Comma => true,
            TokenType::Colon => true,
            TokenType::Dot => true,
            TokenType::Asterisk => true,
            TokenType::Percent => true,
            TokenType::Slash => true,
            TokenType::Implies => true,
            _ => false,
        }
    }

    // Associative operators don't have to be parenthesized in a sequence because it doesn't matter.
    pub fn always_associative(&self) -> bool {
        match self {
            TokenType::Comma => true,
            _ => false,
        }
    }

    // The precedence of a binary operator.
    // Higher precedence operators are bound to arguments first.
    // Operators that are not allowed in an expression have a precedence of 0.
    // "Value" expressions also include "declarations" which is why colons are allowed.
    // Function application implicitly has the same precedence as dot.
    pub fn binary_precedence(&self) -> i8 {
        match self {
            TokenType::Dot => 14,
            TokenType::Asterisk => 12,
            TokenType::Slash => 12,
            TokenType::Plus => 11,
            TokenType::Minus => 11,
            TokenType::Percent => 10,
            TokenType::GreaterThan => 9,
            TokenType::LessThan => 8,
            TokenType::GreaterThanOrEquals => 8,
            TokenType::LessThanOrEquals => 8,
            TokenType::Equals => 7,
            TokenType::NotEquals => 7,
            TokenType::Or => 5,
            TokenType::And => 5,
            TokenType::Iff => 4,
            TokenType::RightArrow => 3,
            TokenType::Implies => 3,
            TokenType::Colon => 2,
            TokenType::Comma => 1,
            _ => 0,
        }
    }

    // The precedence of a unary operator.
    pub fn unary_precedence(&self) -> i8 {
        match self {
            TokenType::Not => 6,
            TokenType::Minus => 13,
            _ => 0,
        }
    }

    // Whether we put a space to the left of this binary operator in the canonical style.
    pub fn left_space(&self) -> bool {
        match self {
            TokenType::Dot => false,
            TokenType::Comma => false,
            TokenType::Colon => false,
            _ => true,
        }
    }

    // Whether we put a space to the right of this binary operator in the canonical style.
    pub fn right_space(&self) -> bool {
        match self {
            TokenType::Dot => false,
            _ => true,
        }
    }

    pub fn is_binder(&self) -> bool {
        match self {
            TokenType::ForAll => true,
            TokenType::Exists => true,
            TokenType::Function => true,
            _ => false,
        }
    }

    // Converts a token to its infix magic method name, if it has one.
    pub fn to_infix_magic_method_name(&self) -> Option<&str> {
        for (name, token_type) in INFIX_MAGIC_METHODS {
            if token_type == self {
                return Some(name);
            }
        }
        None
    }

    pub fn to_prefix_magic_method_name(&self) -> Option<&str> {
        for (name, token_type) in PREFIX_MAGIC_METHODS {
            if token_type == self {
                return Some(name);
            }
        }
        None
    }

    // Converting the other way, from a (potential) magic method name to a token.
    pub fn from_infix_magic_method_name(name: &str) -> Option<TokenType> {
        for (method_name, token_type) in INFIX_MAGIC_METHODS {
            if method_name == &name {
                return Some(*token_type);
            }
        }
        None
    }

    pub fn from_prefix_magic_method_name(name: &str) -> Option<TokenType> {
        for (method_name, token_type) in PREFIX_MAGIC_METHODS {
            if method_name == &name {
                return Some(*token_type);
            }
        }
        None
    }

    pub fn is_magic_method_name(name: &str) -> bool {
        TokenType::from_infix_magic_method_name(name).is_some()
            || TokenType::from_prefix_magic_method_name(name).is_some()
    }

    // A token created without a line.
    // This is used for code generation, when we have an expression and then we wish to create
    // code for it.
    pub fn new_token(self, text: &str) -> Token {
        let len = text.len() as u32;
        Token {
            token_type: self,
            line: Arc::new(text.to_string()),
            line_number: 0,
            start: 0,
            len,
        }
    }

    // Used for code generation.
    pub fn to_str(&self) -> &str {
        match self {
            TokenType::Identifier => "<identifier>",
            TokenType::Invalid => "<invalid>",
            TokenType::LeftParen => "(",
            TokenType::RightParen => ")",
            TokenType::LeftBrace => "{",
            TokenType::RightBrace => "}",
            TokenType::LeftBracket => "[",
            TokenType::RightBracket => "]",
            TokenType::NewLine => "\n",
            TokenType::Comma => ",",
            TokenType::Colon => ":",
            TokenType::Dot => ".",
            TokenType::RightArrow => "->",
            TokenType::Not => "not",
            TokenType::Or => "or",
            TokenType::And => "and",
            TokenType::Iff => "iff",
            TokenType::Equals => "=",
            TokenType::NotEquals => "!=",
            TokenType::GreaterThan => ">",
            TokenType::LessThan => "<",
            TokenType::GreaterThanOrEquals => ">=",
            TokenType::LessThanOrEquals => "<=",
            TokenType::Plus => "+",
            TokenType::Minus => "-",
            TokenType::Let => "let",
            TokenType::Axiom => "axiom",
            TokenType::Define => "define",
            TokenType::Theorem => "theorem",
            TokenType::Type => "type",
            TokenType::ForAll => "forall",
            TokenType::Exists => "exists",
            TokenType::If => "if",
            TokenType::By => "by",
            TokenType::Function => "function",
            TokenType::Structure => "structure",
            TokenType::Import => "import",
            TokenType::True => "true",
            TokenType::False => "false",
            TokenType::Else => "else",
            TokenType::Class => "class",
            TokenType::Attributes => "attributes",
            TokenType::Asterisk => "*",
            TokenType::Percent => "%",
            TokenType::Slash => "/",
            TokenType::Numeral => "<numeral>",
            TokenType::Numerals => "numerals",
            TokenType::From => "from",
            TokenType::Solve => "solve",
            TokenType::Problem => "problem",
            TokenType::Satisfy => "satisfy",
            TokenType::SelfToken => "self",
            TokenType::Inductive => "inductive",
            TokenType::Match => "match",
            TokenType::Todo => "todo",
            TokenType::Constraint => "constraint",
            TokenType::Implies => "implies",
            TokenType::Typeclass => "typeclass",
            TokenType::Instance => "instance",
            TokenType::Extends => "extends",
            TokenType::DocComment => "///",
            TokenType::Lib => "lib",
        }
    }

    // Used to create error messages.
    pub fn describe(&self) -> String {
        match self {
            TokenType::Identifier => "identifier".to_string(),
            TokenType::Invalid => "invalid".to_string(),
            TokenType::NewLine => "newline".to_string(),
            TokenType::Numeral => "number".to_string(),
            _ => format!("\"{}\"", self.to_str()),
        }
    }

    pub fn generate(self) -> Token {
        self.new_token(self.to_str())
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Token {
    pub token_type: TokenType,

    // The entire line containing this token.
    pub line: Arc<String>,

    // The index of this line within the document.
    pub line_number: u32,

    // The index where this token starts, within the line.
    pub start: u32,

    // The length of this token.
    pub len: u32,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.text())
    }
}

impl ErrorSource for Token {
    fn error(&self, message: &str) -> CompilationError {
        CompilationError::new(self, self, message)
    }
}

impl Token {
    // A token to represent an empty file.
    pub fn empty() -> Self {
        Token {
            token_type: TokenType::NewLine,
            line: Arc::new("".to_string()),
            line_number: 0,
            start: 0,
            len: 0,
        }
    }

    pub fn text(&self) -> &str {
        let start = self.start as usize;
        let end = (self.start + self.len) as usize;
        &self.line[start..end]
    }

    /// Checks if a given identifier name is reserved for system use.
    pub fn is_reserved_name(name: &str) -> bool {
        name == "new" || name == "self" || name == "induction" || name == "constraint"
    }

    /// Checks if this token is a reserved name.
    /// Returns an error if it is reserved.
    pub fn check_not_reserved(&self) -> Result<()> {
        if Self::is_reserved_name(self.text()) {
            return Err(self.error(&format!(
                "'{}' is a reserved word. use a different name",
                self.text()
            )));
        }
        Ok(())
    }

    pub fn start_pos(&self) -> Position {
        Position {
            line: self.line_number,
            character: self.start,
        }
    }

    // One spot after the last character in the token.
    pub fn end_pos(&self) -> Position {
        Position {
            line: self.line_number,
            character: (self.start + self.len),
        }
    }

    pub fn range(&self) -> Range {
        Range {
            start: self.start_pos(),
            end: self.end_pos(),
        }
    }

    pub fn binary_precedence(&self) -> i8 {
        self.token_type.binary_precedence()
    }

    pub fn unary_precedence(&self) -> i8 {
        self.token_type.unary_precedence()
    }

    pub fn identifierish(ch: char) -> bool {
        ch.is_alphanumeric() || ch == '_'
    }

    /// Extracts the content from a doc comment token.
    /// Removes the leading "///" and at most one space after it.
    /// Returns an empty string if this is not a doc comment token.
    pub fn doc_comment_content(&self) -> String {
        if self.token_type != TokenType::DocComment {
            return String::new();
        }

        let text = self.text();
        if text.starts_with("///") {
            let after_slash = &text[3..];
            // Remove at most one space from the beginning
            if after_slash.starts_with(' ') {
                after_slash[1..].to_string()
            } else {
                after_slash.to_string()
            }
        } else {
            text.to_string()
        }
    }

    pub fn lsp_type(&self) -> Option<SemanticTokenType> {
        match self.token_type {
            TokenType::Identifier => Some(SemanticTokenType::VARIABLE),

            TokenType::RightArrow
            | TokenType::Iff
            | TokenType::Equals
            | TokenType::NotEquals
            | TokenType::GreaterThan
            | TokenType::LessThan
            | TokenType::GreaterThanOrEquals
            | TokenType::LessThanOrEquals
            | TokenType::Plus
            | TokenType::Minus
            | TokenType::Asterisk
            | TokenType::Percent
            | TokenType::Slash => Some(SemanticTokenType::OPERATOR),

            TokenType::Let
            | TokenType::Axiom
            | TokenType::Define
            | TokenType::Theorem
            | TokenType::Type
            | TokenType::ForAll
            | TokenType::Exists
            | TokenType::If
            | TokenType::By
            | TokenType::Function
            | TokenType::Structure
            | TokenType::Import
            | TokenType::True
            | TokenType::False
            | TokenType::Else
            | TokenType::Class
            | TokenType::Attributes
            | TokenType::Numerals
            | TokenType::From
            | TokenType::Solve
            | TokenType::Problem
            | TokenType::Satisfy
            | TokenType::Not
            | TokenType::Or
            | TokenType::And
            | TokenType::SelfToken
            | TokenType::Inductive
            | TokenType::Match
            | TokenType::Todo
            | TokenType::Constraint
            | TokenType::Implies
            | TokenType::Typeclass
            | TokenType::Instance
            | TokenType::Extends
            | TokenType::Lib => Some(SemanticTokenType::KEYWORD),

            TokenType::NewLine => {
                // Regular comments are encoded as newlines because they act like newlines.
                if self.len > 1 {
                    Some(SemanticTokenType::COMMENT)
                } else {
                    None
                }
            }

            TokenType::DocComment => Some(SemanticTokenType::COMMENT),

            TokenType::Numeral => Some(SemanticTokenType::NUMBER),

            TokenType::Comma
            | TokenType::Invalid
            | TokenType::LeftParen
            | TokenType::RightParen
            | TokenType::LeftBrace
            | TokenType::RightBrace
            | TokenType::LeftBracket
            | TokenType::RightBracket
            | TokenType::Colon
            | TokenType::Dot => None,
        }
    }

    // Convert the lsp type to a u32 for the language server protocol.
    pub fn lsp_type_u32(&self) -> Option<u32> {
        let lsp_type = self.lsp_type()?;
        LSP_TOKEN_TYPES
            .iter()
            .position(|t| t == &lsp_type)
            .map(|i| i as u32)
    }

    // If there is an error in scanning, there will be one or more InvalidToken in the result.
    // scanning always puts a NewLine token at the end of the input.
    pub fn scan(input: &str) -> Vec<Token> {
        Self::scan_with_start_line(input, 0)
    }

    pub fn scan_with_start_line(input: &str, start_line: u32) -> Vec<Token> {
        let mut tokens = Vec::new();
        for (line_offset, line) in input.lines().enumerate() {
            let line_number = start_line + line_offset as u32;
            let rc_line = Arc::new(line.to_string());
            let mut line_all_whitespace_so_far = true;
            let mut char_indices = line.char_indices().peekable();
            while let Some((char_index, ch)) = char_indices.next() {
                let token_type = match ch {
                    ' ' => continue,
                    '\t' => continue,
                    '(' => TokenType::LeftParen,
                    ')' => TokenType::RightParen,
                    '{' => TokenType::LeftBrace,
                    '}' => TokenType::RightBrace,
                    '[' => TokenType::LeftBracket,
                    ']' => TokenType::RightBracket,
                    '\n' => TokenType::NewLine,
                    ',' => TokenType::Comma,
                    ':' => TokenType::Colon,
                    '.' => TokenType::Dot,
                    '!' => match char_indices.next_if_eq(&(char_index + 1, '=')) {
                        Some(_) => TokenType::NotEquals,
                        None => TokenType::Invalid,
                    },
                    '=' => TokenType::Equals,
                    '+' => TokenType::Plus,
                    '*' => TokenType::Asterisk,
                    '%' => TokenType::Percent,
                    '-' => match char_indices.next_if_eq(&(char_index + 1, '>')) {
                        Some(_) => TokenType::RightArrow,
                        None => TokenType::Minus,
                    },
                    '<' => match char_indices.next_if_eq(&(char_index + 1, '=')) {
                        Some(_) => TokenType::LessThanOrEquals,
                        None => TokenType::LessThan,
                    },
                    '>' => match char_indices.next_if_eq(&(char_index + 1, '=')) {
                        Some(_) => TokenType::GreaterThanOrEquals,
                        None => TokenType::GreaterThan,
                    },
                    '/' => match char_indices.next_if_eq(&(char_index + 1, '/')) {
                        Some(_) => {
                            // Advance to the end of the line
                            let doc_comment =
                                char_indices.next_if_eq(&(char_index + 2, '/')).is_some();
                            while let Some((_, ch)) = char_indices.next() {
                                if ch == '\n' {
                                    break;
                                }
                            }
                            if doc_comment && line_all_whitespace_so_far {
                                TokenType::DocComment
                            } else {
                                TokenType::NewLine
                            }
                        }
                        None => TokenType::Slash,
                    },
                    t if t.is_ascii_digit() => {
                        loop {
                            match char_indices.peek() {
                                Some((_, ch)) if ch.is_ascii_digit() => {
                                    char_indices.next();
                                }
                                _ => break,
                            }
                        }
                        TokenType::Numeral
                    }
                    t if Token::identifierish(t) => {
                        let end = loop {
                            match char_indices.peek() {
                                Some((_, ch)) if Token::identifierish(*ch) => {
                                    char_indices.next();
                                }
                                Some((end, _)) => break *end,
                                None => break line.len(),
                            }
                        };
                        let identifier = &line[char_index..end];
                        match keyword_map().get(identifier) {
                            Some(token_type) => *token_type,
                            None => TokenType::Identifier,
                        }
                    }
                    _ => TokenType::Invalid,
                };
                line_all_whitespace_so_far = false;
                let end = if let Some((pos, _)) = char_indices.peek() {
                    *pos
                } else {
                    line.len()
                };
                let token = Token {
                    token_type,
                    line: rc_line.clone(),
                    line_number,
                    start: char_index as u32,
                    len: (end - char_index) as u32,
                };
                tokens.push(token);
            }

            // Add a newline
            tokens.push(Token {
                token_type: TokenType::NewLine,
                line: rc_line,
                line_number,
                start: line.len() as u32,
                len: 0,
            });
        }

        tokens
    }

    pub fn has_invalid_token(tokens: &[Token]) -> bool {
        for token in tokens {
            if token.token_type == TokenType::Invalid {
                return true;
            }
        }
        false
    }

    pub fn is_type_name(&self) -> bool {
        if self.token_type != TokenType::Identifier {
            return false;
        }
        for (i, char) in self.text().chars().enumerate() {
            if i == 0 {
                if !char.is_ascii_uppercase() {
                    return false;
                }
            } else if !char.is_alphanumeric() {
                return false;
            }
        }
        true
    }

    pub fn expect_type_name(&self) -> Result<()> {
        if !self.is_type_name() {
            return Err(self.error("expected a type name"));
        }
        Ok(())
    }

    /// Creates a test token with the specified position information.
    /// Primarily used for testing token mapping functionality.
    #[cfg(test)]
    pub fn test_token(line_number: u32, start: u32, len: u32) -> Self {
        Token {
            token_type: TokenType::Identifier,
            line: Arc::new("test line".to_string()),
            line_number,
            start,
            len,
        }
    }
}

pub struct TokenIter {
    inner: Peekable<IntoIter<Token>>,

    last: Token,
}

impl TokenIter {
    pub fn new(tokens: Vec<Token>) -> TokenIter {
        let last = tokens.last().cloned().unwrap_or_else(Token::empty);
        TokenIter {
            inner: tokens.into_iter().peekable(),
            last,
        }
    }

    pub fn peek(&mut self) -> Option<&Token> {
        self.inner.peek()
    }

    pub fn peek_type(&mut self) -> Option<TokenType> {
        self.peek().map(|t| t.token_type)
    }

    pub fn next(&mut self) -> Option<Token> {
        self.inner.next()
    }

    pub fn error(&mut self, message: &str) -> CompilationError {
        match self.peek() {
            Some(token) => token.error(message),
            None => self.last.error(message),
        }
    }

    // Pops off one token, expecting it to be there.
    pub fn expect_token(&mut self) -> Result<Token> {
        self.next()
            .ok_or_else(|| self.error("unexpected end of file"))
    }

    // Pops off one token, expecting it to be of a known type.
    pub fn expect_type(&mut self, expected: TokenType) -> Result<Token> {
        let token = match self.next() {
            Some(t) => t,
            None => return Err(self.error("unexpected end of file")),
        };
        if token.token_type != expected {
            return Err(token.error(&format!("expected {:?}", expected)));
        }
        Ok(token)
    }

    // Pops off one token, expecting it to be a variable name.
    pub fn expect_variable_name(&mut self, numeral_ok: bool) -> Result<Token> {
        let name_token = self.expect_token()?;
        match name_token.token_type {
            TokenType::SelfToken => {}
            TokenType::Identifier => match name_token.text().chars().next() {
                Some(c) => {
                    if !c.is_ascii_lowercase() {
                        return Err(name_token.error("invalid variable name"));
                    }
                }
                None => return Err(name_token.error("empty token (probably a bug)")),
            },
            TokenType::Numeral => {
                if !numeral_ok {
                    return Err(name_token.error("did not expect a numeral here"));
                }
            }
            _ => return Err(name_token.error("expected a variable name")),
        }
        Ok(name_token)
    }

    // Pops off one token, expecting it to be a type name.
    pub fn expect_type_name(&mut self) -> Result<Token> {
        let name_token = self.expect_type(TokenType::Identifier)?;
        name_token.expect_type_name()?;
        Ok(name_token)
    }

    // Advance past any newlines.
    pub fn skip_newlines(&mut self) {
        while let Some(token) = self.peek() {
            if token.token_type == TokenType::NewLine {
                self.next();
            } else {
                break;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scanning_ok() {
        assert_eq!(Token::scan("theorem t:A->B").len(), 7);
        assert_eq!(Token::scan("theorem _t:A->B").len(), 7);
    }

    #[test]
    fn test_scanning_errors() {
        let tokens = Token::scan("#$@%(#@)(#");
        assert!(Token::has_invalid_token(&tokens));
    }

    #[test]
    fn test_token_types() {
        let tokens = Token::scan("type Nat: axiom\nlet 0: Nat = axiom");
        assert_eq!(tokens.len(), 12);
        assert_eq!(tokens[3].token_type, TokenType::Axiom);
        assert_eq!(tokens[4].token_type, TokenType::NewLine);
    }
}

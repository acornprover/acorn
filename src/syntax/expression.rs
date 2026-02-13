use std::{collections::VecDeque, fmt};

use pretty::{DocAllocator, DocBuilder, Pretty};
use tower_lsp::lsp_types::Range;

use crate::elaborator::error::{Error, ErrorContext, Result};
use crate::syntax::token::{Token, TokenIter, TokenType};

/// There are two main sorts of expressions.
/// Value expressions, like:
///    1 + 2
/// Type expressions, like:
///    (int, bool) -> bool
///
/// There are other sorts of expressions. Module names, argument lists, type parameters.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum ExpressionType {
    Value,
    Type,
}

/// An Expression represents the basic structuring of tokens into a syntax tree.
/// The expression does not typecheck and enforce semantics; it's just parsing into a tree.
#[derive(Debug)]
pub enum Expression {
    /// A singleton expression is one that consists of just a single token.
    /// This includes identifiers, true, false, numeric literals, and "axiom".
    Singleton(Token),

    /// A unary operator applied to another expression.
    Unary(Token, Box<Expression>),

    /// An infix binary operator, with the left and right expressions.
    Binary(Box<Expression>, Token, Box<Expression>),

    /// Expressions you get by placing two expressions next to each other.
    /// This can either be the application of a function, or a type instantiation.
    /// The second parameter can either be an argument list or a type parameter list.
    Concatenation(Box<Expression>, Box<Expression>),

    /// A grouping like ( <expr> ) or < <expr> >.
    /// The tokens that delimit the grouping are included.
    Grouping(Token, Box<Expression>, Token),

    /// A binder is an expression that binds variables, like a forall/exists/function.
    /// The first token is the binder keyword, like "forall".
    /// The declarations are the argument list, like "(x: Nat, y: Nat)".
    /// The expression is the body block.
    /// The last token is the closing brace.
    Binder(Token, Vec<Declaration>, Box<Expression>, Token),

    /// A generic binder is like a binder but with type parameters.
    /// For example: function[T](x: T) { x }
    /// The first token is the "function" keyword.
    /// The type parameters are the [T, U, ...] list.
    /// The declarations are the value argument list.
    /// The expression is the body block.
    /// The last token is the closing brace.
    GenericBinder(
        Token,
        Vec<TypeParamExpr>,
        Vec<Declaration>,
        Box<Expression>,
        Token,
    ),

    /// If-then-else expressions. The else branch is optional.
    /// The first token is the "if" keyword.
    /// The first expression is the condition.
    /// The second expression is the "if" block.
    /// The third expression is the optional "else" block.
    /// The last token is the closing brace.
    IfThenElse(
        Token,
        Box<Expression>,
        Box<Expression>,
        Option<Box<Expression>>,
        Token,
    ),

    /// The first token is the "match" keyword.
    /// The first expression is the "scrutinee", which we are matching.
    /// The pairs indicate exhaustive and mutually exclusive cases for matching the scrutinee, which
    /// must have an inductive type.
    /// For the pair (exp1, exp2) where exp1 matches the scrutinee, the value of our expression is exp2.
    /// The last token is the closing brace.
    Match(Token, Box<Expression>, Vec<(Expression, Expression)>, Token),
}

impl fmt::Display for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Use the pretty-printing logic in flat mode to force everything on one line
        let allocator = pretty::Arena::<()>::new();
        let doc = self.pretty_ref(&allocator, true);
        // Use render_fmt with a very large width to ensure no line breaks
        doc.render_fmt(usize::MAX, f)?;
        Ok(())
    }
}

impl ErrorContext for Expression {
    fn error(&self, message: &str) -> Error {
        Error::new(self.first_token(), self.last_token(), message)
    }
}

// A single variable declaration, like "p: bool".
#[derive(Debug)]
pub enum Declaration {
    // (name token, type expression)
    Typed(Token, Expression),

    // Just the token 'self'.
    SelfToken(Token),
}

impl fmt::Display for Declaration {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Declaration::Typed(name_token, type_expr) => {
                write!(f, "{}: {}", name_token, type_expr)
            }
            Declaration::SelfToken(token) => write!(f, "{}", token),
        }
    }
}

impl Declaration {
    pub fn token(&self) -> &Token {
        match self {
            Declaration::Typed(token, _) => token,
            Declaration::SelfToken(token) => token,
        }
    }

    // Parses an expression that should contain a single declaration.
    // This rejects numerals.
    // Consumes the terminating token and returns it along with the Declaration.
    pub fn parse(tokens: &mut TokenIter, terminator: Terminator) -> Result<(Declaration, Token)> {
        let name_token = tokens.expect_variable_name(false)?;
        if name_token.text() == "self" {
            let token = tokens.expect_token()?;
            if token.token_type == TokenType::Colon {
                return Err(token.error("no type is needed after 'self'"));
            }
            if !terminator.matches(&token.token_type) {
                return Err(
                    token.error(&format!("expected {} but found \"{}\"", terminator, token))
                );
            }
            return Ok((Declaration::SelfToken(name_token.clone()), token));
        }
        tokens.expect_type(TokenType::Colon)?;
        let (type_expr, token) = Expression::parse_type(tokens, terminator)?;

        Ok((Declaration::Typed(name_token, type_expr), token))
    }

    // Parses a declaration list, after the opening left parenthesis has already been consumed.
    // Consumes a closing right paren.
    // Returns the declarations.
    pub fn parse_list(tokens: &mut TokenIter) -> Result<Vec<Declaration>> {
        let mut declarations = Vec::new();
        tokens.skip_newlines();
        if tokens.peek_type() == Some(TokenType::RightParen) {
            tokens.next();
            return Ok(declarations);
        }
        loop {
            let (declaration, last_token) = Declaration::parse(
                tokens,
                Terminator::Or(TokenType::Comma, TokenType::RightParen),
            )?;
            declarations.push(declaration);
            if last_token.token_type == TokenType::RightParen {
                return Ok(declarations);
            }
            // Skip any newlines after a comma
            tokens.skip_newlines();
        }
    }
}

// A single type parameter that may or may not have a typeclass, like "G: Group".
// Can also represent a complex type expression like "List[Color]" for specific attributes.
#[derive(Debug)]
pub struct TypeParamExpr {
    pub name: Token,

    // For complex type expressions like List[Color]
    // None for simple identifiers like K
    // Some(expr) for complex types
    pub type_expr: Option<Expression>,

    pub typeclass: Option<Expression>,
}

impl fmt::Display for TypeParamExpr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Handle complex type expressions
        let base_str = if let Some(type_expr) = &self.type_expr {
            format!("{}", type_expr)
        } else {
            format!("{}", self.name)
        };

        match &self.typeclass {
            None => write!(f, "{}", base_str),
            Some(typeclass) => write!(f, "{}: {}", base_str, typeclass),
        }
    }
}

impl TypeParamExpr {
    // Parses a type parameter list, if it's there.
    // If the tokens don't start with '[', just return an empty list.
    pub fn parse_list(tokens: &mut TokenIter) -> Result<Vec<TypeParamExpr>> {
        if tokens.peek_type() != Some(TokenType::LeftBracket)
            && tokens.peek_type() != Some(TokenType::LessThan)
        {
            return Ok(vec![]);
        }
        let left_delimiter = tokens.next();
        let mut params = vec![];
        if left_delimiter.clone().unwrap().token_type == TokenType::LessThan {
            loop {
                let name = tokens.expect_type(TokenType::Identifier)?;

                // Check if this is a complex type expression (e.g., List[Color])
                let type_expr = if tokens.peek_type() == Some(TokenType::LeftBracket) {
                    // Parse the nested type parameters
                    let name_expr = Expression::Singleton(name.clone());
                    let left_bracket = tokens.next().unwrap();

                    let (inner_expr, right_bracket) =
                        Expression::parse_type(tokens, Terminator::Is(TokenType::RightBracket))?;

                    let params_expr =
                        Expression::Grouping(left_bracket, Box::new(inner_expr), right_bracket);

                    Some(Expression::Concatenation(
                        Box::new(name_expr),
                        Box::new(params_expr),
                    ))
                } else {
                    None
                };

                let terminator = tokens.expect_token()?;
                let (typeclass, terminator) = if terminator.token_type == TokenType::Colon {
                    let (typeclass, terminator) = Expression::parse_type(
                        tokens,
                        Terminator::Or(TokenType::Comma, TokenType::GreaterThan),
                    )?;
                    (Some(typeclass), terminator)
                } else {
                    (None, terminator)
                };
                params.push(TypeParamExpr {
                    name,
                    type_expr,
                    typeclass,
                });
                match terminator.token_type {
                    TokenType::GreaterThan => {
                        break;
                    }
                    TokenType::Comma => {
                        continue;
                    }
                    _ => {
                        return Err(terminator.error("expected '>' or ',' after each type param"));
                    }
                }
            }
        } else if left_delimiter.clone().unwrap().token_type == TokenType::LeftBracket {
            loop {
                let name = tokens.expect_type(TokenType::Identifier)?;

                // Check if this is a complex type expression (e.g., List[Color])
                let type_expr = if tokens.peek_type() == Some(TokenType::LeftBracket) {
                    // Parse the nested type parameters
                    let name_expr = Expression::Singleton(name.clone());
                    let left_bracket = tokens.next().unwrap();

                    let (inner_expr, right_bracket) =
                        Expression::parse_type(tokens, Terminator::Is(TokenType::RightBracket))?;

                    let params_expr =
                        Expression::Grouping(left_bracket, Box::new(inner_expr), right_bracket);

                    Some(Expression::Concatenation(
                        Box::new(name_expr),
                        Box::new(params_expr),
                    ))
                } else {
                    None
                };

                let terminator = tokens.expect_token()?;
                let (typeclass, terminator) = if terminator.token_type == TokenType::Colon {
                    let (typeclass, terminator) = Expression::parse_type(
                        tokens,
                        Terminator::Or(TokenType::Comma, TokenType::RightBracket),
                    )?;
                    (Some(typeclass), terminator)
                } else {
                    (None, terminator)
                };
                params.push(TypeParamExpr {
                    name,
                    type_expr,
                    typeclass,
                });
                match terminator.token_type {
                    TokenType::RightBracket => {
                        break;
                    }
                    TokenType::Comma => {
                        continue;
                    }
                    _ => {
                        return Err(terminator.error("expected ']' or ',' after each type param"));
                    }
                }
            }
        }
        Ok(params)
    }
}

// We use terminators to tell the expression parser when it is allowed to stop.
// This exists to make error messages more readable.
pub enum Terminator {
    Is(TokenType),
    Or(TokenType, TokenType),
}

impl fmt::Display for Terminator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Terminator::Is(t) => write!(f, "{}", t.describe()),
            Terminator::Or(t1, t2) => write!(f, "{} or {}", t1.describe(), t2.describe()),
        }
    }
}

impl Terminator {
    fn matches(&self, t: &TokenType) -> bool {
        match self {
            Terminator::Is(t1) => t == t1,
            Terminator::Or(t1, t2) => t == t1 || t == t2,
        }
    }
}

impl Expression {
    pub fn first_token(&self) -> &Token {
        match self {
            Expression::Singleton(token) => token,
            Expression::Unary(token, _) => token,
            Expression::Binary(left, _, _) => left.first_token(),
            Expression::Concatenation(left, _) => left.first_token(),
            Expression::Grouping(left_paren, _, _) => left_paren,
            Expression::Binder(token, _, _, _) => token,
            Expression::GenericBinder(token, _, _, _, _) => token,
            Expression::IfThenElse(token, _, _, _, _) => token,
            Expression::Match(token, _, _, _) => token,
        }
    }

    pub fn last_token(&self) -> &Token {
        match self {
            Expression::Singleton(token) => token,
            Expression::Unary(token, subexpression) => {
                if token.token_type.is_postfix() {
                    token
                } else {
                    subexpression.last_token()
                }
            }
            Expression::Binary(_, _, right) => right.last_token(),
            Expression::Concatenation(_, right) => right.last_token(),
            Expression::Grouping(_, _, right_paren) => right_paren,
            Expression::Binder(_, _, _, right_brace) => right_brace,
            Expression::GenericBinder(_, _, _, _, right_brace) => right_brace,
            Expression::IfThenElse(_, _, _, _, right_brace) => right_brace,
            Expression::Match(_, _, _, right_brace) => right_brace,
        }
    }

    pub fn is_axiom(&self) -> bool {
        match self {
            Expression::Singleton(token) => token.token_type == TokenType::Axiom,
            _ => false,
        }
    }

    fn is_grouping(&self) -> bool {
        matches!(self, Expression::Grouping(..))
    }

    pub fn print_one_level(&self) {
        match self {
            Expression::Singleton(token) => {
                println!("Singleton:");
                println!("  token: {}", token);
            }
            Expression::Unary(token, subexpression) => {
                println!("Unary:");
                println!("  token: {}", token);
                println!("  subexpression: {}", subexpression);
            }
            Expression::Binary(left, token, right) => {
                println!("Binary:");
                println!("  token: {}", token);
                println!("  left: {}", left);
                println!("  right: {}", right);
            }
            Expression::Concatenation(left, right) => {
                println!("Concatenation:");
                println!("  left: {}", left);
                println!("  right: {}", right);
            }
            Expression::Grouping(_, e, _) => {
                println!("Grouping:");
                println!("  subexpression: {}", e);
            }
            Expression::Binder(token, args, sub, _) => {
                println!("Binder:");
                println!("  token: {}", token);
                println!("  args: {:?}", args);
                println!("  subexpression: {}", sub);
            }
            Expression::GenericBinder(token, type_params, args, sub, _) => {
                println!("GenericBinder:");
                println!("  token: {}", token);
                println!("  type_params: {:?}", type_params);
                println!("  args: {:?}", args);
                println!("  subexpression: {}", sub);
            }
            Expression::IfThenElse(token, cond, if_block, else_block, _) => {
                println!("IfThenElse:");
                println!("  token: {}", token);
                println!("  cond: {}", cond);
                println!("  if: {}", if_block);
                match else_block {
                    Some(else_expr) => println!("  else: {}", else_expr),
                    None => println!("  else: None"),
                }
            }
            Expression::Match(token, scrutinee, cases, _) => {
                println!("Match:");
                println!("  token: {}", token);
                println!("  scrutinee: {}", scrutinee);
                for (pat, exp) in cases {
                    println!("  case: {} => {}", pat, exp);
                }
            }
        }
    }

    // For code generation. Will not point to a token in any larger document
    pub fn generate_identifier(s: &str) -> Expression {
        Expression::Singleton(TokenType::Identifier.new_token(s))
    }

    pub fn generate_lib() -> Expression {
        Expression::Singleton(TokenType::Lib.new_token("lib"))
    }

    /// Adds ".name"  to an expression.
    pub fn add_dot_str(self, name: &str) -> Expression {
        Expression::generate_dot(self, Expression::generate_identifier(name))
    }

    // Generates a dot-separated chain of identifiers, for the provided parts.
    pub fn generate_identifier_chain(parts: &[&str]) -> Expression {
        let mut answer = Expression::generate_identifier(parts[0]);
        for part in &parts[1..] {
            answer = answer.add_dot_str(part);
        }
        answer
    }

    fn generate_grouping(
        mut exprs: Vec<Expression>,
        left: TokenType,
        right: TokenType,
    ) -> Expression {
        assert_ne!(exprs.len(), 0);
        let mut answer = exprs.remove(0);
        for e in exprs {
            answer = Expression::Binary(Box::new(answer), TokenType::Comma.generate(), Box::new(e));
        }
        Expression::Grouping(left.generate(), Box::new(answer), right.generate())
    }

    // Generates a comma-separated grouping in parentheses
    pub fn generate_paren_grouping(exprs: Vec<Expression>) -> Expression {
        Expression::generate_grouping(exprs, TokenType::LeftParen, TokenType::RightParen)
    }

    // Generate a comma-separated grouping in square brackets
    pub fn generate_params(exprs: Vec<Expression>) -> Expression {
        Expression::generate_grouping(exprs, TokenType::LeftBracket, TokenType::RightBracket)
    }

    // Generates a unary expression, parenthesizing if necessary according to precedence.
    pub fn generate_unary(op: TokenType, mut expr: Expression) -> Expression {
        if expr.top_level_precedence(true) < op.unary_precedence() {
            expr = Expression::Grouping(
                TokenType::LeftParen.generate(),
                Box::new(expr),
                TokenType::RightParen.generate(),
            );
        }
        Expression::Unary(op.generate(), Box::new(expr))
    }

    // Generates a binary expression, parenthesizing if necessary according to precedence.
    pub fn generate_binary(
        mut left: Expression,
        op: TokenType,
        mut right: Expression,
    ) -> Expression {
        if left.top_level_precedence(false) < op.binary_precedence() {
            left = Expression::Grouping(
                TokenType::LeftParen.generate(),
                Box::new(left),
                TokenType::RightParen.generate(),
            );
        }
        if right.top_level_precedence(true) <= op.binary_precedence() {
            right = Expression::Grouping(
                TokenType::LeftParen.generate(),
                Box::new(right),
                TokenType::RightParen.generate(),
            );
        }
        Expression::Binary(Box::new(left), op.generate(), Box::new(right))
    }

    pub fn generate_dot(left: Expression, right: Expression) -> Expression {
        Expression::Binary(Box::new(left), TokenType::Dot.generate(), Box::new(right))
    }

    // Converts this expression to a numeric digit, if possible.
    // Ignores the type.
    pub fn to_digit(&self) -> Option<char> {
        match self {
            Expression::Singleton(token) if token.token_type == TokenType::Numeral => {
                let text = token.text();
                if text.len() == 1 {
                    text.chars().next()
                } else {
                    None
                }
            }
            Expression::Binary(_, token, right) if token.token_type == TokenType::Dot => {
                right.to_digit()
            }
            _ => None,
        }
    }

    // Whether this is a number of any type.
    pub fn is_number(&self) -> bool {
        match self {
            Expression::Singleton(token) => token.token_type == TokenType::Numeral,
            Expression::Binary(_, token, right) if token.token_type == TokenType::Dot => {
                right.is_number()
            }
            _ => false,
        }
    }

    // Appends a digit.
    // 'initial' must be a number.
    pub fn generate_number(initial: Expression, digit: char) -> Expression {
        match initial {
            Expression::Singleton(token) => {
                let mut text = token.text().to_string();
                text.push(digit);
                Expression::Singleton(TokenType::Numeral.new_token(&text))
            }
            Expression::Binary(left, token, right) if token.token_type == TokenType::Dot => {
                let new_right = Expression::generate_number(*right, digit);
                Expression::Binary(left, token, Box::new(new_right))
            }
            _ => panic!("expected a number"),
        }
    }

    // The precedence this expression uses at the top level.
    // In some situations, unary operators will be parsed regardless of precedence, so they essentially
    // use maximum precedence. In this situation `unary_counts_as_max` is true.
    pub fn top_level_precedence(&self, unary_counts_as_max: bool) -> i8 {
        match self {
            Expression::Singleton(_)
            | Expression::Grouping(..)
            | Expression::Binder(..)
            | Expression::GenericBinder(..)
            | Expression::IfThenElse(..)
            | Expression::Match(..) => {
                // These expressions never need to be parenthesized.
                i8::MAX
            }
            Expression::Unary(token, _) => {
                if unary_counts_as_max {
                    i8::MAX
                } else {
                    token.unary_precedence()
                }
            }
            Expression::Binary(_, token, _) => token.binary_precedence(),
            Expression::Concatenation(..) => TokenType::Dot.binary_precedence(),
        }
    }

    // If this expression is of the form "premise -> conclusion", return the premise.
    pub fn premise(&self) -> Option<&Expression> {
        match self {
            Expression::Grouping(_, e, _) => e.premise(),
            Expression::Binary(left, token, _) => {
                if token.token_type == TokenType::RightArrow {
                    Some(left)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    pub fn range(&self) -> Range {
        Range {
            start: self.first_token().start_pos(),
            end: self.last_token().end_pos(),
        }
    }

    // Flattens an expression like "1, 2, 3"
    pub fn flatten_comma_separated_list(&self) -> Vec<&Expression> {
        match self {
            Expression::Binary(left, token, right) => {
                if token.token_type == TokenType::Comma {
                    let mut args = left.flatten_comma_separated_list();
                    args.append(&mut right.flatten_comma_separated_list());
                    args
                } else {
                    vec![&self]
                }
            }
            _ => vec![&self],
        }
    }

    // Flattens an expression like "(1, 2, 3)"
    // If allow_singleton is true, then something like "1" also counts as a list.
    // If allow_singleton is false, a list of length 1 must be parenthesized like "(1)".
    pub fn flatten_list(&self, allow_singleton: bool) -> Result<Vec<&Expression>> {
        match self {
            Expression::Grouping(_, e, _) => Ok(e.flatten_comma_separated_list()),
            e => {
                if !allow_singleton {
                    Err(self.error(&format!("expected a grouped list but found: {}", self)))
                } else {
                    Ok(vec![e])
                }
            }
        }
    }

    // Parses a single expression from the provided tokens.
    // termination determines what tokens are allowed to be the terminator.
    // Consumes the terminating token and returns it.
    fn parse(
        tokens: &mut TokenIter,
        expected_type: ExpressionType,
        termination: Terminator,
    ) -> Result<(Expression, Token)> {
        let (mut partials, terminator) =
            parse_partial_expressions(tokens, expected_type, termination)?;
        group_type_parameters(&mut partials)?;
        check_partial_expressions(&partials)?;
        let expression = combine_partial_expressions(partials, expected_type, &terminator)?;
        Ok((expression, terminator))
    }

    // Parse an expression that should represent a value.
    // Consumes the terminating token and returns it.
    pub fn parse_value(
        tokens: &mut TokenIter,
        terminator: Terminator,
    ) -> Result<(Expression, Token)> {
        Expression::parse(tokens, ExpressionType::Value, terminator)
    }

    // Parse an expression that should represent a type, or part of a type.
    // Consumes the terminating token and returns it.
    pub fn parse_type(
        tokens: &mut TokenIter,
        terminator: Terminator,
    ) -> Result<(Expression, Token)> {
        Expression::parse(tokens, ExpressionType::Type, terminator)
    }

    // Whether this expression could be part of a type.
    pub fn could_be_part_of_type(&self) -> bool {
        let answer = match self {
            Expression::Singleton(_) => true,
            Expression::Grouping(_, e, _) => e.could_be_part_of_type(),
            Expression::Binary(left, op, right) => match op.token_type {
                TokenType::Comma | TokenType::RightArrow => {
                    left.could_be_part_of_type() && right.could_be_part_of_type()
                }
                TokenType::Dot => right.could_be_part_of_type(),
                _ => false,
            },
            Expression::Concatenation(left, right) => {
                left.could_be_part_of_type() && right.could_be_part_of_type()
            }
            _ => false,
        };
        answer
    }

    pub fn parse_value_string(input: &str) -> Result<Expression> {
        let tokens = Token::scan(input);
        let mut tokens = TokenIter::new(tokens);
        let (expr, _) = Expression::parse(
            &mut tokens,
            ExpressionType::Value,
            Terminator::Is(TokenType::NewLine),
        )?;
        Ok(expr)
    }

    fn expect_parse(input: &str, expected_type: ExpressionType) -> Expression {
        let tokens = Token::scan(input);
        let mut tokens = TokenIter::new(tokens);
        match Expression::parse(
            &mut tokens,
            expected_type,
            Terminator::Is(TokenType::NewLine),
        ) {
            Ok((e, _)) => e,
            Err(e) => panic!("unexpected error parsing: {}", e),
        }
    }

    pub fn expect_value(input: &str) -> Expression {
        Expression::expect_parse(input, ExpressionType::Value)
    }

    // For the purposes of this function, type params like [T, U] are considered types.
    pub fn is_type(&self) -> bool {
        match &self {
            Expression::Singleton(token) => token.is_type_name(),
            Expression::Grouping(_, e, _) => e.is_type(),
            Expression::Binary(left, token, _) => match token.token_type {
                TokenType::Comma | TokenType::RightArrow => left.is_type(),
                _ => false,
            },
            Expression::Concatenation(left, _) => left.is_type(),
            Expression::Binder(..)
            | Expression::GenericBinder(..)
            | Expression::Unary(..)
            | Expression::Match(..)
            | Expression::IfThenElse(..) => false,
        }
    }
}

// When we have a sequence of precedence-based operators, we need to gather the whole
// sequence before combining them.
// The PartialExpressions are what we have before doing this combination.
// The precedence-based operators include unary operators, infix operators, and function application.
#[derive(Debug)]
enum PartialExpression {
    // Already a complete expression
    Expression(Expression),

    // Tokens that are only part of an expression
    Unary(Token),

    Postfix(Token),

    Binary(Token),

    // An implicit binary expression, like "f(x)" or "List[Bool]".
    // It's located between the f and the (x).
    Implicit(Token),
}

impl fmt::Display for PartialExpression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PartialExpression::Expression(e) => write!(f, "{}", e),
            PartialExpression::Unary(token)
            | PartialExpression::Postfix(token)
            | PartialExpression::Binary(token) => {
                write!(f, "{}", token)
            }
            PartialExpression::Implicit(_) => write!(f, "<implicit>"),
        }
    }
}

impl ErrorContext for PartialExpression {
    fn error(&self, message: &str) -> Error {
        match &self {
            PartialExpression::Expression(e) => e.error(message),
            PartialExpression::Unary(t)
            | PartialExpression::Postfix(t)
            | PartialExpression::Binary(t)
            | PartialExpression::Implicit(t) => t.error(message),
        }
    }
}

impl PartialExpression {
    fn is_grouping(&self) -> bool {
        match self {
            PartialExpression::Expression(e) => e.is_grouping(),
            _ => false,
        }
    }
}

// Create partial expressions from tokens.
// termination determines what tokens are allowed to be the terminator.
// Consumes the terminating token from the iterator and returns it.
fn parse_partial_expressions(
    tokens: &mut TokenIter,
    expected_type: ExpressionType,
    termination: Terminator,
) -> Result<(VecDeque<PartialExpression>, Token)> {
    let mut partials = VecDeque::<PartialExpression>::new();
    while let Some(token) = tokens.next() {
        if termination.matches(&token.token_type) {
            return Ok((partials, token));
        }

        if token.token_type == TokenType::LeftBracket {
            // The start of a type parameter list.
            // If so, we need to parse the whole list as a single expression.
            let (subexpression, last_token) = Expression::parse(
                tokens,
                ExpressionType::Type,
                Terminator::Is(TokenType::RightBracket),
            )?;
            partials.push_back(PartialExpression::Implicit(token.clone()));
            let group = Expression::Grouping(token, Box::new(subexpression), last_token);
            partials.push_back(PartialExpression::Expression(group));
            continue;
        }

        if token.token_type == TokenType::LessThan && expected_type == ExpressionType::Type {
            // The start of a type parameter list.
            // If so, we need to parse the whole list as a single expression.
            let (subexpression, last_token) = Expression::parse(
                tokens,
                ExpressionType::Type,
                Terminator::Is(TokenType::GreaterThan),
            )?;
            partials.push_back(PartialExpression::Implicit(token.clone()));
            let group = Expression::Grouping(token, Box::new(subexpression), last_token);
            partials.push_back(PartialExpression::Expression(group));
            continue;
        }

        if token.token_type.is_binary() {
            match (expected_type, token.token_type) {
                (ExpressionType::Value, TokenType::Colon) => {
                    return Err(token.error("unexpected colon in value"));
                }
                (ExpressionType::Value, _) => {
                    // Anything else can be in a value
                }
                (ExpressionType::Type, TokenType::Comma)
                | (ExpressionType::Type, TokenType::RightArrow)
                | (ExpressionType::Type, TokenType::Dot)
                | (ExpressionType::Type, TokenType::LessThan)
                | (ExpressionType::Type, TokenType::GreaterThan) => {
                    // These are okay in types
                }
                (ExpressionType::Type, _) => {
                    return Err(token.error("unexpected token in type"));
                }
            }

            if token.token_type.is_unary() {
                // This could either be unary or binary.
                // Look at the previous token to decide.
                if match partials.back() {
                    Some(PartialExpression::Expression(_)) => {
                        // An expression can't be followed by a unary operator.
                        false
                    }
                    Some(PartialExpression::Unary(_))
                    | Some(PartialExpression::Postfix(_))
                    | Some(PartialExpression::Implicit(_))
                    | Some(PartialExpression::Binary(_))
                    | None => {
                        // All of these things can be followed by a unary operator.
                        true
                    }
                } {
                    partials.push_back(PartialExpression::Unary(token));
                    continue;
                }
            }

            partials.push_back(PartialExpression::Binary(token.clone()));
            // Skip newlines after certain operators to allow line continuation
            if matches!(
                token.token_type,
                TokenType::Equals
                    | TokenType::NotEquals
                    | TokenType::Or
                    | TokenType::And
                    | TokenType::Plus
                    | TokenType::Minus
                    | TokenType::Asterisk
                    | TokenType::Slash
            ) {
                tokens.skip_newlines();
            }
            continue;
        }
        if token.token_type.is_unary() {
            partials.push_back(PartialExpression::Unary(token));
            continue;
        }
        if token.token_type.is_postfix() {
            partials.push_back(PartialExpression::Postfix(token));
            continue;
        }
        match token.token_type {
            TokenType::LeftParen => {
                let (subexpression, last_token) = Expression::parse(
                    tokens,
                    expected_type,
                    Terminator::Is(TokenType::RightParen),
                )?;

                // A group that has no operator before it gets an implicit apply.
                if matches!(partials.back(), Some(PartialExpression::Expression(_))) {
                    partials.push_back(PartialExpression::Implicit(token.clone()));
                }

                let group = Expression::Grouping(token, Box::new(subexpression), last_token);
                partials.push_back(PartialExpression::Expression(group));
            }

            TokenType::Identifier | TokenType::Axiom | TokenType::Lib | TokenType::Constraint => {
                partials.push_back(PartialExpression::Expression(Expression::Singleton(token)));
            }
            TokenType::Numeral | TokenType::True | TokenType::False | TokenType::SelfToken => {
                if expected_type == ExpressionType::Type {
                    return Err(token.error("expected a type but found a value"));
                }
                partials.push_back(PartialExpression::Expression(Expression::Singleton(token)));
            }

            TokenType::ForAll | TokenType::Exists | TokenType::Function => {
                if expected_type != ExpressionType::Value {
                    return Err(token.error("quantifiers cannot be used here"));
                }
                // Check for optional type parameters on function keyword
                let type_params = if token.token_type == TokenType::Function {
                    TypeParamExpr::parse_list(tokens)?
                } else {
                    vec![]
                };
                let args = if token.token_type == TokenType::Function
                    && !type_params.is_empty()
                    && tokens.peek_type() == Some(TokenType::LeftBrace)
                {
                    Vec::new()
                } else {
                    tokens.expect_type(TokenType::LeftParen)?;
                    Declaration::parse_list(tokens)?
                };
                tokens.expect_type(TokenType::LeftBrace)?;
                let (subexpression, right_brace) = Expression::parse(
                    tokens,
                    ExpressionType::Value,
                    Terminator::Is(TokenType::RightBrace),
                )?;
                let binder = if type_params.is_empty() {
                    Expression::Binder(token, args, Box::new(subexpression), right_brace)
                } else {
                    Expression::GenericBinder(
                        token,
                        type_params,
                        args,
                        Box::new(subexpression),
                        right_brace,
                    )
                };
                partials.push_back(PartialExpression::Expression(binder));
            }

            TokenType::If => {
                if expected_type != ExpressionType::Value {
                    return Err(token.error("'if' expressions cannot be used here"));
                }
                let (condition, _) =
                    Expression::parse_value(tokens, Terminator::Is(TokenType::LeftBrace))?;
                let (if_block, last_right_brace) =
                    Expression::parse_value(tokens, Terminator::Is(TokenType::RightBrace))?;

                // Check if there's an else clause
                let (else_block, final_brace) = if tokens.peek_type() == Some(TokenType::Else) {
                    tokens.next(); // consume the else token
                    tokens.expect_type(TokenType::LeftBrace)?;
                    let (else_expr, else_brace) =
                        Expression::parse_value(tokens, Terminator::Is(TokenType::RightBrace))?;
                    (Some(Box::new(else_expr)), else_brace)
                } else {
                    (None, last_right_brace)
                };

                let exp = Expression::IfThenElse(
                    token,
                    Box::new(condition),
                    Box::new(if_block),
                    else_block,
                    final_brace,
                );
                partials.push_back(PartialExpression::Expression(exp));
            }

            TokenType::Match => {
                if expected_type != ExpressionType::Value {
                    return Err(token.error("'match' cannot be used here"));
                }
                let (scrutinee, _) =
                    Expression::parse_value(tokens, Terminator::Is(TokenType::LeftBrace))?;

                let mut cases = vec![];

                let right_brace = loop {
                    tokens.skip_newlines();
                    match tokens.peek() {
                        None => {
                            return Err(tokens.error("expected a case but got EOF"));
                        }
                        Some(t) => {
                            if t.token_type == TokenType::RightBrace {
                                break tokens.next().unwrap();
                            }
                        }
                    }

                    let (pattern, _) =
                        Expression::parse_value(tokens, Terminator::Is(TokenType::LeftBrace))?;
                    let (exp, _) =
                        Expression::parse_value(tokens, Terminator::Is(TokenType::RightBrace))?;
                    cases.push((pattern, exp));
                };
                if cases.is_empty() {
                    return Err(tokens.error("expected at least one case"));
                }
                let exp = Expression::Match(token, Box::new(scrutinee), cases, right_brace);
                partials.push_back(PartialExpression::Expression(exp));
            }

            TokenType::NewLine => {
                // Ignore newlines. The case where the newline is a terminator, we already caught.
            }

            _ => {
                return Err(token.error(&format!(
                    "expected an expression terminated by {}",
                    termination
                )));
            }
        }
    }
    Err(tokens.error("expected expression but got EOF"))
}

// Find the index of the operator that should operate last. (Ie, the root of the tree.)
// If there are no operators, return None.
fn find_last_operator(partials: &VecDeque<PartialExpression>) -> Result<Option<usize>> {
    let len = partials.len();
    let operators = partials.iter().enumerate().filter_map(|(i, partial)| {
        match partial {
            PartialExpression::Unary(token) => {
                // Only a unary operator at the beginning of the expression can operate last
                if i == 0 {
                    Some((-token.unary_precedence(), i as isize))
                } else {
                    None
                }
            }
            PartialExpression::Postfix(token) => {
                // Only a postfix operator at the end of the expression can operate last
                if i == len - 1 {
                    Some((-token.postfix_precedence(), i as isize))
                } else {
                    None
                }
            }
            PartialExpression::Binary(token) => {
                // For right-associative operators, we negate the index so that
                // max() will pick the leftmost operator among those with the same precedence.
                // For left-associative operators, max() picks the rightmost.
                let index_key = if token.token_type.is_right_associative() {
                    -(i as isize)
                } else {
                    i as isize
                };
                Some((-token.binary_precedence(), index_key))
            }
            PartialExpression::Implicit(_) => {
                // Application has the same precedence as dot, so it goes left to right.
                // This is intuitive if you look at the cases:
                // foo.bar.baz is parsed as (foo.bar).baz
                // foo.bar(baz) is parsed as (foo.bar)(baz)
                // foo(bar).baz is parsed as (foo(bar)).baz
                // foo(bar)(baz) is parsed as (foo(bar))(baz)
                Some((-TokenType::Dot.binary_precedence(), i as isize))
            }
            _ => None,
        }
    });

    match operators.max() {
        Some((neg_precedence, index_key)) => {
            if neg_precedence == 0 {
                let index = index_key.abs() as usize;
                return Err(partials[index].error(&format!(
                    "the parser did not expect a precedence-zero thing here"
                )));
            }
            Ok(Some(index_key.abs() as usize))
        }
        None => Ok(None),
    }
}

// Checks if this "looks like" a type parameter list.
// It only has to find the innermost one when they are nested.
// index is the index of the first partial expression after a '<'.
// If so, returns the index of the closing '>'.
fn looks_like_type_params(partials: &VecDeque<PartialExpression>, index: usize) -> Option<usize> {
    for (i, partial) in partials.iter().enumerate().skip(index) {
        match partial {
            PartialExpression::Binary(token) => match token.token_type {
                TokenType::Comma | TokenType::RightArrow | TokenType::Dot | TokenType::Colon => {
                    continue
                }
                TokenType::GreaterThan => return Some(i),
                _ => {
                    return None;
                }
            },
            PartialExpression::Expression(expr) => {
                if expr.could_be_part_of_type() {
                    continue;
                }
                return None;
            }
            _ => return None,
        }
    }
    None
}

// Checks if anything in this list of partial expressions is actually type parameters.
// Returns the indices of the '<' and '>' if so.
fn find_type_params(partials: &VecDeque<PartialExpression>) -> Option<(usize, usize)> {
    for (i, partial) in partials.iter().enumerate() {
        match partial {
            PartialExpression::Binary(token) => {
                if token.token_type == TokenType::LessThan {
                    if let Some(j) = looks_like_type_params(partials, i + 1) {
                        return Some((i, j));
                    }
                }
            }
            _ => {}
        }
    }
    None
}

// Checks if there are any type parameters in this list of partial expressions.
// If so, it combines them into a single Grouping expression.
// It's weird that sometimes we catch type parameters here and sometimes we catch them
// while parsing partial expressions. It would be better to do it all in one place.
fn group_type_parameters(partials: &mut VecDeque<PartialExpression>) -> Result<()> {
    loop {
        match find_type_params(&partials) {
            Some((i, j)) => {
                // Break into three groups.
                // left, opening token, middle (the type parameters), closing token, right
                // The left group is still called "partials".
                let right = partials.split_off(j + 1);
                let closing = partials.pop_back().unwrap();
                let closing = match closing {
                    PartialExpression::Binary(t) => t,
                    _ => return Err(closing.error("expected a closing '>'")),
                };
                let middle = partials.split_off(i + 1);
                let opening = partials.pop_back().unwrap();
                let opening = match opening {
                    PartialExpression::Binary(t) => t,
                    _ => return Err(opening.error("expected an opening '<'")),
                };

                // Make a partial expression for the type params
                let params = combine_partial_expressions(middle, ExpressionType::Type, &opening)?;
                let grouped =
                    Expression::Grouping(opening.clone(), Box::new(params), closing.clone());

                // Reassemble the whole thing
                partials.push_back(PartialExpression::Implicit(opening));
                partials.push_back(PartialExpression::Expression(grouped));
                if right.front().map_or(false, |p| p.is_grouping()) {
                    partials.push_back(PartialExpression::Implicit(closing));
                }
                partials.extend(right);
            }
            None => return Ok(()),
        }
    }
}

// Checks to see if the partial expressions are valid.
// This is not necessary for correctness. But we can generate a nicer error message here than
// in the depths of a recursion.
fn check_partial_expressions(partials: &VecDeque<PartialExpression>) -> Result<()> {
    if partials.len() > 1 {
        // Iterate over all pairs
        for i in 0..(partials.len() - 1) {
            let left = &partials[i];
            if let PartialExpression::Binary(t) = left {
                if t.token_type == TokenType::GreaterThan {
                    // Our sanity checks don't work for type parameters.
                    continue;
                }
            }
            let right = &partials[i + 1];
            match (left, right) {
                (PartialExpression::Binary(a), PartialExpression::Binary(b))
                | (PartialExpression::Unary(a), PartialExpression::Binary(b)) => {
                    return Err(right.error(&format!(
                        "the '{}' operator cannot be followed by the '{}' operator",
                        a, b
                    )));
                }
                _ => {}
            }
        }
    }
    Ok(())
}

// Combines partial expressions into a single expression.
// Operators work in precedence order, and left-to-right within a single precedence.
// This algorithm is quadratic, so perhaps we should improve it at some point.
fn combine_partial_expressions(
    mut partials: VecDeque<PartialExpression>,
    expected_type: ExpressionType,
    source: &dyn ErrorContext,
) -> Result<Expression> {
    if partials.len() == 0 {
        return Err(source.error("expected an expression here"));
    }
    if partials.len() == 1 {
        let partial = partials.pop_back().unwrap();
        if let PartialExpression::Expression(e) = partial {
            return Ok(e);
        }
        return Err(partial.error("incomplete expression"));
    }

    // If there are operators, find the operator that should operate last,
    // and recurse on each of the two sides.
    if let Some(index) = find_last_operator(&partials)? {
        if index == 0 {
            let partial = partials.pop_front().unwrap();
            if let PartialExpression::Unary(token) = partial {
                return Ok(Expression::Unary(
                    token,
                    Box::new(combine_partial_expressions(
                        partials,
                        expected_type,
                        source,
                    )?),
                ));
            }
            return Err(partial.error("expected unary operator"));
        }

        if index == partials.len() - 1 {
            let partial = partials.pop_back().unwrap();
            if let PartialExpression::Postfix(token) = partial {
                return Ok(Expression::Unary(
                    token,
                    Box::new(combine_partial_expressions(
                        partials,
                        expected_type,
                        source,
                    )?),
                ));
            }
            return Err(partial.error("expected postfix operator"));
        }

        let mut right_partials = partials.split_off(index);
        let partial = right_partials.pop_front().unwrap();

        return match partial {
            PartialExpression::Binary(token) => {
                // Check for deprecated RightArrow in value expressions
                if expected_type == ExpressionType::Value
                    && token.token_type == TokenType::RightArrow
                {
                    return Err(token
                        .error("'->' is deprecated in value expressions, use 'implies' instead"));
                }
                let left = combine_partial_expressions(partials, expected_type, source)?;
                let right = combine_partial_expressions(right_partials, expected_type, source)?;
                Ok(Expression::Binary(Box::new(left), token, Box::new(right)))
            }
            PartialExpression::Implicit(_) => {
                let left = combine_partial_expressions(partials, expected_type, source)?;
                let right = combine_partial_expressions(right_partials, expected_type, source)?;
                Ok(Expression::Concatenation(Box::new(left), Box::new(right)))
            }
            _ => Err(partial.error("expected binary operator")),
        };
    }

    // When there are no operators, the nature of the first partial expression should
    // tell us how to handle the rest of them.
    match partials.pop_front().unwrap() {
        // When the first partial is a normal expression, that looks like a function application.
        PartialExpression::Expression(mut answer) => {
            for partial in partials.into_iter() {
                match partial {
                    PartialExpression::Expression(expr) => match expr {
                        Expression::Grouping(_, _, _) => {
                            answer = Expression::Concatenation(Box::new(answer), Box::new(expr))
                        }
                        _ => return Err(expr.error("expected a grouping")),
                    },
                    _ => return Err(partial.error("unexpected operator")),
                }
            }
            Ok(answer)
        }

        e => Err(e.error("expected an expression")),
    }
}

impl<'a, D, A> Pretty<'a, D, A> for &'a Expression
where
    A: 'a,
    D: DocAllocator<'a, A>,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        self.pretty_ref(allocator, false)
    }
}

impl Expression {
    pub fn pretty_ref<'a, D, A>(&'a self, allocator: &'a D, flat: bool) -> DocBuilder<'a, D, A>
    where
        A: 'a,
        D: DocAllocator<'a, A>,
    {
        let line = || {
            if flat {
                allocator.space()
            } else {
                allocator.hardline()
            }
        };
        match self {
            Expression::Singleton(token) => allocator.text(token.text()),
            Expression::Unary(token, subexpression) => {
                if token.token_type.is_postfix() {
                    // Postfix operators go after the expression
                    subexpression
                        .pretty_ref(allocator, flat)
                        .append(allocator.text(token.text()))
                } else if token.token_type == TokenType::Minus {
                    // Prefix minus has no space
                    allocator
                        .text(token.text())
                        .append(subexpression.pretty_ref(allocator, flat))
                } else {
                    // Other prefix operators have a space
                    allocator
                        .text(token.text())
                        .append(allocator.space())
                        .append(subexpression.pretty_ref(allocator, flat))
                }
            }
            Expression::Binary(left, token, right) => {
                let left_doc = left.pretty_ref(allocator, flat);
                let right_doc = right.pretty_ref(allocator, flat);

                let doc = if token.token_type.left_space() {
                    left_doc
                        .append(allocator.space())
                        .append(allocator.text(token.text()))
                } else {
                    left_doc.append(allocator.text(token.text()))
                }
                .append(if token.token_type.right_space() {
                    // For "or" operator, use a soft line when not in flat mode
                    if token.token_type == TokenType::Or && !flat {
                        allocator.line()
                    } else {
                        allocator.space()
                    }
                } else {
                    allocator.nil()
                })
                .append(right_doc);

                // Group "or" expressions so they can stay on one line if they fit
                if token.token_type == TokenType::Or && !flat {
                    doc.group()
                } else {
                    doc
                }
            }
            Expression::Concatenation(left, right) => left
                .pretty_ref(allocator, flat)
                .append(right.pretty_ref(allocator, flat)),
            Expression::Grouping(left, e, right) => allocator
                .text(left.text())
                .append(e.pretty_ref(allocator, flat))
                .append(allocator.text(right.text())),
            Expression::Binder(token, args, sub, _) => {
                let args_doc = self.pretty_args(allocator, args, flat);
                allocator
                    .text(token.text())
                    .append(args_doc)
                    .append(allocator.space())
                    .append(allocator.text("{"))
                    .append(
                        line()
                            .nest(4)
                            .append(sub.pretty_ref(allocator, flat))
                            .nest(4),
                    )
                    .append(line())
                    .append(allocator.text("}"))
                    .group()
            }
            Expression::GenericBinder(token, type_params, args, sub, _) => {
                let mut type_params_doc = allocator.text("[");
                for (i, tp) in type_params.iter().enumerate() {
                    if i > 0 {
                        type_params_doc = type_params_doc.append(allocator.text(", "));
                    }
                    type_params_doc = type_params_doc.append(allocator.text(format!("{}", tp)));
                }
                type_params_doc = type_params_doc.append(allocator.text("]"));
                let args_doc = if args.is_empty() {
                    allocator.nil()
                } else {
                    self.pretty_args(allocator, args, flat)
                };
                allocator
                    .text(token.text())
                    .append(type_params_doc)
                    .append(args_doc)
                    .append(allocator.space())
                    .append(allocator.text("{"))
                    .append(
                        line()
                            .nest(4)
                            .append(sub.pretty_ref(allocator, flat))
                            .nest(4),
                    )
                    .append(line())
                    .append(allocator.text("}"))
                    .group()
            }
            Expression::IfThenElse(_, cond, if_block, else_block, _) => {
                let if_doc = allocator
                    .text("if")
                    .append(allocator.space())
                    .append(cond.pretty_ref(allocator, flat))
                    .append(allocator.space())
                    .append(allocator.text("{"))
                    .append(
                        line()
                            .nest(4)
                            .append(if_block.pretty_ref(allocator, flat))
                            .nest(4),
                    )
                    .append(line())
                    .append(allocator.text("}"));

                match else_block {
                    Some(else_expr) => if_doc
                        .append(allocator.space())
                        .append(allocator.text("else"))
                        .append(allocator.space())
                        .append(allocator.text("{"))
                        .append(
                            line()
                                .nest(4)
                                .append(else_expr.pretty_ref(allocator, flat))
                                .nest(4),
                        )
                        .append(line())
                        .append(allocator.text("}")),
                    None => if_doc,
                }
                .group()
            }
            Expression::Match(_, scrutinee, cases, _) => {
                let doc = allocator
                    .text("match")
                    .append(allocator.space())
                    .append(scrutinee.pretty_ref(allocator, flat))
                    .append(allocator.space())
                    .append(allocator.text("{"));

                let mut cases_doc = allocator.nil();
                for (pat, exp) in cases {
                    cases_doc = cases_doc
                        .append(line())
                        .append(pat.pretty_ref(allocator, flat))
                        .append(allocator.space())
                        .append(allocator.text("{"))
                        .append(line().append(exp.pretty_ref(allocator, flat)).nest(4))
                        .append(line())
                        .append(allocator.text("}"));
                }

                doc.append(cases_doc.nest(4))
                    .append(line())
                    .append(allocator.text("}"))
                    .group()
            }
        }
    }

    fn pretty_args<'a, D, A>(
        &'a self,
        allocator: &'a D,
        args: &'a [Declaration],
        flat: bool,
    ) -> DocBuilder<'a, D, A>
    where
        A: 'a,
        D: DocAllocator<'a, A>,
    {
        let mut doc = allocator.text("(");
        for (i, arg) in args.iter().enumerate() {
            if i > 0 {
                doc = doc.append(allocator.text(", "));
            }
            doc = doc.append(arg.pretty_ref(allocator, flat));
        }
        doc.append(allocator.text(")"))
    }
}

impl Declaration {
    pub fn pretty_ref<'a, D, A>(&'a self, allocator: &'a D, flat: bool) -> DocBuilder<'a, D, A>
    where
        A: 'a,
        D: DocAllocator<'a, A>,
    {
        match self {
            Declaration::Typed(name_token, type_expr) => allocator
                .text(name_token.text())
                .append(allocator.text(": "))
                .append(type_expr.pretty_ref(allocator, flat)),
            Declaration::SelfToken(token) => allocator.text(token.text()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expect_optimal(input: &str, expected_type: ExpressionType) {
        let expr = Expression::expect_parse(input, expected_type);
        if expected_type == ExpressionType::Type {
            assert!(expr.could_be_part_of_type());
        }
        let output = expr.to_string();
        assert_eq!(input, output);
    }

    fn check_value(input: &str) {
        expect_optimal(input, ExpressionType::Value);
    }

    fn check_type(input: &str) {
        expect_optimal(input, ExpressionType::Type);
    }

    // Expects a parse error, or not-an-expression, but not a lex error
    fn expect_error(input: &str, expected_type: ExpressionType) {
        let tokens = Token::scan(input);
        let mut tokens = TokenIter::new(tokens);
        let res = Expression::parse(
            &mut tokens,
            expected_type,
            Terminator::Is(TokenType::NewLine),
        );
        match res {
            Err(_) => {}
            Ok((e, _)) => panic!("unexpectedly parsed {} => {}", input, e),
        }
    }

    // Expects the input to be a concatenation at the top level
    fn expect_concatenation(input: &str) {
        let exp = Expression::expect_parse(input, ExpressionType::Value);
        if let Expression::Concatenation(_, _) = exp {
            // That's what we expect
            return;
        }
        exp.print_one_level();
        panic!("expected a top-level apply");
    }

    fn expect_dot(input: &str) {
        let exp = Expression::expect_parse(input, ExpressionType::Value);
        if let Expression::Binary(_, token, _) = &exp {
            if token.token_type == TokenType::Dot {
                // That's what we expect
                return;
            }
        }
        exp.print_one_level();
        panic!("expected a top-level dot");
    }

    fn check_not_value(input: &str) {
        expect_error(input, ExpressionType::Value);
    }

    fn check_not_type(input: &str) {
        expect_error(input, ExpressionType::Type);
    }

    #[test]
    fn test_value_parsing() {
        check_value("p implies (q implies p)");
        check_value("(p implies (q implies r)) implies ((p implies q) implies (p implies r))");
        check_value("(p iff q) = ((p implies q) and (q implies p))");
        check_value("p and q iff q and p");
        check_value("(p and q) and r iff p and (q and r)");
        check_value("p or q iff q or p");
        check_value("(p or q) or r iff p or (q or r)");
    }

    #[test]
    fn test_function_application() {
        check_value("f(x)");
        check_value("foo(x, y)");
        check_value("foo(x)(y)");
        check_value("foo(x, y + z, w)");
    }

    #[test]
    fn test_quantifiers() {
        check_value("forall(x: Nat) { (suc(x) = x + 1) }");
        check_value("exists(x: Nat) { (x = 0) }");
        check_value("exists(f: (Nat, Nat) -> Nat) { (f(0, 0) = 0) }");
    }

    #[test]
    fn test_type_parsing() {
        check_type("Bool");
        check_type("Bool -> Bool");
        check_type("(Bool, Bool) -> Bool");
    }

    #[test]
    fn test_comparisons() {
        check_value("p = q");
        check_value("p != q");
        check_value("p < q");
        check_value("p <= q");
        check_value("p > q");
        check_value("p >= q");
    }

    #[test]
    fn test_blocks() {
        check_value("forall(x: Nat) { x = x }");
    }

    #[test]
    fn test_empty_blocks() {
        // Empty blocks in expressions should fail to parse, but not crash
        check_not_value("forall(x: Nat) { }");
        check_not_value("exists(x: Nat) { }");
    }

    #[test]
    fn test_block_inside_binary() {
        check_value("p implies forall(x: Nat) { x = x }");
        check_value("f(forall(x: Nat) { x = x }, forall(y: Nat) { y = y })");
    }

    #[test]
    fn test_bad_values() {
        check_not_value("+ + +");

        // Not expressions
        check_not_value("let a: int = x + 2");
        check_not_value("define (p & q) = !(p -> !q)");
        check_not_value("type Nat: axiom");

        // A math-function has to have arguments
        check_not_value("f()");

        check_not_value("axiom contraposition: (!p -> !q) -> (q -> p)");
        check_not_value("f x");

        check_not_value("forall");
        check_not_value("exists");
        check_not_value("function");
    }

    #[test]
    fn test_bad_types() {
        check_not_type("bool, bool -> bool ->");
        check_not_type("(!p -> !q) -> (q -> p)");
    }

    #[test]
    fn test_extra_newline() {
        Expression::expect_value(
            "(1 +
            2)",
        );
    }

    #[test]
    fn test_dot_expression_values() {
        check_value("NatPair.first(NatPair.new(a, b)) = a");
        check_value("foo(x).bar");
        check_value("foo(x).bar.baz");
        check_value("(foo).bar");
        check_value("(a + b).c");
        check_value("a.b.c = Foo.bar(baz).qux");
        check_value("Rat.constraint(a, b)");
    }

    #[test]
    fn test_dot_parsing_priority() {
        expect_concatenation("foo.bar(baz)");
        expect_dot("foo(x).bar");
        expect_dot("foo(x).bar.baz");
        expect_dot("(foo).bar");
        expect_dot("(a + b).c");
        expect_dot("Foo.bar(baz).qux");
        expect_concatenation("foo(bar).baz(qux)");
    }

    #[test]
    fn test_if_then_else_expressions() {
        check_value("if p { q } else { r }");
        check_value("if a = 0 { 0 } else { 1 }");
        check_value("if foo(a) { 0 } else { 1 }");
        check_value("if (a = 0) { 0 } else { 1 }");
        check_value("if p { q }"); // Now valid - if without else

        check_not_value("if");
        check_not_value("if p");
        check_not_value("else");
        check_not_value("else { r }");
        check_not_value("if p { q } else { r } else { s }");
    }

    #[test]
    fn test_bad_partials() {
        check_not_value("(1 +)");
        check_not_value("(!)");
        check_not_value("{ 1 }");
        check_not_value("forall(x: Nat)");
        check_not_value("forall(x: Nat) { x = x } { x }");
        check_not_value("1 + { 1 }");

        // A block should not be okay where we expect an expression
        check_not_value("{ x = x }");
    }

    #[test]
    fn test_match_expressions() {
        check_value("match a { Foo.bar(b) { b } Foo.qux(b) { b } }");
        check_not_value("match a { }");
    }

    #[test]
    fn test_unary_negate_expression() {
        check_value("-1");
        check_value("-a");
        check_value("-a - b");
        check_value("-(a - b)");
        check_value("a + -b");
        check_value("a - -b");
        check_value("-a * b");
        check_value("-(a * b)");
    }

    #[test]
    fn test_implies_expression() {
        check_value("a implies b");
    }

    #[test]
    fn test_generic_types() {
        check_type("List[List[T]]");
        check_type("List[List[X] -> List[Y], List[Y] -> List[X]]");
        check_type("List[(foo.Foo, bar.Bar) -> baz.Baz[Qux]]");
        check_type("Pair[Bool, Bool]");
    }

    #[test]
    fn test_type_params_in_expressions() {
        check_value("foo[T]");
        check_value("List[T].new");
        check_value("map(add[Int], myList)");
        check_value("is_surjective(identity[T])");
        check_value("foo.bar[T]");
        check_value("maps_to[Bool, Bool](not2, false)");
    }

    #[test]
    fn test_multi_arg_function_in_argument() {
        check_value("forall(f: (Bool, Bool) -> Bool) { f(true, false) }");
    }

    #[test]
    fn test_multiple_type_params_in_argument() {
        check_value("forall(p: Pair[Bool, Bool]) { true }");
    }

    #[test]
    fn test_instantiated_method_expression() {
        check_value("Pair[Foo, Bar].new(foo, bar)");
    }

    #[test]
    fn test_nested_generics_with_method() {
        check_value("List[Pair[T1, T2]].new(nil)");
    }

    #[test]
    fn test_expr_question_mark() {
        check_value("a? + b?");
        check_value("foo?.bar");
    }

    #[test]
    fn test_generic_lambda_parsing() {
        check_value("function[T](x: T) { x }");
        check_value("function[T, U](x: T, y: U) { x }");
    }

    #[test]
    fn test_generic_lambda_with_application() {
        // Generic lambda instantiated with type args, then applied to value args
        expect_concatenation("function[T](x: T) { x }[Nat](5)");
        // Type-only instantiation shape (no value args)
        expect_concatenation("function[T] { true }[Nat]");
        // Backward-compatibility with previous encoding
        expect_concatenation("function[T]() { true }[Nat]");
    }
}

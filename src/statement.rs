use tower_lsp::lsp_types::Range;

use crate::compilation::{CompilationError, ErrorSource, Result};
use crate::expression::{Declaration, Expression, Terminator, TypeParamExpr};
use crate::token::{Token, TokenIter, TokenType};

use pretty::{DocAllocator, DocBuilder, Pretty};
use std::fmt;

pub struct Body {
    pub left_brace: Token,
    pub statements: Vec<Statement>,
    pub right_brace: Token,
}

impl Body {
    pub fn range(&self) -> Range {
        Range {
            start: self.left_brace.start_pos(),
            end: self.right_brace.end_pos(),
        }
    }
}

/// Let statements introduce new named constants. For example:
///   let a: int = x + 2
/// The name token can either be an identifier or a number.
pub struct LetStatement {
    pub name_token: Token,

    /// What the constant is parametrized by, if anything.
    pub type_params: Vec<TypeParamExpr>,

    /// The expression for the type of this constant (optional for type inference)
    pub type_expr: Option<Expression>,

    // /// The expression for the value of this constant
    pub value: Expression,
}

/// Define statements introduce new named functions. For example:
///   define foo(a: int, b: int) -> int = a + a + b
pub struct DefineStatement {
    pub name_token: Token,

    /// For templated definitions
    pub type_params: Vec<TypeParamExpr>,

    /// A list of the named arg types, like "a: int" and "b: int".
    pub args: Vec<Declaration>,

    /// The specified return type of the function, like "int"
    pub return_type: Expression,

    /// The body of the function, like "a + a + b"
    pub return_value: Expression,
}

/// There are two keywords for theorems.
/// The "axiom" keyword indicates theorems that are axiomatic.
/// The "theorem" keyword is used for the vast majority of normal theorems.
/// For example, in:
///   axiom foo(p, q): p -> (q -> p)
/// axiomatic would be "true", the name is "foo", the args are p, q, and the claim is "p -> (q -> p)".
pub struct TheoremStatement {
    pub axiomatic: bool,
    pub name_token: Option<Token>,
    pub type_params: Vec<TypeParamExpr>,
    pub args: Vec<Declaration>,
    pub claim: Expression,
    pub claim_right_brace: Token,
    pub body: Option<Body>,
}

/// Claim statements are a boolean expression.
/// We're implicitly asserting that it is true and provable.
/// It's like an anonymous theorem.
pub struct ClaimStatement {
    pub claim: Expression,
}

/// Type statements declare a name as an alias to a type expression.
pub struct TypeStatement {
    pub name_token: Token,
    pub type_expr: Expression,
}

/// ForAll statements create a new block in which new variables are introduced.
pub struct ForAllStatement {
    pub quantifiers: Vec<Declaration>,
    pub body: Body,
}

/// If statements create a new block that introduces no variables but has an implicit condition.
/// They can optionally create a second block with an "else" keyword followed by a block.
pub struct IfStatement {
    pub condition: Expression,
    pub body: Body,
    pub else_body: Option<Body>,

    /// Just for error reporting
    pub token: Token,
}

/// A variable satisfy statement introduces new variables to the outside block.
/// It is written like:
///   let a: Nat satisfy {
///     a > 0
///   }
pub struct VariableSatisfyStatement {
    pub declarations: Vec<Declaration>,
    pub condition: Expression,
}

/// A function satisfy statement introduces a new function to the outside block,
/// by giving a condition that the output of the function obeys, and claiming that
/// there is such a function.
/// It's like a combination of a "define" and a "theorem".
pub struct FunctionSatisfyStatement {
    /// Name of the new function.
    pub name_token: Token,

    /// The declarations are mostly arguments to the function, but the last one is the return
    /// value of the function.
    pub declarations: Vec<Declaration>,

    pub satisfy_token: Token,

    /// The condition is the only thing we know about the function, that the condition is true.
    pub condition: Expression,

    /// The body is a proof that such a function exists, or more specifically, that an output
    /// exists for every input.
    /// This is implicitly using the axiom of choice. It's convenient for the axiom of choice
    /// to just be true. Maybe we have to worry about this more in the future.
    pub body: Option<Body>,
}

/// Struct statements define a new type by combining existing types
pub struct StructureStatement {
    pub name_token: Token,
    pub type_params: Vec<TypeParamExpr>,

    /// Each field contains a field name-token, a type expression, and doc comments
    pub fields: Vec<(Token, Expression, Vec<String>)>,

    /// The token that ends the first part of the structure statement
    pub first_right_brace: Token,

    /// The constraint on the structure, if there is one.
    pub constraint: Option<Expression>,

    /// The body is a proof that some value satisfies the constraint.
    /// We need to prove this because every type must be inhabited.
    /// If there's no constraint, there cannot be a body.
    pub body: Option<Body>,
}

/// Inductive statements define a new type by defining a set of constructors.
pub struct InductiveStatement {
    pub name_token: Token,
    pub type_params: Vec<TypeParamExpr>,

    /// Each constructor has a name token, an expression for a list of types, and doc comments.
    /// If the expression is None, the constructor is a base value.
    /// The types can refer to the inductive type itself.
    pub constructors: Vec<(Token, Option<Expression>, Vec<String>)>,
}

pub struct ImportStatement {
    /// The tokens for each component in the module path, like in "foo.bar.baz" would be [foo, bar, baz]
    pub components: Vec<Token>,

    /// What names to import from the module.
    /// If this is empty, we just import the module itself.
    pub names: Vec<Token>,
}

/// An attributes statement defines additional attributes for a type or typeclass.
/// They can be accessed either by the type's name, or via a value of the type.
pub struct AttributesStatement {
    /// For type attributes: the type name (e.g., "Foo" in "attributes Foo")
    /// For typeclass attributes: the typeclass name (e.g., "Magma" in "attributes M: Magma")
    pub name_token: Token,
    pub type_params: Vec<TypeParamExpr>,

    /// For typeclass attributes: the instance name (e.g., "M" in "attributes M: Magma")
    /// For type attributes: None
    pub instance_name: Option<Token>,

    /// The body containing the attributes
    pub body: Body,
}

/// A numerals statement determines what datatype is used for numeric literals.
pub struct NumeralsStatement {
    pub type_expr: Expression,
}

pub struct MatchStatement {
    /// The thing we are matching patterns against.
    pub scrutinee: Expression,

    /// (pattern, body) pairs.
    pub cases: Vec<(Expression, Body)>,
}

/// A typeclass condition is a theorem that must be proven for an instance type, to show
/// that it belongs to the typeclass.
pub struct TypeclassCondition {
    pub name_token: Token,
    pub args: Vec<Declaration>,
    pub claim: Expression,
    pub doc_comments: Vec<String>,
}

impl fmt::Display for TypeclassCondition {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Use the pretty-printing logic with a narrow width for mobile-friendly docs
        let allocator = pretty::Arena::<()>::new();
        let doc = self.pretty_ref(&allocator);
        // Break lines really aggressively
        doc.render_fmt(1, f)?;
        Ok(())
    }
}

impl<'a, D, A> Pretty<'a, D, A> for &'a TypeclassCondition
where
    A: 'a,
    D: DocAllocator<'a, A>,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        self.pretty_ref(allocator)
    }
}

impl TypeclassCondition {
    fn pretty_ref<'a, D, A>(&'a self, allocator: &'a D) -> DocBuilder<'a, D, A>
    where
        A: 'a,
        D: DocAllocator<'a, A>,
    {
        let mut doc = allocator.text(self.name_token.text());
        doc = write_theorem_pretty(allocator, doc, &[], &self.args, &self.claim);
        doc
    }
}

/// A typeclass statement defines a typeclass. It can contain some constants that must be
/// specified, and theorems that must be proven.
pub struct TypeclassStatement {
    /// The definition of the typeclass uses a named instance type.
    /// Like Self in Rust, but "Self" would be weird mathematically.
    /// This is None for the no-block syntax.
    pub instance_name: Option<Token>,

    /// The name of the typeclass being defined.
    pub typeclass_name: Token,

    /// The typeclasses that this typeclass extends.
    pub extends: Vec<Expression>,

    /// Each instance type in the typeclass has a list of constants that must be defined.
    /// This is a list of (name, type, doc_comments) tuples.
    /// The type may refer to the instance type itself.
    /// For example, all groups must define the identity, of the type of the group elements.
    pub constants: Vec<(Token, Expression, Vec<String>)>,

    /// Conditions that must be proven for the typeclass to be valid.
    pub conditions: Vec<TypeclassCondition>,
}

/// An instance statement describes how a type is an instance of a typeclass.
pub struct InstanceStatement {
    /// The type that is an instance of the typeclass.
    pub type_name: Token,

    /// The typeclass that the type is an instance of.
    pub typeclass: Expression,

    /// Definitions of each constant the typeclass requires.
    /// This is None for the no-block syntax when no definitions are needed.
    pub definitions: Option<Body>,

    /// The body is a proof that the type is an instance of the typeclass, if needed.
    pub body: Option<Body>,
}

/// A todo statement contains a body that is syntactically verified but not proven.
/// This represents things we want to prove but don't yet know how to prove.
pub struct TodoStatement {
    pub body: Body,
}

/// Acorn is a statement-based language. There are several types.
/// Each type has its own struct.
pub struct Statement {
    pub first_token: Token,
    pub last_token: Token,
    pub statement: StatementInfo,
}

impl ErrorSource for Statement {
    fn error(&self, message: &str) -> CompilationError {
        CompilationError::new(&self.first_token, &self.last_token, message)
    }
}

/// Information about a statement that is specific to the type of statement it is
pub enum StatementInfo {
    Let(LetStatement),
    Define(DefineStatement),
    Theorem(TheoremStatement),
    Claim(ClaimStatement),
    Type(TypeStatement),
    ForAll(ForAllStatement),
    If(IfStatement),
    VariableSatisfy(VariableSatisfyStatement),
    FunctionSatisfy(FunctionSatisfyStatement),
    Structure(StructureStatement),
    Inductive(InductiveStatement),
    Import(ImportStatement),
    Attributes(AttributesStatement),
    Numerals(NumeralsStatement),
    Problem(Body),
    Match(MatchStatement),
    Typeclass(TypeclassStatement),
    Instance(InstanceStatement),
    Todo(TodoStatement),

    /// A doc comment is not actually a statement, but it is treated like one in the parser.
    /// Has the leading /// along with leading and trailing whitespace stripped.
    DocComment(String),
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // Use the pretty-printing logic with a narrow width for mobile-friendly docs
        let allocator = pretty::Arena::<()>::new();
        let doc = self.pretty_ref(&allocator, allocator.nil());
        // Break lines really aggressively
        doc.render_fmt(1, f)?;
        Ok(())
    }
}

/// Parses a block (a list of statements) where the left brace has already been consumed.
/// Returns the statements along with the token for the final right brace.
/// Consumes the right brace, but nothing after that.
fn parse_block(tokens: &mut TokenIter) -> Result<(Vec<Statement>, Token)> {
    let mut body = Vec::new();
    loop {
        match Statement::parse(tokens, true)? {
            (Some(s), maybe_right_brace) => {
                body.push(s);
                if let Some(brace) = maybe_right_brace {
                    return Ok((body, brace));
                }
            }
            (None, Some(brace)) => {
                return Ok((body, brace));
            }
            (None, None) => {
                return Err(tokens.error("expected statement but got EOF"));
            }
        }
    }
}

/// Parse some optional arguments.
/// The tokens should either be "(args) terminator", or just the terminator.
/// Returns the arguments, and the terminator token.
fn parse_args(tokens: &mut TokenIter, terminator: TokenType) -> Result<(Vec<Declaration>, Token)> {
    let token = tokens.expect_token()?;

    if token.token_type == terminator {
        return Ok((vec![], token));
    }

    if token.token_type != TokenType::LeftParen {
        return Err(token.error("expected an argument list"));
    }

    // Parse the arguments list
    let declarations = Declaration::parse_list(tokens)?;
    let terminator = tokens.expect_type(terminator)?;
    return Ok((declarations, terminator));
}

/// Parses a by block if that's the next thing in the token stream.
/// Takes the right brace that ended the previous expression.
/// Returns the last token parsed.
/// Consumes newlines in any case.
fn parse_by_block(right_brace: Token, tokens: &mut TokenIter) -> Result<(Option<Body>, Token)> {
    loop {
        match tokens.peek() {
            Some(token) => {
                if token.token_type == TokenType::NewLine {
                    tokens.next();
                    continue;
                }
                if token.token_type != TokenType::By {
                    break;
                }
                tokens.next();
                let left_brace = tokens.expect_type(TokenType::LeftBrace)?;
                let (statements, right_brace) = parse_block(tokens)?;
                return Ok((
                    Some(Body {
                        left_brace,
                        statements,
                        right_brace: right_brace.clone(),
                    }),
                    right_brace,
                ));
            }
            None => break,
        }
    }
    Ok((None, right_brace))
}

/// Parses a theorem where the keyword identifier (axiom or theorem) has already been found.
/// "axiomatic" is whether this is an axiom.
fn parse_theorem_statement(
    keyword: Token,
    tokens: &mut TokenIter,
    axiomatic: bool,
) -> Result<Statement> {
    let name_token = match tokens.peek_type() {
        Some(TokenType::LeftParen) | Some(TokenType::LeftBrace) => None,
        _ => {
            let token = tokens.expect_variable_name(false)?;
            Some(token)
        }
    };
    let type_params = TypeParamExpr::parse_list(tokens)?;
    let (args, _) = parse_args(tokens, TokenType::LeftBrace)?;
    let (claim, claim_right_brace) =
        Expression::parse_value(tokens, Terminator::Is(TokenType::RightBrace))?;

    let (body, last_token) = parse_by_block(claim_right_brace.clone(), tokens)?;

    let ts = TheoremStatement {
        axiomatic,
        name_token,
        type_params,
        args,
        claim,
        claim_right_brace,
        body,
    };
    let statement = Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::Theorem(ts),
    };
    Ok(statement)
}

/// Finish the rest of a variable satisfy statement, after we've consumed the 'satisfy' keyword
fn complete_variable_satisfy(
    keyword: Token,
    tokens: &mut TokenIter,
    declarations: Vec<Declaration>,
) -> Result<Statement> {
    tokens.expect_type(TokenType::LeftBrace)?;
    let (condition, last_token) =
        Expression::parse_value(tokens, Terminator::Is(TokenType::RightBrace))?;
    let es = VariableSatisfyStatement {
        declarations,
        condition,
    };
    let statement = Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::VariableSatisfy(es),
    };
    Ok(statement)
}

/// Parses a statement where the "let" keyword has already been found.
/// This might not be a LetStatement because multiple statement types can start with "let".
fn parse_let_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    match tokens.peek() {
        Some(token) => {
            if token.token_type == TokenType::LeftParen {
                // This is a parenthesized let..satisfy.
                let (declarations, _) = parse_args(tokens, TokenType::Satisfy)?;
                return complete_variable_satisfy(keyword, tokens, declarations);
            }
        }
        None => return Err(tokens.error("unexpected end of file")),
    }
    let name_token = tokens.expect_variable_name(true)?;
    let _name = name_token.text().to_string();
    if let Some(token) = tokens.peek() {
        if token.token_type == TokenType::LeftParen {
            // This is a function defined via let..satisfy.
            tokens.next();
            let mut declarations = Declaration::parse_list(tokens)?;
            tokens.expect_type(TokenType::RightArrow)?;
            let (return_value, satisfy_token) =
                Declaration::parse(tokens, Terminator::Is(TokenType::Satisfy))?;
            declarations.push(return_value);
            tokens.expect_type(TokenType::LeftBrace)?;
            let (condition, right_brace) =
                Expression::parse_value(tokens, Terminator::Is(TokenType::RightBrace))?;
            let (body, last_token) = parse_by_block(right_brace, tokens)?;
            let fss = FunctionSatisfyStatement {
                name_token,
                declarations,
                satisfy_token,
                condition,
                body,
            };
            return Ok(Statement {
                first_token: keyword,
                last_token,
                statement: StatementInfo::FunctionSatisfy(fss),
            });
        }
    }
    let type_params = TypeParamExpr::parse_list(tokens)?;

    // Check if there's a colon (type annotation) or equals (type inference)
    let next_token = tokens.expect_token()?;
    let (type_expr, _middle_token) = match next_token.token_type {
        TokenType::Colon => {
            // Traditional syntax: let name: Type = value
            let (type_expr, middle_token) = Expression::parse_type(
                tokens,
                Terminator::Or(TokenType::Equals, TokenType::Satisfy),
            )?;
            if middle_token.token_type == TokenType::Satisfy {
                return complete_variable_satisfy(
                    keyword,
                    tokens,
                    vec![Declaration::Typed(name_token, type_expr)],
                );
            }
            (Some(type_expr), middle_token)
        }
        TokenType::Equals => {
            // Type inference syntax: let name = value
            (None, next_token)
        }
        _ => {
            return Err(next_token.error("expected ':' or '='"));
        }
    };

    let (value, last_token) = Expression::parse_value(tokens, Terminator::Is(TokenType::NewLine))?;
    let ls = LetStatement {
        name_token,
        type_params,
        type_expr,
        value,
    };
    Ok(Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::Let(ls),
    })
}

/// Parses a define statement where the "define" keyword has already been found.
fn parse_define_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let name_token = tokens.expect_variable_name(false)?;
    let type_params = TypeParamExpr::parse_list(tokens)?;
    let (args, _) = parse_args(tokens, TokenType::RightArrow)?;
    if args.is_empty() {
        return Err(name_token.error("Functions must have at least one argument. Use 'let' to declare values that aren't functions."));
    }
    let (return_type, _) = Expression::parse_type(tokens, Terminator::Is(TokenType::LeftBrace))?;
    let (return_value, last_token) =
        Expression::parse_value(tokens, Terminator::Is(TokenType::RightBrace))?;
    let ds = DefineStatement {
        name_token,
        type_params,
        args,
        return_type,
        return_value,
    };
    let statement = Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::Define(ds),
    };
    Ok(statement)
}

/// Parses a type statement where the "type" keyword has already been found.
fn parse_type_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let name_token = tokens.expect_type_name()?;
    tokens.expect_type(TokenType::Colon)?;
    tokens.skip_newlines();
    let (type_expr, _) = Expression::parse_type(tokens, Terminator::Is(TokenType::NewLine))?;
    let last_token = type_expr.last_token().clone();
    let ts = TypeStatement {
        name_token: name_token.clone(),
        type_expr,
    };
    let statement = Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::Type(ts),
    };
    Ok(statement)
}

/// Parses a forall statement where the "forall" keyword has already been found.
fn parse_forall_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let (quantifiers, left_brace) = parse_args(tokens, TokenType::LeftBrace)?;
    let (statements, right_brace) = parse_block(tokens)?;
    let body = Body {
        left_brace,
        statements,
        right_brace: right_brace.clone(),
    };
    let fas = ForAllStatement { quantifiers, body };
    let statement = Statement {
        first_token: keyword,
        last_token: right_brace,
        statement: StatementInfo::ForAll(fas),
    };
    Ok(statement)
}

/// If there is an "else { ...statements }" body, parse and consume it.
/// Returns None and consumes nothing if there is not an "else" body here.
fn parse_else_body(tokens: &mut TokenIter) -> Result<Option<Body>> {
    loop {
        match tokens.peek() {
            Some(token) => match token.token_type {
                TokenType::NewLine => {
                    tokens.next();
                }
                TokenType::Else => {
                    tokens.next();
                    break;
                }
                _ => return Ok(None),
            },
            None => return Ok(None),
        }
    }
    let left_brace = tokens.expect_type(TokenType::LeftBrace)?;
    let (statements, right_brace) = parse_block(tokens)?;
    let body = Body {
        left_brace,
        statements,
        right_brace,
    };
    Ok(Some(body))
}

/// Parses an if statement where the "if" keyword has already been found.
fn parse_if_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let token = tokens.peek().unwrap().clone();
    let (condition, left_brace) =
        Expression::parse_value(tokens, Terminator::Is(TokenType::LeftBrace))?;
    let (statements, right_brace) = parse_block(tokens)?;
    let body = Body {
        left_brace,
        statements,
        right_brace: right_brace.clone(),
    };
    let else_body = parse_else_body(tokens)?;
    let is = IfStatement {
        condition,
        body,
        else_body,
        token,
    };
    let statement = Statement {
        first_token: keyword,
        last_token: right_brace,
        statement: StatementInfo::If(is),
    };
    Ok(statement)
}

/// Parses a structure statement where the "structure" keyword has already been found.
fn parse_structure_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let name_token = tokens.expect_type_name()?;
    let type_params = TypeParamExpr::parse_list(tokens)?;
    tokens.expect_type(TokenType::LeftBrace)?;
    let mut fields = vec![];
    let mut doc_comments = vec![];
    while let Some(token) = tokens.peek() {
        match token.token_type {
            TokenType::NewLine => {
                tokens.next();
            }
            TokenType::RightBrace => {
                if fields.len() == 0 {
                    return Err(token.error("structs must have at least one field"));
                }
                let right_brace = tokens.next().unwrap();
                let first_right_brace = right_brace.clone();

                // Check for a constraint
                let (constraint, body, last_token) = match tokens.peek() {
                    Some(token) => match token.token_type {
                        TokenType::Constraint => {
                            tokens.next();
                            tokens.expect_type(TokenType::LeftBrace)?;
                            let (constraint, right_brace) = Expression::parse_value(
                                tokens,
                                Terminator::Is(TokenType::RightBrace),
                            )?;
                            let (body, last_token) = parse_by_block(right_brace, tokens)?;
                            (Some(constraint), body, last_token)
                        }
                        _ => (None, None, right_brace),
                    },
                    None => (None, None, right_brace),
                };

                return Ok(Statement {
                    first_token: keyword,
                    last_token,
                    statement: StatementInfo::Structure(StructureStatement {
                        name_token,
                        type_params,
                        fields,
                        first_right_brace,
                        constraint,
                        body,
                    }),
                });
            }
            TokenType::DocComment => {
                // Collect doc comment
                let doc_token = tokens.next().unwrap();
                doc_comments.push(doc_token.doc_comment_content());
            }
            _ => {
                let token = tokens.expect_variable_name(false)?;
                tokens.expect_type(TokenType::Colon)?;
                let (type_expr, t) = Expression::parse_type(
                    tokens,
                    Terminator::Or(TokenType::NewLine, TokenType::RightBrace),
                )?;
                if t.token_type == TokenType::RightBrace {
                    return Err(t.error("field declarations must end with a newline"));
                }
                fields.push((token, type_expr, doc_comments.clone()));
                doc_comments.clear();
            }
        }
    }
    Err(keyword.error("unterminated structure statement"))
}

/// Parses an inductive statement where the "inductive" keyword has already been found.
fn parse_inductive_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let type_token = tokens.expect_type_name()?;
    let type_params = TypeParamExpr::parse_list(tokens)?;
    tokens.expect_type(TokenType::LeftBrace)?;
    let mut constructors = vec![];
    let mut doc_comments = vec![];
    loop {
        let next_type = match tokens.peek() {
            Some(token) => token.token_type,
            None => break,
        };
        match next_type {
            TokenType::NewLine => {
                tokens.next();
                continue;
            }
            TokenType::RightBrace => {
                if constructors.len() == 0 {
                    return Err(type_token.error("inductive types must have a constructor"));
                }
                return Ok(Statement {
                    first_token: keyword,
                    last_token: tokens.next().unwrap(),
                    statement: StatementInfo::Inductive(InductiveStatement {
                        name_token: type_token,
                        type_params,
                        constructors,
                    }),
                });
            }
            TokenType::DocComment => {
                // Collect doc comment
                let doc_token = tokens.next().unwrap();
                doc_comments.push(doc_token.doc_comment_content());
                continue;
            }
            _ => {}
        }
        let name_token = tokens.expect_variable_name(true)?;
        let next_type = match tokens.peek() {
            Some(token) => token.token_type,
            None => break,
        };
        if next_type == TokenType::NewLine {
            // A no-argument constructor
            constructors.push((name_token, None, doc_comments.clone()));
            doc_comments.clear();
            continue;
        }
        if next_type != TokenType::LeftParen {
            return Err(name_token.error("expected a constructor definition"));
        }
        let (type_list_expr, _) =
            Expression::parse_type(tokens, Terminator::Is(TokenType::NewLine))?;
        constructors.push((name_token, Some(type_list_expr), doc_comments.clone()));
        doc_comments.clear();
    }
    Err(keyword.error("unterminated inductive statement"))
}

/// Parses a module component list, like "foo.bar.baz".
/// Expects to consume a terminator token at the end.
/// Returns the component tokens, along with the token right before the terminator.
fn parse_module_components(
    tokens: &mut TokenIter,
    terminator: TokenType,
) -> Result<(Vec<Token>, Token)> {
    let mut components = Vec::new();
    let last_token = loop {
        let token = tokens.expect_type(TokenType::Identifier)?;
        components.push(token);
        let token = tokens.expect_token()?;
        if token.token_type == terminator {
            break token;
        }
        match token.token_type {
            TokenType::Dot => continue,
            _ => return Err(token.error("unexpected token in module path")),
        }
    };
    Ok((components, last_token))
}

/// Parses an import statement where the "import" keyword has already been found.
fn parse_import_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let (components, last_token) = parse_module_components(tokens, TokenType::NewLine)?;
    let is = ImportStatement {
        components,
        names: vec![],
    };
    let statement = Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::Import(is),
    };
    Ok(statement)
}

/// Parses a "from" statement where the "from" keyword has already been found.
fn parse_from_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let (components, _) = parse_module_components(tokens, TokenType::Import)?;
    let mut names = vec![];
    let last_token = loop {
        let token = tokens.expect_type(TokenType::Identifier)?;
        let separator = tokens.expect_token()?;
        match separator.token_type {
            TokenType::NewLine => {
                names.push(token.clone());
                break token;
            }
            TokenType::Comma => {
                names.push(token);
                continue;
            }
            _ => {
                return Err(token.error("expected comma or newline"));
            }
        }
    };
    let is = ImportStatement { components, names };
    let statement = Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::Import(is),
    };
    Ok(statement)
}

/// Parses an attributes statement where the "class" or "attributes" keyword has already been found.
fn parse_attributes_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let first_name = tokens.expect_type_name()?;

    // Check if we have the typeclass syntax (M: TypeclassName) or type syntax (TypeName)
    let (instance_name, _name, name_token) = match tokens.peek_type() {
        Some(TokenType::Colon) => {
            // Typeclass syntax: attributes M: TypeclassName
            tokens.next(); // consume ':'
            let typeclass_name = tokens.expect_type_name()?;
            (
                Some(first_name.clone()),
                typeclass_name.text().to_string(),
                typeclass_name,
            )
        }
        _ => {
            // Type syntax: attributes TypeName
            (None, first_name.text().to_string(), first_name)
        }
    };

    let type_params = TypeParamExpr::parse_list(tokens)?;
    let left_brace = tokens.expect_type(TokenType::LeftBrace)?;
    let (statements, right_brace) = parse_block(tokens)?;
    let body = Body {
        left_brace,
        statements,
        right_brace: right_brace.clone(),
    };
    let ats = AttributesStatement {
        name_token,
        type_params,
        instance_name,
        body,
    };
    let statement = Statement {
        first_token: keyword,
        last_token: right_brace,
        statement: StatementInfo::Attributes(ats),
    };
    Ok(statement)
}

/// Parses a match statement where the "match" keyword has already been found.
fn parse_match_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let (scrutinee, _) = Expression::parse_value(tokens, Terminator::Is(TokenType::LeftBrace))?;
    let mut cases = vec![];
    loop {
        let next_type = match tokens.peek() {
            Some(token) => token.token_type,
            None => return Err(keyword.error("unterminated match statement")),
        };
        if next_type == TokenType::NewLine {
            tokens.next();
            continue;
        }
        if next_type == TokenType::RightBrace {
            break;
        }
        let (pattern, left_brace) =
            Expression::parse_value(tokens, Terminator::Is(TokenType::LeftBrace))?;
        let (statements, right_brace) = parse_block(tokens)?;
        let body = Body {
            left_brace,
            statements,
            right_brace,
        };
        cases.push((pattern, body));
    }
    tokens.expect_type(TokenType::RightBrace)?;
    let last_token = match cases.last() {
        Some((_, body)) => body.right_brace.clone(),
        None => return Err(keyword.error("match must have cases")),
    };
    let ms = MatchStatement { scrutinee, cases };
    Ok(Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::Match(ms),
    })
}

/// Parses a typeclass statement where the "typeclass" keyword has already been found.
fn parse_typeclass_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let first_name = tokens.expect_type_name()?;

    // Check if we have the block syntax (Q: TypeclassName) or no-block syntax (TypeclassName extends ...)
    let (instance_name, typeclass_name) = match tokens.peek_type() {
        Some(TokenType::Colon) => {
            // Block syntax: typeclass Q: TypeclassName
            tokens.next(); // consume ':'
            let typeclass_name = tokens.expect_type_name()?;
            (Some(first_name), typeclass_name)
        }
        Some(TokenType::Extends) | Some(TokenType::NewLine) | Some(TokenType::LeftBrace) | None => {
            // No-block syntax: typeclass TypeclassName extends ... or just typeclass TypeclassName
            // In this case, we don't have an instance type
            (None, first_name)
        }
        _ => {
            return Err(keyword
                .error("expected ':' for block syntax or 'extends'/'{'  for no-block syntax"));
        }
    };

    // Check for "extends" keyword and parse the extended typeclasses
    let mut extends = vec![];
    let has_block = match tokens.peek_type() {
        Some(TokenType::LeftBrace) => {
            // No extends, has block
            tokens.next();
            true
        }
        Some(TokenType::Extends) => {
            tokens.next();
            loop {
                // Parse a single type expression (just the identifier)
                let type_token = tokens.expect_type_name()?;
                let type_expr = Expression::Singleton(type_token);
                extends.push(type_expr);

                // Check what comes next
                match tokens.peek_type() {
                    Some(TokenType::Comma) => {
                        tokens.next(); // consume comma
                                       // Check if the next thing after comma is EOF/newline (no block)
                        match tokens.peek_type() {
                            Some(TokenType::NewLine) | None => {
                                break false;
                            }
                            _ => {
                                // Continue parsing more extends
                                continue;
                            }
                        }
                    }
                    Some(TokenType::LeftBrace) => {
                        tokens.next(); // consume left brace
                        break true; // has block
                    }
                    Some(TokenType::NewLine) | None => {
                        // End of extends clause, no block
                        break false;
                    }
                    _ => {
                        return Err(keyword.error(
                            "expected ',' or '{' or newline/EOF after typeclass name in extends",
                        ));
                    }
                }
            }
        }
        Some(TokenType::NewLine) | None => {
            // No extends, no block (newline or EOF)
            false
        }
        _ => {
            return Err(
                keyword.error("expected 'extends', '{', newline, or EOF after typeclass name")
            );
        }
    };

    let mut constants = vec![];
    let mut conditions = vec![];
    let mut doc_comments = vec![];

    if !has_block {
        // No-block syntax - just return the typeclass with extends only
        if extends.is_empty() {
            return Err(keyword.error("Typeclass without block must extend at least one typeclass"));
        }

        // Find the last token for this statement
        let last_token = if let Some(ref last_extend) = extends.last() {
            last_extend.last_token().clone()
        } else {
            typeclass_name.clone()
        };

        return Ok(Statement {
            first_token: keyword,
            last_token,
            statement: StatementInfo::Typeclass(TypeclassStatement {
                instance_name,
                typeclass_name,
                extends,
                constants,
                conditions,
            }),
        });
    }

    while let Some(token) = tokens.next() {
        match token.token_type {
            TokenType::NewLine => {
                continue;
            }
            TokenType::DocComment => {
                // Collect doc comment
                doc_comments.push(token.doc_comment_content());
                continue;
            }
            TokenType::RightBrace => {
                if constants.is_empty() && conditions.is_empty() && extends.len() < 2 {
                    return Err(token.error(
                        "This typeclass is redundant, because it has no constants or conditions.",
                    ));
                }

                return Ok(Statement {
                    first_token: keyword,
                    last_token: token,
                    statement: StatementInfo::Typeclass(TypeclassStatement {
                        instance_name,
                        typeclass_name,
                        extends,
                        constants,
                        conditions,
                    }),
                });
            }
            TokenType::Identifier | TokenType::Numeral => {
                let next_type = tokens.peek_type();
                match next_type {
                    Some(TokenType::LeftParen) => {
                        // Theorem with args
                        let (args, _) = parse_args(tokens, TokenType::LeftBrace)?;
                        let (claim, _) =
                            Expression::parse_value(tokens, Terminator::Is(TokenType::RightBrace))?;
                        let condition = TypeclassCondition {
                            name_token: token,
                            args,
                            claim,
                            doc_comments: doc_comments.clone(),
                        };
                        conditions.push(condition);
                        doc_comments.clear();
                    }
                    Some(TokenType::LeftBrace) => {
                        // Theorem with no args
                        tokens.next();
                        let (claim, _) =
                            Expression::parse_value(tokens, Terminator::Is(TokenType::RightBrace))?;
                        let condition = TypeclassCondition {
                            name_token: token,
                            args: vec![],
                            claim,
                            doc_comments: doc_comments.clone(),
                        };
                        conditions.push(condition);
                        doc_comments.clear();
                    }
                    Some(TokenType::Colon) => {
                        // Constant
                        tokens.next();
                        let (type_expr, t) = Expression::parse_type(
                            tokens,
                            Terminator::Or(TokenType::NewLine, TokenType::RightBrace),
                        )?;
                        if t.token_type == TokenType::RightBrace {
                            return Err(t.error("typeclass declarations must end with a newline"));
                        }
                        constants.push((token, type_expr, doc_comments.clone()));
                        doc_comments.clear();
                    }
                    _ => {
                        return Err(
                            token.error("expected ':' or '(' after name in typeclass statement")
                        );
                    }
                }
            }
            _ => {
                return Err(token.error("unexpected token in typeclass statement"));
            }
        }
    }
    Err(keyword.error("unterminated typeclass statement"))
}

/// Parses an instance statement where the "instance" keyword has already been found.
fn parse_instance_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let type_name = tokens.expect_type_name()?;
    tokens.expect_type(TokenType::Colon)?;

    // Parse the typeclass expression, which can end with either '{' (block syntax) or newline/EOF (no-block syntax)
    let (typeclass, terminator) = Expression::parse_type(
        tokens,
        Terminator::Or(TokenType::LeftBrace, TokenType::NewLine),
    )?;

    let (definitions, body, last_token) = match terminator.token_type {
        TokenType::LeftBrace => {
            // Block syntax: instance Type: Typeclass { ... }
            let (statements, right_brace) = parse_block(tokens)?;
            let definitions = Body {
                left_brace: terminator,
                statements,
                right_brace: right_brace.clone(),
            };
            let (body, last_token) = parse_by_block(right_brace, tokens)?;
            (Some(definitions), body, last_token)
        }
        TokenType::NewLine => {
            // No-block syntax: instance Type: Typeclass
            (None, None, typeclass.last_token().clone())
        }
        _ => {
            // Handle EOF case (when input doesn't end with newline)
            if tokens.peek().is_none() {
                (None, None, typeclass.last_token().clone())
            } else {
                return Err(terminator
                    .error("expected '{' or newline after typeclass in instance statement"));
            }
        }
    };

    let is = InstanceStatement {
        type_name,
        typeclass,
        definitions,
        body,
    };
    let statement = Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::Instance(is),
    };
    Ok(statement)
}

fn parse_todo_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let left_brace = tokens.expect_type(TokenType::LeftBrace)?;
    let (statements, right_brace) = parse_block(tokens)?;
    let body = Body {
        left_brace,
        statements,
        right_brace: right_brace.clone(),
    };
    let ts = TodoStatement { body };
    let statement = Statement {
        first_token: keyword,
        last_token: right_brace,
        statement: StatementInfo::Todo(ts),
    };
    Ok(statement)
}

impl Statement {
    /// Tries to parse a single statement from the provided tokens.
    /// If in_block is true, we might get a right brace instead of a statement.
    /// Returns statement, as well as the right brace token, if the current block ended.
    /// Returns Ok((None, None)) if the end of the file was reached.
    ///
    /// Normally, this function consumes the final newline.
    /// When it's a right brace that ends a block, though, the last token consumed is the right brace.
    pub fn parse(
        tokens: &mut TokenIter,
        in_block: bool,
    ) -> Result<(Option<Statement>, Option<Token>)> {
        loop {
            if let Some(token) = tokens.peek() {
                match token.token_type {
                    TokenType::NewLine => {
                        tokens.next();
                        continue;
                    }
                    TokenType::Let => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_let_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Axiom => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_theorem_statement(keyword, tokens, true)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Theorem => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_theorem_statement(keyword, tokens, false)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Define => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_define_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Type => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_type_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::RightBrace => {
                        if !in_block {
                            return Err(token.error("unmatched right brace at top level"));
                        }
                        let brace = tokens.next().unwrap();

                        return Ok((None, Some(brace)));
                    }
                    TokenType::ForAll => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_forall_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::If => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_if_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Structure => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_structure_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Inductive => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_inductive_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Import => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_import_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Class | TokenType::Attributes => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_attributes_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Numerals => {
                        let keyword = tokens.next().unwrap();
                        let (type_expr, last_token) =
                            Expression::parse_type(tokens, Terminator::Is(TokenType::NewLine))?;
                        let ds = NumeralsStatement { type_expr };
                        let s = Statement {
                            first_token: keyword,
                            last_token,
                            statement: StatementInfo::Numerals(ds),
                        };
                        return Ok((Some(s), None));
                    }
                    TokenType::From => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_from_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Solve => {
                        let keyword = tokens.next().unwrap();
                        return Err(CompilationError::new(
                            &keyword,
                            &keyword,
                            "the 'solve' keyword is no longer supported",
                        ));
                    }
                    TokenType::Problem => {
                        let keyword = tokens.next().unwrap();
                        let left_brace = tokens.expect_type(TokenType::LeftBrace)?;
                        let (statements, right_brace) = parse_block(tokens)?;
                        let body = Body {
                            left_brace,
                            statements,
                            right_brace: right_brace.clone(),
                        };
                        let s = Statement {
                            first_token: keyword,
                            last_token: right_brace,
                            statement: StatementInfo::Problem(body),
                        };
                        return Ok((Some(s), None));
                    }
                    TokenType::Match => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_match_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Typeclass => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_typeclass_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Instance => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_instance_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Todo => {
                        let keyword = tokens.next().unwrap();
                        let s = parse_todo_statement(keyword, tokens)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::DocComment => {
                        let doc_token = tokens.next().unwrap();
                        let content = doc_token.doc_comment_content();
                        let s = Statement {
                            first_token: doc_token.clone(),
                            last_token: doc_token,
                            statement: StatementInfo::DocComment(content),
                        };
                        return Ok((Some(s), None));
                    }
                    _ => {
                        if !in_block {
                            return Err(token.error("unexpected token at the top level"));
                        }
                        let first_token = tokens.peek().unwrap().clone();
                        let (claim, token) = Expression::parse_value(
                            tokens,
                            Terminator::Or(TokenType::NewLine, TokenType::RightBrace),
                        )?;
                        let block_ended = token.token_type == TokenType::RightBrace;
                        let brace = if block_ended { Some(token) } else { None };
                        let last_token = claim.last_token().clone();
                        let se = StatementInfo::Claim(ClaimStatement { claim });
                        let s = Statement {
                            first_token,
                            last_token,
                            statement: se,
                        };
                        return Ok((Some(s), brace));
                    }
                }
            } else {
                return Ok((None, None));
            }
        }
    }

    pub fn parse_str(input: &str) -> Result<Statement> {
        Statement::parse_str_with_options(input, false)
    }

    pub fn parse_str_with_options(input: &str, in_block: bool) -> Result<Statement> {
        let tokens = Token::scan(input);
        let mut tokens = TokenIter::new(tokens);
        match Statement::parse(&mut tokens, in_block)? {
            (Some(statement), _) => Ok(statement),
            _ => panic!("expected statement, got EOF"),
        }
    }

    pub fn range(&self) -> Range {
        Range {
            start: self.first_token.start_pos(),
            end: self.last_token.end_pos(),
        }
    }

    pub fn first_line(&self) -> u32 {
        self.first_token.start_pos().line
    }

    pub fn last_line(&self) -> u32 {
        self.last_token.end_pos().line
    }
}

impl<'a, D, A> Pretty<'a, D, A> for &'a Statement
where
    A: 'a,
    D: DocAllocator<'a, A>,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        self.pretty_ref(allocator, allocator.nil())
    }
}

impl Statement {
    fn pretty_ref<'a, D, A>(
        &'a self,
        allocator: &'a D,
        indent: DocBuilder<'a, D, A>,
    ) -> DocBuilder<'a, D, A>
    where
        A: 'a,
        D: DocAllocator<'a, A>,
    {
        let doc = match &self.statement {
            StatementInfo::Let(ls) => {
                let mut doc = allocator
                    .text("let ")
                    .append(allocator.text(ls.name_token.text()));
                doc = write_type_params_pretty(allocator, doc, &ls.type_params);
                match &ls.type_expr {
                    Some(type_expr) => doc
                        .append(allocator.text(": "))
                        .append(type_expr.pretty_ref(allocator))
                        .append(allocator.text(" = "))
                        .append(ls.value.pretty_ref(allocator)),
                    None => doc
                        .append(allocator.text(" = "))
                        .append(ls.value.pretty_ref(allocator)),
                }
            }

            StatementInfo::Define(ds) => {
                let mut doc = allocator
                    .text("define ")
                    .append(allocator.text(ds.name_token.text()));
                doc = write_type_params_pretty(allocator, doc, &ds.type_params);
                doc = write_args_pretty(allocator, doc, &ds.args);
                doc.append(allocator.text(" -> "))
                    .append(ds.return_type.pretty_ref(allocator))
                    .append(allocator.text(" {"))
                    .append(
                        allocator
                            .hardline()
                            .append(ds.return_value.pretty_ref(allocator))
                            .nest(4),
                    )
                    .append(allocator.hardline())
                    .append(allocator.text("}"))
            }

            StatementInfo::Theorem(ts) => {
                let mut doc = if ts.axiomatic {
                    allocator.text("axiom")
                } else {
                    allocator.text("theorem")
                };
                if let Some(name_token) = &ts.name_token {
                    doc = doc
                        .append(allocator.text(" "))
                        .append(allocator.text(name_token.text()));
                }
                doc = write_theorem_pretty(allocator, doc, &ts.type_params, &ts.args, &ts.claim);
                if let Some(body) = &ts.body {
                    doc = doc.append(allocator.text(" by"));
                    doc = write_block_pretty(allocator, doc, &body.statements);
                }
                doc
            }

            StatementInfo::Claim(ps) => ps.claim.pretty_ref(allocator),

            StatementInfo::Type(ts) => allocator
                .text("type ")
                .append(allocator.text(ts.name_token.text()))
                .append(allocator.text(": "))
                .append(ts.type_expr.pretty_ref(allocator)),

            StatementInfo::ForAll(fas) => {
                let mut doc = allocator.text("forall");
                doc = write_args_pretty(allocator, doc, &fas.quantifiers);
                write_block_pretty(allocator, doc, &fas.body.statements).group()
            }

            StatementInfo::If(is) => {
                let mut doc = allocator
                    .text("if ")
                    .append(is.condition.pretty_ref(allocator));
                doc = write_block_pretty(allocator, doc, &is.body.statements);
                if let Some(else_body) = &is.else_body {
                    doc = doc.append(allocator.text(" else"));
                    doc = write_block_pretty(allocator, doc, &else_body.statements);
                }
                doc.group()
            }

            StatementInfo::VariableSatisfy(vss) => {
                let mut doc = allocator.text("let ");
                if vss.declarations.len() == 1 {
                    doc = doc.append(vss.declarations[0].pretty_ref(allocator));
                } else {
                    doc = write_args_pretty(allocator, doc, &vss.declarations);
                }
                doc.append(allocator.text(" satisfy {"))
                    .append(
                        allocator
                            .hardline()
                            .append(vss.condition.pretty_ref(allocator))
                            .nest(4),
                    )
                    .append(allocator.hardline())
                    .append(allocator.text("}"))
            }

            StatementInfo::FunctionSatisfy(fss) => {
                let mut doc = allocator
                    .text("let ")
                    .append(allocator.text(fss.name_token.text()));
                let i = fss.declarations.len() - 1;
                doc = write_args_pretty(allocator, doc, &fss.declarations[..i]);
                doc = doc
                    .append(allocator.text(" -> "))
                    .append(fss.declarations[i].pretty_ref(allocator))
                    .append(allocator.text(" satisfy {"))
                    .append(
                        allocator
                            .line()
                            .nest(4)
                            .append(fss.condition.pretty_ref(allocator))
                            .nest(4),
                    )
                    .append(allocator.line())
                    .append(allocator.text("}"));
                if let Some(body) = &fss.body {
                    doc = doc.append(allocator.text(" by"));
                    doc = write_block_pretty(allocator, doc, &body.statements);
                }
                doc.group()
            }

            StatementInfo::Structure(ss) => {
                let mut doc = allocator
                    .text("structure ")
                    .append(allocator.text(ss.name_token.text()));
                doc = write_type_params_pretty(allocator, doc, &ss.type_params);
                doc = doc.append(allocator.text(" {"));
                let mut fields_inner = allocator.nil();
                for (name, type_expr, _doc_comments) in &ss.fields {
                    fields_inner = fields_inner
                        .append(allocator.hardline())
                        .append(allocator.text(name.text()))
                        .append(allocator.text(": "))
                        .append(type_expr.pretty_ref(allocator));
                }
                doc = doc
                    .append(fields_inner.nest(4))
                    .append(allocator.hardline())
                    .append(allocator.text("}"));
                if let Some(constraint) = &ss.constraint {
                    doc = doc
                        .append(allocator.text(" constraint {"))
                        .append(
                            allocator
                                .hardline()
                                .append(constraint.pretty_ref(allocator))
                                .nest(4),
                        )
                        .append(allocator.hardline())
                        .append(allocator.text("}"));
                }
                if let Some(body) = &ss.body {
                    doc = doc.append(allocator.text(" by"));
                    doc = write_block_pretty(allocator, doc, &body.statements);
                }
                doc.group()
            }

            StatementInfo::Inductive(is) => {
                let mut doc = allocator
                    .text("inductive ")
                    .append(allocator.text(is.name_token.text()));
                doc = write_type_params_pretty(allocator, doc, &is.type_params);
                doc = doc.append(allocator.text(" {"));
                let mut inner = allocator.nil();
                for (name, type_expr, _doc_comments) in &is.constructors {
                    inner = inner
                        .append(allocator.hardline())
                        .append(allocator.text(name.text()));
                    if let Some(te) = type_expr {
                        inner = inner.append(te.pretty_ref(allocator));
                    }
                }
                doc.append(inner.nest(4))
                    .append(allocator.hardline())
                    .append(allocator.text("}"))
            }

            StatementInfo::Import(is) => {
                if is.names.is_empty() {
                    let module_path = is
                        .components
                        .iter()
                        .map(|t| t.text())
                        .collect::<Vec<_>>()
                        .join(".");
                    allocator
                        .text("import ")
                        .append(allocator.text(module_path))
                } else {
                    let module_path = is
                        .components
                        .iter()
                        .map(|t| t.text())
                        .collect::<Vec<_>>()
                        .join(".");
                    let names = is
                        .names
                        .iter()
                        .map(|t| t.text())
                        .collect::<Vec<_>>()
                        .join(", ");
                    allocator
                        .text("from ")
                        .append(allocator.text(module_path))
                        .append(allocator.text(" import "))
                        .append(allocator.text(names))
                }
            }

            StatementInfo::Attributes(ats) => {
                let mut doc = allocator.text("attributes ");
                if let Some(instance_name) = &ats.instance_name {
                    doc = doc
                        .append(allocator.text(instance_name.text()))
                        .append(allocator.text(": "))
                        .append(allocator.text(ats.name_token.text()));
                } else {
                    doc = doc.append(allocator.text(ats.name_token.text()));
                }
                doc = write_type_params_pretty(allocator, doc, &ats.type_params);
                write_block_pretty(allocator, doc, &ats.body.statements).group()
            }

            StatementInfo::Numerals(ds) => allocator
                .text("default ")
                .append(ds.type_expr.pretty_ref(allocator)),

            StatementInfo::Problem(body) => {
                let doc = allocator.text("problem");
                write_block_pretty(allocator, doc, &body.statements).group()
            }

            StatementInfo::Todo(ts) => {
                let doc = allocator.text("todo");
                write_block_pretty(allocator, doc, &ts.body.statements).group()
            }

            StatementInfo::Match(ms) => {
                let doc = allocator
                    .text("match ")
                    .append(ms.scrutinee.pretty_ref(allocator))
                    .append(allocator.text(" {"));
                let mut inner = allocator.nil();
                for (pattern, body) in &ms.cases {
                    inner = inner
                        .append(allocator.hardline())
                        .append(pattern.pretty_ref(allocator));
                    inner = write_block_pretty(allocator, inner, &body.statements);
                }
                doc.append(inner.nest(4))
                    .append(allocator.hardline())
                    .append(allocator.text("}"))
            }

            StatementInfo::Typeclass(ts) => {
                let mut doc = allocator.text("typeclass ");
                if let Some(instance_name) = &ts.instance_name {
                    doc = doc
                        .append(allocator.text(instance_name.text()))
                        .append(allocator.text(": "))
                        .append(allocator.text(ts.typeclass_name.text()));
                } else {
                    doc = doc.append(allocator.text(ts.typeclass_name.text()));
                }
                if !ts.extends.is_empty() {
                    doc = doc.append(allocator.text(" extends "));
                    for (i, typeclass) in ts.extends.iter().enumerate() {
                        if i > 0 {
                            doc = doc.append(allocator.text(", "));
                        }
                        doc = doc.append(typeclass.pretty_ref(allocator));
                    }
                }
                if !ts.constants.is_empty() || !ts.conditions.is_empty() {
                    doc = doc.append(allocator.text(" {"));
                    let mut inner = allocator.nil();
                    for (name, type_expr, _doc_comments) in &ts.constants {
                        inner = inner
                            .append(allocator.hardline())
                            .append(allocator.text(name.text()))
                            .append(allocator.text(": "))
                            .append(type_expr.pretty_ref(allocator));
                    }
                    for theorem in &ts.conditions {
                        inner = inner
                            .append(allocator.hardline())
                            .append(theorem.pretty_ref(allocator));
                    }
                    doc = doc
                        .append(inner.nest(4))
                        .append(allocator.hardline())
                        .append(allocator.text("}"));
                }
                doc
            }

            StatementInfo::Instance(is) => {
                let mut doc = allocator
                    .text("instance ")
                    .append(allocator.text(is.type_name.text()))
                    .append(allocator.text(": "))
                    .append(is.typeclass.pretty_ref(allocator));
                if let Some(definitions) = &is.definitions {
                    doc = write_block_pretty(allocator, doc, &definitions.statements);
                }
                doc.group()
            }

            StatementInfo::DocComment(s) => allocator.text("/// ").append(allocator.text(s)),
        };

        indent.append(doc)
    }
}

fn write_type_params_pretty<'a, D, A>(
    allocator: &'a D,
    doc: DocBuilder<'a, D, A>,
    type_params: &'a [TypeParamExpr],
) -> DocBuilder<'a, D, A>
where
    A: 'a,
    D: DocAllocator<'a, A>,
{
    if type_params.is_empty() {
        return doc;
    }
    let mut result = doc.append(allocator.text("["));
    for (i, param) in type_params.iter().enumerate() {
        if i > 0 {
            result = result.append(allocator.text(", "));
        }
        result = result.append(param.pretty_ref(allocator));
    }
    result.append(allocator.text("]"))
}

fn write_args_pretty<'a, D, A>(
    allocator: &'a D,
    doc: DocBuilder<'a, D, A>,
    args: &'a [Declaration],
) -> DocBuilder<'a, D, A>
where
    A: 'a,
    D: DocAllocator<'a, A>,
{
    if args.is_empty() {
        return doc;
    }
    let mut result = doc.append(allocator.text("("));
    for (i, arg) in args.iter().enumerate() {
        if i > 0 {
            result = result.append(allocator.text(", "));
        }
        result = result.append(arg.pretty_ref(allocator));
    }
    result.append(allocator.text(")"))
}

fn write_theorem_pretty<'a, D, A>(
    allocator: &'a D,
    doc: DocBuilder<'a, D, A>,
    type_params: &'a [TypeParamExpr],
    args: &'a [Declaration],
    claim: &'a Expression,
) -> DocBuilder<'a, D, A>
where
    A: 'a,
    D: DocAllocator<'a, A>,
{
    let mut result = write_type_params_pretty(allocator, doc, type_params);
    result = write_args_pretty(allocator, result, args);
    result
        .append(allocator.text(" {"))
        .append(
            allocator
                .hardline()
                .append(claim.pretty_ref(allocator))
                .nest(4),
        )
        .append(allocator.hardline())
        .append(allocator.text("}"))
}

fn write_block_pretty<'a, D, A>(
    allocator: &'a D,
    doc: DocBuilder<'a, D, A>,
    statements: &'a [Statement],
) -> DocBuilder<'a, D, A>
where
    A: 'a,
    D: DocAllocator<'a, A>,
{
    let mut inner = allocator.nil();
    for s in statements {
        inner = inner
            .append(allocator.hardline())
            .append(s.pretty_ref(allocator, allocator.nil()));
    }
    doc.append(allocator.text(" {"))
        .append(inner.nest(4))
        .append(allocator.hardline())
        .append(allocator.text("}"))
}

impl TypeParamExpr {
    fn pretty_ref<'a, D, A>(&'a self, allocator: &'a D) -> DocBuilder<'a, D, A>
    where
        A: 'a,
        D: DocAllocator<'a, A>,
    {
        match &self.typeclass {
            None => allocator.text(self.name.text()),
            Some(typeclass) => allocator
                .text(self.name.text())
                .append(allocator.text(": "))
                .append(typeclass.pretty_ref(allocator)),
        }
    }
}

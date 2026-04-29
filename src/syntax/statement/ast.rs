use super::*;

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

    /// What the constant is parameterized by, if anything.
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
    pub type_params: Vec<TypeParamExpr>,
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
/// It can also be polymorphic:
///   let foo[T]: T satisfy {
///     bar(foo)
///   }
pub struct VariableSatisfyStatement {
    pub type_params: Vec<TypeParamExpr>,
    pub declarations: Vec<Declaration>,
    pub condition: Expression,
}

/// A function satisfy statement introduces a new function to the outside block,
/// by giving a condition that the output of the function obeys, and claiming that
/// there is such a function.
/// It's like a combination of a "define" and a "theorem".
/// It can also be polymorphic:
///   let flip[T](a: T) -> b: T satisfy {
///     a = b
///   }
pub struct FunctionSatisfyStatement {
    /// Name of the new function.
    pub name_token: Token,

    /// Type parameters for polymorphic function satisfy.
    pub type_params: Vec<TypeParamExpr>,

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
    /// Constrained types may be empty, so the body is ignored.
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
    /// This cannot be empty - must use "from foo import bar" syntax.
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

    /// Parameters for a family-wide instance scheme.
    pub type_params: Vec<TypeParamExpr>,

    /// The typeclass that the type is an instance of.
    pub typeclass: Expression,

    /// Definitions of each constant the typeclass requires.
    /// This is None for the no-block syntax when no definitions are needed.
    pub definitions: Option<Body>,

    /// The body is a proof that the type is an instance of the typeclass, if needed.
    pub body: Option<Body>,
}

/// A destructuring statement defines arguments by giving a function to call on them to
/// equal a value.
/// Like "let Pair.new(a, b) = p".
pub struct DestructuringStatement {
    /// The function being called.
    /// "Pair.new" in "let Pair.new(a, b) = p".
    pub function: Expression,

    /// The arguments to the function.
    /// a, b in "let Pair.new(a, b) = p".
    pub args: Vec<Token>,

    /// The value that is being destructured.
    /// p in "let Pair.new(a, b) = p".
    pub value: Expression,

    /// The body is a proof that this destructuring is satisfiable, if needed.
    pub body: Option<Body>,
}

/// Acorn is a statement-based language. There are several types.
/// Each type has its own struct.
pub struct Statement {
    pub first_token: Token,
    pub last_token: Token,
    pub statement: StatementInfo,
}

impl ErrorContext for Statement {
    fn error(&self, message: &str) -> Error {
        Error::new(&self.first_token, &self.last_token, message)
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
    Match(MatchStatement),
    Typeclass(TypeclassStatement),
    Instance(InstanceStatement),
    Destructuring(DestructuringStatement),

    /// A doc comment is not actually a statement, but it is treated like one in the parser.
    /// Has the leading /// along with leading and trailing whitespace stripped.
    DocComment(String),
}

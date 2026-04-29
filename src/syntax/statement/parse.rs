use super::ast::*;
use super::*;

/// Parses a block (a list of statements) where the left brace has already been consumed.
/// Returns the statements along with the token for the final right brace.
/// Consumes the right brace, but nothing after that.
fn parse_block(tokens: &mut TokenIter, strict: bool) -> Result<(Vec<Statement>, Token)> {
    let mut body = Vec::new();
    loop {
        match Statement::parse(tokens, true, strict)? {
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

    let declarations = Declaration::parse_list(tokens)?;
    let terminator = tokens.expect_type(terminator)?;
    Ok((declarations, terminator))
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
                let (statements, right_brace) = parse_block(tokens, false)?;
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
    Ok(Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::Theorem(ts),
    })
}

/// Finish the rest of a variable satisfy statement, after we've consumed the 'satisfy' keyword
fn complete_variable_satisfy(
    keyword: Token,
    tokens: &mut TokenIter,
    type_params: Vec<TypeParamExpr>,
    declarations: Vec<Declaration>,
) -> Result<Statement> {
    tokens.expect_type(TokenType::LeftBrace)?;
    let (condition, last_token) =
        Expression::parse_value(tokens, Terminator::Is(TokenType::RightBrace))?;
    let es = VariableSatisfyStatement {
        type_params,
        declarations,
        condition,
    };
    Ok(Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::VariableSatisfy(es),
    })
}

/// Parses a statement where the "let" keyword has already been found.
/// This might not be a LetStatement because multiple statement types can start with "let".
fn parse_let_statement(keyword: Token, tokens: &mut TokenIter, strict: bool) -> Result<Statement> {
    let shared_type_params = match tokens.peek() {
        Some(token)
            if token.token_type == TokenType::LeftBracket
                || token.token_type == TokenType::LessThan =>
        {
            TypeParamExpr::parse_list(tokens)?
        }
        _ => vec![],
    };

    match tokens.peek() {
        Some(token) => {
            if token.token_type == TokenType::LeftParen {
                let (declarations, _) = parse_args(tokens, TokenType::Satisfy)?;
                return complete_variable_satisfy(
                    keyword,
                    tokens,
                    shared_type_params,
                    declarations,
                );
            }
        }
        None => return Err(tokens.error("unexpected end of file")),
    }

    let first_token = tokens.expect_token()?;
    let first_name_token = match first_token.token_type {
        TokenType::Identifier | TokenType::Numeral => first_token,
        _ => return Err(first_token.error("expected an identifier or numeral")),
    };
    let mut function_expr = Expression::Singleton(first_name_token.clone());

    while let Some(token) = tokens.peek() {
        if token.token_type == TokenType::Dot {
            let dot_token = tokens.next().unwrap();
            let next_token = tokens.expect_token()?;
            if next_token.token_type != TokenType::Identifier {
                return Err(next_token.error("expected an identifier after dot"));
            }
            function_expr = Expression::Binary(
                Box::new(function_expr),
                dot_token,
                Box::new(Expression::Singleton(next_token)),
            );
        } else {
            break;
        }
    }

    let early_type_params = if let Some(token) = tokens.peek() {
        if token.token_type == TokenType::LeftBracket || token.token_type == TokenType::LessThan {
            TypeParamExpr::parse_list(tokens)?
        } else {
            vec![]
        }
    } else {
        vec![]
    };

    if let Some(token) = tokens.peek() {
        if token.token_type == TokenType::LeftParen {
            match tokens.peek_line(TokenType::Equals, TokenType::RightArrow) {
                Some(TokenType::Equals) => {
                    if !early_type_params.is_empty() {
                        return Err(first_name_token
                            .error("destructuring statements don't support type parameters"));
                    }
                    tokens.next();

                    let mut args = vec![];
                    loop {
                        let token = tokens.expect_token()?;
                        match token.token_type {
                            TokenType::RightParen => break,
                            TokenType::Identifier | TokenType::Numeral => args.push(token),
                            TokenType::Comma => continue,
                            _ => {}
                        }
                    }

                    tokens.expect_type(TokenType::Equals)?;
                    tokens.skip_newlines();

                    let (value, value_end_token) = Expression::parse_value(
                        tokens,
                        Terminator::Or(TokenType::NewLine, TokenType::By),
                    )?;

                    let (body, last_token) = if value_end_token.token_type == TokenType::By {
                        let left_brace = tokens.expect_type(TokenType::LeftBrace)?;
                        let (statements, right_brace) = parse_block(tokens, false)?;
                        (
                            Some(Body {
                                left_brace,
                                statements,
                                right_brace: right_brace.clone(),
                            }),
                            right_brace,
                        )
                    } else {
                        (None, value_end_token)
                    };

                    let ds = DestructuringStatement {
                        function: function_expr,
                        args,
                        value,
                        body,
                    };

                    return Ok(Statement {
                        first_token: keyword,
                        last_token,
                        statement: StatementInfo::Destructuring(ds),
                    });
                }
                Some(TokenType::RightArrow) => {
                    if !matches!(function_expr, Expression::Singleton(_)) {
                        return Err(first_name_token.error("function satisfy statements only support simple function names, not dot expressions"));
                    }
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
                        name_token: first_name_token.clone(),
                        type_params: early_type_params,
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
                _ => {
                    return Err(tokens.error("expected '=' or '->' after argument list"));
                }
            }
        }
    }

    if !matches!(function_expr, Expression::Singleton(_)) {
        return Err(first_name_token.error("unexpected dot expression in let statement"));
    }

    if first_name_token.token_type == TokenType::Identifier {
        if let Some(c) = first_name_token.text().chars().next() {
            if !c.is_ascii_lowercase() {
                return Err(first_name_token.error("invalid variable name"));
            }
        }
    }

    let type_params = if early_type_params.is_empty() {
        TypeParamExpr::parse_list(tokens)?
    } else {
        early_type_params
    };

    let next_token = tokens.expect_token()?;
    let (type_expr, _middle_token) = match next_token.token_type {
        TokenType::Colon => {
            let (type_expr, middle_token) = Expression::parse_type(
                tokens,
                Terminator::Or(TokenType::Equals, TokenType::Satisfy),
            )?;
            if middle_token.token_type == TokenType::Satisfy {
                return complete_variable_satisfy(
                    keyword,
                    tokens,
                    type_params,
                    vec![Declaration::Typed(first_name_token, type_expr)],
                );
            }
            if middle_token.token_type == TokenType::Equals {
                tokens.skip_newlines();
            }
            (Some(type_expr), middle_token)
        }
        TokenType::Equals => {
            tokens.skip_newlines();
            (None, next_token)
        }
        _ => {
            return Err(next_token.error("expected ':' or '='"));
        }
    };

    let (value, last_token) = Expression::parse_value(tokens, Terminator::Is(TokenType::NewLine))?;
    if strict && value.is_axiom() {
        return Err(value
            .first_token()
            .error("axiom keyword is not allowed in strict mode"));
    }
    let ls = LetStatement {
        name_token: first_name_token,
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
    Ok(Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::Define(ds),
    })
}

fn reject_single_character_type_name(name_token: &Token, kind: &str) -> Result<()> {
    if name_token.text().chars().count() == 1 {
        return Err(name_token.error(&format!(
            "single-character {} names are reserved for type variables",
            kind
        )));
    }
    Ok(())
}

/// Parses a type statement where the "type" keyword has already been found.
fn parse_type_statement(keyword: Token, tokens: &mut TokenIter, strict: bool) -> Result<Statement> {
    let name_token = tokens.expect_type_name()?;
    reject_single_character_type_name(&name_token, "type")?;
    let type_params = TypeParamExpr::parse_list(tokens)?;
    tokens.expect_type(TokenType::Colon)?;
    tokens.skip_newlines();
    let (type_expr, _) = Expression::parse_type(tokens, Terminator::Is(TokenType::NewLine))?;
    if strict && type_expr.is_axiom() {
        return Err(type_expr
            .first_token()
            .error("axiom keyword is not allowed in strict mode"));
    }
    let last_token = type_expr.last_token().clone();
    let ts = TypeStatement {
        name_token: name_token.clone(),
        type_params,
        type_expr,
    };
    Ok(Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::Type(ts),
    })
}

/// Parses a forall statement where the "forall" keyword has already been found.
fn parse_forall_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let (quantifiers, left_brace) = parse_args(tokens, TokenType::LeftBrace)?;
    let (statements, right_brace) = parse_block(tokens, false)?;
    let body = Body {
        left_brace,
        statements,
        right_brace: right_brace.clone(),
    };
    let fas = ForAllStatement { quantifiers, body };
    Ok(Statement {
        first_token: keyword,
        last_token: right_brace,
        statement: StatementInfo::ForAll(fas),
    })
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
    let (statements, right_brace) = parse_block(tokens, false)?;
    Ok(Some(Body {
        left_brace,
        statements,
        right_brace,
    }))
}

/// Parses an if statement where the "if" keyword has already been found.
fn parse_if_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let token = tokens.peek().unwrap().clone();
    let (condition, left_brace) =
        Expression::parse_value(tokens, Terminator::Is(TokenType::LeftBrace))?;
    let (statements, right_brace) = parse_block(tokens, false)?;
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
    Ok(Statement {
        first_token: keyword,
        last_token: right_brace,
        statement: StatementInfo::If(is),
    })
}

/// Parses a structure statement where the "structure" keyword has already been found.
fn parse_structure_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let name_token = tokens.expect_type_name()?;
    reject_single_character_type_name(&name_token, "type")?;
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
                if fields.is_empty() {
                    return Err(token.error("structs must have at least one field"));
                }
                let right_brace = tokens.next().unwrap();
                let first_right_brace = right_brace.clone();

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
    reject_single_character_type_name(&type_token, "type")?;
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
                if constructors.is_empty() {
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
/// This syntax is now deprecated in favor of "from foo import bar".
fn parse_import_statement(keyword: Token, _tokens: &mut TokenIter) -> Result<Statement> {
    Err(keyword.error(
        "\"import foo\" syntax is deprecated. try \"from foo import bar\" format for imports",
    ))
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
                tokens.skip_newlines();
                continue;
            }
            _ => {
                return Err(token.error("expected comma or newline"));
            }
        }
    };
    let is = ImportStatement { components, names };
    Ok(Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::Import(is),
    })
}

/// Parses an attributes statement where the "class" or "attributes" keyword has already been found.
fn parse_attributes_statement(keyword: Token, tokens: &mut TokenIter) -> Result<Statement> {
    let first_name = tokens.expect_type_name()?;

    let (instance_name, _name, name_token) = match tokens.peek_type() {
        Some(TokenType::Colon) => {
            tokens.next();
            let typeclass_name = tokens.expect_type_name()?;
            (
                Some(first_name.clone()),
                typeclass_name.text().to_string(),
                typeclass_name,
            )
        }
        _ => (None, first_name.text().to_string(), first_name),
    };

    let type_params = TypeParamExpr::parse_list(tokens)?;
    let left_brace = tokens.expect_type(TokenType::LeftBrace)?;
    let (statements, right_brace) = parse_block(tokens, false)?;
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
    Ok(Statement {
        first_token: keyword,
        last_token: right_brace,
        statement: StatementInfo::Attributes(ats),
    })
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
        let (statements, right_brace) = parse_block(tokens, false)?;
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

    let (instance_name, typeclass_name) = match tokens.peek_type() {
        Some(TokenType::Colon) => {
            tokens.next();
            let typeclass_name = tokens.expect_type_name()?;
            (Some(first_name), typeclass_name)
        }
        Some(TokenType::Extends) | Some(TokenType::NewLine) | Some(TokenType::LeftBrace) | None => {
            (None, first_name)
        }
        _ => {
            return Err(keyword
                .error("expected ':' for block syntax or 'extends'/'{'  for no-block syntax"));
        }
    };
    reject_single_character_type_name(&typeclass_name, "typeclass")?;

    let mut extends = vec![];
    let has_block = match tokens.peek_type() {
        Some(TokenType::LeftBrace) => {
            tokens.next();
            true
        }
        Some(TokenType::Extends) => {
            tokens.next();
            loop {
                let type_token = tokens.expect_type_name()?;
                let type_expr = Expression::Singleton(type_token);
                extends.push(type_expr);

                match tokens.peek_type() {
                    Some(TokenType::Comma) => {
                        tokens.next();
                        match tokens.peek_type() {
                            Some(TokenType::NewLine) | None => {
                                break false;
                            }
                            _ => {
                                continue;
                            }
                        }
                    }
                    Some(TokenType::LeftBrace) => {
                        tokens.next();
                        break true;
                    }
                    Some(TokenType::NewLine) | None => {
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
        Some(TokenType::NewLine) | None => false,
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
        if extends.is_empty() {
            return Err(keyword.error("Typeclass without block must extend at least one typeclass"));
        }

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
    let type_params = TypeParamExpr::parse_list(tokens)?;
    tokens.expect_type(TokenType::Colon)?;

    let (typeclass, terminator) = Expression::parse_type(
        tokens,
        Terminator::Or(TokenType::LeftBrace, TokenType::NewLine),
    )?;

    let (definitions, body, last_token) = match terminator.token_type {
        TokenType::LeftBrace => {
            let (statements, right_brace) = parse_block(tokens, false)?;
            let definitions = Body {
                left_brace: terminator,
                statements,
                right_brace: right_brace.clone(),
            };
            let (body, last_token) = parse_by_block(right_brace, tokens)?;
            (Some(definitions), body, last_token)
        }
        TokenType::NewLine => (None, None, typeclass.last_token().clone()),
        _ => {
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
        type_params,
        typeclass,
        definitions,
        body,
    };
    Ok(Statement {
        first_token: keyword,
        last_token,
        statement: StatementInfo::Instance(is),
    })
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
        strict: bool,
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
                        let s = parse_let_statement(keyword, tokens, strict)?;
                        return Ok((Some(s), None));
                    }
                    TokenType::Axiom => {
                        let keyword = tokens.next().unwrap();
                        if strict {
                            return Err(
                                keyword.error("axiom keyword is not allowed in strict mode")
                            );
                        }
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
                        let s = parse_type_statement(keyword, tokens, strict)?;
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
                        return Err(Error::new(
                            &keyword,
                            &keyword,
                            "the 'solve' keyword is no longer supported",
                        ));
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
        match Statement::parse(&mut tokens, in_block, false)? {
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

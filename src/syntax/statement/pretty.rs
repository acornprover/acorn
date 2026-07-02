use super::ast::*;
use super::*;
use ::pretty::Arena;

impl fmt::Display for TypeclassCondition {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let allocator = Arena::<()>::new();
        let doc = self.pretty_ref(&allocator, false);
        doc.render_fmt(PRINT_WIDTH, f)?;
        Ok(())
    }
}

impl<'a, D, A> Pretty<'a, D, A> for &'a TypeclassCondition
where
    A: 'a,
    D: DocAllocator<'a, A>,
{
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, A> {
        self.pretty_ref(allocator, false)
    }
}

impl TypeclassCondition {
    fn pretty_ref<'a, D, A>(&'a self, allocator: &'a D, _flat: bool) -> DocBuilder<'a, D, A>
    where
        A: 'a,
        D: DocAllocator<'a, A>,
    {
        let mut doc = allocator.text(self.name_token.text());
        doc = write_theorem_pretty(allocator, doc, &[], &self.args, &self.claim);
        doc
    }
}

impl TheoremStatement {
    pub fn statement_string(&self) -> String {
        let allocator = Arena::<()>::new();
        let mut doc = if self.lemma {
            allocator.text("lemma")
        } else if self.axiomatic {
            allocator.text("axiom")
        } else {
            allocator.text("theorem")
        };
        if let Some(name_token) = &self.name_token {
            doc = doc
                .append(allocator.text(" "))
                .append(allocator.text(name_token.text()));
        }
        doc = write_theorem_pretty(&allocator, doc, &self.type_params, &self.args, &self.claim);

        let mut output = String::new();
        doc.render_fmt(PRINT_WIDTH, &mut output)
            .expect("writing theorem statement string should succeed");
        output
    }
}

impl FunctionSatisfyStatement {
    pub fn statement_string(&self) -> String {
        let allocator = Arena::<()>::new();
        let doc = write_function_satisfy_pretty(&allocator, self, false);

        let mut output = String::new();
        doc.render_fmt(PRINT_WIDTH, &mut output)
            .expect("writing function satisfy statement string should succeed");
        output
    }
}

impl StructureStatement {
    pub fn statement_string(&self) -> String {
        let allocator = Arena::<()>::new();
        let doc = write_structure_pretty(&allocator, self, false);

        let mut output = String::new();
        doc.render_fmt(PRINT_WIDTH, &mut output)
            .expect("writing structure statement string should succeed");
        output
    }
}

impl DestructuringStatement {
    pub fn statement_string(&self) -> String {
        let allocator = Arena::<()>::new();
        let doc = write_destructuring_pretty(&allocator, self, false);

        let mut output = String::new();
        doc.render_fmt(PRINT_WIDTH, &mut output)
            .expect("writing destructuring statement string should succeed");
        output
    }
}

impl InstanceStatement {
    fn package_signature_name(&self) -> String {
        let type_params = if self.type_params.is_empty() {
            String::new()
        } else {
            format!(
                "[{}]",
                self.type_params
                    .iter()
                    .map(|param| param.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        format!(
            "{}{}: {}",
            self.type_name.text(),
            type_params,
            self.typeclass
        )
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let allocator = Arena::<()>::new();
        let doc = self.pretty_ref(&allocator, allocator.nil());
        doc.render_fmt(PRINT_WIDTH, f)?;
        Ok(())
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
    fn package_signature_names(&self) -> Vec<String> {
        match &self.statement {
            StatementInfo::Let(statement) => vec![statement.name_token.text().to_string()],
            StatementInfo::Define(statement) => vec![statement.name_token.text().to_string()],
            StatementInfo::Theorem(statement) => {
                if statement.lemma {
                    vec![]
                } else {
                    statement
                        .name_token
                        .as_ref()
                        .map(|token| vec![token.text().to_string()])
                        .unwrap_or_default()
                }
            }
            StatementInfo::Type(statement) => vec![statement.name_token.text().to_string()],
            StatementInfo::VariableSatisfy(statement) => statement
                .declarations
                .iter()
                .map(|declaration| declaration.token().text().to_string())
                .collect(),
            StatementInfo::FunctionSatisfy(statement) => {
                vec![statement.name_token.text().to_string()]
            }
            StatementInfo::Structure(statement) => vec![statement.name_token.text().to_string()],
            StatementInfo::Inductive(statement) => vec![statement.name_token.text().to_string()],
            StatementInfo::Typeclass(statement) => {
                vec![statement.typeclass_name.text().to_string()]
            }
            StatementInfo::Instance(statement) => vec![statement.package_signature_name()],
            StatementInfo::Destructuring(statement) => statement
                .args
                .iter()
                .map(|token| token.text().to_string())
                .collect(),
            StatementInfo::Attributes(_)
            | StatementInfo::Claim(_)
            | StatementInfo::ForAll(_)
            | StatementInfo::If(_)
            | StatementInfo::Import(_)
            | StatementInfo::Numerals(_)
            | StatementInfo::Match(_)
            | StatementInfo::DocComment(_) => vec![],
        }
    }

    fn package_signature_text(&self) -> String {
        match &self.statement {
            StatementInfo::Theorem(statement) => statement.statement_string(),
            StatementInfo::FunctionSatisfy(statement) => statement.statement_string(),
            StatementInfo::Structure(statement) => statement.statement_string(),
            StatementInfo::Destructuring(statement) => statement.statement_string(),
            _ => self.to_string(),
        }
    }

    pub fn package_signatures(&self) -> Vec<(String, String)> {
        if let StatementInfo::Attributes(statement) = &self.statement {
            let mut signatures = Vec::new();
            for member in &statement.body.statements {
                let member_text = attribute_member_signature(statement, member);
                for member_name in member.package_signature_names() {
                    let key = format!("{}.{}", statement.name_token.text(), member_name);
                    signatures.push((key, member_text.clone()));
                }
            }
            return signatures;
        }

        let text = self.package_signature_text();
        self.package_signature_names()
            .into_iter()
            .map(|name| (name, text.clone()))
            .collect()
    }

    pub fn package_signature(&self) -> Option<(String, String)> {
        self.package_signatures().into_iter().next()
    }

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
            StatementInfo::Let(let_statement) => {
                let mut doc = allocator
                    .text("let ")
                    .append(allocator.text(let_statement.name_token.text()));
                doc = write_type_params_pretty(allocator, doc, &let_statement.type_params);
                match &let_statement.type_expr {
                    Some(type_expr) => doc
                        .append(allocator.text(": "))
                        .append(type_expr.pretty_ref(allocator, false))
                        .append(allocator.text(" = "))
                        .append(let_statement.value.pretty_ref(allocator, false)),
                    None => doc
                        .append(allocator.text(" = "))
                        .append(let_statement.value.pretty_ref(allocator, false)),
                }
            }

            StatementInfo::Define(define_statement) => {
                let mut doc = allocator
                    .text("define ")
                    .append(allocator.text(define_statement.name_token.text()));
                doc = write_type_params_pretty(allocator, doc, &define_statement.type_params);
                doc = write_args_pretty(allocator, doc, &define_statement.args);
                doc.append(allocator.text(" -> "))
                    .append(define_statement.return_type.pretty_ref(allocator, false))
                    .append(allocator.text(" {"))
                    .append(
                        allocator
                            .hardline()
                            .append(define_statement.return_value.pretty_ref(allocator, false))
                            .nest(4),
                    )
                    .append(allocator.hardline())
                    .append(allocator.text("}"))
            }

            StatementInfo::Theorem(theorem_statement) => {
                let mut doc = if theorem_statement.lemma {
                    allocator.text("lemma")
                } else if theorem_statement.axiomatic {
                    allocator.text("axiom")
                } else {
                    allocator.text("theorem")
                };
                if let Some(name_token) = &theorem_statement.name_token {
                    doc = doc
                        .append(allocator.text(" "))
                        .append(allocator.text(name_token.text()));
                }
                doc = write_theorem_pretty(
                    allocator,
                    doc,
                    &theorem_statement.type_params,
                    &theorem_statement.args,
                    &theorem_statement.claim,
                );
                if let Some(body) = &theorem_statement.body {
                    doc = doc.append(allocator.text(" by"));
                    doc = write_block_pretty(allocator, doc, &body.statements);
                }
                doc
            }

            StatementInfo::Claim(ps) => ps.claim.pretty_ref(allocator, false),

            StatementInfo::Type(type_statement) => write_type_params_pretty(
                allocator,
                allocator
                    .text("type ")
                    .append(allocator.text(type_statement.name_token.text())),
                &type_statement.type_params,
            )
            .append(allocator.text(": "))
            .append(type_statement.type_expr.pretty_ref(allocator, false)),

            StatementInfo::ForAll(forall_statement) => {
                let mut doc = allocator.text("forall");
                doc = write_args_pretty(allocator, doc, &forall_statement.quantifiers);
                write_block_pretty(allocator, doc, &forall_statement.body.statements).group()
            }

            StatementInfo::If(if_statement) => {
                let mut doc = allocator
                    .text("if ")
                    .append(if_statement.condition.pretty_ref(allocator, false));
                doc = write_block_pretty(allocator, doc, &if_statement.body.statements);
                if let Some(else_body) = &if_statement.else_body {
                    doc = doc.append(allocator.text(" else"));
                    doc = write_block_pretty(allocator, doc, &else_body.statements);
                }
                doc.group()
            }

            StatementInfo::VariableSatisfy(variable_satisfy_statement) => {
                let mut doc = allocator.text("let ");
                if variable_satisfy_statement.declarations.len() == 1 {
                    if let Declaration::Typed(name_token, type_expr) =
                        &variable_satisfy_statement.declarations[0]
                    {
                        doc = doc.append(allocator.text(name_token.text()));
                        doc = write_type_params_pretty(
                            allocator,
                            doc,
                            &variable_satisfy_statement.type_params,
                        );
                        doc = doc
                            .append(allocator.text(": "))
                            .append(type_expr.pretty_ref(allocator, false));
                    } else {
                        doc = doc.append(
                            variable_satisfy_statement.declarations[0].pretty_ref(allocator, false),
                        );
                    }
                } else {
                    doc =
                        write_args_pretty(allocator, doc, &variable_satisfy_statement.declarations);
                }
                doc.append(allocator.text(" satisfy {"))
                    .append(
                        allocator
                            .hardline()
                            .append(
                                variable_satisfy_statement
                                    .condition
                                    .pretty_ref(allocator, false),
                            )
                            .nest(4),
                    )
                    .append(allocator.hardline())
                    .append(allocator.text("}"))
            }

            StatementInfo::FunctionSatisfy(function_satisfy_statement) => {
                write_function_satisfy_pretty(allocator, function_satisfy_statement, true).group()
            }

            StatementInfo::Structure(structure_statement) => {
                write_structure_pretty(allocator, structure_statement, true).group()
            }

            StatementInfo::Inductive(inductive_statement) => {
                let mut doc = allocator
                    .text("inductive ")
                    .append(allocator.text(inductive_statement.name_token.text()));
                doc = write_type_params_pretty(allocator, doc, &inductive_statement.type_params);
                doc = doc.append(allocator.text(" {"));
                let mut inner = allocator.nil();
                for (name, type_expr, _doc_comments) in &inductive_statement.constructors {
                    inner = inner
                        .append(allocator.hardline())
                        .append(allocator.text(name.text()));
                    if let Some(te) = type_expr {
                        inner = inner.append(te.pretty_ref(allocator, false));
                    }
                }
                doc.append(inner.nest(4))
                    .append(allocator.hardline())
                    .append(allocator.text("}"))
            }

            StatementInfo::Import(import_statement) => {
                if import_statement.names.is_empty() {
                    let module_path = import_statement
                        .components
                        .iter()
                        .map(|t| t.text())
                        .collect::<Vec<_>>()
                        .join(".");
                    allocator
                        .text("import ")
                        .append(allocator.text(module_path))
                } else {
                    let module_path = import_statement
                        .components
                        .iter()
                        .map(|t| t.text())
                        .collect::<Vec<_>>()
                        .join(".");
                    let names = import_statement
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

            StatementInfo::Attributes(attributes_statement) => {
                let doc = write_attributes_header_pretty(allocator, attributes_statement);
                write_block_pretty(allocator, doc, &attributes_statement.body.statements).group()
            }

            StatementInfo::Numerals(numerals_statement) => allocator
                .text("default ")
                .append(numerals_statement.type_expr.pretty_ref(allocator, false)),

            StatementInfo::Match(match_statement) => {
                let doc = allocator
                    .text("match ")
                    .append(match_statement.scrutinee.pretty_ref(allocator, false))
                    .append(allocator.text(" {"));
                let mut inner = allocator.nil();
                for (pattern, body) in &match_statement.cases {
                    inner = inner
                        .append(allocator.hardline())
                        .append(pattern.pretty_ref(allocator, false));
                    inner = write_block_pretty(allocator, inner, &body.statements);
                }
                doc.append(inner.nest(4))
                    .append(allocator.hardline())
                    .append(allocator.text("}"))
            }

            StatementInfo::Typeclass(typeclass_statement) => {
                let mut doc = allocator.text("typeclass ");
                if let Some(instance_name) = &typeclass_statement.instance_name {
                    doc = doc
                        .append(allocator.text(instance_name.text()))
                        .append(allocator.text(": "))
                        .append(allocator.text(typeclass_statement.typeclass_name.text()));
                } else {
                    doc = doc.append(allocator.text(typeclass_statement.typeclass_name.text()));
                }
                if !typeclass_statement.extends.is_empty() {
                    doc = doc.append(allocator.text(" extends "));
                    for (i, typeclass) in typeclass_statement.extends.iter().enumerate() {
                        if i > 0 {
                            doc = doc.append(allocator.text(", "));
                        }
                        doc = doc.append(typeclass.pretty_ref(allocator, false));
                    }
                }
                if !typeclass_statement.constants.is_empty()
                    || !typeclass_statement.conditions.is_empty()
                {
                    doc = doc.append(allocator.text(" {"));
                    let mut inner = allocator.nil();
                    for (name, type_expr, _doc_comments) in &typeclass_statement.constants {
                        inner = inner
                            .append(allocator.hardline())
                            .append(allocator.text(name.text()))
                            .append(allocator.text(": "))
                            .append(type_expr.pretty_ref(allocator, false));
                    }
                    for theorem in &typeclass_statement.conditions {
                        inner = inner
                            .append(allocator.hardline())
                            .append(theorem.pretty_ref(allocator, false));
                    }
                    doc = doc
                        .append(inner.nest(4))
                        .append(allocator.hardline())
                        .append(allocator.text("}"));
                }
                doc
            }

            StatementInfo::Instance(instance_statement) => {
                let mut doc = allocator
                    .text("instance ")
                    .append(allocator.text(instance_statement.type_name.text()));
                doc = write_type_params_pretty(allocator, doc, &instance_statement.type_params)
                    .append(allocator.text(": "))
                    .append(instance_statement.typeclass.pretty_ref(allocator, false));
                if let Some(definitions) = &instance_statement.definitions {
                    doc = write_block_pretty(allocator, doc, &definitions.statements);
                }
                doc.group()
            }

            StatementInfo::Destructuring(destructuring_statement) => {
                write_destructuring_pretty(allocator, destructuring_statement, true)
            }

            StatementInfo::DocComment(s) => allocator.text("/// ").append(allocator.text(s)),
        };

        indent.append(doc)
    }
}

fn write_attributes_header_pretty<'a, D, A>(
    allocator: &'a D,
    attributes: &'a AttributesStatement,
) -> DocBuilder<'a, D, A>
where
    A: 'a,
    D: DocAllocator<'a, A>,
{
    let mut doc = allocator.text("attributes ");
    if let Some(instance_name) = &attributes.instance_name {
        doc = doc
            .append(allocator.text(instance_name.text()))
            .append(allocator.text(": "))
            .append(allocator.text(attributes.name_token.text()));
    } else {
        doc = doc.append(allocator.text(attributes.name_token.text()));
    }
    write_type_params_pretty(allocator, doc, &attributes.type_params)
}

fn attribute_member_signature(attributes: &AttributesStatement, member: &Statement) -> String {
    let allocator = Arena::<()>::new();
    let member_doc = match &member.statement {
        StatementInfo::FunctionSatisfy(function_satisfy_statement) => {
            write_function_satisfy_pretty(&allocator, function_satisfy_statement, false)
        }
        _ => member.pretty_ref(&allocator, allocator.nil()),
    };
    let doc = write_attributes_header_pretty(&allocator, attributes)
        .append(allocator.text(" {"))
        .append(allocator.hardline().append(member_doc).nest(4))
        .append(allocator.hardline())
        .append(allocator.text("}"))
        .group();
    let mut output = String::new();
    doc.render_fmt(PRINT_WIDTH, &mut output)
        .expect("writing attribute member signature should succeed");
    output
}

fn write_destructuring_pretty<'a, D, A>(
    allocator: &'a D,
    destructuring_statement: &'a DestructuringStatement,
    include_body: bool,
) -> DocBuilder<'a, D, A>
where
    A: 'a,
    D: DocAllocator<'a, A>,
{
    let mut doc = allocator
        .text("let ")
        .append(
            destructuring_statement
                .function
                .pretty_ref(allocator, false),
        )
        .append(allocator.text("("));
    for (i, arg) in destructuring_statement.args.iter().enumerate() {
        if i > 0 {
            doc = doc.append(allocator.text(", "));
        }
        doc = doc.append(allocator.text(arg.text()));
    }
    doc = doc
        .append(allocator.text(") = "))
        .append(destructuring_statement.value.pretty_ref(allocator, false));

    if include_body {
        if let Some(body) = &destructuring_statement.body {
            doc = doc.append(allocator.text(" by"));
            doc = write_block_pretty(allocator, doc, &body.statements);
        }
    }
    doc
}

fn write_structure_pretty<'a, D, A>(
    allocator: &'a D,
    structure_statement: &'a StructureStatement,
    include_body: bool,
) -> DocBuilder<'a, D, A>
where
    A: 'a,
    D: DocAllocator<'a, A>,
{
    let mut doc = allocator
        .text("structure ")
        .append(allocator.text(structure_statement.name_token.text()));
    doc = write_type_params_pretty(allocator, doc, &structure_statement.type_params);
    doc = doc.append(allocator.text(" {"));
    let mut fields_inner = allocator.nil();
    for (name, type_expr, _doc_comments) in &structure_statement.fields {
        fields_inner = fields_inner
            .append(allocator.hardline())
            .append(allocator.text(name.text()))
            .append(allocator.text(": "))
            .append(type_expr.pretty_ref(allocator, false));
    }
    doc = doc
        .append(fields_inner.nest(4))
        .append(allocator.hardline())
        .append(allocator.text("}"));
    if let Some(constraint) = &structure_statement.constraint {
        doc = doc
            .append(allocator.text(" constraint {"))
            .append(
                allocator
                    .hardline()
                    .append(constraint.pretty_ref(allocator, false))
                    .nest(4),
            )
            .append(allocator.hardline())
            .append(allocator.text("}"));
    }
    if include_body {
        if let Some(body) = &structure_statement.body {
            doc = doc.append(allocator.text(" by"));
            doc = write_block_pretty(allocator, doc, &body.statements);
        }
    }
    doc
}

fn write_function_satisfy_pretty<'a, D, A>(
    allocator: &'a D,
    function_satisfy_statement: &'a FunctionSatisfyStatement,
    include_body: bool,
) -> DocBuilder<'a, D, A>
where
    A: 'a,
    D: DocAllocator<'a, A>,
{
    let mut doc = allocator
        .text("let ")
        .append(allocator.text(function_satisfy_statement.name_token.text()));
    doc = write_type_params_pretty(allocator, doc, &function_satisfy_statement.type_params);
    let return_declaration_index = function_satisfy_statement.declarations.len() - 1;
    doc = write_args_pretty(
        allocator,
        doc,
        &function_satisfy_statement.declarations[..return_declaration_index],
    );
    doc = doc
        .append(allocator.text(" -> "))
        .append(
            function_satisfy_statement.declarations[return_declaration_index]
                .pretty_ref(allocator, false),
        )
        .append(allocator.text(" satisfy {"))
        .append(
            allocator
                .hardline()
                .nest(4)
                .append(
                    function_satisfy_statement
                        .condition
                        .pretty_ref(allocator, false),
                )
                .nest(4),
        )
        .append(allocator.hardline())
        .append(allocator.text("}"));
    if include_body {
        if let Some(body) = &function_satisfy_statement.body {
            doc = doc.append(allocator.text(" by"));
            doc = write_block_pretty(allocator, doc, &body.statements);
        }
    }
    doc
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
        result = result.append(param.pretty_ref(allocator, false));
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
        result = result.append(arg.pretty_ref(allocator, false));
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
                .append(claim.pretty_ref(allocator, false))
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
    fn pretty_ref<'a, D, A>(&'a self, allocator: &'a D, flat: bool) -> DocBuilder<'a, D, A>
    where
        A: 'a,
        D: DocAllocator<'a, A>,
    {
        match &self.typeclass {
            None => allocator.text(self.name.text()),
            Some(typeclass) => allocator
                .text(self.name.text())
                .append(allocator.text(": "))
                .append(typeclass.pretty_ref(allocator, flat)),
        }
    }
}

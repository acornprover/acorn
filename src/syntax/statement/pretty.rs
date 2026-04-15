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
        let mut doc = if self.axiomatic {
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
                        .append(type_expr.pretty_ref(allocator, false))
                        .append(allocator.text(" = "))
                        .append(ls.value.pretty_ref(allocator, false)),
                    None => doc
                        .append(allocator.text(" = "))
                        .append(ls.value.pretty_ref(allocator, false)),
                }
            }

            StatementInfo::Define(ds) => {
                let mut doc = allocator
                    .text("define ")
                    .append(allocator.text(ds.name_token.text()));
                doc = write_type_params_pretty(allocator, doc, &ds.type_params);
                doc = write_args_pretty(allocator, doc, &ds.args);
                doc.append(allocator.text(" -> "))
                    .append(ds.return_type.pretty_ref(allocator, false))
                    .append(allocator.text(" {"))
                    .append(
                        allocator
                            .hardline()
                            .append(ds.return_value.pretty_ref(allocator, false))
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

            StatementInfo::Claim(ps) => ps.claim.pretty_ref(allocator, false),

            StatementInfo::Type(ts) => allocator
                .text("type ")
                .append(allocator.text(ts.name_token.text()))
                .append(allocator.text(": "))
                .append(ts.type_expr.pretty_ref(allocator, false)),

            StatementInfo::ForAll(fas) => {
                let mut doc = allocator.text("forall");
                doc = write_args_pretty(allocator, doc, &fas.quantifiers);
                write_block_pretty(allocator, doc, &fas.body.statements).group()
            }

            StatementInfo::If(is) => {
                let mut doc = allocator
                    .text("if ")
                    .append(is.condition.pretty_ref(allocator, false));
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
                    if let Declaration::Typed(name_token, type_expr) = &vss.declarations[0] {
                        doc = doc.append(allocator.text(name_token.text()));
                        doc = write_type_params_pretty(allocator, doc, &vss.type_params);
                        doc = doc
                            .append(allocator.text(": "))
                            .append(type_expr.pretty_ref(allocator, false));
                    } else {
                        doc = doc.append(vss.declarations[0].pretty_ref(allocator, false));
                    }
                } else {
                    doc = write_args_pretty(allocator, doc, &vss.declarations);
                }
                doc.append(allocator.text(" satisfy {"))
                    .append(
                        allocator
                            .hardline()
                            .append(vss.condition.pretty_ref(allocator, false))
                            .nest(4),
                    )
                    .append(allocator.hardline())
                    .append(allocator.text("}"))
            }

            StatementInfo::FunctionSatisfy(fss) => {
                let mut doc = allocator
                    .text("let ")
                    .append(allocator.text(fss.name_token.text()));
                doc = write_type_params_pretty(allocator, doc, &fss.type_params);
                let i = fss.declarations.len() - 1;
                doc = write_args_pretty(allocator, doc, &fss.declarations[..i]);
                doc = doc
                    .append(allocator.text(" -> "))
                    .append(fss.declarations[i].pretty_ref(allocator, false))
                    .append(allocator.text(" satisfy {"))
                    .append(
                        allocator
                            .hardline()
                            .nest(4)
                            .append(fss.condition.pretty_ref(allocator, false))
                            .nest(4),
                    )
                    .append(allocator.hardline())
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
                        .append(type_expr.pretty_ref(allocator, false));
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
                                .append(constraint.pretty_ref(allocator, false))
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
                        inner = inner.append(te.pretty_ref(allocator, false));
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
                .append(ds.type_expr.pretty_ref(allocator, false)),

            StatementInfo::Match(ms) => {
                let doc = allocator
                    .text("match ")
                    .append(ms.scrutinee.pretty_ref(allocator, false))
                    .append(allocator.text(" {"));
                let mut inner = allocator.nil();
                for (pattern, body) in &ms.cases {
                    inner = inner
                        .append(allocator.hardline())
                        .append(pattern.pretty_ref(allocator, false));
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
                        doc = doc.append(typeclass.pretty_ref(allocator, false));
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
                            .append(type_expr.pretty_ref(allocator, false));
                    }
                    for theorem in &ts.conditions {
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

            StatementInfo::Instance(is) => {
                let mut doc = allocator
                    .text("instance ")
                    .append(allocator.text(is.type_name.text()))
                    .append(allocator.text(": "))
                    .append(is.typeclass.pretty_ref(allocator, false));
                if let Some(definitions) = &is.definitions {
                    doc = write_block_pretty(allocator, doc, &definitions.statements);
                }
                doc.group()
            }

            StatementInfo::Destructuring(ds) => {
                let mut doc = allocator
                    .text("let ")
                    .append(ds.function.pretty_ref(allocator, false))
                    .append(allocator.text("("));
                for (i, arg) in ds.args.iter().enumerate() {
                    if i > 0 {
                        doc = doc.append(allocator.text(", "));
                    }
                    doc = doc.append(allocator.text(arg.text()));
                }
                doc = doc
                    .append(allocator.text(") = "))
                    .append(ds.value.pretty_ref(allocator, false));

                if let Some(body) = &ds.body {
                    doc = doc.append(allocator.text(" by"));
                    doc = write_block_pretty(allocator, doc, &body.statements);
                }
                doc
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

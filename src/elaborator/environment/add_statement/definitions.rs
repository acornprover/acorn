use super::*;
use crate::syntax::expression::TypeParamExpr;

#[derive(Default)]
struct LocalFamilyParams {
    type_param_exprs: Vec<TypeParamExpr>,
    type_params: Vec<TypeParam>,
    value_params: Vec<ValueParam>,
    value_declarations: Vec<Declaration>,
}

fn bind_datatype_value_params(stack: &mut Stack, datatype_params: Option<&DatatypeFamilyScope>) {
    if let Some(datatype_params) = datatype_params {
        datatype_params.bind_value_stack(stack);
    }
}

fn datatype_value_param_types(datatype_params: Option<&DatatypeFamilyScope>) -> Vec<AcornType> {
    datatype_params
        .map(|datatype_params| datatype_params.value_param_types())
        .unwrap_or_default()
}

fn datatype_value_block_args(
    datatype_params: Option<&DatatypeFamilyScope>,
) -> Vec<(String, AcornType)> {
    datatype_params
        .map(|datatype_params| datatype_params.value_block_args())
        .unwrap_or_default()
}

fn quantify_over_datatype_value_params(
    datatype_params: Option<&DatatypeFamilyScope>,
    value: AcornValue,
) -> AcornValue {
    let value_param_types = datatype_value_param_types(datatype_params);
    if value_param_types.is_empty() {
        value
    } else {
        AcornValue::ForAll(value_param_types, Box::new(value))
    }
}

fn bind_explicit_value_params(stack: &mut Stack, value_params: &[ValueParam]) {
    for value_param in value_params {
        stack.insert(value_param.name.clone(), value_param.value_type.clone());
    }
}

fn explicit_value_param_types(value_params: &[ValueParam]) -> Vec<AcornType> {
    value_params
        .iter()
        .map(|param| param.value_type.clone())
        .collect()
}

fn explicit_value_block_args(value_params: &[ValueParam]) -> Vec<(String, AcornType)> {
    value_params
        .iter()
        .map(|param| (param.name.clone(), param.value_type.clone()))
        .collect()
}

fn quantify_over_explicit_value_params(
    value_params: &[ValueParam],
    value: AcornValue,
) -> AcornValue {
    let value_param_types = explicit_value_param_types(value_params);
    if value_param_types.is_empty() {
        value
    } else {
        AcornValue::ForAll(value_param_types, Box::new(value))
    }
}

impl Environment {
    fn evaluate_local_family_params(
        &mut self,
        project: &Project,
        exprs: &[TypeParamExpr],
    ) -> error::Result<LocalFamilyParams> {
        let family_params =
            Evaluator::new(project, &self.bindings, None).evaluate_family_params(exprs)?;
        let mut local_family_params = LocalFamilyParams::default();
        for (expr, family_param) in exprs.iter().cloned().zip(family_params) {
            match family_param {
                crate::elaborator::acorn_type::FamilyParam::Type(type_param) => {
                    self.bindings
                        .check_typename_available(&type_param.name, &expr.name)?;
                    local_family_params.type_param_exprs.push(expr);
                    local_family_params.type_params.push(type_param);
                }
                crate::elaborator::acorn_type::FamilyParam::Value(value_param) => {
                    let annotation = expr.typeclass.clone().expect(
                        "value family parameters should always carry their type annotation",
                    );
                    local_family_params
                        .value_declarations
                        .push(Declaration::Typed(expr.name.clone(), annotation));
                    local_family_params.value_params.push(value_param);
                }
            }
        }
        Ok(local_family_params)
    }

    /// Adds a "let" statement to the environment.
    /// This can also be in a class, typeclass, or instance block.
    /// If this is in an attributes block, the datatype family parameters are provided.
    pub(super) fn add_let_statement(
        &mut self,
        project: &Project,
        statement: &Statement,
        defined_name: DefinedName,
        ls: &LetStatement,
        range: Range,
        datatype_params: Option<&DatatypeFamilyScope>,
    ) -> error::Result<()> {
        ls.name_token.check_not_reserved()?;

        if self.bindings.constant_name_in_use(&defined_name) {
            return Err(ls.name_token.error(&format!(
                "constant name '{}' already defined in this scope",
                &defined_name
            )));
        }

        if self.depth > 0 && !ls.type_params.is_empty() {
            return Err(ls
                .name_token
                .error("parameterized constants may only be defined at the top level"));
        }

        let local_family_params = if datatype_params.is_some() {
            LocalFamilyParams {
                type_param_exprs: ls.type_params.clone(),
                type_params: self
                    .evaluator(project)
                    .evaluate_type_params(&ls.type_params)?,
                value_params: vec![],
                value_declarations: vec![],
            }
        } else {
            self.evaluate_local_family_params(project, &ls.type_params)?
        };
        let local_type_params = local_family_params.type_params.clone();
        for param in &local_type_params {
            self.bindings.add_arbitrary_type(param.clone());
        }

        let datatype_value_param_types = datatype_value_param_types(datatype_params);
        let explicit_value_param_types =
            explicit_value_param_types(&local_family_params.value_params);
        let (acorn_type, value) = match &ls.type_expr {
            Some(type_expr) => {
                let mut stack = Stack::new();
                bind_explicit_value_params(&mut stack, &local_family_params.value_params);
                bind_datatype_value_params(&mut stack, datatype_params);
                let acorn_type = self
                    .evaluator(project)
                    .evaluate_type_with_stack(&mut stack, type_expr)?;
                if ls.name_token.token_type == TokenType::Numeral {
                    match &defined_name {
                        DefinedName::Constant(constant_name) => {
                            let (datatype_module_id, datatype_name) =
                                match constant_name.as_attribute() {
                                    Some((datatype_module_id, datatype_name, _)) => {
                                        (datatype_module_id, datatype_name.to_string())
                                    }
                                    _ => {
                                        return Err(ls
                                            .name_token
                                            .error("numeric literals must be datatype members"))
                                    }
                                };
                            let datatype = Datatype {
                                module_id: datatype_module_id,
                                name: datatype_name,
                            };
                            acorn_type
                                .check_instance(&datatype, type_expr)
                                .map_err(|_| {
                                    type_expr.error(
                                        "numeric datatype variables must be the datatype type",
                                    )
                                })?;
                        }
                        DefinedName::Instance(instance_name) => {
                            acorn_type
                                .check_instance(&instance_name.datatype, type_expr)
                                .map_err(|_| {
                                    type_expr.error(
                                        "numeric instance variables must be the instance datatype type",
                                    )
                                })?;
                        }
                    }
                }
                let value = if ls.value.is_axiom() {
                    None
                } else {
                    let mut stack = Stack::new();
                    bind_explicit_value_params(&mut stack, &local_family_params.value_params);
                    bind_datatype_value_params(&mut stack, datatype_params);
                    let v = if let Some(instance_name) = defined_name.as_instance() {
                        Evaluator::new_for_instance_member(
                            project,
                            &self.bindings,
                            Some(&mut self.token_map),
                            instance_name,
                        )
                        .evaluate_value_with_stack(
                            &mut stack,
                            &ls.value,
                            Some(&acorn_type),
                        )?
                    } else {
                        self.evaluator(project).evaluate_value_with_stack(
                            &mut stack,
                            &ls.value,
                            Some(&acorn_type),
                        )?
                    };
                    Some(v)
                };
                (acorn_type, value)
            }
            None => {
                if ls.value.is_axiom() {
                    return Err(ls
                        .value
                        .first_token()
                        .error("axiom constants require explicit type annotation"));
                }
                let mut stack = Stack::new();
                bind_explicit_value_params(&mut stack, &local_family_params.value_params);
                bind_datatype_value_params(&mut stack, datatype_params);
                let value = if let Some(instance_name) = defined_name.as_instance() {
                    Evaluator::new_for_instance_member(
                        project,
                        &self.bindings,
                        Some(&mut self.token_map),
                        instance_name,
                    )
                    .evaluate_value_with_stack(&mut stack, &ls.value, None)?
                } else {
                    self.evaluator(project)
                        .evaluate_value_with_stack(&mut stack, &ls.value, None)?
                };
                let acorn_type = value.get_type();
                (acorn_type, Some(value))
            }
        };
        let acorn_type = if explicit_value_param_types.is_empty() {
            acorn_type
        } else {
            AcornType::functional(explicit_value_param_types.clone(), acorn_type)
        };
        let value = if explicit_value_param_types.is_empty() {
            value
        } else {
            value.map(|value| AcornValue::lambda(explicit_value_param_types.clone(), value))
        };

        for param in local_type_params.iter().rev() {
            self.bindings.remove_type(&param.name);
        }

        let type_params = match datatype_params {
            Some(p) => {
                if !local_type_params.is_empty() {
                    return Err(ls
                        .name_token
                        .error("datatype parameters and let parameters cannot be used together"));
                }
                p.type_params.clone()
            }
            None => local_type_params,
        };
        let acorn_type = acorn_type.genericize(&type_params);
        let value = value.map(|v| v.genericize(&type_params));
        let def_str = statement.to_string();

        if datatype_value_param_types.is_empty() && explicit_value_param_types.is_empty() {
            if let Some(value) = &value {
                if let Some(simple_name) = value.as_simple_constant() {
                    match &defined_name {
                        DefinedName::Constant(constant_name) => {
                            let doc_comments = self.take_doc_comments();
                            self.bindings.add_constant_alias(
                                constant_name.clone(),
                                simple_name.clone(),
                                PotentialValue::Resolved(value.clone()),
                                doc_comments,
                                Some(def_str),
                            );
                            return Ok(());
                        }
                        DefinedName::Instance(_) => {}
                    }
                }
            }
        }
        self.define_constant(
            defined_name,
            type_params,
            datatype_value_param_types,
            acorn_type,
            value,
            range,
            Some(def_str),
        );
        Ok(())
    }

    pub(super) fn add_define_statement(
        &mut self,
        project: &Project,
        statement: &Statement,
        defined_name: DefinedName,
        self_type: Option<&AcornType>,
        datatype_params: Option<&DatatypeFamilyScope>,
        ds: &DefineStatement,
        range: Range,
    ) -> error::Result<()> {
        ds.name_token.check_not_reserved()?;
        if self.depth > 0 && !ds.type_params.is_empty() {
            return Err(ds
                .name_token
                .error("parameterized functions may only be defined at the top level"));
        }
        if self.bindings.constant_name_in_use(&defined_name) {
            return Err(ds.name_token.error(&format!(
                "function name '{}' already defined in this scope",
                defined_name
            )));
        }

        let recursion_name = defined_name.recursion_name();
        let (type_param_exprs, args) = if datatype_params.is_some() {
            (ds.type_params.clone(), ds.args.clone())
        } else {
            let local_family_params =
                self.evaluate_local_family_params(project, &ds.type_params)?;
            let mut args = local_family_params.value_declarations;
            args.extend(ds.args.clone());
            (local_family_params.type_param_exprs, args)
        };
        let (fn_param_names, _, arg_types, unbound_value, value_type) =
            self.bindings.evaluate_scoped_value(
                &type_param_exprs,
                &args,
                Some(&ds.return_type),
                &ds.return_value,
                self_type,
                recursion_name.as_ref(),
                defined_name.as_instance(),
                datatype_params.map(|params| params.type_params_slice()),
                datatype_params.map(|params| params.value_params_slice()),
                project,
                Some(&mut self.token_map),
            )?;
        let datatype_value_param_types = datatype_value_param_types(datatype_params);

        if let Some(datatype_type) = self_type {
            if &arg_types[0] != datatype_type {
                return Err(ds.args[0].token().error("self must be the datatype type"));
            }

            if ds.name_token.text() == "read"
                && (arg_types.len() != 2
                    || &arg_types[1] != datatype_type
                    || &value_type != datatype_type)
            {
                return Err(ds.name_token.error(&format!(
                    "{}.read should be type ({}, {}) -> {}",
                    datatype_type, datatype_type, datatype_type, datatype_type
                )));
            }
        }

        if let Some(v) = unbound_value {
            let mut fn_value = AcornValue::lambda(arg_types, v);

            let params = if let Some(datatype_params) = datatype_params {
                fn_value = fn_value.genericize(&datatype_params.type_params);

                if !fn_param_names.is_empty() {
                    fn_value = fn_value.genericize(&fn_param_names);
                    let mut combined_params = datatype_params.type_params.clone();
                    combined_params.extend(fn_param_names);
                    combined_params
                } else {
                    datatype_params.type_params.clone()
                }
            } else {
                fn_param_names
            };

            self.define_constant(
                defined_name,
                params,
                datatype_value_param_types,
                fn_value.get_type(),
                Some(fn_value),
                range,
                Some(statement.to_string()),
            );
            return Ok(());
        }

        let new_axiom_type = AcornType::functional(arg_types, value_type);
        let params = if let Some(datatype_params) = datatype_params {
            if !fn_param_names.is_empty() {
                let mut combined_params = datatype_params.type_params.clone();
                combined_params.extend(fn_param_names);
                combined_params
            } else {
                datatype_params.type_params.clone()
            }
        } else {
            fn_param_names
        };
        self.define_constant(
            defined_name,
            params,
            datatype_value_param_types,
            new_axiom_type,
            None,
            range,
            Some(statement.to_string()),
        );
        Ok(())
    }

    pub(super) fn add_theorem_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        ts: &TheoremStatement,
    ) -> error::Result<()> {
        let range = Range {
            start: statement.first_token.start_pos(),
            end: ts.claim_right_brace.end_pos(),
        };

        if let Some(name_token) = &ts.name_token {
            self.bindings
                .check_unqualified_name_available(name_token.text(), &statement.first_token)?;
        }

        let local_family_params = self.evaluate_local_family_params(project, &ts.type_params)?;
        let mut args = local_family_params.value_declarations;
        args.extend(ts.args.clone());
        let (type_params, arg_names, arg_types, value, _) = self.bindings.evaluate_scoped_value(
            &local_family_params.type_param_exprs,
            &args,
            None,
            &ts.claim,
            None,
            None,
            None,
            None,
            None,
            project,
            Some(&mut self.token_map),
        )?;

        let unbound_claim = value.ok_or_else(|| ts.claim.error("theorems must have values"))?;
        unbound_claim.check_type(Some(&AcornType::Bool), &ts.claim)?;

        let is_citation = self.bindings.is_citation(&unbound_claim, project);
        let cited_name = if is_citation {
            unbound_claim
                .is_named_function_call()
                .or_else(|| unbound_claim.as_name())
                .cloned()
        } else {
            None
        };
        if is_citation && ts.body.is_some() {
            return Err(statement.error("citations do not need proof blocks"));
        }

        let mut block_args = vec![];
        for (arg_name, arg_type) in arg_names.iter().zip(&arg_types) {
            block_args.push((arg_name.clone(), arg_type.clone()));
        }

        let arg_count = arg_types.len();
        let external_claim = AcornValue::forall(arg_types.clone(), unbound_claim.clone());
        if let Err(message) = external_claim.validate() {
            return Err(ts.claim.error(&message));
        }
        if let Err(message) = external_claim.validate_constants(&self.bindings) {
            return Err(ts.claim.error(&message));
        }

        let (premise, goal) = match &unbound_claim {
            AcornValue::Binary(BinaryOp::Implies, left, right) => {
                let premise_range = match ts.claim.premise() {
                    Some(p) => p.range(),
                    None => ts.claim.range(),
                };
                (
                    Some((left.to_arbitrary(), premise_range)),
                    right.to_arbitrary(),
                )
            }
            c => (None, c.to_arbitrary()),
        };

        let lambda_claim = AcornValue::lambda(arg_types, unbound_claim);
        let theorem_type = lambda_claim.get_type();
        if let Some(name_token) = &ts.name_token {
            let doc_comments = self.take_doc_comments();
            let name_range = name_token.range();
            self.bindings.add_unqualified_constant(
                name_token.text(),
                type_params.clone(),
                vec![],
                theorem_type.clone(),
                Some(lambda_claim.clone()),
                None,
                doc_comments,
                Some(name_range),
                ts.statement_string(),
            );
        }

        let already_proven = ts.axiomatic || is_citation;
        let source = Source::theorem(
            already_proven,
            self.module_id,
            range,
            true,
            self.depth,
            ts.name_token.as_ref().map(|t| t.text().to_string()),
        );
        let prop =
            Proposition::new(external_claim, type_params.clone(), source).with_arg_count(arg_count);

        let node = if already_proven {
            Node::structural(project, self, prop)
        } else {
            let block = Block::new(
                project,
                &self,
                type_params,
                block_args,
                BlockParams::Theorem(
                    ts.name_token.as_ref().map(|t| t.text()),
                    range,
                    premise,
                    goal,
                ),
                &statement.first_token,
                &statement.last_token,
                ts.body.as_ref(),
            )?;
            Node::block(project, self, block, Some(prop))
        };

        let index = self.add_node(node);
        self.add_node_lines(index, &statement.range());
        if is_citation {
            self.record_citation_statement(statement, cited_name, index);
        }
        if let Some(name_token) = &ts.name_token {
            let name = ConstantName::unqualified(self.module_id, name_token.text());
            self.bindings.mark_as_theorem(&name);
        }

        Ok(())
    }

    pub(super) fn add_variable_satisfy_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        vss: &VariableSatisfyStatement,
    ) -> error::Result<()> {
        let module_id = self.module_id;
        self.add_variable_satisfy_statement_named(project, statement, vss, None, move |name| {
            DefinedName::unqualified(module_id, name)
        })
    }

    pub(super) fn add_variable_satisfy_statement_named<F>(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        vss: &VariableSatisfyStatement,
        datatype_params: Option<&DatatypeFamilyScope>,
        mut defined_name_for: F,
    ) -> error::Result<()>
    where
        F: FnMut(&str) -> DefinedName,
    {
        if self.depth > 0 && !vss.type_params.is_empty() {
            return Err(vss.declarations[0]
                .token()
                .error("parameterized constants may only be defined at the top level"));
        }

        let local_family_params = if datatype_params.is_some() {
            LocalFamilyParams {
                type_param_exprs: vss.type_params.clone(),
                type_params: self
                    .evaluator(project)
                    .evaluate_type_params(&vss.type_params)?,
                value_params: vec![],
                value_declarations: vec![],
            }
        } else {
            self.evaluate_local_family_params(project, &vss.type_params)?
        };
        let local_type_params = local_family_params.type_params.clone();
        for param in &local_type_params {
            self.bindings.add_arbitrary_type(param.clone());
        }

        let family_value_param_count = datatype_params
            .map(|params| params.value_params.len() as AtomId)
            .unwrap_or(0)
            + local_family_params.value_params.len() as AtomId;
        let family_value_param_types = datatype_value_param_types(datatype_params);
        let explicit_value_param_types =
            explicit_value_param_types(&local_family_params.value_params);
        for declaration in &vss.declarations {
            if let Declaration::Typed(_, type_expr) = declaration {
                let mut stack = Stack::new();
                bind_explicit_value_params(&mut stack, &local_family_params.value_params);
                bind_datatype_value_params(&mut stack, datatype_params);
                self.evaluator(project)
                    .evaluate_type_with_stack(&mut stack, type_expr)?;
            }
        }

        let mut stack = Stack::new();
        bind_explicit_value_params(&mut stack, &local_family_params.value_params);
        bind_datatype_value_params(&mut stack, datatype_params);
        let mut no_token_evaluator = Evaluator::new(project, &self.bindings, None);
        let (quant_names, quant_types) =
            no_token_evaluator.bind_args_may_shadow(&mut stack, &vss.declarations, None)?;
        let general_claim_value = no_token_evaluator.evaluate_value_with_stack(
            &mut stack,
            &vss.condition,
            Some(&AcornType::Bool),
        )?;
        let general_claim =
            AcornValue::Exists(quant_types.clone(), Box::new(general_claim_value.clone()));
        let definition_type_params = match datatype_params {
            Some(p) => {
                if !local_type_params.is_empty() {
                    return Err(vss.declarations[0]
                        .token()
                        .error("datatype parameters and let parameters cannot be used together"));
                }
                p.type_params.clone()
            }
            None => local_type_params.clone(),
        };
        let mut block_args = explicit_value_block_args(&local_family_params.value_params);
        block_args.extend(datatype_value_block_args(datatype_params));
        let block = Block::new(
            project,
            &self,
            vec![],
            block_args,
            BlockParams::VariableSatisfy(general_claim, vss.condition.range()),
            &statement.first_token,
            &statement.last_token,
            None,
        )?;

        let mut constant_values = Vec::new();
        for ((declaration, quant_name), quant_type) in vss
            .declarations
            .iter()
            .zip(quant_names.iter())
            .zip(quant_types.iter())
        {
            let defined_name = defined_name_for(quant_name);
            if self.bindings.constant_name_in_use(&defined_name) {
                return Err(declaration.token().error(&format!(
                    "constant name '{}' already defined in this scope",
                    &defined_name
                )));
            }

            let generic_value_type = quant_type.clone().genericize(&definition_type_params);
            let constant_type = if explicit_value_param_types.is_empty() {
                generic_value_type.clone()
            } else {
                AcornType::functional(
                    explicit_value_param_types.clone(),
                    generic_value_type.clone(),
                )
            };
            let def_str = format!("{}: {}", quant_name, constant_type);
            self.bindings.add_defined_name(
                &defined_name,
                definition_type_params.clone(),
                family_value_param_types.clone(),
                constant_type.clone(),
                None,
                None,
                vec![],
                Some(declaration.token().range()),
                Some(def_str),
            );

            let const_name = defined_name
                .as_constant()
                .ok_or_else(|| {
                    statement.error("let ... satisfy cannot define instance attributes")
                })?
                .clone();
            let type_args: Vec<_> = definition_type_params
                .iter()
                .map(|p| AcornType::Arbitrary(p.clone()))
                .collect();
            let mut constant_value = AcornValue::constant(
                const_name,
                type_args,
                constant_type.clone(),
                constant_type,
                vec![],
                vec![],
            );
            if !explicit_value_param_types.is_empty() {
                let explicit_value_args = local_family_params
                    .value_params
                    .iter()
                    .enumerate()
                    .map(|(i, value_param)| {
                        AcornValue::Variable(i as AtomId, value_param.value_type.clone())
                    })
                    .collect();
                constant_value = AcornValue::apply(constant_value, explicit_value_args);
            }
            constant_values.push(constant_value);
        }

        let num_vars = quant_names.len() as AtomId;
        let specific_claim_value = general_claim_value.bind_values(
            family_value_param_count,
            family_value_param_count + num_vars,
            &constant_values,
        );
        let external_claim = quantify_over_explicit_value_params(
            &local_family_params.value_params,
            quantify_over_datatype_value_params(datatype_params, specific_claim_value),
        )
        .genericize(&definition_type_params);
        let source = Source::anonymous(self.module_id, statement.range(), self.depth);
        let specific_prop = Proposition::new(external_claim, definition_type_params, source);
        let index = self.add_node(Node::block(project, self, block, Some(specific_prop)));
        self.add_node_lines(index, &statement.range());

        for param in local_type_params.iter().rev() {
            self.bindings.remove_type(&param.name);
        }

        Ok(())
    }

    pub(super) fn add_function_satisfy_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        fss: &FunctionSatisfyStatement,
    ) -> error::Result<()> {
        let defined_name = DefinedName::unqualified(self.module_id, fss.name_token.text());
        self.add_function_satisfy_statement_named(project, statement, fss, defined_name, None)
    }

    pub(super) fn add_function_satisfy_statement_named(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        fss: &FunctionSatisfyStatement,
        defined_name: DefinedName,
        datatype_params: Option<&DatatypeFamilyScope>,
    ) -> error::Result<()> {
        fss.name_token.check_not_reserved()?;
        if self.bindings.constant_name_in_use(&defined_name) {
            return Err(fss.name_token.error(&format!(
                "function name '{}' already defined in this scope",
                defined_name
            )));
        }

        let definition_range = Range {
            start: statement.first_token.start_pos(),
            end: fss.satisfy_token.end_pos(),
        };

        if self.depth > 0 && !fss.type_params.is_empty() {
            return Err(fss
                .name_token
                .error("parameterized functions may only be defined at the top level"));
        }

        let recursion_name = defined_name.recursion_name();
        let (type_param_exprs, declarations) = if datatype_params.is_some() {
            (fss.type_params.clone(), fss.declarations.clone())
        } else {
            let local_family_params =
                self.evaluate_local_family_params(project, &fss.type_params)?;
            let mut declarations = local_family_params.value_declarations;
            declarations.extend(fss.declarations.clone());
            (local_family_params.type_param_exprs, declarations)
        };
        let (fn_type_params, mut arg_names, mut arg_types, condition, _) =
            self.bindings.evaluate_scoped_value(
                &type_param_exprs,
                &declarations,
                None,
                &fss.condition,
                None,
                recursion_name.as_ref(),
                defined_name.as_instance(),
                datatype_params.map(|params| params.type_params_slice()),
                datatype_params.map(|params| params.value_params_slice()),
                project,
                Some(&mut self.token_map),
            )?;
        let family_value_param_count = datatype_params
            .map(|params| params.value_params.len() as AtomId)
            .unwrap_or(0);
        let family_value_param_types = datatype_value_param_types(datatype_params);

        let unbound_condition = condition.ok_or_else(|| statement.error("missing condition"))?;
        if unbound_condition.get_type() != AcornType::Bool {
            return Err(fss.condition.error("condition must be a boolean"));
        }

        let _return_name = arg_names.pop().unwrap();
        let return_type = arg_types.pop().unwrap();
        let mut block_args = datatype_value_block_args(datatype_params);
        block_args.extend(arg_names.iter().cloned().zip(arg_types.iter().cloned()));
        let return_index = family_value_param_count + arg_types.len() as AtomId;

        let block = Block::new(
            project,
            &self,
            fn_type_params.clone(),
            block_args,
            BlockParams::FunctionSatisfy(
                unbound_condition.clone(),
                return_type.clone(),
                fss.condition.range(),
            ),
            &statement.first_token,
            &statement.last_token,
            fss.body.as_ref(),
        )?;

        let function_type = AcornType::functional(arg_types.clone(), return_type);
        let mut all_type_params = datatype_params
            .map(|params| params.type_params.clone())
            .unwrap_or_default();
        all_type_params.extend(fn_type_params);
        let generic_function_type = function_type.clone().genericize(&all_type_params);
        let doc_comments = self.take_doc_comments();
        self.bindings.add_defined_name(
            &defined_name,
            all_type_params.clone(),
            family_value_param_types.clone(),
            generic_function_type.clone(),
            None,
            None,
            doc_comments,
            Some(fss.name_token.range()),
            Some(statement.to_string()),
        );
        let const_name = defined_name
            .as_constant()
            .ok_or_else(|| statement.error("function satisfy cannot define instance attributes"))?
            .clone();
        let type_args: Vec<_> = all_type_params
            .iter()
            .map(|p| AcornType::Arbitrary(p.clone()))
            .collect();
        let function_constant = AcornValue::constant(
            const_name,
            type_args,
            function_type.clone(),
            generic_function_type,
            vec![],
            vec![],
        );
        let function_term = AcornValue::apply(
            function_constant.clone(),
            arg_types
                .iter()
                .enumerate()
                .map(|(i, t)| {
                    AcornValue::Variable(family_value_param_count + i as AtomId, t.clone())
                })
                .collect(),
        );
        let return_bound =
            unbound_condition.bind_values(return_index, return_index, &[function_term]);
        let arg_count = arg_types.len();
        let arb_condition = AcornValue::ForAll(arg_types, Box::new(return_bound));

        let external_condition =
            quantify_over_datatype_value_params(datatype_params, arb_condition)
                .genericize(&all_type_params);
        let generic_constant = function_constant.genericize(&all_type_params);

        let source = Source::constant_definition(
            self.module_id,
            definition_range,
            self.depth,
            Arc::new(generic_constant),
            &defined_name.to_string(),
        );
        let prop =
            Proposition::new(external_condition, all_type_params, source).with_arg_count(arg_count);

        let index = self.add_node(Node::block(project, self, block, Some(prop)));
        self.add_node_lines(index, &statement.range());
        Ok(())
    }

    /// Adds a claim statement to the environment.
    pub(super) fn add_claim_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        cs: &ClaimStatement,
    ) -> error::Result<()> {
        let claim = self
            .evaluator(project)
            .evaluate_value(&cs.claim, Some(&AcornType::Bool))?;
        if claim == AcornValue::Bool(false) {
            self.includes_explicit_false = true;
        }

        if self.bindings.is_citation(&claim, project) {
            // Extract the cited theorem name before expand_citation inlines it.
            let cited_name = claim
                .is_named_function_call()
                .or_else(|| claim.as_name())
                .cloned();

            let claim = claim.expand_lambdas(0);
            let source = Source::anonymous(self.module_id, statement.range(), self.depth);
            let prop = Proposition::new(claim, vec![], source);
            let prop = self.bindings.expand_citation(prop, project);
            let index = self.add_node(Node::structural(project, self, prop));
            self.record_citation_statement(statement, cited_name, index);
            self.add_other_lines(statement);
        } else {
            let source = Source::anonymous(self.module_id, statement.range(), self.depth);
            let prop = Proposition::new(claim, vec![], source);
            let index =
                self.add_node(Node::claim(project, self, prop).map_err(|e| statement.error(&e))?);
            self.add_node_lines(index, &statement.range());
        }
        Ok(())
    }

    pub(super) fn add_destructuring_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        ds: &DestructuringStatement,
    ) -> error::Result<()> {
        self.add_other_lines(statement);

        let mut arg_names = vec![];
        for arg_token in &ds.args {
            let arg_name = arg_token.text().to_string();
            if arg_names.contains(&arg_name) {
                return Err(arg_token.error(&format!(
                    "duplicate argument name '{}' in destructuring pattern",
                    arg_name
                )));
            }
            arg_names.push(arg_name.clone());

            self.bindings
                .check_unqualified_name_available(&arg_name, arg_token)?;
        }

        let value = self.evaluator(project).evaluate_value(&ds.value, None)?;
        let value_type = value.get_type();

        let mut empty_stack = Stack::new();
        let mut function = self
            .evaluator(project)
            .evaluate_as_generic_value(&mut empty_stack, &ds.function)?;

        let function_type_before = function.get_type();
        let function_ftype_before = match &function_type_before {
            AcornType::Function(ft) => ft,
            _ => {
                return Err(ds.function.error(&format!(
                    "expected a function type, but got {}",
                    function_type_before
                )));
            }
        };

        let return_type_before = function_ftype_before.return_type.as_ref().clone();
        if return_type_before != value_type {
            function = InferenceEngine::new(&self.bindings).infer_function_return_type(
                function,
                &value_type,
                "destructuring function return type",
                &ds.value,
            )?;
        }

        let function_type = function.get_type();
        let (arg_types, return_type) = match &function_type {
            AcornType::Function(ft) => (ft.arg_types.clone(), ft.return_type.as_ref().clone()),
            _ => {
                return Err(ds.function.error(&format!(
                    "expected a function type, but got {}",
                    function_type
                )));
            }
        };

        if arg_types.len() != ds.args.len() {
            return Err(statement.error(&format!(
                "function expects {} arguments, but {} were provided in the pattern",
                arg_types.len(),
                ds.args.len()
            )));
        }

        if return_type != value_type {
            return Err(ds.value.error(&format!(
                "type mismatch: function returns {} but value has type {}",
                return_type, value_type
            )));
        }

        if arg_types.iter().any(|t| t.has_generic()) {
            return Err(ds
                .function
                .error("could not infer all argument types for destructuring pattern"));
        }

        let mut stack = Stack::new();
        let quant_names: Vec<String> = arg_names.clone();
        let quant_types = arg_types.clone();

        let atom_ids: Vec<AtomId> = quant_names
            .iter()
            .zip(&quant_types)
            .map(|(name, arg_type)| stack.insert(name.clone(), arg_type.clone()))
            .collect();

        let general_arg_values: Vec<_> = atom_ids
            .iter()
            .zip(&quant_types)
            .map(|(atom_id, arg_type)| AcornValue::Variable(*atom_id, arg_type.clone()))
            .collect();

        let general_applied = AcornValue::apply(function.clone(), general_arg_values);
        let general_equality = AcornValue::equals(general_applied, value.clone());

        let general_claim = AcornValue::Exists(quant_types.clone(), Box::new(general_equality));
        let source = Source::anonymous(self.module_id, statement.range(), self.depth);
        let general_prop = Proposition::new(general_claim, vec![], source);
        let index = self
            .add_node(Node::claim(project, self, general_prop).map_err(|e| statement.error(&e))?);
        self.add_node_lines(index, &statement.range());

        for (arg_token, arg_type) in ds.args.iter().zip(&arg_types) {
            let arg_name = arg_token.text();
            self.bindings.add_unqualified_constant(
                arg_name,
                vec![],
                vec![],
                arg_type.clone(),
                None,
                None,
                vec![],
                Some(arg_token.range()),
                format!("{}: {}", arg_name, arg_type),
            );
        }

        let arg_values: Vec<_> = ds
            .args
            .iter()
            .zip(&arg_types)
            .map(|(token, arg_type)| {
                let name = ConstantName::unqualified(self.module_id, token.text());
                AcornValue::constant(
                    name,
                    vec![],
                    arg_type.clone(),
                    arg_type.clone(),
                    vec![],
                    vec![],
                )
            })
            .collect();

        let applied = AcornValue::apply(function, arg_values);
        let equality = AcornValue::equals(applied, value);
        let source = Source::anonymous(self.module_id, statement.range(), self.depth);
        let prop = Proposition::new(equality, vec![], source);
        self.add_node(Node::structural(project, self, prop));

        Ok(())
    }
}

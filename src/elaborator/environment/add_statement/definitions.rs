use super::transport::TransportBuilder;
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

fn lambda_over_datatype_value_params(
    datatype_params: Option<&DatatypeFamilyScope>,
    value: AcornValue,
) -> AcornValue {
    let value_param_types = datatype_value_param_types(datatype_params);
    if value_param_types.is_empty() {
        value
    } else {
        AcornValue::lambda(value_param_types, value)
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
    fn declare_witness_constant(
        &mut self,
        defined_name: &DefinedName,
        definition_type_params: &[TypeParam],
        value_type: &AcornType,
        explicit_value_params: &[ValueParam],
        datatype_params: Option<&DatatypeFamilyScope>,
        doc_comments: Vec<String>,
        range: Range,
        definition_string: String,
        source: &dyn ErrorContext,
        instance_error: &str,
    ) -> error::Result<AcornValue> {
        let const_name = defined_name
            .as_constant()
            .ok_or_else(|| source.error(instance_error))?
            .clone();
        let explicit_value_param_types = explicit_value_param_types(explicit_value_params);
        let family_value_param_types = datatype_value_param_types(datatype_params);
        let constant_value_param_types = if explicit_value_param_types.is_empty() {
            family_value_param_types.clone()
        } else {
            explicit_value_param_types.clone()
        };
        let generic_value_type = value_type.clone().genericize(definition_type_params);
        let constant_type = if explicit_value_param_types.is_empty() {
            generic_value_type.clone()
        } else {
            AcornType::functional_from_promoted_ambient(
                explicit_value_param_types.clone(),
                generic_value_type.clone(),
            )
        };

        self.bindings.add_defined_name(
            defined_name,
            definition_type_params.to_vec(),
            constant_value_param_types.clone(),
            constant_type.clone(),
            None,
            None,
            doc_comments,
            Some(range),
            Some(definition_string),
        );

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
            constant_value_param_types,
        );
        if explicit_value_param_types.is_empty() {
            if let Some(datatype_params) = datatype_params {
                let family_value_args = datatype_params
                    .value_params()
                    .iter()
                    .enumerate()
                    .map(|(i, value_param)| {
                        AcornValue::Variable(i as AtomId, value_param.value_type.clone())
                    })
                    .collect::<Vec<_>>();
                constant_value = constant_value.bind_value_params(&family_value_args, source)?;
            }
        } else {
            let explicit_value_args = explicit_value_params
                .iter()
                .enumerate()
                .map(|(i, value_param)| {
                    AcornValue::Variable(i as AtomId, value_param.value_type.clone())
                })
                .collect();
            constant_value = AcornValue::apply(constant_value, explicit_value_args);
        }
        Ok(constant_value)
    }

    fn add_witness_let_from_constraint(
        &mut self,
        project: &dyn ProjectLookup,
        statement: &Statement,
        defined_name: &DefinedName,
        let_statement: &LetStatement,
        range: Range,
        datatype_params: Option<&DatatypeFamilyScope>,
        local_family_params: &LocalFamilyParams,
        definition_type_params: Vec<TypeParam>,
        target_type: AcornType,
        family_value_param_count: AtomId,
        target_constraint: AcornValue,
        instance_error: &str,
    ) -> error::Result<()> {
        let general_claim =
            AcornValue::exists(vec![target_type.clone()], target_constraint.clone());
        let mut block_args = explicit_value_block_args(&local_family_params.value_params);
        block_args.extend(datatype_value_block_args(datatype_params));
        let block = Block::new(
            project,
            &self,
            vec![],
            block_args,
            BlockParams::variable_satisfy(general_claim, let_statement.value.range()),
            &statement.first_token,
            &statement.last_token,
            None,
        )?;

        let doc_comments = self.take_doc_comments();
        let constant_value = self.declare_witness_constant(
            defined_name,
            &definition_type_params,
            &target_type,
            &local_family_params.value_params,
            datatype_params,
            doc_comments,
            range,
            statement.to_string(),
            statement,
            instance_error,
        )?;

        let specific_constraint = target_constraint.bind_values(
            family_value_param_count,
            family_value_param_count + 1,
            &[constant_value],
        );
        let external_claim = quantify_over_explicit_value_params(
            &local_family_params.value_params,
            quantify_over_datatype_value_params(datatype_params, specific_constraint),
        )
        .genericize(&definition_type_params);
        let source = Source::anonymous(self.module_id, statement.range(), self.depth);
        let prop = Proposition::new(external_claim, definition_type_params, source);
        let index = self.add_node(Node::block(project, self, block, Some(prop)));
        self.add_node_lines(index, &statement.range());
        Ok(())
    }

    fn add_result_spec_let_statement(
        &mut self,
        project: &dyn ProjectLookup,
        statement: &Statement,
        defined_name: DefinedName,
        let_statement: &LetStatement,
        range: Range,
        datatype_params: Option<&DatatypeFamilyScope>,
        local_family_params: &LocalFamilyParams,
        local_type_params: &[TypeParam],
        target_type: AcornType,
    ) -> error::Result<()> {
        if let_statement.value.is_axiom() {
            return Err(let_statement
                .value
                .first_token()
                .error("axiom constants require direct definitions"));
        }
        let definition_type_params = match datatype_params {
            Some(p) => {
                if !local_type_params.is_empty() {
                    return Err(let_statement
                        .name_token
                        .error("datatype parameters and let parameters cannot be used together"));
                }
                p.type_params().to_vec()
            }
            None => local_type_params.to_vec(),
        };

        for param in local_type_params {
            self.bindings.add_arbitrary_type(param.clone());
        }

        let result = (|| {
            let mut stack = Stack::new();
            bind_explicit_value_params(&mut stack, &local_family_params.value_params);
            bind_datatype_value_params(&mut stack, datatype_params);
            let family_value_param_count = stack.len() as AtomId;
            let target_index = stack.insert("\0result".to_string(), target_type.clone());
            let target = AcornValue::Variable(target_index, target_type.clone());
            let mut evaluator = if let Some(instance_name) = defined_name.as_instance() {
                Evaluator::new_for_instance_member(project, &self.bindings, None, instance_name)
            } else {
                Evaluator::new(project, &self.bindings, None)
            };
            let spec = evaluator.evaluate_result_spec_with_stack(
                &mut stack,
                &let_statement.value,
                target,
                &target_type,
            )?;
            stack.remove("\0result");
            let local_obligations = evaluator.take_local_obligations();
            self.add_genericized_local_obligations(
                project,
                &definition_type_params,
                local_obligations,
            )?;
            self.add_witness_let_from_constraint(
                project,
                statement,
                &defined_name,
                let_statement,
                range,
                datatype_params,
                local_family_params,
                definition_type_params,
                target_type,
                family_value_param_count,
                spec,
                "result-spec let cannot define instance attributes",
            )
        })();

        for param in local_type_params.iter().rev() {
            self.bindings.remove_type(&param.name);
        }

        result
    }

    fn add_transport_let_statement(
        &mut self,
        project: &dyn ProjectLookup,
        statement: &Statement,
        defined_name: DefinedName,
        let_statement: &LetStatement,
        range: Range,
        datatype_params: Option<&DatatypeFamilyScope>,
        local_family_params: &LocalFamilyParams,
        local_type_params: &[TypeParam],
        target_type: AcornType,
        source_expr: &Expression,
        transport_token: &Token,
    ) -> error::Result<()> {
        if let_statement.name_token.token_type == TokenType::Numeral {
            return Err(let_statement
                .name_token
                .error("transport cannot define numeric datatype members"));
        }

        let definition_type_params = match datatype_params {
            Some(p) => {
                if !local_type_params.is_empty() {
                    return Err(let_statement
                        .name_token
                        .error("datatype parameters and let parameters cannot be used together"));
                }
                p.type_params().to_vec()
            }
            None => local_type_params.to_vec(),
        };

        let mut stack = Stack::new();
        bind_explicit_value_params(&mut stack, &local_family_params.value_params);
        bind_datatype_value_params(&mut stack, datatype_params);
        let mut evaluator = self.evaluator(project);
        let source_value = evaluator.evaluate_value_with_stack(&mut stack, source_expr, None)?;
        let local_obligations = evaluator.take_local_obligations();
        let source_type = source_value.get_type();

        let family_value_param_count = datatype_params
            .map(|params| params.value_params().len() as AtomId)
            .unwrap_or(0)
            + local_family_params.value_params.len() as AtomId;
        let target_variable = AcornValue::Variable(family_value_param_count, target_type.clone());
        let target_constraint = {
            let transport = TransportBuilder::new(self, project);
            transport.relation(
                &source_type,
                &target_type,
                source_value.clone(),
                target_variable,
                transport_token,
                family_value_param_count + 1,
            )?
        };
        self.add_genericized_local_obligations(
            project,
            &definition_type_params,
            local_obligations,
        )?;

        let mut block_args = explicit_value_block_args(&local_family_params.value_params);
        block_args.extend(datatype_value_block_args(datatype_params));
        if local_family_params.value_params.is_empty() && datatype_params.is_none() {
            let prepared = {
                let transport = TransportBuilder::new(self, project);
                if let Some(witness_value) = transport.witness(
                    &source_type,
                    &target_type,
                    source_value.clone(),
                    transport_token,
                    family_value_param_count,
                )? {
                    let claim = transport.relation(
                        &source_type,
                        &target_type,
                        source_value.clone(),
                        witness_value.clone(),
                        transport_token,
                        family_value_param_count,
                    )?;
                    let block = Block::new(
                        project,
                        &self,
                        vec![],
                        block_args.clone(),
                        BlockParams::variable_satisfy(claim, let_statement.value.range()),
                        &statement.first_token,
                        &statement.last_token,
                        None,
                    )?;
                    Some((witness_value, block))
                } else {
                    None
                }
            };
            if let Some((witness_value, block)) = prepared {
                self.define_constant(
                    defined_name.clone(),
                    definition_type_params.clone(),
                    vec![],
                    target_type.clone().genericize(&definition_type_params),
                    Some(witness_value.genericize(&definition_type_params)),
                    range,
                    Some(statement.to_string()),
                );
                let constant_value = self
                    .bindings
                    .get_constant_value(&defined_name)
                    .map_err(|e| statement.error(&e))?
                    .as_value(statement)?;
                let external_claim = {
                    let transport = TransportBuilder::new(self, project);
                    transport.relation(
                        &source_type,
                        &target_type,
                        source_value,
                        constant_value,
                        transport_token,
                        family_value_param_count,
                    )?
                }
                .genericize(&definition_type_params);
                let source = Source::anonymous(self.module_id, statement.range(), self.depth);
                let prop = Proposition::new(external_claim, definition_type_params, source);
                let index = self.add_node(Node::block(project, self, block, Some(prop)));
                self.add_node_lines(index, &statement.range());
                return Ok(());
            }
        }

        self.add_witness_let_from_constraint(
            project,
            statement,
            &defined_name,
            let_statement,
            range,
            datatype_params,
            local_family_params,
            definition_type_params,
            target_type,
            family_value_param_count,
            target_constraint,
            "transport cannot define instance attributes",
        )
    }

    fn evaluate_local_family_params(
        &mut self,
        project: &dyn ProjectLookup,
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
                crate::elaborator::acorn_type::FamilyParam::Value(_) => {
                    return Err(expr.name.error(&format!(
                        "implicit value parameter '{}' in [] is not supported; put value parameters in () instead",
                        expr.name.text()
                    )));
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
        project: &dyn ProjectLookup,
        statement: &Statement,
        defined_name: DefinedName,
        let_statement: &LetStatement,
        range: Range,
        datatype_params: Option<&DatatypeFamilyScope>,
    ) -> error::Result<()> {
        let_statement.name_token.check_not_reserved()?;

        if self.bindings.constant_name_in_use(&defined_name) {
            return Err(let_statement.name_token.error(&format!(
                "constant name '{}' already defined in this scope",
                &defined_name
            )));
        }

        if self.depth > 0 && !let_statement.type_params.is_empty() {
            return Err(let_statement
                .name_token
                .error("parameterized constants may only be defined at the top level"));
        }

        let local_family_params = if datatype_params.is_some() {
            LocalFamilyParams {
                type_param_exprs: let_statement.type_params.clone(),
                type_params: self
                    .evaluator(project)
                    .evaluate_type_params(&let_statement.type_params)?,
                value_params: vec![],
                value_declarations: vec![],
            }
        } else {
            self.evaluate_local_family_params(project, &let_statement.type_params)?
        };
        let local_type_params = local_family_params.type_params.clone();
        for param in &local_type_params {
            self.bindings.add_arbitrary_type(param.clone());
        }

        let datatype_value_param_types = datatype_value_param_types(datatype_params);
        let explicit_value_param_types =
            explicit_value_param_types(&local_family_params.value_params);
        enum LetEvaluation {
            Regular(AcornType, Option<AcornValue>, Vec<LocalObligation>),
            Added(error::Result<()>),
        }
        let evaluation: error::Result<LetEvaluation> = (|| {
            Ok(match &let_statement.type_expr {
                Some(type_expr) => {
                    let mut stack = Stack::new();
                    bind_explicit_value_params(&mut stack, &local_family_params.value_params);
                    bind_datatype_value_params(&mut stack, datatype_params);
                    let acorn_type = self
                        .evaluator(project)
                        .evaluate_type_with_stack(&mut stack, type_expr)?;
                    if let_statement.name_token.token_type == TokenType::Numeral {
                        match &defined_name {
                            DefinedName::Constant(constant_name) => {
                                let (datatype_module_id, datatype_name) =
                                    match constant_name.as_attribute() {
                                        Some((datatype_module_id, datatype_name, _)) => {
                                            (datatype_module_id, datatype_name.to_string())
                                        }
                                        _ => {
                                            return Err(let_statement.name_token.error(
                                                "numeric literals must be datatype members",
                                            ))
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
                    if let Some((transport_token, source_expr)) =
                        let_statement.value.transport_operand()
                    {
                        return Ok(LetEvaluation::Added(self.add_transport_let_statement(
                            project,
                            statement,
                            defined_name.clone(),
                            let_statement,
                            range,
                            datatype_params,
                            &local_family_params,
                            &local_type_params,
                            acorn_type,
                            source_expr,
                            transport_token,
                        )));
                    }
                    let (value, local_obligations) = if let_statement.value.is_axiom() {
                        (None, vec![])
                    } else {
                        let mut stack = Stack::new();
                        bind_explicit_value_params(&mut stack, &local_family_params.value_params);
                        bind_datatype_value_params(&mut stack, datatype_params);
                        let mut evaluator = if let Some(instance_name) = defined_name.as_instance()
                        {
                            Evaluator::new_for_instance_member(
                                project,
                                &self.bindings,
                                Some(&mut self.token_map),
                                instance_name,
                            )
                        } else {
                            self.evaluator(project)
                        };
                        let value = evaluator.evaluate_value_with_stack(
                            &mut stack,
                            &let_statement.value,
                            Some(&acorn_type),
                        )?;
                        let local_obligations = evaluator.take_local_obligations();
                        (Some(value), local_obligations)
                    };
                    LetEvaluation::Regular(acorn_type, value, local_obligations)
                }
                None => {
                    if let Some((transport_token, _)) = let_statement.value.transport_operand() {
                        return Err(
                            transport_token.error("transport requires an explicit type annotation")
                        );
                    }
                    if let_statement.value.is_axiom() {
                        return Err(let_statement
                            .value
                            .first_token()
                            .error("axiom constants require explicit type annotation"));
                    }
                    let mut stack = Stack::new();
                    bind_explicit_value_params(&mut stack, &local_family_params.value_params);
                    bind_datatype_value_params(&mut stack, datatype_params);
                    let mut evaluator = if let Some(instance_name) = defined_name.as_instance() {
                        Evaluator::new_for_instance_member(
                            project,
                            &self.bindings,
                            Some(&mut self.token_map),
                            instance_name,
                        )
                    } else {
                        self.evaluator(project)
                    };
                    let value = evaluator.evaluate_value_with_stack(
                        &mut stack,
                        &let_statement.value,
                        None,
                    )?;
                    let local_obligations = evaluator.take_local_obligations();
                    let acorn_type = value.get_type();
                    LetEvaluation::Regular(acorn_type, Some(value), local_obligations)
                }
            })
        })();

        for param in local_type_params.iter().rev() {
            self.bindings.remove_type(&param.name);
        }

        let (acorn_type, value, local_obligations) = match evaluation? {
            LetEvaluation::Regular(acorn_type, value, local_obligations) => {
                (acorn_type, value, local_obligations)
            }
            LetEvaluation::Added(result) => {
                return result;
            }
        };
        if value.is_some() && local_obligations_need_result_spec_export(&local_obligations) {
            return self.add_result_spec_let_statement(
                project,
                statement,
                defined_name,
                let_statement,
                range,
                datatype_params,
                &local_family_params,
                &local_type_params,
                acorn_type,
            );
        }
        let acorn_type = if explicit_value_param_types.is_empty() {
            acorn_type
        } else {
            AcornType::functional_from_promoted_ambient(
                explicit_value_param_types.clone(),
                acorn_type,
            )
        };
        let value = if explicit_value_param_types.is_empty() {
            value
        } else {
            value.map(|value| AcornValue::lambda(explicit_value_param_types.clone(), value))
        };
        let value = value.map(|value| lambda_over_datatype_value_params(datatype_params, value));

        let type_params = match datatype_params {
            Some(p) => {
                if !local_type_params.is_empty() {
                    return Err(let_statement
                        .name_token
                        .error("datatype parameters and let parameters cannot be used together"));
                }
                p.type_params().to_vec()
            }
            None => local_type_params,
        };
        let acorn_type = acorn_type.genericize(&type_params);
        let value = value.map(|v| v.genericize(&type_params));
        self.add_genericized_local_obligations(project, &type_params, local_obligations)?;
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
            if explicit_value_param_types.is_empty() {
                datatype_value_param_types
            } else {
                explicit_value_param_types.clone()
            },
            acorn_type,
            value,
            range,
            Some(def_str),
        );
        Ok(())
    }

    fn add_result_spec_define_from_parts(
        &mut self,
        project: &dyn ProjectLookup,
        statement: &Statement,
        defined_name: DefinedName,
        datatype_params: Option<&DatatypeFamilyScope>,
        define_statement: &DefineStatement,
        range: Range,
        explicit_value_param_types: Vec<AcornType>,
        fn_type_params: Vec<TypeParam>,
        arg_names: Vec<String>,
        arg_types: Vec<AcornType>,
        spec: AcornValue,
        value_type: AcornType,
        local_obligations: Vec<LocalObligation>,
    ) -> error::Result<()> {
        let datatype_value_param_types = datatype_value_param_types(datatype_params);
        let family_value_param_count = datatype_value_param_types.len() as AtomId;
        let mut all_type_params = datatype_params
            .map(|params| params.type_params().to_vec())
            .unwrap_or_default();
        all_type_params.extend(fn_type_params.clone());
        self.add_local_obligations(project, &all_type_params, local_obligations)?;

        let mut block_args = datatype_value_block_args(datatype_params);
        block_args.extend(arg_names.iter().cloned().zip(arg_types.iter().cloned()));
        let block = Block::new(
            project,
            &self,
            fn_type_params.clone(),
            block_args,
            BlockParams::FunctionSatisfy(
                spec.clone(),
                value_type.clone(),
                define_statement.return_value.range(),
            ),
            &statement.first_token,
            &statement.last_token,
            None,
        )?;

        let function_type = AcornType::functional_from_scoped_context(
            arg_types.clone(),
            value_type,
            family_value_param_count,
        );
        let generic_function_type = function_type.clone().genericize(&all_type_params);
        let doc_comments = self.take_doc_comments();
        self.bindings.add_defined_name(
            &defined_name,
            all_type_params.clone(),
            if explicit_value_param_types.is_empty() {
                datatype_value_param_types.clone()
            } else {
                explicit_value_param_types.clone()
            },
            generic_function_type.clone(),
            None,
            None,
            doc_comments,
            Some(range),
            Some(statement.to_string()),
        );
        let const_name = defined_name
            .as_constant()
            .ok_or_else(|| statement.error("result-spec define cannot define instance attributes"))?
            .clone();
        let type_args: Vec<_> = all_type_params
            .iter()
            .map(|p| AcornType::Arbitrary(p.clone()))
            .collect();
        let mut function_constant = AcornValue::constant(
            const_name,
            type_args,
            function_type.clone(),
            generic_function_type,
            vec![],
            if explicit_value_param_types.is_empty() {
                datatype_value_param_types.clone()
            } else {
                explicit_value_param_types.clone()
            },
        );
        if explicit_value_param_types.is_empty() && !datatype_value_param_types.is_empty() {
            let family_value_args = datatype_params
                .expect("family value params should have a datatype scope")
                .value_params()
                .iter()
                .enumerate()
                .map(|(i, value_param)| {
                    AcornValue::Variable(i as AtomId, value_param.value_type.clone())
                })
                .collect::<Vec<_>>();
            function_constant =
                function_constant.bind_value_params(&family_value_args, statement)?;
        }
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
        let return_index = family_value_param_count + arg_types.len() as AtomId;
        let return_bound = spec.bind_values(return_index, return_index, &[function_term]);
        let arg_count = arg_types.len();
        let arb_condition = AcornValue::ForAll(arg_types, Box::new(return_bound));

        let external_condition =
            quantify_over_datatype_value_params(datatype_params, arb_condition)
                .genericize(&all_type_params);
        let generic_constant = function_constant.genericize(&all_type_params);

        let source = Source::constant_definition(
            self.module_id,
            statement.range(),
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

    pub(super) fn add_define_statement(
        &mut self,
        project: &dyn ProjectLookup,
        statement: &Statement,
        defined_name: DefinedName,
        self_type: Option<&AcornType>,
        datatype_params: Option<&DatatypeFamilyScope>,
        define_statement: &DefineStatement,
        range: Range,
    ) -> error::Result<()> {
        define_statement.name_token.check_not_reserved()?;
        if self.depth > 0 && !define_statement.type_params.is_empty() {
            return Err(define_statement
                .name_token
                .error("parameterized functions may only be defined at the top level"));
        }
        if self.bindings.constant_name_in_use(&defined_name) {
            return Err(define_statement.name_token.error(&format!(
                "function name '{}' already defined in this scope",
                defined_name
            )));
        }

        let recursion_name = defined_name.recursion_name();
        let (type_param_exprs, args, explicit_value_param_types) = if datatype_params.is_some() {
            (
                define_statement.type_params.clone(),
                define_statement.args.clone(),
                vec![],
            )
        } else {
            let local_family_params =
                self.evaluate_local_family_params(project, &define_statement.type_params)?;
            let mut args = local_family_params.value_declarations;
            args.extend(define_statement.args.clone());
            (
                local_family_params.type_param_exprs,
                args,
                explicit_value_param_types(&local_family_params.value_params),
            )
        };
        let (fn_param_names, _, arg_types, unbound_value, value_type, local_obligations) =
            self.bindings.evaluate_scoped_value(
                &type_param_exprs,
                &args,
                Some(&define_statement.return_type),
                &define_statement.return_value,
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
                return Err(define_statement.args[0]
                    .token()
                    .error("self must be the datatype type"));
            }

            if define_statement.name_token.text() == "read"
                && (arg_types.len() != 2
                    || &arg_types[1] != datatype_type
                    || &value_type != datatype_type)
            {
                return Err(define_statement.name_token.error(&format!(
                    "{}.read should be type ({}, {}) -> {}",
                    datatype_type, datatype_type, datatype_type, datatype_type
                )));
            }
        }

        if unbound_value.is_some() && local_obligations_need_result_spec_export(&local_obligations)
        {
            let (
                rel_fn_type_params,
                rel_arg_names,
                rel_arg_types,
                spec,
                rel_value_type,
                rel_local_obligations,
            ) = self.bindings.evaluate_scoped_result_spec(
                &type_param_exprs,
                &args,
                &define_statement.return_type,
                &define_statement.return_value,
                self_type,
                recursion_name.as_ref(),
                defined_name.as_instance(),
                datatype_params.map(|params| params.type_params_slice()),
                datatype_params.map(|params| params.value_params_slice()),
                project,
                None,
            )?;
            return self.add_result_spec_define_from_parts(
                project,
                statement,
                defined_name,
                datatype_params,
                define_statement,
                range,
                explicit_value_param_types,
                rel_fn_type_params,
                rel_arg_names,
                rel_arg_types,
                spec,
                rel_value_type,
                rel_local_obligations,
            );
        }

        let definition_type_params = if let Some(datatype_params) = datatype_params {
            if !fn_param_names.is_empty() {
                let mut combined_params = datatype_params.type_params().to_vec();
                combined_params.extend(fn_param_names.clone());
                combined_params
            } else {
                datatype_params.type_params().to_vec()
            }
        } else {
            fn_param_names.clone()
        };
        self.add_local_obligations(project, &definition_type_params, local_obligations)?;

        if let Some(v) = unbound_value {
            let fn_type = AcornType::functional_from_scoped_context(
                arg_types.clone(),
                value_type.clone(),
                datatype_value_param_types.len() as AtomId,
            );
            let mut fn_value = AcornValue::lambda(arg_types, v);

            let params = if let Some(datatype_params) = datatype_params {
                fn_value = lambda_over_datatype_value_params(Some(datatype_params), fn_value);
                fn_value = fn_value.genericize(datatype_params.type_params());

                if !fn_param_names.is_empty() {
                    fn_value = fn_value.genericize(&fn_param_names);
                    let mut combined_params = datatype_params.type_params().to_vec();
                    combined_params.extend(fn_param_names.clone());
                    combined_params
                } else {
                    datatype_params.type_params().to_vec()
                }
            } else {
                fn_param_names.clone()
            };
            let fn_type = fn_type.genericize(&params);

            self.define_constant(
                defined_name,
                params,
                if explicit_value_param_types.is_empty() {
                    datatype_value_param_types.clone()
                } else {
                    explicit_value_param_types.clone()
                },
                fn_type,
                Some(fn_value),
                range,
                Some(statement.to_string()),
            );
            return Ok(());
        }

        let new_axiom_type = AcornType::functional_from_scoped_context(
            arg_types,
            value_type,
            datatype_value_param_types.len() as AtomId,
        );
        let params = if let Some(datatype_params) = datatype_params {
            if !fn_param_names.is_empty() {
                let mut combined_params = datatype_params.type_params().to_vec();
                combined_params.extend(fn_param_names.clone());
                combined_params
            } else {
                datatype_params.type_params().to_vec()
            }
        } else {
            fn_param_names.clone()
        };
        let new_axiom_type = new_axiom_type.genericize(&params);
        self.define_constant(
            defined_name,
            params,
            if explicit_value_param_types.is_empty() {
                datatype_value_param_types
            } else {
                explicit_value_param_types
            },
            new_axiom_type,
            None,
            range,
            Some(statement.to_string()),
        );
        Ok(())
    }

    pub(super) fn add_theorem_statement(
        &mut self,
        project: &dyn ProjectLookup,
        statement: &Statement,
        theorem_statement: &TheoremStatement,
    ) -> error::Result<()> {
        let range = Range {
            start: statement.first_token.start_pos(),
            end: theorem_statement.claim_right_brace.end_pos(),
        };

        if let Some(name_token) = &theorem_statement.name_token {
            self.bindings
                .check_unqualified_name_available(name_token.text(), &statement.first_token)?;
        }

        let local_family_params =
            self.evaluate_local_family_params(project, &theorem_statement.type_params)?;
        let mut args = local_family_params.value_declarations;
        args.extend(theorem_statement.args.clone());
        let (mut type_params, mut arg_names, mut arg_types, value, _, mut local_obligations) =
            self.bindings.evaluate_scoped_value(
                &local_family_params.type_param_exprs,
                &args,
                None,
                &theorem_statement.claim,
                None,
                None,
                None,
                None,
                None,
                project,
                Some(&mut self.token_map),
            )?;

        let mut unbound_claim =
            value.ok_or_else(|| theorem_statement.claim.error("theorems must have values"))?;
        unbound_claim.check_type(Some(&AcornType::Bool), &theorem_statement.claim)?;

        if local_obligations_need_result_spec_export(&local_obligations) {
            let scoped_spec = self.bindings.evaluate_scoped_bool_result_spec(
                &local_family_params.type_param_exprs,
                &args,
                &theorem_statement.claim,
                None,
                None,
                None,
                None,
                None,
                project,
                None,
            )?;
            type_params = scoped_spec.0;
            arg_names = scoped_spec.1;
            arg_types = scoped_spec.2;
            unbound_claim = scoped_spec.3;
            local_obligations = scoped_spec.4;
        }

        let is_citation = self.bindings.is_citation(&unbound_claim, project);
        let cited_name = if is_citation {
            unbound_claim
                .is_named_function_call()
                .or_else(|| unbound_claim.as_name())
                .cloned()
        } else {
            None
        };
        if is_citation && theorem_statement.body.is_some() {
            return Err(statement.error("citations do not need proof blocks"));
        }

        let mut block_args = vec![];
        for (arg_name, arg_type) in arg_names.iter().zip(&arg_types) {
            block_args.push((arg_name.clone(), arg_type.clone()));
        }

        let arg_count = arg_types.len();
        let external_claim = AcornValue::forall(arg_types.clone(), unbound_claim.clone());
        if let Err(message) = external_claim.validate() {
            return Err(theorem_statement.claim.error(&message));
        }
        if let Err(message) = external_claim.validate_constants(&self.bindings) {
            return Err(theorem_statement.claim.error(&message));
        }
        self.add_local_obligations(project, &type_params, local_obligations)?;

        let (premise, goal) = match &unbound_claim {
            AcornValue::Binary(BinaryOp::Implies, left, right) => {
                let premise_range = match theorem_statement.claim.premise() {
                    Some(p) => p.range(),
                    None => theorem_statement.claim.range(),
                };
                (
                    Some(BlockPremise::new(left.to_arbitrary(), premise_range)),
                    right.to_arbitrary(),
                )
            }
            c => (None, c.to_arbitrary()),
        };

        let lambda_claim = AcornValue::lambda(arg_types, unbound_claim);
        let theorem_type = lambda_claim.get_type();
        if let Some(name_token) = &theorem_statement.name_token {
            let doc_comments = self.take_doc_comments();
            let name_range = name_token.range();
            self.bindings.add_unqualified_constant(
                name_token.text(),
                type_params.clone(),
                explicit_value_param_types(&local_family_params.value_params),
                theorem_type.clone(),
                Some(lambda_claim.clone()),
                None,
                doc_comments,
                Some(name_range),
                theorem_statement.statement_string(),
            );
        }

        let already_proven =
            theorem_statement.axiomatic || theorem_statement.trusted || is_citation;
        let source_name = theorem_statement
            .name_token
            .as_ref()
            .map(|t| t.text().to_string());
        let source = if theorem_statement.lemma {
            Source::lemma(self.module_id, range, self.depth, source_name)
        } else {
            Source::theorem(
                theorem_statement.axiomatic,
                self.module_id,
                range,
                true,
                self.depth,
                source_name,
            )
        };
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
                    theorem_statement.name_token.as_ref().map(|t| t.text()),
                    range,
                    premise,
                    goal,
                    theorem_statement.lemma,
                ),
                &statement.first_token,
                &statement.last_token,
                theorem_statement.body.as_ref(),
            )?;
            Node::block(project, self, block, Some(prop))
        };

        let index = self.add_node(node);
        self.add_node_lines(index, &statement.range());
        if is_citation {
            self.record_citation_statement(statement, cited_name, index);
        }
        if let Some(name_token) = &theorem_statement.name_token {
            let name = ConstantName::unqualified(self.module_id, name_token.text());
            self.bindings.mark_as_theorem(&name);
            if theorem_statement.lemma {
                self.hide_unqualified_name_from_export(name_token.text());
            }
        }

        Ok(())
    }

    pub(super) fn add_variable_satisfy_statement(
        &mut self,
        project: &dyn ProjectLookup,
        statement: &Statement,
        variable_satisfy_statement: &VariableSatisfyStatement,
    ) -> error::Result<()> {
        let module_id = self.module_id;
        self.add_variable_satisfy_statement_named(
            project,
            statement,
            variable_satisfy_statement,
            None,
            move |name| DefinedName::unqualified(module_id, name),
        )
    }

    pub(super) fn add_variable_satisfy_statement_named<F>(
        &mut self,
        project: &dyn ProjectLookup,
        statement: &Statement,
        variable_satisfy_statement: &VariableSatisfyStatement,
        datatype_params: Option<&DatatypeFamilyScope>,
        mut defined_name_for: F,
    ) -> error::Result<()>
    where
        F: FnMut(&str) -> DefinedName,
    {
        if self.depth > 0 && !variable_satisfy_statement.type_params.is_empty() {
            return Err(variable_satisfy_statement.declarations[0]
                .token()
                .error("parameterized constants may only be defined at the top level"));
        }

        let local_family_params = if datatype_params.is_some() {
            LocalFamilyParams {
                type_param_exprs: variable_satisfy_statement.type_params.clone(),
                type_params: self
                    .evaluator(project)
                    .evaluate_type_params(&variable_satisfy_statement.type_params)?,
                value_params: vec![],
                value_declarations: vec![],
            }
        } else {
            self.evaluate_local_family_params(project, &variable_satisfy_statement.type_params)?
        };
        let local_type_params = local_family_params.type_params.clone();
        for param in &local_type_params {
            self.bindings.add_arbitrary_type(param.clone());
        }

        let family_value_param_count = datatype_params
            .map(|params| params.value_params().len() as AtomId)
            .unwrap_or(0)
            + local_family_params.value_params.len() as AtomId;
        let explicit_value_param_types =
            explicit_value_param_types(&local_family_params.value_params);
        let result = (|| {
            for declaration in &variable_satisfy_statement.declarations {
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
            let (quant_names, quant_types) = no_token_evaluator.bind_args_may_shadow(
                &mut stack,
                &variable_satisfy_statement.declarations,
                None,
            )?;
            let mut general_claim_value = no_token_evaluator.evaluate_value_with_stack(
                &mut stack,
                &variable_satisfy_statement.condition,
                Some(&AcornType::Bool),
            )?;
            let mut local_obligations = no_token_evaluator.take_local_obligations();
            if local_obligations_need_result_spec_export(&local_obligations) {
                let mut stack = Stack::new();
                bind_explicit_value_params(&mut stack, &local_family_params.value_params);
                bind_datatype_value_params(&mut stack, datatype_params);
                let mut no_token_evaluator = Evaluator::new(project, &self.bindings, None);
                no_token_evaluator.bind_args_may_shadow(
                    &mut stack,
                    &variable_satisfy_statement.declarations,
                    None,
                )?;
                general_claim_value = no_token_evaluator.evaluate_result_spec_with_stack(
                    &mut stack,
                    &variable_satisfy_statement.condition,
                    AcornValue::Bool(true),
                    &AcornType::Bool,
                )?;
                local_obligations = no_token_evaluator.take_local_obligations();
            }
            let general_claim =
                AcornValue::Exists(quant_types.clone(), Box::new(general_claim_value.clone()));
            let definition_type_params = match datatype_params {
                Some(p) => {
                    if !local_type_params.is_empty() {
                        return Err(variable_satisfy_statement.declarations[0].token().error(
                            "datatype parameters and let parameters cannot be used together",
                        ));
                    }
                    p.type_params().to_vec()
                }
                None => local_type_params.clone(),
            };
            self.add_genericized_local_obligations(
                project,
                &definition_type_params,
                local_obligations,
            )?;
            let mut block_args = explicit_value_block_args(&local_family_params.value_params);
            block_args.extend(datatype_value_block_args(datatype_params));
            let block = Block::new(
                project,
                &self,
                vec![],
                block_args,
                BlockParams::variable_satisfy(
                    general_claim,
                    variable_satisfy_statement.condition.range(),
                ),
                &statement.first_token,
                &statement.last_token,
                None,
            )?;

            let mut constant_values = Vec::new();
            for ((declaration, quant_name), quant_type) in variable_satisfy_statement
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
                    AcornType::functional_from_promoted_ambient(
                        explicit_value_param_types.clone(),
                        generic_value_type.clone(),
                    )
                };
                let def_str = format!("{}: {}", quant_name, constant_type);
                let constant_value = self.declare_witness_constant(
                    &defined_name,
                    &definition_type_params,
                    quant_type,
                    &local_family_params.value_params,
                    datatype_params,
                    vec![],
                    declaration.token().range(),
                    def_str,
                    declaration.token(),
                    "let ... satisfy cannot define instance attributes",
                )?;
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
            Ok(())
        })();

        for param in local_type_params.iter().rev() {
            self.bindings.remove_type(&param.name);
        }

        result
    }

    pub(super) fn add_function_satisfy_statement(
        &mut self,
        project: &dyn ProjectLookup,
        statement: &Statement,
        function_satisfy_statement: &FunctionSatisfyStatement,
    ) -> error::Result<()> {
        let defined_name =
            DefinedName::unqualified(self.module_id, function_satisfy_statement.name_token.text());
        self.add_function_satisfy_statement_named(
            project,
            statement,
            function_satisfy_statement,
            defined_name,
            None,
        )
    }

    pub(super) fn add_function_satisfy_statement_named(
        &mut self,
        project: &dyn ProjectLookup,
        statement: &Statement,
        function_satisfy_statement: &FunctionSatisfyStatement,
        defined_name: DefinedName,
        datatype_params: Option<&DatatypeFamilyScope>,
    ) -> error::Result<()> {
        function_satisfy_statement.name_token.check_not_reserved()?;
        if self.bindings.constant_name_in_use(&defined_name) {
            return Err(function_satisfy_statement.name_token.error(&format!(
                "function name '{}' already defined in this scope",
                defined_name
            )));
        }

        let definition_range = Range {
            start: statement.first_token.start_pos(),
            end: function_satisfy_statement.satisfy_token.end_pos(),
        };

        if self.depth > 0 && !function_satisfy_statement.type_params.is_empty() {
            return Err(function_satisfy_statement
                .name_token
                .error("parameterized functions may only be defined at the top level"));
        }

        let recursion_name = defined_name.recursion_name();
        let local_family_params = if datatype_params.is_some() {
            LocalFamilyParams {
                type_param_exprs: function_satisfy_statement.type_params.clone(),
                type_params: self
                    .evaluator(project)
                    .evaluate_type_params(&function_satisfy_statement.type_params)?,
                value_params: vec![],
                value_declarations: vec![],
            }
        } else {
            self.evaluate_local_family_params(project, &function_satisfy_statement.type_params)?
        };
        let mut declarations = local_family_params.value_declarations.clone();
        declarations.extend(function_satisfy_statement.declarations.clone());
        let type_param_exprs = local_family_params.type_param_exprs.clone();
        let (mut fn_type_params, mut arg_names, mut arg_types, condition, _, mut local_obligations) =
            self.bindings.evaluate_scoped_value(
                &type_param_exprs,
                &declarations,
                None,
                &function_satisfy_statement.condition,
                None,
                recursion_name.as_ref(),
                defined_name.as_instance(),
                datatype_params.map(|params| params.type_params_slice()),
                datatype_params.map(|params| params.value_params_slice()),
                project,
                Some(&mut self.token_map),
            )?;
        let family_value_param_count = datatype_params
            .map(|params| params.value_params().len() as AtomId)
            .unwrap_or(0);
        let family_value_param_types = datatype_value_param_types(datatype_params);
        let explicit_value_param_types =
            explicit_value_param_types(&local_family_params.value_params);

        let mut unbound_condition =
            condition.ok_or_else(|| statement.error("missing condition"))?;
        if unbound_condition.get_type() != AcornType::Bool {
            return Err(function_satisfy_statement
                .condition
                .error("condition must be a boolean"));
        }
        if local_obligations_need_result_spec_export(&local_obligations) {
            let scoped_spec = self.bindings.evaluate_scoped_bool_result_spec(
                &type_param_exprs,
                &declarations,
                &function_satisfy_statement.condition,
                None,
                recursion_name.as_ref(),
                defined_name.as_instance(),
                datatype_params.map(|params| params.type_params_slice()),
                datatype_params.map(|params| params.value_params_slice()),
                project,
                None,
            )?;
            fn_type_params = scoped_spec.0;
            arg_names = scoped_spec.1;
            arg_types = scoped_spec.2;
            unbound_condition = scoped_spec.3;
            local_obligations = scoped_spec.4;
        }

        let _return_name = arg_names.pop().unwrap();
        let return_type = arg_types.pop().unwrap();
        let mut block_args = datatype_value_block_args(datatype_params);
        block_args.extend(arg_names.iter().cloned().zip(arg_types.iter().cloned()));
        let return_index = family_value_param_count + arg_types.len() as AtomId;
        let mut all_type_params = datatype_params
            .map(|params| params.type_params().to_vec())
            .unwrap_or_default();
        all_type_params.extend(fn_type_params.clone());
        self.add_local_obligations(project, &all_type_params, local_obligations)?;

        let block = Block::new(
            project,
            &self,
            fn_type_params.clone(),
            block_args,
            BlockParams::FunctionSatisfy(
                unbound_condition.clone(),
                return_type.clone(),
                function_satisfy_statement.condition.range(),
            ),
            &statement.first_token,
            &statement.last_token,
            function_satisfy_statement.body.as_ref(),
        )?;

        let function_type = AcornType::functional_from_scoped_context(
            arg_types.clone(),
            return_type,
            family_value_param_count,
        );
        let generic_function_type = function_type.clone().genericize(&all_type_params);
        let doc_comments = self.take_doc_comments();
        self.bindings.add_defined_name(
            &defined_name,
            all_type_params.clone(),
            if explicit_value_param_types.is_empty() {
                family_value_param_types.clone()
            } else {
                explicit_value_param_types.clone()
            },
            generic_function_type.clone(),
            None,
            None,
            doc_comments,
            Some(function_satisfy_statement.name_token.range()),
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
        let mut function_constant = AcornValue::constant(
            const_name,
            type_args,
            function_type.clone(),
            generic_function_type,
            vec![],
            if explicit_value_param_types.is_empty() {
                family_value_param_types.clone()
            } else {
                explicit_value_param_types.clone()
            },
        );
        if explicit_value_param_types.is_empty() && !family_value_param_types.is_empty() {
            let family_value_args = datatype_params
                .expect("family value params should have a datatype scope")
                .value_params()
                .iter()
                .enumerate()
                .map(|(i, value_param)| {
                    AcornValue::Variable(i as AtomId, value_param.value_type.clone())
                })
                .collect::<Vec<_>>();
            function_constant = function_constant
                .bind_value_params(&family_value_args, &function_satisfy_statement.name_token)?;
        }
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
        project: &dyn ProjectLookup,
        statement: &Statement,
        cs: &ClaimStatement,
    ) -> error::Result<()> {
        let mut evaluator = self.evaluator(project);
        let mut claim = evaluator.evaluate_value(&cs.claim, Some(&AcornType::Bool))?;
        let mut local_obligations = evaluator.take_local_obligations();
        if local_obligations_need_result_spec_export(&local_obligations) {
            let mut stack = Stack::new();
            let mut evaluator = Evaluator::new(project, &self.bindings, None);
            claim = evaluator.evaluate_result_spec_with_stack(
                &mut stack,
                &cs.claim,
                AcornValue::Bool(true),
                &AcornType::Bool,
            )?;
            local_obligations = evaluator.take_local_obligations();
        }
        self.add_local_obligations(project, &[], local_obligations)?;
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
        project: &dyn ProjectLookup,
        statement: &Statement,
        destructuring_statement: &DestructuringStatement,
    ) -> error::Result<()> {
        self.add_other_lines(statement);

        let mut arg_names = vec![];
        for arg_token in &destructuring_statement.args {
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

        let mut value_evaluator = self.evaluator(project);
        let value = value_evaluator.evaluate_value(&destructuring_statement.value, None)?;
        let mut value_local_obligations = value_evaluator.take_local_obligations();
        let value_type = value.get_type();

        let mut empty_stack = Stack::new();
        let mut function_evaluator = self.evaluator(project);
        let mut function = function_evaluator
            .evaluate_as_generic_value(&mut empty_stack, &destructuring_statement.function)?;
        let function_local_obligations = function_evaluator.take_local_obligations();

        let function_type_before = function.get_type();
        let function_ftype_before = match &function_type_before {
            AcornType::Function(ft) => ft,
            _ => {
                return Err(destructuring_statement.function.error(&format!(
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
                &destructuring_statement.value,
            )?;
        }

        let function_type = function.get_type();
        let (arg_types, return_type) = match &function_type {
            AcornType::Function(ft) => (ft.arg_types.clone(), ft.return_type.as_ref().clone()),
            _ => {
                return Err(destructuring_statement.function.error(&format!(
                    "expected a function type, but got {}",
                    function_type
                )));
            }
        };

        if arg_types.len() != destructuring_statement.args.len() {
            return Err(statement.error(&format!(
                "function expects {} arguments, but {} were provided in the pattern",
                arg_types.len(),
                destructuring_statement.args.len()
            )));
        }

        if return_type != value_type {
            return Err(destructuring_statement.value.error(&format!(
                "type mismatch: function returns {} but value has type {}",
                return_type, value_type
            )));
        }

        if arg_types.iter().any(|t| t.has_generic()) {
            return Err(destructuring_statement
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
        let mut general_condition = AcornValue::equals(general_applied.clone(), value.clone());
        if local_obligations_need_result_spec_export(&value_local_obligations) {
            let mut spec_evaluator = Evaluator::new(project, &self.bindings, None);
            general_condition = spec_evaluator.evaluate_result_spec_with_stack(
                &mut stack,
                &destructuring_statement.value,
                general_applied,
                &return_type,
            )?;
            value_local_obligations = spec_evaluator.take_local_obligations();
        }
        self.add_local_obligations(project, &[], value_local_obligations)?;
        self.add_local_obligations(project, &[], function_local_obligations)?;

        let specific_condition = general_condition.clone();
        let general_claim = AcornValue::Exists(quant_types.clone(), Box::new(general_condition));
        let source = Source::anonymous(self.module_id, statement.range(), self.depth);
        let general_prop = Proposition::new(general_claim.clone(), vec![], source);
        let node = if let Some(body) = &destructuring_statement.body {
            let block = Block::new(
                project,
                self,
                vec![],
                vec![],
                BlockParams::variable_satisfy(general_claim, destructuring_statement.value.range()),
                &statement.first_token,
                &statement.last_token,
                Some(body),
            )?;
            Node::block(project, self, block, Some(general_prop))
        } else {
            Node::claim(project, self, general_prop).map_err(|e| statement.error(&e))?
        };
        let index = self.add_node(node);
        self.add_node_lines(index, &statement.range());

        for (arg_token, arg_type) in destructuring_statement.args.iter().zip(&arg_types) {
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

        let arg_values: Vec<_> = destructuring_statement
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

        let specific_claim =
            specific_condition.bind_values(0, quant_names.len() as AtomId, &arg_values);
        let source = Source::anonymous(self.module_id, statement.range(), self.depth);
        let prop = Proposition::new(specific_claim, vec![], source);
        self.add_node(Node::structural(project, self, prop));

        Ok(())
    }
}

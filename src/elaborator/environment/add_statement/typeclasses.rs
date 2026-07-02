use super::*;

impl Environment {
    pub(super) fn add_typeclass_statement(
        &mut self,
        project: &dyn ProjectLookup,
        statement: &Statement,
        typeclass_statement: &TypeclassStatement,
    ) -> error::Result<()> {
        self.add_other_lines(statement);

        let mut extends = vec![];
        for extend in &typeclass_statement.extends {
            let typeclass = self.evaluator(project).evaluate_typeclass(extend)?;
            extends.push(typeclass);
        }

        let typeclass_name = typeclass_statement.typeclass_name.text();
        self.bindings
            .check_typename_available(typeclass_name, statement)?;
        let typeclass = Typeclass {
            module_id: self.module_id,
            name: typeclass_name.to_string(),
        };
        let doc_comments = self.take_doc_comments();
        let definition_string = Some(statement.to_string());
        self.bindings.add_typeclass(
            typeclass_name,
            extends,
            doc_comments,
            Some(typeclass_statement.typeclass_name.range()),
            definition_string,
            project,
            &typeclass_statement.typeclass_name,
        )?;

        let type_params = if let Some(instance_name_token) = &typeclass_statement.instance_name {
            let instance_name = instance_name_token.text();
            self.bindings
                .check_typename_available(instance_name, statement)?;
            let type_param = TypeParam {
                name: instance_name.to_string(),
                typeclass: Some(typeclass.clone()),
            };
            self.bindings.add_arbitrary_type(type_param.clone());
            vec![type_param.clone()]
        } else {
            vec![]
        };

        let mut inhabitant_provider = None;
        if !type_params.is_empty() {
            let type_param = &type_params[0];
            for (attr_name, type_expr, doc_comments) in &typeclass_statement.constants {
                if let Some(existing_tc) = self
                    .bindings
                    .cached_typeclass_attr_lookup(&typeclass, attr_name.text())
                {
                    return Err(attr_name.error(&format!(
                        "attribute '{}' is already defined via base typeclass '{}'",
                        attr_name.text(),
                        existing_tc.name
                    )));
                }
                let arb_type = self.evaluator(project).evaluate_type(type_expr)?;
                let var_type = arb_type.genericize(&type_params);

                let defined_name = DefinedName::typeclass_attr(&typeclass, attr_name.text());
                self.bindings
                    .check_defined_name_available(&defined_name, attr_name)?;
                let def_str = format!("{}: {}", attr_name.text(), type_expr);
                let potential = self.bindings.add_typeclass_attribute(
                    &typeclass,
                    &attr_name.text(),
                    vec![type_param.clone()],
                    vec![],
                    var_type,
                    None,
                    None,
                    doc_comments.clone(),
                    def_str,
                );
                self.bindings
                    .mark_typeclass_attr_required(&typeclass, &attr_name.text());

                if inhabitant_provider.is_none() {
                    if let AcornType::Variable(tp) = potential.get_type() {
                        if tp.name == type_param.name {
                            inhabitant_provider = Some(potential);
                        }
                    }
                }
            }
        }

        if let Some(extends_set) = self.bindings.get_extends_set(&typeclass) {
            let source = Source {
                module_id: self.module_id,
                range: statement.range(),
                source_type: SourceType::Extends(typeclass_name.to_string()),
                importable: true,
                depth: self.depth,
            };
            let extends_fact = Fact::Extends(
                typeclass.clone(),
                extends_set.clone(),
                inhabitant_provider,
                source,
            );
            self.add_node(Node::Structural(extends_fact));
        }

        if !type_params.is_empty() {
            let type_param = &type_params[0];
            for condition in &typeclass_statement.conditions {
                let range = Range {
                    start: condition.name_token.start_pos(),
                    end: condition.claim.last_token().end_pos(),
                };
                let defined_name =
                    DefinedName::typeclass_attr(&typeclass, &condition.name_token.text());
                self.bindings
                    .check_defined_name_available(&defined_name, &condition.name_token)?;

                let (mut bad_params, _, mut arg_types, unbound_claim, _, mut local_obligations) =
                    self.bindings.evaluate_scoped_value(
                        &[],
                        &condition.args,
                        None,
                        &condition.claim,
                        None,
                        None,
                        None,
                        None,
                        None,
                        project,
                        Some(&mut self.token_map),
                    )?;
                if !bad_params.is_empty() {
                    return Err(condition
                        .name_token
                        .error("type parameters are not allowed here"));
                }
                let mut unbound_claim = unbound_claim
                    .ok_or_else(|| condition.claim.error("conditions must have values"))?;
                if local_obligations_need_result_spec_export(&local_obligations) {
                    let scoped_spec = self.bindings.evaluate_scoped_bool_result_spec(
                        &[],
                        &condition.args,
                        &condition.claim,
                        None,
                        None,
                        None,
                        None,
                        None,
                        project,
                        None,
                    )?;
                    bad_params = scoped_spec.0;
                    if !bad_params.is_empty() {
                        return Err(condition
                            .name_token
                            .error("type parameters are not allowed here"));
                    }
                    arg_types = scoped_spec.2;
                    unbound_claim = scoped_spec.3;
                    local_obligations = scoped_spec.4;
                }
                let external_claim = AcornValue::forall(arg_types.clone(), unbound_claim.clone())
                    .genericize(&type_params);
                if let Err(message) = external_claim.validate() {
                    return Err(condition.claim.error(&message));
                }
                self.add_genericized_local_obligations(project, &type_params, local_obligations)?;
                let lambda_claim = AcornValue::lambda(arg_types.clone(), unbound_claim.clone())
                    .genericize(&type_params);
                let theorem_type = lambda_claim.get_type();
                self.bindings.add_typeclass_attribute(
                    &typeclass,
                    &condition.name_token.text(),
                    type_params.clone(),
                    vec![],
                    theorem_type.clone(),
                    Some(lambda_claim),
                    None,
                    condition.doc_comments.clone(),
                    condition.to_string(),
                );

                let source = Source::type_definition(
                    self.module_id,
                    range,
                    self.depth,
                    typeclass.name.clone(),
                    condition.name_token.text().to_string(),
                );
                let prop = Proposition::new(external_claim, vec![type_param.clone()], source);
                self.add_node(Node::structural(project, self, prop));
                let constant_name = ConstantName::typeclass_attr(
                    self.module_id,
                    typeclass.clone(),
                    &condition.name_token.text(),
                );
                self.bindings.mark_as_theorem(&constant_name);
            }
        }

        if let Some(instance_name_token) = &typeclass_statement.instance_name {
            self.bindings.remove_type(instance_name_token.text());
        }
        Ok(())
    }

    pub(super) fn add_instance_statement(
        &mut self,
        project: &dyn ProjectLookup,
        statement: &Statement,
        instance_statement: &InstanceStatement,
    ) -> error::Result<()> {
        let typeclass = self
            .evaluator(project)
            .evaluate_typeclass(&instance_statement.typeclass)?;

        let (instance_type, instance_datatype, family_scope, family_value_args) =
            if instance_statement.type_params.is_empty() {
                let type_expr = Expression::Singleton(instance_statement.type_name.clone());
                let instance_type = self.evaluator(project).evaluate_type(&type_expr)?;
                let instance_datatype = self
                    .check_can_add_attributes(&instance_statement.type_name, &instance_type)?
                    .clone();
                (
                    instance_type,
                    instance_datatype,
                    DatatypeFamilyScope::default(),
                    vec![],
                )
            } else {
                let potential = self
                    .bindings
                    .get_type_for_typename(instance_statement.type_name.text())
                    .cloned()
                    .ok_or_else(|| instance_statement.type_name.error("expected type name"))?;
                let Some(unresolved) = potential.as_unresolved() else {
                    return Err(instance_statement
                        .type_name
                        .error("instance parameters require a parameterized datatype"));
                };
                let Some(datatype) = unresolved.base_datatype().cloned() else {
                    return Err(instance_statement
                        .type_name
                        .error("instance parameters require a datatype family"));
                };
                let expected_kinds = self
                    .bindings
                    .get_datatype_family_param_kinds(&datatype)
                    .unwrap_or(&[])
                    .to_vec();
                let family_params = self
                    .evaluator(project)
                    .evaluate_family_params(&instance_statement.type_params)?;
                if family_params.len() != expected_kinds.len() {
                    return Err(instance_statement.type_name.error(&format!(
                        "type {} expects {} parameters, but got {}",
                        instance_statement.type_name.text(),
                        expected_kinds.len(),
                        family_params.len()
                    )));
                }
                let family_param_kinds = family_params.canonical_kinds();
                for (expr, ((param, param_kind), expected_kind)) in
                    instance_statement.type_params.iter().zip(
                        family_params
                            .iter()
                            .zip(&family_param_kinds)
                            .zip(expected_kinds.iter()),
                    )
                {
                    match (param, param_kind, expected_kind) {
                        (
                            FamilyParam::Type(type_param),
                            FamilyParamKind::Type(_),
                            FamilyParamKind::Type(expected),
                        ) if expected.is_none() || &type_param.typeclass == expected => {}
                        (
                            FamilyParam::Value(_),
                            FamilyParamKind::Value(value_type),
                            FamilyParamKind::Value(expected_type),
                        ) if value_type == expected_type => {}
                        (
                            FamilyParam::Type(_),
                            FamilyParamKind::Type(_),
                            FamilyParamKind::Value(expected_type),
                        ) => {
                            return Err(expr.name.error(&format!(
                                "expected a dependent value parameter like '{}: {}'",
                                expr.name.text(),
                                expected_type
                            )));
                        }
                        (
                            FamilyParam::Value(_),
                            FamilyParamKind::Value(_),
                            FamilyParamKind::Type(_),
                        ) => {
                            return Err(expr
                                .name
                                .error("expected a type parameter here, not a value parameter"));
                        }
                        _ => {
                            return Err(expr
                                .name
                                .error("instance parameter kind does not match datatype"));
                        }
                    }
                }
                for (expr, family_param) in
                    instance_statement.type_params.iter().zip(&family_params)
                {
                    if let Some(type_param) = family_param.as_type_param() {
                        self.bindings
                            .check_typename_available(&type_param.name, &expr.name)?;
                    }
                }

                let family_scope = DatatypeFamilyScope::new(family_params.clone());
                let mut arbitrary_type_args = vec![];
                for param in family_scope.type_params() {
                    arbitrary_type_args.push(self.bindings.add_arbitrary_type(param.clone()));
                }
                let (family_args, family_value_args) =
                    family_params.family_args_for_type_args(&arbitrary_type_args);
                let instance_type =
                    potential.resolve_args(family_args, &instance_statement.type_name)?;
                let instance_datatype = self
                    .check_can_add_attributes(&instance_statement.type_name, &instance_type)?
                    .clone();
                (
                    instance_type,
                    instance_datatype,
                    family_scope,
                    family_value_args,
                )
            };

        let family_type_args: Vec<_> = family_scope
            .type_params()
            .iter()
            .map(|param| AcornType::Arbitrary(param.clone()))
            .collect();

        for base_typeclass in self.bindings.get_extends(&typeclass) {
            if !self
                .bindings
                .is_instance_of_type(&instance_type, &base_typeclass)
            {
                return Err(statement.error(&format!(
                    "'{}' must be an instance of '{}' in order to be an instance of '{}'",
                    instance_statement.type_name, base_typeclass.name, typeclass.name
                )));
            }
        }

        let mut pairs = vec![];
        let public_definition_for_instance =
            |bindings: &crate::elaborator::binding_map::BindingMap,
             attr_name: &str|
             -> Option<AcornValue> {
                let name =
                    DefinedName::instance(typeclass.clone(), attr_name, instance_datatype.clone());
                let definition = bindings.get_definition(&name)?.clone();
                if family_value_args.is_empty() {
                    return Some(definition);
                }
                let generic_family_value_args: Vec<_> = family_value_args
                    .iter()
                    .map(|value| value.genericize(family_scope.type_params()))
                    .collect();
                Some(
                    AcornValue::apply(definition, generic_family_value_args)
                        .expand_lambdas(family_scope.value_params().len() as AtomId),
                )
            };

        if let Some(definitions) = &instance_statement.definitions {
            for substatement in &definitions.statements {
                match &substatement.statement {
                    StatementInfo::Let(let_statement) => {
                        let attr_name = let_statement.name_token.text().to_string();
                        self.add_let_statement(
                            project,
                            substatement,
                            DefinedName::instance(
                                typeclass.clone(),
                                &attr_name,
                                instance_datatype.clone(),
                            ),
                            let_statement,
                            let_statement.name_token.range(),
                            if instance_statement.type_params.is_empty() {
                                None
                            } else {
                                Some(&family_scope)
                            },
                        )?;

                        let (public_attr, instance_impl) = self.bindings.check_instance_attribute(
                            &instance_type,
                            &typeclass,
                            &attr_name,
                            family_scope.type_params(),
                            &family_value_args,
                            project,
                            substatement,
                        )?;
                        let public_definition =
                            public_definition_for_instance(&self.bindings, &attr_name);
                        pairs.push((public_attr, instance_impl, public_definition));
                    }
                    StatementInfo::Define(define_statement) => {
                        if !define_statement.type_params.is_empty() {
                            return Err(substatement.error("type parameters are not allowed here"));
                        }
                        let attr_name = define_statement.name_token.text().to_string();
                        self.add_define_statement(
                            project,
                            substatement,
                            DefinedName::instance(
                                typeclass.clone(),
                                &attr_name,
                                instance_datatype.clone(),
                            ),
                            Some(&instance_type),
                            if instance_statement.type_params.is_empty() {
                                None
                            } else {
                                Some(&family_scope)
                            },
                            define_statement,
                            define_statement.name_token.range(),
                        )?;

                        let (public_attr, instance_impl) = self.bindings.check_instance_attribute(
                            &instance_type,
                            &typeclass,
                            &attr_name,
                            family_scope.type_params(),
                            &family_value_args,
                            project,
                            substatement,
                        )?;
                        let public_definition =
                            public_definition_for_instance(&self.bindings, &attr_name);
                        pairs.push((public_attr, instance_impl, public_definition));
                    }
                    _ => {
                        return Err(substatement.error(
                            "only let and define statements are allowed in instance bodies",
                        ));
                    }
                }
            }
        }

        let attributes = self.bindings.get_typeclass_attributes(&typeclass, project);
        let mut conditions = vec![];
        let mut defaults_to_add = vec![];

        for (attr_name, (_module_id, root_tc)) in attributes.iter() {
            if root_tc != &typeclass {
                continue;
            }

            let tc_attr_name =
                ConstantName::typeclass_attr(typeclass.module_id, typeclass.clone(), attr_name);
            let tc_bindings = self.bindings.get_bindings(typeclass.module_id, project);
            if tc_bindings.is_theorem(&tc_attr_name) {
                let unsafe_condition = self.bindings.unsafe_instantiate_condition(
                    &typeclass,
                    &attr_name,
                    &instance_type,
                    family_scope.value_params().len() as AtomId,
                    project,
                    statement,
                )?;
                let family_value_stack_size = family_scope.value_params().len() as AtomId;
                let condition = unsafe_condition.replace_constants_with_base_stack(
                    family_value_stack_size,
                    family_value_stack_size,
                    &|ci| {
                        let name = match ci.to_defined_instance_name(&typeclass, &instance_datatype)
                        {
                            Some(name) => name,
                            None => return None,
                        };
                        let definition = self.bindings.get_definition(&name)?.clone();
                        let replacements: Vec<_> = family_scope
                            .type_params()
                            .iter()
                            .cloned()
                            .zip(family_type_args.iter().cloned())
                            .map(|(param, arg)| (param.name, arg))
                            .collect();
                        let definition = definition
                            .instantiate_with_ambient_stack(family_value_stack_size, &replacements);
                        if family_value_args.is_empty() {
                            Some(definition)
                        } else {
                            Some(
                                AcornValue::apply(definition, family_value_args.clone())
                                    .expand_lambdas(family_value_stack_size),
                            )
                        }
                    },
                );
                conditions.push(condition);
                continue;
            }

            if !self
                .bindings
                .is_typeclass_attr_required(&typeclass, attr_name)
            {
                continue;
            }

            let name =
                DefinedName::instance(typeclass.clone(), attr_name, instance_datatype.clone());
            if !self.bindings.constant_name_in_use(&name) {
                if self.bindings.has_type_attr(&instance_datatype, attr_name) {
                    let defining_module = self
                        .bindings
                        .get_module_for_datatype_attr(&instance_datatype, attr_name)
                        .expect("has_type_attr should imply module exists");
                    let datatype_attr_name = DefinedName::datatype_attr_defined(
                        defining_module,
                        &instance_datatype,
                        attr_name,
                    );
                    let tc_attr_name = DefinedName::typeclass_attr(&typeclass, attr_name);
                    let tc_attr = self
                        .bindings
                        .get_constant_value(&tc_attr_name)
                        .map_err(|e| statement.error(&e))?;
                    let tc_unresolved = tc_attr.to_unresolved(statement)?;
                    let tc_resolved =
                        tc_unresolved.resolve(statement, vec![instance_type.clone()])?;
                    let tc_resolved = tc_resolved.genericize(family_scope.type_params());
                    let tc_type = tc_resolved.get_type();

                    let dt_attr = self
                        .bindings
                        .get_constant_value(&datatype_attr_name)
                        .map_err(|e| statement.error(&e))?;
                    let dt_value = dt_attr.resolve_constant_with_datatype_args(
                        &family_type_args,
                        &family_value_args,
                        statement,
                    )?;
                    let dt_value = dt_value.genericize(family_scope.type_params());
                    let dt_type = dt_value.get_type();

                    if tc_type != dt_type {
                        return Err(statement.error(&format!(
                            "type mismatch for attribute '{}': typeclass expects {}, but datatype has {}",
                            attr_name, tc_type, dt_type
                        )));
                    }

                    defaults_to_add.push((name, tc_type, dt_value.clone(), tc_resolved));
                } else {
                    return Err(statement
                        .error(&format!("missing implementation for attribute '{}'", name)));
                }
            }
        }

        for (name, tc_type, dt_value, tc_resolved) in defaults_to_add {
            let public_definition = dt_value.clone();
            let definition = if family_value_args.is_empty() {
                dt_value
            } else {
                AcornValue::lambda(
                    family_scope
                        .value_params()
                        .iter()
                        .map(|param| param.value_type.clone())
                        .collect(),
                    dt_value,
                )
            };
            self.define_constant(
                name.clone(),
                family_scope.type_params().to_vec(),
                family_scope
                    .value_params()
                    .iter()
                    .map(|param| param.value_type.clone())
                    .collect(),
                tc_type,
                Some(definition),
                statement.range(),
                None,
            );
            let instance_impl = self
                .bindings
                .get_constant_value(&name)
                .map_err(|e| statement.error(&e))?
                .resolve_constant_with_datatype_args(
                    &family_type_args,
                    &family_value_args,
                    statement,
                )?
                .genericize(family_scope.type_params());
            pairs.push((tc_resolved, instance_impl, Some(public_definition)));
        }

        let instance_source = Source::instance(
            self.module_id,
            statement.range(),
            self.depth,
            instance_statement.type_name.text(),
            &typeclass.name,
        );
        let typeclass_instance = TypeclassInstance {
            instance_type: instance_type.clone().genericize(family_scope.type_params()),
            datatype: instance_datatype.clone(),
            family_params: family_scope.clone_telescope(),
            typeclass: typeclass.clone(),
        };
        let instance_fact = Fact::Instance(typeclass_instance.clone(), instance_source.clone());

        let range = Range {
            start: statement.first_token.start_pos(),
            end: if let Some(definitions) = &instance_statement.definitions {
                definitions.right_brace.end_pos()
            } else {
                statement.last_token.end_pos()
            },
        };
        let node = self.requirement_backed_fact_node(
            project,
            statement,
            family_scope.type_params().to_vec(),
            family_scope.value_block_args(),
            conditions,
            range,
            instance_statement.body.as_ref(),
            instance_fact,
        )?;

        for type_param in family_scope.type_params() {
            self.bindings.remove_type(&type_param.name);
        }
        let index = self.add_node(node);
        self.add_node_lines(index, &statement.range());
        self.bindings.add_typeclass_instance(typeclass_instance);

        for (public_attr, instance_impl, public_definition) in pairs {
            let bridge = if family_scope.is_empty() {
                Node::definition(
                    PotentialValue::Resolved(public_attr),
                    instance_impl,
                    instance_source.clone(),
                )
            } else {
                let definition = public_definition.unwrap_or(instance_impl);
                let mut claim = public_attr.inflate_function_definition(definition);
                let value_param_types: Vec<_> = family_scope
                    .value_params()
                    .iter()
                    .map(|param| param.value_type.genericize(family_scope.type_params()))
                    .collect();
                if !value_param_types.is_empty() {
                    claim = AcornValue::ForAll(value_param_types, Box::new(claim));
                }
                let prop = Proposition::new(
                    claim,
                    family_scope.type_params().to_vec(),
                    instance_source.clone(),
                );
                Node::Structural(Fact::Proposition(Arc::new(prop)))
            };
            let index = self.add_node(bridge);
            self.add_node_lines(index, &statement.range());
        }
        Ok(())
    }
}

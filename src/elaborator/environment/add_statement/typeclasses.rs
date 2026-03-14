use super::*;

impl Environment {
    pub(super) fn add_typeclass_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        ts: &TypeclassStatement,
    ) -> error::Result<()> {
        self.add_other_lines(statement);

        let mut extends = vec![];
        for extend in &ts.extends {
            let typeclass = self.evaluator(project).evaluate_typeclass(extend)?;
            extends.push(typeclass);
        }

        let typeclass_name = ts.typeclass_name.text();
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
            Some(ts.typeclass_name.range()),
            definition_string,
            &project,
            &ts.typeclass_name,
        )?;

        let type_params = if let Some(instance_name_token) = &ts.instance_name {
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
            for (attr_name, type_expr, doc_comments) in &ts.constants {
                if let Some(existing_tc) = self
                    .bindings
                    .typeclass_attr_lookup(&typeclass, attr_name.text())
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
            self.add_node(Node::Structural(extends_fact, None));
        }

        if !type_params.is_empty() {
            let type_param = &type_params[0];
            for condition in &ts.conditions {
                let range = Range {
                    start: condition.name_token.start_pos(),
                    end: condition.claim.last_token().end_pos(),
                };
                let defined_name =
                    DefinedName::typeclass_attr(&typeclass, &condition.name_token.text());
                self.bindings
                    .check_defined_name_available(&defined_name, &condition.name_token)?;

                let (bad_params, _, arg_types, unbound_claim, _) =
                    self.bindings.evaluate_scoped_value(
                        &[],
                        &condition.args,
                        None,
                        &condition.claim,
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
                let unbound_claim = unbound_claim
                    .ok_or_else(|| condition.claim.error("conditions must have values"))?;
                let external_claim = AcornValue::forall(arg_types.clone(), unbound_claim.clone())
                    .genericize(&type_params);
                if let Err(message) = external_claim.validate() {
                    return Err(condition.claim.error(&message));
                }
                let lambda_claim = AcornValue::lambda(arg_types.clone(), unbound_claim.clone())
                    .genericize(&type_params);
                let theorem_type = lambda_claim.get_type();
                self.bindings.add_typeclass_attribute(
                    &typeclass,
                    &condition.name_token.text(),
                    type_params.clone(),
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

        if let Some(instance_name_token) = &ts.instance_name {
            self.bindings.remove_type(instance_name_token.text());
        }
        Ok(())
    }

    pub(super) fn add_instance_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        is: &InstanceStatement,
    ) -> error::Result<()> {
        let type_expr = Expression::Singleton(is.type_name.clone());
        let instance_type = self.evaluator(project).evaluate_type(&type_expr)?;
        let instance_datatype = self.check_can_add_attributes(&is.type_name, &instance_type)?;
        let typeclass = self.evaluator(project).evaluate_typeclass(&is.typeclass)?;

        for base_typeclass in self.bindings.get_extends(&typeclass) {
            if !self
                .bindings
                .is_instance_of(&instance_datatype, &base_typeclass)
            {
                return Err(statement.error(&format!(
                    "'{}' must be an instance of '{}' in order to be an instance of '{}'",
                    is.type_name, base_typeclass.name, typeclass.name
                )));
            }
        }

        let mut pairs = vec![];

        if let Some(definitions) = &is.definitions {
            for substatement in &definitions.statements {
                match &substatement.statement {
                    StatementInfo::Let(ls) => {
                        self.add_let_statement(
                            project,
                            substatement,
                            DefinedName::instance(
                                typeclass.clone(),
                                ls.name_token.text(),
                                instance_datatype.clone(),
                            ),
                            ls,
                            ls.name_token.range(),
                            None,
                        )?;

                        pairs.push(self.bindings.check_instance_attribute(
                            &instance_type,
                            &typeclass,
                            ls.name_token.text(),
                            &project,
                            substatement,
                        )?);
                    }
                    StatementInfo::Define(ds) => {
                        if !ds.type_params.is_empty() {
                            return Err(substatement.error("type parameters are not allowed here"));
                        }
                        self.add_define_statement(
                            project,
                            substatement,
                            DefinedName::instance(
                                typeclass.clone(),
                                ds.name_token.text(),
                                instance_datatype.clone(),
                            ),
                            Some(&instance_type),
                            None,
                            ds,
                            ds.name_token.range(),
                        )?;

                        pairs.push(self.bindings.check_instance_attribute(
                            &instance_type,
                            &typeclass,
                            ds.name_token.text(),
                            &project,
                            substatement,
                        )?);
                    }
                    _ => {
                        return Err(substatement.error(
                            "only let and define statements are allowed in instance bodies",
                        ));
                    }
                }
            }
        }

        let attributes = self.bindings.get_typeclass_attributes(&typeclass, &project);
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
                    project,
                    statement,
                )?;
                let condition = unsafe_condition.replace_constants(0, &|ci| {
                    let name = match ci.to_defined_instance_name(&typeclass, &instance_datatype) {
                        Some(name) => name,
                        None => return None,
                    };
                    self.bindings.get_definition(&name).cloned()
                });
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
                    let tc_type = tc_resolved.get_type();

                    let dt_attr = self
                        .bindings
                        .get_constant_value(&datatype_attr_name)
                        .map_err(|e| statement.error(&e))?;
                    let dt_value = dt_attr.as_value(statement)?;
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
            self.define_constant(
                name.clone(),
                vec![],
                tc_type,
                Some(dt_value),
                statement.range(),
                None,
            );
            let instance_impl = self
                .bindings
                .get_constant_value(&name)
                .map_err(|e| statement.error(&e))?
                .as_value(statement)?;
            pairs.push((tc_resolved, instance_impl));
        }

        let instance_source = Source::instance(
            self.module_id,
            statement.range(),
            self.depth,
            is.type_name.text(),
            &typeclass.name,
        );
        let instance_fact = Fact::Instance(
            instance_datatype.clone(),
            typeclass.clone(),
            instance_source.clone(),
        );

        let node = if conditions.is_empty() {
            Node::Structural(instance_fact, None)
        } else {
            let range = Range {
                start: statement.first_token.start_pos(),
                end: if let Some(definitions) = &is.definitions {
                    definitions.right_brace.end_pos()
                } else {
                    statement.last_token.end_pos()
                },
            };
            let block_params = BlockParams::TypeRequirement(conditions, range);
            let block = Block::new(
                project,
                &self,
                vec![],
                vec![],
                block_params,
                &statement.first_token,
                &statement.last_token,
                is.body.as_ref(),
            )?;
            Node::Block(block, Some(instance_fact), None)
        };

        let index = self.add_node(node);
        self.add_node_lines(index, &statement.range());
        self.bindings
            .add_instance_of(instance_datatype.clone(), typeclass);

        for (public_attr, instance_impl) in pairs {
            let bridge = Node::definition(
                PotentialValue::Resolved(public_attr),
                instance_impl,
                instance_source.clone(),
            );
            let index = self.add_node(bridge);
            self.add_node_lines(index, &statement.range());
        }
        Ok(())
    }
}

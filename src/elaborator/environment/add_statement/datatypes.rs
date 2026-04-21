use super::*;

impl Environment {
    pub(super) fn add_structure_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        ss: &StructureStatement,
    ) -> error::Result<()> {
        self.add_line_types(
            LineType::Other,
            statement.first_line(),
            ss.first_right_brace.line_number,
        );
        self.bindings
            .check_typename_available(ss.name_token.text(), statement)?;

        let mut arbitrary_params = vec![];
        let type_params = self
            .evaluator(project)
            .evaluate_type_params(&ss.type_params)?;
        for type_param in &type_params {
            arbitrary_params.push(self.bindings.add_arbitrary_type(type_param.clone()));
        }

        let mut member_fn_names = vec![];
        let mut field_types = vec![];
        let mut field_doc_comments = vec![];
        for (field_name_token, field_type_expr, doc_comments) in &ss.fields {
            let field_type = self.evaluator(project).evaluate_type(field_type_expr)?;
            field_types.push(field_type.clone());
            if TokenType::is_magic_method_name(&field_name_token.text())
                && field_name_token.text() != "contains"
                && field_name_token.text() != "not_contains"
            {
                return Err(field_name_token.error(&format!(
                    "'{}' is a reserved word. use a different name",
                    field_name_token.text()
                )));
            }
            member_fn_names.push(field_name_token.text());
            field_doc_comments.push(doc_comments.clone());
        }

        let variances = type_params
            .iter()
            .map(|param| {
                let mut combined = Variance::None;
                for field_type in &field_types {
                    combined = combined.merge(field_type.compute_variance_with_lookup(
                        param,
                        true,
                        &|dt| self.bindings.get_datatype_variances(dt),
                    ));
                }
                combined
            })
            .collect::<Vec<_>>();

        let unbound_constraint = if let Some(constraint) = &ss.constraint {
            let mut stack = Stack::new();
            for ((name_token, _, _), t) in ss.fields.iter().zip(&field_types) {
                stack.insert(name_token.to_string(), t.clone());
            }
            let unbound = self.evaluator(project).evaluate_value_with_stack(
                &mut stack,
                constraint,
                Some(&AcornType::Bool),
            )?;
            let inhabited = AcornValue::Exists(field_types.clone(), Box::new(unbound.clone()));
            let block_params = BlockParams::TypeRequirement(vec![inhabited], constraint.range());

            let block = Block::new(
                project,
                &self,
                vec![],
                vec![],
                block_params,
                &statement.first_token,
                &statement.last_token,
                ss.body.as_ref(),
            )?;
            let index = self.add_node(Node::block(project, self, block, None));
            self.add_node_lines(index, &statement.range());
            Some(unbound)
        } else {
            None
        };

        let datatype = Datatype {
            module_id: self.module_id,
            name: ss.name_token.text().to_string(),
        };
        let typeclasses = type_params.iter().map(|tp| tp.typeclass.clone()).collect();
        let doc_comments = self.take_doc_comments();
        let definition_string = Some(statement.to_string());
        let potential_type = self.bindings.add_potential_type(
            &ss.name_token,
            typeclasses,
            doc_comments,
            Some(ss.name_token.range()),
            definition_string,
        );
        self.bindings.set_datatype_variances(&datatype, variances);
        self.bindings
            .set_datatype_arity(&datatype, type_params.len() as u8);
        let struct_type = potential_type.resolve(arbitrary_params, &ss.name_token)?;
        let mut member_fns = vec![];
        for ((member_fn_name, field_type), doc_comments) in member_fn_names
            .into_iter()
            .zip(&field_types)
            .zip(&field_doc_comments)
        {
            let member_fn_type =
                AcornType::functional(vec![struct_type.clone()], field_type.clone());
            let def_str = format!(
                "{}.{}: {}",
                ss.name_token.text(),
                member_fn_name,
                member_fn_type
            );
            let potential = self.bindings.add_datatype_attribute(
                &datatype,
                member_fn_name,
                type_params.clone(),
                member_fn_type.genericize(&type_params),
                None,
                None,
                doc_comments.clone(),
                def_str,
            );
            member_fns.push(potential);
        }

        let bind_new = unbound_constraint.is_none() || !cfg!(feature = "ncn");
        let new_fn = if bind_new {
            let new_fn_type = AcornType::functional(field_types.clone(), struct_type.clone());
            let constructor_info = ConstructorInfo {
                datatype: datatype.clone(),
                index: 0,
                total: 1,
            };
            let def_str = format!("{}.new: {}", ss.name_token.text(), new_fn_type);
            Some(self.bindings.add_datatype_attribute(
                &datatype,
                "new",
                type_params.clone(),
                new_fn_type.genericize(&type_params),
                None,
                Some(constructor_info),
                vec![],
                def_str,
            ))
        } else {
            None
        };
        let object_var = AcornValue::Variable(0, struct_type.clone());
        let mut member_args = vec![];
        for (i, member_fn) in member_fns.iter().enumerate() {
            let member_arg = self.bindings.apply_potential(
                member_fn.clone(),
                vec![object_var.clone()],
                None,
                &ss.fields[i].0,
            )?;
            member_args.push(member_arg);
        }
        let range = Range {
            start: statement.first_token.start_pos(),
            end: ss.name_token.end_pos(),
        };

        let constraint_fn = if let Some(unbound_constraint) = &unbound_constraint {
            let constraint_fn_type = AcornType::functional(field_types.clone(), AcornType::Bool);
            let def_str = format!(
                "{}.constraint: {}",
                ss.name_token.text(),
                constraint_fn_type
            );
            let constraint_fn = self.bindings.add_datatype_attribute(
                &datatype,
                "constraint",
                type_params.clone(),
                constraint_fn_type.genericize(&type_params),
                None,
                None,
                vec![],
                def_str,
            );

            let constraint_args = (0..ss.fields.len())
                .map(|i| AcornValue::Variable(i as AtomId, field_types[i].clone()))
                .collect::<Vec<_>>();
            let constraint_application = self.bindings.apply_potential(
                constraint_fn.clone(),
                constraint_args,
                Some(&AcornType::Bool),
                &ss.name_token,
            )?;
            let constraint_eq =
                AcornValue::equals(constraint_application, unbound_constraint.clone());
            let constraint_eq_claim =
                AcornValue::ForAll(field_types.clone(), Box::new(constraint_eq))
                    .genericize(&type_params);
            let source = Source::type_definition(
                self.module_id,
                range,
                self.depth,
                ss.name_token.text().to_string(),
                "constraint".to_string(),
            );
            let prop = Proposition::new(constraint_eq_claim, type_params.clone(), source);
            self.add_node(Node::structural(project, self, prop));
            Some(constraint_fn)
        } else {
            None
        };

        if let Some(unbound_constraint) = &unbound_constraint {
            let c = unbound_constraint.clone().insert_stack(0, 1);
            let partially_bound = c.bind_values(1, 1, &member_args);
            let constraint_claim =
                AcornValue::ForAll(vec![struct_type.clone()], Box::new(partially_bound))
                    .genericize(&type_params);
            let source = Source::type_definition(
                self.module_id,
                range,
                self.depth,
                ss.name_token.text().to_string(),
                "constraint".to_string(),
            );
            let prop = Proposition::new(constraint_claim, type_params.clone(), source);
            self.add_node(Node::structural(project, self, prop));
        }

        if let Some(new_fn) = &new_fn {
            let recreated = self.bindings.apply_potential(
                new_fn.clone(),
                member_args.clone(),
                None,
                &ss.name_token,
            )?;
            let new_eq = AcornValue::Binary(
                BinaryOp::Equals,
                Box::new(recreated),
                Box::new(object_var.clone()),
            );
            let new_claim = AcornValue::ForAll(vec![struct_type.clone()], Box::new(new_eq))
                .genericize(&type_params);
            let source = Source::type_definition(
                self.module_id,
                range,
                self.depth,
                ss.name_token.text().to_string(),
                "new".to_string(),
            );
            let prop = Proposition::new(new_claim, type_params.clone(), source);
            self.add_node(Node::structural(project, self, prop));
        }

        let var_args = (0..ss.fields.len())
            .map(|i| AcornValue::Variable(i as AtomId, field_types[i].clone()))
            .collect::<Vec<_>>();
        let new_application = match &new_fn {
            Some(new_fn) => Some(self.bindings.apply_potential(
                new_fn.clone(),
                var_args.clone(),
                None,
                &ss.name_token,
            )?),
            None => None,
        };
        let constraint_for_args = if let Some(constraint_fn) = &constraint_fn {
            Some(self.bindings.apply_potential(
                constraint_fn.clone(),
                var_args.clone(),
                Some(&AcornType::Bool),
                &ss.name_token,
            )?)
        } else {
            None
        };

        if let Some(constraint) = &constraint_for_args {
            if let Some(option_type) = self.bindings.get_type_for_typename("Option").cloned() {
                let option_datatype = option_type.as_base_datatype().cloned().ok_or_else(|| {
                    ss.name_token
                        .error("Option must be a datatype to auto-generate constrained new_option")
                })?;
                let option_struct_type =
                    option_type.resolve(vec![struct_type.clone()], &ss.name_token)?;

                let (some_module_id, some_name) = self
                    .bindings
                    .resolve_datatype_attr(&option_datatype, "some")
                    .map_err(|e| ss.name_token.error(&e))?;
                let option_some = self
                    .bindings
                    .get_bindings(some_module_id, project)
                    .get_constant_value(&DefinedName::Constant(some_name))
                    .map_err(|e| ss.name_token.error(&e))?;

                let (none_module_id, none_name) = self
                    .bindings
                    .resolve_datatype_attr(&option_datatype, "none")
                    .map_err(|e| ss.name_token.error(&e))?;
                let option_none = self
                    .bindings
                    .get_bindings(none_module_id, project)
                    .get_constant_value(&DefinedName::Constant(none_name))
                    .map_err(|e| ss.name_token.error(&e))?;

                let new_option_fn_type =
                    AcornType::functional(field_types.clone(), option_struct_type.clone());
                let def_str = format!(
                    "{}.new_option: {}",
                    ss.name_token.text(),
                    new_option_fn_type
                );
                let new_option_fn = self.bindings.add_datatype_attribute(
                    &datatype,
                    "new_option",
                    type_params.clone(),
                    new_option_fn_type.genericize(&type_params),
                    None,
                    None,
                    vec![],
                    def_str,
                );

                let new_option_application = self.bindings.apply_potential(
                    new_option_fn.clone(),
                    var_args.clone(),
                    Some(&option_struct_type),
                    &ss.name_token,
                )?;
                let none_value = self.bindings.apply_potential(
                    option_none,
                    vec![],
                    Some(&option_struct_type),
                    &ss.name_token,
                )?;

                let witness =
                    AcornValue::Variable(field_types.len() as AtomId, struct_type.clone());
                let some_witness = self.bindings.apply_potential(
                    option_some.clone(),
                    vec![witness.clone()],
                    Some(&option_struct_type),
                    &ss.name_token,
                )?;
                let witness_match =
                    AcornValue::equals(new_option_application.clone(), some_witness.clone());
                let exists_some =
                    AcornValue::Exists(vec![struct_type.clone()], Box::new(witness_match.clone()));
                let some_claim = AcornValue::ForAll(
                    field_types.clone(),
                    Box::new(AcornValue::implies(constraint.clone(), exists_some)),
                )
                .genericize(&type_params);
                let source = Source::type_definition(
                    self.module_id,
                    range,
                    self.depth,
                    ss.name_token.text().to_string(),
                    "new_option".to_string(),
                );
                let prop = Proposition::new(some_claim, type_params.clone(), source);
                self.add_node(Node::structural(project, self, prop));

                for i in 0..ss.fields.len() {
                    let witness_member = self.bindings.apply_potential(
                        member_fns[i].clone(),
                        vec![witness.clone()],
                        None,
                        &ss.fields[i].0,
                    )?;
                    let field_eq = AcornValue::equals(
                        witness_member,
                        AcornValue::Variable(i as AtomId, field_types[i].clone()),
                    );
                    let projection_claim = AcornValue::ForAll(
                        [field_types.clone(), vec![struct_type.clone()]].concat(),
                        Box::new(AcornValue::implies(witness_match.clone(), field_eq)),
                    )
                    .genericize(&type_params);
                    let source = Source::type_definition(
                        self.module_id,
                        range,
                        self.depth,
                        ss.name_token.text().to_string(),
                        "new_option".to_string(),
                    );
                    let prop = Proposition::new(projection_claim, type_params.clone(), source);
                    self.add_node(Node::structural(project, self, prop));
                }

                let none_eq = AcornValue::equals(new_option_application, none_value);
                let none_claim = AcornValue::ForAll(
                    field_types.clone(),
                    Box::new(AcornValue::implies(constraint.clone().negate(), none_eq)),
                )
                .genericize(&type_params);
                let source = Source::type_definition(
                    self.module_id,
                    range,
                    self.depth,
                    ss.name_token.text().to_string(),
                    "new_option".to_string(),
                );
                let prop = Proposition::new(none_claim, type_params.clone(), source);
                self.add_node(Node::structural(project, self, prop));

                let round_trip_application = self.bindings.apply_potential(
                    new_option_fn.clone(),
                    member_args.clone(),
                    Some(&option_struct_type),
                    &ss.name_token,
                )?;
                let some_object = self.bindings.apply_potential(
                    option_some.clone(),
                    vec![object_var.clone()],
                    Some(&option_struct_type),
                    &ss.name_token,
                )?;
                let round_trip_eq = AcornValue::equals(round_trip_application, some_object);
                let round_trip_claim =
                    AcornValue::ForAll(vec![struct_type.clone()], Box::new(round_trip_eq))
                        .genericize(&type_params);
                let source = Source::type_definition(
                    self.module_id,
                    range,
                    self.depth,
                    ss.name_token.text().to_string(),
                    "new_option".to_string(),
                );
                let prop = Proposition::new(round_trip_claim, type_params.clone(), source);
                self.add_node(Node::structural(project, self, prop));
            }
        }

        if let Some(new_application) = new_application {
            for i in 0..ss.fields.len() {
                let (field_name_token, field_type_expr, _) = &ss.fields[i];
                let member_fn = &member_fns[i];
                let applied = self.bindings.apply_potential(
                    member_fn.clone(),
                    vec![new_application.clone()],
                    None,
                    field_name_token,
                )?;
                let member_eq = AcornValue::Binary(
                    BinaryOp::Equals,
                    Box::new(applied),
                    Box::new(AcornValue::Variable(i as AtomId, field_types[i].clone())),
                );
                let unbound_member_claim = if let Some(constraint) = &unbound_constraint {
                    AcornValue::implies(constraint.clone(), member_eq)
                } else {
                    member_eq
                };
                let member_claim =
                    AcornValue::ForAll(field_types.clone(), Box::new(unbound_member_claim))
                        .genericize(&type_params);
                let range = Range {
                    start: field_name_token.start_pos(),
                    end: field_type_expr.last_token().end_pos(),
                };
                let source = Source::type_definition(
                    self.module_id,
                    range,
                    self.depth,
                    ss.name_token.text().to_string(),
                    field_name_token.text().to_string(),
                );
                let prop = Proposition::new(member_claim, type_params.clone(), source);
                self.add_node(Node::structural(project, self, prop));
            }
        }

        for type_param in &ss.type_params {
            self.bindings.remove_type(type_param.name.text());
        }
        Ok(())
    }

    pub(super) fn add_inductive_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        is: &InductiveStatement,
    ) -> error::Result<()> {
        self.add_other_lines(statement);
        self.bindings
            .check_typename_available(is.name_token.text(), statement)?;
        let range = Range {
            start: statement.first_token.start_pos(),
            end: is.name_token.end_pos(),
        };

        let mut arbitrary_params = vec![];
        let type_params = self
            .evaluator(project)
            .evaluate_type_params(&is.type_params)?;
        for type_param in &type_params {
            arbitrary_params.push(self.bindings.add_arbitrary_type(type_param.clone()));
        }
        let typeclasses = type_params.iter().map(|tp| tp.typeclass.clone()).collect();
        let doc_comments = self.take_doc_comments();
        let definition_string = Some(statement.to_string());
        let potential_type = self.bindings.add_potential_type(
            &is.name_token,
            typeclasses,
            doc_comments,
            Some(is.name_token.range()),
            definition_string,
        );
        let arb_inductive_type =
            potential_type.resolve(arbitrary_params.clone(), &is.name_token)?;

        let mut constructors = vec![];
        let mut has_base = false;
        for (name_token, type_list_expr, doc_comments) in &is.constructors {
            let type_list = match type_list_expr {
                Some(expr) => {
                    let mut type_list = vec![];
                    self.evaluator(project)
                        .evaluate_type_list(expr, &mut type_list)?;
                    type_list
                }
                None => vec![],
            };
            if !type_list.contains(&arb_inductive_type) {
                has_base = true;
            }
            constructors.push((name_token.text(), type_list, doc_comments.clone()));
        }
        if !has_base {
            return Err(statement.error("inductive type must have a base case"));
        }

        let variances = type_params
            .iter()
            .map(|param| {
                let mut combined = Variance::None;
                for (_, type_list, _) in &constructors {
                    for arg_type in type_list {
                        combined = combined.merge(arg_type.compute_variance_with_lookup(
                            param,
                            true,
                            &|dt| self.bindings.get_datatype_variances(dt),
                        ));
                    }
                }
                combined
            })
            .collect::<Vec<_>>();

        let datatype_for_variance = Datatype {
            module_id: self.module_id,
            name: is.name_token.text().to_string(),
        };
        self.bindings
            .set_datatype_variances(&datatype_for_variance, variances);
        self.bindings
            .set_datatype_arity(&datatype_for_variance, type_params.len() as u8);

        for (constructor_name, type_list, _) in &constructors {
            for arg_type in type_list {
                self.check_strict_positivity(
                    arg_type,
                    &arb_inductive_type,
                    &arbitrary_params,
                    &is.name_token,
                )
                .map_err(|e| {
                    statement.error(&format!(
                        "constructor {} has invalid type: {}",
                        constructor_name, e
                    ))
                })?;
            }
        }

        let datatype = Datatype {
            module_id: self.module_id,
            name: is.name_token.text().to_string(),
        };
        let mut constructor_fns = vec![];
        let total = constructors.len();
        for (i, (constructor_name, type_list, doc_comments)) in constructors.iter().enumerate() {
            let arb_constructor_type =
                AcornType::functional(type_list.clone(), arb_inductive_type.clone());
            let gen_constructor_type = arb_constructor_type.genericize(&type_params);
            let constructor_info = ConstructorInfo {
                datatype: datatype.clone(),
                index: i,
                total,
            };
            let def_str = format!(
                "{}.{}: {}",
                is.name_token.text(),
                constructor_name,
                arb_constructor_type
            );
            let gen_constructor_fn = self.bindings.add_datatype_attribute(
                &datatype,
                constructor_name,
                type_params.clone(),
                gen_constructor_type,
                None,
                Some(constructor_info),
                doc_comments.clone(),
                def_str,
            );
            let arb_constructor_fn =
                gen_constructor_fn.resolve_constant(&arbitrary_params, &is.name_token)?;

            constructor_fns.push(arb_constructor_fn);
        }

        let mut match_result_param_name = "R".to_string();
        let mut match_result_suffix = 0;
        while type_params
            .iter()
            .any(|p| p.name == match_result_param_name)
        {
            match_result_suffix += 1;
            match_result_param_name = format!("R{}", match_result_suffix);
        }
        let match_result_param = TypeParam {
            name: match_result_param_name,
            typeclass: None,
        };
        let arb_match_result_type = AcornType::Arbitrary(match_result_param.clone());
        let mut arb_match_arg_types = vec![arb_inductive_type.clone()];
        for (_, constructor_arg_types, _) in &constructors {
            let case_type =
                AcornType::functional(constructor_arg_types.clone(), arb_match_result_type.clone());
            arb_match_arg_types.push(case_type);
        }
        let arb_match_type =
            AcornType::functional(arb_match_arg_types, arb_match_result_type.clone());
        let mut match_type_params = type_params.clone();
        match_type_params.push(match_result_param);
        let gen_match_type = arb_match_type.genericize(&match_type_params);
        let match_def_str = format!("{}.match: {}", is.name_token.text(), gen_match_type);
        self.bindings.add_datatype_attribute(
            &datatype,
            "match",
            match_type_params,
            gen_match_type,
            None,
            None,
            vec![],
            match_def_str,
        );

        for i in 0..constructors.len() {
            let (member_name, i_arg_types, _) = &constructors[i];
            let i_fn = constructor_fns[i].clone();
            let i_vars: Vec<_> = i_arg_types
                .iter()
                .enumerate()
                .map(|(k, t)| AcornValue::Variable(k as AtomId, t.clone()))
                .collect();
            let i_app = AcornValue::apply(i_fn, i_vars);
            for j in 0..i {
                let (_, j_arg_types, _) = &constructors[j];
                let j_fn = constructor_fns[j].clone();
                let j_vars: Vec<_> = j_arg_types
                    .iter()
                    .enumerate()
                    .map(|(k, t)| {
                        AcornValue::Variable((k + i_arg_types.len()) as AtomId, t.clone())
                    })
                    .collect();
                let j_app = AcornValue::apply(j_fn, j_vars);
                let inequality = AcornValue::not_equals(i_app.clone(), j_app);
                let mut quantifiers = i_arg_types.clone();
                quantifiers.extend(j_arg_types.clone());
                let arb_claim = AcornValue::forall(quantifiers, inequality);
                let source = Source::type_definition(
                    self.module_id,
                    range,
                    self.depth,
                    is.name_token.text().to_string(),
                    member_name.to_string(),
                );
                let gen_claim = arb_claim.genericize(&type_params);
                let prop = Proposition::new(gen_claim, type_params.clone(), source);
                self.add_node(Node::structural(project, self, prop));
            }
        }

        let mut disjuncts = vec![];
        for (i, constructor_fn) in constructor_fns.iter().enumerate() {
            let (_, arg_types, _) = &constructors[i];
            let args = arg_types
                .iter()
                .enumerate()
                .map(|(k, t)| AcornValue::Variable((k + 1) as AtomId, t.clone()))
                .collect();
            let app = AcornValue::apply(constructor_fn.clone(), args);
            let var = AcornValue::Variable(0, arb_inductive_type.clone());
            let equality = AcornValue::equals(var, app);
            let exists = AcornValue::exists(arg_types.clone(), equality);
            disjuncts.push(exists);
        }
        let disjunction = AcornValue::reduce(BinaryOp::Or, disjuncts);
        let arb_claim = AcornValue::forall(vec![arb_inductive_type.clone()], disjunction);
        let source = Source::type_definition(
            self.module_id,
            range,
            self.depth,
            is.name_token.text().to_string(),
            "new".to_string(),
        );
        let gen_claim = arb_claim.genericize(&type_params);
        let prop = Proposition::new(gen_claim, type_params.clone(), source);
        self.add_node(Node::structural(project, self, prop));

        for (i, constructor_fn) in constructor_fns.iter().enumerate() {
            let (member_name, arg_types, _) = &constructors[i];
            if arg_types.is_empty() {
                continue;
            }

            let left_args = arg_types
                .iter()
                .enumerate()
                .map(|(k, t)| AcornValue::Variable(k as AtomId, t.clone()))
                .collect();
            let lhs = AcornValue::apply(constructor_fn.clone(), left_args);
            let right_args = arg_types
                .iter()
                .enumerate()
                .map(|(k, t)| AcornValue::Variable((k + arg_types.len()) as AtomId, t.clone()))
                .collect();
            let rhs = AcornValue::apply(constructor_fn.clone(), right_args);
            let equality = AcornValue::equals(lhs, rhs);

            let mut conjuncts = vec![];
            for (i, arg_type) in arg_types.iter().enumerate() {
                let left = AcornValue::Variable(i as AtomId, arg_type.clone());
                let right = AcornValue::Variable((i + arg_types.len()) as AtomId, arg_type.clone());
                let arg_equality = AcornValue::equals(left, right);
                conjuncts.push(arg_equality);
            }
            let conjunction = AcornValue::reduce(BinaryOp::And, conjuncts);
            let mut forall_types = arg_types.clone();
            forall_types.extend_from_slice(arg_types);
            let arb_claim =
                AcornValue::forall(forall_types, AcornValue::implies(equality, conjunction));
            let source = Source::type_definition(
                self.module_id,
                range,
                self.depth,
                is.name_token.text().to_string(),
                member_name.to_string(),
            );
            let gen_claim = arb_claim.genericize(&type_params);
            let prop = Proposition::new(gen_claim, type_params.clone(), source);
            self.add_node(Node::structural(project, self, prop));
        }

        let hyp_type = AcornType::functional(vec![arb_inductive_type.clone()], AcornType::Bool);
        let mut conjuncts = vec![];
        for (i, constructor_fn) in constructor_fns.iter().enumerate() {
            let (_, arg_types, _) = &constructors[i];
            let mut args = vec![];
            let mut conditions = vec![];
            for (j, arg_type) in arg_types.iter().enumerate() {
                let id = (j + 1) as AtomId;
                args.push(AcornValue::Variable(id, arg_type.clone()));
                if arg_type == &arb_inductive_type {
                    conditions.push(AcornValue::apply(
                        AcornValue::Variable(0, hyp_type.clone()),
                        vec![AcornValue::Variable(id, arg_type.clone())],
                    ));
                }
            }

            let new_instance = AcornValue::apply(constructor_fn.clone(), args);
            let instance_claim = AcornValue::apply(
                AcornValue::Variable(0, hyp_type.clone()),
                vec![new_instance],
            );
            let unbound = if conditions.is_empty() {
                instance_claim
            } else {
                AcornValue::implies(
                    AcornValue::reduce(BinaryOp::And, conditions),
                    instance_claim,
                )
            };
            let conjunction_part = AcornValue::forall(arg_types.clone(), unbound);
            conjuncts.push(conjunction_part);
        }
        let conjunction = AcornValue::reduce(BinaryOp::And, conjuncts);
        let conclusion = AcornValue::forall(
            vec![arb_inductive_type.clone()],
            AcornValue::apply(
                AcornValue::Variable(0, hyp_type.clone()),
                vec![AcornValue::Variable(1, arb_inductive_type.clone())],
            ),
        );
        let unbound_claim = AcornValue::implies(conjunction, conclusion);

        let name = ConstantName::datatype_attr(self.module_id, datatype.clone(), "induction");
        let arb_lambda_claim = AcornValue::lambda(vec![hyp_type.clone()], unbound_claim.clone());
        let gen_lambda_claim = arb_lambda_claim.genericize(&type_params);
        let def_str = format!(
            "{}.induction: {}",
            is.name_token.text(),
            gen_lambda_claim.get_type()
        );
        self.bindings.add_datatype_attribute(
            &datatype,
            "induction",
            type_params.clone(),
            gen_lambda_claim.get_type(),
            Some(gen_lambda_claim),
            None,
            vec![],
            def_str,
        );
        self.bindings.mark_as_theorem(&name);

        let arb_forall_claim = AcornValue::forall(vec![hyp_type], unbound_claim);
        let source = Source::type_definition(
            self.module_id,
            range,
            self.depth,
            datatype.name.clone(),
            "induction".to_string(),
        );
        let gen_forall_claim = arb_forall_claim.genericize(&type_params);
        let prop = Proposition::new(gen_forall_claim, type_params, source);
        self.add_node(Node::structural(project, self, prop));

        for type_param in &is.type_params {
            self.bindings.remove_type(type_param.name.text());
        }
        Ok(())
    }

    /// Check that an inductive type appears only in strictly positive positions.
    fn check_strict_positivity(
        &self,
        arg_type: &AcornType,
        inductive_type: &AcornType,
        inductive_params: &[AcornType],
        source: &dyn ErrorContext,
    ) -> error::Result<()> {
        match arg_type {
            AcornType::Data(datatype, type_args) => {
                for (i, arg) in type_args.iter().enumerate() {
                    if self.contains_inductive_type(arg, inductive_type, inductive_params) {
                        if let Some(variances) = self.bindings.get_datatype_variances(datatype) {
                            if i < variances.len() {
                                match &variances[i] {
                                    Variance::Negative | Variance::Both => {
                                        return Err(source.error(&format!(
                                            "inductive type appears in negative position (via type {})",
                                            datatype.name
                                        )));
                                    }
                                    Variance::Positive | Variance::None => {
                                        self.check_strict_positivity(
                                            arg,
                                            inductive_type,
                                            inductive_params,
                                            source,
                                        )?;
                                    }
                                }
                            }
                        } else {
                            self.check_strict_positivity(
                                arg,
                                inductive_type,
                                inductive_params,
                                source,
                            )?;
                        }
                    }
                }
                Ok(())
            }
            AcornType::Function(ftype) => {
                for arg in &ftype.arg_types {
                    if self.contains_inductive_type(arg, inductive_type, inductive_params) {
                        return Err(source.error(
                            "inductive type appears in negative position (function argument)",
                        ));
                    }
                }
                self.check_strict_positivity(
                    &ftype.return_type,
                    inductive_type,
                    inductive_params,
                    source,
                )
            }
            _ => Ok(()),
        }
    }

    /// Helper to check if a type contains the inductive type being defined.
    fn contains_inductive_type(
        &self,
        arg_type: &AcornType,
        inductive_type: &AcornType,
        inductive_params: &[AcornType],
    ) -> bool {
        if arg_type == inductive_type {
            return true;
        }
        if let (AcornType::Data(dt1, _), AcornType::Data(dt2, _)) = (arg_type, inductive_type) {
            if dt1 == dt2 {
                return true;
            }
        }
        match arg_type {
            AcornType::Data(_, type_args) => type_args
                .iter()
                .any(|t| self.contains_inductive_type(t, inductive_type, inductive_params)),
            AcornType::Function(ftype) => {
                ftype
                    .arg_types
                    .iter()
                    .any(|t| self.contains_inductive_type(t, inductive_type, inductive_params))
                    || self.contains_inductive_type(
                        &ftype.return_type,
                        inductive_type,
                        inductive_params,
                    )
            }
            _ => false,
        }
    }
}

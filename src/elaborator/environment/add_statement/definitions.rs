use super::*;

impl Environment {
    /// Adds a "let" statement to the environment.
    /// This can also be in a class, typeclass, or instance block.
    /// If this is in an attributes block, the datatype parameters are provided.
    pub(super) fn add_let_statement(
        &mut self,
        project: &Project,
        statement: &Statement,
        defined_name: DefinedName,
        ls: &LetStatement,
        range: Range,
        datatype_params: Option<&Vec<TypeParam>>,
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

        let local_type_params = self
            .evaluator(project)
            .evaluate_type_params(&ls.type_params)?;
        for param in &local_type_params {
            self.bindings.add_arbitrary_type(param.clone());
        }

        let (acorn_type, value) = match &ls.type_expr {
            Some(type_expr) => {
                let acorn_type = self.evaluator(project).evaluate_type(type_expr)?;
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
                            if acorn_type != AcornType::Data(datatype, vec![]) {
                                return Err(type_expr.error(
                                    "numeric datatype variables must be the datatype type",
                                ));
                            }
                        }
                        DefinedName::Instance(instance_name) => {
                            if acorn_type != AcornType::Data(instance_name.datatype.clone(), vec![])
                            {
                                return Err(type_expr.error(
                                    "numeric instance variables must be the instance datatype type",
                                ));
                            }
                        }
                    }
                }
                let value = if ls.value.is_axiom() {
                    None
                } else {
                    let v = if let Some(instance_name) = defined_name.as_instance() {
                        Evaluator::new_for_instance_member(
                            project,
                            &self.bindings,
                            Some(&mut self.token_map),
                            instance_name,
                        )
                        .evaluate_value(&ls.value, Some(&acorn_type))?
                    } else {
                        self.evaluator(project)
                            .evaluate_value(&ls.value, Some(&acorn_type))?
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
                let value = if let Some(instance_name) = defined_name.as_instance() {
                    Evaluator::new_for_instance_member(
                        project,
                        &self.bindings,
                        Some(&mut self.token_map),
                        instance_name,
                    )
                    .evaluate_value(&ls.value, None)?
                } else {
                    self.evaluator(project).evaluate_value(&ls.value, None)?
                };
                let acorn_type = value.get_type();
                (acorn_type, Some(value))
            }
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
                p.clone()
            }
            None => local_type_params,
        };
        let acorn_type = acorn_type.genericize(&type_params);
        let value = value.map(|v| v.genericize(&type_params));
        let def_str = statement.to_string();

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
        self.define_constant(
            defined_name,
            type_params,
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
        datatype_params: Option<&Vec<TypeParam>>,
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
        let (fn_param_names, _, arg_types, unbound_value, value_type) =
            self.bindings.evaluate_scoped_value(
                &ds.type_params,
                &ds.args,
                Some(&ds.return_type),
                &ds.return_value,
                self_type,
                recursion_name.as_ref(),
                defined_name.as_instance(),
                datatype_params,
                project,
                Some(&mut self.token_map),
            )?;

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
                fn_value = fn_value.genericize(datatype_params);

                if !fn_param_names.is_empty() {
                    fn_value = fn_value.genericize(&fn_param_names);
                    let mut combined_params = datatype_params.clone();
                    combined_params.extend(fn_param_names);
                    combined_params
                } else {
                    datatype_params.clone()
                }
            } else {
                fn_param_names
            };

            self.define_constant(
                defined_name,
                params,
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
                let mut combined_params = datatype_params.clone();
                combined_params.extend(fn_param_names);
                combined_params
            } else {
                datatype_params.clone()
            }
        } else {
            fn_param_names
        };
        self.define_constant(
            defined_name,
            params,
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

        let (type_params, arg_names, arg_types, value, _) = self.bindings.evaluate_scoped_value(
            &ts.type_params,
            &ts.args,
            None,
            &ts.claim,
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
                theorem_type.clone(),
                Some(lambda_claim.clone()),
                None,
                doc_comments,
                Some(name_range),
                statement.to_string(),
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
            self.record_citation_statement(statement);
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
        datatype_params: Option<&Vec<TypeParam>>,
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

        let local_type_params = self
            .evaluator(project)
            .evaluate_type_params(&vss.type_params)?;
        for param in &local_type_params {
            self.bindings.add_arbitrary_type(param.clone());
        }

        for declaration in &vss.declarations {
            if let Declaration::Typed(_, type_expr) = declaration {
                self.evaluator(project).evaluate_type(type_expr)?;
            }
        }

        let mut stack = Stack::new();
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
                p.clone()
            }
            None => local_type_params.clone(),
        };
        let block = Block::new(
            project,
            &self,
            vec![],
            vec![],
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

            let generic_type = quant_type.clone().genericize(&definition_type_params);
            let def_str = format!("{}: {}", quant_name, generic_type);
            self.bindings.add_defined_name(
                &defined_name,
                definition_type_params.clone(),
                generic_type.clone(),
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
            let constant_value = AcornValue::constant(
                const_name,
                type_args,
                quant_type.clone(),
                generic_type,
                vec![],
            );
            constant_values.push(constant_value);
        }

        let num_vars = quant_names.len() as AtomId;
        let specific_claim_value = general_claim_value.bind_values(0, num_vars, &constant_values);
        let external_claim = specific_claim_value.genericize(&definition_type_params);
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
        datatype_params: Option<&Vec<TypeParam>>,
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
        let (fn_type_params, mut arg_names, mut arg_types, condition, _) =
            self.bindings.evaluate_scoped_value(
                &fss.type_params,
                &fss.declarations,
                None,
                &fss.condition,
                None,
                recursion_name.as_ref(),
                defined_name.as_instance(),
                datatype_params,
                project,
                Some(&mut self.token_map),
            )?;

        let unbound_condition = condition.ok_or_else(|| statement.error("missing condition"))?;
        if unbound_condition.get_type() != AcornType::Bool {
            return Err(fss.condition.error("condition must be a boolean"));
        }

        let _return_name = arg_names.pop().unwrap();
        let return_type = arg_types.pop().unwrap();
        let block_args: Vec<_> = arg_names
            .iter()
            .cloned()
            .zip(arg_types.iter().cloned())
            .collect();
        let num_args = block_args.len() as AtomId;

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
        let mut all_type_params = datatype_params.cloned().unwrap_or_default();
        all_type_params.extend(fn_type_params);
        let generic_function_type = function_type.clone().genericize(&all_type_params);
        let doc_comments = self.take_doc_comments();
        self.bindings.add_defined_name(
            &defined_name,
            all_type_params.clone(),
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
        );
        let function_term = AcornValue::apply(
            function_constant.clone(),
            arg_types
                .iter()
                .enumerate()
                .map(|(i, t)| AcornValue::Variable(i as AtomId, t.clone()))
                .collect(),
        );
        let return_bound = unbound_condition.bind_values(num_args, num_args, &[function_term]);
        let arg_count = arg_types.len();
        let arb_condition = AcornValue::ForAll(arg_types, Box::new(return_bound));

        let external_condition = arb_condition.genericize(&all_type_params);
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
            let claim = claim.expand_lambdas(0);
            let source = Source::anonymous(self.module_id, statement.range(), self.depth);
            let prop = Proposition::new(claim, vec![], source);
            let prop = self.bindings.expand_citation(prop, project);
            self.add_node(Node::structural(project, self, prop));
            self.record_citation_statement(statement);
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
                AcornValue::constant(name, vec![], arg_type.clone(), arg_type.clone(), vec![])
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

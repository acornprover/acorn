use super::*;

impl Environment {
    pub(super) fn add_attributes_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        ats: &AttributesStatement,
    ) -> error::Result<()> {
        self.add_other_lines(statement);

        if let Some(potential) = self.bindings.get_type_for_typename(ats.name_token.text()) {
            self.add_type_attributes(project, ats, potential.clone())
        } else if let Some(typeclass) = self.bindings.get_typeclass_for_name(ats.name_token.text())
        {
            self.add_typeclass_attributes(project, ats, typeclass.clone())
        } else {
            Err(ats.name_token.error(&format!(
                "undefined type or typeclass name '{}'",
                ats.name_token.text()
            )))
        }
    }

    fn add_type_attributes(
        &mut self,
        project: &mut Project,
        ats: &AttributesStatement,
        potential: crate::elaborator::acorn_type::PotentialType,
    ) -> error::Result<()> {
        let defining_module = self.module_id;
        let type_args = self
            .evaluator(project)
            .evaluate_attributes_type_args(&ats.type_params)?;

        match type_args {
            AttributesTypeArgs::Generic(family_params) => {
                let expected_param_kinds = match &potential {
                    crate::elaborator::acorn_type::PotentialType::Resolved(_) => vec![],
                    crate::elaborator::acorn_type::PotentialType::Unresolved(unresolved) => {
                        unresolved.params.clone()
                    }
                };
                if family_params.len() != expected_param_kinds.len() {
                    return Err(ats.name_token.error(&format!(
                        "type {} expects {} parameters, but got {}",
                        ats.name_token.text(),
                        expected_param_kinds.len(),
                        family_params.len()
                    )));
                }

                for ((expr, family_param), expected_kind) in ats
                    .type_params
                    .iter()
                    .zip(&family_params)
                    .zip(&expected_param_kinds)
                {
                    match (family_param, expected_kind) {
                        (
                            crate::elaborator::acorn_type::FamilyParam::Type(_),
                            crate::elaborator::acorn_type::FamilyParamKind::Type(_),
                        ) => {}
                        (
                            crate::elaborator::acorn_type::FamilyParam::Value(value_param),
                            crate::elaborator::acorn_type::FamilyParamKind::Value(expected_type),
                        ) => {
                            if value_param.value_type != *expected_type {
                                return Err(expr.name.error(&format!(
                                    "expected a value parameter of type {}, but found {}",
                                    expected_type, value_param.value_type
                                )));
                            }
                        }
                        (
                            crate::elaborator::acorn_type::FamilyParam::Type(_),
                            crate::elaborator::acorn_type::FamilyParamKind::Value(expected_type),
                        ) => {
                            return Err(expr.name.error(&format!(
                                "expected a dependent value parameter like '{}: {}'",
                                expr.name.text(),
                                expected_type
                            )));
                        }
                        (
                            crate::elaborator::acorn_type::FamilyParam::Value(_),
                            crate::elaborator::acorn_type::FamilyParamKind::Type(_),
                        ) => {
                            return Err(expr
                                .name
                                .error("expected a type parameter here, not a value parameter"));
                        }
                    }
                }
                for (expr, family_param) in ats.type_params.iter().zip(&family_params) {
                    if let Some(type_param) = family_param.as_type_param() {
                        self.bindings
                            .check_typename_available(&type_param.name, &expr.name)?;
                    }
                }

                let family_scope = DatatypeFamilyScope {
                    type_params: family_params
                        .iter()
                        .filter_map(|param| param.as_type_param().cloned())
                        .collect(),
                    value_params: family_params
                        .iter()
                        .filter_map(|param| param.as_value_param().cloned())
                        .collect(),
                };
                let mut arbitrary_type_args = vec![];
                for param in &family_scope.type_params {
                    arbitrary_type_args.push(self.bindings.add_arbitrary_type(param.clone()));
                }
                let mut next_type_arg = 0usize;
                let mut next_value_arg = 0usize;
                let family_args = family_params
                    .iter()
                    .map(|param| match param {
                        crate::elaborator::acorn_type::FamilyParam::Type(_) => {
                            let arg = crate::elaborator::acorn_type::DependentTypeArg::Type(
                                arbitrary_type_args[next_type_arg].clone(),
                            );
                            next_type_arg += 1;
                            arg
                        }
                        crate::elaborator::acorn_type::FamilyParam::Value(value_param) => {
                            let arg = crate::elaborator::acorn_type::DependentTypeArg::Value(
                                AcornValue::Variable(
                                    next_value_arg as AtomId,
                                    value_param.value_type.clone(),
                                ),
                            );
                            next_value_arg += 1;
                            arg
                        }
                    })
                    .collect();
                let instance_type = potential.resolve_args(family_args, &ats.name_token)?;
                let datatype = self
                    .check_can_add_attributes(&ats.name_token, &instance_type)?
                    .clone();

                for substatement in &ats.body.statements {
                    match &substatement.statement {
                        StatementInfo::Let(ls) => {
                            self.add_let_statement(
                                project,
                                substatement,
                                DefinedName::datatype_attr_defined(
                                    defining_module,
                                    &datatype,
                                    ls.name_token.text(),
                                ),
                                ls,
                                ls.name_token.range(),
                                Some(&family_scope),
                            )?;
                        }
                        StatementInfo::VariableSatisfy(vss) => {
                            let datatype = datatype.clone();
                            self.add_variable_satisfy_statement_named(
                                project,
                                substatement,
                                vss,
                                Some(&family_scope),
                                move |name| {
                                    DefinedName::datatype_attr_defined(
                                        defining_module,
                                        &datatype,
                                        name,
                                    )
                                },
                            )?;
                        }
                        StatementInfo::FunctionSatisfy(fss) => {
                            self.add_function_satisfy_statement_named(
                                project,
                                substatement,
                                fss,
                                DefinedName::datatype_attr_defined(
                                    defining_module,
                                    &datatype,
                                    fss.name_token.text(),
                                ),
                                Some(&family_scope),
                            )?;
                        }
                        StatementInfo::Define(ds) => {
                            self.add_define_statement(
                                project,
                                substatement,
                                DefinedName::datatype_attr_defined(
                                    defining_module,
                                    &datatype,
                                    ds.name_token.text(),
                                ),
                                Some(&instance_type),
                                Some(&family_scope),
                                ds,
                                ds.name_token.range(),
                            )?;
                        }
                        StatementInfo::DocComment(s) => {
                            self.doc_comments.push(s.clone());
                        }
                        _ => {
                            return Err(substatement
                                .error("only let, let ... satisfy, define, and doc comment statements are allowed in attributes bodies"));
                        }
                    }
                }
                for type_param in &family_scope.type_params {
                    self.bindings.remove_type(&type_param.name);
                }
                Ok(())
            }
            AttributesTypeArgs::Concrete(concrete_types) => {
                let instance_type = potential.resolve(concrete_types.clone(), &ats.name_token)?;
                let datatype = self
                    .check_can_add_attributes(&ats.name_token, &instance_type)?
                    .clone();

                self.check_no_conflicting_attributes(&datatype, &ats.body)?;

                for substatement in &ats.body.statements {
                    match &substatement.statement {
                        StatementInfo::Let(ls) => {
                            self.add_let_statement(
                                project,
                                substatement,
                                DefinedName::datatype_specific_attr_defined(
                                    defining_module,
                                    datatype.clone(),
                                    &concrete_types,
                                    ls.name_token.text(),
                                ),
                                ls,
                                ls.name_token.range(),
                                None,
                            )?;
                        }
                        StatementInfo::VariableSatisfy(vss) => {
                            let datatype = datatype.clone();
                            let concrete_types = concrete_types.clone();
                            self.add_variable_satisfy_statement_named(
                                project,
                                substatement,
                                vss,
                                None,
                                move |name| {
                                    DefinedName::datatype_specific_attr_defined(
                                        defining_module,
                                        datatype.clone(),
                                        &concrete_types,
                                        name,
                                    )
                                },
                            )?;
                        }
                        StatementInfo::FunctionSatisfy(fss) => {
                            self.add_function_satisfy_statement_named(
                                project,
                                substatement,
                                fss,
                                DefinedName::datatype_specific_attr_defined(
                                    defining_module,
                                    datatype.clone(),
                                    &concrete_types,
                                    fss.name_token.text(),
                                ),
                                None,
                            )?;
                        }
                        StatementInfo::Define(ds) => {
                            self.add_define_statement(
                                project,
                                substatement,
                                DefinedName::datatype_specific_attr_defined(
                                    defining_module,
                                    datatype.clone(),
                                    &concrete_types,
                                    ds.name_token.text(),
                                ),
                                Some(&instance_type),
                                None,
                                ds,
                                ds.name_token.range(),
                            )?;
                        }
                        StatementInfo::DocComment(s) => {
                            self.doc_comments.push(s.clone());
                        }
                        _ => {
                            return Err(substatement
                                .error("only let, let ... satisfy, define, and doc comment statements are allowed in attributes bodies"));
                        }
                    }
                }
                Ok(())
            }
        }
    }

    fn add_typeclass_attributes(
        &mut self,
        project: &mut Project,
        ats: &AttributesStatement,
        typeclass: crate::elaborator::acorn_type::Typeclass,
    ) -> error::Result<()> {
        let defining_module = self.module_id;
        if !ats.type_params.is_empty() {
            return Err(ats.type_params[0]
                .name
                .error("typeclass attributes do not support type parameters"));
        }

        let instance_name_token = ats.instance_name.as_ref().ok_or_else(|| {
            ats.name_token.error(
                "typeclass attributes require an instance name (e.g., 'attributes M: Magma')",
            )
        })?;

        let instance_name = instance_name_token.text();
        let type_param = crate::elaborator::acorn_type::TypeParam {
            name: instance_name.to_string(),
            typeclass: Some(typeclass.clone()),
        };
        let instance_type = self.bindings.add_arbitrary_type(type_param.clone());
        let family_scope = DatatypeFamilyScope {
            type_params: vec![type_param],
            value_params: vec![],
        };

        for substatement in &ats.body.statements {
            match &substatement.statement {
                StatementInfo::Let(ls) => {
                    self.add_let_statement(
                        project,
                        substatement,
                        DefinedName::typeclass_attr_defined(
                            defining_module,
                            &typeclass,
                            ls.name_token.text(),
                        ),
                        ls,
                        ls.name_token.range(),
                        Some(&family_scope),
                    )?;
                }
                StatementInfo::VariableSatisfy(vss) => {
                    let typeclass = typeclass.clone();
                    self.add_variable_satisfy_statement_named(
                        project,
                        substatement,
                        vss,
                        Some(&family_scope),
                        move |name| {
                            DefinedName::typeclass_attr_defined(defining_module, &typeclass, name)
                        },
                    )?;
                }
                StatementInfo::FunctionSatisfy(fss) => {
                    self.add_function_satisfy_statement_named(
                        project,
                        substatement,
                        fss,
                        DefinedName::typeclass_attr_defined(
                            defining_module,
                            &typeclass,
                            fss.name_token.text(),
                        ),
                        Some(&family_scope),
                    )?;
                }
                StatementInfo::Define(ds) => {
                    self.add_define_statement(
                        project,
                        substatement,
                        DefinedName::typeclass_attr_defined(
                            defining_module,
                            &typeclass,
                            ds.name_token.text(),
                        ),
                        Some(&instance_type),
                        Some(&family_scope),
                        ds,
                        ds.name_token.range(),
                    )?;
                }
                StatementInfo::DocComment(s) => {
                    self.doc_comments.push(s.clone());
                }
                _ => {
                    return Err(substatement
                        .error("only let, let ... satisfy, define, and doc comment statements are allowed in attributes bodies"));
                }
            }
        }

        self.bindings.remove_type(instance_name);
        Ok(())
    }
}

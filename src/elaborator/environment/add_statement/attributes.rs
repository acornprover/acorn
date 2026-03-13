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
            AttributesTypeArgs::Generic(type_params) => {
                let mut params = vec![];
                for param in &type_params {
                    params.push(self.bindings.add_arbitrary_type(param.clone()));
                }
                let instance_type = potential.resolve_with_arbitrary(params, &ats.name_token)?;
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
                                Some(&type_params),
                            )?;
                        }
                        StatementInfo::VariableSatisfy(vss) => {
                            let datatype = datatype.clone();
                            self.add_variable_satisfy_statement_named(
                                project,
                                substatement,
                                vss,
                                Some(&type_params),
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
                                Some(&type_params),
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
                                Some(&type_params),
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
                for type_param in &ats.type_params {
                    self.bindings.remove_type(type_param.name.text());
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
        let type_params = vec![type_param];

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
                        Some(&type_params),
                    )?;
                }
                StatementInfo::VariableSatisfy(vss) => {
                    let typeclass = typeclass.clone();
                    self.add_variable_satisfy_statement_named(
                        project,
                        substatement,
                        vss,
                        Some(&type_params),
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
                        Some(&type_params),
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
                        Some(&type_params),
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

use super::*;

fn attribute_name_tokens(statement: &Statement) -> Vec<&Token> {
    match &statement.statement {
        StatementInfo::Let(let_statement) => vec![&let_statement.name_token],
        StatementInfo::VariableSatisfy(variable_satisfy_statement) => variable_satisfy_statement
            .declarations
            .iter()
            .map(|declaration| declaration.token())
            .collect(),
        StatementInfo::FunctionSatisfy(function_satisfy_statement) => {
            vec![&function_satisfy_statement.name_token]
        }
        StatementInfo::Define(define_statement) => vec![&define_statement.name_token],
        _ => vec![],
    }
}

impl Environment {
    fn check_attribute_body_names_unique(
        &self,
        body: &crate::syntax::statement::Body,
    ) -> error::Result<()> {
        let mut names = std::collections::BTreeSet::new();
        for statement in &body.statements {
            for token in attribute_name_tokens(statement) {
                if !names.insert(token.text()) {
                    return Err(
                        token.error(&format!("duplicate attribute name '{}'", token.text()))
                    );
                }
            }
        }
        Ok(())
    }

    fn check_type_attribute_names_available(
        &self,
        datatype: &Datatype,
        body: &crate::syntax::statement::Body,
    ) -> error::Result<()> {
        self.check_attribute_body_names_unique(body)?;
        for statement in &body.statements {
            for token in attribute_name_tokens(statement) {
                if self.bindings.has_type_attr(datatype, token.text()) {
                    return Err(token.error(&format!(
                        "attribute '{}' is already defined on {}",
                        token.text(),
                        datatype.name
                    )));
                }
            }
        }
        Ok(())
    }

    fn check_typeclass_attribute_names_available(
        &self,
        typeclass: &Typeclass,
        body: &crate::syntax::statement::Body,
    ) -> error::Result<()> {
        self.check_attribute_body_names_unique(body)?;
        for statement in &body.statements {
            for token in attribute_name_tokens(statement) {
                if let Some(existing_tc) = self
                    .bindings
                    .cached_typeclass_attr_lookup(typeclass, token.text())
                {
                    return Err(token.error(&format!(
                        "attribute '{}' is already defined via typeclass '{}'",
                        token.text(),
                        existing_tc.name
                    )));
                }
            }
        }
        Ok(())
    }

    pub(super) fn add_attributes_statement(
        &mut self,
        project: &dyn ProjectLookup,
        statement: &Statement,
        attributes_statement: &AttributesStatement,
    ) -> error::Result<()> {
        self.add_other_lines(statement);

        if let Some(potential) = self
            .bindings
            .get_type_for_typename(attributes_statement.name_token.text())
        {
            self.add_type_attributes(project, attributes_statement, potential.clone())
        } else if let Some(typeclass) = self
            .bindings
            .get_typeclass_for_name(attributes_statement.name_token.text())
        {
            self.add_typeclass_attributes(project, attributes_statement, typeclass.clone())
        } else {
            Err(attributes_statement.name_token.error(&format!(
                "undefined type or typeclass name '{}'",
                attributes_statement.name_token.text()
            )))
        }
    }

    fn add_type_attributes(
        &mut self,
        project: &dyn ProjectLookup,
        attributes_statement: &AttributesStatement,
        potential: crate::elaborator::acorn_type::PotentialType,
    ) -> error::Result<()> {
        let defining_module = self.module_id;
        let type_args = self
            .evaluator(project)
            .evaluate_attributes_type_args(&attributes_statement.type_params)?;

        match type_args {
            AttributesTypeArgs::Generic(family_params) => {
                let expected_param_kinds = match &potential {
                    crate::elaborator::acorn_type::PotentialType::Resolved(_) => vec![],
                    crate::elaborator::acorn_type::PotentialType::Unresolved(unresolved) => {
                        unresolved.params.clone()
                    }
                };
                if family_params.len() != expected_param_kinds.len() {
                    return Err(attributes_statement.name_token.error(&format!(
                        "type {} expects {} parameters, but got {}",
                        attributes_statement.name_token.text(),
                        expected_param_kinds.len(),
                        family_params.len()
                    )));
                }

                let family_param_kinds = family_params.canonical_kinds();
                for (((expr, family_param), family_param_kind), expected_kind) in
                    attributes_statement
                        .type_params
                        .iter()
                        .zip(&family_params)
                        .zip(&family_param_kinds)
                        .zip(&expected_param_kinds)
                {
                    match (family_param, family_param_kind, expected_kind) {
                        (
                            FamilyParam::Type(_),
                            FamilyParamKind::Type(_),
                            FamilyParamKind::Type(_),
                        ) => {}
                        (
                            FamilyParam::Value(_),
                            FamilyParamKind::Value(value_type),
                            FamilyParamKind::Value(expected_type),
                        ) if value_type == expected_type => {}
                        (
                            FamilyParam::Value(_),
                            FamilyParamKind::Value(value_type),
                            FamilyParamKind::Value(expected_type),
                        ) => {
                            return Err(expr.name.error(&format!(
                                "expected a value parameter of type {}, but found {}",
                                expected_type, value_type
                            )));
                        }
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
                        _ => unreachable!("family parameter kind should match the parameter"),
                    }
                }
                for (expr, family_param) in
                    attributes_statement.type_params.iter().zip(&family_params)
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
                let (family_args, _) =
                    family_params.family_args_for_type_args(&arbitrary_type_args);
                let instance_type =
                    potential.resolve_args(family_args, &attributes_statement.name_token)?;
                let datatype = self
                    .check_can_add_attributes(&attributes_statement.name_token, &instance_type)?
                    .clone();
                self.check_type_attribute_names_available(&datatype, &attributes_statement.body)?;

                let result = (|| {
                    for substatement in &attributes_statement.body.statements {
                        match &substatement.statement {
                            StatementInfo::Let(let_statement) => {
                                self.add_let_statement(
                                    project,
                                    substatement,
                                    DefinedName::datatype_attr_defined(
                                        defining_module,
                                        &datatype,
                                        let_statement.name_token.text(),
                                    ),
                                    let_statement,
                                    let_statement.name_token.range(),
                                    Some(&family_scope),
                                )?;
                            }
                            StatementInfo::VariableSatisfy(variable_satisfy_statement) => {
                                let datatype = datatype.clone();
                                self.add_variable_satisfy_statement_named(
                                    project,
                                    substatement,
                                    variable_satisfy_statement,
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
                            StatementInfo::FunctionSatisfy(function_satisfy_statement) => {
                                self.add_function_satisfy_statement_named(
                                    project,
                                    substatement,
                                    function_satisfy_statement,
                                    DefinedName::datatype_attr_defined(
                                        defining_module,
                                        &datatype,
                                        function_satisfy_statement.name_token.text(),
                                    ),
                                    Some(&family_scope),
                                )?;
                            }
                            StatementInfo::Define(define_statement) => {
                                self.add_define_statement(
                                    project,
                                    substatement,
                                    DefinedName::datatype_attr_defined(
                                        defining_module,
                                        &datatype,
                                        define_statement.name_token.text(),
                                    ),
                                    Some(&instance_type),
                                    Some(&family_scope),
                                    define_statement,
                                    define_statement.name_token.range(),
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
                })();
                for type_param in family_scope.type_params() {
                    self.bindings.remove_type(&type_param.name);
                }
                result
            }
            AttributesTypeArgs::Concrete(concrete_types) => {
                let instance_type =
                    potential.resolve(concrete_types.clone(), &attributes_statement.name_token)?;
                let datatype = self
                    .check_can_add_attributes(&attributes_statement.name_token, &instance_type)?
                    .clone();

                self.check_type_attribute_names_available(&datatype, &attributes_statement.body)?;

                for substatement in &attributes_statement.body.statements {
                    match &substatement.statement {
                        StatementInfo::Let(let_statement) => {
                            self.add_let_statement(
                                project,
                                substatement,
                                DefinedName::datatype_specific_attr_defined(
                                    defining_module,
                                    datatype.clone(),
                                    &concrete_types,
                                    let_statement.name_token.text(),
                                ),
                                let_statement,
                                let_statement.name_token.range(),
                                None,
                            )?;
                        }
                        StatementInfo::VariableSatisfy(variable_satisfy_statement) => {
                            let datatype = datatype.clone();
                            let concrete_types = concrete_types.clone();
                            self.add_variable_satisfy_statement_named(
                                project,
                                substatement,
                                variable_satisfy_statement,
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
                        StatementInfo::FunctionSatisfy(function_satisfy_statement) => {
                            self.add_function_satisfy_statement_named(
                                project,
                                substatement,
                                function_satisfy_statement,
                                DefinedName::datatype_specific_attr_defined(
                                    defining_module,
                                    datatype.clone(),
                                    &concrete_types,
                                    function_satisfy_statement.name_token.text(),
                                ),
                                None,
                            )?;
                        }
                        StatementInfo::Define(define_statement) => {
                            self.add_define_statement(
                                project,
                                substatement,
                                DefinedName::datatype_specific_attr_defined(
                                    defining_module,
                                    datatype.clone(),
                                    &concrete_types,
                                    define_statement.name_token.text(),
                                ),
                                Some(&instance_type),
                                None,
                                define_statement,
                                define_statement.name_token.range(),
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
        project: &dyn ProjectLookup,
        attributes_statement: &AttributesStatement,
        typeclass: crate::elaborator::acorn_type::Typeclass,
    ) -> error::Result<()> {
        let defining_module = self.module_id;
        if !attributes_statement.type_params.is_empty() {
            return Err(attributes_statement.type_params[0]
                .name
                .error("typeclass attributes do not support type parameters"));
        }

        let instance_name_token = attributes_statement.instance_name.as_ref().ok_or_else(|| {
            attributes_statement.name_token.error(
                "typeclass attributes require an instance name (e.g., 'attributes M: Magma')",
            )
        })?;

        let instance_name = instance_name_token.text();
        let type_param = crate::elaborator::acorn_type::TypeParam {
            name: instance_name.to_string(),
            typeclass: Some(typeclass.clone()),
        };
        let instance_type = self.bindings.add_arbitrary_type(type_param.clone());
        let family_scope =
            DatatypeFamilyScope::new(Telescope::new(vec![FamilyParam::Type(type_param)]));

        let result = (|| {
            self.check_typeclass_attribute_names_available(&typeclass, &attributes_statement.body)?;
            for substatement in &attributes_statement.body.statements {
                match &substatement.statement {
                    StatementInfo::Let(let_statement) => {
                        self.add_let_statement(
                            project,
                            substatement,
                            DefinedName::typeclass_attr_defined(
                                defining_module,
                                &typeclass,
                                let_statement.name_token.text(),
                            ),
                            let_statement,
                            let_statement.name_token.range(),
                            Some(&family_scope),
                        )?;
                    }
                    StatementInfo::VariableSatisfy(variable_satisfy_statement) => {
                        let typeclass = typeclass.clone();
                        self.add_variable_satisfy_statement_named(
                            project,
                            substatement,
                            variable_satisfy_statement,
                            Some(&family_scope),
                            move |name| {
                                DefinedName::typeclass_attr_defined(
                                    defining_module,
                                    &typeclass,
                                    name,
                                )
                            },
                        )?;
                    }
                    StatementInfo::FunctionSatisfy(function_satisfy_statement) => {
                        self.add_function_satisfy_statement_named(
                            project,
                            substatement,
                            function_satisfy_statement,
                            DefinedName::typeclass_attr_defined(
                                defining_module,
                                &typeclass,
                                function_satisfy_statement.name_token.text(),
                            ),
                            Some(&family_scope),
                        )?;
                    }
                    StatementInfo::Define(define_statement) => {
                        self.add_define_statement(
                            project,
                            substatement,
                            DefinedName::typeclass_attr_defined(
                                defining_module,
                                &typeclass,
                                define_statement.name_token.text(),
                            ),
                            Some(&instance_type),
                            Some(&family_scope),
                            define_statement,
                            define_statement.name_token.range(),
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
        })();

        self.bindings.remove_type(instance_name);
        result
    }
}

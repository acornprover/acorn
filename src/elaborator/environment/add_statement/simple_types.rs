use super::*;
use crate::elaborator::acorn_type::{PotentialType, UnresolvedType};

impl Environment {
    fn canonicalize_alias_template(
        template: &AcornType,
        source_names: &[String],
        type_params: &[TypeParam],
    ) -> AcornType {
        let replacements: Vec<_> = type_params
            .iter()
            .enumerate()
            .zip(source_names.iter())
            .map(|((i, param), source_name)| {
                (
                    source_name.clone(),
                    AcornType::Arbitrary(TypeParam {
                        name: format!("T{}", i),
                        typeclass: param.typeclass.clone(),
                    }),
                )
            })
            .collect();
        template.instantiate(&replacements)
    }

    /// Adds a type statement to the environment.
    pub(super) fn add_type_statement(
        &mut self,
        project: &dyn ProjectLookup,
        statement: &Statement,
        type_statement: &TypeStatement,
    ) -> error::Result<()> {
        self.add_other_lines(statement);
        self.bindings
            .check_typename_available(type_statement.name_token.text(), statement)?;
        let family_params = self
            .evaluator(project)
            .evaluate_family_params(&type_statement.type_params)?;
        if type_statement.type_expr.is_axiom() {
            let doc_comments = self.take_doc_comments();
            let definition_string = Some(statement.to_string());
            self.bindings.add_potential_type_with_family_params(
                &type_statement.name_token,
                family_params.canonical_kinds(),
                doc_comments,
                Some(type_statement.name_token.range()),
                definition_string,
            );
        } else {
            let family_param_kinds = family_params.canonical_kinds();
            let type_params = family_params.type_params().to_vec();
            if type_params.len() != family_params.len() {
                return Err(type_statement.name_token.error(
                    "parameterized type aliases with value parameters are not supported yet",
                ));
            }

            for param in &type_params {
                self.bindings.add_arbitrary_type(param.clone());
            }
            let potential = self
                .evaluator(project)
                .evaluate_potential_type(&type_statement.type_expr);
            for param in &type_params {
                self.bindings.remove_type(&param.name);
            }
            let potential = potential?;
            let potential = match (type_params.is_empty(), potential) {
                (true, potential) => potential,
                (false, PotentialType::Resolved(template)) => {
                    PotentialType::Unresolved(UnresolvedType {
                        name: type_statement.name_token.text().to_string(),
                        params: family_param_kinds.clone(),
                        template: Self::canonicalize_alias_template(
                            &template,
                            &type_params
                                .iter()
                                .map(|param| param.name.clone())
                                .collect::<Vec<_>>(),
                            &type_params,
                        ),
                    })
                }
                (false, PotentialType::Unresolved(ut)) => {
                    if ut.has_value_params() {
                        return Err(type_statement.type_expr.error(
                            "parameterized type aliases can only target type-only families",
                        ));
                    }
                    if ut.params.len() != type_params.len() {
                        return Err(type_statement.type_expr.error(
                            "parameterized type aliases must explicitly apply their target type parameters",
                        ));
                    }
                    PotentialType::Unresolved(UnresolvedType {
                        name: type_statement.name_token.text().to_string(),
                        params: family_param_kinds.clone(),
                        template: Self::canonicalize_alias_template(
                            &ut.template,
                            &(0..type_params.len())
                                .map(|i| format!("T{}", i))
                                .collect::<Vec<_>>(),
                            &type_params,
                        ),
                    })
                }
            };
            self.bindings.add_type_alias(
                type_statement.name_token.text(),
                potential,
                &type_statement.name_token,
            )?;
        };
        Ok(())
    }

    /// Adds a numerals statement to the environment.
    pub(super) fn add_numerals_statement(
        &mut self,
        project: &dyn ProjectLookup,
        statement: &Statement,
        numerals_statement: &NumeralsStatement,
    ) -> error::Result<()> {
        self.add_other_lines(statement);
        let acorn_type = self
            .evaluator(project)
            .evaluate_type(&numerals_statement.type_expr)?;
        if let AcornType::Data(datatype, params) = acorn_type {
            if !params.is_empty() {
                return Err(numerals_statement
                    .type_expr
                    .error("numerals type cannot have type parameters"));
            }
            self.bindings.set_numerals(datatype);
            Ok(())
        } else {
            Err(numerals_statement
                .type_expr
                .error("numerals type must be a data type"))
        }
    }
}

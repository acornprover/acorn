use super::*;

impl Environment {
    /// Adds a type statement to the environment.
    pub(super) fn add_type_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        ts: &TypeStatement,
    ) -> error::Result<()> {
        self.add_other_lines(statement);
        self.bindings
            .check_typename_available(ts.name_token.text(), statement)?;
        if ts.type_expr.is_axiom() {
            let doc_comments = self.take_doc_comments();
            let definition_string = Some(statement.to_string());
            self.bindings.add_potential_type(
                &ts.name_token,
                vec![],
                doc_comments,
                Some(ts.name_token.range()),
                definition_string,
            );
        } else {
            let potential = self
                .evaluator(project)
                .evaluate_potential_type(&ts.type_expr)?;
            self.bindings
                .add_type_alias(ts.name_token.text(), potential, &ts.name_token)?;
        };
        Ok(())
    }

    /// Adds a numerals statement to the environment.
    pub(super) fn add_numerals_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        ds: &NumeralsStatement,
    ) -> error::Result<()> {
        self.add_other_lines(statement);
        let acorn_type = self.evaluator(project).evaluate_type(&ds.type_expr)?;
        if let AcornType::Data(datatype, params) = acorn_type {
            if !params.is_empty() {
                return Err(ds
                    .type_expr
                    .error("numerals type cannot have type parameters"));
            }
            self.bindings.set_numerals(datatype);
            Ok(())
        } else {
            Err(ds.type_expr.error("numerals type must be a data type"))
        }
    }
}

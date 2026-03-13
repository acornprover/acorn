use super::*;

impl Environment {
    /// Adds an import statement to the environment.
    pub(super) fn add_import_statement(
        &mut self,
        project: &mut Project,
        statement: &Statement,
        is: &ImportStatement,
    ) -> error::Result<()> {
        self.add_other_lines(statement);

        if is.names.is_empty() {
            return Err(statement.error(
                "import statement must specify names to import. use 'from foo import bar' syntax",
            ));
        }

        let full_name_vec: Vec<_> = is.components.iter().map(|t| t.text().to_string()).collect();
        let full_name = full_name_vec.join(".");
        let module_id = match project.load_module_by_name(&full_name) {
            Ok(module_id) => module_id,
            Err(ImportError::NotFound(message)) => {
                return Err(statement.error(&message));
            }
            Err(ImportError::Circular(module_id)) => {
                return Err(Error::circular(
                    module_id,
                    &statement.first_token,
                    &statement.last_token,
                    &format!("circular import of '{}' module", full_name),
                ));
            }
        };
        let bindings = match project.get_bindings(module_id) {
            None => {
                return Err(Error::indirect(
                    &statement.first_token,
                    &statement.last_token,
                    &format!("error in '{}' module", full_name),
                ));
            }
            Some(bindings) => bindings,
        };

        self.bindings
            .import_module(full_name_vec, &bindings, &statement.first_token)?;

        if let Some(last_component) = is.components.last() {
            self.token_map
                .track_token(last_component, &NamedEntity::Module(module_id));
        }

        for name in &is.names {
            let entity = self.bindings.import_name(project, module_id, name)?;
            self.token_map.track_token(name, &entity);
        }

        Ok(())
    }
}

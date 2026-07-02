use super::*;
use crate::elaborator::environment::ImportBindingInfo;
use crate::syntax::token_map::TokenKey;

impl Environment {
    /// Adds an import statement to the environment.
    pub(super) fn add_import_statement(
        &mut self,
        project: &dyn ProjectLookup,
        statement: &Statement,
        import_statement: &ImportStatement,
    ) -> error::Result<()> {
        self.add_other_lines(statement);

        if import_statement.names.is_empty() {
            return Err(statement.error(
                "import statement must specify names to import. use 'from foo import bar' syntax",
            ));
        }

        let module_path: Vec<_> = import_statement
            .components
            .iter()
            .map(|t| t.text().to_string())
            .collect();
        let module_name = module_path.join(".");
        let module_id = match project.get_loaded_module_id_by_name(&module_name) {
            Ok(module_id) => module_id,
            Err(ImportError::NotFound(message)) => {
                return Err(statement.error(&message));
            }
            Err(ImportError::Circular(module_id)) => {
                return Err(Error::circular(
                    module_id,
                    &statement.first_token,
                    &statement.last_token,
                    &format!("circular import of '{}' module", module_name),
                ));
            }
        };
        let bindings = match project.get_bindings(module_id) {
            None => {
                return Err(Error::indirect(
                    &statement.first_token,
                    &statement.last_token,
                    &format!("error in '{}' module", module_name),
                ));
            }
            Some(bindings) => bindings,
        };
        if let Err(message) = project.validate_import_visibility(self.module_id, module_id) {
            return Err(statement.error(&message));
        }

        self.bindings
            .import_module(module_path, &bindings, &statement.first_token)?;

        if let Some(last_component) = import_statement.components.last() {
            self.token_map
                .track_token(last_component, &NamedEntity::Module(module_id));
        }

        for name in &import_statement.names {
            let entity = self.bindings.import_name(project, module_id, name)?;
            self.token_map.track_token(name, &entity);
            self.import_bindings.push(ImportBindingInfo {
                key: TokenKey::new(name.line_number, name.start, name.len),
                line: name.line_number + 1,
                column: name.start + 1,
                import_name: name.text().to_string(),
                module_name: module_name.clone(),
                module_id,
                entity,
            });
        }

        Ok(())
    }
}

use std::collections::HashMap;
use std::fmt;
use std::io::Write;
use std::path::Path;

use crate::elaborator::acorn_type::{Datatype, Typeclass};
use crate::elaborator::environment::Environment;
use crate::elaborator::names::ConstantName;
use crate::module::{ModuleDescriptor, ModuleId};
use crate::project::Project;
use crate::syntax::token::Token;

#[derive(Debug)]
pub enum DocError {
    IoError(std::io::Error),
    DirectoryNotFound(String),
    NotADirectory(String),
    MissingCategoryFile(String),
    DocumentationConflict {
        type_name: String,
        first_module: String,
        second_module: String,
    },
}

impl fmt::Display for DocError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DocError::IoError(e) => write!(f, "{}", e),
            DocError::DirectoryNotFound(path) => write!(f, "Directory '{}' does not exist", path),
            DocError::NotADirectory(path) => write!(f, "'{}' is not a directory", path),
            DocError::MissingCategoryFile(path) => write!(
                f,
                "Directory '{}' is missing required _category_.json file",
                path
            ),
            DocError::DocumentationConflict {
                type_name,
                first_module,
                second_module,
            } => {
                write!(f, "Documentation conflict for type '{}': both modules '{}' and '{}' appear to be authoritative", 
                       type_name, first_module, second_module)
            }
        }
    }
}

impl From<std::io::Error> for DocError {
    fn from(err: std::io::Error) -> Self {
        DocError::IoError(err)
    }
}

pub struct DocGenerator<'a> {
    project: &'a Project,
}

impl<'a> DocGenerator<'a> {
    pub fn new(project: &'a Project) -> Self {
        DocGenerator { project }
    }

    /// Checks if we should document an entity (type or typeclass) from this module.
    /// Returns Ok(true) if we should document it, Ok(false) if we should skip it,
    /// or an error if there's a conflict.
    fn should_document_entity(
        entity_name: &str,
        canonical_name: &str,
        entity_module_id: ModuleId,
        current_module_id: ModuleId,
        descriptor: &ModuleDescriptor,
        documented_names: &mut HashMap<String, String>,
    ) -> Result<bool, DocError> {
        // Only document if the entity name matches the canonical name
        // This ensures we're using the canonical name
        if entity_name != canonical_name {
            return Ok(false);
        }

        // Only document if this is the authoritative source
        // Either the module that defines the entity, or a module whose name matches
        if current_module_id != entity_module_id
            && !descriptor.is_authoritative_name(canonical_name)
        {
            return Ok(false);
        }

        // Check if we've already documented this entity
        if let Some(first_module) = documented_names.get(entity_name) {
            return Err(DocError::DocumentationConflict {
                type_name: entity_name.to_string(),
                first_module: first_module.clone(),
                second_module: descriptor.to_string(),
            });
        }

        // Record that we're documenting this entity from this module
        documented_names.insert(entity_name.to_string(), descriptor.to_string());

        Ok(true)
    }

    /// Helper function to write the header section of a documentation file.
    /// This includes the title, definition, doc comments, GitHub link, and horizontal rule.
    fn write_header(
        &self,
        file: &mut std::fs::File,
        title: &str,
        definition_string: Option<&String>,
        doc_comments: Option<&Vec<String>>,
        module_id: crate::module::ModuleId,
    ) -> Result<(), DocError> {
        writeln!(file, "# {}", title)?;

        // Write definition string if it exists
        if let Some(definition) = definition_string {
            writeln!(file)?;
            writeln!(file, "```acorn")?;
            writeln!(file, "{}", definition)?;
            writeln!(file, "```")?;
        }

        // Write doc comments if they exist
        if let Some(comments) = doc_comments {
            writeln!(file)?;
            for comment in comments {
                writeln!(file, "{}", comment)?;
            }
        } else {
            eprintln!("warning: no doc comments for '{}'", title);
        }

        // Add GitHub link
        if let Some(github_link) = self.project.github_link(module_id) {
            writeln!(file)?;
            writeln!(file, "[GitHub]({})", github_link)?;
        }

        // Add horizontal rule
        writeln!(file)?;
        writeln!(file, "---")?;

        Ok(())
    }

    /// Helper function to write a section for an attribute with its definition and doc comments.
    /// This handles the common pattern of looking up a constant name's environment and documentation.
    fn write_section(
        &self,
        file: &mut std::fs::File,
        env: &Environment,
        constant_name: &ConstantName,
        section_name: &str,
    ) -> Result<(), DocError> {
        // Get the environment for this constant name
        let Some(def_env) = self.project.get_env_for_name(env, constant_name) else {
            return Ok(());
        };

        // Get doc comments and definition string
        let doc_comments = def_env.bindings.get_constant_doc_comments(constant_name);
        let definition_string = def_env
            .bindings
            .get_constant_definition_string(constant_name);

        // Write the section header
        writeln!(file, "## {}", section_name)?;

        // Check if this is inherited
        if let Some((_base_module_id, base_name)) = env.bindings.resolve_name(constant_name) {
            if &base_name != constant_name {
                if let Some((_, base, attr)) = base_name.as_attribute() {
                    writeln!(file, "Inherited from [{}](../{}/#{}).", base, base, attr)?;
                    return Ok(());
                }
            }
        }

        // Write definition string if it exists
        if let Some(definition) = definition_string {
            writeln!(file)?;
            writeln!(file, "```acorn")?;
            writeln!(file, "{}", definition)?;
            writeln!(file, "```")?;
        }

        // Write doc comments if they exist
        if let Some(comments) = doc_comments {
            writeln!(file)?;
            for comment in comments {
                writeln!(file, "{}", comment)?;
            }
        } else {
            eprintln!("warning: no doc comments for '{}'", constant_name);
        }

        Ok(())
    }

    /// Documents a type by writing all its methods to a markdown file.
    /// env: The environment with the canonical import location of the type
    /// type_name: The name of the type (e.g., "Int")
    /// datatype: The datatype to document
    /// filename: Where to write the documentation
    pub fn document_type(
        &self,
        env: &Environment,
        type_name: &str,
        datatype: &Datatype,
        filename: impl AsRef<Path>,
    ) -> Result<(), DocError> {
        let mut methods = env.bindings.get_datatype_attributes(datatype);
        // Filter out attributes that are wholly numeric or reserved names
        methods
            .retain(|name| !name.chars().all(|c| c.is_numeric()) && !Token::is_reserved_name(name));
        methods.sort();
        let mut file = std::fs::File::create(filename)?;

        // Write header
        let doc_comments = self.project.get_datatype_doc_comments(datatype);
        let definition_string = self.project.get_datatype_definition_string(datatype);
        self.write_header(
            &mut file,
            type_name,
            definition_string,
            doc_comments,
            env.module_id,
        )?;

        // Write methods
        for method_name in methods {
            let defining_module = env
                .bindings
                .get_datatype_attribute_module(datatype, &method_name)
                .unwrap_or(datatype.module_id);
            let constant_name =
                ConstantName::datatype_attr(defining_module, datatype.clone(), &method_name);
            self.write_section(&mut file, env, &constant_name, &method_name)?;
        }

        Ok(())
    }

    /// Documents a typeclass by writing all its attributes to a markdown file.
    /// env: The environment with the canonical import location of the typeclass
    /// typeclass_name: The name of the typeclass (e.g., "Ring")
    /// typeclass: The typeclass to document
    /// filename: Where to write the documentation
    pub fn document_typeclass(
        &self,
        env: &Environment,
        typeclass_name: &str,
        typeclass: &Typeclass,
        filename: impl AsRef<Path>,
    ) -> Result<(), DocError> {
        let attributes = env
            .bindings
            .get_typeclass_attributes(typeclass, self.project);
        let mut attribute_names: Vec<String> = attributes.keys().cloned().collect();
        // Filter out attributes that are wholly numeric or reserved names
        attribute_names
            .retain(|name| !name.chars().all(|c| c.is_numeric()) && !Token::is_reserved_name(name));
        attribute_names.sort();
        let mut file = std::fs::File::create(filename)?;

        // Write header
        let doc_comments = self.project.get_typeclass_doc_comments(typeclass);
        let definition_string = self.project.get_typeclass_definition_string(typeclass);
        self.write_header(
            &mut file,
            typeclass_name,
            definition_string,
            doc_comments,
            env.module_id,
        )?;

        // Write attributes
        for attribute_name in attribute_names {
            let constant_name = ConstantName::typeclass_attr(typeclass.clone(), &attribute_name);
            self.write_section(&mut file, env, &constant_name, &attribute_name)?;
        }

        Ok(())
    }

    /// Generates documentation for all types in all top-level modules.
    /// Creates one file named "Typename.md" for each type in the doc_root directory.
    /// Returns the number of files created.
    pub fn generate(&self, doc_root: impl AsRef<Path>) -> Result<usize, DocError> {
        let doc_root = doc_root.as_ref();

        if !doc_root.exists() {
            return Err(DocError::DirectoryNotFound(doc_root.display().to_string()));
        }
        if !doc_root.is_dir() {
            return Err(DocError::NotADirectory(doc_root.display().to_string()));
        }

        // Check for _category_.json file
        let category_file = doc_root.join("_category_.json");
        if !category_file.exists() {
            return Err(DocError::MissingCategoryFile(
                doc_root.display().to_string(),
            ));
        }

        // Remove all existing .md files in the directory
        for entry in std::fs::read_dir(doc_root)? {
            let entry = entry?;
            let path = entry.path();
            if path.is_file() && path.extension().and_then(|s| s.to_str()) == Some("md") {
                std::fs::remove_file(path)?;
            }
        }

        let mut documented_names: HashMap<String, String> = HashMap::new();
        let mut file_count = 0;

        // Iterate over all modules
        let mut modules: Vec<_> = self.project.iter_modules().collect();
        modules.sort();
        for (descriptor, module_id) in modules {
            // Skip non-top-level modules
            if !descriptor.is_top_level() {
                continue;
            }

            // Get the module environment
            let env = match self.project.get_env_by_id(module_id) {
                Some(env) => env,
                None => continue, // Skip if we can't get the environment
            };

            // Iterate over all types in this module
            for (type_name, potential_type) in env.bindings.iter_types() {
                // Extract the base datatype
                let datatype = match potential_type.as_base_datatype() {
                    Some(dt) => dt,
                    None => continue, // Skip types without a base datatype
                };

                // Check if we should document this datatype
                if !Self::should_document_entity(
                    type_name,
                    &datatype.name,
                    datatype.module_id,
                    module_id,
                    &descriptor,
                    &mut documented_names,
                )? {
                    continue;
                }

                // Create the output filename
                let filename = doc_root.join(format!("{}.md", type_name));

                self.document_type(env, type_name, datatype, filename)?;
                file_count += 1;
            }

            // Iterate over all typeclasses in this module
            for (typeclass_name, typeclass) in env.bindings.iter_typeclasses() {
                // Check if we should document this typeclass
                if !Self::should_document_entity(
                    typeclass_name,
                    &typeclass.name,
                    typeclass.module_id,
                    module_id,
                    &descriptor,
                    &mut documented_names,
                )? {
                    continue;
                }

                // Create the output filename
                let filename = doc_root.join(format!("{}.md", typeclass_name));

                self.document_typeclass(env, typeclass_name, typeclass, filename)?;
                file_count += 1;
            }
        }

        Ok(file_count)
    }
}

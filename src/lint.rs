use std::collections::{BTreeSet, HashSet};
use std::fmt;

use crate::elaborator::acorn_type::{AcornType, Datatype, Typeclass};
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::environment::Environment;
use crate::elaborator::named_entity::NamedEntity;
use crate::elaborator::names::ConstantName;
use crate::module::{ModuleDescriptor, ModuleId};
use crate::project::Project;
use crate::syntax::statement::{Body, Statement, StatementInfo};
use crate::syntax::token::{Token, TokenIter};
use crate::syntax::token_map::TokenKey;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LintWarning {
    pub path: String,
    pub line: u32,
    pub column: u32,
    pub import_name: String,
    pub module_name: String,
}

impl fmt::Display for LintWarning {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}:{}:{}: unused import '{}' from {}",
            self.path, self.line, self.column, self.import_name, self.module_name
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum EntityKey {
    Constant(ConstantName),
    Datatype(Datatype),
    Typeclass(Typeclass),
    Module(ModuleId),
    Other(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ImportBinding {
    key: TokenKey,
    line: u32,
    column: u32,
    import_name: String,
    module_name: String,
    top_level: bool,
}

pub fn lint_project_targets(project: &Project) -> Result<Vec<LintWarning>, String> {
    let targets: Vec<_> = project.targets.iter().cloned().collect();
    lint_targets(project, &targets)
}

pub fn lint_targets(
    project: &Project,
    targets: &[ModuleDescriptor],
) -> Result<Vec<LintWarning>, String> {
    let mut targets = targets.to_vec();
    targets.sort();

    let mut warnings = Vec::new();
    for descriptor in &targets {
        warnings.extend(lint_module(project, descriptor)?);
    }
    warnings.sort();
    Ok(warnings)
}

fn lint_module(
    project: &Project,
    descriptor: &ModuleDescriptor,
) -> Result<Vec<LintWarning>, String> {
    let env = project
        .get_env(descriptor)
        .ok_or_else(|| format!("could not load module '{}'", descriptor))?;
    let path = project
        .path_from_descriptor(descriptor)
        .map_err(|e| e.to_string())?;
    let source = project.read_file(&path).map_err(|e| e.to_string())?;
    let statements = parse_statements(&source)?;
    let allow_default_reexports = path.file_name().and_then(|name| name.to_str())
        == Some("default.ac")
        && is_reexport_default_module(&statements);

    let mut imports = Vec::new();
    collect_imports(&statements, &mut imports, true);

    let import_keys: BTreeSet<_> = imports.iter().map(|import| import.key).collect();
    let mut used_entities = HashSet::new();
    collect_used_entities(env, &import_keys, &mut used_entities);

    let display_path = project.display_path(descriptor);
    let mut warnings = Vec::new();
    for import in imports {
        if allow_default_reexports && import.top_level {
            continue;
        }
        let entity = find_tracked_entity(env, import.key).ok_or_else(|| {
            format!(
                "could not resolve imported name '{}' at {}:{}:{}",
                import.import_name, display_path, import.line, import.column
            )
        })?;
        if !used_entities.contains(&entity_key(entity)) {
            warnings.push(LintWarning {
                path: display_path.clone(),
                line: import.line,
                column: import.column,
                import_name: import.import_name,
                module_name: import.module_name,
            });
        }
    }
    Ok(warnings)
}

fn parse_statements(source: &str) -> Result<Vec<Statement>, String> {
    let mut tokens = TokenIter::new(Token::scan(source));
    let mut statements = Vec::new();
    loop {
        match Statement::parse(&mut tokens, false, false) {
            Ok((Some(statement), _)) => statements.push(statement),
            Ok((None, _)) => return Ok(statements),
            Err(e) => return Err(e.to_string()),
        }
    }
}

fn is_reexport_default_module(statements: &[Statement]) -> bool {
    statements.iter().all(|statement| {
        matches!(
            statement.statement,
            StatementInfo::Import(_) | StatementInfo::DocComment(_)
        )
    })
}

fn collect_imports(statements: &[Statement], imports: &mut Vec<ImportBinding>, top_level: bool) {
    for statement in statements {
        if let StatementInfo::Import(import_statement) = &statement.statement {
            let module_name = import_statement
                .components
                .iter()
                .map(|component| component.text())
                .collect::<Vec<_>>()
                .join(".");
            for name in &import_statement.names {
                imports.push(ImportBinding {
                    key: TokenKey::new(name.line_number, name.start, name.len),
                    line: name.line_number + 1,
                    column: name.start + 1,
                    import_name: name.text().to_string(),
                    module_name: module_name.clone(),
                    top_level,
                });
            }
        }
        collect_nested_imports(statement, imports);
    }
}

fn collect_nested_imports(statement: &Statement, imports: &mut Vec<ImportBinding>) {
    match &statement.statement {
        StatementInfo::Theorem(ts) => {
            if let Some(body) = &ts.body {
                collect_body_imports(body, imports);
            }
        }
        StatementInfo::ForAll(fas) => collect_body_imports(&fas.body, imports),
        StatementInfo::If(ifs) => {
            collect_body_imports(&ifs.body, imports);
            if let Some(else_body) = &ifs.else_body {
                collect_body_imports(else_body, imports);
            }
        }
        StatementInfo::FunctionSatisfy(fss) => {
            if let Some(body) = &fss.body {
                collect_body_imports(body, imports);
            }
        }
        StatementInfo::Structure(ss) => {
            if let Some(body) = &ss.body {
                collect_body_imports(body, imports);
            }
        }
        StatementInfo::Attributes(ats) => collect_body_imports(&ats.body, imports),
        StatementInfo::Match(ms) => {
            for (_, body) in &ms.cases {
                collect_body_imports(body, imports);
            }
        }
        StatementInfo::Instance(instance) => {
            if let Some(definitions) = &instance.definitions {
                collect_body_imports(definitions, imports);
            }
            if let Some(body) = &instance.body {
                collect_body_imports(body, imports);
            }
        }
        StatementInfo::Destructuring(ds) => {
            if let Some(body) = &ds.body {
                collect_body_imports(body, imports);
            }
        }
        _ => {}
    }
}

fn collect_body_imports(body: &Body, imports: &mut Vec<ImportBinding>) {
    collect_imports(&body.statements, imports, false);
}

fn collect_used_entities(
    env: &Environment,
    import_keys: &BTreeSet<TokenKey>,
    used_entities: &mut HashSet<EntityKey>,
) {
    for (key, token_info) in env.token_map.iter() {
        if !import_keys.contains(key) {
            used_entities.insert(entity_key(&token_info.entity));
        }
    }

    for node in &env.nodes {
        if let Some(block) = node.get_block() {
            collect_used_entities(&block.env, import_keys, used_entities);
        }
    }
}

fn find_tracked_entity(env: &Environment, key: TokenKey) -> Option<&NamedEntity> {
    for (candidate_key, token_info) in env.token_map.iter() {
        if *candidate_key == key {
            return Some(&token_info.entity);
        }
    }

    for node in &env.nodes {
        if let Some(block) = node.get_block() {
            if let Some(entity) = find_tracked_entity(&block.env, key) {
                return Some(entity);
            }
        }
    }

    None
}

fn entity_key(entity: &NamedEntity) -> EntityKey {
    match entity {
        NamedEntity::Value(value) => EntityKey::value(value),
        NamedEntity::Type(acorn_type) => EntityKey::acorn_type(acorn_type),
        NamedEntity::Module(module_id) => EntityKey::Module(*module_id),
        NamedEntity::Typeclass(typeclass) => EntityKey::Typeclass(typeclass.clone()),
        NamedEntity::UnresolvedValue(unresolved) => EntityKey::Constant(unresolved.name.clone()),
        NamedEntity::UnresolvedType(unresolved) => EntityKey::Datatype(unresolved.datatype.clone()),
    }
}

impl EntityKey {
    fn value(value: &AcornValue) -> Self {
        if let Some(name) = value
            .as_simple_constant()
            .or_else(|| value.is_named_function_call())
        {
            EntityKey::Constant(name.clone())
        } else {
            EntityKey::Other(format!("value:{value}"))
        }
    }

    fn acorn_type(acorn_type: &AcornType) -> Self {
        match acorn_type {
            AcornType::Data(datatype, _) => EntityKey::Datatype(datatype.clone()),
            _ => EntityKey::Other(format!("type:{acorn_type}")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::project::Project;

    #[test]
    fn test_reports_unused_import() {
        let mut project = Project::new_mock();
        project.mock("/mock/foo.ac", "let bar: Bool = true\n");
        project.mock(
            "/mock/main.ac",
            "from foo import bar\n\ntheorem goal { true }\n",
        );
        project.add_target_by_name("main").unwrap();

        assert!(project.errors().is_empty());

        let warnings = lint_targets(&project, &[ModuleDescriptor::name("main")]).unwrap();
        assert_eq!(warnings.len(), 1);
        assert_eq!(warnings[0].path, "main.ac");
        assert_eq!(warnings[0].line, 1);
        assert_eq!(warnings[0].column, 17);
        assert_eq!(warnings[0].import_name, "bar");
        assert_eq!(warnings[0].module_name, "foo");
    }

    #[test]
    fn test_import_used_in_child_block_is_not_reported() {
        let mut project = Project::new_mock();
        project.mock("/mock/foo.ac", "let bar: Bool = true\n");
        project.mock(
            "/mock/main.ac",
            "from foo import bar\n\nif true {\n    bar\n}\n",
        );
        project.add_target_by_name("main").unwrap();

        assert!(project.errors().is_empty());
        let warnings = lint_targets(&project, &[ModuleDescriptor::name("main")]).unwrap();
        assert!(warnings.is_empty());
    }

    #[test]
    fn test_dependency_warnings_are_not_reported_for_non_targets() {
        let mut project = Project::new_mock();
        project.mock("/mock/base.ac", "let x: Bool = true\n");
        project.mock("/mock/foo.ac", "from base import x\nlet y: Bool = true\n");
        project.mock("/mock/main.ac", "from foo import y\nlet z: Bool = y\n");
        project.add_target_by_name("main").unwrap();

        assert!(project.errors().is_empty());
        let warnings = lint_targets(&project, &[ModuleDescriptor::name("main")]).unwrap();
        assert!(warnings.is_empty());
    }

    #[test]
    fn test_default_module_allows_unused_top_level_reexport_import() {
        let mut project = Project::new_mock();
        project.mock("/mock/foo.ac", "let bar: Bool = true\n");
        project.mock("/mock/pkg/default.ac", "from foo import bar\n");
        project.add_target_by_name("pkg").unwrap();

        assert!(project.errors().is_empty());
        let warnings = lint_targets(&project, &[ModuleDescriptor::name("pkg")]).unwrap();
        assert!(warnings.is_empty());
    }

    #[test]
    fn test_non_facade_default_module_still_flags_unused_import() {
        let mut project = Project::new_mock();
        project.mock("/mock/foo.ac", "let bar: Bool = true\n");
        project.mock(
            "/mock/pkg/default.ac",
            "from foo import bar\n\ntheorem goal { true }\n",
        );
        project.add_target_by_name("pkg").unwrap();

        assert!(project.errors().is_empty());
        let warnings = lint_targets(&project, &[ModuleDescriptor::name("pkg")]).unwrap();
        assert_eq!(warnings.len(), 1);
        assert_eq!(warnings[0].path, "pkg/default.ac");
        assert_eq!(warnings[0].import_name, "bar");
    }

    #[test]
    fn test_default_module_still_flags_nested_unused_import() {
        let mut project = Project::new_mock();
        project.mock("/mock/foo.ac", "let bar: Bool = true\n");
        project.mock(
            "/mock/pkg/default.ac",
            "if true {\n    from foo import bar\n}\n",
        );
        project.add_target_by_name("pkg").unwrap();

        assert!(project.errors().is_empty());
        let warnings = lint_targets(&project, &[ModuleDescriptor::name("pkg")]).unwrap();
        assert_eq!(warnings.len(), 1);
        assert_eq!(warnings[0].path, "pkg/default.ac");
        assert_eq!(warnings[0].import_name, "bar");
    }
}

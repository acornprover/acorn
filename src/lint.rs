use std::borrow::Cow;
use std::collections::{BTreeSet, HashSet};
use std::fmt;

use crate::certificate::Certificate;
use crate::elaborator::acorn_type::{
    AcornType, Datatype, DependentTypeArg, FunctionType, TypeParam, Typeclass,
};
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::environment::{Environment, ImportBindingInfo};
use crate::elaborator::lowered_module::LoweredModule;
use crate::elaborator::named_entity::NamedEntity;
use crate::elaborator::names::ConstantName;
use crate::kernel::atom::Atom;
use crate::kernel::certificate_step::CertificateStep;
use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::symbol::Symbol;
use crate::kernel::term::Term;
use crate::module::{ModuleDescriptor, ModuleId};
use crate::project::{PackageRole, Project, ProjectLookup};
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
    let module_descriptor = project
        .get_module_descriptor(env.module_id)
        .unwrap_or(descriptor);
    let mut imports = Vec::new();
    collect_imports(env, &mut imports);

    let import_keys: BTreeSet<_> = imports.iter().map(|import| import.key).collect();
    let mut usage = Usage::default();
    collect_exported_import_usage(env, &mut usage);
    collect_source_token_usage(env, &import_keys, &mut usage);

    let lowered = project
        .get_lowered_module(env.module_id)
        .ok_or_else(|| format!("could not load lowered module '{}'", descriptor))?;
    collect_lowered_module_usage(lowered, &mut usage);
    collect_cached_certificate_usage(project, module_descriptor, lowered, &imports, &mut usage)?;

    let display_path = project.display_path(module_descriptor);
    let mut warnings = Vec::new();
    for import in imports {
        if !usage.import_is_used(import) {
            warnings.push(LintWarning {
                path: display_path.clone(),
                line: import.line,
                column: import.column,
                import_name: import.import_name.clone(),
                module_name: import.module_name.clone(),
            });
        }
    }
    Ok(warnings)
}

fn collect_imports<'a>(env: &'a Environment, imports: &mut Vec<&'a ImportBindingInfo>) {
    imports.extend(env.import_bindings.iter());
    for node in &env.nodes {
        if let Some(block) = node.get_block() {
            collect_imports(&block.env, imports);
        }
    }
}

fn collect_exported_import_usage(env: &Environment, usage: &mut Usage) {
    let exports = env.export_bindings();
    for import in &env.import_bindings {
        if exports.exported_entity_matches(&import.import_name, &import.entity) {
            usage.exact_entities.insert(entity_key(&import.entity));
            usage.conservative_modules.insert(import.module_id);
        }
    }
}

#[derive(Default)]
struct Usage {
    exact_entities: HashSet<EntityKey>,
    conservative_modules: HashSet<ModuleId>,
}

impl Usage {
    fn import_is_used(&self, import: &ImportBindingInfo) -> bool {
        self.exact_entities.contains(&entity_key(&import.entity))
            || self.conservative_modules.contains(&import.module_id)
    }
}

fn collect_source_token_usage(
    env: &Environment,
    import_keys: &BTreeSet<TokenKey>,
    usage: &mut Usage,
) {
    for (key, token_info) in env.token_map.iter() {
        if !import_keys.contains(key) {
            usage.exact_entities.insert(entity_key(&token_info.entity));
        }
    }

    for node in &env.nodes {
        if let Some(block) = node.get_block() {
            collect_source_token_usage(&block.env, import_keys, usage);
        }
    }
}

fn collect_lowered_module_usage(lowered: &LoweredModule, usage: &mut Usage) {
    for fact in lowered.facts() {
        collect_lowered_steps_usage(&fact.steps, &fact.kernel_context, usage);
    }

    for (_, entry) in lowered.goals() {
        collect_lowered_steps_usage(
            &entry.lowered_goal.steps,
            &entry.lowered_goal.kernel_context,
            usage,
        );
    }
}

fn collect_lowered_steps_usage(
    steps: &[crate::kernel::proof_step::ProofStep],
    kernel_context: &KernelContext,
    usage: &mut Usage,
) {
    for step in steps {
        collect_clause_usage(&step.clause, kernel_context, usage);
    }
}

fn collect_cached_certificate_usage(
    project: &Project,
    descriptor: &ModuleDescriptor,
    lowered: &LoweredModule,
    imports: &[&ImportBindingInfo],
    usage: &mut Usage,
) -> Result<(), String> {
    if lowered.goal_count() == 0 {
        return Ok(());
    }
    if project.package_role(lowered.module_id) == PackageRole::Interface
        || project.is_surface_check_target(descriptor)
    {
        return Ok(());
    }

    let cert_store = project.build_cache.get_certificates(descriptor).ok_or_else(|| {
        format!(
            "cannot lint {}: no cached certificates found; run `acorn check` or `acorn verify {}` first",
            project.display_path(descriptor),
            descriptor
        )
    })?;

    for (_, entry) in lowered.goals() {
        let goal = &entry.lowered_goal.goal;
        let mut matching = cert_store
            .certs
            .iter()
            .filter(|cert| cert.goal == goal.name)
            .peekable();
        if matching.peek().is_none() {
            return Err(format!(
                "cannot lint {}: no cached certificate found for goal '{}' at line {}; run `acorn check` or `acorn verify {}` first",
                project.display_path(descriptor),
                goal.name,
                goal.first_line + 1,
                descriptor
            ));
        }

        for cert in matching {
            if cert.proof.steps.is_empty()
                || collect_certificate_trace_usage(
                    cert,
                    project,
                    imports,
                    &entry.bindings,
                    &entry.lowered_goal.kernel_context,
                    usage,
                )
                .is_err()
            {
                mark_all_imports_used(imports, usage);
                return Ok(());
            }
        }
    }

    Ok(())
}

fn collect_certificate_trace_usage(
    cert: &Certificate,
    project: &Project,
    imports: &[&ImportBindingInfo],
    bindings: &BindingMap,
    kernel_context: &KernelContext,
    usage: &mut Usage,
) -> Result<(), String> {
    let mut bindings = Cow::Borrowed(bindings);
    let mut kernel_context = Cow::Borrowed(kernel_context);
    for trace_step in &cert.proof.steps {
        collect_trace_claim_text_usage(&trace_step.claim, imports, usage);
        let step = Certificate::parse_code_line(
            &trace_step.claim,
            project,
            &mut bindings,
            &mut kernel_context,
        )
        .map_err(|e| e.to_string())?;
        collect_certificate_step_usage(&step, kernel_context.as_ref(), usage)?;
    }
    Ok(())
}

fn collect_trace_claim_text_usage(code: &str, imports: &[&ImportBindingInfo], usage: &mut Usage) {
    for import in imports {
        let module_ref = format!("lib({})", import.module_name);
        if code.contains(&import.import_name) || code.contains(&module_ref) {
            usage.exact_entities.insert(entity_key(&import.entity));
            usage.conservative_modules.insert(import.module_id);
        }
    }
}

fn collect_certificate_step_usage(
    step: &CertificateStep,
    kernel_context: &KernelContext,
    usage: &mut Usage,
) -> Result<(), String> {
    match step {
        CertificateStep::Claim(claim) => {
            collect_clause_usage(&claim.normalized_generic_clause(), kernel_context, usage);
            let specialized = claim.normalized_specialized_clause(kernel_context)?;
            collect_clause_usage(&specialized, kernel_context, usage);
        }
        CertificateStep::Satisfy(satisfy) => {
            for param in &satisfy.type_params {
                collect_type_param_usage(param, usage);
            }
            for (_, arg_type) in &satisfy.arguments {
                collect_acorn_type_usage(arg_type, usage);
            }
            collect_acorn_type_usage(&satisfy.return_type, usage);
            collect_acorn_value_usage(&satisfy.condition, usage);
            collect_clause_usage(
                &satisfy.justification.normalized_generic_clause(),
                kernel_context,
                usage,
            );
            let specialized = satisfy
                .justification
                .normalized_specialized_clause(kernel_context)?;
            collect_clause_usage(&specialized, kernel_context, usage);
            if let Some(clause) = &satisfy.specialized_clause {
                collect_clause_usage(clause, kernel_context, usage);
            }
            for clause in &satisfy.witness_clauses {
                collect_clause_usage(clause, kernel_context, usage);
            }
        }
    }
    Ok(())
}

fn mark_all_imports_used(imports: &[&ImportBindingInfo], usage: &mut Usage) {
    for import in imports {
        usage.exact_entities.insert(entity_key(&import.entity));
        usage.conservative_modules.insert(import.module_id);
    }
}

fn collect_clause_usage(clause: &Clause, kernel_context: &KernelContext, usage: &mut Usage) {
    for var_type in clause.get_local_context().get_var_types().iter().flatten() {
        collect_term_usage(var_type, kernel_context, usage);
    }
    for literal in &clause.literals {
        for atom in literal.iter_atoms() {
            collect_atom_usage(atom, kernel_context, usage);
        }
    }
}

fn collect_term_usage(term: &Term, kernel_context: &KernelContext, usage: &mut Usage) {
    for atom in term.iter_atoms() {
        collect_atom_usage(atom, kernel_context, usage);
    }
}

fn collect_atom_usage(atom: &Atom, kernel_context: &KernelContext, usage: &mut Usage) {
    let Atom::Symbol(symbol) = atom else {
        return;
    };
    match symbol {
        Symbol::GlobalConstant(module_id, atom_id) => {
            if let Some(name) = kernel_context
                .symbol_table
                .try_name_for_global_id(*module_id, *atom_id)
            {
                usage
                    .exact_entities
                    .insert(EntityKey::Constant(name.clone()));
            } else {
                usage.conservative_modules.insert(*module_id);
            }
        }
        Symbol::Type(ground_type_id) => {
            usage
                .conservative_modules
                .insert(ground_type_id.module_id());
        }
        Symbol::Typeclass(typeclass_id) => {
            usage.conservative_modules.insert(typeclass_id.module_id());
        }
        _ => {}
    }
}

fn collect_acorn_value_usage(value: &AcornValue, usage: &mut Usage) {
    value.for_each_constant(&mut |constant| {
        usage
            .exact_entities
            .insert(EntityKey::Constant(constant.name.clone()));
    });
    value.for_each_type(&mut |acorn_type| collect_acorn_type_usage(acorn_type, usage));
}

fn collect_acorn_type_usage(acorn_type: &AcornType, usage: &mut Usage) {
    match acorn_type {
        AcornType::Data(datatype, args) => {
            usage
                .exact_entities
                .insert(EntityKey::Datatype(datatype.clone()));
            usage.conservative_modules.insert(datatype.module_id);
            for arg in args {
                collect_acorn_type_usage(arg, usage);
            }
        }
        AcornType::Family(datatype, args) => {
            usage
                .exact_entities
                .insert(EntityKey::Datatype(datatype.clone()));
            usage.conservative_modules.insert(datatype.module_id);
            for arg in args {
                collect_dependent_type_arg_usage(arg, usage);
            }
        }
        AcornType::Variable(param) | AcornType::Arbitrary(param) => {
            collect_type_param_usage(param, usage);
        }
        AcornType::Function(function_type) => {
            collect_function_type_usage(function_type, usage);
        }
        AcornType::TypeclassConstraint(typeclass) => {
            usage
                .exact_entities
                .insert(EntityKey::Typeclass(typeclass.clone()));
            usage.conservative_modules.insert(typeclass.module_id);
        }
        AcornType::Bool | AcornType::Type0 => {}
    }
}

fn collect_type_param_usage(param: &TypeParam, usage: &mut Usage) {
    if let Some(typeclass) = &param.typeclass {
        usage
            .exact_entities
            .insert(EntityKey::Typeclass(typeclass.clone()));
        usage.conservative_modules.insert(typeclass.module_id);
    }
}

fn collect_function_type_usage(function_type: &FunctionType, usage: &mut Usage) {
    for arg_type in &function_type.arg_types {
        collect_acorn_type_usage(arg_type, usage);
    }
    collect_acorn_type_usage(&function_type.return_type, usage);
}

fn collect_dependent_type_arg_usage(arg: &DependentTypeArg, usage: &mut Usage) {
    match arg {
        DependentTypeArg::Type(acorn_type) => collect_acorn_type_usage(acorn_type, usage),
        DependentTypeArg::Value(value) => collect_acorn_value_usage(value, usage),
    }
}

fn entity_key(entity: &NamedEntity) -> EntityKey {
    match entity {
        NamedEntity::Value(value) => EntityKey::value(value),
        NamedEntity::Type(acorn_type) => EntityKey::acorn_type(acorn_type),
        NamedEntity::Module(module_id) => EntityKey::Module(*module_id),
        NamedEntity::Typeclass(typeclass) => EntityKey::Typeclass(typeclass.clone()),
        NamedEntity::UnresolvedValue(unresolved) => EntityKey::Constant(unresolved.name.clone()),
        NamedEntity::UnresolvedType(unresolved) => {
            EntityKey::acorn_type(&unresolved.to_display_type())
        }
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
    use crate::project::{Project, ProjectConfig, UsageMode};

    #[test]
    fn test_reports_nested_unused_import() {
        let mut project = Project::new_mock_ide();
        project.mock("/mock/foo.ac", "let bar: Bool = true\n");
        project.mock("/mock/main.ac", "if true {\n    from foo import bar\n}\n");
        project.add_target_by_name("main").unwrap();

        assert!(project.errors().is_empty());

        let warnings = lint_targets(&project, &[ModuleDescriptor::name("main")]).unwrap();
        assert_eq!(warnings.len(), 1);
        assert_eq!(warnings[0].path, "main.ac");
        assert_eq!(warnings[0].import_name, "bar");
        assert_eq!(warnings[0].module_name, "foo");
    }

    #[test]
    fn test_import_used_in_child_block_is_not_reported() {
        let mut project = Project::new_mock_ide();
        project.mock("/mock/foo.ac", "let bar: Bool = true\n");
        project.mock(
            "/mock/main.ac",
            "from foo import bar\n\nif true {\n    let baz: Bool = bar\n}\n",
        );
        project.add_target_by_name("main").unwrap();

        assert!(project.errors().is_empty());
        let warnings = lint_targets(&project, &[ModuleDescriptor::name("main")]).unwrap();
        assert!(warnings.is_empty());
    }

    #[test]
    fn test_dependency_warnings_are_not_reported_for_non_targets() {
        let mut project = Project::new_mock_ide();
        project.mock("/mock/base.ac", "let x: Bool = true\n");
        project.mock("/mock/foo.ac", "from base import x\nlet y: Bool = true\n");
        project.mock("/mock/main.ac", "from foo import y\nlet z: Bool = y\n");
        project.add_target_by_name("main").unwrap();

        assert!(project.errors().is_empty());
        let warnings = lint_targets(&project, &[ModuleDescriptor::name("main")]).unwrap();
        assert!(warnings.is_empty());
    }

    #[test]
    fn test_top_level_import_reexport_is_not_reported() {
        let mut project = Project::new_mock_ide();
        project.mock("/mock/foo.ac", "let bar: Bool = true\n");
        project.mock("/mock/pkg/default.ac", "from foo import bar\n");
        project.add_target_by_name("pkg.default").unwrap();

        assert!(project.errors().is_empty());
        let warnings = lint_targets(&project, &[ModuleDescriptor::name("pkg.default")]).unwrap();
        assert!(warnings.is_empty());
    }

    #[test]
    fn test_regular_module_top_level_import_reexport_is_not_reported() {
        let mut project = Project::new_mock_ide();
        project.mock("/mock/foo.ac", "let bar: Bool = true\n");
        project.mock(
            "/mock/pkg/default.ac",
            "from foo import bar\n\nlet baz: Bool = true\n",
        );
        project.add_target_by_name("pkg.default").unwrap();

        assert!(project.errors().is_empty());
        let warnings = lint_targets(&project, &[ModuleDescriptor::name("pkg.default")]).unwrap();
        assert!(warnings.is_empty());
    }

    #[test]
    fn test_default_module_still_flags_nested_unused_import() {
        let mut project = Project::new_mock_ide();
        project.mock("/mock/foo.ac", "let bar: Bool = true\n");
        project.mock(
            "/mock/pkg/default.ac",
            "if true {\n    from foo import bar\n}\n",
        );
        project.add_target_by_name("pkg.default").unwrap();

        assert!(project.errors().is_empty());
        let warnings = lint_targets(&project, &[ModuleDescriptor::name("pkg.default")]).unwrap();
        assert_eq!(warnings.len(), 1);
        assert_eq!(warnings[0].path, "pkg/default.ac");
        assert_eq!(warnings[0].import_name, "bar");
    }

    #[test]
    fn test_module_with_goal_requires_cached_certificate() {
        let mut project = Project::new_mock_ide();
        project.mock("/mock/foo.ac", "let bar: Bool = true\n");
        project.mock(
            "/mock/main.ac",
            "from foo import bar\n\ntheorem goal { true }\n",
        );
        project.add_target_by_name("main").unwrap();

        assert!(project.errors().is_empty());
        let err = lint_targets(&project, &[ModuleDescriptor::name("main")]).unwrap_err();
        assert!(
            err.contains("no cached certificates found"),
            "unexpected lint error: {err}"
        );
    }

    #[test]
    fn test_package_interface_with_goal_does_not_require_cached_certificate() {
        let temp = tempfile::tempdir().expect("temp dir");
        let src_dir = temp.path().join("src");
        let build_dir = temp.path().join("build");
        std::fs::create_dir(&src_dir).expect("src dir");
        std::fs::create_dir(&build_dir).expect("build dir");
        std::fs::create_dir(src_dir.join("pkg")).expect("pkg dir");
        std::fs::write(temp.path().join("acorn.toml"), "").expect("acorn.toml");
        std::fs::write(src_dir.join("shared.ac"), "let fact: Bool = axiom\n").unwrap();
        std::fs::write(
            src_dir.join("pkg/interface.ac"),
            r#"
            from shared import fact

            theorem public {
                fact
            }
            "#,
        )
        .unwrap();
        std::fs::write(
            src_dir.join("pkg/internal.ac"),
            r#"
            from shared import fact

            theorem public {
                fact
            } by {
                fact
            }
            "#,
        )
        .unwrap();

        let mut project = Project::new(
            src_dir,
            build_dir,
            ProjectConfig {
                usage_mode: UsageMode::Ide,
                use_filesystem: true,
                read_cache: true,
                write_cache: false,
                update_version: false,
            },
        )
        .unwrap();
        project.add_target_by_name("pkg").unwrap();

        assert!(project.errors().is_empty());
        let warnings = lint_targets(&project, &[ModuleDescriptor::name("pkg")]).unwrap();
        assert!(warnings.is_empty());
    }

    #[test]
    fn test_cert_only_import_is_not_reported() {
        let temp = tempfile::tempdir().expect("temp dir");
        let src_dir = temp.path().join("src");
        let build_dir = temp.path().join("build");
        let cert_dir = src_dir.join("certs");
        std::fs::create_dir(&src_dir).expect("src dir");
        std::fs::create_dir(&build_dir).expect("build dir");
        std::fs::create_dir(&cert_dir).expect("cert dir");
        std::fs::write(temp.path().join("acorn.toml"), "").expect("acorn.toml");
        std::fs::write(src_dir.join("shared.ac"), "let target: Bool = axiom\n").unwrap();
        std::fs::write(
            src_dir.join("util.ac"),
            "from shared import target\n\ntheorem util_fact { target }\n",
        )
        .unwrap();
        std::fs::write(src_dir.join("unused.ac"), "let junk: Bool = true\n").unwrap();
        std::fs::write(
            src_dir.join("main.ac"),
            r#"
            from shared import target
            from util import util_fact

            if true {
                from unused import junk
            }

            theorem goal { target }
            "#,
        )
        .unwrap();
        std::fs::write(
            cert_dir.join("main.jsonl"),
            r#"{"goal":"goal","p":[{"c":"lib(util).util_fact"}]}"#,
        )
        .unwrap();

        let mut project = Project::new(
            src_dir,
            build_dir,
            ProjectConfig {
                usage_mode: UsageMode::Ide,
                use_filesystem: true,
                read_cache: true,
                write_cache: false,
                update_version: false,
            },
        )
        .unwrap();
        project.add_target_by_name("main").unwrap();

        assert!(project.errors().is_empty());
        let warnings = lint_targets(&project, &[ModuleDescriptor::name("main")]).unwrap();
        assert_eq!(warnings.len(), 1);
        assert_eq!(warnings[0].import_name, "junk");
    }

    #[test]
    fn test_certificate_trace_text_marks_named_import_used() {
        let import = ImportBindingInfo {
            key: TokenKey::new(0, 0, 9),
            line: 1,
            column: 1,
            import_name: "util_fact".to_string(),
            module_name: "util".to_string(),
            module_id: ModuleId(1),
            entity: NamedEntity::Module(ModuleId(1)),
        };
        let mut usage = Usage::default();

        collect_trace_claim_text_usage("lib(util).util_fact", &[&import], &mut usage);

        assert!(usage.import_is_used(&import));
    }
}

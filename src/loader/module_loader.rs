use std::sync::Arc;

use crate::elaborator::environment::Environment;
use crate::elaborator::error;
use crate::elaborator::lowered_module::{LoweredModule, ModuleExport};
use crate::loader::parsed_module::ParsedModule;
use crate::module::ModuleId;
use crate::project::{ProjectLookup, UsageMode};

pub struct LoadedModuleParts {
    pub export: Arc<ModuleExport>,
    pub lowered: LoweredModule,
    pub retained_env: Option<Environment>,
    pub content_hash: blake3::Hash,
}

pub fn elaborate_and_lower_module(
    project: &dyn ProjectLookup,
    usage_mode: UsageMode,
    module_id: ModuleId,
    parsed: ParsedModule,
    is_prelude: bool,
    lib_dependencies: Vec<(ModuleId, Vec<String>)>,
) -> Result<LoadedModuleParts, error::Error> {
    let mut env = Environment::new(module_id);
    if !is_prelude {
        // Try to load prelude, but don't fail if it doesn't exist.
        if let Ok(prelude_id) = project.get_loaded_module_id_by_name("prelude") {
            if let Some(prelude_bindings) = project.get_bindings(prelude_id) {
                // Silently ignore errors when importing prelude.
                let _ = env.bindings.import_prelude(prelude_bindings, project);
                env.sync_current_binding_state();
            }
        }
    }
    for (dep_id, full_name) in lib_dependencies {
        env.bindings.add_module_dependency(dep_id, full_name);
    }
    env.sync_current_binding_state();

    for statement in parsed.statements {
        env.add_statement(project, &statement)?;
    }

    let lowering = env.run_lowering_pass(project);
    if !usage_mode.keeps_ide_metadata() {
        env.discard_ide_metadata();
    }

    let bindings = env.export_bindings();
    let export = ModuleExport::from_lowered(bindings, &lowering.module, usage_mode);
    let export = Arc::new(export);
    let retained_env = usage_mode.keeps_ide_metadata().then_some(env);

    Ok(LoadedModuleParts {
        export,
        lowered: lowering.module,
        retained_env,
        content_hash: parsed.content_hash,
    })
}

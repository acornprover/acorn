use std::collections::BTreeSet;
use std::fs;
use std::io::{self, BufWriter, Write};
use std::path::{Path, PathBuf};

use serde::Serialize;
use tower_lsp::lsp_types::Range;

use crate::code_generator::CodeGenerator;
use crate::elaborator::acorn_type::PotentialType;
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::environment::Environment;
use crate::elaborator::fact::Fact;
use crate::elaborator::names::{ConstantName, DefinedName};
use crate::elaborator::node::Node;
use crate::elaborator::potential_value::PotentialValue;
use crate::elaborator::source::SourceType;
use crate::module::{ModuleDescriptor, ModuleId};
use crate::project::Project;

// ── Exported data structures ────────────────────────────────────────────

#[derive(Serialize)]
pub struct ExportedModule {
    pub name: String,
    pub imports: Vec<String>,
    pub types: Vec<ExportedType>,
    pub typeclasses: Vec<ExportedTypeclass>,
    pub instances: Vec<ExportedInstance>,
    pub definitions: Vec<ExportedDefinition>,
    pub theorems: Vec<ExportedTheorem>,
}

#[derive(Serialize)]
pub struct ExportedType {
    pub name: String,
    pub type_params: Vec<String>,
    pub attributes: Vec<String>,
    pub doc_comments: Vec<String>,
    pub definition_string: Option<String>,
    pub line: u32,
}

#[derive(Serialize)]
pub struct ExportedTypeclass {
    pub name: String,
    pub extends: Vec<String>,
    pub attributes: Vec<ExportedTypeclassAttribute>,
    pub doc_comments: Vec<String>,
    pub line: u32,
}

#[derive(Serialize)]
pub struct ExportedTypeclassAttribute {
    pub name: String,
    pub type_signature: Option<String>,
    pub doc_comments: Vec<String>,
}

#[derive(Serialize)]
pub struct ExportedInstance {
    pub type_name: String,
    pub typeclass: String,
    pub line: u32,
}

#[derive(Serialize)]
pub struct ExportedDefinition {
    pub name: String,
    pub qualified_name: String,
    pub type_signature: Option<String>,
    pub definition_body: Option<String>,
    pub doc_comments: Vec<String>,
    pub line: u32,
}

#[derive(Serialize)]
pub struct ExportedParam {
    pub name: String,
    #[serde(rename = "type")]
    pub param_type: String,
}

#[derive(Serialize)]
pub struct ExportedTheorem {
    pub name: String,
    pub qualified_name: String,
    pub params: Vec<ExportedParam>,
    pub statement: Option<String>,
    pub is_axiom: bool,
    pub proof: Option<Vec<String>>,
    pub source_proof: Option<String>,
    pub doc_comments: Vec<String>,
    pub line: u32,
    pub dependencies: Vec<String>,
}

#[derive(Serialize)]
pub struct ExportedIndex {
    pub modules: Vec<ExportedIndexEntry>,
    pub total_theorems: usize,
    pub total_definitions: usize,
    pub total_types: usize,
    pub total_typeclasses: usize,
    pub total_instances: usize,
}

#[derive(Serialize)]
pub struct ExportedIndexEntry {
    pub name: String,
    pub theorems: usize,
    pub definitions: usize,
    pub types: usize,
    pub typeclasses: usize,
    pub instances: usize,
}

// ── Core export logic ───────────────────────────────────────────────────

/// Export all modules in the project to JSONL files in the given output directory.
pub fn export_project(
    project: &Project,
    output_dir: &Path,
    module_filter: Option<&str>,
    pretty: bool,
) -> Result<(), String> {
    fs::create_dir_all(output_dir).map_err(|e| format!("cannot create output dir: {}", e))?;

    let mut modules: Vec<_> = project.iter_modules().collect();
    modules.sort();

    let mut index_entries = Vec::new();
    let mut total_theorems = 0;
    let mut total_definitions = 0;
    let mut total_types = 0;
    let mut total_typeclasses = 0;
    let mut total_instances = 0;

    for (descriptor, module_id) in &modules {
        let module_name = match descriptor {
            ModuleDescriptor::Name(parts) => parts.join("."),
            _ => continue,
        };

        if let Some(filter) = module_filter {
            if module_name != filter {
                continue;
            }
        }

        let env = match project.get_env_by_id(*module_id) {
            Some(env) => env,
            None => continue,
        };

        let exported = export_module(project, env, *module_id, &module_name, descriptor);

        let entry = ExportedIndexEntry {
            name: module_name.clone(),
            theorems: exported.theorems.len(),
            definitions: exported.definitions.len(),
            types: exported.types.len(),
            typeclasses: exported.typeclasses.len(),
            instances: exported.instances.len(),
        };

        total_theorems += entry.theorems;
        total_definitions += entry.definitions;
        total_types += entry.types;
        total_typeclasses += entry.typeclasses;
        total_instances += entry.instances;

        // Write module JSONL
        let module_path = module_name_to_path(output_dir, &module_name);
        if let Some(parent) = module_path.parent() {
            fs::create_dir_all(parent)
                .map_err(|e| format!("cannot create dir for {}: {}", module_name, e))?;
        }

        write_jsonl(&module_path, &exported)
            .map_err(|e| format!("cannot write {}: {}", module_name, e))?;

        println!(
            "  {} — {} theorems, {} definitions, {} types",
            module_name, entry.theorems, entry.definitions, entry.types
        );

        index_entries.push(entry);
    }

    // Write index
    let index = ExportedIndex {
        modules: index_entries,
        total_theorems,
        total_definitions,
        total_types,
        total_typeclasses,
        total_instances,
    };

    let index_path = output_dir.join("index.json");
    let file =
        fs::File::create(&index_path).map_err(|e| format!("cannot create index.json: {}", e))?;
    let writer = BufWriter::new(file);
    if pretty {
        serde_json::to_writer_pretty(writer, &index)
    } else {
        serde_json::to_writer(writer, &index)
    }
    .map_err(|e| format!("cannot write index.json: {}", e))?;

    println!(
        "\nExported {} modules: {} theorems, {} definitions, {} types, {} typeclasses, {} instances",
        index.modules.len(),
        total_theorems,
        total_definitions,
        total_types,
        total_typeclasses,
        total_instances,
    );

    Ok(())
}

fn module_name_to_path(output_dir: &Path, module_name: &str) -> PathBuf {
    let parts: Vec<&str> = module_name.split('.').collect();
    let mut path = output_dir.to_path_buf();
    for part in &parts {
        path.push(part);
    }
    path.set_extension("jsonl");
    path
}

fn write_jsonl(path: &Path, module: &ExportedModule) -> io::Result<()> {
    let file = fs::File::create(path)?;
    let mut writer = BufWriter::new(file);

    for t in &module.types {
        write_json_line(&mut writer, "type", t)?;
    }
    for tc in &module.typeclasses {
        write_json_line(&mut writer, "typeclass", tc)?;
    }
    for inst in &module.instances {
        write_json_line(&mut writer, "instance", inst)?;
    }
    for def in &module.definitions {
        write_json_line(&mut writer, "definition", def)?;
    }
    for thm in &module.theorems {
        write_json_line(&mut writer, "theorem", thm)?;
    }

    writer.flush()
}

fn write_json_line<W: Write, T: Serialize>(writer: &mut W, kind: &str, item: &T) -> io::Result<()> {
    let item_json =
        serde_json::to_value(item).map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
    let mut obj = serde_json::Map::new();
    obj.insert(
        "kind".to_string(),
        serde_json::Value::String(kind.to_string()),
    );
    if let serde_json::Value::Object(fields) = item_json {
        for (k, v) in fields {
            obj.insert(k, v);
        }
    }
    let line = serde_json::to_string(&serde_json::Value::Object(obj))
        .map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
    writeln!(writer, "{}", line)
}

// ── Per-module export ───────────────────────────────────────────────────

fn export_module(
    project: &Project,
    env: &Environment,
    module_id: ModuleId,
    module_name: &str,
    descriptor: &ModuleDescriptor,
) -> ExportedModule {
    let bindings = &env.bindings;

    let imports = collect_imports(env, project, module_id);

    // Read source file for proof extraction
    let source_lines: Vec<String> = project
        .path_from_descriptor(descriptor)
        .ok()
        .and_then(|path| fs::read_to_string(path).ok())
        .map(|content| content.lines().map(String::from).collect())
        .unwrap_or_default();

    // Types
    let mut types = Vec::new();
    for (type_name, potential_type) in bindings.iter_types() {
        let datatype = match potential_type.as_base_datatype() {
            Some(dt) => dt,
            None => continue,
        };

        // Only export types defined in this module
        if datatype.module_id != module_id {
            continue;
        }

        let mut attributes = bindings.get_datatype_attributes(datatype);
        attributes.retain(|name| !name.chars().all(|c| c.is_numeric()));
        attributes.sort();

        let type_params = match potential_type {
            PotentialType::Unresolved(ut) => ut
                .params
                .iter()
                .enumerate()
                .map(|(i, tc)| {
                    if let Some(tc) = tc {
                        format!("T{}: {}", i, tc.name)
                    } else {
                        format!("T{}", i)
                    }
                })
                .collect(),
            _ => vec![],
        };

        let doc_comments = bindings
            .get_datatype_doc_comments(datatype)
            .cloned()
            .unwrap_or_default();

        let definition_string = bindings.get_datatype_definition_string(datatype).cloned();

        let line = bindings
            .get_datatype_range(datatype)
            .map(|r| r.start.line + 1)
            .unwrap_or(0);

        types.push(ExportedType {
            name: type_name.clone(),
            type_params,
            attributes,
            doc_comments,
            definition_string,
            line,
        });
    }

    // Typeclasses
    let mut typeclasses = Vec::new();
    for (tc_name, typeclass) in bindings.iter_typeclasses() {
        if typeclass.module_id != module_id {
            continue;
        }

        let tc_attrs = bindings.get_typeclass_attributes(typeclass, project);
        let mut attributes = Vec::new();
        for (attr_name, (defining_module, _defining_tc)) in tc_attrs {
            let constant_name =
                ConstantName::typeclass_attr(*defining_module, typeclass.clone(), attr_name);
            let doc_comments = bindings
                .get_constant_doc_comments(&constant_name)
                .cloned()
                .unwrap_or_default();
            let type_sig = get_constant_type_string(bindings, &constant_name);
            attributes.push(ExportedTypeclassAttribute {
                name: attr_name.clone(),
                type_signature: type_sig,
                doc_comments,
            });
        }

        let extends: Vec<String> = bindings
            .get_extends(typeclass)
            .map(|tc| tc.name.clone())
            .collect();

        let doc_comments = bindings
            .get_typeclass_doc_comments(typeclass)
            .cloned()
            .unwrap_or_default();

        let line = bindings
            .get_typeclass_range(typeclass)
            .map(|r| r.start.line + 1)
            .unwrap_or(0);

        typeclasses.push(ExportedTypeclass {
            name: tc_name.clone(),
            extends,
            attributes,
            doc_comments,
            line,
        });
    }

    // Walk nodes to extract instances, definitions, theorems
    let mut instances = Vec::new();
    let mut definitions = Vec::new();
    let mut theorems = Vec::new();

    // Get cached proofs for this module
    let cert_worklist = project.build_cache.make_worklist(descriptor);

    for node in &env.nodes {
        export_node(
            project,
            env,
            module_id,
            module_name,
            node,
            &cert_worklist,
            &source_lines,
            &mut instances,
            &mut definitions,
            &mut theorems,
        );
    }

    ExportedModule {
        name: module_name.to_string(),
        imports,
        types,
        typeclasses,
        instances,
        definitions,
        theorems,
    }
}

fn export_node(
    project: &Project,
    env: &Environment,
    module_id: ModuleId,
    module_name: &str,
    node: &Node,
    cert_worklist: &crate::certificate::CertificateWorklist,
    source_lines: &[String],
    instances: &mut Vec<ExportedInstance>,
    definitions: &mut Vec<ExportedDefinition>,
    theorems: &mut Vec<ExportedTheorem>,
) {
    match node {
        Node::Structural(fact, _) => {
            export_fact(
                env,
                module_id,
                module_name,
                fact,
                cert_worklist,
                instances,
                definitions,
                theorems,
            );
        }
        Node::Claim(goal, _fact, _, _) => {
            // Claims inside blocks are internal goals with incomplete statements
            // (e.g., missing implies premises). Only create a theorem entry if
            // one doesn't already exist (the Block handler processes the complete
            // version first via external_fact).
            let prop = goal.proposition.as_ref();
            let name = match prop.theorem_name() {
                Some(n) => n.to_string(),
                None => return,
            };

            // Skip if already exported (from Block's external_fact)
            if theorems.iter().any(|t| t.name == name) {
                return;
            }

            // Fallback: standalone claim not inside a block
            let qualified_name = format!("{}.{}", module_name, name);
            let line = prop.source.range.start.line + 1;
            let is_axiom = prop.source.is_axiom();

            let mut codegen = CodeGenerator::new(&env.bindings).with_explicit_numerals();
            let statement = codegen.value_to_code(&prop.value).ok();
            let dependencies = collect_dependencies(&prop.value);
            let proof = get_proof_from_worklist(cert_worklist, &goal.name);

            theorems.push(ExportedTheorem {
                name,
                qualified_name,
                params: vec![],
                statement,
                is_axiom,
                proof,
                source_proof: None,
                doc_comments: vec![],
                line,
                dependencies,
            });
        }
        Node::Block(block, external_fact, _) => {
            // Process external_fact FIRST — it has the complete theorem
            // (including ForAll params and implies premises).
            let mut handled_as_theorem = false;

            if let Some(Fact::Proposition(prop)) = external_fact.as_ref() {
                if let Some(name) = prop.theorem_name() {
                    if prop.source.module_id == module_id {
                        handled_as_theorem = true;

                        let qualified_name = format!("{}.{}", module_name, name);
                        let line = prop.source.range.start.line + 1;
                        let is_axiom = prop.source.is_axiom();

                        // Use block args for original parameter names
                        let param_names: Vec<String> =
                            block.args.iter().map(|(n, _)| n.clone()).collect();

                        let mut codegen =
                            CodeGenerator::new(&env.bindings).with_explicit_numerals();
                        let (params, statement) =
                            match codegen.value_to_theorem_parts(&prop.value, &param_names) {
                                Ok((p, s)) => (
                                    p.into_iter()
                                        .map(|(n, t)| ExportedParam {
                                            name: n,
                                            param_type: t,
                                        })
                                        .collect(),
                                    Some(s),
                                ),
                                Err(_) => (vec![], codegen.value_to_code(&prop.value).ok()),
                            };

                        let dependencies = collect_dependencies(&prop.value);
                        let proof = get_proof_from_worklist(cert_worklist, name);
                        let source_proof =
                            extract_source_proof(source_lines, block.source_range.as_ref());

                        theorems.push(ExportedTheorem {
                            name: name.to_string(),
                            qualified_name,
                            params,
                            statement,
                            is_axiom,
                            proof,
                            source_proof,
                            doc_comments: vec![],
                            line,
                            dependencies,
                        });
                    }
                }
            }

            // Handle non-theorem external facts (instances, definitions, etc.)
            if !handled_as_theorem {
                if let Some(fact) = external_fact {
                    export_fact(
                        env,
                        module_id,
                        module_name,
                        fact,
                        cert_worklist,
                        instances,
                        definitions,
                        theorems,
                    );
                }
            }

            // Recurse into block for nested content
            for sub_node in &block.env.nodes {
                export_node(
                    project,
                    &block.env,
                    module_id,
                    module_name,
                    sub_node,
                    cert_worklist,
                    source_lines,
                    instances,
                    definitions,
                    theorems,
                );
            }
        }
    }
}

fn export_fact(
    env: &Environment,
    module_id: ModuleId,
    module_name: &str,
    fact: &Fact,
    cert_worklist: &crate::certificate::CertificateWorklist,
    instances: &mut Vec<ExportedInstance>,
    definitions: &mut Vec<ExportedDefinition>,
    theorems: &mut Vec<ExportedTheorem>,
) {
    match fact {
        Fact::Proposition(prop) => {
            let source = &prop.source;
            if source.module_id != module_id {
                return;
            }
            match &source.source_type {
                SourceType::Axiom(Some(name)) | SourceType::Theorem(Some(name)) => {
                    // Skip if already exported (from Block handler)
                    if theorems.iter().any(|t| t.name == *name) {
                        return;
                    }

                    let is_axiom = source.is_axiom();
                    let qualified_name = format!("{}.{}", module_name, name);

                    // Use value_to_theorem_parts to extract params + body
                    let mut codegen = CodeGenerator::new(&env.bindings).with_explicit_numerals();
                    let (params, statement) = match codegen.value_to_theorem_parts(&prop.value, &[])
                    {
                        Ok((p, s)) => (
                            p.into_iter()
                                .map(|(n, t)| ExportedParam {
                                    name: n,
                                    param_type: t,
                                })
                                .collect(),
                            Some(s),
                        ),
                        Err(_) => (vec![], codegen.value_to_code(&prop.value).ok()),
                    };

                    let dependencies = collect_dependencies(&prop.value);
                    let proof = get_proof_from_worklist(cert_worklist, name);

                    theorems.push(ExportedTheorem {
                        name: name.clone(),
                        qualified_name,
                        params,
                        statement,
                        is_axiom,
                        proof,
                        source_proof: None,
                        doc_comments: vec![],
                        line: source.range.start.line + 1,
                        dependencies,
                    });
                }
                _ => {}
            }
        }
        Fact::Instance(datatype, typeclass, source) => {
            if source.module_id != module_id {
                return;
            }
            instances.push(ExportedInstance {
                type_name: datatype.name.clone(),
                typeclass: typeclass.name.clone(),
                line: source.range.start.line + 1,
            });
        }
        Fact::Definition(potential_value, definition, source) => {
            if source.module_id != module_id {
                return;
            }
            let name = match &source.source_type {
                SourceType::ConstantDefinition(_, name) => name.clone(),
                _ => return,
            };
            let qualified_name = format!("{}.{}", module_name, name);

            let mut codegen = CodeGenerator::new(&env.bindings).with_explicit_numerals();
            let type_sig = codegen
                .type_to_code_for_display(&definition.get_type())
                .ok();
            let def_body = codegen.value_to_code(definition).ok();

            let constant_name = extract_constant_name(potential_value);
            let doc_comments = constant_name
                .and_then(|cn| env.bindings.get_constant_doc_comments(&cn).cloned())
                .unwrap_or_default();

            definitions.push(ExportedDefinition {
                name,
                qualified_name,
                type_signature: type_sig,
                definition_body: def_body,
                doc_comments,
                line: source.range.start.line + 1,
            });
        }
        Fact::Extends(_, _, _, _) => {}
    }
}

// ── Helpers ─────────────────────────────────────────────────────────────

fn collect_imports(env: &Environment, project: &Project, module_id: ModuleId) -> Vec<String> {
    let mut imports = BTreeSet::new();
    for node in &env.nodes {
        if let Some(fact) = node.get_fact() {
            let source = fact.source();
            if source.module_id != module_id && source.importable {
                if let Some(name) = project.get_module_name_by_id(source.module_id) {
                    imports.insert(name);
                }
            }
        }
    }
    imports.into_iter().collect()
}

fn collect_dependencies(value: &AcornValue) -> Vec<String> {
    let mut deps = BTreeSet::new();
    collect_deps_recursive(value, &mut deps);
    deps.into_iter().collect()
}

fn collect_deps_recursive(value: &AcornValue, deps: &mut BTreeSet<String>) {
    match value {
        AcornValue::Constant(ci) => {
            deps.insert(ci.name.to_string());
        }
        AcornValue::Application(app) => {
            collect_deps_recursive(&app.function, deps);
            for arg in &app.args {
                collect_deps_recursive(arg, deps);
            }
        }
        AcornValue::TypeApplication(ta) => {
            collect_deps_recursive(&ta.function, deps);
        }
        AcornValue::Lambda(_, body) => {
            collect_deps_recursive(body, deps);
        }
        AcornValue::Binary(_, left, right) => {
            collect_deps_recursive(left, deps);
            collect_deps_recursive(right, deps);
        }
        AcornValue::Not(inner) | AcornValue::Try(inner, _) => {
            collect_deps_recursive(inner, deps);
        }
        AcornValue::ForAll(_, body) | AcornValue::Exists(_, body) => {
            collect_deps_recursive(body, deps);
        }
        AcornValue::IfThenElse(cond, then_val, else_val) => {
            collect_deps_recursive(cond, deps);
            collect_deps_recursive(then_val, deps);
            collect_deps_recursive(else_val, deps);
        }
        AcornValue::Match(scrutinee, cases) => {
            collect_deps_recursive(scrutinee, deps);
            for case in cases {
                collect_deps_recursive(&case.pattern, deps);
                collect_deps_recursive(&case.result, deps);
            }
        }
        AcornValue::Variable(_, _) | AcornValue::Bool(_) => {}
    }
}

fn get_constant_type_string(
    bindings: &crate::elaborator::binding_map::BindingMap,
    name: &ConstantName,
) -> Option<String> {
    let codegen = CodeGenerator::new(bindings);
    let def = bindings.get_definition(&DefinedName::Constant(name.clone()))?;
    codegen.type_to_code_for_display(&def.get_type()).ok()
}

fn extract_constant_name(pv: &PotentialValue) -> Option<ConstantName> {
    match pv {
        PotentialValue::Resolved(AcornValue::Constant(ci)) => Some(ci.name.clone()),
        _ => None,
    }
}

fn get_proof_from_worklist(
    worklist: &crate::certificate::CertificateWorklist,
    goal_name: &str,
) -> Option<Vec<String>> {
    let indexes = worklist.get_indexes(goal_name);
    if indexes.is_empty() {
        return None;
    }
    let cert = worklist.get_cert(indexes[0])?;
    cert.proof.clone()
}

/// Extract the source code proof body from a block's source range.
/// Returns the text between `by {` and the closing `}`, dedented.
fn extract_source_proof(source_lines: &[String], range: Option<&Range>) -> Option<String> {
    let range = range?;
    let start_line = range.start.line as usize;
    let end_line = range.end.line as usize;

    if source_lines.is_empty() || end_line >= source_lines.len() {
        return None;
    }

    // Build the full text of the block range
    let mut full = String::new();
    for i in start_line..=end_line {
        if i > start_line {
            full.push('\n');
        }
        let line = &source_lines[i];
        if i == start_line {
            let start_char = (range.start.character as usize).min(line.len());
            full.push_str(&line[start_char..]);
        } else if i == end_line {
            // Include up to (but not past) end character
            let end_char = (range.end.character as usize + 1).min(line.len());
            full.push_str(&line[..end_char]);
        } else {
            full.push_str(line);
        }
    }

    // Find "by" keyword and opening brace
    let by_idx = full.find("by")?;
    let open_brace = full[by_idx..].find('{')? + by_idx;
    let close_brace = full.rfind('}')?;

    if open_brace >= close_brace {
        return None;
    }

    let body = full[open_brace + 1..close_brace].trim();
    if body.is_empty() {
        return None;
    }

    Some(dedent(body))
}

/// Remove common leading whitespace from all non-empty lines.
fn dedent(text: &str) -> String {
    let lines: Vec<&str> = text.lines().collect();
    let min_indent = lines
        .iter()
        .filter(|l| !l.trim().is_empty())
        .map(|l| l.len() - l.trim_start().len())
        .min()
        .unwrap_or(0);

    lines
        .iter()
        .map(|l| {
            if l.len() >= min_indent {
                &l[min_indent..]
            } else {
                l.trim()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::{self, BufWriter, Write};
use std::path::{Path, PathBuf};

use serde::Serialize;
use tower_lsp::lsp_types::Range;

use crate::code_generator::CodeGenerator;
use crate::elaborator::acorn_type::{FamilyParamKind, PotentialType};
use crate::elaborator::acorn_value::AcornValue;
use crate::elaborator::environment::Environment;
use crate::elaborator::fact::Fact;
use crate::elaborator::names::{ConstantName, DefinedName};
use crate::elaborator::node::Node;
use crate::elaborator::potential_value::PotentialValue;
use crate::elaborator::source::SourceType;
use crate::module::{ModuleDescriptor, ModuleId};
use crate::project::Project;

// ── Export options ───────────────────────────────────────────────────────

/// Controls which optional fields are included in the export.
pub struct ExportOptions {
    pub pretty: bool,
    pub type_annotations: bool,
    pub proof_deps: bool,
    pub elaborated: bool,
}

impl ExportOptions {
    /// Basic export with no optional fields.
    #[cfg(test)]
    pub fn basic() -> Self {
        ExportOptions {
            pretty: false,
            type_annotations: false,
            proof_deps: false,
            elaborated: false,
        }
    }
}

// ── Exported data structures ────────────────────────────────────────────

#[derive(Serialize)]
pub struct ExportedModule {
    pub name: String,
    pub imports: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub numerals: Option<String>,
    pub types: Vec<ExportedType>,
    pub typeclasses: Vec<ExportedTypeclass>,
    pub attributes: Vec<ExportedAttributes>,
    pub instances: Vec<ExportedInstance>,
    pub definitions: Vec<ExportedDefinition>,
    pub theorems: Vec<ExportedTheorem>,
}

#[derive(Serialize)]
pub struct ExportedAttributes {
    pub type_name: String,
    pub line: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_block: Option<String>,
}

#[derive(Serialize)]
pub struct ExportedType {
    pub name: String,
    pub type_params: Vec<String>,
    pub attributes: Vec<String>,
    pub doc_comments: Vec<String>,
    pub definition_string: Option<String>,
    pub line: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_block: Option<String>,
}

#[derive(Serialize)]
pub struct ExportedTypeclass {
    pub name: String,
    pub extends: Vec<String>,
    pub attributes: Vec<ExportedTypeclassAttribute>,
    pub doc_comments: Vec<String>,
    pub line: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_block: Option<String>,
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
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_block: Option<String>,
}

#[derive(Serialize)]
pub struct ExportedDefinition {
    pub name: String,
    pub qualified_name: String,
    pub type_signature: Option<String>,
    pub definition_body: Option<String>,
    pub doc_comments: Vec<String>,
    pub line: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_block: Option<String>,
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

    // Optional fields (controlled by ExportOptions)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_dependencies: Option<Vec<String>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub elaborated_proof: Option<Vec<String>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub statement_annotations: Option<Vec<IdentifierInfo>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub proof_annotations: Option<Vec<IdentifierInfo>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source_block: Option<String>,
}

#[derive(Serialize, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct IdentifierInfo {
    pub name: String,
    pub full_name: String,
    #[serde(rename = "type")]
    pub id_type: String,
    pub kind: String, // "constant" | "variable"
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
    options: &ExportOptions,
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

        let exported = export_module(project, env, *module_id, &module_name, descriptor, options);

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
    if options.pretty {
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

    // Write module metadata line
    {
        let mut meta = serde_json::Map::new();
        meta.insert(
            "kind".to_string(),
            serde_json::Value::String("module".to_string()),
        );
        meta.insert(
            "name".to_string(),
            serde_json::Value::String(module.name.clone()),
        );
        meta.insert(
            "imports".to_string(),
            serde_json::to_value(&module.imports)
                .map_err(|e| io::Error::new(io::ErrorKind::Other, e))?,
        );
        if let Some(ref numerals) = module.numerals {
            meta.insert(
                "numerals".to_string(),
                serde_json::Value::String(numerals.clone()),
            );
        }
        let line = serde_json::to_string(&serde_json::Value::Object(meta))
            .map_err(|e| io::Error::new(io::ErrorKind::Other, e))?;
        writeln!(writer, "{}", line)?;
    }

    for t in &module.types {
        write_json_line(&mut writer, "type", t)?;
    }
    for tc in &module.typeclasses {
        write_json_line(&mut writer, "typeclass", tc)?;
    }
    for attr in &module.attributes {
        write_json_line(&mut writer, "attributes", attr)?;
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
    options: &ExportOptions,
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
                .map(|(i, kind)| match kind {
                    FamilyParamKind::Type(Some(tc)) => format!("T{}: {}", i, tc.name),
                    FamilyParamKind::Type(None) => format!("T{}", i),
                    FamilyParamKind::Value(value_type) => format!("x{}: {}", i, value_type),
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
            source_block: None,
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
            source_block: None,
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
            options,
            false,
            &mut instances,
            &mut definitions,
            &mut theorems,
        );
    }

    let numerals = bindings.numerals().map(|dt| dt.name.clone());

    // ── Scan source for `attributes Type { ... }` blocks ────────────────
    let mut attr_blocks: Vec<ExportedAttributes> = Vec::new();
    for (i, line) in source_lines.iter().enumerate() {
        if !line.starts_with(' ')
            && !line.starts_with('\t')
            && line.trim_start().starts_with("attributes ")
        {
            // Extract type name: "attributes Nat {" -> "Nat"
            // or "attributes A: AddGroup {" -> "A: AddGroup"
            let rest = line.trim_start().strip_prefix("attributes ").unwrap_or("");
            let type_name = rest.split('{').next().unwrap_or("").trim().to_string();
            attr_blocks.push(ExportedAttributes {
                type_name,
                line: (i + 1) as u32,
                source_block: None,
            });
        }
    }

    // ── Populate source_block for every item ────────────────────────────
    // Collect (1-based line, kind, index) for each exported item, sort by
    // line, then slice source_lines between consecutive items.
    //
    // Only top-level items (no leading whitespace) participate in the
    // range calculation. Nested items (definitions inside instance/
    // attributes blocks) are excluded — they're part of their parent's
    // source_block.
    if !source_lines.is_empty() {
        #[derive(Clone, Copy)]
        enum ItemKind {
            Type,
            Typeclass,
            Attributes,
            Instance,
            Definition,
            Theorem,
        }

        let mut entries: Vec<(u32, ItemKind, usize)> = Vec::new();
        for (i, t) in types.iter().enumerate() {
            if t.line > 0 {
                entries.push((t.line, ItemKind::Type, i));
            }
        }
        for (i, t) in typeclasses.iter().enumerate() {
            if t.line > 0 {
                entries.push((t.line, ItemKind::Typeclass, i));
            }
        }
        for (i, t) in attr_blocks.iter().enumerate() {
            if t.line > 0 {
                entries.push((t.line, ItemKind::Attributes, i));
            }
        }
        for (i, t) in instances.iter().enumerate() {
            if t.line > 0 {
                entries.push((t.line, ItemKind::Instance, i));
            }
        }
        for (i, t) in definitions.iter().enumerate() {
            if t.line > 0 {
                entries.push((t.line, ItemKind::Definition, i));
            }
        }
        for (i, t) in theorems.iter().enumerate() {
            if t.line > 0 {
                entries.push((t.line, ItemKind::Theorem, i));
            }
        }

        entries.sort_by_key(|(line, _, _)| *line);

        // Determine which entries are top-level (no leading whitespace).
        let is_top_level: Vec<bool> = entries
            .iter()
            .map(|(line, _, _)| {
                let idx = (*line - 1) as usize;
                if idx < source_lines.len() {
                    let first_char = source_lines[idx].chars().next().unwrap_or(' ');
                    !first_char.is_whitespace()
                } else {
                    false
                }
            })
            .collect();

        // Collect top-level lines for range boundary calculation.
        let mut top_level_lines: Vec<u32> = entries
            .iter()
            .zip(is_top_level.iter())
            .filter(|(_, &tl)| tl)
            .map(|((line, _, _), _)| *line)
            .collect();
        top_level_lines.sort();
        top_level_lines.dedup();

        for idx in 0..entries.len() {
            let (start_line, kind, item_idx) = entries[idx];
            let mut start_0 = (start_line - 1) as usize; // to 0-based

            if !is_top_level[idx] {
                // Nested item: no source_block (it's part of the parent's block)
                continue;
            }

            // Walk backwards to include doc comments (///) preceding this item
            while start_0 > 0 && source_lines[start_0 - 1].trim().starts_with("///") {
                start_0 -= 1;
            }

            // Find the next top-level item's line to determine range end
            let end_0 = match top_level_lines.iter().find(|&&l| l > start_line) {
                Some(&next_line) => {
                    let next_line_0 = (next_line - 1) as usize;
                    // Walk backwards to skip blank lines, imports, numerals,
                    // and comments between items
                    let mut end = next_line_0;
                    while end > start_0 {
                        let trimmed = source_lines[end - 1].trim();
                        if trimmed.is_empty()
                            || trimmed.starts_with("from ")
                            || trimmed.starts_with("numerals ")
                            || trimmed.starts_with("//")
                        {
                            end -= 1;
                        } else {
                            break;
                        }
                    }
                    end
                }
                None => {
                    // Last top-level item: take to end of file
                    let mut end = source_lines.len();
                    while end > start_0 && source_lines[end - 1].trim().is_empty() {
                        end -= 1;
                    }
                    end
                }
            };

            if start_0 < end_0 && end_0 <= source_lines.len() {
                let block: String = source_lines[start_0..end_0].join("\n");
                let block = if let Some(ref num_type) = numerals {
                    replace_bare_numerals(&block, num_type)
                } else {
                    block
                };
                match kind {
                    ItemKind::Type => types[item_idx].source_block = Some(block),
                    ItemKind::Typeclass => typeclasses[item_idx].source_block = Some(block),
                    ItemKind::Attributes => attr_blocks[item_idx].source_block = Some(block),
                    ItemKind::Instance => instances[item_idx].source_block = Some(block),
                    ItemKind::Definition => definitions[item_idx].source_block = Some(block),
                    ItemKind::Theorem => theorems[item_idx].source_block = Some(block),
                }
            }
        }
    }

    ExportedModule {
        name: module_name.to_string(),
        imports,
        numerals,
        types,
        typeclasses,
        attributes: attr_blocks,
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
    options: &ExportOptions,
    inside_proof: bool,
    instances: &mut Vec<ExportedInstance>,
    definitions: &mut Vec<ExportedDefinition>,
    theorems: &mut Vec<ExportedTheorem>,
) {
    match node {
        Node::Structural(fact, _) => {
            export_fact(
                project,
                env,
                module_id,
                module_name,
                fact,
                cert_worklist,
                inside_proof,
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
            let dependencies = collect_dependencies(&prop.value, project);
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
                proof_dependencies: None,
                elaborated_proof: None,
                statement_annotations: None,
                proof_annotations: None,
                source_block: None,
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

                        let stmt_dep_names = collect_dep_names(&prop.value);
                        let dependencies: Vec<String> = stmt_dep_names
                            .iter()
                            .map(|cn| qualify_constant_name(cn, project))
                            .collect();
                        let proof = get_proof_from_worklist(cert_worklist, name);
                        let source_proof =
                            extract_source_proof(source_lines, block.source_range.as_ref());

                        // Optional fields
                        let proof_dependencies = if options.proof_deps {
                            Some(collect_proof_dependencies(
                                &block.env,
                                env,
                                &stmt_dep_names,
                                &param_names,
                                project,
                            ))
                        } else {
                            None
                        };

                        let elaborated_proof = if options.elaborated {
                            Some(collect_elaborated_proof(&block.env, &env.bindings))
                        } else {
                            None
                        };

                        let statement_annotations = if options.type_annotations {
                            Some(collect_identifiers(
                                &prop.value,
                                &env.bindings,
                                &param_names,
                            ))
                        } else {
                            None
                        };

                        let proof_annotations = if options.type_annotations {
                            Some(collect_block_identifiers(
                                &block.env,
                                &env.bindings,
                                &param_names,
                            ))
                        } else {
                            None
                        };

                        let doc_comments = env
                            .bindings
                            .get_constant_doc_comments(&ConstantName::Unqualified(
                                module_id,
                                name.to_string(),
                            ))
                            .cloned()
                            .unwrap_or_default();

                        theorems.push(ExportedTheorem {
                            name: name.to_string(),
                            qualified_name,
                            params,
                            statement,
                            is_axiom,
                            proof,
                            source_proof,
                            doc_comments,
                            line,
                            dependencies,
                            proof_dependencies,
                            elaborated_proof,
                            statement_annotations,
                            proof_annotations,
                            source_block: None,
                        });
                    }
                }
            }

            // Handle non-theorem external facts (instances, definitions, etc.)
            if !handled_as_theorem {
                if let Some(fact) = external_fact {
                    export_fact(
                        project,
                        env,
                        module_id,
                        module_name,
                        fact,
                        cert_worklist,
                        inside_proof,
                        instances,
                        definitions,
                        theorems,
                    );
                }
            }

            // Recurse into block for nested content
            // All sub-nodes inside a block are proof-internal;
            // skip definition exports from them
            for sub_node in &block.env.nodes {
                export_node(
                    project,
                    &block.env,
                    module_id,
                    module_name,
                    sub_node,
                    cert_worklist,
                    source_lines,
                    options,
                    true,
                    instances,
                    definitions,
                    theorems,
                );
            }
        }
    }
}

fn export_fact(
    project: &Project,
    env: &Environment,
    module_id: ModuleId,
    module_name: &str,
    fact: &Fact,
    cert_worklist: &crate::certificate::CertificateWorklist,
    inside_proof: bool,
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

                    let dependencies = collect_dependencies(&prop.value, project);
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
                        proof_dependencies: None,
                        elaborated_proof: None,
                        statement_annotations: None,
                        proof_annotations: None,
                        source_block: None,
                    });
                }
                _ => {}
            }
        }
        Fact::Instance(instance, source) => {
            if source.module_id != module_id {
                return;
            }
            instances.push(ExportedInstance {
                type_name: instance.instance_type.to_string(),
                typeclass: instance.typeclass.name.clone(),
                line: source.range.start.line + 1,
                source_block: None,
            });
        }
        Fact::Definition(potential_value, definition, source) => {
            if source.module_id != module_id || inside_proof {
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
                source_block: None,
            });
        }
        Fact::Extends(_, _, _, _) => {}
    }
}

// ── Optional field collectors ───────────────────────────────────────────

/// Collect proof-level dependencies by walking the block's sub-nodes and
/// extracting all referenced constants, then filtering out statement-level deps,
/// block argument names, and block-internal local definitions.
fn collect_proof_dependencies(
    block_env: &Environment,
    parent_env: &Environment,
    statement_deps: &BTreeSet<ConstantName>,
    block_arg_names: &[String],
    project: &Project,
) -> Vec<String> {
    let arg_set: BTreeSet<&str> = block_arg_names.iter().map(|s| s.as_str()).collect();

    // Collect all names defined locally inside the block (define, let, forall args, etc.)
    let mut local_names = BTreeSet::new();
    collect_local_definitions(&block_env.nodes, &mut local_names);

    // Collect module-level theorem/definition names to distinguish
    // external references from proof-local constants (e.g. let ... satisfy variables)
    let mut module_level_names = BTreeSet::new();
    for node in &parent_env.nodes {
        if let Some(name) = node.source_name() {
            module_level_names.insert(name);
        }
    }

    let mut proof_deps = BTreeSet::new();
    for node in &block_env.nodes {
        collect_node_constants(node, &mut proof_deps);
    }

    // Include cited theorem names (these are lost after expand_citation inlines them)
    for cited_name in block_env.collect_cited_names() {
        proof_deps.insert(cited_name);
    }

    // Remove statement-level deps, block argument names, and block-internal definitions.
    proof_deps
        .into_iter()
        .filter(|dep| {
            // Remove deps that also appear in the statement
            if statement_deps.contains(dep) {
                return false;
            }
            // Remove block argument names (these are Unqualified constants matching arg names)
            let short = dep.to_string();
            if arg_set.contains(short.as_str()) {
                return false;
            }
            if local_names.contains(short.as_str()) {
                return false;
            }
            // For Unqualified names (no '.'), only keep if they're module-level definitions
            if !short.contains('.') {
                return module_level_names.contains(short.as_str());
            }
            true
        })
        .map(|cn| qualify_constant_name(&cn, project))
        .collect()
}

/// Recursively collect all locally-defined names within a block's nodes.
/// This includes: `define` names, sub-block argument names (forall/if/let vars).
fn collect_local_definitions(nodes: &[Node], names: &mut BTreeSet<String>) {
    for node in nodes {
        match node {
            Node::Structural(fact, _) => {
                if let Fact::Definition(_, _, source) = fact {
                    if let SourceType::ConstantDefinition(_, name) = &source.source_type {
                        names.insert(name.clone());
                    }
                }
            }
            Node::Claim(_, _, _, _) => {}
            Node::Block(block, _, _) => {
                // Sub-block args (forall x, if condition, let d1, etc.)
                for (arg_name, _) in &block.args {
                    names.insert(arg_name.clone());
                }
                // Recurse into sub-block
                collect_local_definitions(&block.env.nodes, names);
            }
        }
    }
}

/// Recursively collect all constant names from a node's values.
fn collect_node_constants(node: &Node, deps: &mut BTreeSet<ConstantName>) {
    match node {
        Node::Structural(fact, _) => {
            if let Some(value) = fact_value(fact) {
                collect_deps_recursive(value, deps);
            }
        }
        Node::Claim(goal, _fact, _, _) => {
            collect_deps_recursive(&goal.proposition.value, deps);
        }
        Node::Block(block, external_fact, _) => {
            if let Some(fact) = external_fact {
                if let Some(value) = fact_value(fact) {
                    collect_deps_recursive(value, deps);
                }
            }
            for sub_node in &block.env.nodes {
                collect_node_constants(sub_node, deps);
            }
        }
    }
}

fn fact_value(fact: &Fact) -> Option<&AcornValue> {
    match fact {
        Fact::Proposition(prop) => Some(&prop.value),
        Fact::Definition(_, def, _) => Some(def),
        _ => None,
    }
}

/// Collect elaborated proof lines from a block's sub-nodes.
/// Each claim/structural proposition is rendered with explicit numerals.
fn collect_elaborated_proof(
    block_env: &Environment,
    bindings: &crate::elaborator::binding_map::BindingMap,
) -> Vec<String> {
    let mut lines = Vec::new();

    for node in &block_env.nodes {
        collect_elaborated_from_node(node, bindings, &mut lines);
    }

    lines
}

fn collect_elaborated_from_node(
    node: &Node,
    bindings: &crate::elaborator::binding_map::BindingMap,
    lines: &mut Vec<String>,
) {
    match node {
        Node::Structural(fact, _) => {
            if let Fact::Proposition(prop) = fact {
                let mut codegen = CodeGenerator::new(bindings).with_explicit_numerals();
                if let Ok(code) = codegen.value_to_code(&prop.value) {
                    lines.push(code);
                }
            }
        }
        Node::Claim(goal, _, _, _) => {
            let mut codegen = CodeGenerator::new(bindings).with_explicit_numerals();
            if let Ok(code) = codegen.value_to_code(&goal.proposition.value) {
                lines.push(code);
            }
        }
        Node::Block(block, _, _) => {
            // Recurse into sub-blocks
            for sub_node in &block.env.nodes {
                collect_elaborated_from_node(sub_node, bindings, lines);
            }
        }
    }
}

/// Collect type annotation info for all identifiers in a value.
fn collect_identifiers(
    value: &AcornValue,
    bindings: &crate::elaborator::binding_map::BindingMap,
    var_names: &[String],
) -> Vec<IdentifierInfo> {
    let mut seen = BTreeMap::new();
    collect_identifiers_recursive(value, bindings, var_names, 0, &mut seen);
    seen.into_values().collect()
}

fn collect_identifiers_recursive(
    value: &AcornValue,
    bindings: &crate::elaborator::binding_map::BindingMap,
    var_names: &[String],
    var_offset: usize,
    seen: &mut BTreeMap<String, IdentifierInfo>,
) {
    match value {
        AcornValue::Constant(ci) => {
            let (name, full_name) = constant_name_strings(&ci.name);
            let codegen = CodeGenerator::new(bindings);
            let id_type = codegen
                .type_to_code_for_display(&ci.instance_type)
                .unwrap_or_default();
            let key = format!("c:{}", full_name);
            seen.entry(key).or_insert(IdentifierInfo {
                name,
                full_name,
                id_type,
                kind: "constant".to_string(),
            });
        }
        AcornValue::Variable(id, ty) => {
            let idx = *id as usize;
            let name = if idx < var_names.len() {
                var_names[idx].clone()
            } else {
                format!("x{}", idx - var_offset)
            };
            let codegen = CodeGenerator::new(bindings);
            let id_type = codegen.type_to_code_for_display(ty).unwrap_or_default();
            let key = format!("v:{}:{}", name, id_type);
            seen.entry(key).or_insert(IdentifierInfo {
                name,
                full_name: String::new(),
                id_type,
                kind: "variable".to_string(),
            });
        }
        AcornValue::Application(app) => {
            collect_identifiers_recursive(&app.function, bindings, var_names, var_offset, seen);
            for arg in &app.args {
                collect_identifiers_recursive(arg, bindings, var_names, var_offset, seen);
            }
        }
        AcornValue::TypeApplication(ta) => {
            collect_identifiers_recursive(&ta.function, bindings, var_names, var_offset, seen);
        }
        AcornValue::Lambda(types, body) => {
            collect_identifiers_recursive(
                body,
                bindings,
                var_names,
                var_offset + types.len(),
                seen,
            );
        }
        AcornValue::Grouping(value) => {
            collect_identifiers_recursive(value, bindings, var_names, var_offset, seen);
        }
        AcornValue::Binary(_, left, right) => {
            collect_identifiers_recursive(left, bindings, var_names, var_offset, seen);
            collect_identifiers_recursive(right, bindings, var_names, var_offset, seen);
        }
        AcornValue::Not(inner) | AcornValue::Try(inner, _) => {
            collect_identifiers_recursive(inner, bindings, var_names, var_offset, seen);
        }
        AcornValue::ForAll(types, body) | AcornValue::Exists(types, body) => {
            collect_identifiers_recursive(
                body,
                bindings,
                var_names,
                var_offset + types.len(),
                seen,
            );
        }
        AcornValue::IfThenElse(cond, then_val, else_val) => {
            collect_identifiers_recursive(cond, bindings, var_names, var_offset, seen);
            collect_identifiers_recursive(then_val, bindings, var_names, var_offset, seen);
            collect_identifiers_recursive(else_val, bindings, var_names, var_offset, seen);
        }
        AcornValue::Match(scrutinee, cases) => {
            collect_identifiers_recursive(scrutinee, bindings, var_names, var_offset, seen);
            for case in cases {
                collect_identifiers_recursive(&case.pattern, bindings, var_names, var_offset, seen);
                collect_identifiers_recursive(&case.result, bindings, var_names, var_offset, seen);
            }
        }
        AcornValue::Bool(_) => {}
    }
}

/// Collect identifiers from all proof nodes in a block.
/// Block argument names are re-tagged with kind="parameter" for consistency
/// (they appear as constants inside the block but are parameters from the outside).
fn collect_block_identifiers(
    block_env: &Environment,
    bindings: &crate::elaborator::binding_map::BindingMap,
    block_arg_names: &[String],
) -> Vec<IdentifierInfo> {
    let mut seen = BTreeMap::new();

    for node in &block_env.nodes {
        collect_node_identifiers(node, bindings, &mut seen);
    }

    // Re-tag block args: inside the block they are constants, but semantically
    // they are the theorem's parameters (same as statement_annotations' variables).
    let arg_set: BTreeSet<&str> = block_arg_names.iter().map(|s| s.as_str()).collect();
    for info in seen.values_mut() {
        if info.kind == "constant"
            && arg_set.contains(info.name.as_str())
            && info.full_name == info.name
        {
            info.kind = "parameter".to_string();
        }
    }

    seen.into_values().collect()
}

fn collect_node_identifiers(
    node: &Node,
    bindings: &crate::elaborator::binding_map::BindingMap,
    seen: &mut BTreeMap<String, IdentifierInfo>,
) {
    match node {
        Node::Structural(fact, _) => {
            if let Fact::Proposition(prop) = fact {
                collect_identifiers_recursive(&prop.value, bindings, &[], 0, seen);
            }
        }
        Node::Claim(goal, _, _, _) => {
            collect_identifiers_recursive(&goal.proposition.value, bindings, &[], 0, seen);
        }
        Node::Block(block, _, _) => {
            for sub_node in &block.env.nodes {
                collect_node_identifiers(sub_node, bindings, seen);
            }
        }
    }
}

// ── Helpers ─────────────────────────────────────────────────────────────

/// Extract (short_name, full_name) from a ConstantName.
fn constant_name_strings(name: &ConstantName) -> (String, String) {
    match name {
        ConstantName::Unqualified(_, n) => (n.clone(), n.clone()),
        ConstantName::DatatypeAttribute(_, dt, attr) => {
            (attr.clone(), format!("{}.{}", dt.name, attr))
        }
        ConstantName::SpecificDatatypeAttribute(_, dt, _, attr) => {
            (attr.clone(), format!("{}.{}", dt.name, attr))
        }
        ConstantName::TypeclassAttribute(_, tc, attr) => {
            (attr.clone(), format!("{}.{}", tc.name, attr))
        }
        ConstantName::InstanceAttribute(_, inst) => (
            inst.attribute.clone(),
            format!(
                "{}.{}[{}]",
                inst.typeclass.name, inst.attribute, inst.datatype.name
            ),
        ),
    }
}

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

/// Produce a module-qualified name for a constant, e.g. "nat.nat_base.add_comm".
fn qualify_constant_name(name: &ConstantName, project: &Project) -> String {
    let short = name.to_string();
    if let Some(module_name) = project.get_module_name_by_id(name.module_id()) {
        format!("{}.{}", module_name, short)
    } else {
        short
    }
}

/// Collect raw ConstantName dependencies from a value.
fn collect_dep_names(value: &AcornValue) -> BTreeSet<ConstantName> {
    let mut deps = BTreeSet::new();
    collect_deps_recursive(value, &mut deps);
    deps
}

fn collect_dependencies(value: &AcornValue, project: &Project) -> Vec<String> {
    collect_dep_names(value)
        .into_iter()
        .map(|cn| qualify_constant_name(&cn, project))
        .collect()
}

fn collect_deps_recursive(value: &AcornValue, deps: &mut BTreeSet<ConstantName>) {
    match value {
        AcornValue::Constant(ci) => {
            deps.insert(ci.name.clone());
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
        AcornValue::Grouping(value) => {
            collect_deps_recursive(value, deps);
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

/// Replace bare numeric literals with qualified form (e.g. `2` → `Nat.2`).
///
/// A bare numeral is a sequence of digits that is NOT:
/// - preceded by `.` (already qualified like `Nat.2`)
/// - preceded by `_` or an alphanumeric char (part of an identifier like `nat_base` or `T0`)
/// - followed by `_` or an alphanumeric char
///
/// Lines starting with `//` (comments) are skipped.
fn replace_bare_numerals(source: &str, numeral_type: &str) -> String {
    source
        .lines()
        .map(|line| {
            // Skip comment lines
            if line.trim_start().starts_with("//") {
                return line.to_string();
            }
            replace_numerals_in_line(line, numeral_type)
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn replace_numerals_in_line(line: &str, numeral_type: &str) -> String {
    let chars: Vec<char> = line.chars().collect();
    let mut result = String::with_capacity(line.len());
    let mut i = 0;

    while i < chars.len() {
        // Check if we're at the start of a digit sequence
        if chars[i].is_ascii_digit() {
            // Check preceding character
            let prev = if i > 0 { Some(chars[i - 1]) } else { None };
            let is_qualified = prev == Some('.');
            let is_ident = matches!(prev, Some(c) if c.is_alphanumeric() || c == '_');

            // Check if this numeral is the name in a `let` or `define` statement
            // e.g. "    let 2: Nat = ..." — the `2` is a definition name, not a value
            let is_let_name = {
                let prefix = result.trim();
                prefix == "let" || prefix == "define"
            };

            if is_qualified || is_ident || is_let_name {
                // Part of an identifier or already qualified — emit as-is
                result.push(chars[i]);
                i += 1;
                continue;
            }

            // Collect the full number
            let start = i;
            while i < chars.len() && chars[i].is_ascii_digit() {
                i += 1;
            }

            // Check following character
            let next = if i < chars.len() {
                Some(chars[i])
            } else {
                None
            };
            let followed_by_ident = matches!(next, Some(c) if c.is_alphanumeric() || c == '_');

            if followed_by_ident {
                // Part of identifier — emit as-is
                for j in start..i {
                    result.push(chars[j]);
                }
            } else {
                // Bare numeral — qualify it
                result.push_str(numeral_type);
                result.push('.');
                for j in start..i {
                    result.push(chars[j]);
                }
            }
        } else {
            result.push(chars[i]);
            i += 1;
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dedent_basic() {
        let input = "    a\n    b\n    c";
        assert_eq!(dedent(input), "a\nb\nc");
    }

    #[test]
    fn test_dedent_mixed_indent() {
        let input = "        line1\n    line2\n        line3";
        assert_eq!(dedent(input), "    line1\nline2\n    line3");
    }

    #[test]
    fn test_dedent_empty_lines() {
        let input = "    a\n\n    b";
        assert_eq!(dedent(input), "a\n\nb");
    }

    #[test]
    fn test_dedent_single_line() {
        let input = "  hello";
        assert_eq!(dedent(input), "hello");
    }

    #[test]
    fn test_dedent_no_indent() {
        let input = "a\nb\nc";
        assert_eq!(dedent(input), "a\nb\nc");
    }

    #[test]
    fn test_extract_source_proof_basic() {
        let source = vec![
            "theorem foo(a: Nat) {".to_string(),
            "    a = a".to_string(),
            "} by {".to_string(),
            "    a + 0 = a".to_string(),
            "    done".to_string(),
            "}".to_string(),
        ];
        let range = Range {
            start: tower_lsp::lsp_types::Position {
                line: 2,
                character: 0,
            },
            end: tower_lsp::lsp_types::Position {
                line: 5,
                character: 0,
            },
        };
        let result = extract_source_proof(&source, Some(&range));
        assert!(result.is_some());
        let proof = result.unwrap();
        assert!(proof.contains("a + 0 = a"));
        assert!(proof.contains("done"));
    }

    #[test]
    fn test_extract_source_proof_none_range() {
        let source = vec!["something".to_string()];
        assert!(extract_source_proof(&source, None).is_none());
    }

    #[test]
    fn test_extract_source_proof_empty_body() {
        let source = vec!["} by {}".to_string()];
        let range = Range {
            start: tower_lsp::lsp_types::Position {
                line: 0,
                character: 0,
            },
            end: tower_lsp::lsp_types::Position {
                line: 0,
                character: 6,
            },
        };
        assert!(extract_source_proof(&source, Some(&range)).is_none());
    }

    #[test]
    fn test_export_options_basic() {
        let opts = ExportOptions::basic();
        assert!(!opts.pretty);
        assert!(!opts.type_annotations);
        assert!(!opts.proof_deps);
        assert!(!opts.elaborated);
    }

    #[test]
    fn test_constant_name_strings_unqualified() {
        use crate::module::ModuleId;
        let name = ConstantName::Unqualified(ModuleId(0), "foo".to_string());
        let (short, full) = constant_name_strings(&name);
        assert_eq!(short, "foo");
        assert_eq!(full, "foo");
    }

    #[test]
    fn test_constant_name_strings_datatype_attr() {
        use crate::elaborator::acorn_type::Datatype;
        use crate::module::ModuleId;
        let dt = Datatype {
            module_id: ModuleId(0),
            name: "Nat".to_string(),
        };
        let name = ConstantName::datatype_attr(ModuleId(0), dt, "add");
        let (short, full) = constant_name_strings(&name);
        assert_eq!(short, "add");
        assert_eq!(full, "Nat.add");
    }

    #[test]
    fn test_module_name_to_path() {
        let output = Path::new("/tmp/export");
        let path = module_name_to_path(output, "nat.nat_base");
        assert_eq!(path, PathBuf::from("/tmp/export/nat/nat_base.jsonl"));
    }

    #[test]
    fn test_module_name_to_path_simple() {
        let output = Path::new("/tmp/export");
        let path = module_name_to_path(output, "prelude");
        assert_eq!(path, PathBuf::from("/tmp/export/prelude.jsonl"));
    }

    #[test]
    fn test_replace_bare_numerals_basic() {
        assert_eq!(
            replace_bare_numerals("1 + 1 = 2", "Nat"),
            "Nat.1 + Nat.1 = Nat.2"
        );
    }

    #[test]
    fn test_replace_bare_numerals_already_qualified() {
        assert_eq!(replace_bare_numerals("Nat.0.suc", "Nat"), "Nat.0.suc");
    }

    #[test]
    fn test_replace_bare_numerals_in_identifier() {
        // Don't touch digits in identifiers
        assert_eq!(
            replace_bare_numerals("nat_base T0 x2y", "Nat"),
            "nat_base T0 x2y"
        );
    }

    #[test]
    fn test_replace_bare_numerals_comment_skipped() {
        assert_eq!(
            replace_bare_numerals("// 1 + 1 = 2\nlet x = 3", "Nat"),
            "// 1 + 1 = 2\nlet x = Nat.3"
        );
    }

    #[test]
    fn test_replace_bare_numerals_parens() {
        assert_eq!(replace_bare_numerals("f(0, 1)", "Nat"), "f(Nat.0, Nat.1)");
    }

    #[test]
    fn test_replace_bare_numerals_let_name() {
        // In "let 2: Nat = ...", the 2 is a definition name, not a numeral value
        assert_eq!(
            replace_bare_numerals("    let 2: Nat = Nat.1.suc", "Nat"),
            "    let 2: Nat = Nat.1.suc"
        );
    }
}

use acorn::elaborator::acorn_value::AcornValue;
use acorn::elaborator::binding_map::{BindingMap, BindingMapProfileCounts};
use acorn::elaborator::environment::Environment;
use acorn::elaborator::fact::Fact;
use acorn::elaborator::lowering::{LoweredFact, LoweredGoal};
use acorn::elaborator::node::Node;
use acorn::elaborator::source::Source;
use acorn::kernel::clause::Clause;
use acorn::kernel::kernel_context::KernelContext;
use acorn::kernel::literal::Literal;
use acorn::kernel::local_context::LocalContext;
use acorn::kernel::proof_step::{PremiseMap, ProofStep, Rule};
use acorn::kernel::symbol_table::SymbolTableProfileCounts;
use acorn::kernel::term::Term;
use acorn::kernel::type_store::TypeStoreProfileCounts;
use acorn::kernel::variable_map::VariableMap;
use acorn::project::{Project, ProjectConfig, UsageMode};
use mimalloc::MiMalloc;
use std::hint::black_box;
use std::mem::size_of;
use std::time::{Duration, Instant};
use tower_lsp::lsp_types::{Position, Range};

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

unsafe extern "C" {
    fn mi_collect(force: bool);
}

#[derive(Clone, Copy, Debug)]
enum ClearBucket {
    NodeAndModuleLowered,
    KernelContexts,
    BindingSnapshots,
    CurrentBindings,
    TokenAndLineMaps,
    NodePayloads,
    Nodes,
}

impl ClearBucket {
    fn label(self) -> &'static str {
        match self {
            ClearBucket::NodeAndModuleLowered => "clear node/module lowered facts",
            ClearBucket::KernelContexts => "clear env kernel contexts",
            ClearBucket::BindingSnapshots => "clear binding snapshots",
            ClearBucket::CurrentBindings => "clear current bindings",
            ClearBucket::TokenAndLineMaps => "clear token/line maps",
            ClearBucket::NodePayloads => "clear node payloads",
            ClearBucket::Nodes => "clear nodes",
        }
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct StatusMemory {
    rss_kb: usize,
    hwm_kb: usize,
}

#[derive(Clone, Debug, Default)]
struct ProfileStats {
    modules: usize,
    environments: usize,
    nodes: usize,
    structural_nodes: usize,
    claim_nodes: usize,
    block_nodes: usize,
    binding_snapshots: usize,
    token_infos: usize,
    line_types: usize,
    lowered_module_facts: ProofBucketStats,
    node_lowered_facts: ProofBucketStats,
    lowered_goals: ProofBucketStats,
    env_kernel_contexts: KernelContextStats,
    lowered_kernel_contexts: KernelContextStats,
    current_binding_counts: BindingProfileTotals,
    snapshot_binding_counts: BindingProfileTotals,
}

#[derive(Clone, Debug, Default)]
struct ModuleProfile {
    name: String,
    stats: ProfileStats,
}

#[derive(Clone, Debug, Default)]
struct ProofBucketStats {
    lowered_facts: usize,
    lowered_goals: usize,
    proof_steps: usize,
    clauses: usize,
    literals: usize,
    terms: usize,
    term_components: usize,
    local_contexts: usize,
    local_context_slots: usize,
    variable_maps: usize,
    variable_map_slots: usize,
    premise_maps: usize,
    premise_raw_maps: usize,
    premise_var_ids: usize,
    nested_simplification_steps: usize,
    estimated_heap_bytes: usize,
}

#[derive(Clone, Debug, Default)]
struct KernelContextStats {
    contexts: usize,
    symbol_tables: SymbolTableTotals,
    type_stores: TypeStoreTotals,
}

#[derive(Clone, Copy, Debug, Default)]
struct BindingProfileTotals {
    maps: usize,
    constant_defs: usize,
    typename_to_type: usize,
    type_to_typename: usize,
    datatype_defs: usize,
    name_to_typeclass: usize,
    typeclass_defs: usize,
    unqualified: usize,
    constant_to_alias: usize,
    name_to_module: usize,
    module_info: usize,
    instance_attr_defs: usize,
}

#[derive(Clone, Copy, Debug, Default)]
struct SymbolTableTotals {
    global_constant_modules: usize,
    global_constants: usize,
    global_constant_types: usize,
    scoped_constants: usize,
    scoped_constant_types: usize,
    name_to_symbol: usize,
    instance_to_symbol: usize,
    polymorphic_info: usize,
    match_eliminator_info: usize,
    type_to_element: usize,
    inhabited_type_constructors: usize,
    inhabited_type_constructor_witnesses: usize,
    inhabited_typeclasses: usize,
    inhabited_typeclass_witnesses: usize,
}

#[derive(Clone, Copy, Debug, Default)]
struct TypeStoreTotals {
    ground_type_modules: usize,
    ground_types: usize,
    ground_param_kind_modules: usize,
    ground_param_kinds: usize,
    datatype_to_ground_id: usize,
    arbitrary_to_ground_id: usize,
    typeclass_to_id: usize,
    typeclass_modules: usize,
    typeclasses: usize,
    typeclass_extends_sets: usize,
    typeclass_extends_entries: usize,
    typeclass_instances_sets: usize,
    typeclass_instances_entries: usize,
    typeclass_instance_scheme_sets: usize,
    typeclass_instance_schemes: usize,
}

fn main() {
    let current_dir = std::env::current_dir().expect("failed to get current dir");
    let total_start = Instant::now();
    let mut samples = Vec::new();

    sample("start", &mut samples);

    let project_start = Instant::now();
    let config = ProjectConfig {
        usage_mode: UsageMode::Check,
        ..ProjectConfig::default()
    };
    let mut project = Project::new_local(&current_dir, config).expect("failed to create project");
    let project_time = project_start.elapsed();
    sample("after project setup", &mut samples);

    let load_start = Instant::now();
    project.add_src_targets();
    project.add_pending_targets();
    let load_time = load_start.elapsed();
    sample("after full check-style load", &mut samples);

    {
        let errors = project.errors();
        if !errors.is_empty() {
            println!("loaded with {} module errors", errors.len());
            for (module_id, error) in errors.iter().take(10) {
                println!("  module {}: {}", module_id, error);
            }
        }
    }

    let (total_stats, mut module_stats) = collect_project_stats(&project);
    print_header(project_time, load_time, total_start.elapsed(), &samples);
    print_stats(&total_stats);
    print_top_modules(&mut module_stats);
    print_clear_sequence(&mut project);

    black_box(&project);
}

fn sample(label: &'static str, samples: &mut Vec<(&'static str, StatusMemory)>) {
    force_mimalloc_collect();
    samples.push((label, read_status_memory()));
}

fn force_mimalloc_collect() {
    unsafe {
        mi_collect(true);
    }
}

fn read_status_memory() -> StatusMemory {
    let Ok(status) = std::fs::read_to_string("/proc/self/status") else {
        return StatusMemory::default();
    };
    let mut memory = StatusMemory::default();
    for line in status.lines() {
        if let Some(value) = line.strip_prefix("VmRSS:") {
            memory.rss_kb = parse_status_kb(value);
        } else if let Some(value) = line.strip_prefix("VmHWM:") {
            memory.hwm_kb = parse_status_kb(value);
        }
    }
    memory
}

fn parse_status_kb(value: &str) -> usize {
    value
        .split_whitespace()
        .next()
        .and_then(|v| v.parse::<usize>().ok())
        .unwrap_or(0)
}

fn print_header(
    project_time: Duration,
    load_time: Duration,
    total_time: Duration,
    samples: &[(&'static str, StatusMemory)],
) {
    println!("profile_memory target: full check-style load");
    println!("project setup: {}", format_duration(project_time));
    println!("target/dependency load: {}", format_duration(load_time));
    println!("total measured so far: {}", format_duration(total_time));
    println!();
    println!("rss samples:");
    for (label, memory) in samples {
        println!(
            "  {:>28}: rss {:>9}, hwm {:>9}",
            label,
            format_kb(memory.rss_kb),
            format_kb(memory.hwm_kb)
        );
    }
}

fn collect_project_stats(project: &Project) -> (ProfileStats, Vec<ModuleProfile>) {
    let mut total = ProfileStats::default();
    let mut modules = Vec::new();
    for (descriptor, module_id) in project.iter_modules() {
        let Some(env) = project.get_env_by_id(module_id) else {
            continue;
        };
        let mut module = ModuleProfile {
            name: descriptor.to_string(),
            stats: ProfileStats::default(),
        };
        module.stats.modules = 1;
        add_env_stats(env, &mut module.stats);
        total.add_assign(&module.stats);
        modules.push(module);
    }
    (total, modules)
}

fn add_env_stats(env: &Environment, stats: &mut ProfileStats) {
    stats.environments += 1;
    stats.nodes += env.nodes.len();
    stats.binding_snapshots += env.binding_states.len();
    stats.token_infos += env.token_map.iter().count();
    stats.line_types += env.line_types.len();
    stats
        .current_binding_counts
        .add_counts(env.bindings.profile_counts());
    for bindings in &env.binding_states {
        stats
            .snapshot_binding_counts
            .add_counts(bindings.profile_counts());
    }
    if let Some(context) = &env.kernel_context {
        stats.env_kernel_contexts.add_context(context);
    }
    for lowered in &env.lowered_module_facts {
        add_lowered_fact(
            lowered,
            &mut stats.lowered_module_facts,
            &mut stats.lowered_kernel_contexts,
        );
    }

    for node in &env.nodes {
        match node {
            Node::Structural(_, lowered) => {
                stats.structural_nodes += 1;
                if let Some(lowered) = lowered {
                    add_lowered_fact(
                        lowered,
                        &mut stats.node_lowered_facts,
                        &mut stats.lowered_kernel_contexts,
                    );
                }
            }
            Node::Claim(_, _, lowered_goal, lowered_fact) => {
                stats.claim_nodes += 1;
                if let Some(lowered) = lowered_goal {
                    add_lowered_goal(
                        lowered,
                        &mut stats.lowered_goals,
                        &mut stats.lowered_kernel_contexts,
                    );
                }
                if let Some(lowered) = lowered_fact {
                    add_lowered_fact(
                        lowered,
                        &mut stats.node_lowered_facts,
                        &mut stats.lowered_kernel_contexts,
                    );
                }
            }
            Node::Block(block, _, lowered) => {
                stats.block_nodes += 1;
                if let Some(lowered) = lowered {
                    add_lowered_fact(
                        lowered,
                        &mut stats.node_lowered_facts,
                        &mut stats.lowered_kernel_contexts,
                    );
                }
                add_env_stats(&block.env, stats);
            }
        }
    }
}

fn add_lowered_fact(
    lowered: &LoweredFact,
    proof_stats: &mut ProofBucketStats,
    context_stats: &mut KernelContextStats,
) {
    proof_stats.lowered_facts += 1;
    add_step_slice(&lowered.steps, proof_stats);
    context_stats.add_context(&lowered.kernel_context);
}

fn add_lowered_goal(
    lowered: &LoweredGoal,
    proof_stats: &mut ProofBucketStats,
    context_stats: &mut KernelContextStats,
) {
    proof_stats.lowered_goals += 1;
    add_step_slice(&lowered.steps, proof_stats);
    context_stats.add_context(&lowered.kernel_context);
}

fn add_step_slice(steps: &[ProofStep], stats: &mut ProofBucketStats) {
    stats.estimated_heap_bytes += steps.len() * size_of::<ProofStep>();
    for step in steps {
        add_proof_step(step, stats, false);
    }
}

fn add_proof_step(step: &ProofStep, stats: &mut ProofBucketStats, nested: bool) {
    stats.proof_steps += 1;
    if nested {
        stats.nested_simplification_steps += 1;
        stats.estimated_heap_bytes += size_of::<ProofStep>();
    }
    add_clause(&step.clause, stats);
    add_rule(&step.rule, stats);
    add_premise_map(&step.premise_map, stats);
}

fn add_rule(rule: &Rule, stats: &mut ProofBucketStats) {
    match rule {
        Rule::Assumption(info) => {
            stats.estimated_heap_bytes += info.literals.capacity() * size_of::<Literal>();
            stats.literals += info.literals.len();
            for literal in &info.literals {
                add_literal(literal, stats);
            }
            add_local_context(&info.context, stats);
        }
        Rule::MultipleRewrite(info) => {
            stats.estimated_heap_bytes += info.active_ids.capacity() * size_of::<usize>();
            stats.estimated_heap_bytes += info.passive_ids.capacity() * size_of::<u32>();
        }
        Rule::Simplification(info) => {
            stats.estimated_heap_bytes += size_of::<ProofStep>();
            stats.estimated_heap_bytes += info.simplifying_ids.capacity() * size_of::<usize>();
            add_proof_step(&info.original, stats, true);
        }
        Rule::Resolution(_)
        | Rule::Rewrite(_)
        | Rule::Specialization(_)
        | Rule::EqualityFactoring(_)
        | Rule::EqualityResolution(_)
        | Rule::Injectivity(_)
        | Rule::BooleanReduction(_)
        | Rule::Extensionality(_)
        | Rule::PassiveContradiction(_) => {}
    }
}

fn add_premise_map(premise_map: &PremiseMap, stats: &mut ProofBucketStats) {
    stats.premise_maps += 1;
    stats.premise_raw_maps += premise_map.profile_raw_maps().len();
    stats.premise_var_ids += premise_map.profile_var_ids_len();
    stats.estimated_heap_bytes +=
        premise_map.profile_raw_maps_capacity() * size_of::<VariableMap>();
    stats.estimated_heap_bytes += premise_map.profile_var_ids_capacity() * size_of::<u32>();
    for raw_map in premise_map.profile_raw_maps() {
        add_variable_map(raw_map, stats);
    }
    add_local_context(premise_map.profile_pre_norm_context(), stats);
    add_variable_map(premise_map.profile_witness_map(), stats);
}

fn add_clause(clause: &Clause, stats: &mut ProofBucketStats) {
    stats.clauses += 1;
    stats.literals += clause.literals.len();
    stats.estimated_heap_bytes += clause.literals.capacity() * size_of::<Literal>();
    for literal in &clause.literals {
        add_literal(literal, stats);
    }
    add_local_context(&clause.context, stats);
}

fn add_literal(literal: &Literal, stats: &mut ProofBucketStats) {
    add_term(&literal.left, stats);
    add_term(&literal.right, stats);
}

fn add_local_context(context: &LocalContext, stats: &mut ProofBucketStats) {
    stats.local_contexts += 1;
    stats.local_context_slots += context.len();
    for term in context.get_var_types().iter().flatten() {
        add_term(term, stats);
    }
}

fn add_variable_map(variable_map: &VariableMap, stats: &mut ProofBucketStats) {
    stats.variable_maps += 1;
    stats.variable_map_slots += variable_map.profile_slot_count();
    stats.estimated_heap_bytes += variable_map.profile_capacity() * size_of::<Option<Term>>();
    for (_, term) in variable_map.iter() {
        add_term(term, stats);
    }
}

fn add_term(term: &Term, stats: &mut ProofBucketStats) {
    stats.terms += 1;
    stats.term_components += term.profile_component_len();
    stats.estimated_heap_bytes += term.profile_component_capacity_bytes();
}

impl ProfileStats {
    fn add_assign(&mut self, other: &ProfileStats) {
        self.modules += other.modules;
        self.environments += other.environments;
        self.nodes += other.nodes;
        self.structural_nodes += other.structural_nodes;
        self.claim_nodes += other.claim_nodes;
        self.block_nodes += other.block_nodes;
        self.binding_snapshots += other.binding_snapshots;
        self.token_infos += other.token_infos;
        self.line_types += other.line_types;
        self.lowered_module_facts
            .add_assign(&other.lowered_module_facts);
        self.node_lowered_facts
            .add_assign(&other.node_lowered_facts);
        self.lowered_goals.add_assign(&other.lowered_goals);
        self.env_kernel_contexts
            .add_assign(&other.env_kernel_contexts);
        self.lowered_kernel_contexts
            .add_assign(&other.lowered_kernel_contexts);
        self.current_binding_counts
            .add_assign(&other.current_binding_counts);
        self.snapshot_binding_counts
            .add_assign(&other.snapshot_binding_counts);
    }
}

impl ProofBucketStats {
    fn add_assign(&mut self, other: &ProofBucketStats) {
        self.lowered_facts += other.lowered_facts;
        self.lowered_goals += other.lowered_goals;
        self.proof_steps += other.proof_steps;
        self.clauses += other.clauses;
        self.literals += other.literals;
        self.terms += other.terms;
        self.term_components += other.term_components;
        self.local_contexts += other.local_contexts;
        self.local_context_slots += other.local_context_slots;
        self.variable_maps += other.variable_maps;
        self.variable_map_slots += other.variable_map_slots;
        self.premise_maps += other.premise_maps;
        self.premise_raw_maps += other.premise_raw_maps;
        self.premise_var_ids += other.premise_var_ids;
        self.nested_simplification_steps += other.nested_simplification_steps;
        self.estimated_heap_bytes += other.estimated_heap_bytes;
    }
}

impl KernelContextStats {
    fn add_context(&mut self, context: &KernelContext) {
        self.contexts += 1;
        self.symbol_tables
            .add_counts(context.symbol_table.profile_counts());
        self.type_stores
            .add_counts(context.type_store.profile_counts());
    }

    fn add_assign(&mut self, other: &KernelContextStats) {
        self.contexts += other.contexts;
        self.symbol_tables.add_assign(&other.symbol_tables);
        self.type_stores.add_assign(&other.type_stores);
    }
}

impl BindingProfileTotals {
    fn add_counts(&mut self, counts: BindingMapProfileCounts) {
        self.maps += 1;
        self.constant_defs += counts.constant_defs;
        self.typename_to_type += counts.typename_to_type;
        self.type_to_typename += counts.type_to_typename;
        self.datatype_defs += counts.datatype_defs;
        self.name_to_typeclass += counts.name_to_typeclass;
        self.typeclass_defs += counts.typeclass_defs;
        self.unqualified += counts.unqualified;
        self.constant_to_alias += counts.constant_to_alias;
        self.name_to_module += counts.name_to_module;
        self.module_info += counts.module_info;
        self.instance_attr_defs += counts.instance_attr_defs;
    }

    fn add_assign(&mut self, other: &BindingProfileTotals) {
        self.maps += other.maps;
        self.constant_defs += other.constant_defs;
        self.typename_to_type += other.typename_to_type;
        self.type_to_typename += other.type_to_typename;
        self.datatype_defs += other.datatype_defs;
        self.name_to_typeclass += other.name_to_typeclass;
        self.typeclass_defs += other.typeclass_defs;
        self.unqualified += other.unqualified;
        self.constant_to_alias += other.constant_to_alias;
        self.name_to_module += other.name_to_module;
        self.module_info += other.module_info;
        self.instance_attr_defs += other.instance_attr_defs;
    }

    fn total_entries(self) -> usize {
        self.constant_defs
            + self.typename_to_type
            + self.type_to_typename
            + self.datatype_defs
            + self.name_to_typeclass
            + self.typeclass_defs
            + self.unqualified
            + self.constant_to_alias
            + self.name_to_module
            + self.module_info
            + self.instance_attr_defs
    }
}

impl SymbolTableTotals {
    fn add_counts(&mut self, counts: SymbolTableProfileCounts) {
        self.global_constant_modules += counts.global_constant_modules;
        self.global_constants += counts.global_constants;
        self.global_constant_types += counts.global_constant_types;
        self.scoped_constants += counts.scoped_constants;
        self.scoped_constant_types += counts.scoped_constant_types;
        self.name_to_symbol += counts.name_to_symbol;
        self.instance_to_symbol += counts.instance_to_symbol;
        self.polymorphic_info += counts.polymorphic_info;
        self.match_eliminator_info += counts.match_eliminator_info;
        self.type_to_element += counts.type_to_element;
        self.inhabited_type_constructors += counts.inhabited_type_constructors;
        self.inhabited_type_constructor_witnesses += counts.inhabited_type_constructor_witnesses;
        self.inhabited_typeclasses += counts.inhabited_typeclasses;
        self.inhabited_typeclass_witnesses += counts.inhabited_typeclass_witnesses;
    }

    fn add_assign(&mut self, other: &SymbolTableTotals) {
        self.global_constant_modules += other.global_constant_modules;
        self.global_constants += other.global_constants;
        self.global_constant_types += other.global_constant_types;
        self.scoped_constants += other.scoped_constants;
        self.scoped_constant_types += other.scoped_constant_types;
        self.name_to_symbol += other.name_to_symbol;
        self.instance_to_symbol += other.instance_to_symbol;
        self.polymorphic_info += other.polymorphic_info;
        self.match_eliminator_info += other.match_eliminator_info;
        self.type_to_element += other.type_to_element;
        self.inhabited_type_constructors += other.inhabited_type_constructors;
        self.inhabited_type_constructor_witnesses += other.inhabited_type_constructor_witnesses;
        self.inhabited_typeclasses += other.inhabited_typeclasses;
        self.inhabited_typeclass_witnesses += other.inhabited_typeclass_witnesses;
    }
}

impl TypeStoreTotals {
    fn add_counts(&mut self, counts: TypeStoreProfileCounts) {
        self.ground_type_modules += counts.ground_type_modules;
        self.ground_types += counts.ground_types;
        self.ground_param_kind_modules += counts.ground_param_kind_modules;
        self.ground_param_kinds += counts.ground_param_kinds;
        self.datatype_to_ground_id += counts.datatype_to_ground_id;
        self.arbitrary_to_ground_id += counts.arbitrary_to_ground_id;
        self.typeclass_to_id += counts.typeclass_to_id;
        self.typeclass_modules += counts.typeclass_modules;
        self.typeclasses += counts.typeclasses;
        self.typeclass_extends_sets += counts.typeclass_extends_sets;
        self.typeclass_extends_entries += counts.typeclass_extends_entries;
        self.typeclass_instances_sets += counts.typeclass_instances_sets;
        self.typeclass_instances_entries += counts.typeclass_instances_entries;
        self.typeclass_instance_scheme_sets += counts.typeclass_instance_scheme_sets;
        self.typeclass_instance_schemes += counts.typeclass_instance_schemes;
    }

    fn add_assign(&mut self, other: &TypeStoreTotals) {
        self.ground_type_modules += other.ground_type_modules;
        self.ground_types += other.ground_types;
        self.ground_param_kind_modules += other.ground_param_kind_modules;
        self.ground_param_kinds += other.ground_param_kinds;
        self.datatype_to_ground_id += other.datatype_to_ground_id;
        self.arbitrary_to_ground_id += other.arbitrary_to_ground_id;
        self.typeclass_to_id += other.typeclass_to_id;
        self.typeclass_modules += other.typeclass_modules;
        self.typeclasses += other.typeclasses;
        self.typeclass_extends_sets += other.typeclass_extends_sets;
        self.typeclass_extends_entries += other.typeclass_extends_entries;
        self.typeclass_instances_sets += other.typeclass_instances_sets;
        self.typeclass_instances_entries += other.typeclass_instances_entries;
        self.typeclass_instance_scheme_sets += other.typeclass_instance_scheme_sets;
        self.typeclass_instance_schemes += other.typeclass_instance_schemes;
    }
}

fn print_stats(stats: &ProfileStats) {
    println!();
    println!("retained object counts:");
    println!(
        "  modules/envs/nodes: {} modules, {} envs, {} nodes ({} structural, {} claims, {} blocks)",
        stats.modules,
        stats.environments,
        stats.nodes,
        stats.structural_nodes,
        stats.claim_nodes,
        stats.block_nodes
    );
    println!(
        "  binding maps: {} current maps / {} entries; {} snapshots / {} entries",
        stats.current_binding_counts.maps,
        stats.current_binding_counts.total_entries(),
        stats.snapshot_binding_counts.maps,
        stats.snapshot_binding_counts.total_entries()
    );
    println!(
        "  tokens/line map entries: {} token infos, {} line entries",
        stats.token_infos, stats.line_types
    );
    print_proof_bucket("module lowered facts", &stats.lowered_module_facts);
    print_proof_bucket("node lowered facts", &stats.node_lowered_facts);
    print_proof_bucket("lowered goals", &stats.lowered_goals);
    print_context_bucket("env kernel contexts", &stats.env_kernel_contexts);
    print_context_bucket("lowered kernel contexts", &stats.lowered_kernel_contexts);
}

fn print_proof_bucket(label: &str, stats: &ProofBucketStats) {
    println!(
        "  {:>21}: facts {:>8}, goals {:>6}, steps {:>10}, literals {:>10}, term comps {:>12}, est heap {:>9}",
        label,
        stats.lowered_facts,
        stats.lowered_goals,
        stats.proof_steps,
        stats.literals,
        stats.term_components,
        format_bytes(stats.estimated_heap_bytes)
    );
}

fn print_context_bucket(label: &str, stats: &KernelContextStats) {
    println!(
        "  {:>21}: contexts {:>9}, summed global consts {:>11}, scoped consts {:>10}, ground types {:>10}, typeclasses {:>9}",
        label,
        stats.contexts,
        stats.symbol_tables.global_constants,
        stats.symbol_tables.scoped_constants,
        stats.type_stores.ground_types,
        stats.type_stores.typeclasses
    );
}

fn print_top_modules(modules: &mut [ModuleProfile]) {
    println!();
    println!("top modules by retained local lowered facts:");
    modules.sort_by_key(|module| {
        std::cmp::Reverse(
            module.stats.lowered_module_facts.proof_steps
                + module.stats.node_lowered_facts.proof_steps,
        )
    });
    for module in modules.iter().take(12) {
        println!(
            "  {:>10} steps  {:>8} facts  {}",
            module.stats.lowered_module_facts.proof_steps
                + module.stats.node_lowered_facts.proof_steps,
            module.stats.lowered_module_facts.lowered_facts
                + module.stats.node_lowered_facts.lowered_facts,
            module.name
        );
    }

    println!();
    println!("top modules by binding snapshots:");
    modules.sort_by_key(|module| std::cmp::Reverse(module.stats.binding_snapshots));
    for module in modules.iter().take(12) {
        println!(
            "  {:>8} snapshots  {:>10} snapshot entries  {}",
            module.stats.binding_snapshots,
            module.stats.snapshot_binding_counts.total_entries(),
            module.name
        );
    }
}

fn print_clear_sequence(project: &mut Project) {
    println!();
    println!("rss after destructive diagnostic clears:");
    let mut previous = read_status_memory().rss_kb;
    println!("  {:>34}: {}", "before clears", format_kb(previous));
    for bucket in [
        ClearBucket::NodeAndModuleLowered,
        ClearBucket::KernelContexts,
        ClearBucket::BindingSnapshots,
        ClearBucket::CurrentBindings,
        ClearBucket::TokenAndLineMaps,
        ClearBucket::NodePayloads,
        ClearBucket::Nodes,
    ] {
        project.profile_visit_envs_mut(|_, env| clear_env_bucket(env, bucket));
        force_mimalloc_collect();
        let current = read_status_memory().rss_kb;
        let delta = previous as isize - current as isize;
        println!(
            "  {:>34}: {} ({:+})",
            bucket.label(),
            format_kb(current),
            format_signed_kb(delta)
        );
        previous = current;
    }
}

fn clear_env_bucket(env: &mut Environment, bucket: ClearBucket) {
    match bucket {
        ClearBucket::NodeAndModuleLowered => {
            env.lowered_module_facts.clear();
            env.lowered_module_facts.shrink_to_fit();
        }
        ClearBucket::KernelContexts => {
            env.kernel_context = None;
        }
        ClearBucket::BindingSnapshots => {
            env.binding_states.clear();
            env.binding_states.shrink_to_fit();
        }
        ClearBucket::CurrentBindings => {
            env.bindings = BindingMap::profile_empty(env.module_id);
        }
        ClearBucket::TokenAndLineMaps => {
            env.token_map = Default::default();
            env.line_types.clear();
            env.line_types.shrink_to_fit();
            env.doc_comments.clear();
            env.doc_comments.shrink_to_fit();
            env.module_doc_comments.clear();
            env.module_doc_comments.shrink_to_fit();
        }
        ClearBucket::NodePayloads => {}
        ClearBucket::Nodes => {
            env.nodes.clear();
            env.nodes.shrink_to_fit();
            return;
        }
    }

    let dummy = if matches!(bucket, ClearBucket::NodePayloads) {
        Some(dummy_fact(env.module_id))
    } else {
        None
    };
    for node in &mut env.nodes {
        if let Some(dummy) = &dummy {
            match node {
                Node::Block(block, fact, lowered) => {
                    block.args.clear();
                    block.args.shrink_to_fit();
                    block.source_range = None;
                    *fact = None;
                    *lowered = None;
                    clear_env_bucket(&mut block.env, bucket);
                }
                _ => {
                    *node = Node::Structural(dummy.clone(), None);
                }
            }
            continue;
        }

        match node {
            Node::Structural(_, lowered) => {
                if matches!(bucket, ClearBucket::NodeAndModuleLowered) {
                    *lowered = None;
                }
            }
            Node::Claim(_, _, lowered_goal, lowered_fact) => {
                if matches!(bucket, ClearBucket::NodeAndModuleLowered) {
                    *lowered_goal = None;
                    *lowered_fact = None;
                }
            }
            Node::Block(block, _, lowered) => {
                if matches!(bucket, ClearBucket::NodeAndModuleLowered) {
                    *lowered = None;
                }
                clear_env_bucket(&mut block.env, bucket);
            }
        }
    }
}

fn dummy_fact(module_id: acorn::module::ModuleId) -> Fact {
    let range = Range {
        start: Position {
            line: 0,
            character: 0,
        },
        end: Position {
            line: 0,
            character: 0,
        },
    };
    Fact::proposition(
        AcornValue::Bool(true),
        Source::anonymous(module_id, range, 0),
    )
}

fn format_duration(duration: Duration) -> String {
    let seconds = duration.as_secs_f64();
    if seconds >= 1.0 {
        format!("{:.3}s", seconds)
    } else {
        format!("{:.1}ms", seconds * 1000.0)
    }
}

fn format_kb(kb: usize) -> String {
    format_bytes(kb * 1024)
}

fn format_signed_kb(kb: isize) -> String {
    if kb >= 0 {
        format!("-{}", format_kb(kb as usize))
    } else {
        format!("+{}", format_kb((-kb) as usize))
    }
}

fn format_bytes(bytes: usize) -> String {
    const KIB: f64 = 1024.0;
    const MIB: f64 = KIB * 1024.0;
    const GIB: f64 = MIB * 1024.0;
    let bytes = bytes as f64;
    if bytes >= GIB {
        format!("{:.2} GiB", bytes / GIB)
    } else if bytes >= MIB {
        format!("{:.1} MiB", bytes / MIB)
    } else if bytes >= KIB {
        format!("{:.1} KiB", bytes / KIB)
    } else {
        format!("{} B", bytes as usize)
    }
}

use tower_lsp::lsp_types::Range;

use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::goal::Goal;
use crate::elaborator::lowering::{LoweredFact, LoweredGoal};
use crate::elaborator::source::Source;
use crate::kernel::clause::Clause;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::proof_step::Rule;
use crate::module::ModuleId;
use crate::project::UsageMode;
use std::sync::Arc;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LoweredFactId(usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct LoweredGoalId(usize);

#[derive(Clone)]
pub struct LoweredGoalEntry {
    pub lowered_goal: LoweredGoal,
    pub bindings: BindingMap,
}

#[derive(Clone)]
pub enum LoweredItem {
    Fact {
        fact: LoweredFactId,
        first_line: u32,
        last_line: u32,
    },
    Claim {
        goal: LoweredGoalId,
        post_fact: LoweredFactId,
        first_line: u32,
        last_line: u32,
    },
    Block {
        items: Vec<LoweredItem>,
        external_fact: Option<LoweredFactId>,
        first_line: u32,
        last_line: u32,
    },
}

#[derive(Clone)]
pub struct CheckAssumption {
    pub clause: Clause,
    pub source: Source,
}

#[derive(Clone)]
pub struct CheckExportFact {
    pub assumptions: Vec<CheckAssumption>,
    pub kernel_context: KernelContext,
}

impl CheckExportFact {
    fn from_lowered(fact: &LoweredFact) -> Self {
        let assumptions = fact
            .steps
            .iter()
            .map(|step| {
                let Rule::Assumption(info) = &step.rule else {
                    panic!("exported lowered facts must contain only assumption steps");
                };
                CheckAssumption {
                    clause: step.clause.clone(),
                    source: info.source.clone(),
                }
            })
            .collect();
        Self {
            assumptions,
            kernel_context: fact.kernel_context.clone(),
        }
    }
}

#[derive(Clone)]
pub enum ExportedFact {
    Check(Arc<CheckExportFact>),
    Prove(Arc<LoweredFact>),
}

#[derive(Clone)]
pub struct ModuleExport {
    pub module_id: ModuleId,
    pub bindings: BindingMap,
    pub final_kernel_context: KernelContext,
    facts: Vec<ExportedFact>,
}

impl ModuleExport {
    pub fn new(
        module_id: ModuleId,
        bindings: BindingMap,
        final_kernel_context: KernelContext,
        facts: Vec<ExportedFact>,
    ) -> Self {
        Self {
            module_id,
            bindings,
            final_kernel_context,
            facts,
        }
    }

    pub fn from_lowered(
        bindings: BindingMap,
        lowered: &LoweredModule,
        usage_mode: UsageMode,
    ) -> Self {
        let facts = lowered
            .module_fact_ids
            .iter()
            .map(|id| match usage_mode {
                UsageMode::Check => {
                    ExportedFact::Check(Arc::new(CheckExportFact::from_lowered(lowered.fact(*id))))
                }
                UsageMode::Verify | UsageMode::Ide => {
                    ExportedFact::Prove(Arc::clone(&lowered.facts[id.0]))
                }
            })
            .collect();
        Self::new(
            lowered.module_id,
            bindings,
            lowered.final_kernel_context.clone(),
            facts,
        )
    }

    pub fn facts(&self) -> impl Iterator<Item = &ExportedFact> {
        self.facts.iter()
    }

    pub fn fact_count(&self) -> usize {
        self.facts.len()
    }

    #[doc(hidden)]
    pub fn profile_clear_facts(&mut self) {
        self.facts.clear();
        self.facts.shrink_to_fit();
    }
}

#[derive(Clone)]
pub struct LoweredModule {
    pub module_id: ModuleId,
    pub initial_bindings: BindingMap,
    pub final_kernel_context: KernelContext,
    facts: Vec<Arc<LoweredFact>>,
    goals: Vec<LoweredGoalEntry>,
    pub module_fact_ids: Vec<LoweredFactId>,
    pub items: Vec<LoweredItem>,
    pub top_level_axiom_ranges: Vec<Range>,
}

impl LoweredModule {
    pub fn new(module_id: ModuleId, initial_bindings: BindingMap) -> Self {
        Self {
            module_id,
            initial_bindings,
            final_kernel_context: KernelContext::new(),
            facts: Vec::new(),
            goals: Vec::new(),
            module_fact_ids: Vec::new(),
            items: Vec::new(),
            top_level_axiom_ranges: Vec::new(),
        }
    }

    pub fn add_fact(&mut self, fact: LoweredFact) -> LoweredFactId {
        let id = LoweredFactId(self.facts.len());
        self.facts.push(Arc::new(fact));
        id
    }

    pub fn add_goal(&mut self, lowered_goal: LoweredGoal, bindings: BindingMap) -> LoweredGoalId {
        let id = LoweredGoalId(self.goals.len());
        self.goals.push(LoweredGoalEntry {
            lowered_goal,
            bindings,
        });
        id
    }

    pub fn fact(&self, id: LoweredFactId) -> &LoweredFact {
        self.facts[id.0].as_ref()
    }

    pub fn goal(&self, id: LoweredGoalId) -> &LoweredGoalEntry {
        &self.goals[id.0]
    }

    pub fn module_facts(&self) -> impl Iterator<Item = &LoweredFact> {
        self.module_fact_ids.iter().map(|id| self.fact(*id))
    }

    pub fn facts(&self) -> impl Iterator<Item = &LoweredFact> {
        self.facts.iter().map(|fact| fact.as_ref())
    }

    pub fn goals(&self) -> impl Iterator<Item = (LoweredGoalId, &LoweredGoalEntry)> {
        self.goals
            .iter()
            .enumerate()
            .map(|(i, entry)| (LoweredGoalId(i), entry))
    }

    pub fn goal_by_name(&self, name: &str) -> Option<(LoweredGoalId, &LoweredGoalEntry)> {
        self.goals()
            .find(|(_, entry)| entry.lowered_goal.goal.name == name)
    }

    pub fn goal_for_source_goal(&self, goal: &Goal) -> Option<(LoweredGoalId, &LoweredGoalEntry)> {
        self.goals().find(|(_, entry)| {
            let lowered_goal = &entry.lowered_goal.goal;
            lowered_goal.name == goal.name
                && lowered_goal.first_line == goal.first_line
                && lowered_goal.last_line == goal.last_line
        })
    }

    pub fn visible_facts_for_goal(&self, goal: LoweredGoalId) -> Option<Vec<&LoweredFact>> {
        let mut visible = Vec::new();
        let fact_ids = self.visible_fact_ids_for_goal(goal, &self.items, &mut visible)?;
        Some(fact_ids.into_iter().map(|id| self.fact(id)).collect())
    }

    pub fn fact_for_source_range(&self, range: Range) -> Option<&LoweredFact> {
        self.fact_id_for_source_range(range, &self.items)
            .map(|id| self.fact(id))
    }

    pub fn goal_count(&self) -> usize {
        self.goals.len()
    }

    pub fn fact_count(&self) -> usize {
        self.facts.len()
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    #[doc(hidden)]
    pub fn profile_clear_lowered(&mut self) {
        self.facts.clear();
        self.facts.shrink_to_fit();
        self.goals.clear();
        self.goals.shrink_to_fit();
        self.module_fact_ids.clear();
        self.module_fact_ids.shrink_to_fit();
        self.items.clear();
        self.items.shrink_to_fit();
        self.top_level_axiom_ranges.clear();
        self.top_level_axiom_ranges.shrink_to_fit();
        self.final_kernel_context = KernelContext::new();
    }

    fn visible_fact_ids_for_goal(
        &self,
        goal: LoweredGoalId,
        items: &[LoweredItem],
        visible: &mut Vec<LoweredFactId>,
    ) -> Option<Vec<LoweredFactId>> {
        for item in items {
            match item {
                LoweredItem::Fact { fact, .. } => {
                    visible.push(*fact);
                }
                LoweredItem::Claim {
                    goal: item_goal,
                    post_fact,
                    ..
                } => {
                    if *item_goal == goal {
                        return Some(visible.clone());
                    }
                    visible.push(*post_fact);
                }
                LoweredItem::Block {
                    items,
                    external_fact,
                    ..
                } => {
                    let mut child_visible = visible.clone();
                    if let Some(facts) =
                        self.visible_fact_ids_for_goal(goal, items, &mut child_visible)
                    {
                        return Some(facts);
                    }
                    if let Some(fact) = external_fact {
                        visible.push(*fact);
                    }
                }
            }
        }
        None
    }

    fn fact_id_for_source_range(
        &self,
        range: Range,
        items: &[LoweredItem],
    ) -> Option<LoweredFactId> {
        for item in items {
            match item {
                LoweredItem::Fact {
                    fact,
                    first_line,
                    last_line,
                }
                | LoweredItem::Claim {
                    post_fact: fact,
                    first_line,
                    last_line,
                    ..
                } => {
                    if *first_line == range.start.line && *last_line == range.end.line {
                        return Some(*fact);
                    }
                }
                LoweredItem::Block { items, .. } => {
                    if let Some(fact) = self.fact_id_for_source_range(range, items) {
                        return Some(fact);
                    }
                }
            }
        }
        None
    }
}

pub struct LoweringResult {
    pub module: LoweredModule,
    pub error: Option<String>,
}

use tower_lsp::lsp_types::Range;

use crate::elaborator::binding_map::BindingMap;
use crate::elaborator::lowering::{LoweredFact, LoweredGoal};
use crate::kernel::kernel_context::KernelContext;
use crate::module::ModuleId;

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
    },
    Block {
        items: Vec<LoweredItem>,
        external_fact: Option<LoweredFactId>,
        first_line: u32,
        last_line: u32,
    },
}

#[derive(Clone)]
pub struct LoweredModule {
    pub module_id: ModuleId,
    pub initial_bindings: BindingMap,
    pub final_kernel_context: KernelContext,
    facts: Vec<LoweredFact>,
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
        self.facts.push(fact);
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
        &self.facts[id.0]
    }

    pub fn goal(&self, id: LoweredGoalId) -> &LoweredGoalEntry {
        &self.goals[id.0]
    }

    pub fn module_facts(&self) -> impl Iterator<Item = &LoweredFact> {
        self.module_fact_ids.iter().map(|id| self.fact(*id))
    }

    pub fn goal_count(&self) -> usize {
        self.goals.len()
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}

pub struct LoweringResult {
    pub module: LoweredModule,
    pub error: Option<String>,
}

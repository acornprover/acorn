use super::*;

/// A test wrapper that combines a EqualityGraph with its KernelContext.
struct TestGraph {
    graph: EqualityGraph,
    context: KernelContext,
}

impl TestGraph {
    fn new() -> TestGraph {
        let mut context = KernelContext::new();
        // c0-c7: Bool constants
        context.parse_constants(&["c0", "c1", "c2", "c3", "c4", "c5", "c6", "c7"], "Bool");
        // g1-g4: Bool -> Bool functions
        context.parse_constants(&["g1", "g2", "g3", "g4"], "Bool -> Bool");
        // g5-g10: (Bool, Bool) -> Bool functions (replacing m0-m5)
        context.parse_constants(
            &["g5", "g6", "g7", "g8", "g9", "g10"],
            "(Bool, Bool) -> Bool",
        );
        TestGraph {
            graph: EqualityGraph::new(),
            context,
        }
    }

    fn with_clauses(clauses: &[&str]) -> TestGraph {
        let mut tg = TestGraph::new();
        for (i, s) in clauses.iter().enumerate() {
            tg.insert_clause_str(s, StepId(i));
        }
        tg
    }

    fn insert_term_str(&mut self, s: &str) -> TermId {
        let id = self.graph.insert_term(&Term::parse(s), &self.context);
        self.graph.validate();
        id
    }

    fn insert_clause_str(&mut self, s: &str, step: StepId) {
        let clause = self.context.parse_clause(s, &[]);
        self.graph.insert_clause(&clause, step, &self.context);
        self.graph.validate();
    }

    fn assert_eq(&self, t1: TermId, t2: TermId) {
        assert_eq!(self.graph.get_group_id(t1), self.graph.get_group_id(t2));
    }

    fn assert_ne(&self, t1: TermId, t2: TermId) {
        assert_ne!(self.graph.get_group_id(t1), self.graph.get_group_id(t2));
    }

    fn set_eq(&mut self, t1: TermId, t2: TermId, pattern_id: StepId) {
        self.graph.set_terms_equal(t1, t2, pattern_id, None);
        self.graph.validate();
        self.assert_eq(t1, t2);
    }

    fn get_str(&self, s: &str) -> TermId {
        self.graph.get_term_id(&Term::parse(s)).unwrap()
    }

    fn check_clause_str(&mut self, s: &str) {
        let clause = self.context.parse_clause(s, &[]);
        if !self.graph.check_clause(&clause, &self.context) {
            panic!("check_clause_str(\"{}\") failed", s);
        }
    }

    fn get_step_ids(&self, term1: TermId, term2: TermId) -> Vec<usize> {
        self.graph.get_step_ids(term1, term2)
    }

    fn set_terms_not_equal(&mut self, term1: TermId, term2: TermId, step: StepId) {
        self.graph.set_terms_not_equal(term1, term2, step);
    }

    fn has_contradiction_trace(&self) -> bool {
        self.graph.has_contradiction_trace()
    }

    fn has_contradiction(&self) -> bool {
        self.graph.has_contradiction()
    }

    #[allow(dead_code)]
    fn show_graph(&self) {
        self.graph.show_graph();
    }

    fn update_group_id(&mut self, group_id: GroupId) -> GroupId {
        self.graph.update_group_id(group_id)
    }

    fn get_group_id(&self, term_id: TermId) -> GroupId {
        self.graph.get_group_id(term_id)
    }
}

#[test]
fn test_identifying_atomic_subterms() {
    let mut g = TestGraph::new();
    let id1 = g.insert_term_str("c1(c2, c3)");
    let id2 = g.insert_term_str("c1(c4, c3)");
    g.assert_ne(id1, id2);
    let c2id = g.get_str("c2");
    let c4id = g.get_str("c4");
    g.assert_ne(c2id, c4id);
    g.set_eq(c2id, c4id, StepId(0));
    g.assert_eq(id1, id2);
    assert_eq!(g.get_step_ids(id1, id2), vec![0]);
}

#[test]
fn test_multilevel_cascade() {
    let mut g = TestGraph::new();
    let term1 = g.insert_term_str("c1(c2(c3, c4), c2(c4, c3))");
    let term2 = g.insert_term_str("c1(c5, c5)");
    g.assert_ne(term1, term2);
    let sub1 = g.insert_term_str("c2(c3, c3)");
    let sub2 = g.get_str("c5");
    g.assert_ne(sub1, sub2);
    g.set_eq(sub1, sub2, StepId(0));
    let c3 = g.get_str("c3");
    let c4 = g.get_str("c4");
    g.assert_ne(c3, c4);
    g.set_eq(c3, c4, StepId(1));
    g.assert_eq(term1, term2);
    assert_eq!(g.get_step_ids(term1, term2), vec![0, 1]);
}

#[test]
fn test_identifying_heads() {
    let mut g = TestGraph::new();
    let id1 = g.insert_term_str("c1(c2, c3)");
    let id2 = g.insert_term_str("c4(c2, c3)");
    g.assert_ne(id1, id2);
    let c1 = g.get_str("c1");
    let c4 = g.get_str("c4");
    g.set_eq(c1, c4, StepId(0));
    g.assert_eq(id1, id2);
    assert_eq!(g.get_step_ids(id1, id2), vec![0]);
}

#[test]
fn test_skipping_unneeded_steps() {
    let mut g = TestGraph::new();
    let c0 = g.insert_term_str("c0");
    let c1 = g.insert_term_str("c1");
    let c2 = g.insert_term_str("c2");
    let c3 = g.insert_term_str("c3");
    let c4 = g.insert_term_str("c4");
    let c5 = g.insert_term_str("c5");
    g.set_eq(c1, c2, StepId(0));
    g.set_eq(c4, c5, StepId(1));
    g.set_eq(c0, c1, StepId(2));
    g.set_eq(c3, c4, StepId(3));
    g.set_eq(c0, c3, StepId(4));
    assert_eq!(g.get_step_ids(c0, c3), vec![4]);
}

#[test]
fn test_finding_contradiction() {
    let mut g = TestGraph::new();
    let term1 = g.insert_term_str("c1(c2, c3)");
    let term2 = g.insert_term_str("c4(c5, c6)");
    g.set_terms_not_equal(term1, term2, StepId(0));
    assert!(!g.has_contradiction_trace());
    let c1 = g.get_str("c1");
    let c4 = g.get_str("c4");
    g.set_eq(c1, c4, StepId(1));
    assert!(!g.has_contradiction_trace());
    let c2 = g.get_str("c2");
    let c5 = g.get_str("c5");
    g.set_eq(c2, c5, StepId(2));
    assert!(!g.has_contradiction_trace());
    let c3 = g.get_str("c3");
    let c6 = g.get_str("c6");
    g.set_eq(c3, c6, StepId(3));
    assert!(g.has_contradiction_trace());
}

#[test]
fn test_clause_reduction_basic() {
    let mut g = TestGraph::new();
    g.insert_clause_str("c1 = c2 or c3 != c4 or c5 != c6", StepId(0));
    assert!(!g.has_contradiction());
    g.insert_clause_str("c1 != c2", StepId(1));
    assert!(!g.has_contradiction());
    g.insert_clause_str("c3 = c4", StepId(2));
    assert!(!g.has_contradiction());
    g.insert_clause_str("c5 = c6", StepId(3));
    assert!(g.has_contradiction());
}

#[test]
fn test_clause_reduction_two_to_zero() {
    let mut g = TestGraph::new();
    g.insert_clause_str("c1 = c2 or c1 = c3", StepId(0));
    assert!(!g.has_contradiction());
    g.insert_clause_str("c2 = c4", StepId(1));
    assert!(!g.has_contradiction());
    g.insert_clause_str("c3 = c4", StepId(2));
    assert!(!g.has_contradiction());
    g.insert_clause_str("c1 != c4", StepId(3));
    assert!(g.has_contradiction());
}

#[test]
fn test_subterm_triggering_clause() {
    let mut g = TestGraph::new();
    // Use g1, g4 (Bool -> Bool) for single-arg predicates
    g.insert_clause_str("g1(c2) != g1(c3) or g4(c2) != g4(c3)", StepId(0));
    assert!(!g.has_contradiction());
    g.insert_clause_str("c2 = c3", StepId(1));
    assert!(g.has_contradiction());
}

#[test]
fn test_hypotheses_then_imp() {
    let mut g =
        TestGraph::with_clauses(&["g1(c1)", "g2(c1)", "not g1(c1) or not g2(c1) or g3(c1)"]);
    g.check_clause_str("g3(c1)");
}

#[test]
fn test_imp_then_hypotheses() {
    let mut g =
        TestGraph::with_clauses(&["not g1(c1) or not g2(c1) or g3(c1)", "g1(c1)", "g2(c1)"]);
    g.check_clause_str("g3(c1)");
}

#[test]
fn test_term_graph_rewriting_equality() {
    // Use g6, g7 ((Bool, Bool) -> Bool) for two-arg functions
    let mut g = TestGraph::with_clauses(&["g6(c1, g7(c2, c3)) = c4", "g7(c2, c3) = g7(c3, c2)"]);
    g.check_clause_str("g6(c1, g7(c3, c2)) = c4");
}

#[test]
fn test_term_graph_rewriting_inequality() {
    // Use g6, g7 ((Bool, Bool) -> Bool) for two-arg functions
    let mut g = TestGraph::with_clauses(&["g6(c1, g7(c2, c3)) != c4", "g7(c2, c3) = g7(c3, c2)"]);
    g.check_clause_str("g6(c1, g7(c3, c2)) != c4");
}

#[test]
fn test_term_graph_concluding_opposing_literals() {
    let mut g = TestGraph::with_clauses(&[
        "not g9(c6, g10(c1, c0))",
        "g9(c6, c6) or g8(c6, c6)",
        "not g8(c6, c6) or g9(c6, c6)",
        "g10(c1, c0) = c6",
        "not g9(c6, c6)",
    ]);

    g.check_clause_str("g8(c6, c6)");
}

#[test]
fn test_term_graph_checking_long_clause() {
    let mut g = TestGraph::with_clauses(&["c0 = c1 or c2 = c3"]);

    g.check_clause_str("c0 = c1 or c2 = c3");
}

#[test]
fn test_term_graph_shortening_long_clause() {
    let mut g =
        TestGraph::with_clauses(&["not g5(c2, c3)", "not g6(c2, c3) or g5(c2, c3) or c3 = c2"]);

    g.check_clause_str("not g6(c2, c3) or c3 = c2");
}

#[test]
fn test_term_graph_checking_reducible_clause() {
    // This failed at some point because we were checking a clause that could be reduced.
    let mut g = TestGraph::with_clauses(&[
        // These are necessary to reproduce the bug
        "g9(c4, c5) = c3",
        "c4 != c0",
        "g9(c4, c5) != c3 or g9(c4, g6(c5, c0)) = g6(c3, c0) or c4 = c0",
        // The clauses from the basic case
        "not g5(g6(c5, c0), c1)",
        "g9(c4, g6(c5, c0)) != g6(c3, c0) or not g5(g6(c3, c0), c1) or g5(g6(c5, c0), c1) or c4 = c1",
    ]);
    g.check_clause_str("g9(c4, g6(c5, c0)) != g6(c3, c0) or not g5(g6(c3, c0), c1) or c4 = c1");
}

#[test]
fn test_term_graph_reducing_clauses() {
    let g = TestGraph::with_clauses(&[
        "not g3(c1) or g3(c0)",
        "not g3(c0) or g3(c2)",
        "g3(c1)",
        "not g3(c2)",
    ]);
    assert!(g.has_contradiction());
}

#[test]
fn test_term_graph_eight_case_reduction() {
    let g = TestGraph::with_clauses(&[
        "c0 or c1 or c2",
        "c0 or c1 or not c2",
        "c0 or not c1 or c2",
        "not c0 or c1 or c2",
        "not c0 or not c1 or c2",
        "not c0 or c1 or not c2",
        "c0 or not c1 or not c2",
        "not c0 or not c1 or not c2",
    ]);
    assert!(g.has_contradiction());
}

#[test]
fn test_normalize() {
    let mut g = TestGraph::new();

    // Create some terms
    let t1 = g.insert_term_str("c1");
    let t2 = g.insert_term_str("c2");
    let t3 = g.insert_term_str("c3");
    let t4 = g.insert_term_str("c4");

    let g1 = g.get_group_id(t1);
    let g2 = g.get_group_id(t2);
    let g3 = g.get_group_id(t3);
    let g4 = g.get_group_id(t4);

    // Test 1: Normal clause that stays normal
    let lit1 = LiteralId::new(g1, g2, true);
    let lit2 = LiteralId::new(g3, g4, false);
    let clause_norm = ClauseId::new(vec![lit1, lit2]);
    let clause = match clause_norm {
        Normalization::Clause(c) => c,
        _ => panic!("Expected a clause"),
    };

    match g.graph.normalize(clause.clone()) {
        Normalization::Clause(normalized) => {
            assert_eq!(normalized.literals().len(), 2);
        }
        _ => panic!("Expected a normal clause"),
    }

    // Test 2: Clause that becomes simpler after merging
    g.set_eq(t1, t2, StepId(0));

    // After merging t1 and t2, the literal "g1 = g2" becomes reflexive and should be filtered
    match g.graph.normalize(clause) {
        Normalization::True => {}
        _ => panic!("Expected a tautology after merging"),
    }

    // Test 3: Create a clause that will have duplicate literals after merging
    let t5 = g.insert_term_str("c5");
    let t6 = g.insert_term_str("c6");
    let t7 = g.insert_term_str("c7");

    let g5 = g.get_group_id(t5);
    let g6 = g.get_group_id(t6);
    let g7 = g.get_group_id(t7);

    let lit3 = LiteralId::new(g5, g6, true);
    let lit4 = LiteralId::new(g5, g7, true);
    let clause2_norm = ClauseId::new(vec![lit3, lit4]);
    let clause2 = match clause2_norm {
        Normalization::Clause(c) => c,
        _ => panic!("Expected a clause"),
    };

    // Merge g6 and g7
    g.set_eq(t6, t7, StepId(1));

    // After merging, both literals become "g5 = g6" (or g7), so they should deduplicate
    match g.graph.normalize(clause2) {
        Normalization::Clause(normalized) => {
            assert_eq!(
                normalized.literals().len(),
                1,
                "Should deduplicate to one literal"
            );
        }
        _ => panic!("Expected a normalized clause"),
    }

    // Test 4: Tautology test (p or not p)
    let lit5 = LiteralId::new(g3, g4, true);
    let lit6 = LiteralId::new(g3, g4, false);
    let tautology = ClauseId::new(vec![lit5, lit6]);

    match tautology {
        Normalization::True => {}
        _ => panic!("Expected a tautology"),
    }
}

#[test]
fn test_update_group_id() {
    let mut g = TestGraph::new();

    // Create some terms that will have different groups
    let t1 = g.insert_term_str("c1");
    let t2 = g.insert_term_str("c2");
    let t3 = g.insert_term_str("c3");
    let t4 = g.insert_term_str("c4");

    let initial_g1 = g.get_group_id(t1);
    let initial_g2 = g.get_group_id(t2);
    let initial_g3 = g.get_group_id(t3);
    let initial_g4 = g.get_group_id(t4);

    // All groups should initially map to themselves
    assert_eq!(g.update_group_id(initial_g1), initial_g1);
    assert_eq!(g.update_group_id(initial_g2), initial_g2);
    assert_eq!(g.update_group_id(initial_g3), initial_g3);
    assert_eq!(g.update_group_id(initial_g4), initial_g4);

    // Now merge t1 and t2
    g.set_eq(t1, t2, StepId(0));

    // Find which group survived the merge
    let g1_after_first = g.update_group_id(initial_g1);
    let g2_after_first = g.update_group_id(initial_g2);
    assert_eq!(g1_after_first, g2_after_first);

    // Now merge t2 and t3
    g.set_eq(t2, t3, StepId(1));

    // Find which group survived this merge
    let g1_after_second = g.update_group_id(initial_g1);
    let g2_after_second = g.update_group_id(initial_g2);
    let g3_after_second = g.update_group_id(initial_g3);
    assert_eq!(g1_after_second, g2_after_second);
    assert_eq!(g2_after_second, g3_after_second);

    // Now merge t3 and t4
    g.set_eq(t3, t4, StepId(2));

    // Everyone should now map to the same group
    let final_g1 = g.update_group_id(initial_g1);
    let final_g2 = g.update_group_id(initial_g2);
    let final_g3 = g.update_group_id(initial_g3);
    let final_g4 = g.update_group_id(initial_g4);
    assert_eq!(final_g1, final_g2);
    assert_eq!(final_g2, final_g3);
    assert_eq!(final_g3, final_g4);
    let final_group = final_g1;

    // After calling update_group_id on initial_g1, it should have been optimized
    // to point directly to the final group
    assert_eq!(g.update_group_id(initial_g1), final_group);

    // If initial_g1 was remapped, check that the optimization worked
    if initial_g1 != final_group {
        match &g.graph.groups[initial_g1.get() as usize] {
            PossibleGroupInfo::Remapped(target) => assert_eq!(*target, final_group),
            PossibleGroupInfo::Info(_) => panic!("initial_g1 should be remapped"),
        }
    }

    // Test a chain of remappings specifically
    // Create a longer chain to ensure optimization works
    let t5 = g.insert_term_str("c5");
    let t6 = g.insert_term_str("c6");
    let t7 = g.insert_term_str("c7");

    let g5 = g.get_group_id(t5);
    let _g6 = g.get_group_id(t6);
    let _g7 = g.get_group_id(t7);

    // Create chain: t5 -> t6 -> t7
    g.set_eq(t5, t6, StepId(3));
    g.set_eq(t6, t7, StepId(4));

    // g5 should now map to the final group (either g6 or g7 survived)
    let final_567 = g.update_group_id(g5);

    // Check that g5 now points directly to the final group (optimization happened)
    if g5 != final_567 {
        match &g.graph.groups[g5.get() as usize] {
            PossibleGroupInfo::Remapped(target) => assert_eq!(*target, final_567),
            PossibleGroupInfo::Info(_) => panic!("g5 should be remapped"),
        }
    }
}

#[test]
fn test_term_graph_missed_resolution() {
    let mut g = TestGraph::with_clauses(&[
        "g9(c0, c1) = c1",
        "not g8(g9(c0, c1), c0)",
        "g6(c1, c0) or g6(c0, c1)",
        "g8(g9(c0, c1), c0) = g6(c0, g9(c0, c1))",
        "not g6(c0, c1)",
    ]);
    g.check_clause_str("g6(c1, c0)");
}

// Test partial application congruence: if f(a) = g(c), then f(a, b) = g(c, b).
// This works in EqualityGraph because f(a, b) is represented as ((f a) b),
// and g(c, b) is represented as ((g c) b). When we set (f a) = (g c),
// congruence closure propagates this to make ((f a) b) = ((g c) b).
#[test]
fn test_partial_application_congruence() {
    let mut g = TestGraph::new();

    // Create n1 = f(a, b) and n2 = g(c, b)
    let n1 = g.insert_term_str("c1(c2, c3)");
    let n2 = g.insert_term_str("c4(c5, c3)");

    // Initially they are not equal
    g.assert_ne(n1, n2);

    // Create the partial applications f(a) and g(c)
    let fa = g.insert_term_str("c1(c2)");
    let gc = g.insert_term_str("c4(c5)");

    // Set f(a) = g(c)
    g.set_eq(fa, gc, StepId(0));

    // Now f(a, b) should equal g(c, b) due to congruence on partial applications
    // In lambda calculus style: ((f a) b) = ((g c) b) because (f a) = (g c)
    g.assert_eq(n1, n2);

    // The step ids should show the connection
    let steps = g.get_step_ids(n1, n2);
    assert_eq!(steps, vec![0]);
}

// Test that partial application congruence works transitively
#[test]
fn test_partial_application_congruence_transitive() {
    let mut g = TestGraph::new();

    // Create three terms: f(a, b), g(c, b), h(d, b)
    let n1 = g.insert_term_str("c1(c2, c3)");
    let n2 = g.insert_term_str("c4(c5, c3)");
    let n3 = g.insert_term_str("c6(c7, c3)");

    // Create partial applications
    let fa = g.insert_term_str("c1(c2)");
    let gc = g.insert_term_str("c4(c5)");
    let hd = g.insert_term_str("c6(c7)");

    // Set f(a) = g(c) and g(c) = h(d)
    g.set_eq(fa, gc, StepId(0));
    g.set_eq(gc, hd, StepId(1));

    // Now all three full applications should be equal
    g.assert_eq(n1, n2);
    g.assert_eq(n2, n3);
    g.assert_eq(n1, n3);
}

// Test partial application with different final arguments (should NOT be equal)
#[test]
fn test_partial_application_different_args() {
    let mut g = TestGraph::new();

    // Create n1 = f(a, b) and n2 = g(c, d) where b != d
    let n1 = g.insert_term_str("c1(c2, c3)");
    let n2 = g.insert_term_str("c4(c5, c6)");

    // Create partial applications
    let fa = g.insert_term_str("c1(c2)");
    let gc = g.insert_term_str("c4(c5)");

    // Set f(a) = g(c)
    g.set_eq(fa, gc, StepId(0));

    // n1 and n2 should still NOT be equal because b != d
    g.assert_ne(n1, n2);

    // But if we also set b = d, then they should become equal
    let b = g.get_str("c3");
    let d = g.get_str("c6");
    g.set_eq(b, d, StepId(1));

    g.assert_eq(n1, n2);
}

// Test that Pi types (function types) can be inserted into the graph
#[test]
fn test_insert_pi_type() {
    let mut graph = EqualityGraph::new();
    let kctx = KernelContext::new();

    let bool_type = Term::bool_type();
    let type_sort = Term::type_sort();

    // Create Pi types: Bool -> Bool
    let pi1 = Term::pi(bool_type.clone(), bool_type.clone());
    let pi2 = Term::pi(bool_type.clone(), bool_type.clone());
    // Create a different Pi type: Type -> Bool
    let pi3 = Term::pi(type_sort.clone(), bool_type.clone());

    let id1 = graph.insert_term(&pi1, &kctx);
    let id2 = graph.insert_term(&pi2, &kctx);
    let id3 = graph.insert_term(&pi3, &kctx);

    // Same Pi types should get same TermId
    assert_eq!(id1, id2, "Same Pi types should get same TermId");
    // Different Pi types should get different TermIds
    assert_ne!(id1, id3, "Different Pi types should get different TermIds");

    // Also verify get_term_id works
    assert_eq!(graph.get_term_id(&pi1), Some(id1));
    assert_eq!(graph.get_term_id(&pi2), Some(id2));
    assert_eq!(graph.get_term_id(&pi3), Some(id3));
}

// Test that merging two groups that are marked as unequal:
// 1. Correctly detects a contradiction
// 2. Does not mark a group as unequal to itself
#[test]
fn test_merge_unequal_groups_no_self_inequality() {
    let mut g = TestGraph::new();

    // Create two terms
    let a = g.insert_term_str("c1");
    let b = g.insert_term_str("c2");

    // Mark them as not equal
    g.set_terms_not_equal(a, b, StepId(0));
    assert!(!g.has_contradiction());

    // Get the group IDs before merging
    let group_a = g.get_group_id(a);
    let group_b = g.get_group_id(b);

    // Verify they have each other in their inequalities
    {
        let info_a = g.graph.get_group_info(group_a);
        let info_b = g.graph.get_group_info(group_b);
        assert!(info_a.inequalities.contains_key(&group_b));
        assert!(info_b.inequalities.contains_key(&group_a));
    }

    // Now set them equal - this should detect a contradiction
    g.set_eq(a, b, StepId(1));
    assert!(g.has_contradiction());

    // Find the surviving group (both terms now point to the same group)
    let surviving_group = g.get_group_id(a);
    assert_eq!(g.get_group_id(b), surviving_group);

    // Critical check: the surviving group should NOT have itself in its inequalities
    let surviving_info = g.graph.get_group_info(surviving_group);
    assert!(
        !surviving_info.inequalities.contains_key(&surviving_group),
        "Group should never be marked as unequal to itself"
    );
}

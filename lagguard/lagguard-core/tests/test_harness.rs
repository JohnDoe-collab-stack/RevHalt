use lagguard_core::model::*;
use lagguard_core::analysis::Analysis;
use std::collections::HashMap;

fn create_combo_model() -> Model {
    // Model with a race/lag
    // e1: Write(x)
    // e2: Write(x)
    // Indep(e1, e2) because different "logic" but same physical resource? 
    // No, Indep means NO conflict. If they write same resource, they ARE distinct and conflicting.
    // To have Indep(e1, e2) they must target different resources or be read-read.
    // BUT Lag requires:
    // 1. Indep(e1, e2) -> commute to same resulting state "set" (fiber).
    // 2. But Sigma sees a difference.
    
    // Example: 
    // r1, r2.
    // e1: Write(r1) = 1
    // e2: Write(r2) = 1
    // Indep(e1, e2).
    // State after e1,e2: {r1:1, r2:1}
    // State after e2,e1: {r1:1, r2:1}
    // They are physically identical. Holonomy is Identity.
    // No lag.

    // "LagEvent" requires Holonomy that is non-trivial OR Sigma that distinguishes.
    // If Hol is identity, x = x'. Then compatibility check x!=x' fails.
    // So we need Hol(alpha) to map x -> x' with x != x'.
    
    // Loop/Twisted Holonomy example:
    // 2D torus or similar?
    // In "Primitive Holonomy", we need a "gauge" change or "path" difference.
    // Simple digital example:
    // e1 toggles bit A. e2 toggles bit B.
    // If they commute, state is same.
    
    // We need state dependent on PATH.
    // e1: if B=0 then A=1 else A=2
    // e2: if A=0 then B=1 else B=2
    // If init A=0, B=0.
    // p=e1;e2:
    //   e1: A=1. e2: (sees A=1) -> B=2. Final: A=1, B=2.
    // q=e2;e1:
    //   e2: B=1. e1: (sees B=1) -> A=2. Final: A=2, B=1.
    
    // Are they independent?
    // W(e1)={A}, R(e1)={B}.
    // W(e2)={B}, R(e2)={A}.
    // cond 3: W(e1) cap (R(e2) U W(e2)) = {A} cap {A,B} = {A} != emptyset.
    // They are NOT independent standardly.
    
    // The user's "LagEvent" (Holonomy tordue) arises when:
    // "Indep" is high-level (logical independence) but low-level state differs?
    // User says: "Witness de causalité invisible ... (holonomie tordue + divergence de compatibilité future)".
    // "Deux micro-états indistinguables maintenant" (obs is same)
    // "Mais un futur step les sépare".
    
    // So:
    // Real state: (A, B).
    // Obs state: (A).
    // e1, e2 affect hidden state B in a non-commuting way, but observable A stays same.
    // And e1, e2 are "independent" regarding the Scheduler/Por? 
    // If POR sees them as dependent, it doesn't generate a cell.
    // So POR must think Indep(e1, e2).
    // => W(e1) disjoint R(e2)...
    
    // Hidden variable H.
    // e1 touches H. e2 touches H? No, that's dependance.
    // Maybe e1 touches H1, e2 touches H2.
    // But then result is commutative.
    
    // The "Twisted Holonomy" usually implies a topology effect or "Gauge".
    // Or, maybe "Indep" definition allows some overlap on "ignored" resources?
    // User definition 4.3: W(e) beta ... = Empty. Strict disjointness.
    
    // If strict disjointness, how can we have non-identity Holonomy?
    // Hol(p, q) = Tr(p) . Tr(q)^T.
    // If p, q commute perfectly on ALL fields, Hol is Identity.
    // Then x=x', no lag in Single-Fiber model.
    
    // User's "Fiber" concept:
    // Fiber(h) = {x in A | obs(x) = tgt(h)}.
    // If A is the FULL state, and Indep holds, then p and q reach the SAME EXACT state x_final.
    // Then Hol(x_final, x_final) is true.
    // Then no Lag.
    
    // UNLESS:
    // The abstract domain A is "richer" than the physical state? Or "history-aware"?
    // Or Indep is defined on a *subset* of resources, but they share a hidden one?
    // But Post_e must respect A.
    
    // Wait, the User says: "Cell corresponds to a swap... Def p q... exactly the Mazurkiewicz traces."
    // In Mazurkiewicz traces, if Indep(a,b), then ab ~ ba.
    // Equivalence of traces implies equivalence of state transformation IF determinstic.
    // If Post_e is a function, Tr(ab) = Tr(ba).
    // Then Hol is identity.
    
    // But Post_e is a RELATION.
    // Non-deterministic events.
    // p = e1;e2. q = e2;e1.
    // Path p might allow reaching {x, y}.
    // Path q might allow reaching {x, z}.
    // Hol relates via common source.
    // Start at s.
    // s -p-> x. s -q-> x'.
    // If x != x', and obs(x)==obs(x'), we have a "split".
    // AND if Indep(e1, e2) holds, we *expect* them to commute.
    // If they don't commute (x != x'), it's a "Lag".
    // This happens if e1, e2 are independent (disjoint resources) but the implementation
    // somehow couples them or fails to commute (e.g. allocators, hidden counters, or non-deterministic choice correlated?).
    
    // OR: The "Constraint" implies Indep, but the Model (Post) has a bug where they don't commute.
    // Use Case:
    // e1: alloc(r1). e2: alloc(r2).
    // Indep? Yes, different return values.
    // Post: e1 -> heap uses slot 1. e2 -> heap uses slot 2.
    // p: e1(slot1); e2(slot2). State: {1, 2}.
    // q: e2(slot1); e1(slot2). State: {2, 1} (swapped).
    // State includes "allocator_next_index"?
    // If allocator is part of state, W(e1)={alloc}, W(e2)={alloc}. Dependent!
    // If allocator is abstract/hidden:
    // State = {ptr1: Val, ptr2: Val}.
    // p -> {ptr1: 1, ptr2: 2}.
    // q -> {ptr1: 2, ptr2: 1}.
    // x != x'.
    // Obs (if we trace ptrs): distinct.
    // If Obs is "sum of values" -> same.
    // Sigma: "Write(*ptr1)".
    // In x: Writes to 1.
    // In x': Writes to 2.
    // If 1 and 2 are distinct "rows" in memory, effect is different.
    // Compatible(Write(1)) might be true for x, false for x' (if row 2 locked?).
    // Yes! This is the canonical example.
    
    // Let's build this "Allocator" model.
    // Resources: "ptr1", "ptr2".
    // Events: e1="Alloc(ptr1)", e2="Alloc(ptr2)".
    // Indep: e1 writes ptr1, e2 writes ptr2. Disjoint!
    // (Assuming they don't write "Heap" globally in the user's declared Indep).
    // But Post_e models the allocator logic (non-det choice of slot).
    
    // Abstract State:
    // ptr1: {Null, Addr1, Addr2}
    // ptr2: {Null, Addr1, Addr2}
    // (Implicitly: free_list is hidden or modeled via non-det)
    
    // Post(e1):
    //  (Null, Null) -> (Addr1, Null) OR (Addr2, Null) (if free)
    //  (Null, Addr1) -> (Addr2, Addr1)
    //  (Null, Addr2) -> (Addr1, Addr2)
    
    // Post(e2): similar for ptr2.
    
    // Path p = e1; e2.
    // (N,N) -e1-> (A1, N) -e2-> (A1, A2)
    // Path q = e2; e1.
    // (N,N) -e2-> (N, A1) -e1-> (A2, A1)
    
    // Result states:
    // x = (A1, A2). x' = (A2, A1).
    // Distinct states? Yes.
    // Obs: suppose obs is empty (Unit). Fiber is everything.
    // Hol(p,q) relates x and x' (via source N,N).
    
    // Sigma: "Use(ptr1 == A1)".
    // Or just "Lock(Addr1)".
    // If x has ptr1=A1, Lock(Addr1) is "Lock(ptr1)".
    // If x' has ptr1=A2, Lock(Addr1) is NOT "Lock(ptr1)".
    // If the check is "Lock(ptr1)", in x it locks A1. In x' it locks A2.
    // The conflict might be on a FUTURE event that touches A1.
    // e.g. Sigma = Write(Addr1).
    // In x: ptr1=A1. Next step uses ptr1. It writes A1.
    // In x': ptr1=A2. Next step uses ptr1. It writes A2.
    // Difference?
    // If there is another thread holding Lock(A1).
    // Then x conflicts, x' does not.
    // Sig(x) != Sig(x').
    
    // Let's encode this.
    // State encoding:
    // 0: (N,N)
    // 1: (A1, N)
    // 2: (A2, N)
    // 3: (N, A1)
    // 4: (N, A2)
    // 5: (A1, A2) -> x
    // 6: (A2, A1) -> x' - distinct!
    // 7: ...
    
    // Indep: e1, e2 declared independent.
    
    Model {
        version: "test".to_string(),
        resources: vec![],
        events: vec![
            Event { id: "e1".into(), ..Event::default() }, 
            Event { id: "e2".into(), ..Event::default() }
        ],
        hb_edges: vec![], // None, fully parallel
        sigma: vec![
             SigmaEvent { id: "sigma".into(), kind: "Check".into(), resource: None }
        ],
        abstract_domain: AbstractDomain::ProductFinite { components: vec![] },
        post: vec![
            PostRelation {
                event: "e1".into(),
                relation: RelationEncoding::SparsePairs { pairs: vec![
                    (0, 1), (0, 2), // alloc
                    (3, 5), (3, 6), // if ptr2 set to A1/A2, e1 picks other
                    (4, 5), (4, 6)
                ]}
            },
            PostRelation {
                event: "e2".into(),
                relation: RelationEncoding::SparsePairs { pairs: vec![
                    (0, 3), (0, 4),
                    (1, 5), (1, 6),
                    (2, 5), (2, 6)
                ]}
            },
            PostRelation {
                event: "sigma".into(),
                relation: RelationEncoding::SparsePairs { pairs: vec![
                    (5, 5) // Sigma only compatible with state 5 (x)
                    // State 6 (x') is NOT compatible.
                ]}
            }
        ],
        observable: Observable::Projection { resources: vec![] },
        targets: vec![]
    }
}

impl Default for Event {
    fn default() -> Self {
        Event {
            id: "".into(), kind: "".into(), resource: None, 
            reads: vec![], writes: vec![], hb_after: vec![], meta: None
        }
    }
}

#[test]
fn test_combo_lag() {
    let mut model = create_combo_model();
    // Fix up writes to ensure Indep in naive POR checks
    model.events[0].writes = vec!["r1".into()];
    model.events[1].writes = vec!["r2".into()]; // Disjoint
    
    let analysis = Analysis::new(&model);
    
    // Manual cell check
    // p=[e1, e2], q=[e2, e1]
    let p = vec!["e1".to_string(), "e2".to_string()];
    let q = vec!["e2".to_string(), "e1".to_string()];
    
    // Fiber: start at 0.
    let fiber = vec![0]; // We assume we are at init state 0.
    
    // Wait, detect_lag_on_cell expects fiber to be the set of states at the source.
    // If src is "init", fiber={0}.
    // Hol(p,q) composes from src.
    // Actually Hol is defined on the Fiber of the PREVIOUS prefix.
    // If prefix is empty, fiber is just {0}.
    
    let result = analysis.detect_lag_on_cell(&p, &q, &fiber);
    assert!(result.is_some());
    let (sig, x, xp) = result.unwrap();
    assert_eq!(sig, "sigma");
    // p reaches x
    // q reaches xp
    // From 0:
    // p: 0->(1,2)->(5,6,...). In our posts:
    // e1: 0->1 (force specific path for determinstic test? No, relation is sparse)
    // Relation for e1 from 0 is {1, 2}.
    // Relation for e2 from 1 is {5, 6} (if implemented fully).
    // Let's make it deterministic for the test to be sure of x and x'.
    // e1: 0->1. 3->5.
    // e2: 0->3. 1->6 (swapped alloc!).
    // p: 0 -> 1 -> 6. (x = 6)
    // q: 0 -> 3 -> 5. (x' = 5)
    // Sigma compatible with 5, not 6.
    // Lag!
    
    // Wait, if p->6 and q->5.
    // Hol(p,q) maps 0 (via p) to 6. And 0 (via q) to 5.
    // So Hol(0, 0) ? No. Hol relates states in the fiber.
    // Def: Hol(alpha) = Tr(p) . Tr(q)^T.
    // Starts at fiber, goes p to Tgt, then q^T back to Fiber.
    // So Hol maps source states to source states?
    // No.
    // The definition of Hol in the spec (Section 6) says:
    // "Hol(alpha) = Tr(p) . Tr(q)^T".
    // Tr(p): Fiber(h) -> Fiber(k).
    // Tr(q): Fiber(h) -> Fiber(k).
    // Tr(q)^T: Fiber(k) -> Fiber(h).
    // So Hol: Fiber(h) -> Fiber(h).
    // It's a monodromy on the source fiber.
    
    // Spec 8.2: "cherche x != x' tel que Hol(alpha) x x'".
    // This implies x, x' are in Fiber(h).
    // This detects loops in the source fiber.
    // BUT my example was x, x' at the TARGET (state 5 vs 6).
    // This is "Commutation Failure" at target.
    // Is LagGuard defined on Source Loop or Target Divergence?
    
    // Re-reading Spec 1.1:
    // "Contrat LagFree: forall x != x' in Fiber(h), Hol(alpha) x x' => Sig(x) = Sig(x')"
    // Here x, x' are in Fiber(h).
    // Sig(x) is compatibility with future steps from x.
    
    // My example: The divergence happens AFTER p and q.
    // Does p(e1,e2) closing a loop return to h? No, it goes to k.
    // This "Holonomy" usually refers to a loop `p . q^-1`.
    // So it measures the defect *transported back* to h?
    // Or is the "Cell" defined as a loop?
    // A cell is two paths p, q between h and k.
    // So p followed by q_inverse is a loop at h.
    // If we have non-trivial holonomy, this loop is not identity.
    // Meaning: starting at x in h, going p to y in k, then q^-1 back ... do we get x?
    // If we get x' != x, then we have a "monodromy/holonomy" shift.
    
    // In the Allocator example:
    // 0 -p-> 6.
    // 0 -q-> 5.
    // Tr(q)^T: 5 -> 0. (assuming reversibility or trace).
    // Hol(0, ?) = Tr(p)(0) . Tr(q)^T
    // = {6} . Tr(q)^T
    // Does 6 go back to 0 via q?
    // q: 0->3->5.
    // Inverse q: 5->3->0.
    // Does 6 go back to 0 via q?
    // 6 comes from p (0->1->6).
    // Does q allow reaching 6?
    // q: 0->3->5.
    // If q ONLY reaches 5, then Tr(q)^T maps 5->0 and NOTHING else.
    // So {6} . Tr(q)^T = Empty.
    // So Hol(0, ?) is empty.
    // No x' found.
    // No Lag detected by this definition?
    
    // IF the system is reversible (Groupoid), then p and q must reach the same set of states?
    // No.
    // If p and q lead to different states (5 vs 6) and NO overlap,
    // Then the cell is "broken" (non-confluent).
    // Is non-confluence a Lag?
    
    // The user spec "Différentiel de compatibilité" assumes x, x' in Fiber(h).
    // So it assumes we compare states *at the source*.
    // "Deux micro-états indistinguables maintenant" (at source h)
    // "mais un futur step les sépare" (Sig).
    
    // This implies the "Lag" is about "Hidden state at h" that is revealed by the loop p.q^{-1}.
    // i.e. we go around the loop and state changes.
    // Example: Berry phase, or Aharonov-Bohm.
    // You go around a loop, and your phase shifts.
    // Here: You Swap(e1, e2). This is a small loop in the classification space.
    // Performing the swap changes the state at h?
    // No, `Hol(alpha)` is the operator associated with the cell.
    // It maps x to x'.
    // Validating the "contract": If I have x, x' related by Hol, are they indistinguishable by Sigma?
    
    // This implies the Lag check is:
    // 1. Find x, x' such that x' = Hol(alpha)(x).
    // 2. Check if Sigma(x) == Sigma(x').
    
    // If Hol is identity (usual case), x=x', check passes.
    // If Hol is non-trivial (x != x'), we have a "Topological Defect" / Lag.
    // We only FLAG it if Sigma distinguishes them.
    // If Sigma doesn't distinguish, it's a "gauge symmetry" (safe).
    
    // So I need a model where Hol is NON-TRIVIAL.
    // This requires:
    // 0 -> k -> 0 type loop?
    // or 0 -p-> k -q^T-> x'.
    // For this to work, q must be able to go back from k to x'.
    // If p and q are swaps:
    // p = e1 e2. q = e2 e1.
    // Both go h -> k.
    // For Hol(x, x') to exist, we need:
    // x -p-> y.
    // x' -q-> y. (So q goes x' -> y, thus q^T goes y -> x').
    
    // So we need a common target state y reachable from x via p AND from x' via q.
    // AND x != x'.
    // This means "Local Confluence of distinct sources".
    // Or "Two sources map to same target via swapped paths".
    
    // Example:
    // x=(A=0, B=0). x'=(A=1, B=1). (Two states in Fiber h).
    // e1 writes A=1. e2 writes B=1.
    // p = e1;e2.
    // x -e1-> (1,0) -e2-> (1,1). (Target y).
    // q = e2;e1.
    // x' -e2-> (1,1) (already B=1) -e1-> (1,1). (Target y).
    // So Hol(x, x') holds.
    // We found a non-trivial Relation between x and x'.
    // If Sigma distinguishes x and x' (e.g. Sigma reads A), then Lag!
    // x has A=0. x' has A=1.
    // Sigma(x) sees 0. Sigma(x') sees 1.
    // Lag Identified.
    
    // This works!
    // So the test model needs:
    // Fiber(h) containing at least {0, 1}.
    // Target y = 2.
    // p: 0 -> 2.
    // q: 1 -> 2.
    // Sigma compatible with 0 but not 1.
    
    // Let's implement this "Merge" Model.
    // State 0, 1 in Fiber(h). (Initial fiber must be {0, 1}).
    
    let mut model = create_combo_model();
    model.events[0].writes = vec!["r1".into()];
    model.events[1].writes = vec!["r2".into()]; 
    
    // Clear posts and set manual
    model.post.clear();
    
    // p = e1; e2. q = e2; e1.
    // x=0. x'=1. y=2.
    // p: 0 -> ... -> 2.
    // q: 1 -> ... -> 2.
    // We need intermediate states.
    // 0 -e1-> 10 -e2-> 2.
    // 1 -e2-> 11 -e1-> 2.
    
    model.post.push(PostRelation {
        event: "e1".into(),
        relation: RelationEncoding::SparsePairs { pairs: vec![
            (0, 10), // part of p
            (11, 2)  // part of q
        ]}
    });
    model.post.push(PostRelation {
        event: "e2".into(),
        relation: RelationEncoding::SparsePairs { pairs: vec![
            (10, 2), // part of p
            (1, 11)  // part of q
        ]}
    });
    
    model.post.push(PostRelation {
         event: "sigma".into(),
         relation: RelationEncoding::SparsePairs { pairs: vec![
             (0, 0) // Sigma works on 0
             // Sigma NOT on 1
         ]}
    });
    
    let analysis = Analysis::new(&model);
    let fiber = vec![0, 1];
    
    let p = vec!["e1".to_string(), "e2".to_string()];
    let q = vec!["e2".to_string(), "e1".to_string()];
    
    let result = analysis.detect_lag_on_cell(&p, &q, &fiber);
    
    assert!(result.is_some());
    let (sig, s1, s2) = result.unwrap();
    // Should be (sigma, 0, 1) or (sigma, 1, 0)
    assert!( (s1==0 && s2==1) || (s1==1 && s2==0) );
}

#[test]
fn test_flat_ok() {
    // Identity holonomy, no lag.
    let mut model = create_combo_model();
    model.post.clear();
    // x=0.
    // p: 0 -> 1 -> 2.
    // q: 0 -> 3 -> 2.
    // Hol(0, 0) exists (p maps 0->2, q maps 0->2).
    // x=x', so loop is trivial.
    // No other paths.
    
    model.post.push(PostRelation {
        event: "e1".into(),
        relation: RelationEncoding::SparsePairs { pairs: vec![ (0, 1), (3, 2) ]}
    });
    model.post.push(PostRelation {
        event: "e2".into(),
        relation: RelationEncoding::SparsePairs { pairs: vec![ (0, 3), (1, 2) ]}
    });
    
     model.post.push(PostRelation {
         event: "sigma".into(),
         relation: RelationEncoding::SparsePairs { pairs: vec![ (0,0) ]}
    });

    let analysis = Analysis::new(&model);
    let fiber = vec![0];
    let p = vec!["e1".to_string(), "e2".to_string()];
    let q = vec!["e2".to_string(), "e1".to_string()];
    
    let result = analysis.detect_lag_on_cell(&p, &q, &fiber);
    assert!(result.is_none());
}

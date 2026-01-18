# Detailed explanation of the TSP work in RevHalt

This note explains what was built in the TSP pipeline and how the pieces fit
across the RevHalt theory, proof-carrying, and complexity bounds layers.
It is a technical walkthrough of the current formalization rather than a new
algorithm for TSP.

## 1) Core construction in TSP.lean

The file builds a concrete TSP instance inside the RevHalt framework.
The construction is fully computable (no noncomputable axioms for encoding).

1. Computable encodings
- Lists, tours, graphs, and instances are encoded into natural numbers.
- The pair/unpair encoding is used to make all data reducible to a code.
- Roundtrip lemmas show decode(encode x) = x for lists, tours, and instances.

2. Graphs and tours
- A weighted complete graph is a symmetric weight function with zero self edges.
- A tour is a list of vertices with length and range constraints and no duplicates.
- tourCost computes the cycle length with a return edge.

3. Machine semantics
- TSPTrace enumerates all tours by code and checks ValidTour.
- The key equivalence is proved:
  the machine halts iff the TSP instance has a valid tour.

4. Frontier and trajectory hooks
- S1Rel_TSP captures true-but-unprovable halting statements for TSP codes.
- The trajectory integration connects TSP codes to the general chain/omega limit.

5. Route II and the trilemma
- Route II gives conditions for S1Rel to be nonempty.
- The trilemma shows you cannot keep Absorbable, OmegaAdmissible, and RouteIIAt
  simultaneously; one must fail.

6. Canonization and Collapse
- If RouteIIAt fails, positive completeness at omega follows.
- If negative completeness is also assumed, you get full canonization.
- Collapse is derived from effective canonization data, not assumed as an axiom.

## 2) Witness-carrying extraction (proof-carrying layer)

The earlier abstract ExtractTour requirement is replaced by a concrete
witness-carrying extraction argument.

- ChecksWitness_TSP interprets a witness list as a tour for a decoded instance.
- checkTour_sound proves that a true check yields a concrete Tour structure.
- ExtractTour_of_ProvableWC shows that a proof-carrying derivation implies a
  real tour, which supplies the extraction step needed for Collapse-search.

This makes extraction a theorem, not a separate axiom, once the
proof-carrying framework is available.

## 3) Complexity bounds (price of P)

The complexity section ties search to a polynomial bound on proof sizes.

- TSPSize is a bitlength measure (log2 of the code).
- Collapse_TSP_Poly postulates a polynomial bound on witness-carrying proofs
  for solvable instances.
- Find_poly searches for a bounded derivation and extracts its witness.

Three results are proved:
- Find_poly_correct: found witnesses satisfy checkTour.
- Find_poly_complete: if a solution exists, the search succeeds within the
  polynomial bound.
- Find_poly_sound: if a witness is found, a solution exists.

From there:
- Collapse_TSP_Axiom_of_Poly derives the abstract Collapse axiom from the
  polynomial bound structure.
- Collapse_of_Trajectory_Poly states: if the trajectory limit yields PolyPosWC,
  then Collapse follows.

## 4) What is actually derived vs assumed

Derived (given the setup):
- Halts <-> HasSolution for the machine and trace.
- S1Rel_TSP anti-monotonicity.
- Collapse from effective canonization data.
- Collapse from polynomial proof bounds (Price of P).

Assumed or required inputs:
- Trajectory hypotheses (Absorbable, OmegaAdmissible) to force not RouteIIAt.
- Negative completeness if full canonization is needed.
- Proof-carrying framework (ProvableWC) for extraction.
- Polynomial bound structure for the complexity version of Collapse.

## 5) How this differs from the usual P vs NP framing

- The result is conditional on trajectory choices and hypothesis packages.
- The emphasis is on provability dynamics and witness extraction, not only
  reductions and lower bounds.
- Search vs decision is explicit: an extraction theorem is required.
- Polynomial time is expressed through bounded proof objects, not by a direct
  machine runtime analysis.

## 6) Where to look in the code

- Core pipeline: RevHalt/Theory/Instances/TSP.lean
- Proof-carrying framework: RevHalt/Theory/TheoryDynamics_ProofCarrying.lean
- Complexity bounds: RevHalt/Theory/TheoryDynamics_ComplexityBounds.lean
- Witness helper file (if separated): RevHalt/Theory/Instances/TSP_Witness.lean

## 7) Minimal takeaway

The TSP development does not claim a new algorithm. It builds a formal bridge:
TSP -> halting semantics -> provability frontier -> trajectory constraints ->
canonization -> Collapse. With proof-carrying extraction and polynomial proof
bounds, Collapse can be derived as output, and TSP is placed in P within
this trajectory-dependent framework.

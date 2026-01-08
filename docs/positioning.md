# Related Work and Positioning

## Scope

RevHalt should be read as a **certificate architecture** for non-termination / temporal safety: it defines (i) a *certificate schema* (`Splitter` + `Queue` + local obligations), and (ii) a *verified compilation pipeline* that turns such finite certificates into global infinitary guarantees (Up2 coinductive avoidance; Up1 Π₁ stabilization, and its algebraic “null-signal” form `up(TimeTrace)=⊥`). The novelty claim is therefore **architectural** (interfaces + compilation), not the underlying mathematical primitives taken in isolation.

## Fixed points, coinduction, and safety games (Up2 layer)

The use of a coinductive “winning region” is closely aligned with classical views where **safety properties correspond to greatest fixed points** and can be explained via **safety games** (stay forever in a safe region / avoid a losing set). ([Logic RWTH Aachen][1])
RevHalt’s Up2 (`Avoid2Mem`) fits this pattern: it is a greatest-fixed-point-style kernel of positions from which the target can be avoided indefinitely. RevHalt’s contribution is to make this kernel an *explicit intermediate compilation target* for arithmetic/local certificates (Splitter/Queue), rather than starting from a transition system and computing the winning region directly.

## Abstract interpretation, closure operators, and lattice-theoretic structure (Up1 as operator form)

Abstract interpretation is traditionally formulated in a lattice-theoretic setting where abstractions can be represented via **Galois connections** or **(upper) closure operators** (monotone, extensive, idempotent). ([Di ENS][2])
RevHalt’s `up` operator is deliberately presented in this family: stabilization is equivalently expressed as a **kernel condition** (`up T = ⊥`) rather than only as a Π₁ formula (`∀n, ¬T n`). This is best understood as a *representation change* that enables uniform algebraic/categorical tooling (closure operator laws, thin-category adjunction viewpoint), rather than a new decidability result.

## Proof-carrying code and certificate checking (Splitter/Queue as “proof-carrying” artifacts)

RevHalt’s central design choice—“the hard part is producing a certificate; the easy part is checking and compiling it”—is in direct continuity with **proof-carrying code (PCC)**: a producer supplies code plus a checkable certificate, and the consumer validates it with a small trusted checker. ([ACM Digital Library][3])
Positioning-wise, `Splitter/Queue` are best viewed as a domain-specific certificate format for non-termination/safety, while `Hierarchy/Temporal` are the verified validators/compilers from certificates to global semantic guarantees.

## Non-termination proofs via recurrent sets (relation to Up2 invariants)

A standard approach to non-termination proofs is to exhibit a **recurrent set** (or related closed set) of states: once reached, execution cannot escape, and there is always a successor—thus yielding infinite behavior. ([www0.cs.ucl.ac.uk][4])
RevHalt’s Up2 kernel is conceptually close to these “closed region” witnesses. The distinctive point in RevHalt is the **three-level factoring**: a local, structured certificate (`Queue` assembled from a `Splitter`) compiles into a coinductive invariant (Up2), which then exports into a trace-level Π₁ statement (Up1). This makes the local→global step reusable across instantiations.

## Contrast with termination via ranking functions

Termination proofs are commonly obtained by synthesizing **ranking functions** into a well-founded order, enforcing a strictly decreasing measure along transitions. ([SeaHorn][5])
RevHalt intentionally targets the dual use-case: rather than decreasing measures (induction), it emphasizes **persistent certificates** (coinduction) and their verified transport/compilation to infinitary guarantees. This does not contradict classical undecidability results; it reframes the workflow as: (i) certificate synthesis is external (human/oracle/heuristics), (ii) certificate checking and infinitary reasoning are internal and generic.

## Summary of contribution

In one sentence: **RevHalt is not a new “logic of infinity”; it is a verified compilation architecture that maps finite, locally checkable certificates (Splitter/Queue + local safety) to global infinitary guarantees (Up2 avoidance; Up1 stabilization; and the algebraic kernel form `up(TimeTrace)=⊥`).**
This architectural separation cleanly isolates the system-specific difficulty (certificate construction) from the system-agnostic infinitary reasoning (transport + bridge + export), aligning with proof-carrying and abstract-interpretation traditions while providing a distinctive certificate schema and compilation pipeline.

[1]: https://logic.rwth-aachen.de/pub/graedel/dependenceBook.pdf?utm_source=chatgpt.com "Games for Inclusion Logic and Fixed-Point Logic"
[2]: https://www.di.ens.fr/~cousot/publications.www/CousotCousot-POPL-77-ACM-p238--252-1977.pdf?utm_source=chatgpt.com "Abstract interpretation: a unified lattice"
[3]: https://dl.acm.org/doi/10.1145/263699.263712?utm_source=chatgpt.com "Proof-carrying code | Proceedings of the 24th ..."
[4]: https://www0.cs.ucl.ac.uk/staff/b.cook/pdfs/reasoning_about_nendeterminism_in_programs.pdf?utm_source=chatgpt.com "Reasoning about Nondeterminism in Programs"
[5]: https://seahorn.github.io/papers/termination_tacas16.pdf?utm_source=chatgpt.com "Synthesizing Ranking Functions from Bits and Pieces?"

Improve the demonstration theory (proof layer) — a complete plan (Markdown, no LaTeX)

This is the upgrade path for the “demonstration theory” itself (your internal proof layer), so that T2/T3 rely on an explicit, auditable proof mechanism rather than an opaque Provable : PropT -> Prop.

The goal is to make the proof layer:

constructive and checkable,

compatible with your Trace/up/Rev dynamic style,

strong enough to derive the diagonal bridge (instead of assuming it),

cleanly separated from the external semantic layer Truth.



---

1) What the demonstration theory must represent

Your current internal layer typically contains:

PropT : type of internal formulas (arithmetical sentences, encoded)

Provable : PropT -> Prop : “provable in S2”

FalseT : internal contradiction

Not : PropT -> PropT : internal negation

minimal consistency: not Provable FalseT

absurd rule: Provable p -> Provable (Not p) -> Provable FalseT


This is sufficient for a minimal diagonal argument, but it is not yet a demonstration theory in the operational sense.

The improvement is to make “provable” mean:

there exists a finite proof object whose validity is checkable.



---

2) Make proofs explicit: Proof and Check

2.1 Proof objects

Add a type of proof objects:

Proof is a finite object (or a code of such an object).


Minimal interface:

concl : Proof -> PropT (what it claims to prove)

size : Proof -> Nat (a code size or index bound, for enumeration)


2.2 Proof checking

Add a checker:

Check : Proof -> Bool


Meaning:

Check pr = true means: “pr is a valid proof according to S2’s rules”.


This single function is the operational core of the demonstration theory.


---

3) Redefine Provable as existence of a checked proof

Define:

Provable p means: there exists a proof object pr such that:

Check pr = true

concl pr = p



This change has three consequences:

1. proofs are now tangible objects you can enumerate;


2. provability becomes a “finite witness” concept;


3. many future meta-lemmas become constructive by default.




---

4) Introduce a proof-search trace (dynamic provability)

Your framework is dynamic: it treats “existence” as “eventually found”.

Do the same for proofs.

Define a trace:

ProofTrace p : Trace

ProofTrace p n means: “within bound n, a valid proof of p exists”.


Concrete definition pattern:

ProofTrace p n holds if there exists pr with size pr <= n, concl pr = p, and Check pr = true.


Now:

Halts (ProofTrace p) is equivalent to Provable p.


This aligns your internal notion of provability with the same time-indexed logic as halting.


---

5) Minimal inference rules to keep (and how they look now)

You want the proof system to satisfy a small set of properties, stated as lemmas about Check or Provable.

5.1 Absurd rule

Keep:

if Provable p and Provable (Not p), then Provable FalseT.


5.2 Consistency

Keep:

not Provable FalseT.


5.3 Optional (recommended) closure properties

If you want a cleaner arithmetical theory interface later:

closure under modus ponens (if your PropT has implication)

closure under substitution (if you formalize arithmetic terms)

representability / encoding lemmas (if you derive diagonalization)


These are not needed to keep T3 local sound extension operators, but they are needed if you want to derive the diagonal bridge internally and cleanly.


---

6) Separate the external semantics: Truth

Your external layer remains:

Truth : PropT -> Prop


And your main semantic assumption is:

soundness: if Provable p then Truth p.


Important: this is a meta-level statement. It does not require the internal theory to “know” its own soundness.

This keeps your complementarity clean:

internal provability is syntactic,

external truth is semantic,

they are linked only by a one-way soundness bridge.



---

7) Replace the assumed diagonal bridge with a derived one

Right now, your T2 pipeline assumes a field like:

for all H : Code -> PropT, there exists e such that

Rev(Machine e) is equivalent to Provable (Not (H e)).



To improve the demonstration theory, you want this to become a theorem derived from two standard operational ingredients:

7.1 Provability is enumerable (r.e.)

Once Provable p is “exists checked proof”, it is enumerable:

you can systematically enumerate proof objects by size,

check them using Check,

and eventually find a proof if one exists.


7.2 A fixed-point / recursion principle for your code model

You need a fixed-point principle for the Code/Machine model:

for any computable transformation on programs, you can build a program that refers to its own code.


With these, you can build the diagonal program instead of postulating it:

given H, build a program that halts exactly when a proof of Not (H e) is found,

use the fixed point to tie the program’s index to itself,

use T1 to swap between halting and Rev.


Net effect:

the diagonal bridge becomes a theorem from explicit, auditable assumptions.



---

8) What this upgrade buys you immediately

8.1 Constructive T2

You can remove any classical case split on external Prop and instead split on internal totality, if totality is part of the internalization attempt:

use I.total e : Provable (H e) or Provable (Not (H e)).


This yields a fully constructive T2 proof style.

8.2 Cleaner “audit story”

You can tell exactly what the internal theory is:

what counts as a proof,

how proofs are checked,

how proofs are enumerated,

why diagonalization is justified.


8.3 Better alignment with your core theme

Everything becomes dynamic and witness-based:

existence is witnessed by a time index,

provability is witnessed by a proof object,

halting is witnessed by a time index,

T3 consumes local witnesses and produces local extensions.



---

9) Minimal module structure to implement this upgrade

Suggested files (names are illustrative):

1. ProofSystem.lean



PropT, Proof, Check, concl, size

Provable p := exists pr, Check pr = true and concl pr = p

absurd, consistent


2. ProofTrace.lean



ProofTrace p n := exists pr with size pr <= n and Check pr = true and concl pr = p

lemma: Halts (ProofTrace p) <-> Provable p


3. Diagonal.lean



proof-enumeration program for Not (H e)

fixed-point principle assumptions

theorem: diagonal bridge


4. Impossibility.lean



T2 proof rewritten to be constructive and to use the derived diagonal bridge


Your existing Trace/Kit/Canonicity/Complementarity stay unchanged.


---

10) One-sentence summary

Upgrade the demonstration theory by making proofs explicit and checkable, define provability as “exists a checked finite proof”, mirror provability as a trace, and then derive the diagonal bridge from proof enumeration plus a fixed-point principle, so the whole T2/T3 pipeline becomes auditable and constructive while keeping your Rev/Kit/Trace core intact.

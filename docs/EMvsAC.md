# TODO: EM vs AC Clarification

## Status: CONCEPTUAL CLAIM — Needs formal backing

The claim: "The 'choice' in PickOracle is EM-regime, not AC-regime."

Current status: **argued but not fully formalized**.

---

## What IS Proven

### 1. The dichotomy is binary and exclusive
```lean
theorem dichotomy (x : X) : x ∈ D.Ker ∨ D.Sig x
theorem dichotomy_exclusive (x : X) : ¬ (x ∈ D.Ker ∧ D.Sig x)
```
Each element is in exactly one side. No ambiguity.

### 2. The content is forced once the side is known
- If `Sig x`: the pick is `encode_halt e` with `Rev0_K` certificate
- If `¬Sig x`: the pick is `encode_not_halt e` with `KitStabilizes` certificate

No arbitrary selection among multiple valid options.

### 3. EM is located precisely
```lean
-- Constructive
theorem ne_bot_imp_notnot_sig : D.O x ≠ ⊥ → ¬¬ D.Sig x

-- Classical (EM here)
theorem ne_bot_imp_sig : D.O x ≠ ⊥ → D.Sig x
```
The step `¬¬P → P` is the only classical content.

### 4. The dynamics is parameterized
```lean
def PickOracle (D) : Type := ∀ e, OraclePick ... e
```
Given an oracle, we get confluence, minimality, omegaState.

---

## What IS NOT Proven

### 1. PickOracle is constructible from EM alone
The code **assumes** `PickOracle` as a parameter. It does not **derive** it.

To claim "EM suffices, AC not needed", we would need:
```lean
theorem pickOracle_from_EM (D : StructuralDichotomy X) 
    [∀ x, Decidable (D.Sig x)] : -- or weaker classical assumption
    ∀ i, SDPick D (elem i)
```
This is NOT in the codebase.

### 2. The distinction is formal in Lean's type theory
In Lean:
- `Classical.em` gives `∀ P, P ∨ ¬P` in Prop
- `Classical.choice` extracts data from `Nonempty`

To go from `∀ e, (Sig e ∨ ¬Sig e)` to `∀ e, SDPick e` requires:
- Either decidability (computational)
- Or classical choice (to extract the proof term)

The claim "not AC" may be true **mathematically** but needs care **type-theoretically**.

---

## The Conceptual Argument (Not Yet Formalized)

### Why it's not AC (mathematically)

AC says: "For each non-empty set in a family, select an element."

The selection is **arbitrary** — multiple valid choices exist.

RevHalt says: "For each trace, determine which side of a partition."

The "selection" is **unique** — only one correct answer per trace.

### Why it's EM (mathematically)

The only non-constructive content is: "For each trace, either Halts or Stabilizes."

This is `∀ T, Halts T ∨ ¬Halts T` — exactly EM applied to a specific predicate.

### The gap

Mathematically: EM on `Halts` gives the bit. Structure gives the content.

Type-theoretically: extracting a **term** `SDPick D x` from a **proposition** `Sig x ∨ ¬Sig x` requires care.

---

## Formalization Roadmap

### Level 1: Propositional (Weak)
```lean
-- Given EM, we can decide the side (in Prop)
theorem side_decidable [Classical] (x : X) : D.Sig x ∨ ¬D.Sig x := 
  Classical.em (D.Sig x)
```
This is trivial with `Classical`.

### Level 2: Data Extraction (Medium)
```lean
-- Construct SDPick from classical EM
noncomputable def sdpick_of_classical (x : X) : SDPick D x := by
  classical
  by_cases h : D.Sig x
  · exact ⟨true, h⟩
  · exact ⟨false, D.not_sig_imp_bot x h⟩
```
This should work but is `noncomputable`. Uses `Classical.em`, not `Classical.choice` on arbitrary sets.

### Level 3: Oracle Construction (Strong)
```lean
-- Full oracle from EM alone
noncomputable def pickOracle_of_classical : SDOracle D Index elem := 
  fun i => sdpick_of_classical D (elem i)
```
If Level 2 works, this follows.

### Level 4: Characterization (Ideal)
```lean
-- Theorem: SDOracle requires exactly EM, not AC
-- (This would need a formal model comparison)
```
This is meta-level — comparing what's needed in different foundations.

---

## What Needs To Be Done

### Minimal (clarify current status)
- [ ] Add `sdpick_of_classical` to show EM suffices for single picks
- [ ] Add `pickOracle_of_classical` to show EM suffices for full oracle
- [ ] Document that these are `noncomputable` but don't use `Classical.choice` on arbitrary types

### Medium (strengthen the claim)
- [ ] Analyze exactly which classical principles are used
- [ ] Show that `Classical.em` suffices, `Classical.choice` is not invoked
- [ ] Compare with a construction that **would** need AC

### Strong (formal separation)
- [ ] Define what "AC-regime" vs "EM-regime" means formally
- [ ] Prove that PickOracle is in EM-regime
- [ ] This may require working in a weaker foundation to show the distinction

---

## The Honest Statement

**Current**: "Conceptually, the choice is EM not AC, because it's binary and forced."

**After Level 2-3**: "In Lean, SDOracle is constructible using only Classical.em, not Classical.choice on arbitrary types."

**After Level 4**: "Formally, PickOracle is independent of AC in the sense of [precise definition]."

---

## Why This Matters

If the EM/AC distinction holds formally:
- RevHalt shows that certain "choice functions" are not really choices
- They are readings of a structural partition
- This is a contribution to understanding what AC actually does

If it doesn't hold (in some technical sense):
- The claim needs to be weakened
- But the structural insight (binary, forced, unique) remains valid

---

## Connection to Main Thesis

The main thesis is:
> "Dichotomies can be structural (EM-regime) rather than extensional (AC-regime), and StructuralDichotomy captures when."

Formalizing the EM/AC distinction would make this thesis **provable**, not just **argued**.

---

## Files to Modify/Create

- [ ] `StructuralDichotomy.lean` — add `sdpick_of_classical`
- [ ] `AbstractDynamics.lean` — add `pickOracle_of_classical`
- [ ] `EMvsAC.lean` (new) — formal analysis of which principles are used

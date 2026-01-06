# Kernel Unification Roadmap

> **Purpose:** This document provides a precise specification of the unified kernel characterization. It is designed to be actionable in a new session and uses rigorous formulations.

---

## Precise Formulation (Publication-Ready)

The set **𝒦 := { T : Trace | up T = ⊥ }** (called `upKernel` in code) satisfies:

### 1. Logical (Π₁)
```
T ∈ 𝒦 ↔ Stabilizes T ↔ ¬ Halts T
```
- **File:** `Theory/Stabilization.lean` lines 30, 47
- **File:** `Theory/Categorical.lean` line 681 (`upKernel`)

### 2. Topological (Scott)
```
𝒦 is Scott-closed and NOT Scott-open (hence not clopen)
```
- **File:** `Theory/ScottTopology.lean` lines 96, 106

### 3. Coinductive (via HitTrace functor)
```
For any transition system (Moves, Target) and state x:
  Safe(x) ↔ HitTrace(x) ∈ 𝒦
```
- **Note:** This applies to traces arising from transition systems, not to all abstract traces.
- **File:** `Theory/OrdinalKernelBridge.lean` lines 103, 118

### 4. Computational (restricted to Machine traces)
```
The predicate e ↦ (Machine e ∈ 𝒦) is not r.e.
```
- **Note:** This restriction uses arithmetization of Halts via `HaltsSigma1`.
- **File:** `Theory/KernelUndecidability.lean` line 51

---

## Important Clarifications

### On Notation
- **In code:** `K` refers to `RHKit` (a Kit structure), NOT the kernel.
- **The kernel:** is `upKernel : Set Trace := { T | upOp T = ⊥ }`.
- **In documentation:** Use `𝒦` for the kernel to avoid confusion.

### On "Ordinal Compression"
- The `OrdinalKernelBridge` works via the `HitTrace` functor.
- It proves: for transition systems, `PostFix C → C x → HitTrace(x) ∈ 𝒦`.
- This is NOT a claim about all traces, only those arising from transition systems.

### On "Gödel without Arithmetization"
- **Object level:** The kernel 𝒦 is defined abstractly (no encoding).
- **Proof level:** The undecidability proof USES arithmetization (`HaltsSigma1.lean`).
- **Accurate formulation:** "The kernel is abstract, the undecidability proof uses arithmetization."

---

## Status: What Exists

| # | Perspective | Status | File | Line |
|---|-------------|--------|------|------|
| 1 | Logical (Π₁) | ✅ Done | `Stabilization.lean` | 30, 47 |
| 2 | Algebraic (Kernel) | ✅ Done | `Categorical.lean` | 681 |
| 3 | Topological (Scott) | ✅ Done | `ScottTopology.lean` | 96, 106 |
| 4 | Computational (not r.e.) | ✅ Done | `KernelUndecidability.lean` | 51 |
| 5 | Coinductive (via HitTrace) | ✅ Done | `OrdinalKernelBridge.lean` | 103, 118 |
| 6 | Constructive (Queue) | ⚠️ Partial | See below |

---

## Remaining Work

### Task 1: Complete `EvalnGraph_spec` (Priority: HIGH)

**Location:** `RevHalt/Theory/Arithmetization/EvalnGraph0.lean`

**Current state:** Two `admit` statements at soundness/completeness.

**What's needed:**
1. **Soundness (→):** Extract evaln from the finite β-table witness.
2. **Completeness (←):** Build the β-table from an evaln derivation tree.

**Verification:**
```bash
lake build RevHalt.Theory.Arithmetization.EvalnGraph0
# Should compile without `admit` warnings
```

---

### Task 2: Splitter → Trace Bridge (Priority: MEDIUM)

**Goal:** Connect `Queue` certificate from `Splitter/Core.lean` to `Stabilizes`.

**Missing theorem:**
```lean
-- File: RevHalt/Theory/Splitter/TraceBridge.lean (NEW)

def trace_of_splitter (s : Splitter) (x : s.Pos) : Trace :=
  fun n => ∃ y, ReachN s.Next x n y ∧ s.Target y

theorem queue_implies_stabilizes (s : Splitter) (x : s.Pos) :
    Queue s x → Stabilizes (trace_of_splitter s x)
```

**Key:** Use `OrdinalKernelBridge.Safe_iff_Stabilizes_HitTrace` + show Queue is PostFix.

---

### Task 3: Create `KernelUnified.lean` (Priority: AFTER Tasks 1-2)

**Location:** `RevHalt/Theory/KernelUnified.lean` (NEW)

**Contents:**
```lean
import RevHalt.Theory.Stabilization
import RevHalt.Theory.Categorical
import RevHalt.Theory.ScottTopology
import RevHalt.Theory.KernelUndecidability
import RevHalt.Theory.OrdinalKernelBridge

theorem kernel_unified :
    -- 1. Logical: Stabilizes ↔ up = ⊥ ↔ ¬ Halts
    (∀ T, Stabilizes T ↔ up T = ⊥) ∧
    (∀ T, Stabilizes T ↔ ¬ Halts T) ∧
    -- 2. Topological: Scott-closed, not Scott-open
    IsScottClosed { T | Stabilizes T } ∧
    ¬ IsScottOpen { T | Stabilizes T } ∧
    -- 3. Computational: not r.e. on Machine traces
    (RECodePred (fun e => Stabilizes (Machine e)) → False) ∧
    -- 4. Coinductive: via HitTrace
    (∀ Moves Target C x, PostFix Moves Target C → C x →
      Stabilizes (HitTrace Moves Target x))
:= by
  exact ⟨Stabilizes_iff_up_eq_bot,
         Stabilizes_iff_NotHalts,
         stabilizesSet_isScottClosed,
         stabilizesSet_not_isScottOpen,
         kernel_not_re _ _,
         fun M T C x hC hx => (Safe_iff_Stabilizes_HitTrace M T x).mp
           (postFix_imp_safe M T C hC x hx)⟩
```

---

## Quick Reference: Key Files

| Purpose | Path |
|---------|------|
| Kernel definition | `Theory/Categorical.lean:681` |
| Stabilizes definition | `Theory/Stabilization.lean:20` |
| Scott closedness | `Theory/ScottTopology.lean:96` |
| Not r.e. | `Theory/KernelUndecidability.lean:51` |
| Coinduction bridge | `Theory/OrdinalKernelBridge.lean:73-118` |
| Queue definition | `Theory/Splitter/Core.lean` |
| EvalnGraph (incomplete) | `Theory/Arithmetization/EvalnGraph0.lean:837` |

---

## Success Criteria

- [ ] `EvalnGraph_spec` compiles without `admit`
- [ ] `queue_implies_stabilizes` is proven
- [ ] `KernelUnified.lean` exports the unified theorem
- [ ] `lake build` succeeds with no `sorry`/`admit` in core theory files

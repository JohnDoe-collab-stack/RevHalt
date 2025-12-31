# Dependency Architecture

This document shows the complete dependency structure of RevHalt, separating the constructive core from evaluation layers.

## Full Dependency Graph

```mermaid
graph TD

%% =========================
%% 0) CONSTRUCTIVE KERNEL
%% =========================
subgraph K["Lean kernel / constructive core"]
  K0["Induction + bounded search (finite m)"]
  K1["Operator facts (mono, idem, ker_iff, sig_invar)"]
  K2["¬¬-content (no branch selection)"]
end

%% =========================
%% 1) STRUCTURAL (GEOMETRY)
%% =========================
subgraph S["Structural layer (operator geometry)"]
  SD["StructuralDichotomy(O, Sig, ker_iff, sig_invar)"]
  NNSig["O x ≠ ⊥  →  ¬¬ Sig x   (constructive)"]
  Ker["O x = ⊥  ↔  ¬ Sig x     (kernel identification)"]
  Inv["Sig(O x) ↔ Sig x        (signal invariance)"]
end

K1 --> SD
SD --> Ker
SD --> Inv
SD --> NNSig

%% =========================
%% 2) SEMANTICS (TRUTH)
%% =========================
subgraph T["Semantics layer (Truth : PropT → Prop)"]
  EMT["EM_Truth: ∀p, Truth p ∨ ¬Truth p"]
  DNTruth["DN-Elim_Truth: ∀p, ¬¬Truth p → Truth p"]
  LPOT["LPO_Truth: ∀T:ℕ→PropT, (∃n, Truth(T n)) ∨ (∀n, ¬Truth(T n))"]
end

LPOT --> EMT
EMT --> DNTruth

%% =========================
%% 3) EVALUATION (OPERATIONAL ACCESS)
%% =========================
subgraph E["Evaluation layer (Eval Γ φ : Prop)"]
  EME["EM_Eval(Γ): ∀φ, Eval Γ φ ∨ ¬Eval Γ φ"]
  DNEval["DN-Elim_Eval(Γ): ∀φ, ¬¬Eval Γ φ → Eval Γ φ"]
  LPOE["LPO_Eval(Γ): ∀s:ℕ→Sentence, (∃n, Eval Γ (s n)) ∨ (∀n, ¬Eval Γ (s n))"]
end

LPOE --> EME
EME --> DNEval

%% =========================
%% 4) CLASSICAL META-LEVEL (Prop)
%% =========================
subgraph C["Classical meta-level (Prop)"]
  EM["EM: ∀P:Prop, P ∨ ¬P"]
  LPOB["LPOBool: ∀f:ℕ→Bool, (∃n, f n = true) ∨ (∀n, f n = false)"]
end

EM --> LPOB
EM --> EMT
EM --> LPOT
EM --> EME
EM --> LPOE

%% =========================
%% 5) THE TWO GAPS (LOCALIZATION)
%% =========================
subgraph G["Two independent gaps (source localization)"]
  ClassGap["Class gap: Prop ↪ PropT (e.g. constTrace / degenerate Truth := id)"]
  OrdGap["Ordinal gap: finite m → ω (existential-over-ℕ)"]
end

ClassGap --> EM
OrdGap --> LPOT
OrdGap --> LPOE
OrdGap --> LPOB

%% =========================
%% 6) DEGENERATE BASE INSTANCE (RevHalt/Base)
%% =========================
subgraph D["Degenerate base instance"]
  Deg["PropT := Prop,  Truth := id,  Trace := ℕ→Prop"]
  Stage0["Stage 0 dichotomy over Trace  ↔  EM (via constTrace)"]
end

Deg --> Stage0
Stage0 --> EM
ClassGap --> Deg

%% =========================
%% 7) FROM STRUCTURE TO BRANCH SELECTION (RELATIVE)
%% =========================
subgraph R["Relative branch selection (where evaluation is used)"]
  ReadSigTruth["(Truth-level)  ¬¬Sig → Sig  via DNTruth"]
  ReadSigEval["(Eval-level)   ¬¬Sig → Sig  via DNEval"]
end

NNSig --> ReadSigTruth
DNTruth --> ReadSigTruth

NNSig --> ReadSigEval
DNEval --> ReadSigEval

%% =========================
%% 8) FINITE vs ω (DECIDABLE DATA)
%% =========================
subgraph F["Finite vs ω on decidable data"]
  FinBool["Finite m (Bool): decidable bounded dichotomy  (constructive)"]
  OmegaBool["ω (Bool): LPOBool"]
end

K0 --> FinBool
FinBool -. "not derivable constructively" .-> OmegaBool
LPOB --> OmegaBool
```

## Key Observations

1. **Constructive Core (K)**: All operator facts (`up_mono`, `up_idem`, `up_eq_bot_iff`, `exists_up_iff`) live here with 0 axioms.

2. **Two Independent Gaps (G)**:
   - **Class gap**: `Prop ↪ PropT` — yields EM when you can encode arbitrary propositions
   - **Ordinal gap**: finite → ω — yields LPO on decidable data

3. **Layered Evaluation**:
   - `EM_Truth` / `LPO_Truth` — semantic level
   - `EM_Eval` / `LPO_Eval` — operational level (what an evaluator can decide)

4. **Branch Selection is Relative**: The passage from `¬¬Sig` to `Sig` can be resolved at different levels (Truth or Eval), depending on which layer you're working in.

5. **Degenerate Instance**: `RevHalt/Base` is the special case where `PropT := Prop` and `Truth := id`, which collapses everything to the meta-level EM.

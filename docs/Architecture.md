# RevHalt — Architecture de continuation au-delà de l'indécidabilité uniforme

## Problème fondamental

La théorie standard formalise l'arrêt via une alternative globale ("halte / ne halte pas") puis constate l'impossibilité d'un décideur uniforme (mur de Turing). Le point aveugle est que cette présentation **fusionne** plusieurs notions distinctes :

- ce qui est **formable** (quels objets/suites on autorise),
- ce qui est **vrai** (au sens sémantique),
- ce qui est **accessible** (au sens opératoire/évaluatif).

RevHalt traite cette fusion comme le vrai problème : **comment continuer à faire des mathématiques rigoureuses** quand l'uniformité statique est impossible, tout en gardant un contrôle fin sur ce qui relève (ou non) du classique.

---

## Les 3 référentiels (séparation minimale)

| Référentiel | Rôle | Description |
|-------------|------|-------------|
| **R1 — Formation/grammaire** | Quels énoncés et suites sont admissibles | `Adm : (ℕ → Sentence) → Prop` |
| **R2 — Sémantique/vérité** | Ce qui est vrai "en soi" | `Truth : PropT → Prop`, sans supposer EM |
| **R3 — Évaluation/accès** | Ce qu'un mécanisme permet de trancher | `Eval : List Sentence → Sentence → Prop` |

Cette séparation est structurelle : changer R1 change le sens de "∀s"; R3 peut décider localement sans fournir de décision globale.

---

## Noyau technique minimal (Traces et Clôture)

### Définitions de base

| Concept | Définition | Fichier |
|---------|------------|---------|
| **Trace** | `ℕ → Prop` | [Trace.lean](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Base/Trace.lean) |
| **Halts** | `∃ n, T n` (Σ₁) | [Trace.lean#L24](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Base/Trace.lean#L24) |
| **up (clôture)** | `(up T)(n) ↔ ∃ k ≤ n, T k` | [Trace.lean#L27](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Base/Trace.lean#L27) |
| **Stabilizes** | `∀ n, ¬ T n` (Π₁) | [Stabilization.lean#L20](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Stabilization.lean#L20) |

### Théorème clé : Noyau algébrique

Le "négatif" (stabilisation) devient manipulable comme **objet algébrique** :

```
up T = ⊥  ↔  ∀ n, ¬ T n
```

> [!IMPORTANT]
> Ce déplacement remplace une négation Π₁ "fantôme" par un critère de noyau (kernel).

| Théorème | Fichier |
|----------|---------|
| `up_eq_bot_iff` | [Categorical.lean#L115-L132](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Categorical.lean#L115-L132) |
| `Stabilizes_iff_up_eq_bot` | [Stabilization.lean#L47-L49](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Stabilization.lean#L47-L49) |
| `KitStabilizes_iff_up_eq_bot` | [Stabilization.lean#L70-L73](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Stabilization.lean#L70-L73) |
| `up_is_projector` | [Categorical.lean#L196-L204](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Categorical.lean#L196-L204) |

---

## T1 : Canonicité

L'opérateur `up` normalise toutes les traces en traces monotones. Sous `DetectsMonotone`, le verdict Rev est extensionnellement équivalent à Halts.

| Théorème | Énoncé | Fichier |
|----------|--------|---------|
| `T1_traces` | `Rev0_K K T ↔ Halts T` | [Canonicity.lean#L26-L36](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Canonicity.lean#L26-L36) |
| `T1_uniqueness` | `Rev0_K K1 T ↔ Rev0_K K2 T` | [Canonicity.lean#L48-L52](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Canonicity.lean#L48-L52) |
| `T1_stabilization` | `KitStabilizes K T ↔ Stabilizes T` | [Stabilization.lean#L54-L61](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Stabilization.lean#L54-L61) |

---

## T2 : Impossibilité (statique)

Il n'existe pas d'objet unique `H` qui décide uniformément toutes les instances dans un cadre fixé.

```
¬∃ H . ∀ e, Total(H,e) ∧ Correct(H,e) ∧ Complete(H,e)
```

| Composant | Description | Fichier |
|-----------|-------------|---------|
| `ImpossibleSystem` | Système de preuve minimal | [Impossibility.lean#L68-L74](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Impossibility.lean#L68-L74) |
| `InternalHaltingPredicate` | Prédicat H avec Total+Correct+Complete+r.e. | [Impossibility.lean#L80-L88](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Impossibility.lean#L80-L88) |
| `diagonal_bridge` | Diagonalisation via Kleene SRT | [Impossibility.lean#L46-L66](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Impossibility.lean#L46-L66) |
| **`T2_impossibility`** | Le théorème final | [Impossibility.lean#L94-L118](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Impossibility.lean#L94-L118) |

---

## T3 : Complémentarité (cinétique)

Au lieu d'un décideur statique, on formalise une **dynamique d'extensions** :

```
∀ e, ∃ Sₑ (extension/étape admissible ajoutant l'info pertinente à e)
```

Le point n'est pas de "contredire" T2 mais de préciser : T2 interdit l'uniformité fermée; T3 décrit une cinétique d'extensions vérifiables.

| Composant | Description | Fichier |
|-----------|-------------|---------|
| `OraclePick` | Certificat Σ₁ ou Π₁ pour un code `e` | [Complementarity.lean#L363-L368](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Complementarity.lean#L363-L368) |
| `S1Set` | Frontière non-internalisable | [Complementarity.lean#L122-L127](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Complementarity.lean#L122-L127) |
| `S3Set` | Extension S₂ ∪ S₁ | [Complementarity.lean#L129-L132](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Complementarity.lean#L129-L132) |
| **`T3_weak_extension_explicit`** | S₃ sain + contient encode_halt(e) | [Complementarity.lean#L190-L246](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Complementarity.lean#L190-L246) |
| **`T3_strong`** | Famille {S₃ₙ} depuis partitions de S₁ | [Complementarity.lean#L299-L346](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Complementarity.lean#L299-L346) |
| **`T3_oracle_extension_explicit`** | Extension two-sided locale | [Complementarity.lean#L390-L472](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Complementarity.lean#L390-L472) |

---

## Quantifier Swap : T2 vs T3

| Demande | Forme quantificateur | Statut | Interprétation |
|---------|----------------------|--------|----------------|
| Turing (uniforme) | `∃H ∀e` | Interdit (T2) | Pas de détecteur uniforme |
| RevHalt (instance) | `∀e ∃Sₑ` | Permis (T3) | Certificats locaux |

| Théorème | Fichier |
|----------|---------|
| `T3_permits_instancewise` | [QuantifierSwap.lean#L44-L97](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/QuantifierSwap.lean#L44-L97) |
| `quantifier_swap_coexistence` | [QuantifierSwap.lean#L112-L136](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/QuantifierSwap.lean#L112-L136) |

---

## EM vs LPO au niveau évaluatif (R3) et rôle de R1

### Définitions

| Concept | Définition | Fichier |
|---------|------------|---------|
| `EM_Eval` | `∀ φ, Eval Γ φ ∨ ¬ Eval Γ φ` | [RelativeR1.lean#L46-L47](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/RelativeR1.lean#L46-L47) |
| `LPO_Eval_R1` | `∀ s, Adm s → (∃ n, Eval Γ (s n)) ∨ (∀ n, ¬ Eval Γ (s n))` | [RelativeR1.lean#L41-L43](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/RelativeR1.lean#L41-L43) |
| `AdmitsConst` | `∀ φ, Adm (fun _ => φ)` | [RelativeR1.lean#L55-L56](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/RelativeR1.lean#L55-L56) |

### Mécanisme de collapse (localisé)

```
AdmitsConst(Adm) ⟹ (LPO_R1 → EM_Eval)
```

| Théorème | Fichier |
|----------|---------|
| `LPO_R1_imp_EM_if_const` | [RelativeR1.lean#L64-L82](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/RelativeR1.lean#L64-L82) |

> [!IMPORTANT]
> **LPO ne "force" EM que si R1 autorise le const-trick**. La sécurité logique se contrôle via R1.

---

## Cut/Bit : Interface discret/continu comme grammaire de probes

### Définitions

| Grammaire | Description | Fichier |
|-----------|-------------|---------|
| `AdmBit` | Suites indexées `Bit(n, a, x)` | [RelativeR1.lean#L199-L200](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/RelativeR1.lean#L199-L200) |
| `AdmCutDyadic` | Suites dyadiques `Cut(k/2^n, x)` | [RelativeR1.lean#L203-L204](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/RelativeR1.lean#L203-L204) |
| `AdmMix` | Alternance contrôlée Cut/Bit | [RelativeR1.lean#L207-L211](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/RelativeR1.lean#L207-L211) |
| `BitCutLink` | Compatibilité sémantique | [RelativeR1.lean#L189-L196](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/RelativeR1.lean#L189-L196) |

### Non-collapse structurel

| Théorème | Énoncé | Fichier |
|----------|--------|---------|
| `BitIndexDistinct` | Hypothèse minimale de distinction | [RelativeR1.lean#L299-L300](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/RelativeR1.lean#L299-L300) |
| **`AdmBit_not_admits_const`** | `¬ AdmitsConst (AdmBit Bit x)` | [RelativeR1.lean#L304-L319](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/RelativeR1.lean#L304-L319) |
| `bit_noncollapse_package` | Package complet non-collapse | [RelativeR1.lean#L324-L344](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/RelativeR1.lean#L324-L344) |

---

## Theorem de Séparation (SeparationTheorem.lean)

| Théorème | Énoncé | Fichier |
|----------|--------|---------|
| `separation` | `LPO_R1(AdmTwoProbes) ∧ ¬EM_Eval ∧ ¬AdmitsConst` | [SeparationTheorem.lean#L131-L141](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/SeparationTheorem.lean#L131-L141) |
| `LPO_R1_not_implies_EM` | `¬(LPO_R1 → EM_Eval)` en général | [SeparationTheorem.lean#L144-L153](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/SeparationTheorem.lean#L144-L153) |

---

## Dynamique et Navigation

| Composant | Description | Fichier |
|-----------|-------------|---------|
| `State` | Corpus + preuve de soundness | [Dynamics.lean#L75-L77](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Dynamics.lean#L75-L77) |
| `Chain` | Itération de steps | [Dynamics.lean#L210-L222](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Dynamics.lean#L210-L222) |
| `lim` | Limite (union) d'une chaîne | [Dynamics.lean#L275](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Dynamics.lean#L275) |
| `omegaState` | État canonique ω | [Dynamics.lean#L749-L755](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Dynamics.lean#L749-L755) |
| `lim_schedule_free` | Indépendance du schedule | [Dynamics.lean#L686-L713](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Dynamics.lean#L686-L713) |
| `lim_eq_omegaState` | Équivalence limite/omegaState | [Dynamics.lean#L779-L789](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/Dynamics.lean#L779-L789) |

---

## Théorèmes de Synthèse (RelativeHalting.lean)

| Théorème | Énoncé | Fichier |
|----------|--------|---------|
| **`RelativeHaltingDecision`** | Décision sous LPO_R1 | [RelativeHalting.lean#L19-L35](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theorems/RelativeHalting.lean#L19-L35) |
| **`Safety_NoCollapse`** | Sécurité : ¬AdmitsConst | [RelativeHalting.lean#L37-L56](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theorems/RelativeHalting.lean#L37-L56) |

---

## EM ↔ Dichotomy (OrdinalBoundary.lean)

| Théorème | Énoncé | Fichier |
|----------|--------|---------|
| `dichotomy_all_iff_em` | `(∀T, Halts T ∨ Stabilizes T) ↔ (∀P, P ∨ ¬P)` | [OrdinalBoundary.lean#L227-L231](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/OrdinalBoundary.lean#L227-L231) |
| `stage_zero_is_em` | Étage 0 sur traces arbitraires = EM | [OrdinalMechanical.lean#L303-L316](file:///c:/Users/frederick.loubli.TKS/OneDrive%20-%20t-kartor.com/Pictures/WORKSPACELEAN/RevHalt/RevHalt/Theory/OrdinalMechanical.lean#L303-L316) |

---

## Milestone Concret : Triptyque (A)(B)(C)

### État actuel

| Objectif | Théorèmes existants | Statut |
|----------|---------------------|--------|
| **(A) LPO_R1 constructif sur grammaires probes** | `LPO_R1_AdmBit_finite_support` (NEW), `LPO_R1_finite_orbit`, `LPO_R1_mono_finite_support` | ✅ Non-jouet pour AdmBit |
| **(B) ¬AdmitsConst structurel** | `AdmBit_not_admits_const`, `Safety_NoCollapse` | ✅ Formalisé |
| **(C) Négation-kernel** | `Stabilizes_iff_up_eq_bot`, `KitStabilizes_iff_up_eq_bot`, `StabilizesE_AdmBit_iff` (NEW) | ✅ Formalisé |

### Nouveau fichier: LPO_AdmBit_Constructive.lean

| Théorème | Axiomes | Description |
|----------|---------|-------------|
| `LPO_R1_AdmBit_finite_support` | **propext** (no Classical.choice) | LPO_R1 pour AdmBit avec support fini |
| `StabilizesE_AdmBit_iff` | Aucun | Lien stabilisation ↔ kernel pour AdmBit |
| `HaltsE_AdmBit_witness` | Aucun | Extraction du témoin (n, a) |
| `AdmBit_noncollapse_with_LPO` | **propext** | Package complet : LPO_R1 ∧ ¬AdmitsConst |

> [!TIP]
> Le théorème principal `LPO_R1_AdmBit_finite_support` ne dépend que de `propext`, pas de `Classical.choice`.
> C'est la **preuve constructive** que LPO_R1 fonctionne sur grammaires Bit réelles.

### Chaînons restants (optionnels)

1. **`LPO_R1_AdmDyadicProbe`** : Étendre au cas `AdmDyadicProbe` du Models/DyadicSystem (combine Bit + Cut).

---

## Hiérarchie des fichiers

```
RevHalt/
├── Base/
│   ├── Trace.lean          # Trace, Halts, up
│   └── Kit.lean            # RHKit, DetectsMonotone, Rev_K
├── Theory/
│   ├── Canonicity.lean     # T1
│   ├── Impossibility.lean  # T2
│   ├── Complementarity.lean # T3
│   ├── Stabilization.lean  # Kernel (up T = ⊥)
│   ├── Categorical.lean    # up_is_projector, Galois
│   ├── QuantifierSwap.lean # ∃H∀e vs ∀e∃Sₑ
│   ├── Dynamics.lean       # Navigation, omegaState
│   ├── RelativeFoundations.lean # LPO_Eval, EM_Eval
│   ├── RelativeR1.lean     # LPO_R1, AdmBit, AdmitsConst
│   ├── LPO_AdmBit_Constructive.lean # LPO_R1 constructif pour AdmBit
│   ├── SeparationTheorem.lean # LPO_R1 ∧ ¬EM_Eval
│   ├── MonotoneGrammar.lean # Séquences croissantes
│   ├── OrbitGrammar.lean   # Orbites finies + pigeonhole
│   ├── OrdinalBoundary.lean # EM ↔ Dichotomy
│   └── ...
├── Theorems/
│   └── RelativeHalting.lean # Synthèse : Decision + Safety
└── Models/
    └── DyadicSystem.lean   # Grammaire concrète AdmDyadicProbe
```

---

## Statut actuel

✅ **`RevHalt/Theory/LPO_AdmBit_Constructive.lean`** a été implémenté avec succès.

Le fichier contient les théorèmes suivants, tous prouvés sans `Classical.choice` :

```lean
-- LPO_R1 pour AdmBit avec support fini (propext seulement)
theorem LPO_R1_AdmBit_finite_support
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Bit : ℕ → Fin 2 → Referent → Sentence) (x : Referent)
    [∀ n a, Decidable (Eval Γ (Bit n a x))]
    (hFS : FiniteSupportBit Eval Γ Bit x) :
    LPO_Eval_R1 Eval Γ (AdmBit Bit x)

-- Package complet : LPO_R1 ∧ ¬AdmitsConst (propext seulement)
theorem AdmBit_noncollapse_with_LPO
    (Eval : List Sentence → Sentence → Prop) (Γ : List Sentence)
    (Bit : ℕ → Fin 2 → Referent → Sentence) (x : Referent)
    [∀ n a, Decidable (Eval Γ (Bit n a x))]
    (hDist : BitIndexDistinct Bit)
    (hFS : FiniteSupportBit Eval Γ Bit x) :
    LPO_Eval_R1 Eval Γ (AdmBit Bit x) ∧ ¬ AdmitsConst (AdmBit Bit x)
```

> [!NOTE]
> Le triptyque (A)(B)(C) est maintenant **complet** pour les grammaires AdmBit.


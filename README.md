# RevHalt

RevHalt est un développement Lean 4 / mathlib sur une “théorie du reverse-halting” visant à rendre explicite
où se situe la puissance non-constructive (EM, choix, etc.) : comme **capacité d’accès** localisée (bridge/pick),
pas comme axiome ambiant implicite.

## Idée centrale

Le projet sépare trois niveaux souvent confondus :
- **(R1) Formable/testable** : ce qui est encodable et manipulable mécaniquement.
- **(R2) Vrai sémantiquement** : ce qui est vrai dans un modèle (représenté externement).
- **(R3) Accessible opératoirement** : ce qui est sélectionnable/décidable par un évaluateur/oracle.

Le cœur structurel repose sur les traces `Trace := ℕ → Prop` et l’opérateur de clôture cumulative `up`,
qui rigidifie le “négatif” : la stabilisation devient un **noyau** (`up T = ⊥`) au lieu d’une négation opaque.

## Perspective opératoire (R3)

La partie “opératoire” n’est pas un commentaire : elle est formalisée via une architecture et des transferts.

- **Flux (concret)** : `⟨Sat, compile, oBridge⟩` (sémantique + compilation + pont) donne, pour une entrée `(Γ, φ)` :
  1) du **code** `e := compile Γ φ`,
  2) une **évaluation** `Eval Γ φ := Converges e`,
  3) une **trace mécanique** `LR Γ φ := aMachine e`,
  4) et, via le pont, l’identification `Eval Γ φ ↔ SemConsequences Sat Γ φ`
  (`RevHalt/Theory/ThreeBlocksArchitecture.lean`).

- `Rev0_K K T := K.Proj (up T)` force une normalisation (via `up`) avant observation : c’est une décision *par accès*
  plutôt qu’une vérité primitive (`RevHalt/Base/Kit.lean`).
- `OracleMachine.Eval` est défini uniquement depuis la compilation (`compile`) et la convergence, et `OracleBridge`
  est l’unique hypothèse reliant cette évaluation à la conséquence sémantique (`SemConsequences`)
  (`RevHalt/Theory/ThreeBlocksArchitecture.lean`).
- La section “Coverage & Decidability” de `ThreeBlocksArchitecture` formalise des transferts du type :
  “`Eval` décidable + compilation couvrante ⇒ `Halts` (et donc `Rev0_K`) décidable”, ce qui explicite
  exactement où se loge la puissance de décision.
- T3 formalise une procédure d’extension locale (un pas `S₂ ↦ S₂ ∪ {pick.p}`) à partir d’un certificat externe,
  et `AbstractDynamics` itère ces pas le long d’une schedule puis prend une limite (union) ; `omegaState` capture
  l’état canonique sous fairness (`RevHalt/Theory/Complementarity.lean`, `RevHalt/Theory/AbstractDynamics.lean`).

## Ce qui est formalisé dans ce dépôt

- **Base** : `Trace`, `Halts`, `up` (`RevHalt/Base/Trace.lean`) ; `RHKit`, `DetectsMonotone`, `Rev0_K`
  (`RevHalt/Base/Kit.lean`).
- **Structure** : ordre pointwise sur `Trace`, `up` comme fermeture/réflecteur, noyau `up_eq_bot_iff`
  (`RevHalt/Theory/Categorical.lean`).
- **Stabilisation** : `Stabilizes`, `KitStabilizes` et équivalences avec `up T = ⊥`
  (`RevHalt/Theory/Stabilization.lean`).
- **T1 (Canonicité)** : `T1_traces` + pont sémantique `T1_semantics`
  (`RevHalt/Theory/Canonicity.lean`).
- **T2 (Barrière uniforme)** : diagonalisation et `T2_impossibility`
  (`RevHalt/Theory/Impossibility.lean`).
- **T3 (Navigation locale)** : complémentarité S1/S2/S3, `OraclePick`, extensions locales et “swap”
  (`RevHalt/Theory/Complementarity.lean`, `RevHalt/Theory/QuantifierSwap.lean`).
- **Architecture 3-blocs** : `OracleMachine` + bridge `Eval ↔ SemConsequences`, plus transferts “decidability/coverage”
  (`RevHalt/Theory/ThreeBlocksArchitecture.lean`).
- **Dynamique abstraite** : `PickWorld`, chaînes/limites, `omegaState`
  (`RevHalt/Theory/AbstractDynamics.lean`).
- **Frontière ordinale (EM/LPO)** : la caractérisation `dichotomy_all_iff_em`, plus `LPO`/`LPOBool` et le “const-trick” `AdmitsConst`
  (`RevHalt/Theory/OrdinalBoundary.lean`).
- **Vérification mécanique (frontière ordinale)** : version “audit/étapes finies → ω” avec `HaltsUpTo`/`StabilizesUpTo`, `LPOBool ↔ LPOProp`, et `stage_zero_is_em`
  (`RevHalt/Theory/OrdinalMechanical.lean`).
- **Fondations relatives** : principes paramétrés `EM_Truth` / `EM_Eval`, schémas `LPO_Truth` / `LPO_Eval`, opérateur cumulatif `upE` et caractérisations noyau/dichotomie
  (`RevHalt/Theory/RelativeFoundations.lean`).
- **R1 relatif (grammaires)** : `LPO_Eval_R1` restreint à une grammaire admissible `Adm`, condition de collapse `AdmitsConst`, et hiérarchies/contre-exemples (p.ex. `CutBit`)
  (`RevHalt/Theory/RelativeR1.lean`).

## Points d’entrée

- Racine librairie : `RevHalt.lean` (importe `RevHalt.Main`).
- Entrée base : `RevHalt/Base.lean`.
- Entrée théorie : `RevHalt/Theory.lean`.

## Audit d’axiomes

Plusieurs fichiers finissent avec des `#print axioms ...` pour auditer les preuves **par théorème**.
Selon les imports et le style de preuve, certains résultats peuvent légitimement faire apparaître
des axiomes (p.ex. `propext`, `Classical.choice`) : l’objectif est de **localiser** où ils entrent.

## Build

Le projet dépend de mathlib (voir `lakefile.lean`). Commandes usuelles :

- `lake build`
- `lake build RevHalt`

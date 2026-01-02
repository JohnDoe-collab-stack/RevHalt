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
- **Architecture 3-blocs** : `OracleMachine` + bridge `Eval ↔ SemConsequences`
  (`RevHalt/Theory/ThreeBlocksArchitecture.lean`).
- **Dynamique abstraite** : `PickWorld`, chaînes/limites, `omegaState`
  (`RevHalt/Theory/AbstractDynamics.lean`).
- **Frontière ordinale / EM** : la caractérisation `dichotomy_all_iff_em`
  (`RevHalt/Theory/OrdinalBoundary.lean`).

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

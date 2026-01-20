# RevHalt — Reste à faire (pousser la théorie, pas du polish)

Objectif: transformer le “pipeline” actuel (dynamics + canonization + instances) en résultats plus robustes, mieux classifiés (constructif vs classique), et moins dépendants d’artefacts (choix de `K`, `Cn`, encodages, checkers WC).

Références existantes:
- Axiomes (mécanique): `RevHalt/Diagnostics/AxiomsReport.lean`
- Classification actuelle: `docs/Axiom_Dependence_Report.md`

---

## 0) Conditions pour que l’apport soit “majeur”

Le code donne déjà un pont formel du type:
`(Stabilité au bord) + (Price of P) -> Collapse` et donc une contraposée du type
`¬Collapse -> (¬Stabilité) ∨ (¬Price of P)`.

Pour que ça soit perçu comme un “grand apport” (pas juste intéressant), il faut bétonner:
- (A) **Non‑trivialité de Price of P**: montrer que `PolyCompressionWC` n’est pas une hypothèse déguisée de collapse.
- (B) **Robustesse de Stabilité**: montrer que `S1Rel … ωΓ = ∅` et le pont vers collapse sont invariants sous des variations raisonnables (encodages/checkers/politiques/instances).

Ces deux axes sont développés dans les sections 3) et 4).

---

## 1) Dépendance aux axiomes (résultat théorique sur la force du cadre)

### 1.1 Étendre le rapport `#print axioms`
Ajouter au rapport (ou créer `RevHalt/Diagnostics/AxiomsReport_Extended.lean`) les theorems “centraux”:
- Escape / fork law:
  - `RevHalt.structural_escape_transfinite`
  - `RevHalt.structural_escape_at_limit`
  - `RevHalt.structural_escape_at_limit_L`
  - `RevHalt.fork_law_False`
  - `RevHalt.fork_law_not_ContinuousAtL`
- Jump:
  - `RevHalt.jump_fixpoint_from_continuity`
  - `RevHalt.limitIncludesStages_jumpLimitOp`
  - `RevHalt.not_JumpDiscontinuousAlong_frontier`
- TSP endpoints:
  - `RevHalt.TSP.Collapse_TSP_of_Stable_and_PriceOfP`
  - (et tout autre endpoint “final API” que tu veux mettre en avant)

### 1.2 Classifier “constructif vs classique” au niveau module
Produire une table “fichier -> dépendance” (pas une opinion, mais basée sur `#print axioms`):
- “constructif” = pas de `Classical.choice`
- “classique” = `Classical.choice` apparaît
- noter aussi `Lean.trustCompiler` / `Lean.ofReduceBool` quand ils apparaissent (c’est important pour les couches WC/checkers).

Livrable: un doc “module map” (ex: `docs/Axiom_Map.md`) qui liste les modules et les résultats qu’ils portent, avec leur classe.

---

## 2) Réduire le “classical” quand c’est évitable (gains réels)

### 2.1 Supprimer les classiques purement “Set.Nonempty”
Pattern déjà appliqué (à répéter ailleurs):
- remplacer `by_contra h; have : s.Nonempty := Set.nonempty_iff_ne_empty.mpr h` par
  `apply Set.eq_empty_iff_forall_notMem.mpr; intro p hp; ...`

Cibles évidentes:
- occurrences de `Set.nonempty_iff_ne_empty` et `Set.not_nonempty_iff_eq_empty` dans le cœur (route II / transfinite / instances).

### 2.2 Isoler le vrai point dur: `Classical.decPred`
Là où la théorie force vraiment une décision de “Provable Δ p”:
- `RevHalt/Theory/TheoryDynamics_TwoSided.lean`:
  - garder la version constructive `F0_pm_monotone_of_provClosed` (déjà paramétrée par `DecidablePred`)
  - faire de la version classique `F0_pm_monotone_classical` une “instance séparée” (déjà le cas), et tracer précisément où elle est utilisée.

But: rendre explicite “ce que coûte” la version functorielle globale (sans hypothèse de décidabilité).

---

## 3) Non‑trivialité / statut mathématique de “Price of P” (PolyCompressionWC)

Point à clarifier dans Lean: où se situe l’hypothèse `PolyCompressionWC` par rapport à des notions standard.

### 3.0 Résultats “non‑tautologie” déjà formalisés
Fichier: `RevHalt/Theory/TheoryDynamics_PriceOfP_Nontriviality.lean`

Ce fichier verrouille le point suivant, au niveau des signatures Lean (pas en prose):
- `RevHalt.CanonizationWC.polyCompressionWC_of_no_provable`:
  si `ProvableWC Γ p` est faux pour tout `p`, alors `PolyCompressionWC Γ size` est habité (vacuement).
  Donc `PolyCompressionWC` seul n’implique pas “vérité -> preuve”, ni un collapse.
- `RevHalt.CanonizationWC.not_PosCompleteWC_of_no_provable`:
  si rien n’est WC‑provable mais qu’il existe un `p0` vrai, alors `PosCompleteWC` est impossible.
  Ça sépare formellement “Price of P” (compression de preuves) de “complétude positive”.
- `RevHalt.CanonizationWC.no_polyCompressionWC_size0`:
  exemple concret d’un système où **tout** est WC‑provable mais où `PolyCompressionWC` est impossible
  si la mesure de taille est constante (`size0`).
  Donc `PolyCompressionWC` n’est pas une tautologie: c’est une vraie hypothèse de compression.

### 3.1 Montrer des implications “sens standard -> Price of P”
Écrire des lemmes du type:
- “si on a une procédure polynomiale X, alors on obtient une borne polynomiale sur les WC-derivations”.

Idée (structure, pas slogan):
- définir un pont “algorithme” -> “derivation checker + witness checker” -> “existence d’un code borné”.
- isoler l’endroit exact où la majoration polynomiale est supposée.

### 3.2 Tester la robustesse de la définition de Price of P
Montrer des invariances internes:
- changer `encodeList/decodeList` par une équivalence -> `PolyCompressionWC` équivalent (ou au moins une implication dans un sens).
- changer `ChecksWitness` par une variante extensionnelle -> `PolyCompressionWC` stable.

But: que l’hypothèse ne soit pas “fragile” au niveau du choix des codes.

---

## 4) Robustesse de “Stabilité” (S1Rel vide à omega) et du pont vers Collapse

### 4.1 Paramétrer et factoriser au maximum
Objectif: pouvoir dire “le pipeline marche pour une classe d’instances”, pas seulement TSP.

Travail Lean:
- extraire une interface “InstanceWC” minimale:
  - type `PropT`, machine, encode_halt, notion `IsTrue`, `ChecksDerivation`, `ChecksWitness`, taille `size`
  - et prouver une version générique du endpoint “Stable + Price -> Collapse” (si ce n’est pas déjà le bon niveau d’abstraction).

### 4.2 Ajouter une 2e instance (SAT/3SAT/CLIQUE)
But: démontrer que la chaîne n’est pas spécifique à TSP.

Livrable: un fichier `RevHalt/Theory/Instances/<NPcomplete>_Canonization.lean` qui réutilise exactement le même schéma que TSP.

---

## 5) Consolider les “résultats noyau” (ceux qui valent publication)

À isoler comme objets centraux (avec noms stables + signatures propres):
- “Bridge”: `Stable + Price -> Collapse` (au bon niveau d’abstraction)
- “Fork law”: `FixpointFromContinuity -> ¬ ContinuousAtL` sous hypothèses d’escape
- “Jump separation”: résultats qui montrent que “union-only” écrase une différence (via `jumpLimitOp`)

Pour chacun:
- décider un théorème “flagship” (le plus court possible)
- lister explicitement ses hypothèses (pas de meta-texte)
- lister `#print axioms` et la classe (constructif/classique)

---

## 6) Commandes utiles (répétables)

- Build ciblé:
  - `lake build RevHalt.Diagnostics.AxiomsReport`
  - `lake build RevHalt.Theory.Instances.TSP_Dynamics`
  - `lake build RevHalt.Theory.Instances.TSP_Canonization`

- Scan des usages classiques:
  - `rg -n \"\\bclassical\\b|by_contra\\b|Classical\\.decPred\" RevHalt`

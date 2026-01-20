# Directives Lean (strict) : pas de `noncomputable`, pas de `Classical`

Ce document fixe des règles de développement strictes pour les parties du projet qui doivent rester constructives (au sens : ne pas dépendre de `Classical.*` dans `#print axioms`).

---

## 1) Interdictions (zéro tolérance)

- Pas de `noncomputable section`, `noncomputable def`, `by classical`, `open Classical`.
- Pas de `Classical.choice`, `Classical.decEq`, `Classical.propDecidable`, `Classical.byContradiction`.
- Pas de `by_contra` (sauf dans un fichier explicitement `*_Classical.lean`).
- Pas de `simp`/`aesop`/tactiques qui introduisent implicitement `Classical` (si `#print axioms` montre `Classical.choice`, c’est un échec).

---

## 2) Décidabilité : toujours explicite

Quand une preuve a besoin de “décider” un cas, on ne fait pas appel à `Classical` :

- Ajouter les paramètres nécessaires :
  - `DecidableEq α`
  - `DecidablePred P`
  - `Decidable (p = q)` / `Decidable (P x)`
- Faire les branches via :
  - `by_cases h : P x`
  - `by_cases h : x = y`
  - ou `match`/`cases` sur des booléens déjà calculables.

Règle : toute dépendance “décidable” doit apparaître dans la signature (hypothèses explicites), pas en global.

---

## 3) Extraction de témoins : pas de `choose`

Interdit :
- `Classical.choose`, `choose`, `by classical exact ...`

Autorisé (constructif) :
- `rcases h with ⟨w, hw⟩`
- `refine ⟨w, ?_⟩`
- `match h with | ⟨w, hw⟩ => ...`

Idée : on élimine un `∃` localement, on ne fabrique pas de fonction globale de choix.

---

## 4) Séparation “constructif vs classique”

- Toute preuve qui requiert réellement un principe classique (typ. transformer `¬(A ∧ B ∧ C)` en `A → B → ¬C` + disjonctions globales, ou faire une complétion non décidée) va dans un fichier `*_Classical.lean`.
- Le fichier constructif correspondant :
  - garde la version “négative” (ex: `¬ (A ∧ B ∧ C)`),
  - ou exige une décidabilité explicite en hypothèse (`..._of_decidable`).

Règle : les endpoints “flagship” doivent exister en double quand c’est pertinent :
- version `..._of_decidable` (constructive),
- version classique dans `*_Classical.lean` (assumant la décidabilité implicitement).

---

## 5) Vérification mécanique obligatoire

À chaque itération :

- Compiler :
  - `lake build`
- Vérifier la dépendance d’axiomes :
  - `lake build RevHalt.Diagnostics.AxiomsReport`
  - inspecter les lignes `depends on axioms:` pour les theorems ciblés

Critère de succès “constructif” :
- absence de `Classical.choice` dans `#print axioms` pour les résultats annoncés comme constructifs.

---

## 6) Conseils de refactor (patterns qui marchent)

- Remplacer “contradiction globale” par :
  - une preuve directe (`Nat.lt_of_lt_of_le`, `Nat.not_lt_of_ge`, etc.)
  - une analyse de cas explicitement décidée.
- Remplacer une “existence de complétion” implicite par :
  - un paramètre `Complete : ∀ p, HasSolution p → ∃ c, ...`
  - ou une structure de données qui transporte le témoin (proof-carrying).


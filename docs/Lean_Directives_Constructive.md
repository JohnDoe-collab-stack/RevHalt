# Directives Lean (constructif strict)

Objectif: isoler un noyau **constructif** (sans axiomes classiques) et ne mettre le classique que dans des modules explicitement marqués.

---

## 1) Règles non négociables (noyau constructif)

Dans tout fichier du noyau constructif:

- Interdit: `noncomputable`, `classical`, `open Classical`, `by_contra`.
- Interdit: `by_cases h : P` **si** `P` n’est pas décidable via une instance locale explicite.
- Interdit: introduire implicitement `Decidable` via `Classical.decPred` / `Classical.propDecidable` (même si ce n’est pas écrit).

Règle pratique: si tu veux un split sur un `Prop` non décidables “par nature”, tu dois **passer** une hypothèse de décidabilité et l’installer localement.

Exemple (pattern imposé):

```lean
(hDec : DecidablePred (fun p => ProvableWC … Γ p))
…
haveI : Decidable (ProvableWC … Γ p) := hDec p
by_cases hp : ProvableWC … Γ p
```

---

## 2) Organisation des modules (constructif vs classique)

- Tout argument classique doit aller dans un fichier suffixé `*_Classical.lean`.
- Un fichier `*_Classical.lean` peut utiliser `classical`/`by_contra`, mais doit le documenter en tête.
- Les modules “API endpoints” qui dépendent du classique importent explicitement `*_Classical.lean`.
- Les modules “noyau” (dynamics/transfinite/jump/proof complexity/canonization constructive) n’importent **jamais** de `*_Classical.lean`.

---

## 3) Directive objective A (très précise)

Pour “finir” l’objectif A:

- Pour chaque instance concrète `X` (ex: `TSP`, `ThreeSAT`, …), ajouter un module `RevHalt/Theory/Instances/X_ProofComplexity.lean` (constructif) qui expose un endpoint:
  - `PolyPosWC_X … -> RevHalt.ProofComplexity.PolynomiallyBoundedPPS …`
  - en instanciant `RevHalt.Theory.ProofComplexity.Correspondence` via des lemmes `IsTrue_X_of_ChecksWC` et `ChecksWC_complete_of_PolyPosWC_X`.
- Pousser la correspondance jusqu’aux objets “Price of P” du projet:
  - relier `PolyCompressionWC_X` à `PolyPosWC_X` (ou justifier formellement pourquoi on ne peut pas).
- Tout usage de raisonnement classique nécessaire à une étape “glue” (ex: `S1Rel = ∅` ⇒ complétude sans décidabilité) doit être déplacé dans `RevHalt/Theory/Instances/X_*_Classical.lean`.

---

## 4) Vérifications (avant de dire “OK”)

- Recherche interdits (noyau constructif):
  - `rg -n "\\b(noncomputable|classical|by_contra)\\b" <fichiers>`
- Vérification axiomatique:
  - utiliser `RevHalt/Diagnostics/AxiomsReport.lean` et vérifier que les lemmes “constructifs” n’introduisent pas `Classical.choice`.


# Objectif A (Price of P / non-tautologie) : reste à faire (directive opérationnelle)

Objectif A = rendre “Price of P” exploitable et non‑tautologique, en le reliant à des objets standard (proof complexity), puis pousser la chaîne jusqu’aux instances concrètes (`*_TSP`, `*_3SAT`) avec un contrôle strict des hypothèses classiques.

---

## 1) Étendre la correspondance jusqu’aux objets concrets du dépôt

Point de départ (déjà en place) :
- `RevHalt/Theory/ProofComplexity/Correspondence.lean`
  - `RevHalt.ProofComplexity.PolyPosWC_implies_PolyPPS`
  - `RevHalt.ProofComplexity.PolyPPS_implies_PolyPosWC`
- `RevHalt/Theory/Instances/TSP_ProofComplexity.lean`
  - `RevHalt.TSP.PolyPosWC_TSP_implies_PolyPPS`
- `RevHalt/Theory/Instances/ThreeSAT_ProofComplexity.lean`
  - `RevHalt.ThreeSATCanonization.PolyPosWC_3SAT_implies_PolyPPS`
- pont “stabilité/frontière vide + Price-of-P (TSP) ⇒ PolyPosWC_TSP” en version constructive (décidabilité explicite) :
  - `RevHalt/Theory/Instances/TSP_Canonization.lean`
    - `RevHalt.TSP.PolyPosWC_TSP_of_Stable_of_decidable`
- endpoint “objectif A” bout‑en‑bout (constructif, décidabilité explicite) :
  - `RevHalt/Theory/Instances/TSP_ProofComplexity.lean`
    - `RevHalt.TSP.PolyCompressionWC_TSP_of_Stable_of_decidable_implies_PolyPPS`

Ce qu’il reste à pousser :
- relier explicitement les hypothèses “dynamique/canonization WC” (ex: `PolyCompressionWC_*`, `PosCompleteWC_*`, stabilité/frontière vide, etc.) aux hypothèses “proof complexity” (`PolyPosWC_*`), au moins pour une instance (TSP) :
  - un lemme de forme : `(...hypothèse(s) Price-of-P localisées...) -> PolyPosWC_TSP ...`
  - puis composition avec `RevHalt.TSP.PolyPosWC_TSP_implies_PolyPPS`.

Critère : que l’objet standard obtenu (`PolynomiallyBoundedPPS`) soit atteignable depuis les API “framework” sans étape informelle.

---

## 2) Clarifier / réduire les hypothèses classiques (et les isoler)

But : que la partie “objectif A” soit au maximum constructive.

À faire :
- pour chaque endpoint “A” important, produire une variante constructive (si nécessaire en ajoutant des hypothèses de décidabilité) :
  - suffixe `..._of_decidable` dans le fichier constructif,
  - version sans décidabilité dans `*_Classical.lean`.
- maintenir un diagnostic mécanique dans `RevHalt/Diagnostics/AxiomsReport.lean` (ajouter les nouveaux endpoints à surveiller si besoin).

Critère : dans `RevHalt/Diagnostics/AxiomsReport.lean`, les endpoints annoncés constructifs ne doivent plus avoir `Classical.choice` dans `#print axioms`.

Note (état actuel, objectif A) :
- un diagnostic dédié existe : `RevHalt/Diagnostics/AxiomsReport_ObjA.lean`
- les endpoints “A” suivants sont censés être sans `Classical.choice` :
  - `RevHalt.TSP.PosCompleteWC_of_S1Rel_empty_TSP_of_decidable`
  - `RevHalt.TSP.PolyPosWC_TSP_of_Stable_of_decidable`

---

## 3) Positionner “Price of P” comme hypothèse non-tautologique

État (déjà présent) :
- `RevHalt/Theory/TheoryDynamics_PriceOfP_Nontriviality.lean`
- `RevHalt/Theory/ProofComplexity/Separation.lean`

Ce qu’il reste :
- expliciter une “thèse de naturalité” : montrer que `PolyCompressionWC` / `PolyPosWC` correspond (au moins dans une direction) à un principe standard identifié, et que l’implication vers “collapse” n’est pas une reformulation déguisée.
- idéalement : produire un résultat de séparation plus “invariant” (moins toy), en s’appuyant sur :
  - `RevHalt/Theory/StabilityInvariance.lean` (transfert de stabilité via réduction),
  - et les instances (TSP/3SAT) pour éviter un artefact de codage.

---

## 4) Checklist de validation

- Compilation : `lake build`.
- Diagnostic axiomes (global) : `lake build RevHalt.Diagnostics.AxiomsReport`.
- Diagnostic axiomes (objectif A) : `lake env lean RevHalt/Diagnostics/AxiomsReport_ObjA.lean`.
- Différences attendues :
  - baisse des dépendances `Classical.choice` sur les endpoints “A” annoncés constructifs,
  - et séparation claire des fichiers `*_Classical.lean`.

# Ce que le projet démontre (état actuel, affirmatif)

Ce document liste, de façon positive et vérifiable dans Lean, les résultats établis dans le dépôt (avec pointeurs vers les fichiers).

---

## 1) Correspondence “PolyPosWC ↔ PPS (Cook–Reckhow, version verificateur)”

Dans `RevHalt/Theory/ProofComplexity/Correspondence.lean`, le projet :

- définit un objet standard de complexité des preuves :
  - `RevHalt.ProofComplexity.PropositionalProofSystem`
  - `RevHalt.ProofComplexity.PolynomiallyBoundedPPS`
- construit un PPS canonique à partir d’un système WC via :
  - `RevHalt.ProofComplexity.toPPS`
- démontre les deux directions (à hypothèses explicites `hSound`/`hComplete`) :
  - `RevHalt.ProofComplexity.PolyPosWC_implies_PolyPPS`
  - `RevHalt.ProofComplexity.PolyPPS_implies_PolyPosWC`

Interprétation formelle : `PolyPosWC` est équivalent à “il existe des preuves (au sens PPS induit par `ChecksWC`) de taille polynomiale pour toutes les instances vraies”, avec une borne polynomiale explicite.

---

## 2) Instanciation concrète : TSP → PPS polynomialement borné (objectif A)

Dans `RevHalt/Theory/Instances/TSP_ProofComplexity.lean`, le projet :

- prouve la correction “checker WC ⇒ vérité” pour TSP :
  - `RevHalt.TSP.IsTrue_TSP_of_ChecksWC`
- extrait une complétude “vérité ⇒ existence d’un code accepté” à partir de `PolyPosWC_TSP` :
  - `RevHalt.TSP.ChecksWC_complete_of_PolyPosWC_TSP`
- construit le PPS induit par le checker (`ChecksWC`) :
  - `RevHalt.TSP.TSP_PPS`
- dérive l’endpoint concret :
  - `RevHalt.TSP.PolyPosWC_TSP_implies_PolyPPS`
- et, en composant la canonization (stabilité/frontière vide + Price-of-P localisé) avec la correspondance PPS :
  - `RevHalt.TSP.PolyCompressionWC_TSP_of_Stable_of_decidable_implies_PolyPPS`

Interprétation formelle : une hypothèse “preuves WC courtes pour tous les TSP vrais” entraîne l’existence d’un PPS polynomialement borné pour le vérificateur induit par le checker TSP.

---

## 3) Instanciation concrète : 3SAT → PPS polynomialement borné

Dans `RevHalt/Theory/Instances/ThreeSAT_ProofComplexity.lean`, le projet :

- prouve la correction “checker WC ⇒ vérité” pour 3SAT :
  - `RevHalt.ThreeSATCanonization.IsTrue_3SAT_of_ChecksWC`
- extrait la complétude depuis `PolyPosWC_3SAT` :
  - `RevHalt.ThreeSATCanonization.ChecksWC_complete_of_PolyPosWC_3SAT`
- construit le PPS induit :
  - `RevHalt.ThreeSATCanonization.SAT_PPS`
- dérive l’endpoint :
  - `RevHalt.ThreeSATCanonization.PolyPosWC_3SAT_implies_PolyPPS`
- et, désormais, ferme aussi l’endpoint end‑to‑end “stabilité + Price‑of‑P ⇒ PPS p‑borné” :
  - `RevHalt.ThreeSATCanonization.PolyCompressionWC_3SAT_of_Stable_of_decidable_implies_PolyPPS`

---

## 4) Bornes inférieures : formalisation et implications

Dans `RevHalt/Theory/ProofComplexity/LowerBounds.lean`, le projet :

- formalise la négation “super‑polynomial lower bound” de `PolyPosWC` :
  - `RevHalt.ProofComplexity.SuperPolyLowerBound`
- démontre la direction constructive :
  - `RevHalt.ProofComplexity.SuperPolyLowerBound.not_PolyPosWC`

Dans `RevHalt/Theory/ProofComplexity/LowerBounds_Classical.lean`, le projet :

- isole la direction réciproque (forme contraposée globale), dans un fichier explicitement classique :
  - `RevHalt.ProofComplexity.not_PolyPosWC_implies_LowerBound`

---

## 4.5 Outil de robustesse (thèse naturalité) : simulation PPS ⇒ transfert p‑borné

Dans `RevHalt/Theory/ProofComplexity/Simulation.lean`, le projet :

- formalise une notion de simulation polynomiale entre PPS (`PPSSimulates`) ;
- prouve le transfert générique :
  - `RevHalt.ProofComplexity.PolynomiallyBoundedPPS_of_simulation`.

Interprétation formelle : une fois qu’on a une traduction polynomiale des preuves préservant la vérification, la propriété “p‑borné” se transfère au système simulé ; c’est la brique de base pour rendre les endpoints Objectif A robustes aux encodages/systèmes de preuve.

---

## 5) “Price of P” : non‑tautologie et séparations formelles

Dans `RevHalt/Theory/TheoryDynamics_PriceOfP_Nontriviality.lean`, le projet :

- construit un modèle où `PolyCompressionWC` est satisfait vacuement si rien n’est provable :
  - `RevHalt.CanonizationWC.polyCompressionWC_of_no_provable`
- sépare formellement `PolyCompressionWC` et `PosCompleteWC` :
  - `RevHalt.CanonizationWC.not_PosCompleteWC_of_no_provable`
- donne un exemple simple où `PolyCompressionWC` échoue (selon une mesure de taille donnée) :
  - `RevHalt.CanonizationWC.no_polyCompressionWC_size0`

Dans `RevHalt/Theory/ProofComplexity/Separation.lean`, le projet :

- construit un modèle (toy system) où une hypothèse de type “Price of P” tient mais où le “Collapse” échoue :
  - `RevHalt.ProofComplexity.Separation.PriceOfP_does_not_imply_Collapse`

---

## 6) “Stabilité” : invariance sous réduction (début de robustesse)

Dans `RevHalt/Theory/StabilityInvariance.lean`, le projet :

- formalise une notion de réduction de systèmes (preservation halting + preservation provability) :
  - `RevHalt.ReducibleSystem`
- démontre un transfert de stabilité (frontière vide) le long d’une réduction :
  - `RevHalt.Stability_of_Reducible`

---

## 7) Split constructif / classique (canonization et endpoints)

Dans `RevHalt/Theory/Instances/TSP_Canonization.lean`, le projet :

- donne une version constructive de “S1Rel = ∅ ⇒ PosCompleteWC” en rendant explicite une hypothèse de décidabilité :
  - `RevHalt.TSP.PosCompleteWC_of_S1Rel_empty_TSP_of_decidable`
- donne une version constructive de la chaîne “stabilité (frontière vide) + Price-of-P (TSP) ⇒ PolyPosWC_TSP” (pont vers ProofComplexity) :
  - `RevHalt.TSP.PolyPosWC_TSP_of_Stable_of_decidable`

Dans `RevHalt/Theory/Instances/TSP_Canonization_Classical.lean`, le projet :

- isole le passage classique “S1Rel = ∅ ⇒ PosCompleteWC” sans décidabilité :
  - `RevHalt.TSP.PosCompleteWC_of_S1Rel_empty_TSP`
- ferme l’API classique “stabilité + Price of P ⇒ collapse (TSP)” :
  - `RevHalt.TSP.PolyPosWC_TSP_of_Stable`
  - `RevHalt.TSP.Collapse_TSP_of_Stable_and_PriceOfP`

---

## 8) Rapport mécanique de dépendance aux axiomes (diagnostic)

Dans `RevHalt/Diagnostics/AxiomsReport.lean`, le projet :

- produit des sorties `#print axioms` pour classer des résultats clés (constructif vs classique au sens “dépendance à `Classical.choice`”) :
  - trilemme (`omega_trilemma_*`), dynamique two‑sided (`F0_pm_monotone_*`),
    transfini (`continuous_implies_fixpoint_at_limit`), endpoints TSP, endpoints ProofComplexity.

---

## 9) Statut “résultat majeur” (évaluation technique actuelle)

Pas encore majeur : certains endpoints “flagship” (en particulier les versions “tout‑automatique” sans hypothèses de décidabilité explicites) restent dépendants de `Classical.choice` et/ou d’axiomes Lean (voir `RevHalt/Diagnostics/AxiomsReport.lean`).

En revanche, sur l’objectif A, il y a désormais une chaîne **sans `Classical.choice`** (au sens `#print axioms`) pour relier stabilité + Price‑of‑P (localisés) jusqu’à `PolyPosWC_TSP` via `..._of_decidable` (voir `RevHalt/Diagnostics/AxiomsReport_ObjA.lean`). Les dépendances résiduelles visibles côté TSP sont typiquement `propext` / `Quot.sound` (axiomes noyau/PropExt), pas du choix classique.

Pour 3SAT, l’endpoint end‑to‑end existe aussi, mais l’audit `#print axioms` montre qu’il dépend encore de `Classical.choice` (via `Machine_3SAT_halts_iff` et/ou les encodages auxiliaires), ce qui le classe actuellement dans la colonne “classique” du diagnostic.

Le point restant pour un “résultat majeur” est toujours la thèse nette de naturalité/robustesse : positionner `PolyCompressionWC`/`PolyPosWC` et la politique de limite par rapport à des objets standard (proof complexity / systèmes de preuve connus) sans tautologie et sans artefact d’encodage.

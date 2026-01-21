# Thèse de naturalité / robustesse (PolyCompressionWC, PolyPosWC, politiques de limite)

Objectif : formuler une thèse courte mais techniquement précise qui positionne `PolyCompressionWC` / `PolyPosWC` et les politiques de limite (`LimitOp`) par rapport à des objets standard (proof complexity / systèmes de preuve), et dire exactement quelles preuves Lean manquent pour éviter (i) la tautologie, (ii) l’artefact d’encodage.

Ce document ne “polish” rien : il fixe les critères d’un résultat majeur et les lemmes à obtenir.

---

## 1) Point d’ancrage standard déjà formalisé (le noyau “naturel”)

### 1.1 PolyPosWC est déjà relié à Cook–Reckhow (version “verifier”)

Dans `RevHalt/Theory/ProofComplexity/Correspondence.lean`, on a une correspondance explicite :

- Objet standard : `RevHalt.ProofComplexity.PropositionalProofSystem` + `RevHalt.ProofComplexity.PolynomiallyBoundedPPS`
- Construction canonique depuis WC : `RevHalt.ProofComplexity.toPPS`
- Équivalence :
  - `RevHalt.ProofComplexity.PolyPosWC_implies_PolyPPS`
  - `RevHalt.ProofComplexity.PolyPPS_implies_PolyPosWC`

Thèse “naturalité minimale” (déjà vraie dans Lean) :
`PolyPosWC` n’est pas un slogan interne ; c’est exactement “le PPS induit par le checker WC admet des preuves de taille polynomiale pour toutes les instances vraies”, sous hypothèses `sound/complete`.

### 1.2 “Price of P” n’est pas tautologique tout seul (séparations déjà en code)

Deux garde-fous existent déjà :

- `RevHalt/Theory/TheoryDynamics_PriceOfP_Nontriviality.lean` : `PolyCompressionWC` ne donne pas “Truth -> Provable” et peut échouer selon `size`.
- `RevHalt/Theory/ProofComplexity/Separation.lean` : `PriceOfP_does_not_imply_Collapse`.

Thèse “non-tautologie minimale” (déjà vraie dans Lean) :
`PolyCompressionWC` et “Collapse” sont séparables ; le pont vers un objet standard (PPS p-borné) dépend d’hypothèses explicites (complétude/stabilité) et n’est pas automatique.

---

## 2) La thèse de naturalité à rendre nette (ce qu’il faut pouvoir dire publiquement)

La thèse qu’on veut pouvoir écrire, en une phrase précise, est :

- “Dans RevHalt, `PolyPosWC` est équivalent à l’existence d’un PPS polynomialement borné (Cook–Reckhow) induit par `ChecksWC`; les endpoints (TSP/3SAT) produisent donc, sous hypothèses explicites (stabilité/frontière vide + Price-of-P), un objet standard de proof complexity.”

Ce n’est “majeur” que si on ajoute ensuite :

1) une robustesse d’encodage (le résultat ne dépend pas d’un choix fragile de `encodeList/decodeList`, de `WCCode`, ou d’une machine particulière),
2) une robustesse d’instance (TSP/3SAT ne sont pas des exceptions : on peut transférer l’hypothèse et/ou le résultat le long de réductions standard),
3) une robustesse de politique de limite (union vs cnUnion vs jump : ce qui change, et ce qui ne change pas, est explicitement prouvé).

---

## 3) Robustesse d’encodage (éviter “artefact de code”)

### 3.1 Cible : invariance de `PolyPosWC` et du PPS induit sous recodage polynomial

Problème à éviter :
si `PolyPosWC` dépend du détail “comment on encode les preuves/derivations”, alors le pont vers PPS est formel mais fragile.

Lemme-type à ajouter (au bon niveau d’abstraction, pas instance) :

- `PolyPosWC_invariant_under_poly_recode` :
  si on a deux checkers WC `(ChecksDerivation₁, ChecksWitness₁, decodeList₁, size₁)` et `(ChecksDerivation₂, ChecksWitness₂, decodeList₂, size₂)`
  reliés par des fonctions de traduction `enc/dec` et des bornes polynomiales (sur tailles + codes), alors
  `PolyPosWC Γ ...₁ ... -> PolyPosWC Γ ...₂ ...`.

Version “PPS standard” (souvent plus propre) :

- définir une notion de simulation entre PPS :
  - `PPS_Simulates(Sys1, Sys2)` = traduction des preuves `π2 -> π1` + préservation de l’acceptation + borne polynomiale sur `sizeProof`.
  - alors montrer : `PolynomiallyBoundedPPS Sys1 -> PolynomiallyBoundedPPS Sys2`.

Livrable Lean attendu :
un fichier `RevHalt/Theory/ProofComplexity/Simulation.lean` qui formalise une notion de simulation PPS et prouve un transfert générique “p-bounded -> p-bounded” le long d’une simulation polynomiale.

État actuel (déjà fait dans Lean) :
- `RevHalt/Theory/ProofComplexity/Simulation.lean` existe et fournit `RevHalt.ProofComplexity.PolynomiallyBoundedPPS_of_simulation`.
- Axiomes (vérification mécanique) : `RevHalt/Diagnostics/AxiomsReport_Simulation.lean` montre que
  `RevHalt.ProofComplexity.PolynomiallyBoundedPPS_of_simulation` ne dépend que de `[propext]`
  (pas de `Classical.choice`, pas de `Quot.sound`).

### 3.2 Cible : “le pairing / decodeList” ne doit pas importer `Classical.choice` dans les endpoints annoncés constructifs

Ce n’est pas une question de style : si un recodage force `Classical.choice`, on casse la classification “constructif” (cf. `docs/Lean_Directives_NoClassical.md`).

Livrable Lean attendu :
pour chaque instance flagship (TSP, 3SAT, …), isoler :
- une version `*_of_decidable` (constructive) où les encodages/roundtrips n’introduisent pas `Classical.choice` dans `#print axioms`,
- une version classique dans `*_Classical.lean` si nécessaire.

État actuel (déjà fait au niveau du noyau “IsPoly/Simulation”) :
- `RevHalt.Complexity.IsPoly.comp` est désormais axiomatiquement “propre” (seulement `[propext]`), cf.
  `RevHalt/Diagnostics/AxiomsReport_IsPolyCompDetail.lean`.
- Cela verrouille la partie la plus fragile : la composition de bornes polynomiales, utilisée pour
  propager “p-boundedness” le long d’une simulation.
- Côté instances, le pont “Price-of-P (version Pos/WC) -> objet standard (PPS p-borné)” est aussi
  axiomatiquement propre :
  `RevHalt/Diagnostics/AxiomsReport_ObjA.lean` montre que `RevHalt.TSP.PolyPosWC_TSP_implies_PolyPPS`
  et `RevHalt.ThreeSATCanonization.PolyPosWC_3SAT_implies_PolyPPS` ne dépendent que de `[propext]`.

---

## 4) Robustesse d’instance (éviter “artefact TSP-only / 3SAT-only”)

### 4.1 Cible : transfert des hypothèses et/ou des résultats le long de réductions standard

Il existe déjà une brique côté stabilité :

- `RevHalt/Theory/StabilityInvariance.lean` : `RevHalt.Stability_of_Reducible`.

À compléter pour l’objectif A :

1) Invariance de “complétude positive” (ou du moins transfert de `ChecksWC_complete`) le long d’une réduction,
2) Invariance de `PolyPosWC` sous réduction (avec contrôle polynomial explicite),
3) Transfert de “PPS p-borné” sous réduction / simulation.

Lemme-type (niveau “langages / instances”) :

- si `L1` many-one réduit à `L2` par une réduction dont la correction est internalisable (au niveau `IsTrue` + `ChecksWC_complete` + tailles),
  alors : `PolyPosWC_L2 -> PolyPosWC_L1`.

Pourquoi c’est la bonne forme :
ça transforme “Price-of-P sur TSP” en “Price-of-P sur toute NP-complete instance”, et inversement, donc on sort du “demo sur un jouet”.

Livrables Lean attendus :
- une structure `PolyReduction` (réduction + bornes polynomiales sur tailles et preuves),
- un théorème `PolyPosWC_of_PolyPosWC_under_PolyReduction`,
- (optionnel) un corollaire concret : `PolyPosWC_TSP <-> PolyPosWC_3SAT` sous une réduction concrète, dans un fichier `RevHalt/Theory/Instances/NPComplete_Reductions.lean`.

### 4.2 Cible : plusieurs endpoints concrets, pas un seul

Critère simple “robustesse” :
avoir au moins 2–3 instances NP-complètes, toutes reliées au même objet standard (PPS) avec les mêmes hypothèses, et un transfert (réduction/simulation) entre elles.

---

## 5) Robustesse de politique de limite (union vs cnUnion vs jump)

Point RevHalt spécifique :
les candidats-limites et les obligations de continuité/fixpoint dépendent d’un choix explicite `LimitOp` (`unionLimitOp`, `cnUnionLimitOp`, `jumpLimitOp`, …).

La thèse à rendre nette ici est :

- “Le pont dynamique ‘stabilité + Price-of-P -> PolyPosWC -> PPS p-borné’ se formule à un niveau où la politique de limite est un paramètre, et on sait exactement quelles étapes utilisent l’union (ou la clôture) et lesquelles sont policy-agnostic.”

Livrable Lean attendu :
- une version paramétrée des endpoints “A” où `L : LimitOp` est un paramètre explicite,
- et un tableau “policy -> hypothèses supplémentaires” (ex : inclusion des stades, existence du fixpoint depuis continuité, etc.).

---

## 6) Checklist “pas de tautologie / pas d’artefact” (ce qu’il faut pouvoir démontrer)

Pour revendiquer un résultat majeur, il faut pouvoir pointer des théorèmes Lean (pas du texte) pour :

1) Non-tautologie :
   - `PriceOfP_does_not_imply_Collapse` (déjà)
   - + un résultat “invariant” (pas toy) : par ex. transfert via `ReducibleSystem` ou via `PPS_Simulates`.
2) Naturalité :
   - correspondance `PolyPosWC ↔ PolynomiallyBoundedPPS` (déjà)
   - + simulation PPS : “votre PPS est polynomialement simulable par un système standard choisi” (EF/Frege, ou un PPS canonique de la littérature).
3) Robustesse d’encodage :
   - invariance de `PolyPosWC` sous recodage polynomial,
   - invariance de “p-bounded PPS” sous simulation polynomiale.
4) Robustesse d’instance :
   - transfert de `PolyPosWC` et/ou `PolyPPS` le long d’une réduction standard entre instances.

---

## 7) Où cela vit dans le dépôt (pointeurs)

- Correspondance standard : `RevHalt/Theory/ProofComplexity/Correspondence.lean`
- Séparation (non-tautologie) : `RevHalt/Theory/ProofComplexity/Separation.lean`
- Invariance stabilité : `RevHalt/Theory/StabilityInvariance.lean`
- Canonization WC (définitions Price-of-P) : `RevHalt/Theory/TheoryDynamics_CanonizationWC.lean`
- Instances endpoints :
  - TSP : `RevHalt/Theory/Instances/TSP_ProofComplexity.lean`
  - 3SAT : `RevHalt/Theory/Instances/ThreeSAT_ProofComplexity.lean`

# Directive Objectif A (Price of P) : correspondance + instanciation (profil constructif)

But: “finir l’objectif A” au niveau Lean, c’est-à-dire (i) pousser la correspondance `PolyPosWC` ↔ PPS jusqu’aux objets concrets (`PolyCompressionWC_TSP`, `PolyPosWC_TSP`, etc.), et (ii) isoler / éliminer les dépendances classiques là où c’est possible, **sans** introduire `noncomputable` ni `classical`.

Cette directive est volontairement opérationnelle (fichiers, noms, étapes, checks).

---

## 0) Contrainte globale (à respecter partout)

Appliquer `docs/Directives_Constructives.md` (zéro `noncomputable`, zéro `classical`).

Commande “stop” avant toute PR:

```sh
rg -n "\\bnoncomputable\\b|\\bclassical\\b|by_contra\\b|Classical\\.(choice|decPred|propDecidable)" RevHalt
```

---

## 1) Cible “Correspondence” sur TSP (instanciation)

### 1.1 Nouveau fichier d’endpoint (recommandé)

Créer un fichier dédié (ne pas polluer `TSP_Canonization.lean`) :

- `RevHalt/Theory/Instances/TSP_ProofComplexity.lean`

Imports minimaux:

- `RevHalt.Theory.ProofComplexity.Correspondence`
- `RevHalt.Theory.Instances.TSP_Canonization`

### 1.2 Objet à construire

Dans `RevHalt/Theory/ProofComplexity/Correspondence.lean`, la construction est:

- `RevHalt.ProofComplexity.toPPS`
- `RevHalt.ProofComplexity.PolyPosWC_implies_PolyPPS`
- `RevHalt.ProofComplexity.PolyPPS_implies_PolyPosWC`

Objectif TSP:

1) Définir un “PPS TSP” via `toPPS` avec:
   - `PropT := ℕ`
   - `HasSolution := RevHalt.TSP.IsTrue_TSP`
   - `ChecksDerivation := (paramètre)` (même paramètre que dans `TSP_Canonization.lean`)
   - `ChecksWitness := RevHalt.TSP.ChecksWitness_TSP`
   - `decodeList := RevHalt.TSP.decodeList`
   - `Proof := WCCode` (déjà le choix fait dans `toPPS`)
   - `sizeProp := RevHalt.TSP.TSPSize`

2) Exposer un théorème “objet concret”:

- `PolyPosWC_TSP ChecksDerivation ωΓ -> PolynomiallyBoundedPPS (TSP_PPS ...) TSPSize`

Ce théorème doit être **constructif** (aucun `classical` nécessaire) parce que:
`PolyPosWC` fournit déjà une borne + un témoin (un `WCDerivation`) pour chaque instance vraie.

### 1.3 Hypothèses à fournir (soundness/complete) sans classique

`toPPS` demande deux hypothèses:

- `hSound : ∀ p, (∃ c, ChecksWC ... ωΓ p c) -> IsTrue_TSP p`
- `hComplete : ∀ p, IsTrue_TSP p -> ∃ c, ChecksWC ... ωΓ p c`

Construction attendue:

- `hComplete` se prouve **à partir** de `PosCompleteWC` ou de `PolyPosWC_TSP` lui-même:
  - `PolyPosWC_TSP` donne `∃ d : WCDerivation ..., d.code < B (...)` donc on récupère `∃ c, ChecksWC ... = true`.

- `hSound` doit être un lemme de correction des checkers:
  - si `ChecksWC` accepte, alors le couple (preuve, témoin) encode bien une solution TSP.
  - si ce lemme n’existe pas encore, l’ajouter côté TSP “checker correctness” (dans `RevHalt/Theory/Instances/TSP.lean` ou un fichier `TSP_CheckerSoundness.lean`).
  - important: rester Bool->Prop via le contenu de `ChecksWitness_TSP` (pas de “choix”).

### 1.4 Vérif de succès

Build ciblé:

```sh
lake build RevHalt.Theory.Instances.TSP_ProofComplexity
```

Puis vérifier les axiomes:

- ajouter le théorème endpoint à `RevHalt/Diagnostics/AxiomsReport.lean`
- lancer:

```sh
lake env lean RevHalt/Diagnostics/AxiomsReport.lean
```

Critère: pas de `Classical.choice`.

---

## 2) Chaîne “PolyCompressionWC_TSP -> PolyPosWC_TSP -> PolyPPS” (objectif A complet)

Le projet a déjà:

- `RevHalt/Theory/Instances/TSP_Canonization.lean`
  - `PolyCompressionWC_TSP`
  - `PolyPosWC_TSP_of_Stable` (actuellement via une étape classique)
  - `Collapse_TSP_of_Stable_and_PriceOfP`

Directive:

1) Ne pas toucher à `Collapse_*` pour l’instant.
2) Produire une chaîne “proof complexity” **indépendante** du collapse:

- `PolyCompressionWC_TSP` + (un `PosCompleteWC` explicite, ou une version constructive de “stabilité -> PosCompleteWC”) -> `PolyPosWC_TSP`
- puis `PolyPosWC_TSP -> PolynomiallyBoundedPPS` (via §1)

Résultat: “Price of P” pour TSP est relié à un objet standard de proof complexity, sans parler de P=NP.

---

## 3) Réduction du classique: isoler le seul point dur (stabilité -> complétude)

### 3.1 Constat

Dans `RevHalt/Theory/Instances/TSP_Canonization.lean`, le théorème:

- `PosCompleteWC_of_S1Rel_empty_TSP`

utilise `classical` + `by_contra` pour passer de:

- `S1Rel ... ωΓ = ∅`

à:

- `PosCompleteWC ... ωΓ`

C’est un passage “non constructif” typique: on obtient `¬¬ Provable` mais pas un témoin.

### 3.2 Directive “constructive” minimale

Créer une variante **constructive** (sans `classical`) qui rend la décidabilité explicite:

- `PosCompleteWC_of_S1Rel_empty_TSP_of_decidable`

Hypothèse additionnelle obligatoire:

- `decProv : DecidablePred (Provable_TSP_WC (ChecksDerivation := ChecksDerivation) ωΓ)`

Idée:

- faire `by_cases hP : Provable_TSP_WC ... ωΓ p` (justifié par `decProv p`)
- cas `hP = true`: on a le témoin, fini
- cas `hP = false`: on construit `p ∈ S1Rel ... ωΓ`, contradiction avec `S1Rel = ∅`

Cette variante est constructive parce qu’on n’élimine pas une double négation sans décidabilité.

### 3.3 Politique sur l’ancienne version classique

Option recommandée (hygiène):

- garder `PosCompleteWC_of_S1Rel_empty_TSP` mais la déplacer dans un fichier explicitement “classical”, par exemple:
  - `RevHalt/Theory/Instances/TSP_Canonization_Classical.lean`
  - et ne plus l’importer depuis le noyau.

Ainsi, la chaîne constructive garde une frontière nette.

---

## 4) Seuil de fin (Objectif A “clos”)

Objectif A est considéré “clos” quand:

1) `RevHalt/Theory/Instances/TSP_ProofComplexity.lean` existe et compile.
2) On a un endpoint explicite:
   - `PolyPosWC_TSP ... -> PolynomiallyBoundedPPS ...`
3) `PosCompleteWC_of_S1Rel_empty_TSP_of_decidable` existe (même si la version “sans decidability” reste classique et isolée).
4) `#print axioms` des endpoints “A” ne contient pas `Classical.choice`.


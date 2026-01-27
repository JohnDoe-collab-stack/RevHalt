# Plan d attaque robuste (RevHalt)

Ce document est un plan d attaque detaille pour transformer le projet
en un resultat complet, sans axiomes ni "sorry" restants dans les
instances Collatz et les ponts Route II/T2.

## 0) Objectif final (definition claire)

Objectif final: obtenir une preuve formelle complete (Lean) que
`CollatzDynamicPA.collatz_AB_indices_bounded` est derivable sans axiomes
externes non justifies. Concretement:

1) `ConcreteInstance : CollatzInstance` est construit sans `sorry` ni `axiom`.
2) `bridge_proof : PA_implies_RouteIIAt ...` est prouve sans axiomes ad hoc.
3) Les trois witnesses `witBC`, `witAC`, `witAB` sont construits.
4) `#print axioms` des theoremes clefs renvoie `[]`.

## 1) Etat actuel (factuel, sans jugement)

### 1.1 Ce qui est solide

- Logique generique du trilemme et extinction AB (fichier generique).
- Infrastructure "CofinalHorns*" et "Trilemma.lean".
- Theorie dynamique (TheoryDynamics*), y compris les versions transfinies.

### 1.2 Ce qui est encore hypothetique

**Instances/CollatzWitnesses.lean**
- `Provable`, `Cn`, `PAax`, `A0` sont `sorry`.
- Propriete structurelles: `hIdem`, `hProvCn`, `hMono`, `hCnExt` sont `sorry`.
- `SProvable_PA`, `SNot_PA`, `hSound_PA`, `hNegComp_PA`, `hBarrier_PA` sont `sorry`.
- Witnesses `witBC`, `witAC`, `witAB` sont `sorry`.

**Instances/CollatzBridge.lean**
- `encode_U`, `richness_bridge_axiom`, `hSound_U`, `hNegComp_U`, `f_U`, `hf_U`,
  `hsemidec_U` sont declares comme axiomes.
- Construction de `S_PA : ImpossibleSystem` utilise `sorry`.
**TheoryDynamics_RouteII.lean**
- `frontier_nonempty_of_route_II` contient un `sorry`.
- `frontier_empty_T2_full` contient un `sorry` (construction `total_constructive`).

## 2) Principe de travail

- Aucun "patch cosmetique". Chaque trou doit devenir un lemme/proof.
- Les hypotheses meta (PA soundness, neg completeness, etc.) doivent etre soit:
  a) prouvees dans Lean, soit
  b) isolees dans une structure d hypotheses explicites et justifiees.
- La structure de la preuve generique doit rester stable.
- Les modifications doivent etre minimales et localisees.

## 3) Cartographie des dependances (graphe mental)

1) `TheoryDynamics*` definit les objets de base:
   - `Provable`, `Cn`, `ThState`, `chainState`, `omegaGamma`, `RouteIIAt`, etc.

2) `Trilemma.lean` utilise `TheoryDynamics` pour formuler le trilemme.

3) `CofinalHornsSimple/PA` utilisent `Trilemma` pour donner les witnesses
   le long d une sous-suite definie par `times`.

4) `GenericExtinction.lean` assemble:
   - witnesses + monotonicite + pont PA -> RouteII
   - pour conclure `EventuallyNotAB`.

5) `CollatzDynamicPA.lean` applique a `sigmaOf`.

6) `Instances/ConcreteCollatz.lean` doit fournir une instance concrete
   a partir de `CollatzWitnesses` + `CollatzBridge`.

Conclusion: si `CollatzWitnesses` et `CollatzBridge` sont completes,
tout le reste se ferme automatiquement.

## 4) Plan d attaque detaille (phases et taches)

### Phase A - Inventaire et hygiene (1 jour)

**Objectif:** connaitre exactement tous les trous restants.

Taches:
1. Lister tous les `sorry` et `axiom` dans `RevHalt/Instances` et `RevHalt/Theory`.
   - Commande: `rg -n "sorry|axiom" RevHalt/Instances RevHalt/Theory`
2. Lister les theoremes clefs et verifier leurs axiomes:
   - `#print axioms` pour:
     - `Generic.eventuallyNotAB_of_instance`
     - `Trilemma.trilemma_not_all`
     - `TheoryDynamics_RouteII.frontier_nonempty_of_route_II`
     - `Instances.CollatzBridge.bridge_proof`
3. Creer un tableau "trous -> fichier -> dependants".

Livrables:
- Tableau des trous.
- Liste priorisee des trous critiques.

### Phase B - Definir la logique concrete (Provable, Cn, PAax) (2-5 jours)

**Objectif:** remplacer `Provable`, `Cn`, `PAax` par des definitions reelles.

Options possibles:
1. **Option minimaliste**: utiliser un `Provable` simplifie ou un noyau
   formel (ex: `Provable` comme relation axiomatique) mais sans `sorry`.
   - Avantage: rapide.
   - Inconvenient: resultats restent conditionnels.
2. **Option standard PA**: formaliser PA dans Lean (long).

Taches:
1. Fixer une option (decision ferme).
2. Definir:
   - `Provable : Set PropT -> PropT -> Prop`
   - `Cn : Set PropT -> Set PropT`
   - `PAax : Set PropT`
3. Prouver:
   - `hIdem : CnIdem Cn`
   - `hProvCn : ProvClosedCn Provable Cn`
   - `hMono : ProvRelMonotone Provable`
   - `hCnExt : CnExtensive Cn`
4. Construire un `A0 : ThState`.

Acceptance criteria:
- Aucun `sorry` dans `CollatzWitnesses` sur ces definitions.
- `#print axioms` ne montre rien pour ces preuves.

### Phase C - Route II sans trou (2-5 jours)

**Objectif:** fermer la Route II et ses dependances.

Sous-taches:
1. Completer `frontier_nonempty_of_route_II` dans `TheoryDynamics_RouteII.lean`.
   - Remplacer le `sorry` par une preuve ou une hypothese explicite
     dans une structure (ex: `RouteIIHyp`).
1.b Completer la preuve `frontier_empty_T2_full` (notamment `total_constructive`).
2. Re-ecrire `CollatzBridge.bridge_proof` pour:
   - Minimiser les axiomes.
   - Documenter chaque hypothese (soundness, negative completeness, barrier).
3. Decider si `richness_bridge_axiom` est un axiome ou un lemme prouve.
   - Si axiome: l isoler proprement (module `Assumptions`).
   - Si lemme: construire reduction formelle Collatz -> Universal.

Acceptance criteria:
- `bridge_proof` compile sans `axiom`.
- `frontier_nonempty_of_route_II` compile sans `sorry`.

### Phase D - Witnesses cofinaux (2-4 jours)

**Objectif:** construire `witBC`, `witAC`, `witAB` (PairPA).

Sous-taches:
1. Utiliser `CofinalHornsPA` pour transformer des hypotheses en witnesses.
2. Definir concretement la fonction `sigma` (si besoin) ou montrer
   l existence de witnesses sans sigma (via cofinality sur `chainState`).
3. Verifier les dependances:
   - `PairPA` = `Pair` + `PA_at`
   - `PA_at` doit etre prouve cofinalement (utiliser `PA_Eventually_of_exists`).

Acceptance criteria:
- `witBC/witAC/witAB` definis sans `sorry`.
- `#print axioms` pour `ConcreteInstance` est vide.

### Phase E - Integration finale (1-2 jours)

1. Construire `ConcreteInstance` sans axiomes.
2. Recompiler `CollatzDynamicPA.collatz_AB_indices_bounded`.
3. Lancer un audit final:
   - `rg "sorry|axiom" RevHalt/Instances RevHalt/Trilemma RevHalt/Theory`
   - `#print axioms` des theoremes finaux.

Livrables:
- Theoreme final sans axiomes.
- Rapport d axiomes vide.

## 5) Risques majeurs et contournements

1) **Formalisation PA trop lourde**
   - Contournement: isoler dans un module d hypotheses explicites.
2) **Route II depend de T2 complexe**
   - Contournement: factoriser dans un "axiom pack" propre.
3) **Bridge Collatz -> Universal**
   - Peut exiger un travail de reduction algorithmique lourd.
   - Contournement: declarer explicitement la reduction comme hypothese,
     et marquer la partie comme "conditional theorem".

## 6) Definition d un "resultat honneste"

Un resultat est dit "robuste" si:
- Les axiomes restants sont limites et **explicites**.
- Aucun `sorry` ne subsiste.
- Les hypotheses non prouvees sont regroupees dans une structure unique
  (ex: `CollatzAssumptions`) avec documentation.

## 7) Contenu du rapport final

1. Resume des preuves reelles.
2. Liste des hypotheses residuelles (si il en reste).
3. Preuve de l extinction AB pour `sigmaOf`.
4. Liste des theoremes clefs avec `#print axioms` vide.

## 8) Check-list rapide (a cocher)

- [ ] Aucun `sorry` dans `RevHalt/Instances`
- [ ] Aucun `axiom` dans `RevHalt/Instances`
- [ ] Route II sans `sorry`
- [ ] Witnesses BC/AC/AB construits
- [ ] `ConcreteInstance` sans axiomes
- [ ] `collatz_AB_indices_bounded` sans axiomes

## 9) Actions immediates proposees

1) Valider quelle option de formalisation PA est acceptable.
2) Fermer la Route II (ou isoler une structure d hypotheses explicites).
3) Construire les witnesses `witBC/AC/AB`.

Fin du plan.

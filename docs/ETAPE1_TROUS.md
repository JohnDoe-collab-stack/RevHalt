# Etape 1 - Inventaire strict des trous (sorry/axiom)

Ce document liste uniquement les **vrais trous de preuve** (sorry/axiom)
detectes dans le code Lean. Les commentaires ne sont pas comptabilises.

## 1) Resultat du scan (code reel)

Commandes utilisees:
- `rg -n "\bsorry\b" RevHalt/Instances RevHalt/Theory RevHalt/Trilemma`
- `rg -n "^\s*axiom\b" RevHalt/Instances RevHalt/Theory RevHalt/Trilemma`

**Resultat:** aucun `sorry` ni `axiom` **dans le code** des dossiers scannes.
Les seules occurrences sont dans des commentaires ou des `#print axioms`.

## 2) Ce qui reste "conditionnel" (mais sans `sorry/axiom`)

Les trous ont ete **deplaces en hypotheses explicites** (donnees) :

### RevHalt/Instances/CollatzWitnesses.lean

Le fichier ne contient pas de `sorry/axiom`, mais expose la structure:
`CollatzWitnessesData`, qui demande (entre autres):
- `Provable`, `Cn`, `PAax`, `A0`
- `hIdem`, `hProvCn`, `hMono`, `hCnExt`
- `SProvable_PA`, `SNot_PA`, `hSound_PA`, `hNegComp_PA`, `hBarrier_PA`
- `witBC`, `witAC`, `witAB`

### RevHalt/Instances/CollatzBridge.lean

Le fichier ne contient pas de `sorry/axiom`, mais expose:
`CollatzBridgeAssumptions`, qui demande (entre autres):
- `encode_U`
- `richness_bridge_axiom`
- `hSound_U`, `hNegComp_U`
- `f_U`, `hf_U`, `hsemidec_U`
- `S_PA_consistent`, `S_PA_absurd`
- (a ajouter) `hTotal_U` pour `frontier_empty_T2_full`

### RevHalt/Theory/TheoryDynamics_RouteII.lean

Les anciens `sorry` ont ete retires, mais les hypotheses sont
**fortes** (ex: `hBarrier` + `classical` => contradiction immediate).

## 3) Note importante

Il n y a plus de trous explicites (`sorry/axiom`), mais
la **partie concrete** reste conditionnelle tant que
`CollatzWitnessesData` et `CollatzBridgeAssumptions`
ne sont pas instancies par des definitions/proofs reelles.

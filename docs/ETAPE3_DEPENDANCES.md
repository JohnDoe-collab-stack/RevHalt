# Etape 3 - Dependances des trous (impact)

Ce document mappe chaque trou (sorry/axiom) vers les theoremes ou
modules qu il bloque directement.

## 1) Synthese rapide

- Les trous **Instances/** bloquent la construction de `ConcreteInstance`,
  donc l application Collatz finale.
- Les trous **RouteII** bloquent `Cycle.lean` et les lemmas de trajectoire.
- Les axiomes du pont **CollatzBridge** bloquent directement `bridge_proof`.

## 2) Tableau des dependances

| Trou (symbole) | Fichier | Type | Dependances directes | Impact |
|---|---|---|---|---|
| `Provable`, `Cn`, `PAax` | `RevHalt/Instances/CollatzWitnesses.lean` | sorry | `ConcreteInstance` | Instance concrete impossible |
| `hIdem`, `hProvCn`, `hMono`, `hCnExt` | `RevHalt/Instances/CollatzWitnesses.lean` | sorry | `ConcreteInstance` + `GenericExtinction` (via instance) | Extinction AB concrete impossible |
| `A0 : ThState` | `RevHalt/Instances/CollatzWitnesses.lean` | sorry | `ConcreteInstance` | Instance concrete impossible |
| `SProvable_PA`, `SNot_PA`, `hSound_PA`, `hNegComp_PA`, `hBarrier_PA` | `RevHalt/Instances/CollatzWitnesses.lean` | sorry | `CollatzBridge.bridge_proof` | Pont PA -> RouteII bloque |
| `witBC`, `witAC`, `witAB` | `RevHalt/Instances/CollatzWitnesses.lean` | sorry | `ConcreteInstance` + `GenericExtinction` (via instance) | Extinction AB concrete impossible |
| `encode_U` | `RevHalt/Instances/CollatzBridge.lean` | axiom | `bridge_proof` | Pont bloque |
| `richness_bridge_axiom` | `RevHalt/Instances/CollatzBridge.lean` | axiom | `bridge_proof` | Pont bloque |
| `hSound_U`, `hNegComp_U`, `f_U`, `hf_U`, `hsemidec_U` | `RevHalt/Instances/CollatzBridge.lean` | axiom | `bridge_proof` | Pont bloque |
| `S_PA.consistent`, `S_PA.absurd` | `RevHalt/Instances/CollatzBridge.lean` | sorry | `bridge_proof` | Pont bloque |
| `frontier_nonempty_of_route_II` | `RevHalt/Theory/TheoryDynamics_RouteII.lean` | sorry | `Trilemma/Cycle.lean`, `TheoryDynamics_Trajectory.lean` | Lemmes Route II incomplets |
| `total_constructive` dans `frontier_empty_T2_full` | `RevHalt/Theory/TheoryDynamics_RouteII.lean` | sorry | `CollatzBridge.bridge_proof` | Pont T2 bloque |

## 3) Graphe d impact (lecture rapide)

1. `TheoryDynamics_RouteII` trous -> `CollatzBridge.bridge_proof` + `Cycle.lean` + trajectoire.
2. `CollatzBridge` axiomes/sorry -> `ConcreteInstance` bloque.
3. `CollatzWitnesses` sorries -> `ConcreteInstance` bloque.
4. `ConcreteInstance` bloque -> pas de preuve concrete Collatz.


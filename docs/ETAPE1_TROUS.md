# Etape 1 - Inventaire strict des trous (sorry/axiom)

Ce document liste uniquement les vrais trous de preuve (sorry/axiom)
detectes dans le code Lean. Les commentaires ne sont pas comptabilises.

## 1) Instances (blocants)

### RevHalt/Instances/CollatzWitnesses.lean

- `Provable` : definition manquante (`sorry`)
- `Cn` : definition manquante (`sorry`)
- `PAax` : definition manquante (`sorry`)
- `hIdem` : preuve manquante (`sorry`)
- `hProvCn` : preuve manquante (`sorry`)
- `hMono` : preuve manquante (`sorry`)
- `hCnExt` : preuve manquante (`sorry`)
- `A0 : ThState` : construction manquante (`sorry`)
- `SProvable_PA` : definition manquante (`sorry`)
- `SNot_PA` : definition manquante (`sorry`)
- `hSound_PA` : preuve manquante (`sorry`)
- `hNegComp_PA` : preuve manquante (`sorry`)
- `hBarrier_PA` : preuve manquante (`sorry`)
- `witBC` : witness manquant (`sorry`)
- `witAC` : witness manquant (`sorry`)
- `witAB` : witness manquant (`sorry`)

### RevHalt/Instances/CollatzBridge.lean

**Axiomes declares**
- `encode_U : UCode → PropT`
- `richness_bridge_axiom`
- `hSound_U`
- `hNegComp_U`
- `f_U`
- `hf_U`
- `hsemidec_U`

**sorry**
- `S_PA.consistent := sorry`
- `S_PA.absurd := sorry`

## 2) Theory (Route II / T2)

### RevHalt/Theory/TheoryDynamics_RouteII.lean

- `frontier_nonempty_of_route_II` contient un `sorry`
- `frontier_empty_T2_full` contient un `sorry` (construction `total_constructive`)

## 3) Note importante

Tant que ces trous existent, toute instanciation Collatz reste conditionnelle.
La logique generique (Trilemma/GenericExtinction) est correcte, mais
la partie concrete est encore incomplete.


# Etape 2 - Verification des axiomes (resultats)

Commande executee:

```
lake env lean AxiomsCheck.lean
```

## Resultats (copie)

- `RevHalt.Trilemma.Generic.eventuallyNotAB_of_instance` depends on axioms:
  `[propext, Quot.sound]`
- `RevHalt.Trilemma.trilemma_not_all` depends on axioms:
  `[propext, Quot.sound]`
- `RevHalt.frontier_nonempty_of_route_II` depends on axioms:
  `[propext, sorryAx, Classical.choice, Quot.sound]`
- `RevHalt.Instances.bridge_proof` depends on axioms:
  `[propext, sorryAx, Classical.choice, Quot.sound,
    RevHalt.Instances.encode_U,
    RevHalt.Instances.f_U,
    RevHalt.Instances.hNegComp_U,
    RevHalt.Instances.hSound_U,
    RevHalt.Instances.hf_U,
    RevHalt.Instances.hsemidec_U,
    RevHalt.Instances.richness_bridge_axiom]`
- `RevHalt.Trilemma.App.collatz_AB_indices_bounded` depends on axioms:
  `[propext, Quot.sound]`
- `RevHalt.Instances.ConcreteInstance` depends on axioms:
  `[propext, sorryAx, Classical.choice, Quot.sound,
    RevHalt.Instances.encode_U,
    RevHalt.Instances.f_U,
    RevHalt.Instances.hNegComp_U,
    RevHalt.Instances.hSound_U,
    RevHalt.Instances.hf_U,
    RevHalt.Instances.hsemidec_U,
    RevHalt.Instances.richness_bridge_axiom]`

## Interpretation rapide

- `propext` et `Quot.sound` sont des axiomes systeme Lean (classiques).
- `sorryAx` montre des preuves inachevees.
- Les axiomes `encode_U`, `richness_bridge_axiom`, etc. bloquent le pont Collatz.


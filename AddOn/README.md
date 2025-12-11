# AddOn: Extension Modules

This folder contains **extension modules** that build on top of the core `RevHalt.lean`.

## Files

| File | Purpose |
|------|---------|
| `RevHaltInstances.lean` | Concrete models: RecursiveKit, PropLogic, ComputabilityModel |
| `OmegaRevHalt.lean` | Ω as a cut of H*, connection to T2 |
| `ChaitinOmega.lean` | Kolmogorov complexity K, Chaitin's bound |
| `ConcreteUniversalMachine.lean` | Concrete PrefixUniversalModel with explicit codes |
| `Profiles.lean` | Cut×Bit classification grid (pure abstract vocabulary) |
| `ProfilesOmega.lean` | Links profiles to Ω via Kolmogorov complexity K |
| `RevHaltDelta.lean` | Finite halting counters and DR0/DR1 theorems |

---

## Dependency Hierarchy

```
Level 0: RevHalt.lean (root)
      ↓
Level 1: RevHaltInstances.lean
      ↓
Level 2: OmegaRevHalt.lean
      ↓
Level 3: ChaitinOmega.lean
      ↓
Level 4: ConcreteUniversalMachine.lean, Profiles.lean
      ↓
Level 5: ProfilesOmega.lean
```

---

## Building

All files are in the Lake build path:

```bash
lake build AddOn
```

Or build specific modules:

```bash
lake build AddOn.ChaitinOmega
lake build AddOn.ProfilesOmega
```

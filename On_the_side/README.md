# On_the_side: Experimental Modules

This folder contains **experimental modules** that are not yet in the main build path.

## Current Status

The following files have been **promoted to the main directory**:

| File | Status | Notes |
|------|--------|-------|
| `RevHaltDelta.lean` | ⚠️ Still here | Needs promotion to main |
| `Profiles.lean` | ✅ Promoted | Now in root as `Profiles.lean` |
| `ProfilesOmega.lean` | ✅ Promoted | Now in root as `ProfilesOmega.lean` |

## Architecture

See the main `README.md` for the complete architecture.

The promoted files follow this hierarchy:

```
Profiles.lean          (Level 4: pure abstract vocabulary)
      ↑
ProfilesOmega.lean     (Level 5: connects profiles to K/Ω)
      ↑
ChaitinOmega.lean      (Level 2: K, OmegaPrefix, Chaitin bound)
OmegaRevHalt.lean      (Level 1: Ω as cut of H*)
```

## Building

Files in `On_the_side/` are not in the Lake build path. To compile manually:

```bash
lake env lean On_the_side/RevHaltDelta.lean
```

Promoted files can be built with Lake:

```bash
lake build Profiles ProfilesOmega
```

# RevHalt: Proof Map

This map links the main statements to their Lean proofs.

## Base layer

- Trace, Halts, up:
  `RevHalt/Base/Trace.lean`
- Reverse halting kit and detection condition:
  `RevHalt/Base/Kit.lean`

## T1: Canonicity

- `T1_traces` (kit collapses to halting):
  `RevHalt/Theory/Canonicity.lean`
- `T1_uniqueness` (two valid kits agree):
  `RevHalt/Theory/Canonicity.lean`

## T2: Impossibility

- `diagonal_bridge` (Kleene SRT bridge):
  `RevHalt/Theory/Impossibility.lean`
- `T2_impossibility` (no uniform internal predicate):
  `RevHalt/Theory/Impossibility.lean`

## T3: Complementarity

- S1/S3 definitions:
  `RevHalt/Theory/Complementarity.lean`
- `T3_weak_extension_explicit` (sound extension S3):
  `RevHalt/Theory/Complementarity.lean`
- `OraclePick` and `T3_oracle_extension_explicit`:
  `RevHalt/Theory/Complementarity.lean`
- `T3_strong` (many extensions from partitions):
  `RevHalt/Theory/Complementarity.lean`

## Structural dichotomy schema

- `StructuralDichotomy` structure:
  `RevHalt/Theory/StructuralDichotomy.lean`
- `ne_bot_imp_notnot_sig`, `sig_iff_ne_bot`:
  `RevHalt/Theory/StructuralDichotomy.lean`
- `traceSD` instantiation:
  `RevHalt/Theory/StructuralDichotomy.lean`

## Parametric dynamics (PickWorld)

- `PickWorld` structure and chain/limit:
  `RevHalt/Theory/AbstractDynamics.lean`
- `lim_schedule_free`, `lim_eq_omegaState`, `omegaState_minimal`:
  `RevHalt/Theory/AbstractDynamics.lean`

## Bridge to dynamics

- `pickWorldOfSDOracle`:
  `RevHalt/Theory/SD_Bridge.lean`


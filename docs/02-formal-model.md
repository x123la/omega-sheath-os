# OMEGA-SHEAF-OS Formal Model

## Scope
Layer A defines sections, restrictions, compatibility, merge witnesses, and obstruction witnesses.

## Core Contracts
- Runtime MUST order events by `(lamport,node_id,stream_id,event_id)`.
- Runtime MUST NOT certify merge results unless checker output versions match batch metadata.
- Checker output domain is exactly one of `MergeWitness` or `ObstructionWitness`.
- Checker/schema/predicate bindings are carried as explicit metadata and validated at certification boundaries.

## Objects
- `Event`, `GlobalMerge`, `Obstruction`, `SnapshotManifest`, `ReplayIncident`
- Predicate IDs:
  - `1000-1999`: ordering
  - `2000-2999`: dependency
  - `3000-3999`: overlap agreement
  - `4000-4999`: domain extension

## Soundness Intent
The formal checker semantics are represented in Lean at:
- `layers/lean4/Formal/OMEGA.lean`

Runtime conformance is enforced by data-contract checks and deterministic replay comparison.

# OMEGA-SHEAF-OS Runtime Design

## Actor Graph (spec target)
`InputSource -> IngressActor -> SequencerActor -> ReconcileCoordinator -> ReconcileWorkerPool -> CertificateActor/SnapshotActor/ReplayActor`.

## Implemented Reference Runtime
This repository includes:
- Rust reference microkernel + CLI in `crates/omega-core` and `crates/omega-cli`
- Elixir OTP actor skeleton in `layers/elixir/runtime`
- Zig systems-boundary library in `layers/zig/src/lib.zig`
- Futhark analytics kernels in `layers/futhark/kernels.fut`
- TLA+ protocol model in `layers/tla/OMEGA.tla`
- Nushell orchestration in `layers/nushell/pipeline.nu`

## Layer B Language Choice
- Layer B is implemented in Elixir/OTP to preserve actor/supervision semantics with easier installation on common systems.
- Pony remains available as a legacy reference in `layers/pony/runtime/main.pony`, but is not a strict build requirement.

## Implemented Runtime Guarantees
- Checker input/output are version-bound through `CheckerBinding` and validated before certification.
- Sequencing enforces duplicate rejection, per-stream lamport monotonicity, and dependency readiness.
- Reconcile batching is deterministic and timer/size driven in the Elixir coordinator.
- Certificate persistence writes append-only `cert.log`, `cert.idx`, and `cert.hash` files with hash-chain linkage.
- Snapshot/replay actors persist deterministic manifests and replay incidents.

## Determinism and Durability
- Event ordering is deterministic and independent of arrival time.
- `.omega` recovery truncates at first invalid frame boundary.
- Certificate log chaining uses `prev_cert_hash`.
- Replay emits mismatch incidents when expected and observed hashes diverge.

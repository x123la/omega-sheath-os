# OMEGA-SHEAF-OS

**State-of-the-Art Distributed Consistency Kernel & Truth Platform.**

OMEGA-SHEAF-OS is a high-integrity, formal-methods-backed distributed system designed to make consistency a chain of enforceable contracts. It integrates six layers of verification into a single, high-performance deterministic pipeline.

## 🏛 The World-Class Architecture

### 1. Hexagonal Verification Stack
The system is governed by a multi-layer logical gauntlet:
*   **Layer A (Lean 4)**: Mathematical proof of Lamport Monotonicity.
*   **Layer B (Elixir/OTP)**: Fault-tolerant actor runtime with BFT-ready quorum consensus.
*   **Layer C (Zig)**: Low-level systems boundary with zero-copy memory-mapped I/O.
*   **Layer D (Futhark)**: Data-parallel analytics using hardware-agnostic fixed-point arithmetic.
*   **Layer E (TLA+)**: Formal protocol model checking for safety and liveness invariants.
*   **Layer F (Nushell/React)**: High-fidelity orchestration and the **OC2 Command Center**.

### 2. Perfect Determinism
*   **Hardware Agnostic**: Replaced floating-point math with fixed-point `i32` logic, ensuring bit-for-bit identical results across Intel, ARM, and RISC-V architectures.
*   **Causal Integrity**: Enforces strict ordering using a canonical key `(lamport, node_id, stream_id, event_id)` ensuring arrival-time independence.

### 3. Cryptographic Rigor
*   **Rigid Binary Contracts**: Standardized on a strictly packed binary envelope for all certificates, eliminating the fragility of string-based serialization.
*   **BFT Quorum Finalization**: Moves beyond passive detection to active consensus, requiring a majority of Ed25519 signatures before a state is finalized.

### 4. Zero-Copy Performance
*   Uses `mmap` (memory mapping) in both Rust and Zig to map the `.omega` log directly into the CPU's address space, processing data at the speed of the hardware memory bus.

---

## 🖥 OMEGA Command Center (OC2)

Transform raw cryptographic truth into actionable intelligence with our Palantir-grade dashboard.

*   **Causal Sheaf Map**: Real-time D3.js visualization of the "Mental Map" of event dependencies.
*   **BFT Quorum Monitor**: Visual tracking of signature collection and finalization progress.
*   **Audit Scroll**: Merkle-chain explorer for inspecting the immutable lineage of verified certificates.

### Launch the Platform
```bash
# 1. Build the full stack
./scripts/build_all.sh

# 2. Start the Command Center
./scripts/start_command_center.sh

# 3. Access the UI
# Open http://localhost:4000
```

---

## 🛠 Command Reference (`omega` CLI)

| Command | Purpose |
|---|---|
| `omega ingest` | Validates `.omega` log integrity using zero-copy prefix recovery. |
| `omega reconcile` | Performs deterministic reconciliation with cross-batch dependency tracking. |
| `omega certify` | Generates signed binary envelopes with hash-chain linkage. |
| `omega explain` | Deconstructs and visualizes binary certificate data. |
| `omega doctor` | Comprehensive environment and toolchain health check. |

## 📊 Technical Specifications
*   **Hash Algorithm**: SHA-256 (Standardized across all layers).
*   **Signature Scheme**: Ed25519 (Deterministic identity).
*   **Data Model**: Canonical Ordering Key + Causal Deps + Payload Hash.
*   **Consensus**: N/N Quorum (Configurable for BFT thresholds).

## ⚖️ Mission Statement
OMEGA-SHEAF-OS exists to make distributed consistency a chain of enforceable contracts, not a convention. It provides the "Source of Truth" for systems where the cost of a consistency error is catastrophic.

**License**: Apache-2.0
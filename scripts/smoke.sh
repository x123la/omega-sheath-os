#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

./scripts/make_sample_log.sh examples/sample.omega

SMOKE_DIR="$(mktemp -d /tmp/omega-smoke.XXXXXX)"

cargo run -q -p omega-cli -- ingest --input examples/sample.omega > "$SMOKE_DIR/omega_ingest.json"
cargo run -q -p omega-cli -- generate-events --output "$SMOKE_DIR/events.json" --count 3 > "$SMOKE_DIR/omega_generate_events.json"
cargo run -q -p omega-cli -- reconcile --input "$SMOKE_DIR/events.json" --batch-id 1 --replay-seed 99 --output "$SMOKE_DIR/omega_reconcile.json" > "$SMOKE_DIR/omega_reconcile_stdout.json"
cargo run -q -p omega-cli -- certify --result "$SMOKE_DIR/omega_reconcile.json" --batch-id 1 --replay-seed 99 --schema-version 1 --output "$SMOKE_DIR/omega_cert.json" --cert-log "$SMOKE_DIR/omega_cert.log" > "$SMOKE_DIR/omega_certify.json"
cargo run -q -p omega-cli -- explain --input "$SMOKE_DIR/omega_cert.json" > "$SMOKE_DIR/omega_explain.json"
cargo run -q -p omega-cli -- doctor --root . > "$SMOKE_DIR/omega_doctor.json" || true

echo "smoke artifacts:"
ls -1 "$SMOKE_DIR/omega_ingest.json" "$SMOKE_DIR/omega_reconcile.json" "$SMOKE_DIR/omega_cert.json" "$SMOKE_DIR/omega_explain.json" "$SMOKE_DIR/omega_doctor.json"

#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

echo "[omega] starting command center..."
echo "[omega] api and ui will be available at http://localhost:4000"

cd layers/elixir/runtime
export OMEGA_BATCH_SIZE=5
export OMEGA_FLUSH_MS=1000
mix run --no-halt

#!/usr/bin/env bash
set -euo pipefail

required=(
  "layers/lean4/Formal/OMEGA.lean"
  "layers/elixir/runtime/mix.exs"
  "layers/elixir/runtime/lib/omega_runtime/application.ex"
  "layers/zig/src/lib.zig"
  "layers/futhark/kernels.fut"
  "layers/tla/OMEGA.tla"
  "layers/nushell/pipeline.nu"
  "schemas/certificate.schema.json"
  "schemas/event.schema.json"
)

for file in "${required[@]}"; do
  [[ -f "$file" ]] || { echo "missing required file: $file"; exit 1; }
done

echo "architecture files present"

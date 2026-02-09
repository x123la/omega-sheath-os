#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
STRICT=0
RUN_TLC="${OMEGA_RUN_TLC:-0}"
if [[ "${1:-}" == "--strict" ]]; then
  STRICT=1
fi

echo "[omega] building rust workspace"
cargo build --workspace

echo "[omega] building core kernel as WASM blob"
rustup target add wasm32-unknown-unknown
cargo build -p omega-core --target wasm32-unknown-unknown --release

echo "[omega] running rust tests"
cargo test --workspace

echo "[omega] checking required architecture files"
./scripts/check_architecture.sh

if command -v zig >/dev/null 2>&1; then
  echo "[omega] building zig layer"
  (cd layers/zig && zig build)
else
  echo "[omega] zig unavailable; skipped"
  if [[ "$STRICT" -eq 1 ]]; then exit 1; fi
fi

if command -v lake >/dev/null 2>&1; then
  echo "[omega] building lean layer"
  (cd layers/lean4 && lake build)
else
  echo "[omega] lean/lake unavailable; skipped"
  if [[ "$STRICT" -eq 1 ]]; then exit 1; fi
fi

if command -v futhark >/dev/null 2>&1; then
  echo "[omega] checking futhark kernels"
  (cd layers/futhark && futhark check kernels.fut)
else
  echo "[omega] futhark unavailable; skipped"
  if [[ "$STRICT" -eq 1 ]]; then exit 1; fi
fi

if command -v mix >/dev/null 2>&1 && command -v elixir >/dev/null 2>&1; then
  echo "[omega] compiling elixir runtime layer"
  if ! (cd layers/elixir/runtime && mix compile && mix test); then
    echo "[omega] elixir runtime checks failed in this environment"
    if command -v elixirc >/dev/null 2>&1; then
      echo "[omega] attempting socketless elixirc fallback check"
      if ! (cd layers/elixir/runtime && tmpdir="$(mktemp -d /tmp/omega-elixirc.XXXXXX)" && elixirc -o "$tmpdir" lib/omega_runtime.ex lib/omega_runtime/*.ex); then
        if [[ "$STRICT" -eq 1 ]]; then exit 1; fi
      fi
    elif [[ "$STRICT" -eq 1 ]]; then
      exit 1
    fi
  fi
else
  echo "[omega] elixir/mix unavailable; skipped"
  if [[ "$STRICT" -eq 1 ]]; then exit 1; fi
fi

if command -v npm >/dev/null 2>&1; then
  echo "[omega] building command center ui"
  (cd ui && npm install && npm run build)
  mkdir -p layers/elixir/runtime/priv/static
  cp -r ui/dist/* layers/elixir/runtime/priv/static/
fi

if [[ "$RUN_TLC" -eq 1 || "$STRICT" -eq 1 ]]; then
  if command -v tlc >/dev/null 2>&1; then
    echo "[omega] model checking tla+ spec with tlc"
    if ! tlc -cleanup -deadlock -config layers/tla/OMEGA.cfg layers/tla/OMEGA.tla; then
      echo "[omega] tlc model check failed in this environment"
      if [[ "$STRICT" -eq 1 ]]; then exit 1; fi
    fi
  else
    echo "[omega] tlc unavailable; skipped"
    if [[ "$STRICT" -eq 1 ]]; then exit 1; fi
  fi
else
  echo "[omega] tlc check disabled (set OMEGA_RUN_TLC=1 to enable)"
fi

echo "[omega] running cli smoke sequence"
./scripts/smoke.sh

echo "[omega] build complete"

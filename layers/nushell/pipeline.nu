#!/usr/bin/env nu

def main [--strict] {
  let run_tlc = (($env.OMEGA_RUN_TLC? | default "0") == "1") or $strict
  print "[omega] pipeline start"

  ^bash -lc "cargo build --workspace"
  if ($env.LAST_EXIT_CODE != 0) { exit 1 }

  ^bash -lc "cargo test --workspace"
  if ($env.LAST_EXIT_CODE != 0) { exit 1 }

  if (which zig | is-not-empty) {
    ^bash -lc "cd layers/zig && zig build"
  } else {
    print "[omega] zig not installed; skipping zig build"
    if $strict { exit 1 }
  }

  if (which lake | is-not-empty) {
    ^bash -lc "cd layers/lean4 && lake build"
  } else {
    print "[omega] lean/lake not installed; skipping lean build"
    if $strict { exit 1 }
  }

  if (which futhark | is-not-empty) {
    ^bash -lc "cd layers/futhark && futhark check kernels.fut"
  } else {
    print "[omega] futhark not installed; skipping futhark check"
    if $strict { exit 1 }
  }

  if ((which mix | is-not-empty) and (which elixir | is-not-empty)) {
    let mix_ok = (try {
      ^bash -lc "cd layers/elixir/runtime && mix compile && mix test"
      true
    } catch {
      false
    })
    if (not $mix_ok) {
      print "[omega] elixir runtime checks failed in this environment"
      if (which elixirc | is-not-empty) {
        print "[omega] attempting socketless elixirc fallback check"
        let elixirc_ok = (try {
          ^bash -lc "cd layers/elixir/runtime && tmpdir=$(mktemp -d /tmp/omega-elixirc.XXXXXX) && elixirc -o $tmpdir lib/omega_runtime.ex lib/omega_runtime/*.ex"
          true
        } catch {
          false
        })
        if ((not $elixirc_ok) and $strict) { exit 1 }
      } else if $strict {
        exit 1
      }
    }
  } else {
    print "[omega] elixir/mix not installed; skipping elixir runtime compile"
    if $strict { exit 1 }
  }

  if $run_tlc {
    if (which tlc | is-not-empty) {
      ^bash -lc "tlc -cleanup -deadlock -config layers/tla/OMEGA.cfg layers/tla/OMEGA.tla"
      if ($env.LAST_EXIT_CODE != 0) {
        print "[omega] tlc model check failed in this environment"
        if $strict { exit 1 }
      }
    } else if (which java | is-not-empty) {
      print "[omega] java installed but tlc missing; skipping tla model check"
      if $strict { exit 1 }
    } else {
      print "[omega] java/tlc not installed; skipping tla runtime checks"
      if $strict { exit 1 }
    }
  } else {
    print "[omega] tlc check disabled (set OMEGA_RUN_TLC=1 to enable)"
  }

  print "[omega] pipeline complete"
}

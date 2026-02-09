import Lake
open Lake DSL

package "omega_formal" where
  version := v!"0.1.0"

lean_lib Formal where
  roots := #[`Formal.OMEGA]

import Lake
open Lake DSL

package «miniF2F» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/xinhjBrant/mathlib4.git" @ "2f65ba7f1a9144b20c8e7358513548e317d26de1"

-- require aesop from git "https://github.com/leanprover-community/aesop" @ "master"
-- require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4" @ "v0.0.36"

@[default_target]
lean_lib «MiniF2F» where
  -- add any library configuration options here

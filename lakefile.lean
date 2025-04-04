import Lake
open Lake DSL

-- package «miniF2F» where
--   -- Settings applied to both builds and interactive editing
--   leanOptions := #[
--     ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
--   ]
--   -- add any additional package configuration options here

package «miniF2F» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- require mathlib from git
--   "https://github.com/leanprover-community/mathlib4.git" @ "v4.0.0"

require aesop from git "https://github.com/leanprover-community/aesop" @ "master"
-- require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4" @ "v0.0.36"
require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4" @ "v0.0.30"


@[default_target]
lean_lib «MiniF2F» where
  -- add any library configuration options here

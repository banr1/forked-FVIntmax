import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"20c73142afa995ac9c8fb80a9bb585a55ca38308"

package «FVIntmax» where

@[default_target]
lean_lib «FVIntmax» where
  

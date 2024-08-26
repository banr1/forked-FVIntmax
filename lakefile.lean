import Lake
open Lake DSL

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"e2938e094a7a98a6f18f06ac1bd15cc0d2e89c8e"

package «FVIntmax» where

@[default_target]
lean_lib «FVIntmax» where
  

import Aesop

import Mathlib.Data.Finmap

/-
Just ignore this section.
-/
section HicSuntDracones

declare_aesop_rule_sets [Intmax.aesop_dict] (default := false)

end HicSuntDracones

namespace Finmap

section Lookup

variable {α : Type} {β : α → Type}

/--
`Finmap` prioritises partial `lookup` operator in the `Option` monad.

`Finmap.lookup_h` also takes a proof that key is in the map in order to escape the `Option`.

NB it looks a bit strange but the key `{a : α}` is implicit because it can be inferred from `h`.
-/
def lookup_h [DecidableEq α] {a : α}
  (s : Finmap β) (h : a ∈ s) : β a := s.lookup a |>.get (Option.isSome_iff_exists.2 (Finmap.mem_iff.1 h))

end Lookup

end Finmap

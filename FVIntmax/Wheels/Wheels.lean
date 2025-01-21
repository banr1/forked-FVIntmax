import Aesop

import Mathlib.Data.Finmap

/-
Just ignore this section.
-/
section HicSuntDracones

declare_aesop_rule_sets [Intmax.aesop_dict, Intmax.aesop_valid] (default := false)

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

namespace Intmax

/--
A model of a random bistring.
-/
abbrev ExtraDataT : Type := ℕ

instance : Nonempty ExtraDataT := inferInstanceAs (Nonempty ℕ)

/--
NB we are not here to model assymetric cryptography, we choose whatever.
-/
abbrev KₛT : Type := ℕ

/--
NB we are not here to model assymetric cryptography, we choose whatever.
-/
abbrev KₚT : Type := ℕ

section RubeGoldberg

/--
This is _opaque_, we will reason by axioms.
-/
opaque ComputationallyInfeasible (p : Prop) : Prop := p

/--
This is not provable because `ComputationallyInfeasible` is opaque; as such, it can NOT be unfolded.
The point of this setup is to make sure that we can _not_ easily show `¬p → ComputationallyInfeasible p`.
-/
axiom computationallyInfeasible_axiom : ∀ {p : Prop}, ComputationallyInfeasible p → ¬p

end RubeGoldberg

namespace SimpleRandom

def Seed : Type := ℕ

def isRandom (f : Seed → α) (x : α) := ∃ seed, x = f seed

scoped notation x "←ᵣ" f => isRandom f x

end SimpleRandom

section ByteArray

deriving instance DecidableEq for ByteArray

end ByteArray

end Intmax

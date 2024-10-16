import FVIntmax.Wheels.Wheels
import Mathlib.Data.Set.Basic

namespace Intmax

/-
NB: PAPER: Definition 1 - Let X be a set. We define Maybe ...
This is Lean's `Option` type, for which we have a litany of lemmas.
As such, we use this without abbreviating to `Maybe`.
-/

/--
PAPER: Given two sets X and Y, we define Dict(X, Y ) := Maybe(Y )X
-/
def Dict (α ω : Type) : Type := α → Option ω

section Dict

variable {α ω : Type}

def Dict.is_mem (m : Dict α ω) (x : α) : Prop := (m x).isSome

instance : Membership α (Dict α ω) := ⟨flip Dict.is_mem⟩

instance : GetElem (Dict α ω) α ω Dict.is_mem where
  getElem := λ m x h ↦ (m x).get h

namespace Dict

def keys (m : Dict α ω) : Set α := { x | Dict.is_mem m x }

/--
PAPER: Definition 3 Let X be a set. We define First

NB: We use the applactive choice here to define this. Subject to change, but it seems cozy for now.
To clarify, `x <|> y` yields `x` unless it fails, in which case it yeilds `y`.
If one considers `Option.none (i.e. the ⊥)` a failure, then this has the intended semantics.
-/
def First (x₁ x₂ : Option α) : Option α := x₁ <|> x₂

def Merge (D₁ D₂ : Dict α ω) : Dict α ω := D
  where D := λ x ↦ First (D₁ x) (D₂ x)

lemma mem_iff_isSome {m : Dict α ω} {x : α} : x ∈ m ↔ (m x).isSome := by rfl

/-
Just ignore this section.
-/
section AutomateMembership

@[aesop norm (rule_sets := [Intmax.aesop_dict])]
lemma mem_dict_iff_mem_keys {dict : Dict α ω} : k ∈ dict ↔ k ∈ dict.keys := by rfl

open Lean.Elab.Tactic in
/--
`dict` tries to automatically resolve membership in dictionaries.
- uses the `Intmax.aesop_dict` set
-/
elab "dict" : tactic => do
  evalTactic <| ← `(tactic| aesop (erase simp Sum.exists) (rule_sets := [Intmax.aesop_dict]))

/--
Resolve membership proof obligation by the custom `dict` tactic.
Thus, `dict[k]` will conceptually do `dict[k]'(by dict)`.
-/
macro_rules | `(tactic| get_elem_tactic_trivial) =>
              `(tactic| first | trivial | simp (config := { arith := true }); done | omega | dict)

end AutomateMembership

end Dict

end Dict

end Intmax

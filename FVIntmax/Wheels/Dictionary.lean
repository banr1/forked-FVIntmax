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
abbrev Dict (α ω : Type) : Type := α → Option ω

section Dict
variable {α ω : Type}

def Dict.is_mem (m : Dict α ω) (x : α) : Prop := (m x).isSome

@[ext]
lemma Dict.ext {D₁ D₂ : Dict α ω} (h : ∀ k, D₁ k = D₂ k) : D₁ = D₂ := by funext; aesop

instance : Membership α (Dict α ω) := ⟨Dict.is_mem⟩

instance : GetElem (Dict α ω) α ω Dict.is_mem where
  getElem := λ m x h ↦ (m x).get h

namespace Dict

def keys (m : Dict α ω) : Set α := { x | Dict.is_mem m x }

/--
PAPER: Definition 3 Let X be a set. We define First

NB we explicitly enumerate all the cases to simplify reasoning.
-/
def First (x₁ x₂ : Option α) : Option α :=
  match x₁, x₂ with
  | .some x, .none => .some x
  | .some x, .some _ => .some x
  | .none, .some y => .some y
  | .none, .none => .none

@[simp]
lemma isSome_First {x₁ x₂ : Option α} : (First x₁ x₂).isSome ↔ x₁.isSome ∨ x₂.isSome := by
  simp [First]; aesop

def Merge (D₁ D₂ : Dict α ω) : Dict α ω := D
  where D := λ x ↦ First (D₁ x) (D₂ x)

lemma mem_iff_isSome {m : Dict α ω} {x : α} : x ∈ m ↔ (m x).isSome := by rfl

@[simp]
lemma keys_Merge {D₁ D₂ : Dict α ω} : (Merge D₁ D₂).keys = D₁.keys ∪ D₂.keys := by
  unfold Merge Merge.D keys
  simp [is_mem, mem_iff_isSome]
  rfl

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

section Lemmas

variable {x₁ x₂ : Option α}
         {D₁ D₂ : Dict α ω}

lemma first_left (h : x₁.isSome) : First x₁ x₂ = x₁ := by
  simp [First]; ext; aesop

lemma first_right (h : x₁.isNone) : First x₁ x₂ = x₂ := by
  simp [First]; ext; aesop

@[simp]
lemma first_none : First .none x₂ = x₂ := by
  simp [First]; ext; aesop

@[simp]
lemma first_some {x₁ : α} : First (.some x₁) x₂ = x₁ := by
  simp [First]; ext; aesop

lemma keys_Merge_left' (h : ∀ x, x ∈ D₁) : Merge D₁ D₂ = D₁ := by
  unfold Merge Merge.D
  ext x _; simp [First]
  have : (D₁ x).isSome := by dict
  aesop

lemma keys_Merge_left {x : α} (h : x ∈ D₁) : Merge D₁ D₂ x = D₁ x := by
  unfold Merge Merge.D
  ext k; simp [First]
  have : (D₁ x).isSome := by dict
  aesop

lemma keys_Merge_right {x : α}
                       (h₁ : x ∉ D₁) (h₂ : x ∈ D₂) : Merge D₁ D₂ x = D₂ x := by
  unfold Merge Merge.D
  ext k; simp [First]
  have : (D₂ x).isSome := by dict
  have : (D₁ x).isNone := by rw [mem_iff_isSome] at h₁; aesop
  aesop

lemma keys_Merge_right' (h : ∀ x : α, x ∉ D₁) : Merge D₁ D₂ = D₂ := by
  unfold Merge Merge.D
  apply funext; intros x; specialize h x
  simp [First]
  have : (D₁ x).isNone := by rw [mem_iff_isSome] at h; aesop
  aesop

lemma Merge_assoc {D₃ : Dict α ω} :
  Merge (Merge D₁ D₂) D₃ = Merge D₁ (Merge D₂ D₃) := by
  unfold Merge Merge.D
  apply funext; intros x
  unfold First
  generalize eq₁ : D₁ x = X₁
  generalize eq₂ : D₂ x = X₂
  generalize eq₃ : D₃ x = X₃
  rcases X₁ <;> rcases X₂ <;> rcases X₃ <;> aesop

@[simp]
lemma First_none_none : Dict.First (.none : Option α) .none = .none := by
  unfold First
  simp

end Lemmas

end Dict

end Dict

end Intmax

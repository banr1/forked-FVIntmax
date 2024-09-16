import Aesop

import Mathlib.Data.Finite.Basic
import Mathlib.Data.Finmap
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Defs

namespace Intmax

/--
PAPER: K := K1 ⨿ K2
-/
abbrev Key (K₁ K₂ : Type) := K₁ ⊕ K₂

instance : Coe K₁ (Key K₁ K₂) := ⟨.inl⟩
instance : Coe K₂ (Key K₁ K₂) := ⟨.inr⟩

section Ordering

/-
NB the `LinearOrder` is _technically_ too strong, we could be a lot weaker, but for brevity and simplcitiy,
I think this is fair, because the keys are thought of as some fixed-sized integers, a'la `UInt256` - 
these can naturally be equipped with a linear order.

NB further that `LinearOrder` in Lean means _decidable_ linear order.s
-/
variable {K₁} [LinearOrder K₁]
         {K₂} [LinearOrder K₂]

def Key.le (k₁ k₂ : Key K₁ K₂) : Prop :=
  match k₁, k₂ with
  | .inl k₁, .inl k₁' => k₁ ≤ k₁'
  | .inl _,  .inr _   => True
  | .inr _,  .inl _   => False
  | .inr k₂, .inr k₂' => k₂ ≤ k₂'

instance : LE (Key K₁ K₂) := ⟨Key.le⟩

def Key.lt (k₁ k₂ : Key K₁ K₂) : Prop :=
  match k₁, k₂ with
  | .inl k₁, .inl k₁' => k₁ < k₁'
  | .inl _,  .inr _   => True
  | .inr _,  .inl _   => False
  | .inr k₂, .inr k₂' => k₂ < k₂'

instance : LT (Key K₁ K₂) := ⟨Key.lt⟩

private theorem lt_iff_le_not_le {k₁ k₂ : Key K₁ K₂} : k₁ < k₂ ↔ k₁ ≤ k₂ ∧ ¬k₂ ≤ k₁ := by
  dsimp [(·<·), (·≤·), Key.le, Key.lt]
  aesop (add safe forward le_of_lt)

private instance [(a b : K₁) → Decidable (a ≤ b)] [(a b : K₂) → Decidable (a ≤ b)] :
         (a b : Key K₁ K₂) → Decidable (a ≤ b) :=
  λ a b ↦ by
    dsimp [(·≤·), Key.le]
    rcases a with a | a <;> rcases b with b | b <;> infer_instance

private instance [IsTrans K₁ (·≤·)] [IsTrans K₂ (·≤·)] : IsTrans (Key K₁ K₂) (·≤·) :=
  {
    trans := λ a b c ↦ by
      dsimp [(·≤·), Key.le]; intros h₁ h₂
      aesop (add safe forward IsTrans.trans)
  }

private instance WW [IsAntisymm K₁ (·≤·)] [IsAntisymm K₂ (·≤·)] : IsAntisymm (Key K₁ K₂) (·≤·) :=
  {
    antisymm := λ a b ↦ by
      dsimp [(·≤·), Key.le]; intros h₁ h₂
      aesop (add safe forward IsAntisymm.antisymm)
  }

private instance : IsTotal (Key K₁ K₂) (·≤·) :=
  {
    total := λ a b ↦ by
      dsimp [(·≤·), Key.le]
      aesop (add simp le_total)
  }

/--
We order keys linearly putting K₁s first, then K₂s.
-/
instance : LinearOrder (Key K₁ K₂) where
  le := Key.le
  le_refl := λ a ↦ by dsimp [Key.le]; aesop
  le_trans := IsTrans.trans
  le_antisymm := IsAntisymm.antisymm
  le_total := IsTotal.total
  decidableLE := inferInstance
  lt_iff_le_not_le := λ a b ↦ lt_iff_le_not_le

-- theorem ¬ Sum.inr val_2 < Sum.inl val_1 := by simp [(·<·), Key.lt]

end Ordering

section Finite

variable {K₁ K₂ : Type}

instance : Coe K₁ (Key K₁ K₂) := ⟨.inl⟩
instance : Coe K₂ (Key K₁ K₂) := ⟨.inr⟩

variable [Finite K₁] [Finite K₂]

instance : Finite (Key K₁ K₂) := by
  /-
    We make a codomain `|K₁| + |K₂|` big. We put `K₁`s starting at 0 and we put `K₂`s starting at `|K₁|`.
    To recover these, we map `K₁`s directly and subtract `|K₁|` for `K₂`s.
    It is easy to show these are inverse to each other, thus yielding a bijection with a finite set of size `|K₁| + |K₂|`,
    which is finite by definition.
  -/
  unfold Key
  rw [finite_iff_exists_equiv_fin]
  obtain ⟨w₁, hw₁⟩ := Finite.exists_equiv_fin K₁
  obtain ⟨w₂, hw₂⟩ := Finite.exists_equiv_fin K₂
  have h₁ := hw₁.some
  have h₂ := hw₂.some
  use w₁ + w₂
  constructor
  exact {
    toFun := λ sum ↦
               match sum with
               | .inl k₁ => ⟨h₁ k₁, by omega⟩
               | .inr k₂ => ⟨h₂ k₂ + w₁, by omega⟩
    invFun := λ fin ↦
                if h : fin < w₁
                then .inl (h₁.invFun ⟨fin.1, h⟩)
                else .inr (h₂.invFun ⟨fin.1 - w₁, by omega⟩)
    left_inv := by unfold Function.LeftInverse
                   intros sum
                   rcases sum with k₁ | k₂ <;> simp
    right_inv := by unfold Function.RightInverse Function.LeftInverse
                    intros fin
                    by_cases eq : fin < w₁ <;> aesop
  }

noncomputable instance : Fintype (Key K₁ K₂) :=
  have := Fintype.ofFinite K₁
  have := Fintype.ofFinite K₂
  inferInstance

end Finite

end Intmax

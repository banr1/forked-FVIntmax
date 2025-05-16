import Aesop

import Mathlib.Data.Finite.Defs
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

/--
PAPER: Formally, let K := K1 ⨿ K2 ⨿ {Source}
-/
inductive Kbar (K₁ K₂ : Type) where
  | key (k : Key K₁ K₂)
  | Source
deriving DecidableEq

instance : Coe (Key K₁ K₂) (Kbar K₁ K₂) := ⟨.key⟩

def Kbar.isK₁ (k : Kbar K₁ K₂) := k matches key (.inl _)

def Kbar.getK₁ (k : Kbar K₁ K₂) (_h : k.isK₁) : K₁ :=
  match h : k with
  | .key (.inl k₁) => k₁
  | .key (.inr _) | .Source => by aesop (add simp isK₁)

section Ordering

/-
NB the `LinearOrder` is _technically_ too strong, we could be a lot weaker, but for brevity and simplicity,
I think this is fair, because the keys are thought of as some fixed-sized integers, a'la `UInt256` -
these can naturally be equipped with a linear order.

NB further that `LinearOrder` in Lean means _decidable_ linear order.s
-/
variable {K₁ : Type} [LinearOrder K₁]
         {K₂ : Type} [LinearOrder K₂]

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

private instance [IsAntisymm K₁ (·≤·)] [IsAntisymm K₂ (·≤·)] : IsAntisymm (Key K₁ K₂) (·≤·) :=
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

namespace Key

def lexLe (a b : K₂ × Key K₁ K₂) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

instance : DecidableRel (lexLe (K₁ := K₁) (K₂ := K₂)) :=
  λ a b ↦ by unfold lexLe; infer_instance

/-
NB this is an abbrev for `aesop` to extract the obvious invariants.
-/
abbrev keysUneq (k₂ : K₂) (k : Key K₁ K₂) : Prop :=
  match k with
  | .inl _   => True
  | .inr k₂' => k₂ ≠ k₂'

section CanSortWith

instance : IsTrans (K₂ × Key K₁ K₂) lexLe := by
  constructor; dsimp [lexLe]
  aesop (add safe forward le_trans) (add safe forward lt_trans)

instance : IsAntisymm (K₂ × Key K₁ K₂) lexLe := by
  constructor; dsimp [lexLe]
  aesop (add safe forward IsAntisymm.antisymm)

instance : IsTotal (K₂ × Key K₁ K₂) lexLe := by
  constructor; dsimp [lexLe]
  intros a b
  by_cases eq : a.1 = b.1
  · simp [eq]
    exact le_total _ _
  · have : a.1 < b.1 ∨ b.1 < a.1 := by aesop
    rcases this with h | h <;> tauto

end CanSortWith

end Key

infix:50 " ≠ₖ " => Key.keysUneq

instance {k₂ : K₂} {k : Key K₁ K₂} [DecidableEq K₂] : Decidable (k₂ ≠ₖ k) := by
  dsimp [(·≠ₖ·)]
  cases k <;> infer_instance

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
  have : Finite (Key K₁ K₂) := inferInstance
  Fintype.ofFinite (Key K₁ K₂)

/--
NB not important. There's an obvious equivalence between the inductive `Kbar` and the
`Key K₁ K₂ ⊕ Unit` sum, for which Lean knows how to infer things.
I prefer the wrapped inductive.
-/
def univKbar : Kbar K₁ K₂ ≃ Key K₁ K₂ ⊕ Unit :=
  {
    toFun := λ kbar ↦ match kbar with | .key k => k | .Source => ()
    invFun := λ sum ↦ match sum with | .inl k => .key k | .inr _ => .Source
    left_inv := by simp [Function.LeftInverse]; aesop
    right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  }

instance [Finite K₁] [Finite K₂] : Finite (Kbar K₁ K₂ : Type) :=
  Finite.of_equiv _ univKbar.symm

/-
Yes, noncomputable Fintype - why? Fintype fits slightly better in the hierarchy available in Mathlib.
-/
noncomputable instance : Fintype K₁ := Fintype.ofFinite _

noncomputable instance : Fintype K₂ := Fintype.ofFinite _

end Finite

end Intmax

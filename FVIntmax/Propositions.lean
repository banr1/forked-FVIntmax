import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Bounds.Defs

import Mathlib.Order.Defs

import Aesop

import FVIntmax.Wheels.Dictionary

namespace Intmax

/--
Definition 15
Let (X, ≤X) be a proset. We define the induced preorder ≤ on
Maybe(X) where for all x, y ∈ M aybe(X) we have
x ≤ y ⇔ x = ⊥ ∨ (x, y ∈ X ∧ x ≤X y)
-/
instance (priority := high) maybeInduced {α : Type} [Preorder α] : Preorder (Option α) :=
  let le : Option α → Option α → Prop := λ x y ↦
                                           match x, y with
                                           | .none, .none | .none, .some _ => True
                                           | .some x, .some y => x ≤ y
                                           | .some _, .none   => False
  {
    le := le
    lt := λ a b ↦ le a b ∧ ¬ le b a -- `False` at home.
    le_refl := by dsimp [le]; aesop
    le_trans := by dsimp [le, (·≤·)]; aesop (add safe forward le_trans)
  }

def iso {X : Type} [Preorder X] (a b : X) := a ≤ b ∧ b ≤ a

notation (priority := high) a " ≅ " b => iso a b

section iso

variable {X : Type} [Preorder X]
         {a b c : X}

@[simp, refl]
lemma iso_rfl : a ≅ a := by unfold iso; aesop

@[symm]
lemma iso_symm : (a ≅ b) ↔ b ≅ a := by unfold iso; aesop

@[trans]
lemma iso_trans : (a ≅ b) → (b ≅ c) → a ≅ c := by unfold iso; aesop (add unsafe forward le_trans)

end iso

def IsEquivRel {X : Type} [Preorder X] := ∀ a b : X, a ≤ b ↔ a ≅ b

class Setoid' (X : Type) extends Preorder X where
  isEquiv : IsEquivRel (X := X)

section Automation

@[simp]
lemma le_eq_iso [φ : Setoid' X] {a b : X} : a ≤ b ↔ a ≅ b := by
  rcases φ with ⟨equiv⟩; unfold IsEquivRel at equiv
  aesop

variable {α : Type} [Preorder α]
         {x y : α}

@[simp]
lemma none_le : Option.none ≤ .some x := by simp [(·≤·)]

@[simp]
lemma some_le_none_eq_False : .some x ≤ none ↔ False := by
  simp [(·≤·)]

@[simp]
lemma some_le_some :
  Option.some x ≤ .some y ↔ x ≤ y := by simp [(·≤·)]

@[simp]
lemma some_iso_some :
  (Option.some x ≅ .some y) ↔ x ≅ y := by
  simp [iso]

@[simp]
lemma none_iso_some : (.none ≅ some x) ↔ False := by
  simp [iso]

end Automation

section Propositions

variable {X : Type}

/--
PAPER: Proposition 1 Let (X, ≤) be a proset, let (xi)i∈I be an indexed family of el-
ements of X and let x, y ∈ X. If x and y are both joins (or both meets) of
(xi)i∈I , then we have x ≃ y. If (X, ≤) is also a poset, we have x = y.
-/
lemma proposition1 [Preorder X] {x y : X} {s : Set X}
  (h₁ : IsLUB s x) (h₂ : IsLUB s y) : x ≅ y := by
  simp [IsLUB, IsLeast, lowerBounds, upperBounds] at h₁ h₂
  unfold iso
  aesop

/--
PAPER: Proposition 2 Let (X, ≃) be a setoid, and let x, y ∈ X. Then we have that x
and y have a join in X iff x ≃ y
-/
lemma proposition2 [Setoid' X] {x y : X} :
  (∃ join : X, IsLUB {x, y} join) ↔ x ≅ y := by
  refine' Iff.intro (λ h ↦ _) (λ h ↦ _)
  · rcases h with ⟨join, ⟨h₁, -⟩⟩
    simp [mem_upperBounds] at h₁
    exact iso_trans h₁.1 h₁.2.symm
  · simp [IsLUB, IsLeast, lowerBounds, upperBounds]
    by_contra contra; simp at contra
    have : ∃ x', (x ≅ x') ∧ (y ≅ x') ∧ ¬y ≅ x' := contra _ h iso_rfl
    rcases this; aesop

/--
PAPER: in which case we have x ≃ y ≃ x ∨ y.
-/
lemma proposition2' [Setoid' X] {join x y : X} (h : IsLUB {x, y} join) :
  (x ≅ join) ∧ y ≅ join := by
  simp [IsLUB, IsLeast, upperBounds, lowerBounds] at h
  aesop

lemma iso_of_isLUB [Setoid' X] {x y join : X} (h : IsLUB {x, y} join) : x ≅ y :=
  by rw [←proposition2]; tauto

section proposition3

variable [Preorder X]
         {x? y? join? join'? : Option X}
         {x y join join' : X}

/-
NB we use different types for `X` and `Maybe(X)`.
As such, we need the injection `.some : X → Maybe(X)` to talk about joins in `Maybe(X)` for 
elements in `X`.
-/

/--
PAPER: Proposition 3 Let X be a proset and consider the induced proset Maybe(X).
For all x ∈ Maybe(x) we have x ∨ ⊥ ≃ x.
-/
lemma proposition3 (h : IsLUB {x?, .none} join?) :
  join? ≅ x? := by
  simp [IsLUB, IsLeast, upperBounds, lowerBounds, (·≤·)] at h
  rcases h with ⟨⟨h₁, h₂⟩, h₃⟩
  rcases x? with _ | x <;> rcases join? with _ | _
  · simp
  · specialize @h₃ .none; simp at h₃
  · simp at h₁
  · specialize @h₃ x (by simp) (by simp); simp [iso]; aesop

/--
PAPER: Also, for all x, y ∈ X, we have that x and y have a join in Maybe(X) iff they have a join in X
-/
lemma proposition3' : 
  (∃ join : X, IsLUB {x, y} join) ↔ (∃ join : Option X, IsLUB {.some x, .some y, .none} join) := by
  simp [IsLUB, IsLeast, Set.Ici, lowerBounds, upperBounds]
  refine' ⟨λ ⟨join, ⟨⟨h₁, h₂⟩, h₃⟩⟩ ↦ ⟨join, ⟨by simp [*], λ x? _ _ ↦ _⟩⟩, λ ⟨join, ⟨h₁, h₂⟩⟩ ↦ _⟩
  · rcases x? <;> aesop
  · rcases join with _ | join <;> simp at h₁; refine' ⟨join, ⟨by simp [*], λ x? h₃ h₄ ↦ _⟩⟩
    specialize @h₂ (.some x?)
    simp [h₃, h₄] at h₂
    exact h₂

/--
PAPER: in which case the two joins are isomorphic.
-/
lemma proposition3''
  (h : IsLUB {x, y} join)
  (h' : IsLUB {.some x, .some y, .none} join'?) :
  .some join ≅ join'? := by
  simp [iso]
  simp [IsLUB, IsLeast, Set.Ici, lowerBounds, upperBounds] at h h'
  aesop (config := {warnOnNonterminal := false}); simp [(·≤·)]
  aesop

end proposition3

section Automation

variable {X : Type} [Setoid' X]
         {x y : X}
         {x? y? : Option X}

@[simp]
lemma isLUB_some_none_of_some :
  IsLUB {.some x, none} y? ↔ IsLUB {.some x} y? := by
  simp [IsLUB, Set.Ici, IsLeast, lowerBounds, upperBounds, (·≤·)]
  rcases y?
  aesop
  aesop (config := {warnOnNonterminal := false}); exact iso_trans a.symm a_3

@[simp]
lemma isLUB_some_some_none_of_some :
  IsLUB {.some x, .some y, none} y? ↔ IsLUB {.some x, .some y} y? := by
  simp [IsLUB, Set.Ici, IsLeast, lowerBounds, upperBounds, (·≤·)]
  rcases y?
  aesop
  aesop (config := {warnOnNonterminal := false}); exact iso_trans a.symm a_4

@[simp]
lemma isLUB_any_any_none_of_any_any :
  IsLUB {x?, y?, none} join? ↔ IsLUB {x?, y?} join? := by
  simp [IsLUB, Set.Ici, IsLeast, lowerBounds, upperBounds, (·≤·)]
  rcases join?
  aesop
  rcases x?
  · aesop
  · aesop (config := {warnOnNonterminal := false})
    · exact iso_trans a.symm a_4
    · exact iso_trans a_1.symm a_5
    
@[simp]
lemma isLUB_some_none_iff_False :
  IsLUB {none} (.some x) ↔ False := by
  simp [IsLUB, IsLeast, Set.Ici, lowerBounds]
  use .none
  simp

@[simp]
lemma isLUB_none_some_iff_False :
  IsLUB {.some x} none ↔ False := by
  simp [IsLUB, IsLeast, Set.Ici, lowerBounds]

@[simp]
lemma isLUB_some_some_iff_iso :
  IsLUB {some x} (some y) ↔ some x ≅ some y := by
  simp [IsLUB, IsLeast, Set.Ici, lowerBounds]
  simp [(·≤·)]
  intros a b c
  aesop (config := {warnOnNonterminal := false})
  exact iso_trans a.symm c

@[simp]
lemma isLUB_some_some_none :
  IsLUB {some x, some y} .none ↔ False := by
  simp [IsLUB, IsLeast, Set.Ici, lowerBounds]

@[simp]
lemma isLUB_some_some_none_none :
  IsLUB {some x, some y, none} .none ↔ False := by
  simp [IsLUB, IsLeast, Set.Ici, lowerBounds]

@[simp]
lemma isLUB_some_some_none_some :
  IsLUB {some x, some y, none} (some join) ↔ ((join ≅ x) ∧ join ≅ y) := by
  simp [IsLUB, IsLeast, Set.Ici, lowerBounds]
  aesop (config := {warnOnNonterminal := false})
  exact left.symm
  exact right_1.symm
  exact left.symm
  exact right.symm
  rcases a <;> aesop (config := {warnOnNonterminal := false})
  exact iso_trans right a_2

@[simp]
lemma isLUB_some_some_some :
  IsLUB {some x, some y} (some join) ↔ ((join ≅ x) ∧ join ≅ y) := by
  simp [IsLUB, IsLeast, Set.Ici, lowerBounds]
  aesop (config := {warnOnNonterminal := false})
  exact left.symm
  exact right_1.symm
  exact left.symm
  exact right.symm
  rcases a <;> aesop (config := {warnOnNonterminal := false})
  exact iso_trans right a_2

end Automation

/--
PAPER: Proposition 4 Let (X, ≃) be a setoid, and let x, y ∈ Maybe(X). Then, x and
y have a join in Maybe(X) iff x̸ = ⊥ ∧ y̸ = ⊥ ⇒ x ≃ y.
-/
lemma proposition4 {X : Type} [Setoid' X] {x y : Option X} :
  (∃ join : Option X, IsLUB {x, y, .none} join) ↔ (x ≠ .none ∧ y ≠ .none → x ≅ y) := by
  refine' Iff.intro (λ h ⟨h₁, h₂⟩ ↦ _) (λ h ↦ _)
  · rcases x with _ | x <;> rcases y with _ | y <;> [rfl; simp at h₁; simp at h₂; skip]
    simp
    rw [←proposition3'] at h
    rcases h with ⟨join, h⟩
    obtain ⟨h₁, h₂⟩ := proposition2' h
    exact iso_trans h₁ h₂.symm
  · rcases x with _ | x <;> rcases y with _ | y
    · use .none; simp
    · use .some y; simp
    · use .some x; simp
    · simp at h
      simp_rw [←proposition3']
      exact proposition2.2 h

/--
PAPER: If this is the case, we have x ∨ y ≃ First(x, y).
-/
lemma proposition4' {X : Type} [Setoid' X] {join x y : Option X} (h : IsLUB {x, y, .none} join) :
  join ≅ Dict.First x y := by
  have eq : ∃ join, IsLUB {x, y, .none} join := (by aesop); rw [proposition4] at eq
  rcases x with _ | x <;> rcases y with _ | y <;> rcases join with _ | join <;> simp_all
  all_goals exact h.symm

/--
PAPER: Let X be a set, let (Y, ≤Y) be a proset and let f, g ∈ Y X. We
have that f and g have a join in Y X iff f(x) and g(x) have a join f(x) ∨ g(x)
in Y for all x ∈ X. 
-/
lemma proposition5 {X Y : Type} [Preorder Y] {f g : X → Y} {join : X → Y} :
  IsLUB {f, g} join ↔ ∀ x : X, IsLUB {f x, g x} (join x) := by
  simp_rw [isLUB_pi]; simp [Function.eval, Set.image]
  have : ∀ x, {x_1 | f x = x_1 ∨ g x = x_1} = {f x, g x} := by aesop
  simp_rw [this]

/--
PAPER: In this case, we have f ∨ g ≃ h, where h is a map where
h(x) ≃ f(x) ∨ g(x) for all x ∈ X.
-/
lemma proposition5' {X Y : Type} [Preorder Y] {f g h join' : X → Y}
  (h₀ : IsLUB {f, g} join')
  (h₁ : ∀ x, h x ≅ join' x) :
  join' ≅ h := by
    simp [(·≅·)] at h₁ ⊢
    simp [IsLUB, IsLeast, Set.Ici, lowerBounds, upperBounds] at h₀
    aesop (config := {warnOnNonterminal := false})
    simp [(·≤·)]
    aesop
    simp [(·≤·)]
    aesop

private lemma proposition6_aux {X Y : Type} [Setoid' Y] {D₁ D₂ : Dict X Y}
  (h : ∀ k, D₁ k ≠ .none ∧ D₂ k ≠ .none → D₁ k ≅ D₂ k) : IsLUB {D₁, D₂} (Dict.Merge D₁ D₂) := by
  unfold Dict.Merge Dict.Merge.D Dict.First
  simp [IsLUB, IsLeast, lowerBounds]
  split_ands
  · intros i; simp
    aesop
  · intros i; simp
    set X := D₁ i with eqX
    set Y := D₂ i with eqY
    rcases X with _ | X <;> rcases Y with _ | Y
    · simp [(·≤·)]
    · simp [(·≤·)]
    · simp [(·≤·)]
    · have eq₁ : (D₁ i).isSome := by rw [←eqX]; simp
      have eq₂ : (D₂ i).isSome := by rw [←eqY]; simp
      simp [←Dict.mem_iff_isSome, -Prod.forall] at h
      have : D₁ i ≤ D₂ i ∧ D₂ i ≤ D₁ i := h _ (by aesop) (by aesop)
      rw [eqX, eqY]
      aesop
  · intros π hπ₁ hπ₂ i; simp
    have hπ₁' : ∀ k, D₁ k ≤ π k := by aesop
    have hπ₂' : ∀ k, D₂ k ≤ π k := by aesop
    set X := D₁ i with eqX
    set Y := D₂ i with eqY
    set PI := π i with eqPI
    rcases X with _ | X <;> rcases Y with _ | Y <;> rcases PI with _ | PI
    · simp [(·≤·)]
    · simp [(·≤·)]
    · specialize hπ₂' i
      rw [←eqPI, ←eqY] at hπ₂'
      simp [(·≤·)] at hπ₂'
    · aesop
    · specialize hπ₂' i
      rw [←eqPI] at hπ₂'
      specialize hπ₁' i
      rw [←eqPI] at hπ₁'
      simp
      rw [←eqX] at hπ₁'
      assumption
    · specialize hπ₂' i
      specialize hπ₁' i
      aesop
    · specialize hπ₂' i
      specialize hπ₁' i
      aesop
    · specialize hπ₂' i
      specialize hπ₁' i
      aesop

/--
PAPER: Proposition 6 Let X be a set, let (Y, ≃) be a setoid and let D1, D2 ∈ Dict(X, Y )
be two dictionaries. Then, we have that D1 and D2 have a join in Dict(X, Y )
iff for all x ∈ X we have D1(x)̸ = ⊥ ∧ D2(x)̸ = ⊥ ⇒ D1(x) ≃ D2(x).
-/
lemma proposition6 {X Y : Type} [Setoid' Y] {D₁ D₂ : Dict X Y} :
  (∃ join, IsLUB {D₁, D₂} join) ↔ ∀ x, D₁ x ≠ .none ∧ D₂ x ≠ .none → D₁ x ≅ D₂ x := by
  refine' ⟨λ h ↦ _, λ h ↦ _⟩
  simp_rw [proposition5] at h
  simp_rw [←proposition4]
  aesop
  use D₁.Merge D₂
  exact proposition6_aux h

/--
PAPER: If this is the case, then we have D1 ∨ D2 ≃ Merge(D1, D2).
-/
lemma proposition6' {X Y : Type} [Setoid' Y] {D₁ D₂ join : Dict X Y} (h : IsLUB {D₁, D₂} join) :
  join ≅ Dict.Merge D₁ D₂ := by
  unfold Dict.Merge Dict.Merge.D
  apply proposition5' (h₀ := h)
  intros x
  rw [iso_symm]
  apply proposition4'
  revert x
  rw [proposition5] at h
  simpa

end Propositions

end Intmax

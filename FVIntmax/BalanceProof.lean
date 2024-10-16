import Mathlib.Algebra.Order.Group.Lattice

import FVIntmax.Wheels.AuthenticatedDictionary
import FVIntmax.Wheels.Dictionary
import FVIntmax.TransactionBatch

import Mathlib.Algebra.BigOperators.Ring

import Mathlib

namespace Intmax

section Pi

variable {K₁ : Type} [Finite K₁] [DecidableEq K₁]
         {K₂ : Type} [Finite K₂] [DecidableEq K₂]
         {V : Type} [Finite V] [DecidableEq V] [Nonnegative V]
         {C Pi : Type} (Λ : ℕ) (aggregator : K₁) (extradata : ExtraDataT)
         /-
           TODO(REVIEW) - Do we need this as a transaction batch or can we abstract over this to <some type T>?

           TODO(CHECK) - Do we need this as a transaction batch or can we abstract over this?
                         (I'll figure this out at some point in the future :grin:).
         -/
         [AD : ADScheme K₂ ((TransactionBatch K₁ K₂ V × K₂)) C Pi]

/--
Π := Dict(AD.C × K2,(AD.Π × {0, 1}∗) × VK+ ).

NB we postpone nonnegative V into validity.
-/
abbrev BalanceProof (K₁ K₂ : Type) [Finite K₁] [Finite K₂]
                    (C Pi V : Type) [Nonnegative V] : Type :=
  Dict (C × K₂) (Pi × ExtraDataT × TransactionBatch K₁ K₂ V) 

namespace BalanceProof

section Valid

/-
V is a lattice ordered abelian group
-/
variable [Lattice V]
         [AddCommGroup V]
         [CovariantClass V V (· + ·) (· ≤ ·)]
         [CovariantClass V V (Function.swap (· + ·)) (· ≤ ·)]

-- def Meet' {α : Type} (s : Finset α) (f : α → V) : V := (s.1.map f).fold (·⊓·) 0

-- def Meet'' {α : Type} (s : Finset α) (f : α → V) : V := ⨅ s, f s

open scoped BigOperators

set_option linter.unusedVariables false in
/--
PAPER: A balance proof is valid if the following algorithm returns True.
       Verify : Π → {True, F alse}
        (K, D) 7 → ^ (C,s)∈K ((π,salt),t)=D(C,s)

DO NOT FORGET NONNEG

TODO(MYSELF)
-/
def isValid [Nonnegative V] (π : BalanceProof K₁ K₂ C Pi V) : Bool := true

end Valid

end BalanceProof

end Pi

end Intmax

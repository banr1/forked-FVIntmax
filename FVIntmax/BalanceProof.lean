import Mathlib.Algebra.Order.Group.Lattice

import FVIntmax.Wheels.AuthenticatedDictionary
import FVIntmax.Wheels.Dictionary
import FVIntmax.TransactionBatch

import Mathlib.Algebra.BigOperators.Ring

import Mathlib

namespace Intmax

section Pi

variable {K₁ : Type} [Finite K₁] [DecidableEq K₁] [Nonempty K₁]
         {K₂ : Type} [Finite K₂] [DecidableEq K₂]
         {V : Type} [Finite V] [DecidableEq V] [Nonnegative V]
         {C : Type} [Nonempty C]
         {Pi : Type}
         {M : Type} [Nonempty M]
        --  /-
        --    TODO(REVIEW) - Do we need this as a transaction batch or can we abstract over this to <some type T>?

        --    TODO(CHECK) - Do we need this as a transaction batch or can we abstract over this?
        --                  (I'll figure this out at some point in the future :grin:).
        --  -/
        --  [AD : ADScheme K₂ ((TransactionBatch K₁ K₂ V × K₂)) C Pi]

/--
Π := Dict(AD.C × K2,(AD.Π × {0, 1}∗) × VK+ ).
-/
abbrev BalanceProof (K₁ K₂ : Type) [Finite K₁] [Finite K₂]
                    (C Pi V : Type) [Nonnegative V] : Type :=
  Dict (C × K₂) ((Pi × ExtraDataT) × TransactionBatch K₁ K₂ V) 

instance : Inhabited (BalanceProof K₁ K₂ C Pi V) := ⟨λ _ ↦ .none⟩

namespace BalanceProof

section Valid

open Classical

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

/-
TODO(my esteemed self) - probably remove later.
-/
noncomputable section

/--
PAPER: A balance proof is valid if the following algorithm returns True.
       Verify : Π → {True, F alse}
        (K, D) 7 → ^ (C,s)∈K ((π,salt),t)=D(C,s)

NB this is slightly more usable than `⨅ x : Dict.keys π, ...`.
-/
def Verify (π : BalanceProof K₁ K₂ C Pi V)
           [AD : ADScheme K₂ M C Pi] : Bool :=
  ∀ x, (h : x ∈ Dict.keys π) → let ((π', salt), t) := (π x).get (by dict)
                               AD.Verify π' x.2 (H _ (t, salt)) x.1

end

end Valid

end BalanceProof

end Pi

end Intmax

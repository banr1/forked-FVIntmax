import Mathlib.Algebra.Order.Group.Lattice

import FVIntmax.Propositions
import FVIntmax.TransactionBatch

import FVIntmax.Wheels.AuthenticatedDictionary
import FVIntmax.Wheels.Dictionary

import Mathlib.Algebra.BigOperators.Ring

import Mathlib

namespace Intmax

section Pi

variable {K₁ : Type} [Finite K₁] [DecidableEq K₁] [Nonempty K₁]
         {K₂ : Type} [Finite K₂] [DecidableEq K₂]
         {V : Type} [DecidableEq V] [Nonnegative V]
         {C : Type} [Nonempty C]
         {Pi : Type}
         {M : Type} [Nonempty M]

/--
Π := Dict(AD.C × K2,(AD.Π × {0, 1}∗) × VK+ ).
-/
abbrev BalanceProof (K₁ K₂ : Type) [Finite K₁] [Finite K₂]
                    (C Pi V : Type) [Nonnegative V] : Type :=
  Dict (C × K₂) ((Pi × ExtraDataT) × TransactionBatch K₁ K₂ V) 

def BalanceProof.initial : BalanceProof K₁ K₂ C Pi V := λ _ ↦ .none

instance : Inhabited (BalanceProof K₁ K₂ C Pi V) := ⟨BalanceProof.initial⟩

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

section BalanceProofLemmas

variable {K₁ : Type} [Finite K₁] 
         {K₂ : Type} [Finite K₂] 
         {V : Type} [Nonnegative V]
         {C : Type}
         {Pi : Type}
         {M : Type} [Nonempty M]

@[simp]
lemma initial_Merge {π : BalanceProof K₁ K₂ C Pi V} :
  BalanceProof.initial.Merge π = π := by
  rw [Dict.keys_Merge_right']
  intros x contra
  unfold BalanceProof.initial at contra
  rw [Dict.mem_iff_isSome] at contra
  simp at contra

@[simp]
lemma Merge_initial {π : BalanceProof K₁ K₂ C Pi V} :
  π.Merge BalanceProof.initial = π := by
  unfold BalanceProof.initial Dict.Merge Dict.Merge.D Dict.First
  apply funext; intros K
  aesop

variable [Nonempty C] [Nonempty K₁]

@[simp]
lemma BalanceProof.valid_initial :
  BalanceProof.initial.Verify (K₁ := K₁) (AD := AD) (K₂ := K₂) (V := V) (M := (C × K₁ × ExtraDataT)) := by
  simp [Verify, Dict.keys, Dict.is_mem, initial]

end BalanceProofLemmas

end Intmax

import Mathlib.Data.Finite.Defs

import FVIntmax.Balance
import FVIntmax.BalanceProof
import FVIntmax.Block
import FVIntmax.Wheels

import FVIntmax.Wheels.AuthenticatedDictionary
import FVIntmax.Wheels.SignatureAggregation

set_option lang.lemmaCmd true

namespace Intmax

noncomputable section

open Classical

def AgreedUponAggregator {K₁ : Type} [Nonempty K₁] : K₁ := Classical.arbitrary _

section Request

variable (K₁ : Type) [Finite K₁] (K₂ : Type) [Finite K₂]
         (C Sigma Pi V : Type)

section

variable [Nonnegative V]

inductive Request :=
  | deposit (recipient : K₂) (amount : V₊)
  | transfer (aggregator : K₁) (extradata : ExtraDataT) (commitment : C) (senders : List K₂) (sigma : Sigma)
  | withdrawal (π : BalanceProof K₁ K₂ C Pi V)

end

section

variable {K₁ : Type} [Finite K₁] {K₂ : Type} [Finite K₂]
         {C Sigma Pi V : Type}
         [Nonempty C] [Finite K₁] [Finite K₂] [Nonempty K₁] [Nonnegative V]
         [ADScheme K₂ (C × K₁ × ExtraDataT) C Pi]
         [SA : SignatureAggregation (C × K₁ × ExtraDataT) K₂ KₛT Sigma]

def Request.isValid (request : Request K₁ K₂ C Sigma Pi V) : Bool :=
  match request with
  /- 2.5 -/
  | deposit .. =>
      true
  /- 2.6 -/
  | transfer aggregator extradata commitment senders sigma =>
      let isValidSA := SA.Verify senders (commitment, aggregator, extradata) sigma
      let isValidAggregator := aggregator = AgreedUponAggregator
      isValidSA ∧ isValidAggregator
  /- 2.7 -/
  | withdrawal π =>
      π.Verify (M := (C × K₁ × ExtraDataT))

end

end Request

section

variable {K₁ : Type} [Finite K₁]
         {K₂ : Type} [Finite K₂]
         {C Sigma Pi : Type}
         {V : Type}

section Defs

section

variable [Nonnegative V]

def Request.getWithdrawal (request : Request K₁ K₂ C Sigma Pi V) : Option (BalanceProof K₁ K₂ C Pi V) :=
  match request with
  | withdrawal π => .some π
  | transfer .. | deposit .. => .none

end

variable [Nonempty K₁]
         [Nonempty C] [ADScheme K₂ (C × K₁ × ExtraDataT) C Pi]
         [SignatureAggregation (C × K₁ × ExtraDataT) K₂ KₛT Sigma]

section

variable [Lattice V] [AddCommGroup V]
         [CovariantClass V V (· + ·) (· ≤ ·)]
         [CovariantClass V V (Function.swap (· + ·)) (· ≤ ·)]
         [LinearOrder K₁] [LinearOrder K₂]

def BalanceProof.toBalanceF (π : BalanceProof K₁ K₂ C Pi V)
                            (σ : RollupState K₁ K₂ V C Sigma) : K₁ → V₊ :=
  λ k : K₁ ↦ ⟨Bal π σ k, by simp⟩

end

end Defs

namespace Request

section

variable [Lattice V] [AddCommGroup V]
         [CovariantClass V V (· + ·) (· ≤ ·)]
         [CovariantClass V V (Function.swap (· + ·)) (· ≤ ·)]
         [LinearOrder K₁] [Nonempty K₁] [LinearOrder K₂] [Nonempty C]
         [ADScheme K₂ (C × K₁ × ExtraDataT) C Pi]
         [SignatureAggregation (C × K₁ × ExtraDataT) K₂ KₛT Sigma]

def toBlock (σ : RollupState K₁ K₂ V C Sigma)
            (request : Request K₁ K₂ C Sigma Pi V) : Option (Block K₁ K₂ C Sigma V) :=
  if ¬request.isValid
  then .none
  else .some <|
  match request with
  /- 2.5 -/
  | .deposit r v            => .deposit r v
  /- 2.6 -/
  | .transfer a e c s sigma => .transfer a e c s sigma
  /- 2.7 -/
  | .withdrawal π           => .withdrawal (π.toBalanceF σ)

def toBlock! (σ : RollupState K₁ K₂ V C Sigma)
             (request : Request K₁ K₂ C Sigma Pi V) : Block K₁ K₂ C Sigma V :=
  match request with
  | .deposit r v            => .deposit r v
  | .transfer a e c s sigma => .transfer a e c s sigma
  | .withdrawal π           => .withdrawal (π.toBalanceF σ)

end

section Lemmas

variable [Lattice V] [AddCommGroup V]
         {request : Request K₁ K₂ C Sigma Pi V} {σ : RollupState K₁ K₂ V C Sigma}

@[simp]
lemma getWithdrawal_isSome :
  request.getWithdrawal.isSome ↔ request matches .withdrawal .. := by
  unfold getWithdrawal
  aesop

variable [CovariantClass V V (· + ·) (· ≤ ·)]
         [CovariantClass V V (Function.swap (· + ·)) (· ≤ ·)]
         [LinearOrder K₁] [Nonempty K₁] [LinearOrder K₂] [Nonempty C]
         [ADScheme K₂ (C × K₁ × ExtraDataT) C Pi]
         [SignatureAggregation (C × K₁ × ExtraDataT) K₂ KₛT Sigma]

lemma toBlock_eq_toBlock!_of_isValid (h : request.isValid) :
  (toBlock σ request) = toBlock! σ request := by unfold toBlock; aesop

lemma toBlock_eq_id_of_not_isValid (h : ¬request.isValid)  :
  (toBlock σ request) = .none := by unfold toBlock; aesop

end Lemmas

end Request

end

end

end Intmax

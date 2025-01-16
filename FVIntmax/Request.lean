import Mathlib.Data.Finite.Defs

import FVIntmax.Balance
import FVIntmax.BalanceProof
import FVIntmax.Block
import FVIntmax.Wheels

import FVIntmax.Wheels.AuthenticatedDictionary
import FVIntmax.Wheels.SignatureAggregation

/-!
NB the request infrastructure is ever so slightly different from the paper version as it came
to exist in its current form at the time of mechanisation. The differences are of technical nature
only and do not impact the model semantically (we hope).

We point out the differences whenever possible.
-/

namespace Intmax

noncomputable section

open Classical

/--
The formalisation differs ever so slightly from the paper by fixing the aggregator.
However, theorem 1 is independent of how blocks are validated (cf. `attackGame_eq_attackGameBlocks!_normalise`),
so even though this does technically influence the validity proof, it does not influence
the main security statement.
-/
def AgreedUponAggregator {K₁ : Type} [Nonempty K₁] : K₁ := Classical.arbitrary _

section Request

variable (K₁ : Type) [Finite K₁] (K₂ : Type) [Finite K₂]
         (C Sigma Pi V : Type)

section

variable [PreWithZero V]

/-
Definition 29

NB we choose to not wrap the blocks in `Request.deposit` and `Request.transfer`,
as the notion of `Block` is semantically richer (cf. `Request.withdrawal`).
As such, we choose to construct a `Block` for a _deposit_ and _transfer_ request with the natural
injection.
-/
inductive Request where
  | deposit (recipient : K₂) (amount : V₊)
  | transfer (aggregator : K₁) (extradata : ExtraDataT) (commitment : C) (senders : List K₂) (sigma : Sigma)
  | withdrawal (π : BalanceProof K₁ K₂ C Pi V)

end

section

variable {K₁ : Type} [Finite K₁] {K₂ : Type} [Finite K₂]
         {C Sigma Pi V : Type}
         [Nonempty C] [Finite K₁] [Finite K₂] [Nonempty K₁] [AddCommGroup V] [Lattice V]
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

variable [PreWithZero V]

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
                            (σ : Scontract K₁ K₂ V C Sigma) : K₁ → V₊ :=
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

/-
Definition 34

NB we also have `toBlock!` for valid requests.
Note further we do validation separately with `Request.isValid`.
-/
def toBlock (σ : Scontract K₁ K₂ V C Sigma)
            (request : Request K₁ K₂ C Sigma Pi V) : Option (Block K₁ K₂ C Sigma V) :=
  if ¬request.isValid
  then .none
  else .some <|
  match request with
  /- Definition 31 -/
  | .deposit r v            => .deposit r v
  /- Definition 32 -/
  | .transfer a e c s sigma => .transfer a e c s sigma
  /- Definition 33 -/
  | .withdrawal π           => .withdrawal (π.toBalanceF σ)

def toBlock! (σ : Scontract K₁ K₂ V C Sigma)
             (request : Request K₁ K₂ C Sigma Pi V) : Block K₁ K₂ C Sigma V :=
  match request with
  | .deposit r v            => .deposit r v
  | .transfer a e c s sigma => .transfer a e c s sigma
  | .withdrawal π           => .withdrawal (π.toBalanceF σ)

end

section Lemmas

variable [Lattice V] [AddCommGroup V]
         {request : Request K₁ K₂ C Sigma Pi V} {σ σ' : Scontract K₁ K₂ V C Sigma}

@[simp]
lemma getWithdrawal_isSome :
  request.getWithdrawal.isSome ↔ request matches .withdrawal .. := by
  unfold getWithdrawal
  aesop

variable [CovariantClass V V (· + ·) (· ≤ ·)]
         [CovariantClass V V (Function.swap (· + ·)) (· ≤ ·)]
         [LinearOrder K₁] [LinearOrder K₂]

lemma toBlock_σ_matches_withdrawal (σ σ' : Scontract K₁ K₂ V C Sigma) :
  request.toBlock! σ matches .withdrawal .. ↔
  request.toBlock! σ' matches .withdrawal .. := by unfold toBlock!; aesop

lemma toBlock_σ_isWithdrawalBlock (σ σ' : Scontract K₁ K₂ V C Sigma) :
  (request.toBlock! σ).isWithdrawalBlock ↔
  (request.toBlock! σ').isWithdrawalBlock := by unfold toBlock!; aesop

lemma toBlock!_of_deposit (h : request matches .deposit ..) :
  request.toBlock! σ matches .deposit .. := by unfold toBlock!; aesop

lemma toBlock!_of_transfer (h : request matches .transfer ..) :
  request.toBlock! σ matches .transfer .. := by unfold toBlock!; rcases request <;> simp_all

lemma toBlock!_of_withdrawal (h : request matches .withdrawal ..) :
  request.toBlock! σ matches .withdrawal .. := by unfold toBlock!; aesop

variable [Nonempty K₁] [Nonempty C]
         [ADScheme K₂ (C × K₁ × ExtraDataT) C Pi]
         [SignatureAggregation (C × K₁ × ExtraDataT) K₂ KₛT Sigma]

lemma toBlock_eq_toBlock!_of_isValid (h : request.isValid) :
  (toBlock σ request) = toBlock! σ request := by unfold toBlock; aesop

lemma toBlock_eq_id_of_not_isValid (h : ¬request.isValid) :
  (toBlock σ request) = .none := by unfold toBlock; aesop

end Lemmas

end Request

end

end

end Intmax

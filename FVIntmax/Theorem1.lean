import FVIntmax.Lemma1
import FVIntmax.Lemma2
import FVIntmax.Request

import FVIntmax.Wheels
import FVIntmax.Wheels.AuthenticatedDictionary
import FVIntmax.Wheels.SignatureAggregation

set_option lang.lemmaCmd true
set_option linter.unusedSectionVars false

namespace Intmax

open Classical

noncomputable section Intmax

variable {C Sigma Pi M : Type}
         {V : Type}
         [Lattice V] [AddCommGroup V]
         [CovariantClass V V (· + ·) (· ≤ ·)]
         [CovariantClass V V (Function.swap (· + ·)) (· ≤ ·)]
         {K₁ : Type} [Nonempty K₁] [Finite K₁] [LinearOrder K₁]
         {K₂ : Type} [Finite K₂] [LinearOrder K₂]
         {Kₚ : Type} [Nonempty Kₚ]
         {Kₛ : Type} [Nonempty Kₛ]

section RollupState

variable [Nonempty C]
         [ADScheme K₂ (C × K₁ × ExtraDataT) C Pi]
         [SA : SignatureAggregation (C × K₁ × ExtraDataT) K₂ KₛT Sigma]

def Block.isValid (block : Block K₁ K₂ C Sigma V) (π : BalanceProof K₁ K₂ C Pi V) : Bool :=
  match block with
  /- 2.5 -/
  | deposit .. => true
  /- 2.6 -/
  | transfer aggregator extradata commitment senders sigma =>
      let isValidSA := SA.Verify senders (commitment, aggregator, extradata) sigma
      let isValidAggregator := aggregator = AgreedUponAggregator
      isValidSA ∧ isValidAggregator
  /- 2.7 -/
  | withdrawal _ => π.Verify (M := (C × K₁ × ExtraDataT))

def Block.updateBalance (bal : V) (block : Block K₁ K₂ C Sigma V) : V :=
  match block with
  /- 2.5 -/
  | .deposit _ v  => bal + v
  /- 2.6 -/
  | .transfer ..  => bal
  /- 2.7 -/
  | .withdrawal B => bal - ∑ k : K₁, (B k).1

namespace RollupState

def appendBlock (σ : RollupState K₁ K₂ V C Sigma)
                (request : Request K₁ K₂ C Sigma Pi V) : RollupState K₁ K₂ V C Sigma :=
  (request.toBlock σ).elim σ (σ ++ [·])

def appendBlock! (σ : RollupState K₁ K₂ V C Sigma)
                 (request : Request K₁ K₂ C Sigma Pi V) : RollupState K₁ K₂ V C Sigma :=
  σ ++ [request.toBlock! σ]

section appendBlock

variable {σ : RollupState K₁ K₂ V C Sigma} {request : Request K₁ K₂ C Sigma Pi V}

lemma appendBlock_eq_appendBlock!_of_isValid (h : request.isValid) :
  appendBlock σ request = appendBlock! σ request := by
  unfold appendBlock
  rw [Request.toBlock_eq_toBlock!_of_isValid h]
  rfl

lemma appendBlock_eq_id_of_not_isValid (h : ¬request.isValid) :
  appendBlock σ request = σ := by
  unfold appendBlock
  rw [Request.toBlock_eq_id_of_not_isValid h]
  rfl

end appendBlock

end RollupState

end RollupState

noncomputable section lemma1

variable {K₁ : Type} [Finite K₁] [LinearOrder K₁] [Nonempty K₁]
         {K₂ : Type} [Finite K₂] [LinearOrder K₂]
         {C : Type} [Nonempty C]
         {Pi : Type}
         {Sigma V : Type} [Lattice V]
                          [AddCommGroup V]
                          [CovariantClass V V (· + ·) (· ≤ ·)]
                          [CovariantClass V V (Function.swap (· + ·)) (· ≤ ·)]
         [ADScheme K₂ (C × K₁ × ExtraDataT) C Pi]
         [SignatureAggregation (C × K₁ × ExtraDataT) K₂ KₛT Sigma]

def attackGameBlocks' (requests : List (Request K₁ K₂ C Sigma Pi V))
                      (σ : RollupState K₁ K₂ V C Sigma) : RollupState K₁ K₂ V C Sigma :=
  requests.foldl RollupState.appendBlock σ

def attackGame (requests : List (Request K₁ K₂ C Sigma Pi V)) : RollupState K₁ K₂ V C Sigma :=
  attackGameBlocks' requests []

def attackGameBlocks'! (requests : List (Request K₁ K₂ C Sigma Pi V))
                       (σ : RollupState K₁ K₂ V C Sigma) : RollupState K₁ K₂ V C Sigma :=
  requests.foldl RollupState.appendBlock! σ

def attackGameBlocks! (requests : List (Request K₁ K₂ C Sigma Pi V)) : RollupState K₁ K₂ V C Sigma :=
  attackGameBlocks'! requests []

section AttackGame

variable [Nonempty C] [Finite K₁] [Finite K₂] [Nonempty K₁]
         [Lattice V]
         [AddCommGroup V]
         [CovariantClass V V (· + ·) (· ≤ ·)]
         [CovariantClass V V (Function.swap (· + ·)) (· ≤ ·)]
         [ADScheme K₂ (C × K₁ × ExtraDataT) C Pi]
         [SA : SignatureAggregation (C × K₁ × ExtraDataT) K₂ KₛT Sigma]
         {request : Request K₁ K₂ C Sigma Pi V}
         {requests : List (Request K₁ K₂ C Sigma Pi V)}
         {σ : RollupState K₁ K₂ V C Sigma}

def normalise (requests : List (Request K₁ K₂ C Sigma Pi V)) : List (Request K₁ K₂ C Sigma Pi V) :=
  requests.filter Request.isValid

lemma attackGameBlocks'_eq_attackGameBlocks'!_normalise : 
  attackGameBlocks' requests σ = attackGameBlocks'! (normalise requests) σ := by
  unfold attackGameBlocks' attackGameBlocks'!
  unfold normalise
  induction' requests with hd tl ih generalizing σ
  · rfl
  · by_cases eq : hd.isValid
    · rw [List.filter_cons_of_pos eq]; dsimp
      rw [ih, ←RollupState.appendBlock_eq_appendBlock!_of_isValid eq]
    · rw [List.filter_cons_of_neg eq]; dsimp
      rw [ih]
      rw [RollupState.appendBlock_eq_id_of_not_isValid eq]

lemma attackGameBlocks_eq_attackGameBlocks!_normalise {requests : List (Request K₁ K₂ C Sigma Pi V)} :
  attackGame requests = attackGameBlocks! (normalise requests) :=
  attackGameBlocks'_eq_attackGameBlocks'!_normalise

def computeBalance' (blocks : RollupState K₁ K₂ V C Sigma) (acc : V) : V :=
  blocks.foldl Block.updateBalance acc

def computeBalance (blocks : RollupState K₁ K₂ V C Sigma) : V :=
  computeBalance' blocks 0

end AttackGame

def adversaryWon (blocks : RollupState K₁ K₂ V C Sigma) := ¬0 ≤ computeBalance blocks

variable {requests : List (Request K₁ K₂ C Sigma Pi V)}
         [ADScheme K₂ (C × K₁ × ExtraDataT) C Pi]
         [CryptoAssumptions.Injective (H (α := TransactionBatch K₁ K₂ V × ExtraDataT) (ω := (C × K₁ × ExtraDataT)))]

theorem theorem1 : ¬adversaryWon (attackGame requests) := by
  /-
    Something like this.
    This shows that the attack game plays out the same regardless of whether all requests are valid.
  -/
  rw [attackGameBlocks_eq_attackGameBlocks!_normalise]
  /-
    And then the proof continues :).
  -/
  sorry

end lemma1

end Intmax

end Intmax

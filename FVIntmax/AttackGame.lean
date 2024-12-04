import FVIntmax.Wheels.AuthenticatedDictionary
import FVIntmax.Wheels.SignatureAggregation

import FVIntmax.BalanceProof
import FVIntmax.Block
import FVIntmax.Request
import FVIntmax.Wheels

namespace Intmax

noncomputable section Intmax

namespace RollupContract

open Classical

section

variable {C : Type} [Nonempty C]

         {V : Type} [Nonnegative V] [AddCommGroup V]
         
         {K₁ : Type} [Finite K₁] [Nonempty K₁]
         {K₂ : Type} [Finite K₂]
         {Sigma : Type}
         [ADScheme K₂ (C × K₁ × ExtraDataT) C Pi]
         [SA : SignatureAggregation (C × K₁ × ExtraDataT) K₂ KₛT Sigma]

def Block.isValid (block : Block K₁ K₂ C Sigma V) (π : BalanceProof K₁ K₂ C Pi V) : Bool :=
  match block with
  /- 2.5 -/
  | .deposit .. => true
  /- 2.6 -/
  | .transfer aggregator extradata commitment senders sigma =>
      let isValidSA := SA.Verify senders (commitment, aggregator, extradata) sigma
      let isValidAggregator := aggregator = AgreedUponAggregator
      isValidSA ∧ isValidAggregator
  /- 2.7 -/
  | .withdrawal _ => π.Verify (M := (C × K₁ × ExtraDataT))

def Block.updateBalance (bal : V) (block : Block K₁ K₂ C Sigma V) : V :=
  match block with
  /- 2.5 -/
  | .deposit _ v  => bal + v
  /- 2.6 -/
  | .transfer ..  => bal
  /- 2.7 -/
  | .withdrawal B => bal - ∑ k : K₁, (B k).1

end

end RollupContract

end Intmax

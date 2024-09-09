import Mathlib.Data.Finmap

import FVIntmax.Wheels

namespace Intmax

/--
2.4

NB the `V` here does not _yet_ need the fact that it is a latticed-ordered abelian group.

𝔹 := Bdeposit ⨿ Btransf er ⨿ Bwithdrawal
-/
inductive Block (K₁ K₂ : Type) (C Sigma : Type) (V : Type) :=
  /--
    Bdeposit - (2.5 - Bdeposit := K₂ × V+)
    
    TODO(REVIEW): > A deposit block contains only one deposit tx?
                  I have no intuition for this, but formally they state this is in fact the case.
  -/
  | deposit (recipient : K₂) (amount : V)
  /--
    Btransfer - (2.6 - Btransfer = Btransf er = K1 × {0, 1}∗ × AD.C × P(K) × SA.Σ)

    NB I can _not_ bring myself to abuse DTT to express `validUsers : K₂` beyond `K₂`.
    The intent is to subset en passant in subsequent statements about transfers.
  -/
  | transfer (aggregator : K₁) (extradata : ByteArray) (commitment : C) (validUsers : K₂) (sigma : Sigma)
  /--
    Bwithdrawal - (2.7 - Bwithdrawal = V^{K_1}_+)

    NB we will see later about total/partial in this particular instance.
  -/ 
  | withdrawal (withdrawals : Finmap (λ _ : K₁ ↦ V))

namespace Block

def mkDepositBlock {K₂ V : Type}
  (K₁ C Sigma : Type) (addr : K₂) (value : V) : Block K₁ K₂ C Sigma V := Block.deposit addr value 

def mkTransferBlock {K₁ K₂ V Sigma : Type}
  (aggregator : K₁) (extradata : ByteArray) (commitment : C) (validUsers : K₂) (sigma : Sigma) :
  Block K₁ K₂ C Sigma V := Block.transfer aggregator extradata commitment validUsers sigma

def mkWithdrawalBlock {K₁ V : Type}
  (K₂ C Sigma : Type) (withdrawals : Finmap (λ _ : K₁ ↦ V)) : Block K₁ K₂ C Sigma V :=
  Block.withdrawal withdrawals

section ValidBlock

/-
Valid blocks are blocks that contain nonnegative `V`s. We avoid subtyping `V`s in the definition
of the block itself for convenience:
- it declutters requirements on the types `Block` can be made of
- it removes the ugly subtype (i.e. a dependent type) in the `Block`

NB this is subject to change, especiall with respect to partial `isValid<X>` definitions - 
keeping just the global one with direct definitions might be slightly more convenient.
-/

variable {K₁ : Type} [DecidableEq K₁]
         {K₂ : Type} {C Sigma : Type}
         {V : Type} [OfNat V 0] [LE V]

def isValid (block : Block K₁ K₂ C Sigma V) :=
  match block with
  | deposit _ amount   => 0 ≤ amount
  | transfer _ _ _ _ _ => True  
  | withdrawal ws      => isCodomainNonneg ws

/-
`depositBlockOfDeposit` constructs a valid block if the value being deposited is nonnegative
-/
theorem isValid_mkDepositBlock_of_nonneg {value : V}
  (h : 0 ≤ value) : (Block.mkDepositBlock K₁ C Sigma addr value).isValid := h

end ValidBlock

end Block

end Intmax

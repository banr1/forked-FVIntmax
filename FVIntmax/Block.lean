import Mathlib.Data.Finmap

import FVIntmax.Wheels

namespace Intmax

/--
2.4

NB the `V` here does not _yet_ need the fact that it is a latticed-ordered abelian group.

𝔹 := Bdeposit ⨿ Btransf er ⨿ Bwithdrawal
-/
inductive Block (K₁ K₂ : Type) (C Sigma : Type) (V : Type) [Nonnegative V] :=
  /--
    Bdeposit - (2.5 - Bdeposit := K₂ × V+)

    TODO(REVIEW): > A deposit block contains only one deposit tx?
                  I have no intuition for this, but formally they state this is in fact the case.
  -/
  | deposit (recipient : K₂) (amount : V₊)
  /--
    Btransfer - (2.6 - Btransfer = K1 × {0, 1}∗ × AD.C × P(K) × SA.Σ)

    NB `senders` is currently a list with potentially duplicates, this can morph into a set
    or at least a list with `List.Nodup`, let's see if this is needed.
  -/
  | transfer (aggregator : K₁) (extradata : ExtraDataT) (commitment : C) (senders : List K₂) (sigma : Sigma)
  /--
    Bwithdrawal - (2.7 - Bwithdrawal = V^{K_1}_+)

    NB we will see later about total/partial in this particular instance.
  -/
  | withdrawal (withdrawals : Finmap (λ _ : K₁ ↦ V₊))

namespace Block

section Block

variable {K₁ K₂ C Sigma V : Type} [Nonnegative V]

def mkDepositBlock (K₁ C Sigma : Type) (addr : K₂) (value : V₊) : Block K₁ K₂ C Sigma V :=
  Block.deposit addr value

def mkTransferBlock (aggregator : K₁) (extradata : ExtraDataT)
                    (commitment : C) (senders : List K₂) (sigma : Sigma) : Block K₁ K₂ C Sigma V :=
  Block.transfer aggregator extradata commitment senders sigma

def mkWithdrawalBlock (K₂ C Sigma : Type) (withdrawals : Finmap (λ _ : K₁ ↦ V₊)) : Block K₁ K₂ C Sigma V :=
  Block.withdrawal withdrawals

abbrev isDepositBlock (b : Block K₁ K₂ C Sigma V) := b matches (Block.deposit _ _) 

abbrev isTransferBlock (b : Block K₁ K₂ C Sigma V) := b matches (Block.transfer _ _ _ _ _)

abbrev isWithdrawalBlock (b : Block K₁ K₂ C Sigma V) := b matches (Block.withdrawal _)

@[simp]
lemma transfer_ne_deposit :
  (transfer aggregator extradata commitment senders sigma).isDepositBlock (V := V) = False := by aesop

@[simp]
lemma withdrawal_ne_deposit :
  (withdrawal ws).isDepositBlock (V := V) (Sigma := Sigma) (C := C) (K₂ := K₂) = False := by aesop

@[simp]
lemma deposit_ne_transfer : 
  (deposit s v).isTransferBlock (V := V) (Sigma := Sigma) (C := C) (K₁ := K₁) = False := by aesop

@[simp]
lemma withdrawal_ne_transfer : 
  (withdrawal ws).isTransferBlock (V := V) (Sigma := Sigma) (C := C) (K₂ := K₂) = False := by aesop

@[simp]
lemma deposit_ne_widthdrawal : 
  (deposit s v).isWithdrawalBlock (V := V) (Sigma := Sigma) (C := C) (K₁ := K₁) = False := by aesop

@[simp]
lemma transfer_ne_widthdrawal : 
  (transfer aggregator extradata commitment senders sigma).isWithdrawalBlock (V := V) = False := by aesop

end Block

end Block

end Intmax

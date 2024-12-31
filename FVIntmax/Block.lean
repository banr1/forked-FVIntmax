import Mathlib.Data.Finmap

import FVIntmax.Wheels

namespace Intmax

/--
2.4

NB the `V` here does not _yet_ need the fact that it is a latticed-ordered abelian group.

𝔹 := Bdeposit ⨿ Btransf er ⨿ Bwithdrawal
-/
inductive Block (K₁ K₂ : Type) (C Sigma : Type) (V : Type) [Nonnegative V] where
  /--
    Bdeposit - (2.5 - Bdeposit := K₂ × V+)
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
  | withdrawal (withdrawals : K₁ → V₊)

namespace Block

section Block

variable {K₁ K₂ C Sigma V : Type} [Nonnegative V]

def mkDepositBlock (K₁ C Sigma : Type) (addr : K₂) (value : V₊) : Block K₁ K₂ C Sigma V :=
  deposit addr value

def mkTransferBlock (aggregator : K₁) (extradata : ExtraDataT)
                    (commitment : C) (senders : List K₂) (sigma : Sigma) : Block K₁ K₂ C Sigma V :=
  transfer aggregator extradata commitment senders sigma

def mkWithdrawalBlock (K₂ C Sigma : Type) (withdrawals : K₁ → V₊) : Block K₁ K₂ C Sigma V :=
  withdrawal withdrawals

abbrev isDepositBlock (b : Block K₁ K₂ C Sigma V) := b matches (Block.deposit _ _) 

abbrev isTransferBlock (b : Block K₁ K₂ C Sigma V) := b matches (Block.transfer _ _ _ _ _)

abbrev isWithdrawalBlock (b : Block K₁ K₂ C Sigma V) := b matches (Block.withdrawal _)

/--
Definition 35

NB we define this function in the `Π` space of blocks that are withdrawal blocks.
-/
def getWithdrawal (b : Block K₁ K₂ C Sigma V) (_h : b.isWithdrawalBlock) : K₁ → V₊ :=
  match b with | .withdrawal B => B

def getDeposit? (b : Block K₁ K₂ C Sigma V) : Option (K₂ × V₊) :=
  match b with
  | deposit r v => .some (r, v)
  | transfer .. | withdrawal .. => .none

lemma isSome_getDeposit?_of_isDepositBlock {b : Block K₁ K₂ C Sigma V}
  (h : b.isDepositBlock) : b.getDeposit?.isSome := by unfold getDeposit?; aesop

def getDeposit (b : Block K₁ K₂ C Sigma V) (_h : b.isDepositBlock) : K₂ × V₊ :=
  match b with | deposit r v => (r, v)

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

@[simp]
lemma getDeposit_deposit {r : K₂} {v : V₊} :
  getDeposit (.deposit r v) (by aesop) = (r, v) := rfl

end Block

end Block

/--
Definition 28

- Scontract := `𝔹* × V`

NB we keep `V` as a separate entity during the attack game, instead of merging it with the state.
Furthermore, we do _not_ model Definition 30 explicitly; once again, we take the values separately 
instead. This helps with housekeeping as it avoids an extra abstraction that is used only once.
-/
abbrev Scontract (K₁ K₂ V : Type) [Nonnegative V] (C Sigma : Type) :=
  List (Block K₁ K₂ C Sigma V)

namespace Scontract

section Defs

variable (K₁ K₂ C Sigma : Type)
         (V : Type) [Nonnegative V]

def initial : Scontract K₁ K₂ V C Sigma := []

end Defs

section Lemmas

variable {K₁ K₂ C Sigma : Type}
         {V : Type} [Nonnegative V]

@[simp]
lemma length_initial : (@initial K₁ K₂ C Sigma V _).length = 0 := rfl

@[simp]
lemma bs_initial : (@initial K₁ K₂ C Sigma V _) = [] := rfl

end Lemmas

end Scontract

end Intmax

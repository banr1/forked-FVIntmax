import Mathlib

import FVIntmax.BalanceProof
import FVIntmax.Block
import FVIntmax.Key
import FVIntmax.RollupContract
import FVIntmax.Wheels

import FVIntmax.Wheels.Dictionary

namespace Intmax

open Classical -- Don't care :).

/-
Appendix B - Computing balances
-/
section Balance

variable {Pi : Type}
         {K₁ : Type} -- [DecidableEq K₁]
         {K₂ : Type} -- [DecidableEq K₂]
         {V C Sigma : Type}

/--
PAPER: Formally, let K := K1 ⨿ K2 ⨿ {Source}
-/
inductive Kbar (K₁ K₂ : Type) where
  | key (k : Key K₁ K₂)
  | Source
deriving DecidableEq

instance : Coe (Key K₁ K₂) (Kbar K₁ K₂) := ⟨.key⟩

/--
NB we use Lean's natural associativity for products to get some freebies.
As such, our tuples are technically `(a, (b, c))` here. Obviously, this is associative
so not much changes.

NB further, we postpone nonnegativity of V into `Τ.isValid`.
-/
abbrev Τ (K₁ K₂ V : Type) := Kbar K₁ K₂ × Kbar K₁ K₂ × Option V

def Τ.isValid (τ : Τ K₁ K₂ V) [LE V] [OfNat V 0] :=
  match τ with
  | (s, r, v) => s ≠ r ∧ v.elim True (0 ≤ ·) ∧ s matches .Source → v.isSome 

section Deposit

def TransactionsInBlock_deposit (b : { b : Block K₁ K₂ C Sigma V // b.isDepositBlock }) : List (Τ K₁ K₂ V) :=
  match h : b.1 with
  | .deposit r v => [(.Source, r, v)]
  | .withdrawal .. | .transfer .. => by aesop

end Deposit

section Order

variable [LinearOrder K₁] [LinearOrder K₂]

def lexLe [LinearOrder K₁] [LinearOrder K₂] (a b : K₂ × Key K₁ K₂) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

instance [LinearOrder K₁] [LinearOrder K₂] : DecidableRel (lexLe (K₁ := K₁) (K₂ := K₂)) :=
  λ a b ↦ by unfold lexLe; infer_instance

section Transfer

def keysUneq (k₂ : K₂) (k : Key K₁ K₂) : Prop :=
  match k with
  | .inl _   => True
  | .inr k₂' => k₂ ≠ k₂' 

infix:50 " ≠ₖ " => keysUneq 

@[deprecated]
instance [DecidableEq K₂] : DecidablePred (Function.uncurry (keysUneq (K₁ := K₁) (K₂ := K₂))) :=
  λ keys ↦
    by unfold Function.uncurry keysUneq
       rcases keys with ⟨_, k₂'⟩
       cases k₂' <;> infer_instance

instance {k₂ : K₂} {k : Key K₁ K₂} [DecidableEq K₂] : Decidable (k₂ ≠ₖ k) := by
  unfold keysUneq
  cases k <;> infer_instance

/-
Sort will behave.
-/
instance : IsTrans (K₂ × Key K₁ K₂) lexLe := by
  constructor; dsimp [lexLe]
  intros a b c h₁ h₂
  aesop (add safe forward le_trans) (add safe forward lt_trans) (config := {warnOnNonterminal := false})
  · have : ¬ Sum.inr val_2 < Sum.inl val_1 := by simp [(·<·), Key.lt]
    contradiction
  · have : ¬ Sum.inr val_1 < Sum.inl val := by simp [(·<·), Key.lt]
    contradiction

instance : IsAntisymm (K₂ × Key K₁ K₂) lexLe := by
  constructor; dsimp [lexLe]
  intros a b h₁ h₂
  aesop (add safe forward IsAntisymm.antisymm)

instance : IsTotal (K₂ × Key K₁ K₂) lexLe := by
  constructor; dsimp [lexLe]
  intros a b
  by_cases eq : a.1 = b.1
  · simp [eq]
    apply le_total
  · have : a.1 < b.1 ∨ b.1 < a.1 := by aesop
    rcases this with h | h <;> tauto

noncomputable def TransactionsInBlock_transfer [Finite K₁] [Finite K₂] [MulOneClass V]
  (π : BalanceProof K₁ K₂ V C Pi)
  (b : { b : Block K₁ K₂ C Sigma V // b.isTransferBlock }) :
  List (Τ K₁ K₂ V) :=
  match h : b.1 with
  | .transfer _ _ commitment S _ =>
    /-
      Plumbing, ignore.
    -/
    have : Fintype K₁ := Fintype.ofFinite _; have : Fintype K₂ := Fintype.ofFinite _
    /-
      PAPER: for each sender-recipient pair (s, r) ∈ K2 × K where s ̸= r

      TODO(MY ESTEEMED SELF):
      -- (Set.univ |>.prod Set.univ).toFinset.filter (Function.uncurry keysUneq)
    -/
    let senderRecipient : Finset (K₂ × Key K₁ K₂) := { (k₂, k) | (k₂ : K₂) (k : Key K₁ K₂) (_h : k₂ ≠ₖ k) }
    let sorted : List (K₂ × Key K₁ K₂) := senderRecipient.sort lexLe
    /-
      PAPER:
      v = t(r), where ( , t) = π(C, s), if s ∈ S and π(C, s) ̸= ⊥
          ⊥,                            if s ∈ S and π(C, s) = ⊥
          0,                            if s /∈ S

      NB this is using the old notion of `Dict` because it's half a day's of work to restitch to the new one.
    -/
    let v (s : K₂) (r : Key K₁ K₂) : Option V :=
      -- NB Lean's default groups are multiplicative
      -- if this bothers anyone reading this, I can switch to AddGroup somehow I think
      if s ∉ S then .some 1 else 
      if h : (commitment, s) ∈ π.keys
      then let (_, _, t) := π[(commitment, s)]
           t.lookup r
      else .none
    sorted.map λ (s, r) ↦ (s, r, v s r)
  | .deposit .. | .withdrawal .. => by aesop

end Transfer

/--
TODO(REVIEW):
> Given a withdrawal block, the list of transactions extracted from it consists of
  a transaction from each L1 account to the source account in order:

In... what order?
-/
noncomputable def TransactionsInBlock_withdrawal [Finite K₁]
  (b : { b : Block K₁ K₂ C Sigma V // b.isWithdrawalBlock }) :
  List (Τ K₁ K₂ V) :=
  match h : b.1 with
  | .withdrawal withdrawals =>
    /-
      Plumbing. Ignore.
    -/
    have : Fintype K₁ := Fintype.ofFinite _

    /-
      The paper says 'in order'. This natural linear order?
    -/
    let k₁InOrder := { s | s : K₁ }.toFinset.sort (·≤·)
    k₁InOrder.map λ s : K₁ ↦ (s, .Source, withdrawals.lookup s)
    -- TODO(MY ESTEEMED SELF): This is of replication for l.map λ x ↦ (x, ...) happens in the transfer as well.
    -- Might be worth giving it a think to avoid reproving random stuff in the future.
  | .deposit r v | .transfer .. => by aesop

end Order

end Balance

end Intmax

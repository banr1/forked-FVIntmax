import Mathlib

import FVIntmax.Block
import FVIntmax.Key
import FVIntmax.RollupContract
import FVIntmax.Wheels

namespace Intmax

/-
Appendix B - Computing balances
-/
section Balance

variable {Pi : Type}
         {K₁ : Type} [DecidableEq K₁]
         {K₂ : Type} [DecidableEq K₂]
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

def TransactionsInBlock_deposit (b : { b : Block K₁ K₂ C Sigma V // b.isDepositBlock }) : Τ K₁ K₂ V :=
  match h : b.1 with
  | .deposit r v => (.Source, r, v)
  | .withdrawal .. | .transfer .. => by aesop

end Deposit

section Transfer

def keysUneq (k₂ : K₂) (k : Key K₁ K₂) : Prop :=
  match k with
  | .inl _   => True
  | .inr k₂' => k₂ ≠ k₂' 

infix:50 "≠ₖ" => keysUneq 

@[deprecated]
instance : DecidablePred (Function.uncurry (keysUneq (K₁ := K₁) (K₂ := K₂))) :=
  λ keys ↦
    by unfold Function.uncurry keysUneq
       rcases keys with ⟨_, k₂'⟩
       cases k₂' <;> infer_instance

instance {k₂ : K₂} {k : Key K₁ K₂} : Decidable (k₂ ≠ₖ k) := by
  unfold keysUneq
  cases k <;> infer_instance

def almostLexLt [LinearOrder K₁] [LinearOrder K₂] (a b : K₂ × Key K₁ K₂) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

instance [LinearOrder K₁] [LinearOrder K₂] : DecidableRel (almostLexLt (K₁ := K₁) (K₂ := K₂)) :=
  λ a b ↦ by unfold almostLexLt; infer_instance

def TransactionsInBlock_transfer
  [Finite K₁] [LinearOrder K₁]
  [Finite K₂] [LinearOrder K₂]
  (π : Pi) (b : { b : Block K₁ K₂ C Sigma V // b.isTransferBlock }) : Τ K₁ K₂ V :=
  match h : b.1 with
  | .transfer aggregator extradata C S σ =>
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
    /-
      We need to show transitivity, antisymmetry and totality to have a well-behaved sort.
    -/
    have : IsTrans (K₂ × Key K₁ K₂) almostLexLt := by
      constructor; dsimp [almostLexLt]
      intros a b c h₁ h₂
      aesop (add safe forward le_trans) (add safe forward lt_trans) (config := {warnOnNonterminal := false})
      · have : ¬ Sum.inr val_2 < Sum.inl val_1 := by simp [(·<·), Key.lt]
        contradiction
      · have : ¬ Sum.inr val_1 < Sum.inl val := by simp [(·<·), Key.lt]
        contradiction
    have : IsAntisymm (K₂ × Key K₁ K₂) almostLexLt := by
      constructor; dsimp [almostLexLt]
      intros a b h₁ h₂
      aesop (add safe forward IsAntisymm.antisymm)
    have : IsTotal (K₂ × Key K₁ K₂) almostLexLt := by
      constructor; dsimp [almostLexLt]
      intros a b
      by_cases eq : a.1 = b.1
      · simp [eq]
        apply le_total
      · have : a.1 < b.1 ∨ b.1 < a.1 := by aesop
        rcases this with h | h <;> tauto
    let sorted : List (K₂ × Key K₁ K₂) := senderRecipient.sort almostLexLt
    /-
      PAPER:
      v = t(r), where ( , t) = π(C, s), if s ∈ S and π(C, s) ̸= ⊥
          ⊥,                            if s ∈ S and π(C, s) = ⊥
          0,                            if s /∈ S
    -/
    -- let v (s : K₂) (r : Key K₁ K₂) : Option V :=
    --   if s ∉ senders then .some 0 else
    --   match 
    sorry
  | .deposit .. | .withdrawal .. => by aesop

end Transfer

def TransactionsInBlock_withdrawal (b : { b : Block K₁ K₂ C Sigma V // b.isWithdrawalBlock }) : Τ K₁ K₂ V :=
  match h : b.1 with
  | .withdrawal _ => sorry
  | .deposit r v | .transfer .. => by aesop

-- def TransactionsInBlocks (Pi : Type) (s : RollupState K₁ K₂ V C Sigma) : Τ K₁ K₂ V :=
--   match s

-- def Bal (pi : Pi) (s : RollupState K₁ K₂ V C Sigma) : Finmap (λ _ : Kbar K₁ K₂ ↦ V) := _



end Balance

end Intmax

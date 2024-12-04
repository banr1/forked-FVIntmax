import FVIntmax.Lemma1
import FVIntmax.Lemma2
import FVIntmax.Propositions
import FVIntmax.Request

import FVIntmax.Wheels
import FVIntmax.Wheels.AuthenticatedDictionary
import FVIntmax.Wheels.SignatureAggregation

import Mathlib

set_option lang.lemmaCmd true
set_option linter.unusedSectionVars false

namespace Intmax

open Classical

noncomputable section Intmax

section

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

section Lemmas

variable {block : Block K₁ K₂ C Sigma V}

lemma Block.updateBalance_eq_zero :
  block.updateBalance v = v + block.updateBalance 0 := by
  unfold Block.updateBalance
  match block with
  | .deposit .. => simp
  | .transfer .. => simp
  | .withdrawal B => simp; exact sub_eq_add_neg v (∑ x : K₁, ↑(B x))

lemma Block.updateBalance_of_transfer (h : block.isTransferBlock) :
  block.updateBalance v = v := by
  unfold Block.updateBalance
  match block with
  | .transfer .. => simp
  | .withdrawal .. | .deposit .. => aesop

@[simp]
lemma Block.updateBalance_transfer {v : V} {a : K₁} {b : ExtraDataT} {c : C} {d : List K₂} (e : Sigma) :
  (Block.transfer a b c d e).updateBalance v = v :=
  Block.updateBalance_of_transfer rfl

@[simp]
lemma Block.updateBalance_deposit {r : K₂} {v : V} {vplus : V₊} :
  (Block.deposit r vplus).updateBalance (K₁ := K₁) (C := C) (Sigma := Sigma) v = v + vplus := by
  unfold Block.updateBalance; aesop

@[simp]
lemma Block.updateBalance_withdrawal {B : K₁ → V₊} :
  (Block.withdrawal B).updateBalance (K₁ := K₁) (K₂ := K₂) (C := C) (Sigma := Sigma) v = v - ∑ (k : K₁), (B k).1 := by
  unfold Block.updateBalance; aesop

end Lemmas

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

@[simp]
lemma length_appendBlock :
  (appendBlock! σ request).length = σ.length + 1 := by simp [appendBlock!]

lemma appendBlock!_def : σ.appendBlock! request = σ ++ [request.toBlock! σ] := rfl

@[simp]
lemma appendBlock!_nil : RollupState.appendBlock! [] request = [request.toBlock! []] := rfl

end appendBlock

end RollupState

end RollupState

noncomputable section lemma1

section

variable {K₁ : Type} [Finite K₁] [LinearOrder K₁] [Nonempty K₁]
         {K₂ : Type} [Finite K₂] [LinearOrder K₂] [Nonempty K₂]
         {C : Type} [Nonempty C]
         {Pi : Type}
         {Sigma V : Type} [Lattice V]
                          [AddCommGroup V]
                          [CovariantClass V V (· + ·) (· ≤ ·)]
                          [CovariantClass V V (Function.swap (· + ·)) (· ≤ ·)]
         [ADScheme K₂ (C × K₁ × ExtraDataT) C Pi]
         [SignatureAggregation (C × K₁ × ExtraDataT) K₂ KₛT Sigma]

section AttackGameDefs

variable (requests : List (Request K₁ K₂ C Sigma Pi V))
         (σ : RollupState K₁ K₂ V C Sigma)

def attackGameBlocks' : RollupState K₁ K₂ V C Sigma :=
  requests.foldl RollupState.appendBlock σ

def attackGame : RollupState K₁ K₂ V C Sigma :=
  attackGameBlocks' requests []

def attackGameBlocks'! : RollupState K₁ K₂ V C Sigma :=
  requests.foldl RollupState.appendBlock! σ

def attackGameBlocks'!r (requests : List (Request K₁ K₂ C Sigma Pi V))
                        (σ : RollupState K₁ K₂ V C Sigma) : RollupState K₁ K₂ V C Sigma :=
  match requests with
  | [] => σ
  | hd :: tl => attackGameBlocks'!r tl (σ.appendBlock! hd)

def attackGameRGo (requests : List (Request K₁ K₂ C Sigma Pi V))
                  (σ : RollupState K₁ K₂ V C Sigma) : RollupState K₁ K₂ V C Sigma :=
  match requests with
  | [] => []
  | hd :: tl => hd.toBlock! σ :: attackGameRGo tl (σ.appendBlock! hd)

def attackGameR : RollupState K₁ K₂ V C Sigma :=
  σ ++ attackGameRGo requests σ

def attackGameBlocks! (requests : List (Request K₁ K₂ C Sigma Pi V)) : RollupState K₁ K₂ V C Sigma :=
  attackGameBlocks'! requests []

end AttackGameDefs

end

section AttackGameLemmas

end AttackGameLemmas

section AttackGame

variable [Nonempty C] [Finite K₁] [Finite K₂] [Nonempty K₁]
         [Lattice V]
         [AddCommGroup V]
         [CovariantClass V V (· + ·) (· ≤ ·)]
         [CovariantClass V V (Function.swap (· + ·)) (· ≤ ·)]
         [AD : ADScheme K₂ (C × K₁ × ExtraDataT) C Pi]
         [SA : SignatureAggregation (C × K₁ × ExtraDataT) K₂ KₛT Sigma]
         {request : Request K₁ K₂ C Sigma Pi V}
         {requests : List (Request K₁ K₂ C Sigma Pi V)}
         {σ : RollupState K₁ K₂ V C Sigma}

instance : Setoid' ((Pi × ExtraDataT) × TransactionBatch K₁ K₂ V) where
  isEquiv := λ _ _ ↦
    by simp [iso, (·≤·)]
       unfold LE.le Preorder.toLE instPreorderTransactionBatch discretePreorder
       aesop

def normalise (requests : List (Request K₁ K₂ C Sigma Pi V)) : List (Request K₁ K₂ C Sigma Pi V) :=
  requests.filter Request.isValid

def computeBalance' (blocks : RollupState K₁ K₂ V C Sigma) (acc : V) : V :=
  blocks.foldl Block.updateBalance acc

def computeBalance (blocks : RollupState K₁ K₂ V C Sigma) : V :=
  computeBalance' blocks 0

def adversaryWon (blocks : RollupState K₁ K₂ V C Sigma) : Prop :=
  ¬0 ≤ computeBalance blocks

section AttackGameLemmas

variable {request : Request K₁ K₂ C Sigma Pi V}
         {requests : List (Request K₁ K₂ C Sigma Pi V)}
         {σ : RollupState K₁ K₂ V C Sigma}

def aggregateDeposits (σ : RollupState K₁ K₂ V C Sigma) : V :=
  ∑ i : Fin σ.length,
    if h : σ[i].isDepositBlock
    then (σ[i.1].getDeposit h).2.1
    else 0

@[simp]
lemma aggregateDeposits_nil : aggregateDeposits ([] : RollupState K₁ K₂ V C Sigma) = 0 := rfl

@[simp]
lemma aggregateDeposits_cons {hd} {tl : List (Block K₁ K₂ C Sigma V)} :
  aggregateDeposits (hd :: tl) =
  (if h : hd.isDepositBlock
   then (hd.getDeposit h).2.1
   else 0) +
  aggregateDeposits tl := by
  simp [aggregateDeposits]
  rw [
    Finset.sum_fin_eq_sum_range,
    Finset.sum_eq_sum_diff_singleton_add (i := 0),
    dif_pos (show 0 < tl.length + 1 by omega)
  ]
  simp_rw [List.getElem_cons_zero (h := _)]; case h => exact Finset.mem_range.2 (by omega)
  let F : ℕ → V := λ i ↦
    if h : i < tl.length
    then if h_1 : tl[i].isDepositBlock = true
         then (tl[i].getDeposit h_1).2
         else 0
    else 0
  let F' : (a : ℕ) → a ∈ Finset.range (tl.length + 1) \ {0} → ℕ :=
    λ a ha ↦ a.pred
  rw [Finset.sum_bij (t := Finset.range tl.length) (g := F) (i := F')]
  unfold F
  rw [Finset.sum_dite_of_true (λ _ ↦ (Finset.mem_range.1 ·)), Finset.sum_fin_eq_sum_range]
  simp
  nth_rw 2 [Finset.sum_dite_of_true]; case h => exact λ _ ↦ (Finset.mem_range.1 ·)
  rw [add_comm]
  simp
  intros i hi; simp [F']
  simp at hi; rcases i <;> omega
  simp [F']; intros; omega
  simp [F']; intros b hb; use b.succ; simp [hb]
  intros n hn
  simp at hn
  simp [hn]
  rcases n with _ | n <;> [omega; simp [F, F']]
  nth_rw 2 [dif_pos (by rcases hn with ⟨hn, _⟩; omega)]

def aggregateWithdrawals (σ : RollupState K₁ K₂ V C Sigma) : V :=
  ∑ i : Fin σ.length,
    if h : σ[i].isWithdrawalBlock
    then ∑ (k : K₁), (σ[i.1].getWithdrawal h) k
    else 0

def aggregateWithdrawals' (σ : RollupState K₁ K₂ V C Sigma) : V :=
  ∑ (i : Fin σ.length × K₁),
    if h : σ[i.1].isWithdrawalBlock
    then (σ[i.1].getWithdrawal h) i.2
    else 0

lemma aggregateWithdrawals_eq_aggregateWithdrawals' {σ : RollupState K₁ K₂ V C Sigma} :
  aggregateWithdrawals σ = aggregateWithdrawals' σ := by
  unfold aggregateWithdrawals aggregateWithdrawals'
  rw [Fintype.sum_prod_type, Fintype.sum_congr]
  aesop

/--
The 'obvious' `∑ (i : {i : Fin σ.length // σ[i].isDepositBlock}) ...` is slightly clumsy.
-/
def computeBalanceErik (σ : RollupState K₁ K₂ V C Sigma) :=
  let v_deposited : V := aggregateDeposits σ
  let v_withdrawn : V := aggregateWithdrawals σ
  v_deposited - v_withdrawn

@[simp]
lemma computeBalance'_nil : computeBalance' ([] : RollupState K₁ K₂ V C Sigma) v = v := rfl

@[simp]
lemma computeBalance'_cons : computeBalance' (hd :: σ) v =
                             computeBalance' σ (Block.updateBalance v hd) := rfl

lemma computeBalance'_eq_zero : computeBalance' σ v = v + computeBalance' σ 0 := by
  induction' σ with hd tl ih generalizing v
  · simp
  · rw [computeBalance'_cons, computeBalance'_cons, ih, Block.updateBalance_eq_zero]
    nth_rw 2 [ih]
    exact add_assoc v _ _

@[simp]
lemma TransactionsInBlocks_nil {π : BalanceProof K₁ K₂ C Pi V} :
  TransactionsInBlocks π ([] : RollupState K₁ K₂ V C Sigma) = [] := rfl

@[simp]
lemma TransactionsInBlocks_cons {π : BalanceProof K₁ K₂ C Pi V}
                                {hd}
                                {tl : List (Block K₁ K₂ C Sigma V)} :
  TransactionsInBlocks π (hd :: tl) =
  TransactionsInBlock π hd ++ (List.map (TransactionsInBlock π) tl).flatten := rfl

@[simp]
lemma transactionsInBlock_deposit {r : K₂} {v : V₊} :
  TransactionsInBlock (K₁ := K₁) (Sigma := Sigma) π (Block.deposit r v) =
  [⟨(.Source, r, v), by simp [Τ'.isValid]⟩] := by
  unfold TransactionsInBlock
  aesop

section ComputeBalanceErik

variable {k : ℕ}

@[simp]
private def reindex : (a : ℕ) → a ∈ Finset.range (k + 1) \ {0} → ℕ :=
  λ a _ ↦ a.pred

private lemma reindex_mem :
  ∀ (a : ℕ) (ha : a ∈ Finset.range (k + 1) \ {0}), reindex a ha ∈ Finset.range k := by
  simp; omega

private lemma reindex_inj :
  ∀ (a₁ : ℕ) (ha₁ : a₁ ∈ Finset.range (k + 1) \ {0})
    (a₂ : ℕ) (ha₂ : a₂ ∈ Finset.range (k + 1) \ {0}),
  reindex a₁ ha₁ = reindex a₂ ha₂ → a₁ = a₂ := by simp; omega

end ComputeBalanceErik

set_option hygiene false in
open Lean.Elab.Tactic in
scoped elab "blast_sum" "with" f:ident : tactic => do
  evalTactic <| ← `(tactic| (
    simp [d₁, d₂, Finset.sum_fin_eq_sum_range]
    rw [
      Finset.sum_eq_sum_diff_singleton_add (s := Finset.range (tl.length + 1)) (i := 0) eq₁,
      dif_pos (show 0 < tl.length + 1 by omega),
      dif_neg (by rcases hd <;> aesop),
      add_zero
    ]
    rw [Finset.sum_bij (s := _ \ _)
                       (t := Finset.range tl.length)
                       (i := reindex) (g := $f)
                       (hi := reindex_mem)
                       (i_inj := reindex_inj)
                       (i_surj := λ b hb ↦ by use b.succ; simp; exact Finset.mem_range.1 hb)]
    intros n hn
    rw [dif_pos (by simp at hn; exact hn.1)]
    rcases n with _ | n <;> simp at hn
    simp [$f:ident, hn]))

set_option maxHeartbeats 600000 in
private lemma computeBalance'_eq_Erik_aux : computeBalance' σ v = v + computeBalanceErik σ := by
  induction' σ with hd tl ih generalizing v
  · simp [computeBalanceErik, aggregateWithdrawals, aggregateDeposits]
  · rw [computeBalance'_eq_zero]; simp; rw [ih]
    unfold computeBalanceErik aggregateWithdrawals aggregateDeposits
    lift_lets
    intros d₁ w₁ d₂ w₂
    have eq₁ : 0 ∈ Finset.range (tl.length + 1) := by rw [Finset.mem_range]; omega
    have eqd (h : ¬ hd matches .deposit ..) : d₁ = d₂ := by
      simp [d₁, d₂]
      let F : ℕ → V := λ i ↦
        if h : i < tl.length then
          if h_1 : tl[i].isDepositBlock
          then (tl[i].getDeposit h_1).2
          else 0
        else 0
      blast_sum with F
    have eqw (h : ¬ hd matches .withdrawal ..) : w₁ = w₂ := by
      simp [w₁, w₂]
      let F : ℕ → V := λ i ↦
        if h : i < tl.length then
          if h' : tl[i].isWithdrawalBlock
          then ∑ x : K₁, tl[i].getWithdrawal h' x
          else 0
        else 0
      blast_sum with F
    rcases heq : hd
    · have : w₁ = w₂ := eqw (by aesop)
      simp [this, d₁, d₂, add_sub, Finset.sum_fin_eq_sum_range]
      rw [
        Finset.sum_eq_sum_diff_singleton_add (s := Finset.range (tl.length + 1)) (i := 0) eq₁,
        dif_pos (show 0 < tl.length + 1 by omega),
        dif_pos (by aesop)
      ]
      simp_rw [List.getElem_cons_zero, heq]; nth_rw 2 [add_comm]
      refine' congr_arg _ (Eq.symm (Finset.sum_bij (i := reindex)
                                                   (t := Finset.range tl.length)
                                                   (hi := reindex_mem)
                                                   (i_inj := reindex_inj)
                                                   (i_surj := λ b hb ↦ by use b.succ; simp; exact Finset.mem_range.1 hb)
                                                   _))
      simp; rintro a ⟨ha₁, ha₂⟩
      rw [dif_pos ha₁]
      have : a - 1 < tl.length ↔ a < tl.length + 1 := by omega
      simp_rw [this, dif_pos ha₁]
      rcases a with _ | a; simp at ha₂
      simp
    · have eq₁ : d₁ = d₂ := eqd (by aesop)
      have eq₂ : w₁ = w₂ := eqw (by aesop)
      simp [eq₁, eq₂]
    · have eq : d₁ = d₂ := eqd (by aesop)
      rw [add_sub, add_comm, ←add_sub, sub_eq_add_neg (b := w₂)]
      simp [eq, w₁, w₂, Finset.sum_fin_eq_sum_range]
      rw [
        Finset.sum_eq_sum_diff_singleton_add (s := Finset.range (tl.length + 1)) (i := 0) eq₁,
        dif_pos (show 0 < tl.length + 1 by omega),
        dif_pos (by aesop)
      ]
      simp_rw [List.getElem_cons_zero]
      conv_rhs => congr; arg 2; simp [heq]; simp [Block.getWithdrawal]
      rw [neg_add, add_comm, sub_eq_add_neg]
      apply congr_arg
      let F : ℕ → V := λ i ↦
        if h : i < tl.length then
          if h₁ : tl[i].isWithdrawalBlock
          then ∑ x : K₁, tl[i].getWithdrawal h₁ x else 0
        else 0
      rw [Finset.sum_bij (s := _ \ _)
                         (i := reindex)
                         (t := Finset.range tl.length)
                         (g := F)
                         (hi := reindex_mem)
                         (i_inj := reindex_inj)
                         (i_surj := λ b hb ↦ by use b.succ; simp; exact Finset.mem_range.1 hb)]
      simp [F]; intros a ha₁ ha₂
      simp_rw [dif_pos ha₁, show a - 1 < tl.length ↔ a < tl.length + 1 by omega, dif_pos ha₁]
      rcases a with _ | a; simp at ha₂
      simp

lemma computeBalance_eq_sum : computeBalance σ = computeBalanceErik σ := by
  simp [computeBalance, computeBalance'_eq_Erik_aux]

@[simp]
lemma attackGameRGo_nil :
  attackGameRGo ([] : List (Request K₁ K₂ C Sigma Pi V)) σ = [] := rfl

@[simp]
lemma attackGameRGo_cons :
  attackGameRGo (request :: requests) σ =
  request.toBlock! σ :: attackGameRGo requests (σ.appendBlock! request) := rfl

@[simp]
lemma attackGameR_nil :
  attackGameR ([] : List (Request K₁ K₂ C Sigma Pi V)) σ = σ := by simp [attackGameR]

@[simp]
lemma attackGameR_cons :
  attackGameR (request :: requests) σ =
  σ ++ attackGameRGo (request :: requests) σ := rfl

lemma attackGameR_eq_attackGameBlocks' :
  attackGameR requests σ = attackGameBlocks'!r requests σ := by
  induction' requests with hd tl ih generalizing σ
  · unfold attackGameR attackGameBlocks'!r attackGameRGo
    rw [List.append_nil]
  · unfold attackGameR attackGameBlocks'!r
    simp [ih.symm]
    unfold attackGameR
    simp [RollupState.appendBlock!_def]

lemma attackGameBlocks'r_eq_attackGameBlocks' :
  attackGameBlocks'! requests σ = attackGameBlocks'!r requests σ := by
  induction' requests with hd tl ih generalizing σ
  · rfl
  · unfold attackGameBlocks'! attackGameBlocks'!r
    simp [ih.symm]
    rfl

lemma attackGameBlocks_eq_attackGameR :
  attackGameBlocks! requests = attackGameR requests [] := by
  rw [attackGameR_eq_attackGameBlocks']
  rw [←attackGameBlocks'r_eq_attackGameBlocks']
  rfl

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
      rw [ih, RollupState.appendBlock_eq_id_of_not_isValid eq]

lemma attackGame_eq_attackGameBlocks!_normalise :
  attackGame requests = attackGameBlocks! (normalise requests) :=
  attackGameBlocks'_eq_attackGameBlocks'!_normalise

@[simp]
lemma length_attackGameBlocks'! :
  (attackGameBlocks'! requests σ).length = σ.length + requests.length := by
  unfold attackGameBlocks'!
  induction' requests with hd tl ih generalizing σ
  · rfl
  · simp [ih]; omega

@[simp]
lemma length_attackGameBlocks! :
  (attackGameBlocks! requests).length = requests.length := by simp [attackGameBlocks!]

@[simp]
lemma attackGameBlocks'!_cons :
  attackGameBlocks'! (hd :: requests) σ = attackGameBlocks'! requests (σ ++ [hd.toBlock! σ]) := by
  unfold attackGameBlocks'!
  rfl

@[simp]
lemma length_attackGameRGo : (attackGameRGo requests σ).length = requests.length := by
  induction' requests with hd tl ih generalizing σ
  · simp
  · simp [attackGameRGo, ih]

@[simp]
lemma length_attackGameR : (attackGameR requests σ).length = σ.length + requests.length := by
  simp [attackGameR]

lemma attackGameRGo_isWithdrawal_iff (σ σ' : RollupState K₁ K₂ V C Sigma)
                                     (h : i < (attackGameRGo requests σ).length) :
  (attackGameRGo requests σ)[i].isWithdrawalBlock ↔
  (attackGameRGo requests σ')[i].isWithdrawalBlock := by
  simp
  induction' requests with hd tl ih generalizing i σ σ'
  · rfl
  · simp
    rcases i with _ | i
    · simp; unfold Request.toBlock!; aesop
    · aesop

set_option maxHeartbeats 400000 in
private lemma isWithdrawalRequest_of_isWithdrawalBlock_aux
  {σ : RollupState K₁ K₂ V C Sigma}
  {requests : List (Request K₁ K₂ C Sigma Pi V)}
  (h₀ : ∀ request ∈ requests, request.isValid)
  (i : ℕ)
  (hi₁ : σ.length ≤ i)
  (hi₂ : i < (attackGameR requests σ).length)
  (h₁ : ((attackGameR requests σ)[i]'(by simp; simp at hi₂; exact hi₂)).isWithdrawalBlock) :
  (requests[i - σ.length]'(by rcases i with _ | i <;> rcases requests with _ | ⟨hd, tl⟩
                              · simp at hi₂; omega
                              · simp
                              · simp at hi₂; omega
                              · simp at hi₂ ⊢; omega)) matches .withdrawal .. := by
  simp [attackGameR] at h₁
  induction' requests with hd tl ih generalizing i
  · simp at hi₂ h₁; omega
  · rcases i with _ | i
    · simp at hi₁; subst hi₁
      simp at h₁
      simp [Request.toBlock!] at h₁ ⊢; rcases hd <;> simp_all
    · rcases σ with _ | ⟨hd', tl'⟩
      · simp at hi₁ hi₂ h₁ ih ⊢
        apply ih (by aesop) _ hi₂
        rw [attackGameRGo_isWithdrawal_iff (σ' := RollupState.appendBlock! [] hd)]
        exact h₁
      · simp at hi₁ ⊢
        rw [le_iff_eq_or_lt] at hi₁
        rcases hi₁ with hi₁ | hi₁
        · simp_rw [hi₁];
          simp [Request.toBlock!] at h₁ ⊢
          simp_rw [←hi₁] at h₁
          rw [List.getElem_append_right (le_refl _)] at h₁
          rcases hd <;> simp_all
        · rw [lt_iff_exists_add] at hi₁
          rcases hi₁ with ⟨c, ⟨hc₁, hc₂⟩⟩
          simp_rw [hc₂]
          rcases c with _ | c <;> [simp at hc₁; simp]
          specialize ih (by aesop) (c + (hd' :: tl').length); simp at ih
          refine' ih (by simp at hi₂; omega) _
          simp_rw [←Nat.add_assoc]; simp at h₁ ⊢
          simp_rw [
            hc₂, ←Nat.add_assoc,
            List.append_cons (as := tl') (b := Request.toBlock! _ _) (bs := attackGameRGo _ _)
          ] at h₁
          rw [List.getElem_append_right] at h₁ ⊢ <;> simp at h₁ ⊢
          rwa [←attackGameRGo_isWithdrawal_iff]

lemma isWithdrawalRequest_of_isWithdrawalBlock
  {requests : List (Request K₁ K₂ C Sigma Pi V)}
  (h₀ : ∀ request ∈ requests, request.isValid)
  (i : Fin (attackGameR requests []).length)
  (h₁ : ((attackGameR requests [])[i]'(by simp; rcases i with ⟨i, hi⟩; simp at hi; exact hi)).isWithdrawalBlock) :
  (requests[i]'(by rcases i with ⟨h, hi⟩; rcases requests with _ | ⟨hd, tl⟩
                   · simp at hi
                   · simp at hi ⊢; omega)) matches .withdrawal .. := by
  let σ : RollupState K₁ K₂ V C Sigma := []
  have hσ : σ.length = 0 := by simp [σ]
  rcases i with ⟨i, hi⟩; dsimp at h₁ ⊢
  have eq := isWithdrawalRequest_of_isWithdrawalBlock_aux (σ := [])
                                                          (requests := requests)
                                                          h₀
                                                          (i + σ.length)
                                                          (zero_le _)
                                                          (hσ ▸ hi)
  aesop

def getBalanceProof (requests : List (Request K₁ K₂ C Sigma Pi V))
                    (h₀ : ∀ request ∈ requests, request.isValid)
                    (i : Fin (attackGameR requests []).length)
                    (h₁ : (attackGameR requests [])[i].isWithdrawalBlock) :
                    BalanceProof K₁ K₂ C Pi V :=
  let request := requests[i]'(by rcases i with ⟨i, hi⟩; simp at hi; exact hi)
  have : request.getWithdrawal.isSome := by
    rw [Request.getWithdrawal_isSome]
    dsimp only [request]
    have := isWithdrawalRequest_of_isWithdrawalBlock (requests := requests) h₀ i h₁
    aesop
  request.getWithdrawal.get this

def isπ (requests : List (Request K₁ K₂ C Sigma Pi V)) :=
  ∀ (h₀ : ∀ request ∈ requests, request.isValid)
    (i : Fin (attackGameR requests []).length)
    (h : (attackGameR requests [])[i].isWithdrawalBlock),
    (attackGameR requests [])[i].getWithdrawal h =
    let π := getBalanceProof requests h₀ i h
    let σ := (attackGameR requests []).take i.1
    π.toBalanceF σ

end AttackGameLemmas

set_option maxHeartbeats 1000000 in
private lemma lemma5_aux {len : ℕ} {σ : RollupState K₁ K₂ V C Sigma}
  (hlen : len = σ.length) :
  (Bal π σ) Kbar.Source =
  (∑ x ∈ (Finset.univ : Finset (Fin σ.length)) ×ˢ Finset.univ,
      if h : σ[x.1].isWithdrawalBlock then
        (σ[x.1].getWithdrawal h x.2).1 ⊓ ((Bal π (List.take (x.1.1) σ)) x.2)
      else 0) -
  ∑ i : Fin (List.length σ), if h : σ[i].isDepositBlock then (σ[↑i].getDeposit h).2 else 0 := by
  induction' len with k ih generalizing σ
  · rcases σ <;> aesop
  · obtain ((_ | _) | ⟨bs, b, ⟨⟩⟩) := List.eq_nil_or_concat' σ <;> [simp at hlen; skip]
    unfold Bal fStar
    simp only [
      transactionsInBlocks_append_singleton, List.foldl_append, Finset.univ_product_univ, Fin.getElem_fin,
      Fintype.sum_prod_type, Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range,
      List.length_append, List.length_singleton
    ]
    simp_rw [
      Finset.sum_eq_sum_diff_singleton_add
        (show bs.length ∈ Finset.range (bs.length + 1) by rw [Finset.mem_range]; omega),
      dif_pos (show bs.length < bs.length + 1 by omega),
      show Finset.range (bs.length + 1) \ {bs.length} = Finset.range bs.length by
              rw [Finset.range_succ, Finset.insert_eq, Finset.union_sdiff_cancel_left (by simp)
    ]]
    rcases hb : b with ⟨r, v⟩ | ⟨x₁, x₂, x₃, x₄, x₅⟩ | ⟨B⟩
    · erw [
        f_deposit_source'' (b := b) (h := by aesop) (π := π) (h₁ := by aesop),
        ih (show k = bs.length by simp at hlen; exact hlen)
      ]
      simp only [Finset.univ_eq_attach, id_eq, Int.reduceNeg, Int.Nat.cast_ofNat_Int,
        eq_mpr_eq_cast, List.getElem_concat_length, Block.deposit_ne_widthdrawal, ↓reduceDIte,
        Finset.sum_const_zero, add_zero]
      rw [sub_add]
      congr 1
      /-
        IH matches rhs.
      -/
      · simp only [Finset.univ_product_univ, Fin.getElem_fin, Finset.univ_eq_attach, id_eq,
          Int.reduceNeg, Int.Nat.cast_ofNat_Int, eq_mpr_eq_cast, Fintype.sum_prod_type,
          Finset.sum_fin_eq_sum_range]
        refine' Finset.sum_congr rfl (λ idx hidx ↦ _)
        have hlen : idx < bs.length := Finset.mem_range.1 hidx
        simp_rw [dif_pos hlen, dif_pos (Nat.lt_add_one_of_lt hlen)]
        refine' Finset.sum_congr rfl (λ k hk ↦
                  dite_congr (by rw [List.getElem_append_left hlen]) (λ h ↦ _) (by simp))
        congr 2
        · have : bs[idx] = (bs ++ [Block.deposit r v])[idx]'(by simp; omega) := by
            rw [List.getElem_append_left hlen]
          simp_rw [this]
        · have : List.take idx (bs ++ [Block.deposit r v]) = List.take idx bs := by
            rw [List.take_append_of_le_length (by omega)]
          simp_rw [this]
          rfl
      /-
        Rest matches rhs.
      -/
      · rw [Finset.sum_fin_eq_sum_range]
        simp only [Fin.getElem_fin, Block.getDeposit, Τ.value, Option.get_some, sub_neg_eq_add,
          List.length_singleton, add_left_inj]
        refine' (Finset.sum_congr rfl (λ idx hidx ↦ _))
        have hlen : idx < bs.length := Finset.mem_range.1 hidx
        have : (bs ++ [Block.deposit r v])[idx]'(by simp; omega) = bs[idx] := by
          rw [List.getElem_append_left hlen]
        
        refine' dite_congr (by simp [hlen]; omega) (λ h ↦ (dite_congr (by simp [this]) (λ h ↦ _) (by simp))) (by simp)
        split; split; aesop
    · rw [f_transfer_block_source' (by simp)]
      erw [ih (show k = bs.length by simp at hlen; exact hlen)]
      congr 1
      /-
        IH matches rhs
      -/
      · simp only [
          Finset.univ_product_univ, Fin.getElem_fin, Fintype.sum_prod_type, Finset.sum_fin_eq_sum_range,
          List.length_append, List.length_singleton
        ]
        nth_rw 3 [Finset.sum_dite_of_false (by simp)]
        simp only [Finset.sum_dite_irrel, Finset.sum_const_zero, add_zero]
        refine' Finset.sum_congr rfl (λ idx hidx ↦ _)
        have hlen : idx < bs.length := Finset.mem_range.1 hidx
        refine' dite_congr
                  (by simp [hidx]; omega)
                  (λ _ ↦ dite_congr (by rw [List.getElem_append_left hlen])
                                    (λ _ ↦ Finset.sum_congr rfl λ _ _ ↦ _)
                                    (by simp))
                  (by simp)
        congr 2
        · have : bs[idx] = (bs ++ [Block.transfer x₁ x₂ x₃ x₄ x₅])[idx]'(by simp; omega) := by
            rw [List.getElem_append_left hlen]
          simp_rw [List.getElem_append_left hlen]
        · have : List.take idx (bs ++ [Block.transfer x₁ x₂ x₃ x₄ x₅]) = List.take idx bs := by
            rw [List.take_append_of_le_length (by omega)]
          simp_rw [this]
          rfl
      /-
        Rest matches rhs.
      -/
      · simp only [Fin.getElem_fin, Finset.sum_fin_eq_sum_range, List.length_append, List.length_singleton]
        simp only [List.getElem_concat_length, Block.transfer_ne_deposit, ↓reduceDIte, add_zero]
        refine' (Finset.sum_congr rfl (λ idx hidx ↦ _))
        have hlen : idx < bs.length := Finset.mem_range.1 hidx
        have : (bs ++ [Block.transfer x₁ x₂ x₃ x₄ x₅])[idx]'(by simp; omega) = bs[idx] := by
          rw [List.getElem_append_left hlen]
        exact dite_congr (by simp [hlen]; omega)
                         (λ _ ↦ (dite_congr (by simp [this]) (λ _ ↦ by simp_rw [this]) (by simp)))
                         (by simp)
    · rw [f_withdrawal_block_source' (by simp)]
      erw [ih (show k = bs.length by simp at hlen; exact hlen)]
      simp only [
        Finset.univ_product_univ, Fin.getElem_fin, Finset.sum_fin_eq_sum_range, Fintype.sum_prod_type,
        List.length_append, List.length_singleton, Finset.sum_dite_irrel, Finset.sum_const_zero]
      nth_rw 2 [dif_neg (by simp)]
      simp only [List.getElem_concat_length, ↓reduceDIte, List.take_left', add_zero]
      rw [sub_add, ←add_sub, sub_eq_add_neg]
      congr 1
      /-
        IH matches rhs.
      -/
      · refine' Finset.sum_congr rfl (λ idx hidx ↦ _)
        have hlen : idx < bs.length := Finset.mem_range.1 hidx
        simp_rw [dif_pos hlen, dif_pos (Nat.lt_add_one_of_lt hlen)]
        have : (bs ++ [Block.withdrawal B])[idx]'(by simp; omega) = bs[idx] := by
          rw [List.getElem_append_left hlen]
        simp_rw [this]
        refine' dite_congr rfl (λ h₁ ↦ Finset.sum_congr rfl (λ i hi ↦ _)) (by simp)
        have : List.take idx (bs ++ [Block.withdrawal B]) = List.take idx bs := by
          rw [List.take_append_of_le_length (by omega)]
        simp_rw [this]
        rfl
      /-
        Rest matches rhs.
      -/
      · simp only [neg_sub, sub_right_inj]
        refine' Finset.sum_congr rfl (λ idx hidx ↦ _)
        have hlen : idx < bs.length := Finset.mem_range.1 hidx
        exact dite_congr
                (by simp [hidx]; omega)
                (λ h ↦ dite_congr (by rw [List.getElem_append_left hlen])
                                  (λ h₁ ↦ by simp_rw [List.getElem_append_left hlen])
                                  (by simp))
                (by simp)

lemma lemma5 (π : BalanceProof K₁ K₂ C Pi V) :
  Bal π σ .Source =
  (∑ (i : Fin σ.length) (k : K₁),
     if h : σ[i].isWithdrawalBlock
     then let w := σ[i].getWithdrawal h
          w k ⊓ Bal π (σ.take i.1) k
     else 0)
  -
  aggregateDeposits σ := lemma5_aux (len := σ.length) rfl

variable -- [ADScheme K₂ (C × K₁ × ExtraDataT) C Pi]
         [Hinj : CryptoAssumptions.Injective (H (α := TransactionBatch K₁ K₂ V × ExtraDataT) (ω := (C × K₁ × ExtraDataT)))]
         (isπ : isπ (normalise requests))

def BalanceProof.initial : BalanceProof K₁ K₂ C Pi V := λ _ ↦ .none

@[simp]
lemma Merge_initial {π : BalanceProof K₁ K₂ C Pi V} :
  BalanceProof.initial.Merge π = π := by
  rw [Dict.keys_Merge_right']
  intros x contra
  unfold BalanceProof.initial at contra
  rw [Dict.mem_iff_isSome] at contra
  simp at contra

@[simp]
lemma BalanceProof.valid_initial :
  BalanceProof.initial.Verify (K₁ := K₁) (AD := AD) (K₂ := K₂) (V := V) (M := (C × K₁ × ExtraDataT)) := by
  simp [Verify, Dict.keys, Dict.is_mem, initial]

@[simp]
lemma BalanceProof.le_initial {k} {π : BalanceProof K₁ K₂ C Pi V} :
  BalanceProof.initial k ≤ π k := by
  unfold initial
  simp [(·≤·)]
  aesop

@[simp]
lemma BalanceProof.IsBot_initial : IsBot (BalanceProof.initial : BalanceProof K₁ K₂ C Pi V) := by
  unfold initial; simp [IsBot, (·≤·)]; intros a b; aesop

lemma proposition4W {x y : Option ((Pi × ExtraDataT) × TransactionBatch K₁ K₂ V)}
  (h : x.isSome ∧ y.isSome → x = y) : IsLUB {x, y} (Dict.First x y) := by
  simp [IsLUB, IsLeast, lowerBounds, Dict.First]
  aesop

@[simp]
lemma BalanceProof.snd_discrete {x y : TransactionBatch K₁ K₂ V} :
  @LE.le (TransactionBatch K₁ K₂ V) Preorder.toLE x y ↔ x = y := by
  unfold LE.le Preorder.toLE instPreorderTransactionBatch
  aesop

instance : Setoid' ((Pi × ExtraDataT) × TransactionBatch K₁ K₂ V) where
  isEquiv := by unfold IsEquivRel
                intros a b
                unfold iso
                simp [(·≤·)]
                aesop

lemma setoid_rewrite_LUB {X : Type} {s : Set X} [Setoid' X] {x y : X} (h₁ : IsLUB s x) (h₂ : x ≅ y) :
  IsLUB s y := by
  simp [IsLUB, IsLeast, lowerBounds, upperBounds] at h₁ ⊢
  rcases h₁ with ⟨h₃, h₄⟩; split_ands
  · intros x' hx
    specialize @h₃ x' hx
    specialize @h₄ x'
    apply iso_trans <;> assumption
  · intros x' hx
    specialize @h₄ x' hx
    rw [iso_symm] at h₂
    apply iso_trans <;> assumption

def mergeR (πs : List (BalanceProof K₁ K₂ C Pi V)) (n : ℕ) : BalanceProof K₁ K₂ C Pi V :=
  if _ : n < πs.length.succ
  then match n with
       | 0 => .initial
       | k + 1 => Dict.Merge (mergeR πs k) πs[k]
  else .initial

def mergeR' (πs : List (BalanceProof K₁ K₂ C Pi V)) : Fin πs.length.succ → BalanceProof K₁ K₂ C Pi V :=
  λ i ↦ match h : i.1 with
        | 0 => .initial
        | k + 1 => Dict.Merge (mergeR' πs ⟨k, by rcases i; omega⟩) πs[k]
  termination_by i => i
  decreasing_by { simp_wf; next m => rcases m; aesop }

def mergeR'' (πs : List (BalanceProof K₁ K₂ C Pi V)) (acc : BalanceProof K₁ K₂ C Pi V) : BalanceProof K₁ K₂ C Pi V :=
  match πs with
  | [] => acc
  | π :: πs => Dict.Merge acc (mergeR'' πs π)

@[simp]
lemma mergeR''_nil {acc : BalanceProof K₁ K₂ C Pi V} : mergeR'' [] acc = acc := rfl

def mergeR''' (πs : List (BalanceProof K₁ K₂ C Pi V)) (acc : BalanceProof K₁ K₂ C Pi V) : BalanceProof K₁ K₂ C Pi V :=
  πs.foldl Dict.Merge acc

instance : Std.Associative
             (Dict.Merge (α := (C × K₂)) (ω := ((Pi × ExtraDataT) × TransactionBatch K₁ K₂ V))) :=
  ⟨λ _ _ _ ↦ Dict.Merge_assoc⟩

lemma mergeR''_eq_foldl {πs : List (BalanceProof K₁ K₂ C Pi V)} {acc} :
  mergeR'' πs acc = mergeR''' πs acc := by
  induction' πs with hd tl ih generalizing acc
  · rfl
  · unfold mergeR'' mergeR'''
    simp
    rw [List.foldl_assoc]
    rw [ih]
    conv_lhs => unfold mergeR'''

@[simp]
lemma mergeR''_cons {π} {πs : List (BalanceProof K₁ K₂ C Pi V)} {acc} :
  mergeR'' (π :: πs) acc =  Dict.Merge acc (mergeR'' πs π) := rfl

def P : BalanceProof K₁ K₂ C Pi V → Prop :=
  λ π ↦ True

lemma P_initial : P (.initial : BalanceProof K₁ K₂ C Pi V) := by trivial

@[simp]
lemma mem_list_singleton_iff {π} : π ∈ ({acc} : List (BalanceProof K₁ K₂ C Pi V)) ↔ π = acc := by
  simp [singleton]

def BalanceProof.compat (π₁ π₂ : BalanceProof K₁ K₂ C Pi V) : Prop :=
  ∀ k, π₁ k ≠ none ∧ π₂ k ≠ none → π₁ k ≅ π₂ k

notation:51 π₁:52 " <≅> " π₂:52 => BalanceProof.compat π₁ π₂

notation:65 π₁:65 " <+> " π₂:66 => Dict.Merge π₁ π₂

section compat

@[symm]
lemma BalanceProof.compat_comm {π₁ π₂ : BalanceProof K₁ K₂ C Pi V} :
  π₁ <≅> π₂ ↔ π₂ <≅> π₁ := by unfold BalanceProof.compat; simp_rw [iso_symm]; tauto

lemma Merge_comm_of_compat {π₁ π₂ : BalanceProof K₁ K₂ C Pi V}
  (h : π₁ <≅> π₂) : π₁ <+> π₂ ≅ π₂ <+> π₁ := by
  apply proposition5'
  have := proposition6_aux h
  exact this
  unfold Dict.Merge Dict.Merge.D Dict.First
  have h₁ := BalanceProof.compat_comm.1 h
  intros x; specialize h x; specialize h₁ x
  aesop

lemma Merge_iso_of_iso {π₁ π₂ π₃ : BalanceProof K₁ K₂ C Pi V} (h : π₁ ≅ π₂) :
  π₁ <+> π₃ ≅ π₂ <+> π₃ := by
  simp [iso] at *
  unfold LE.le Preorder.toLE instPreorderBalanceProof id inferInstance _root_.Pi.preorder at *
  simp [inferInstanceAs, id, _root_.Pi.hasLe, -Prod.forall] at *
  rcases h with ⟨h₁, h₂⟩
  unfold Dict.Merge Dict.Merge.D Dict.First
  split_ands <;> intros x <;> specialize h₁ x <;> specialize h₂ x <;> aesop

lemma Merge_mergeR''_comm {πs : List (BalanceProof K₁ K₂ C Pi V)} (h : π <≅> acc) :
  acc <+> (mergeR'' πs π) ≅ π <+> (mergeR'' πs acc) := by
  induction' πs with hd tl ih generalizing acc
  · simp; exact Merge_comm_of_compat (BalanceProof.compat_comm.1 h)
  · simp
    rw [←Dict.Merge_assoc]
    rw [←Dict.Merge_assoc]
    exact Merge_iso_of_iso (Merge_comm_of_compat (BalanceProof.compat_comm.1 h))

lemma existsLUB_iff_compat {π₁ π₂ : BalanceProof K₁ K₂ C Pi V} :
  (∃ join, IsLUB {π₁, π₂} join) ↔ π₁ <≅> π₂ := proposition6

lemma le_of_iso {π₁ π₂ π₃ : BalanceProof K₁ K₂ C Pi V} (h : π₂ ≅ π₃) (h₁ : π₁ ≤ π₂) : π₁ ≤ π₃ :=
  le_trans h₁ h.1

lemma le_of_iso' {π₁ π₂ π₃ : BalanceProof K₁ K₂ C Pi V} (h : π₁ ≅ π₂) (h₁ : π₂ ≤ π₃) : π₁ ≤ π₃ :=
  le_trans h.1 h₁

@[simp]
lemma snd_eq_of_iso {d₁ d₂ : (Pi × ExtraDataT) × TransactionBatch K₁ K₂ V} :
  d₁.2 = d₂.2 ↔ (d₁ ≅ d₂) := by
  unfold iso
  simp [(·≤·)]
  tauto

lemma compat_of_iso {π π' : BalanceProof K₁ K₂ C Pi V}
  (h : π ≅ π') : π <≅> π' := by
  intros x y
  simp [iso] at h
  unfold LE.le Preorder.toLE instPreorderBalanceProof id inferInstance _root_.Pi.preorder at h
  simp [-Prod.forall, inferInstanceAs, _root_.Pi.hasLe] at h
  rcases h with ⟨h₁, h₂⟩
  specialize h₁ x
  specialize h₂ x
  unfold iso
  tauto

lemma isLUB_of_isLUB_iso {π π' : BalanceProof K₁ K₂ C Pi V}
  (h : IsLUB A π) (h₁ : π ≅ π') : IsLUB A π' := by
  simp only [IsLUB, IsLeast, upperBounds, Set.mem_setOf_eq, lowerBounds] at *
  rcases h with ⟨h₂, h₃⟩
  split_ands
  · intros X hX
    have : X ≤ π := h₂ hX
    exact le_trans this h₁.1
  · intros X hX
    specialize h₃ hX
    exact le_trans h₁.2 h₃

end compat

lemma merge_le {π₁ π₂ π₃ : BalanceProof K₁ K₂ C Pi V}
  (h₁ : π₁ ≤ π₃) (h₂ : π₂ ≤ π₃) : π₁ <+> π₂ ≤ π₃ := by
  have h₃ : π₁ <≅> π₂ := by
    intros k hk
    simp [-Prod.forall, (·≤·)] at h₁ h₂
    specialize h₁ k
    specialize h₂ k
    aesop (config := {warnOnNonterminal := false})
    exact iso_trans h₁ h₂.symm
  obtain ⟨π, hπ⟩ := existsLUB_iff_compat.2 h₃
  have hπ' := hπ
  apply proposition6' at hπ
  have eq₁ : π₁ ≤ π := by unfold IsLUB IsLeast upperBounds lowerBounds at hπ'; aesop
  have eq₂ : π₂ ≤ π := by unfold IsLUB IsLeast upperBounds lowerBounds at hπ'; aesop
  transitivity π
  exact hπ.symm.1
  have eq₃ := hπ.2
  unfold IsLUB IsLeast upperBounds lowerBounds at hπ'
  rcases hπ' with ⟨hπ₁, hπ₂⟩
  simp at hπ₂
  apply hπ₂ <;> assumption

lemma isLUB_union_Merge_of_isLUB_isLUB_compat {A B : Set (BalanceProof K₁ K₂ C Pi V)}
  (h₁ : IsLUB A j₁) (h₂ : IsLUB B j₂) (h₃ : j₁ <≅> j₂) : IsLUB (A ∪ B) (j₁ <+> j₂) := by
  have h₃'' := h₃
  obtain ⟨j, h₃⟩ := existsLUB_iff_compat.2 h₃
  split_ands
  · simp only [IsLUB, IsLeast, upperBounds, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq, Set.mem_setOf_eq, lowerBounds, and_imp, Set.mem_union] at h₁ h₂ h₃ ⊢
    rcases h₁ with ⟨h₁, h₁'⟩
    rcases h₂ with ⟨h₂, h₂'⟩
    rintro D₁ (hD₁ | hD₂)
    · simp [-Prod.forall, (·≤·)]
      intros x
      unfold Dict.Merge Dict.Merge.D Dict.First
      specialize h₁ hD₁
      simp [-Prod.forall, (·≤·)] at h₁
      specialize h₁ x
      set d₁ := D₁ x with eqX
      set d₂ := j₁ x with eqY
      set d₃ := j₂ x with eqZ
      rcases d₁ with _ | d₁ <;> rcases d₂ with _ | d₂ <;> rcases d₃ with _ | d₃ <;> simp
      · simp at h₁
      · simp at h₁
      · simp at h₁
        exact h₁
      · simp at h₁
        exact h₁
    · simp only [LE.le, discretePreorder_eq_equality_Pi_Prod_ExtraDataT, BalanceProof.snd_discrete,]
      intros x
      unfold Dict.Merge Dict.Merge.D Dict.First
      have eq₂ : D₁ ≤ j₂ := h₂ hD₂
      simp [-Prod.forall, (·≤·)] at eq₂
      specialize eq₂ x
      set d₁ := D₁ x with eqX
      set d₂ := j₁ x with eqY
      set d₃ := j₂ x with eqZ
      rcases d₁ with _ | d₁ <;> rcases d₂ with _ | d₂ <;> rcases d₃ with _ | d₃ <;> simp
      · simp at eq₂
      · simp at eq₂
        exact eq₂
      · simp at eq₂
      · simp at eq₂
        specialize h₃'' x
        rw [←eqY, ←eqZ] at h₃''
        simp at h₃''
        exact iso_trans eq₂ h₃''.symm
  · exact λ _ hπ ↦ merge_le (h₁.right λ _ hd ↦ hπ (by tauto))
                            (h₂.right λ _ hd ↦ hπ (by tauto))

@[simp]
lemma merge_eq_none {π acc : BalanceProof K₁ K₂ C Pi V} :
  (π <+> acc) K = none ↔ π K = none ∧ acc K = none := by
  unfold Dict.Merge Dict.Merge.D Dict.First; aesop

@[simp]
lemma mergeR''_eq_none' {acc : BalanceProof K₁ K₂ C Pi V} {πs} :
  (mergeR'' πs acc) K = none ↔ acc K = none ∧ ∀ π ∈ πs, π K = none := by
  induction' πs with hd tl ih generalizing acc <;> aesop

lemma merge_K {π acc : BalanceProof K₁ K₂ C Pi V} :
  (π <+> acc) K = Dict.First (π K) (acc K) := rfl

lemma iso_K_merge_left_of_ne_none {π acc : BalanceProof K₁ K₂ C Pi V} (h : π K ≠ none) : 
  π K ≅ (π <+> acc) K := by
  rw [merge_K]
  unfold Dict.First
  aesop

lemma iso_K_merge_right_of_ne_none_compat {π acc : BalanceProof K₁ K₂ C Pi V} (h : π K ≠ none) (h : π <≅> acc) : 
  π K ≅ (acc <+> π) K := by
  unfold BalanceProof.compat at h
  specialize h K
  rw [merge_K]
  unfold Dict.First
  aesop

lemma iso_K_of_iso {π acc : BalanceProof K₁ K₂ C Pi V} (h : π ≅ acc) : π K ≅ acc K := by
  unfold iso LE.le Preorder.toLE instPreorderBalanceProof id inferInstance _root_.Pi.preorder inferInstanceAs _root_.Pi.hasLe at h
  simp [-Prod.forall] at h
  tauto

lemma mergeR_eq_left {acc : BalanceProof K₁ K₂ C Pi V}
  (h : ∀ k, acc k ≠ none) : mergeR'' πs acc = acc := by
  unfold mergeR''
  rcases πs with _ | ⟨π, πs⟩
  · simp
  · simp
    rw [Dict.keys_Merge_left']
    simp_rw [Dict.mem_iff_isSome, Option.isSome_iff_ne_none]
    exact h

-- IsLUB {π | π ∈ πs} (mergeR'' πs ⊥)

lemma proposition6_pog {πs : List (BalanceProof K₁ K₂ C Pi V)}
                       {acc : BalanceProof K₁ K₂ C Pi V}
                       (h : ∀ {π₁ π₂ : BalanceProof K₁ K₂ C Pi V},
                              π₁ ∈ {acc} ∪ πs  →
                              π₂ ∈ {acc} ∪ πs →
                              π₁ <≅> π₂) :
  IsLUB {π | π ∈ {acc} ∪ πs} (mergeR'' πs acc) ∧
  ∀ x, (mergeR'' πs acc x = .none ∧ ∀ π ∈ {acc} ∪ πs, π x = .none) ∨
       (mergeR'' πs acc x ≠ .none ∧ ∀ π ∈ {acc} ∪ πs,
                                      π x = .none ∨ π x ≅ mergeR'' πs acc x) := by
  induction' πs with π πs ih generalizing acc
  · sorry
  · simp only [
      List.mem_union_iff, List.mem_cons, mergeR''_cons, List.cons_union,
      List.mem_insert_iff, forall_eq_or_imp, mem_list_singleton_iff]
    have ih' := @ih
    have ih'' := @ih
    specialize @ih acc ?compat
    case compat =>
      intros π₁ π₂ h₁ h₂ k hk
      specialize @h π₁ π₂ (by simp at h₁ ⊢; tauto) (by simp at h₂ ⊢; tauto)
      exact h _ hk
    
    simp_rw [show {π_1 | π_1 ∈ {acc} ∪ πs} = {acc} ∪ {π | π ∈ πs} by simp; rfl] at ih
    rcases ih with ⟨ih₁, ih₂⟩
    refine' ⟨_, _⟩
    · have : {π_1 | π_1 = acc ∨ π_1 = π ∨ π_1 ∈ πs} =
             {π} ∪ ({acc} ∪ {π | π ∈ πs}) := (by simp; rw [Set.insert_comm]; ac_rfl); simp_rw [this]; clear this
      have : acc <+> (mergeR'' πs π) ≅ π <+> (mergeR'' πs acc) := Merge_mergeR''_comm (h (by simp) (by simp))
      apply isLUB_of_isLUB_iso _ this.symm
      refine' isLUB_union_Merge_of_isLUB_isLUB_compat (by simp) ih₁ _
      -- π <≅> mergeR'' πs acc
      sorry
    · intros K
      by_cases eq : (acc <+> mergeR'' πs π) K = .none
      · simp [eq]; simp at eq; exact eq
      · simp [eq]; simp at eq
        split_ands
        · by_cases eq? : acc K = none
          · simp [eq?]
          · simp [eq?]
            apply iso_K_merge_left_of_ne_none eq?
        · by_cases eq? : π K = none
          · simp [eq?]
          · simp [eq?]
            have t₁ : acc <+> (mergeR'' πs π) ≅ π <+> (mergeR'' πs acc) := Merge_mergeR''_comm (h (by simp) (by simp))
            have t₂ := iso_K_merge_left_of_ne_none (acc := mergeR'' πs acc) eq?
            apply iso_K_of_iso (K := K) at t₁
            exact iso_trans t₂ t₁.symm
        · intros π' hπ'
          by_cases eq? : π' K = none
          · tauto
          · simp [eq?]
            specialize @ih'' π' ?compat
            case compat =>
              intros π₁ π₂ h₁ h₂ k hk
              specialize @h π₁ π₂ (by simp at h₁ ⊢; rcases h₁ with h₁ | h₁ <;> (try rw [h₁]) <;> tauto)
                                  (by simp at h₂ ⊢; rcases h₂ with h₁ | h₁ <;> (try rw [h₁]) <;> tauto)
              exact h _ hk
            rcases ih'' with ⟨ih''₁, ih''₂⟩
            specialize ih''₂ K
            simp [eq?] at ih''₂
            rcases ih''₂ with ⟨ih''₂, ih''₃⟩
            apply iso_trans ih''₂
            -- acc <≅> mergeR'' πs π
            sorry

lemma mergeR'_eq_mergeR_of_lt {πs : List (BalanceProof K₁ K₂ C Pi V)} {n : ℕ}
                              (h : n < πs.length.succ) :
  mergeR' πs ⟨n, h⟩ = mergeR πs n := by
  induction' n with hd tl ih <;> unfold mergeR' mergeR <;> aesop

lemma mergeR'_zero {πs : List (BalanceProof K₁ K₂ C Pi V)} (h : 0 < πs.length.succ) :
  mergeR' πs ⟨0, h⟩ = .initial := by
  unfold mergeR'
  aesop

lemma mergeR'_succ {πs : List (BalanceProof K₁ K₂ C Pi V)} {n : ℕ} (h : n + 1 < πs.length.succ) :
  mergeR' πs ⟨n + 1, h⟩ = (mergeR' πs ⟨n, by omega⟩).Merge (πs[n]) := by
  conv_lhs => unfold mergeR'

lemma verify_merge_of_valid {π₁ π₂ : BalanceProof K₁ K₂ C Pi V}
                            (h₁ : π₁.Verify (M := (C × K₁ × ExtraDataT)))
                            (h₂ : π₂.Verify (M := (C × K₁ × ExtraDataT))) :
                            BalanceProof.Verify (M := (C × K₁ × ExtraDataT)) (Dict.Merge π₁ π₂) := by
  simp [-Prod.forall, BalanceProof.Verify, iInf_subtype] at *
  intros k h
  rcases h with h | h
  · simp_rw [Dict.keys_Merge_left (D₂ := π₂) h]; aesop
  · by_cases h₁ : k ∈ π₁.keys
    · simp_rw [Dict.keys_Merge_left (D₂ := π₂) h₁]
      aesop
    · simp_rw [Dict.keys_Merge_right (D₂ := π₂) h₁ h]
      aesop

lemma valid_mergeR' {πs : List (BalanceProof K₁ K₂ C Pi V)} {n : Fin πs.length.succ}
  (h : ∀ π ∈ πs, π.Verify (M := (C × K₁ × ExtraDataT))) :
  (mergeR' πs n).Verify (M := (C × K₁ × ExtraDataT)) := by
  rcases n with ⟨n, hn⟩
  induction' n with n ih generalizing πs
  · unfold mergeR'; aesop (add safe apply List.getElem_mem)
  · rw [mergeR'_succ]
    apply verify_merge_of_valid (ih _ _) <;> aesop (add safe apply List.getElem_mem)

private lemma valid_mergeR''_aux {π : BalanceProof K₁ K₂ C Pi V}
                                 {πs : List (BalanceProof K₁ K₂ C Pi V)}
                                 {n : ℕ}
  (hn : n < πs.length.succ)
  (h₀ : π.Verify (M := (C × K₁ × ExtraDataT)))
  (h : ∀ π ∈ πs, π.Verify (M := (C × K₁ × ExtraDataT))) :
  (mergeR'' (πs.take n) π).Verify (M := (C × K₁ × ExtraDataT)) := by
  induction' n with n ih generalizing π πs <;> unfold mergeR''
  · aesop
  · rcases πs with _ | ⟨π', πs'⟩
    · simp at hn
    · apply verify_merge_of_valid h₀ (ih _ _ _) <;> aesop

lemma valid_mergeR'' {πs : List (BalanceProof K₁ K₂ C Pi V)} {n : ℕ}
  (hn : n < πs.length.succ)
  (h : ∀ π ∈ πs, π.Verify (M := (C × K₁ × ExtraDataT))) :
  (mergeR'' (πs.take n) .initial).Verify (M := (C × K₁ × ExtraDataT)) :=
  valid_mergeR''_aux hn (by simp) h

lemma le_Merge_of_le_le
        {π π₁ π₂ : BalanceProof K₁ K₂ C Pi V}
        {k : C × K₂}
        (h : π k ≤ π₁ k)
        (h₁ : π k ≤ π₂ k) :
        π k ≤ Dict.Merge π₁ π₂ k := by
  unfold Dict.Merge Dict.Merge.D Dict.First
  aesop

lemma le_mergeR''_aux {π acc : BalanceProof K₁ K₂ C Pi V}
                      {πs : List (BalanceProof K₁ K₂ C Pi V)}
                      {k : C × K₂}
                      (h₀ : π k ≤ acc k)
                      (h : ∀ acc : BalanceProof K₁ K₂ C Pi V, acc ∈ πs → π k ≤ acc k) :
                      π k ≤ mergeR'' πs acc k := by
  induction' πs with hd tl ih generalizing π acc
  · simp [mergeR'', h, h₀]
  · simp
    apply le_Merge_of_le_le h₀
    aesop

lemma batch_eq_iff {π₁k π₂k : (Pi × ExtraDataT) × TransactionBatch K₁ K₂ V} :
  (π₁k ≅ π₂k) ↔ π₁k.2 = π₂k.2 := by
  unfold iso
  simp [(·≤·)]
  rw [iso_symm]
  tauto

lemma batch?_eq_of_mem {π₁k π₂k : Option ((Pi × ExtraDataT) × TransactionBatch K₁ K₂ V)}
  (h₀ : π₁k ≠ .none ∨ π₂k ≠ .none)
  (h : π₁k ≅ π₂k) : (π₁k.get (by unfold iso at h
                                 simp [(·≤·)] at h
                                 aesop)).2 =
                    (π₂k.get (by unfold iso at h
                                 simp [(·≤·)] at h
                                 aesop)).2 := by
  unfold iso at h
  simp [(·≤·)] at h
  aesop

lemma batch?_neq_of_mem {π₁k π₂k : Option ((Pi × ExtraDataT) × TransactionBatch K₁ K₂ V)}
  (h₀ : π₁k ≠ .none ∧ π₂k ≠ .none)
  (h : ¬(π₁k ≅ π₂k)) : (π₁k.get (Option.isSome_iff_ne_none.2 h₀.1)).2 ≠
                       (π₂k.get (Option.isSome_iff_ne_none.2 h₀.2)).2 := by
  rcases π₁k <;> rcases π₂k <;> aesop

#exit

include isπ in
set_option maxHeartbeats 2000000 in
theorem theorem1 : ¬adversaryWon (attackGame requests) := λ contra ↦ by
  /-
    The attack game plays out the same regardless of validity of requests.
  -/
  rw [attackGame_eq_attackGameBlocks!_normalise, attackGameBlocks_eq_attackGameR] at contra
  set requests! := normalise requests with eqRequests
  set Bstar := attackGameR requests! [] with eqBstar
  /-
    All requests in `normalise requests` are valid.
  -/
  have hValid : ∀ request ∈ (normalise requests), request.isValid := by unfold normalise; aesop
  let n := Bstar.length
  /-
    Section ugly.
  -/
  have hValid_withdrawal {i : Fin n} {h₀} (h : (requests![i.1]'h₀).getWithdrawal.isSome) :
    requests![i.1]'h₀ matches .withdrawal .. := by -- sorry
    rcases i with ⟨i, hi⟩
    simp [Request.getWithdrawal] at h
    aesop
  have hValidπ {i : Fin n} {h₀} {h₁} {π} (h : (requests![i.1]'h₀).getWithdrawal.get h₁ = π) :
    π.Verify (M := (C × K₁ × ExtraDataT)) := by -- sorry
    rcases i with ⟨i, hi⟩
    unfold Request.isValid at hValid
    set request := requests![i] with eqRequest
    specialize hValid request (by simp [eqRequest, requests!])
    have := @hValid_withdrawal (i := ⟨i, hi⟩)
    simp [eqRequest] at h
    next h' => specialize this h'; aesop
    done
  /-
    End Ugly.
  -/
  have hn : n = requests!.length := by simp [n, eqBstar]
  let I : List (Fin n) := (List.finRange n).filter (Bstar[·].isWithdrawalBlock)
  have hI : ∀ i, i ∈ I ↔ Bstar[i].isWithdrawalBlock := by aesop
  let getπ : {i : Fin n // i ∈ I} → ({i : Fin n // i ∈ I} × BalanceProof K₁ K₂ C Pi V) :=
    λ i ↦
      have lenEq : (attackGameR requests! []).length = n := by simp [n, eqBstar]
      have hi₁ : i.1.1 < (attackGameR requests! []).length := by rw [lenEq]; exact i.1.2
      (i, getBalanceProof requests! hValid ⟨i.1.1, hi₁⟩ ((hI i.1).1 i.2))
  let πs : List ({i : Fin n // i ∈ I} × BalanceProof K₁ K₂ C Pi V) := I.attach.map getπ
  have lenπs : πs.length ≤ n := by
    -- sorry
    simp [πs, I, n]
    simp_rw [show Bstar.length = (List.finRange (List.length Bstar)).length by aesop]
    exact List.length_filter_le _ _
  have hπs : ∀ i : {i : Fin n // i ∈ I}, (πs.lookup i).isSome := λ i ↦ -- sorry
    have : i ∈ I.attach := by rcases i with ⟨i, hi⟩; aesop
    by simp [πs, getπ, List.lookup_graph _ this]
  have validπs {π : BalanceProof K₁ K₂ C Pi V} (h : π ∈ List.map Prod.snd πs) :
               π.Verify (M := (C × K₁ × ExtraDataT)) := by
    -- sorry
    simp [πs] at h; exact hValidπ h.2.2
  unfold Intmax.isπ at isπ; specialize isπ hValid; dsimp at isπ
  dsimp [adversaryWon] at contra; simp [computeBalance_eq_sum] at contra
  by_cases eq : ∃ join : BalanceProof K₁ K₂ C Pi V, IsLUB {π | π ∈ πs.map Prod.snd} join
  -- · sorry
  · rcases eq with ⟨π, hπ₂⟩
    have hlub {π'} (h' : π' ∈ πs.map Prod.snd) : π' ≤ π :=
      mem_upperBounds.1 (hπ₂.1) _ (by simp_all)
    /-
      Step 1.
    -/
    have eq₁ : 0 ≤ -Bal π Bstar .Source := (by have : Bal π Bstar .Source ≤ 0 := lemma1; aesop)
    rw [lemma5] at eq₁; simp only [Bstar] at eq₁
    /-
      Step 2.
    -/
    let indexingSet := Finset.univ (α := Fin n) ×ˢ Finset.univ (α := K₁)
    let σ := λ x : Fin n × K₁ ↦ List.take x.1.1 Bstar
    let πᵢ := λ (x : Fin n × K₁) (h : Bstar[x.1].isWithdrawalBlock) ↦
                (πs.lookup ⟨x.1, (hI x.1).2 h⟩).get (hπs ⟨x.1, (hI x.1).2 h⟩)
    have hπᵢ {x} (h) : πᵢ x h ∈ List.map Prod.snd πs := by
      simp [πᵢ, πs, List.lookup_graph, getπ]
      rw [←hI] at h
      use x.1; use h
    let F : Fin n × K₁ → V :=
      λ x ↦ if h : Bstar[x.1].isWithdrawalBlock
            then Bal (πᵢ x h) (σ x) x.2 ⊓ Bal π (σ x) x.2
            else 0
    rw [Finset.sum_congr (s₂ := indexingSet) (g := F) (h := rfl)
                         (by simp [
                               F, σ, πᵢ, Bstar, isπ, BalanceProof.toBalanceF,
                               πs, getπ, List.lookup_graph])] at eq₁
    simp only [Fin.getElem_fin, F] at eq₁
    let F : Fin n × K₁ → V :=
      λ x ↦ if h : Bstar[x.1].isWithdrawalBlock
            then Bal (πᵢ x h) (σ x) x.2
            else 0
    rw [Finset.sum_congr (s₂ := indexingSet) (g := F) (h := rfl)
                         (by simp [F]; intros idx k₁ h
                             split <;> try simp
                             next h' =>
                                have := lemma2 (bs := (σ (idx, k₁)))
                                               (show πᵢ (idx, k₁) h' ≤ π from hlub (hπᵢ h'))
                                simp [(·≤·)] at this; apply this)] at eq₁
    simp only [
      computeBalanceErik, aggregateWithdrawals_eq_aggregateWithdrawals', aggregateWithdrawals'
    ] at contra
    rw [Finset.sum_congr (s₂ := indexingSet) (g := F) (h := by simp [indexingSet])
                         (by simp [
                               F, σ, πᵢ, Bstar, isπ, BalanceProof.toBalanceF,
                               πs, getπ, List.lookup_graph])] at contra
    simp at eq₁ contra; contradiction
  · -- by_cases hwithdrawal : πs = []; sorry -- If no withdrawal happens, balance cannot decrease.
    let πproofs := πs.map Prod.snd
    have lenπs': πproofs.length = πs.length := by simp [πproofs]
    let πs' := List.Ico 0 (πs.length + 1) |>.map λ i ↦ mergeR'' (πproofs.take i) .initial
    have lenπs'': πs'.length = πs.length + 1 := by simp [πs', lenπs']
    have hπs' : ∀ π ∈ πs', π.Verify (M := (C × K₁ × ExtraDataT)) := by
      simp [πs', πproofs]; intros n hn
      exact valid_mergeR'' (by simp; omega) (λ _ hx ↦ validπs hx)
    have recπs' : ∀ {i : ℕ} (hi : i < πs'.length), πs'[i] = mergeR'' (πproofs.take i) .initial :=
      by simp [πs', πproofs]; intros i hi; rw [List.getElem_Ico_of_lt hi]
    let m := πs'.length.pred
    set π'ₘ := πs'[m]'(by simp [m]; omega) with eqπ'ₘ
    simp [-Prod.forall, -Prod.exists] at eq
    have idx : ∃ i : Fin πs.length, ¬ IsLUB { π | π ∈ πproofs.take i.1 } (πs'[i.1 + 1]'(by rcases i; omega)) := sorry
    rcases idx with ⟨i, lubi⟩
    have eq₁ : ∃ key : { k : C × K₂ // k ∈ πs'[i.1 + 1]'(by rcases i; omega) ∧ k ∈ (πproofs[i.1]'(by simp [lenπs'])) },
      ¬((((πs'[i.1 + 1]'(by rcases i; omega)) key.1).get key.2.1) ≅ ((πproofs[i.1]'(by simp [lenπs'])) key.1).get key.2.2) := sorry
    rcases eq₁ with ⟨⟨key, ⟨mem₁, mem₂⟩⟩, hkey⟩
    set π₁ := ((πs'[i.1 + 1]'(by rcases i; omega)) key).get mem₁ with eqπ₁
    set π₂ := ((πproofs[i.1]'(by simp [lenπs'])) key).get mem₂ with eqπ₂
    rcases key with ⟨c, s⟩
    rcases π₁ with ⟨⟨π, salt⟩, t⟩
    have π₁valid : AD.Verify π s (H _ (t, salt)) c := by
      have : (πs'[i.1 + 1]'(by rcases i; omega)).Verify (M := (C × K₁ × ExtraDataT)) := hπs' _ (by simp)
      simp [BalanceProof.Verify] at this; simp_rw [←Dict.mem_dict_iff_mem_keys] at this
      specialize this c s mem₁
      convert this <;> rw [←eqπ₁]
    rcases π₂ with ⟨⟨π', salt'⟩, t'⟩
    have π₂valid : AD.Verify π' s (H _ (t', salt')) c := by
      have : (πproofs[i.1]'(by simp [lenπs'])).Verify (M := (C × K₁ × ExtraDataT)) := validπs (by simp)
      simp [BalanceProof.Verify] at this; simp_rw [←Dict.mem_dict_iff_mem_keys] at this
      specialize this c s mem₂
      convert this <;> rw [←eqπ₂]
    have tneq : t ≠ t' := by rw [batch_eq_iff] at hkey; tauto
    by_cases hashEq : H (ω := (C × K₁ × ExtraDataT)) (t, salt) = H _ (t', salt')
    · have : Function.Injective (H (ω := (C × K₁ × ExtraDataT))) :=
        Intmax.CryptoAssumptions.Function.injective_of_CryptInjective (inj := Hinj) -- AXIOMATISED
      have : (t, salt) = (t', salt') := this hashEq
      injection this
      contradiction
    · have binding := AD.binding
      apply computationallyInfeasible_axiom at binding -- AXIOMATISED
      simp at binding
      specialize binding _ _ _ _ _ _ π₁valid _ _ _ _ π₂valid
      rcases H (C × K₁ × ExtraDataT) (t, salt) with ⟨c, k₁, extra⟩
      set hash₁ := H (C × K₁ × ExtraDataT) (t, salt) with eqhash₁
      set hash₂ := H (C × K₁ × ExtraDataT) (t', salt') with eqhash₂
      rcases hash₁ with ⟨c₁, k₁, ed₁⟩; rcases hash₂ with ⟨c₂, k₂, ed₂⟩
      dsimp at binding hashEq
      simp [binding] at hashEq

end AttackGame

end lemma1

end

end Intmax

end Intmax

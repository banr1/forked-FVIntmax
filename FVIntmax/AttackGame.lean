import FVIntmax.Wheels.AuthenticatedDictionary
import FVIntmax.Wheels.SignatureAggregation

import FVIntmax.BalanceProof
import FVIntmax.Block
import FVIntmax.Request
import FVIntmax.Wheels

/-!
NB the attack game infrastructure is ever so slightly different from the paper version as it came
to exist in its current form at the time of mechanisation. The differences are of technical nature
only and do not impact the model semantically (we hope).

We point out the differences whenever possible.
-/

namespace Intmax

noncomputable section Intmax

section RollupContract

open Classical

section

variable {C : Type} [Nonempty C]

         {V : Type} [Lattice V] [AddCommGroup V]
         
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

section

variable {C : Type}
         {V : Type} [Lattice V] [AddCommGroup V]
         {K₁ : Type} [Finite K₁]
         {K₂ : Type}
         {Sigma : Type}
         {block : Block K₁ K₂ C Sigma V}
         {v : V}

section Lemmas

lemma Block.updateBalance_eq_zero :
  block.updateBalance v = v + block.updateBalance 0 := by
  unfold Block.updateBalance
  match block with
  | .deposit ..   => simp
  | .transfer ..  => simp
  | .withdrawal B => simp; exact sub_eq_add_neg v (∑ x : K₁, ↑(B x))

lemma Block.updateBalance_of_transfer (h : block.isTransferBlock) :
  block.updateBalance v = v := by
  unfold Block.updateBalance
  match block with
  | .transfer .. => simp
  | .withdrawal .. | .deposit .. => aesop

@[simp]
lemma Block.updateBalance_transfer {a : K₁} {b : ExtraDataT} {c : C} {d : List K₂} (e : Sigma) :
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

namespace Scontract

section

variable [LinearOrder K₁] [Nonempty K₁]
         [LinearOrder K₂] [Finite K₂]
         [Nonempty C]
         [CovariantClass V V (· + ·) (· ≤ ·)]
         [CovariantClass V V (Function.swap (· + ·)) (· ≤ ·)]
         [ADScheme K₂ (C × K₁ × ExtraDataT) C Pi]
         [SignatureAggregation (C × K₁ × ExtraDataT) K₂ KₛT Sigma]

def appendBlock (σ : Scontract K₁ K₂ V C Sigma)
                (request : Request K₁ K₂ C Sigma Pi V) : Scontract K₁ K₂ V C Sigma :=
  (request.toBlock σ).elim σ (σ ++ [·])

def appendBlock! (σ : Scontract K₁ K₂ V C Sigma)
                 (request : Request K₁ K₂ C Sigma Pi V) : Scontract K₁ K₂ V C Sigma :=
  σ ++ [request.toBlock! σ]

section appendBlock

variable {σ : Scontract K₁ K₂ V C Sigma} {request : Request K₁ K₂ C Sigma Pi V}

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

end

section

variable [LinearOrder K₁]
         [Finite K₂] [LinearOrder K₂]
         {σ : Scontract K₁ K₂ V C Sigma}
         {request : Request K₁ K₂ C Sigma Pi V}
         [CovariantClass V V (· + ·) (· ≤ ·)]
         [CovariantClass V V (Function.swap (· + ·)) (· ≤ ·)]

@[simp]
lemma length_appendBlock :
  (appendBlock! σ request).length = σ.length + 1 := by simp [appendBlock!]

lemma appendBlock!_def : σ.appendBlock! request = σ ++ [request.toBlock! σ] := rfl

@[simp]
lemma appendBlock!_nil : Scontract.appendBlock! [] request = [request.toBlock! []] := rfl

end

end Scontract

end

end RollupContract

section AttackGameDefs

variable {K₁ : Type} [Finite K₁] [LinearOrder K₁] [Nonempty K₁]
         {K₂ : Type} [Finite K₂] [LinearOrder K₂]

         {V : Type} [Lattice V] [AddCommGroup V]
         [CovariantClass V V (· + ·) (· ≤ ·)]
         [CovariantClass V V (Function.swap (· + ·)) (· ≤ ·)]

         {Sigma : Type}
         {C : Type} [Nonempty C]

         [ADScheme K₂ (C × K₁ × ExtraDataT) C Pi]
         [SignatureAggregation (C × K₁ × ExtraDataT) K₂ KₛT Sigma]

         (requests : List (Request K₁ K₂ C Sigma Pi V))
         (σ : Scontract K₁ K₂ V C Sigma)

def attackGameBlocks' : Scontract K₁ K₂ V C Sigma :=
  requests.foldl Scontract.appendBlock σ

def attackGame : Scontract K₁ K₂ V C Sigma :=
  attackGameBlocks' requests []

def attackGameBlocks'! : Scontract K₁ K₂ V C Sigma :=
  requests.foldl Scontract.appendBlock! σ

def attackGameBlocks'!r (requests : List (Request K₁ K₂ C Sigma Pi V))
                        (σ : Scontract K₁ K₂ V C Sigma) : Scontract K₁ K₂ V C Sigma :=
  match requests with
  | [] => σ
  | hd :: tl => attackGameBlocks'!r tl (σ.appendBlock! hd)

def attackGameRGo (requests : List (Request K₁ K₂ C Sigma Pi V))
                  (σ : Scontract K₁ K₂ V C Sigma) : Scontract K₁ K₂ V C Sigma :=
  match requests with
  | [] => []
  | hd :: tl => hd.toBlock! σ :: attackGameRGo tl (σ.appendBlock! hd)

def attackGameR : Scontract K₁ K₂ V C Sigma :=
  σ ++ attackGameRGo requests σ

def attackGameBlocks! (requests : List (Request K₁ K₂ C Sigma Pi V)) : Scontract K₁ K₂ V C Sigma :=
  attackGameBlocks'! requests []

def normalise (requests : List (Request K₁ K₂ C Sigma Pi V)) : List (Request K₁ K₂ C Sigma Pi V) :=
  requests.filter Request.isValid

def computeBalance' (blocks : Scontract K₁ K₂ V C Sigma) (acc : V) : V :=
  blocks.foldl Block.updateBalance acc

def computeBalance (blocks : Scontract K₁ K₂ V C Sigma) : V :=
  computeBalance' blocks 0

def adversaryWon (blocks : Scontract K₁ K₂ V C Sigma) : Prop :=
  ¬0 ≤ computeBalance blocks

def aggregateDeposits (σ : Scontract K₁ K₂ V C Sigma) : V :=
  ∑ i : Fin σ.length,
    if h : σ[i].isDepositBlock
    then (σ[i.1].getDeposit h).2.1
    else 0

def aggregateWithdrawals (σ : Scontract K₁ K₂ V C Sigma) : V :=
  ∑ i : Fin σ.length,
    if h : σ[i].isWithdrawalBlock
    then ∑ (k : K₁), (σ[i.1].getWithdrawal h) k
    else 0

def aggregateWithdrawals' (σ : Scontract K₁ K₂ V C Sigma) : V :=
  ∑ (i : Fin σ.length × K₁),
    if h : σ[i.1].isWithdrawalBlock
    then (σ[i.1].getWithdrawal h) i.2
    else 0

def computeBalanceSum (σ : Scontract K₁ K₂ V C Sigma) :=
  let v_deposited : V := aggregateDeposits σ
  let v_withdrawn : V := aggregateWithdrawals σ
  v_deposited - v_withdrawn

end AttackGameDefs

section AttackGameLemmas

variable {K₁ K₂ Sigma C : Type}
         {V : Type} [Lattice V] [AddCommGroup V]
         [CovariantClass V V (· + ·) (· ≤ ·)]
         [ADScheme K₂ (C × K₁ × ExtraDataT) C Pi]

@[simp]
lemma aggregateDeposits_nil : aggregateDeposits ([] : Scontract K₁ K₂ V C Sigma) = 0 := rfl

section computeBalanceSum

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

end computeBalanceSum

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
  rw [Finset.sum_bij (t := Finset.range tl.length)
                     (g := F)
                     (i := reindex)
                     (hi := reindex_mem)
                     (i_inj := reindex_inj)
                     (i_surj := λ b hb ↦ by use b.succ; simp; exact Finset.mem_range.1 hb)
                     (h := λ n hn ↦ by simp at hn; simp [hn]
                                       rcases n with _ | n <;> [omega; simp [F, reindex]]
                                       nth_rw 2 [dif_pos (by rcases hn with ⟨hn, _⟩; omega)])]
  unfold F
  rw [Finset.sum_dite_of_true (λ _ ↦ (Finset.mem_range.1 ·)), Finset.sum_fin_eq_sum_range, Finset.univ_eq_attach]
  nth_rw 2 [Finset.sum_dite_of_true]; case h => exact λ _ ↦ (Finset.mem_range.1 ·)
  rw [add_comm]; simp

variable [Finite K₁]

lemma aggregateWithdrawals_eq_aggregateWithdrawals' {σ : Scontract K₁ K₂ V C Sigma} :
  aggregateWithdrawals σ = aggregateWithdrawals' σ := by
  unfold aggregateWithdrawals aggregateWithdrawals'
  rw [Fintype.sum_prod_type, Fintype.sum_congr]
  aesop

end AttackGameLemmas

section ComputeLemmas

variable {K₁ : Type} [Finite K₁] {K₂ Sigma C : Type}
         {V : Type} [Lattice V] [AddCommGroup V]
         {σ : Scontract K₁ K₂ V C Sigma}
         [ADScheme K₂ (C × K₁ × ExtraDataT) C Pi]

@[simp]
lemma computeBalance'_nil : computeBalance' ([] : Scontract K₁ K₂ V C Sigma) v = v := rfl

@[simp]
lemma computeBalance'_cons : computeBalance' (hd :: σ) v =
                             computeBalance' σ (Block.updateBalance v hd) := rfl

lemma computeBalance'_eq_zero : computeBalance' σ v = v + computeBalance' σ 0 := by
  induction' σ with hd tl ih generalizing v
  · simp
  · rw [computeBalance'_cons, computeBalance'_cons, ih, Block.updateBalance_eq_zero]
    nth_rw 2 [ih]
    exact add_assoc v _ _

end ComputeLemmas

section ComputeBalanceEqLemmas

variable {K₁ : Type} [Finite K₁]
         {K₂ Sigma C : Type}

         {V : Type} [Lattice V] [AddCommGroup V]
         [CovariantClass V V (· + ·) (· ≤ ·)]
         [ADScheme K₂ (C × K₁ × ExtraDataT) C Pi]

         {σ : Scontract K₁ K₂ V C Sigma}
         {v : V}

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
private lemma computeBalance_eq_sum_aux : computeBalance' σ v = v + computeBalanceSum σ := by
  induction' σ with hd tl ih generalizing v
  · simp [computeBalanceSum, aggregateWithdrawals, aggregateDeposits]
  · rw [computeBalance'_eq_zero]; simp; rw [ih]
    unfold computeBalanceSum aggregateWithdrawals aggregateDeposits
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

lemma computeBalance_eq_sum : computeBalance σ = computeBalanceSum σ := by
  simp [computeBalance, computeBalance_eq_sum_aux]

end ComputeBalanceEqLemmas

section AttackGameLemmas

variable {K₁ : Type} [Finite K₁] [LinearOrder K₁]
         {K₂ : Type} [Finite K₂] [LinearOrder K₂]
         {Sigma C : Type}

         {V : Type} [Lattice V] [AddCommGroup V]
         [CovariantClass V V (· + ·) (· ≤ ·)]

         {σ : Scontract K₁ K₂ V C Sigma}
         {requests : List (Request K₁ K₂ C Sigma Pi V)}
         {v : V}

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
  induction' requests with hd tl ih generalizing σ <;> simp [attackGameR, attackGameBlocks'!r]
  simp [ih.symm, attackGameR, Scontract.appendBlock!_def]

lemma attackGameBlocks'r_eq_attackGameBlocks' :
  attackGameBlocks'! requests σ = attackGameBlocks'!r requests σ := by
  induction' requests with hd tl ih generalizing σ <;> aesop

lemma attackGameBlocks_eq_attackGameR :
  attackGameBlocks! requests = attackGameR requests [] := by
  rw [attackGameR_eq_attackGameBlocks', ←attackGameBlocks'r_eq_attackGameBlocks']
  rfl

@[simp]
lemma length_attackGameBlocks'! :
  (attackGameBlocks'! requests σ).length = σ.length + requests.length := by
  unfold attackGameBlocks'!
  induction' requests with hd tl ih generalizing σ <;> [rfl; (simp [ih]; omega)]

@[simp]
lemma length_attackGameBlocks! :
  (attackGameBlocks! requests).length = requests.length := by simp [attackGameBlocks!]

@[simp]
lemma attackGameBlocks'!_cons :
  attackGameBlocks'! (hd :: requests) σ = attackGameBlocks'! requests (σ ++ [hd.toBlock! σ]) := rfl

@[simp]
lemma length_attackGameRGo : (attackGameRGo requests σ).length = requests.length := by
  induction' requests with hd tl ih generalizing σ <;> aesop

@[simp]
lemma length_attackGameR : (attackGameR requests σ).length = σ.length + requests.length := by
  simp [attackGameR]

lemma attackGameRGo_isWithdrawal_iff (σ σ' : Scontract K₁ K₂ V C Sigma)
                                     (h : i < (attackGameRGo requests σ).length) :
  (attackGameRGo requests σ)[i].isWithdrawalBlock ↔
  (attackGameRGo requests σ')[i].isWithdrawalBlock := by
  simp
  induction' requests with hd tl ih generalizing i σ σ' <;>
    [rfl; (simp [Request.toBlock!]; rcases i <;> aesop)]

variable [Nonempty K₁] [Nonempty C]
         [ADScheme K₂ (C × K₁ × ExtraDataT) C Pi]
         [SignatureAggregation (C × K₁ × ExtraDataT) K₂ KₛT Sigma]

lemma attackGameBlocks'_eq_attackGameBlocks'!_normalise :
  attackGameBlocks' requests σ = attackGameBlocks'! (normalise requests) σ := by
  unfold attackGameBlocks' attackGameBlocks'!
  unfold normalise
  induction' requests with hd tl ih generalizing σ <;> [rfl; skip]
  by_cases eq : hd.isValid
  · rw [List.filter_cons_of_pos eq]; dsimp
    rw [ih, ←Scontract.appendBlock_eq_appendBlock!_of_isValid eq]
  · rw [List.filter_cons_of_neg eq]; dsimp
    rw [ih, Scontract.appendBlock_eq_id_of_not_isValid eq]

lemma attackGame_eq_attackGameBlocks!_normalise :
  attackGame requests = attackGameBlocks! (normalise requests) :=
  attackGameBlocks'_eq_attackGameBlocks'!_normalise

end AttackGameLemmas

section InteractionLemmas

variable {K₁ : Type} [Finite K₁] [LinearOrder K₁] [Nonempty K₁]
         {K₂ : Type} [Finite K₂] [LinearOrder K₂]
         {Sigma C : Type} [Nonempty C]

         {V : Type} [Lattice V] [AddCommGroup V]
         [CovariantClass V V (· + ·) (· ≤ ·)]

         [ADScheme K₂ (C × K₁ × ExtraDataT) C Pi]
         [SignatureAggregation (C × K₁ × ExtraDataT) K₂ KₛT Sigma]

         {σ : Scontract K₁ K₂ V C Sigma}
         {requests : List (Request K₁ K₂ C Sigma Pi V)}
         {v : V}

private lemma isWithdrawalRequest_of_isWithdrawalBlock_aux {i : ℕ}
  (h₀ : ∀ request ∈ requests, request.isValid)
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
      simp [Request.toBlock!] at h₁ ⊢; rcases hd <;> [simp at h₁; simp at h₁; simp]
    · rcases σ with _ | ⟨hd', tl'⟩
      · simp at ih hi₂ ⊢
        apply ih (by aesop) hi₂
        rwa [attackGameRGo_isWithdrawal_iff (σ' := Scontract.appendBlock! [] hd)]
      · simp at hi₁ ⊢
        rcases le_iff_eq_or_lt.1 hi₁ with hi₁ | hi₁
        · simp_rw [hi₁]; simp [Request.toBlock!] at h₁ ⊢
          simp_rw [←hi₁, List.getElem_append_right (le_refl _)] at h₁
          rcases hd <;> [simp at h₁; simp at h₁; simp]
        · rcases lt_iff_exists_add.1 hi₁ with ⟨c, ⟨hc₁, hc₂⟩⟩
          simp_rw [hc₂]
          rcases c with _ | c <;> [simp at hc₁; simp]
          specialize ih (by aesop) (i := (c + (hd' :: tl').length)); simp at ih
          refine' ih (by simp at hi₂; omega) _
          simp_rw [←Nat.add_assoc]; simp at h₁ ⊢
          simp_rw [
            hc₂, ←Nat.add_assoc,
            List.append_cons (as := tl') (b := Request.toBlock! _ _) (bs := attackGameRGo _ _)
          ] at h₁
          rw [List.getElem_append_right] at h₁ ⊢ <;> simp at h₁ ⊢
          rwa [←attackGameRGo_isWithdrawal_iff]

lemma isWithdrawalRequest_of_isWithdrawalBlock
  (h₀ : ∀ request ∈ requests, request.isValid)
  (i : Fin (attackGameR requests []).length)
  (h₁ : ((attackGameR requests [])[i]'(by simp; rcases i with ⟨i, hi⟩; simp at hi; exact hi)).isWithdrawalBlock) :
  (requests[i]'(by rcases i with ⟨h, hi⟩; rcases requests with _ | ⟨hd, tl⟩
                   · simp at hi
                   · simp at hi ⊢; omega)) matches .withdrawal .. := by
  let σ : Scontract K₁ K₂ V C Sigma := []
  have hσ : σ.length = 0 := by simp [σ]
  rcases i with ⟨i, hi⟩; dsimp at h₁ ⊢
  have eq := isWithdrawalRequest_of_isWithdrawalBlock_aux (σ := [])
                                                          (requests := requests)
                                                          h₀
                                                          (i := i + σ.length)
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

end InteractionLemmas

end Intmax

end Intmax

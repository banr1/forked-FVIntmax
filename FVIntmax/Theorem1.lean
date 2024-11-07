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

def normalise (requests : List (Request K₁ K₂ C Sigma Pi V)) : List (Request K₁ K₂ C Sigma Pi V) :=
  requests.filter Request.isValid

def computeBalance' (blocks : RollupState K₁ K₂ V C Sigma) (acc : V) : V :=
  blocks.foldl Block.updateBalance acc

def computeBalance (blocks : RollupState K₁ K₂ V C Sigma) : V :=
  computeBalance' blocks 0

def adversaryWon (blocks : RollupState K₁ K₂ V C Sigma) :=
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

-- (∑ (i : Fin σ.length) (k : K₁),
--  if h : σ[i].isWithdrawalBlock
--  then let w := σ[i].getWithdrawal h
--       w k ⊓ Bal π (σ.take i.1) k
--  else 0)

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
  · rw [computeBalance'_cons, computeBalance'_cons]
    rw [ih]; nth_rw 2 [ih]
    rw [Block.updateBalance_eq_zero]
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

-- @[simp]
-- lemma f_Source {r : K₂} {v : V₊} {h} :
--   f (K₁ := K₁) acc' ⟨(Kbar.Source, Kbar.key (Sum.inr r), some v), h⟩ .Source = sorry := by
--   have := f_IsGLB_of_V' (b := acc') (T:= ⟨(Kbar.Source, Kbar.key (Sum.inr r), some v), h⟩) (k := .Source)
--   simp at this ⊢


--   done

@[simp]
lemma transactionsInBlock_deposit {r : K₂} {v : V₊} :
  TransactionsInBlock (K₁ := K₁) (Sigma := Sigma) π (Block.deposit r v) =
  [⟨(.Source, r, v), by simp [Τ'.isValid]⟩] := by
  unfold TransactionsInBlock
  aesop

-- @[simp]
-- lemma is_glb_fold_f_of_glb {σ : RollupState K₁ K₂ V C Sigma}
--                            {π : BalanceProof K₁ K₂ C Pi V}
--                            {acc : S K₁ K₂ V × Fin σ.length}
--                            {k : Kbar K₁ K₂}
--   (h : IsGLB (Set.univ (α := S K₁ K₂ V)) acc.1) :
--   IsGLB _ (List.foldl (λ acc s ↦ (f acc.1 σ, acc.2 + 1)) acc.1 σ) := by sorry
--   -- (h : IsGLB (Set.iUnion (· ∈ TransactionsInBlocks π (σ.take acc.2.1))) acc.1) :
--   -- IsGLB _ (List.foldl (λ acc s ↦ (f acc.1 σ, acc.2 + 1)) acc.1 σ) := by sorry
--   -- -- sorry

-- f S (.deposit (r, v)) .Source
-- S .Source

lemma fold_f_any_transaction_transfer {acc : S K₁ K₂ V} {l : List (Τ K₁ K₂ V)}
  (h : ∀ T ∈ l, (¬ T.1.1 matches .Source) ∧ (¬ T.1.2.1 matches .Source)) :
  (List.foldl f acc l) .Source = acc .Source := by
  rw [f_eq_f']
  simp only
  induction' l with hd tl ih generalizing acc
  · simp
  · simp only [List.map_cons, List.foldl_cons, f']
    simp only [List.mem_cons, Bool.not_eq_true, forall_eq_or_imp, Subtype.forall, Prod.forall] at h ih
    split
    next k₁ k₂ v hvalid =>
      rcases h with ⟨hhd, htl⟩
      rcases k₁ with k₁ | _ <;> rcases k₂ with k₂ | _ <;> simp at hhd
      simp [fc]; rw [ih _ _ htl]; aesop
    next k₁ k₂ hvalid =>
      obtain ⟨_, ⟨⟩⟩ := Τ'.exists_key_of_isValid hvalid
      rw [ih _ _ h.2]
      aesop

instance {V : Type} [OrderedAddCommMonoid V] : Add V₊ where
  add := λ a b ↦ ⟨a.1 + b.1, add_nonneg a.2 b.2⟩

structure IterState (K₁ K₂ V : Type) [Nonnegative V] where
  vs : List V₊
  ts : List (Τ K₁ K₂ V)
  s  : S K₁ K₂ V

def v'_of_ΤcxS (τc : Τc K₁ K₂ V) (b : S K₁ K₂ V) : V₊ :=
  match τc with | ⟨⟨⟨s, _, v⟩, _⟩, hτ⟩ => v' (v.get hτ) b s

def bumpState (v' : V₊) (τc : Τc K₁ K₂ V) (b : S K₁ K₂ V) : S' K₁ K₂ V :=
  λ k : Kbar K₁ K₂ ↦ match τc with | ⟨⟨⟨s, r, _⟩, _⟩, _⟩ => b k + (e r - e s) k • v'

def fc' (τc : Τc K₁ K₂ V) (σ : IterState K₁ K₂ V) : IterState K₁ K₂ V :=
  let v' := v'_of_ΤcxS τc σ.s
  let s' := bumpState v' τc σ.s
  {
    vs := σ.vs ++ [v']
    ts := σ.ts ++ [τc.1]
    s  := ⟨s', by simp [S'.isValid, v', v'_of_ΤcxS, s', bumpState];
                  rintro (k | _) <;>
                  aesop (add unsafe apply le_add_of_le_of_nonneg)⟩
  }

lemma snd_fc'_eq_fc {τc : Τc K₁ K₂ V} {b : IterState K₁ K₂ V} : fc (τc, b.s) = (fc' τc b).s := rfl

def fₜ (σ : IterState K₁ K₂ V) (T : Τ K₁ K₂ V) : IterState K₁ K₂ V :=
  match h : T with
  | ⟨(_, _, .some _), hT⟩ => fc' ⟨T, by simp [h]⟩ σ
  | ⟨(s, _, .none), _⟩ =>
  {
    vs := σ.vs ++ [0]
    ts := σ.ts ++ [T]
    s  := ⟨λ k ↦ if k = s then 0 else σ.s k, by rintro (k | k) <;> valid⟩
  }

lemma fₜ_eq_f' {σ : IterState K₁ K₂ V} {T : Τ K₁ K₂ V} : (fₜ σ T).s = f' σ.s T := by
  unfold fₜ f'
  simp_rw [snd_fc'_eq_fc]
  split <;> simp

lemma fold_fₜ_eq_fold_f {σ : IterState K₁ K₂ V} {l : List (Τ K₁ K₂ V)} :
  (l.foldl fₜ σ).s = l.foldl f σ.s := by
  induction' l with hd tl ih generalizing σ
  · simp
  · simp [ih, fₜ_eq_f']; congr; rw [f_eq_f']

def P (acc : IterState K₁ K₂ V) : Prop := True -- acc.s .Source = fStar acc.ts acc.s .Source

def IterState.initial (K₁ K₂ V : Type) [Nonnegative V] : IterState K₁ K₂ V :=
  {
    ts := []
    vs := []
    s  := S.initial K₁ K₂ V
  }

lemma P_initial : P (IterState.initial K₁ K₂ V) := by unfold P; aesop

namespace lemma5

section lemma5_aux

-- def reindexRange {k : ℕ} : (a : ℕ) → a ∈ Finset.range k \ {0} → ℕ := λ a _ ↦ a.pred

end lemma5_aux

end lemma5

lemma f'_comm {hd T : Τ K₁ K₂ V} :
  f' (f' s T) hd = f' (f' s hd) T := by sorry
--   ext k
--   simp [f']
--   rcases hd with ⟨⟨s, r, _ | v⟩, hT⟩
--   · rcases T with ⟨⟨s', r', _ | v'⟩, hT₁⟩
--     · unfold Τ'.isValid at hT hT₁
--       simp at hT hT₁
--       rcases s with s | _ <;> [skip; simp at hT]
--       rcases s' with s' | _ <;> [skip; simp at hT₁]
--       rcases hT with ⟨h₁, _⟩
--       rcases hT₁ with ⟨h₂, _⟩
--       simp only
--       aesop
--     · unfold Τ'.isValid at hT hT₁
--       rcases s with s | _ <;> [skip; simp at hT]
--       rcases s' with s' | _
--       · simp at hT hT₁
--         simp [fc]
--         by_cases eq : k = Kbar.key s
--         · simp [eq]
--           by_cases eq₁ : r' = Kbar.key s
--           · simp [eq₁]
--             by_cases eq₂ : s' = s
--             · simp [eq₂]
--             · simp [eq₂]
              

          
        

      
  -- · sorry
  
    


-- lemma lem {T : Τ K₁ K₂ V}
--           {ts : List (Τ K₁ K₂ V)}
--           {k : Kbar K₁ K₂}
--           {s : S K₁ K₂ V}
--           (h : ∃ block : Block K₁ K₂ C Sigma V, T ∈ TransactionsInBlock π block)
--           (h₁ : ∀ T ∈ ts, ∃ block : Block K₁ K₂ C Sigma V, T ∈ TransactionsInBlock π block) :
--   fStar ts (f s T) k = f s T k + fStar ts (S.initial K₁ K₂ V) k := by
--   simp; rw [f_eq_f']
--   induction' ts with hd tl ih generalizing s 
--   · simp
--   · simp; rw [f_eq_f']
--     generalize eq : f' s T = next
--     nth_rw 1 [f']
--     simp
--     rcases h with ⟨⟨r, v⟩ | _ | _, hb⟩
--     · simp at hb h₁
--       rcases h₁ with ⟨⟨b', h₂⟩, hb'⟩
--       rcases b' with ⟨r', v'⟩ | _ | _
--       · simp at h₂
--         rw [h₂]
--         simp [fc]

-- lemma Bal_cons_aux -- {hd : Block K₁ K₂ C Sigma V}
--                    {σ : RollupState K₁ K₂ V C Sigma}
--                    {π : BalanceProof K₁ K₂ C Pi V}
--                    {k : Kbar K₁ K₂}
--                    {acc : S K₁ K₂ V} :
--   (fStar (TransactionsInBlock π hd ++ (List.map (TransactionsInBlock π) tl).flatten) acc) k =
--   fStar (TransactionsInBlock π hd) acc k + fStar (TransactionsInBlocks π tl) (S.initial K₁ K₂ V) k := by
--   simp only
--   induction' tl with hd' tl' ih generalizing acc
--   · simp [Bal]
--   · simp [fStar]

    


  

-- lemma traverse_split {hd : Block K₁ K₂ C Sigma V}
--                      {tl : RollupState K₁ K₂ V C Sigma}
--                      {π : BalanceProof K₁ K₂ C Pi V}
--                      {k : Kbar K₁ K₂} :
--   (fStar (TransactionsInBlock π hd ++ (List.map (TransactionsInBlock π) tl).flatten) (S.initial K₁ K₂ V)) k =
--   fStar (TransactionsInBlock π hd) (S.initial K₁ K₂ V) k + Bal π tl k := by
--   unfold Bal fStar
--   simp



-- -- X = Y + whatever there was left in acc!!!!!
-- -- -- {l : List (Τ K₁ K₂ V)} {∀ T ∈ l, T ∈ TransactionsInBlocks π σ} - If not general enough. P acc'????
-- lemma lemma5_aux''''' {σ : RollupState K₁ K₂ V C Sigma}
--                       {π : BalanceProof K₁ K₂ C Pi V}
--                       {acc acc' : IterState K₁ K₂ V}
--                       (h : P acc) :
--   (List.foldl fₜ acc (List.map (TransactionsInBlock π) σ).flatten).s Kbar.Source =
--   (∑ x : Fin (List.length σ) × K₁,
--      if h : σ[x.1].isWithdrawalBlock
--      then ↑(σ[x.1].getWithdrawal h x.2) ⊓
--           (List.foldl fₜ acc' (List.map (TransactionsInBlock π) (List.take x.1.1 σ)).flatten).s x.2
--      else 0) -
--   aggregateDeposits σ := by
--   have : (∑ x : Fin (List.length σ) × K₁,
--            if h : σ[x.1].isWithdrawalBlock
--            then (σ[x.1].getWithdrawal h x.2).1 ⊓
--                 (List.foldl fₜ acc' (List.map (TransactionsInBlock π) (List.take x.1.1 σ)).flatten).s x.2
--            else 0) =
--          (∑ x : Fin (List.length σ),
--            if h : σ[x].isWithdrawalBlock
--            then ∑ y : K₁,
--                   (σ[x].getWithdrawal h y).1 ⊓
--                   (List.foldl fₜ acc' (List.map (TransactionsInBlock π) (List.take x.1 σ)).flatten).s y
--            else 0) := by sorry -- rw [Fintype.sum_prod_type]; exact Finset.sum_congr rfl (λ _ _ ↦ by aesop)
--   rw [this]; clear this
--   simp only [Fin.getElem_fin, List.map_take]
--   induction' σ with hd tl ih generalizing acc acc'
--   · simp
--   · simp only [List.map_cons, List.flatten_cons, List.foldl_append, List.length_cons, aggregateDeposits_cons]
--     generalize eqsmol : (List.foldl _ _ _) = smol
--     rw [
--       Finset.sum_fin_eq_sum_range,
--       Finset.sum_eq_sum_diff_singleton_add (i := 0) (Finset.mem_range.2 (by omega)),
--       dif_pos (show 0 < tl.length + 1 by omega)
--     ]
--     simp_rw [List.getElem_cons_zero]
--     generalize eqpartialsum : (∑ _ ∈ _, (_ : V)) = partialsum
--     rcases hd with ⟨r, v⟩ | ⟨a, b, c, d, e⟩ | vs
--     · simp [Block.getDeposit]
--       generalize eqsummand : ↑v + aggregateDeposits tl = summand
--       rw [←eqpartialsum]
--       let F : ℕ → V := λ x ↦
--         if h : x < tl.length then
--           ∑ k₁ : K₁,
--             if h' : (tl[x]'h).isWithdrawalBlock = true then
--               ((tl[x]'h).getWithdrawal h' k₁).1 ⊓
--                 (List.foldl fₜ acc'
--                   (List.take (x + 1)
--                     (TransactionsInBlock (Sigma := Sigma) π (Block.deposit r v) :: List.map (TransactionsInBlock π) tl)).flatten).s k₁
--             else 0
--         else 0
--       let F' : (a : ℕ) → a ∈ Finset.range (tl.length + 1) \ {0} → ℕ :=
--         λ a ha ↦ a.pred
--       rw [Finset.sum_bij (t := Finset.range tl.length) (g := F) (i := F')] <;>
--          [skip; (simp [F']; omega); (simp [F']; omega); (simp [F']; intros b _; use b + 1; omega);
--          (
--           simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton, List.take_succ_cons,
--                      List.flatten_cons, List.foldl_append, Finset.sum_dite_irrel, Finset.sum_const_zero,
--                      Nat.pred_eq_sub_one, and_imp, F, F']
--           intros i hi₁ hi₂
--           rw [dif_pos hi₁]; nth_rw 2 [dif_pos (by omega)]
--           rcases i with _ | i <;> [contradiction; skip]
--           simp only [List.getElem_cons_succ, List.take_succ_cons, List.flatten_cons, List.foldl_append,
--             Finset.sum_dite_irrel, Finset.sum_const_zero, add_tsub_cancel_right, Nat.add_one_sub_one,
--             Int.Nat.cast_ofNat_Int, id_eq, Int.reduceNeg, Int.reduceAdd])
--          ]
--       simp only [List.take_succ_cons, List.flatten_cons, List.foldl_append, Finset.sum_dite_irrel,
--                  Finset.sum_const_zero, F]
--       rw [Finset.sum_dite_of_true]; case h => exact λ _ ↦ (Finset.mem_range.1 ·)
--       simp only [← eqsmol, Finset.univ_eq_attach]
--       rw [ih (acc' := acc') sorry, Finset.sum_fin_eq_sum_range] -- `P` →! `P (List.foldl fₜ acc (TransactionsInBlock π (Block.deposit r v)))`
--       simp only [Fin.getElem_fin, List.map_take]
--       rw [Finset.sum_dite_of_true]; case h => exact λ _ ↦ (Finset.mem_range.1 ·)
--       simp only [Finset.univ_eq_attach]
--       rw [←eqsummand]
--       generalize eqindices : (Finset.range tl.length).attach = indices
--       rw [sub_add_eq_sub_sub]
--       simp only [sub_left_inj, transactionsInBlock_deposit, List.foldl_cons, List.foldl_nil]
--       sorry
--     · simp only [Block.transfer_ne_widthdrawal, ↓reduceDIte, add_zero, Block.transfer_ne_deposit, zero_add]
--       rw [←eqpartialsum]
--       let F : ℕ → V := λ x ↦
--         if h : x < tl.length then
--           ∑ k₁ : K₁,
--             if h' : (tl[x]'h).isWithdrawalBlock = true then
--               ((tl[x]'h).getWithdrawal h' k₁).1 ⊓
--                 (List.foldl fₜ acc'
--                   (List.take (x + 1)
--                     (TransactionsInBlock (Sigma := Sigma) π (Block.transfer a b c d e) :: List.map (TransactionsInBlock π) tl)).flatten).s k₁
--             else 0
--         else 0
--       let F' : (a : ℕ) → a ∈ Finset.range (tl.length + 1) \ {0} → ℕ :=
--         λ a ha ↦ a.pred
--       rw [Finset.sum_bij (t := Finset.range tl.length) (g := F) (i := F')] <;>
--          [skip; (simp [F']; omega); (simp [F']; omega); (simp [F']; intros b _; use b + 1; omega);
--          (
--           simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton, List.take_succ_cons,
--                      List.flatten_cons, List.foldl_append, Finset.sum_dite_irrel, Finset.sum_const_zero,
--                      Nat.pred_eq_sub_one, and_imp, F, F']
--           intros i hi₁ hi₂
--           rw [dif_pos hi₁]; nth_rw 2 [dif_pos (by omega)]
--           rcases i with _ | i <;> [contradiction; skip]
--           simp only [List.getElem_cons_succ, List.take_succ_cons, List.flatten_cons, List.foldl_append,
--             Finset.sum_dite_irrel, Finset.sum_const_zero, add_tsub_cancel_right, Nat.add_one_sub_one,
--             Int.Nat.cast_ofNat_Int, id_eq, Int.reduceNeg, Int.reduceAdd])
--          ]
--       simp only [List.take_succ_cons, List.flatten_cons, List.foldl_append, Finset.sum_dite_irrel,
--                  Finset.sum_const_zero, F]
--       rw [Finset.sum_dite_of_true]; case h => exact λ _ ↦ (Finset.mem_range.1 ·)
--       simp only [← eqsmol, Finset.univ_eq_attach]
--       rw [ih (acc' := acc') sorry, Finset.sum_fin_eq_sum_range] -- `P` →! `P (List.foldl fₜ acc (TransactionsInBlock π (Block.transfer a b c d e)))`
--       simp only [Fin.getElem_fin, List.map_take]
--       rw [Finset.sum_dite_of_true]; case h => exact λ _ ↦ (Finset.mem_range.1 ·)
--       simp only [Finset.univ_eq_attach]
--       generalize eqindices : (Finset.range tl.length).attach = indices
--       simp only [sub_left_inj]
--       refine' Finset.sum_congr rfl (λ i hi ↦ _)
--       split_ifs with eq
--       · refine' Finset.sum_congr rfl (λ i' hi' ↦ _)
--         simp_rw [fold_fₜ_eq_fold_f]
--         have := fold_f_any_transaction_transfer
--           (acc := acc'.s)
--           (l := TransactionsInBlock π (Block.transfer a b c d e))
--           sorry
--         dsimp at this
--         rw [inf_eq_inf_iff_left]
--         refine' ⟨_, _⟩
--         · sorry
--         · sorry
--       · rfl
--     · simp only [Block.transfer_ne_widthdrawal, ↓reduceDIte, add_zero, Block.transfer_ne_deposit, zero_add]
--       rw [←eqpartialsum]
--       let F : ℕ → V := λ x ↦
--         if h : x < tl.length then
--           ∑ k₁ : K₁,
--             if h' : (tl[x]'h).isWithdrawalBlock = true then
--               ((tl[x]'h).getWithdrawal h' k₁).1 ⊓
--                 (List.foldl fₜ acc'
--                   (List.take (x + 1)
--                     (TransactionsInBlock (Sigma := Sigma) π (Block.withdrawal vs) :: List.map (TransactionsInBlock π) tl)).flatten).s k₁
--             else 0
--         else 0
--       let F' : (a : ℕ) → a ∈ Finset.range (tl.length + 1) \ {0} → ℕ :=
--         λ a ha ↦ a.pred
--       rw [Finset.sum_bij (t := Finset.range tl.length) (g := F) (i := F')] <;>
--          [skip; (simp [F']; omega); (simp [F']; omega); (simp [F']; intros b _; use b + 1; omega);
--          (
--           simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton, List.take_succ_cons,
--                      List.flatten_cons, List.foldl_append, Finset.sum_dite_irrel, Finset.sum_const_zero,
--                      Nat.pred_eq_sub_one, and_imp, F, F']
--           intros i hi₁ hi₂
--           rw [dif_pos hi₁]; nth_rw 2 [dif_pos (by omega)]
--           rcases i with _ | i <;> [contradiction; skip]
--           simp only [List.getElem_cons_succ, List.take_succ_cons, List.flatten_cons, List.foldl_append,
--             Finset.sum_dite_irrel, Finset.sum_const_zero, add_tsub_cancel_right, Nat.add_one_sub_one,
--             Int.Nat.cast_ofNat_Int, id_eq, Int.reduceNeg, Int.reduceAdd])
--          ]
--       simp only [List.take_succ_cons, List.flatten_cons, List.foldl_append, Finset.sum_dite_irrel,
--                  Finset.sum_const_zero, F]
--       rw [Finset.sum_dite_of_true]; case h => exact λ _ ↦ (Finset.mem_range.1 ·)
--       simp only [← eqsmol, Finset.univ_eq_attach]
--       rw [ih (acc' := acc') sorry, Finset.sum_fin_eq_sum_range] -- `P` →! `P (List.foldl fₜ acc (TransactionsInBlock π (Block.withdrawal vs)))`
--       simp only [Fin.getElem_fin, List.map_take]
--       rw [Finset.sum_dite_of_true]; case h => exact λ _ ↦ (Finset.mem_range.1 ·)
--       simp only [Finset.univ_eq_attach]
--       simp only [List.take_zero, List.flatten_nil, List.foldl_nil, Block.withdrawal_ne_deposit,
--         ↓reduceDIte, zero_add, sub_left_inj]
--       sorry

namespace lemma5

def reindexRange (k : ℕ) : (a : ℕ) → a ∈ Finset.range k \ {0} → ℕ := λ a _ ↦ a.pred

lemma rR_mem {k : ℕ} : ∀ (a : ℕ) (ha : a ∈ Finset.range (k + 1) \ {0}),
  reindexRange (k + 1) a ha ∈ Finset.range k := by simp [reindexRange]; omega

lemma rR_eq {k : ℕ} :
  ∀ (a₁ : ℕ) (ha₁ : a₁ ∈ Finset.range (k + 1) \ {0})
    (a₂ : ℕ) (ha₂ : a₂ ∈ Finset.range (k + 1) \ {0}),
    reindexRange (k + 1) a₁ ha₁ = lemma5.reindexRange (k + 1) a₂ ha₂ → a₁ = a₂ := by simp [reindexRange]; omega

lemma isK₁_of_withdrawal {T : Τ K₁ K₂ V}
                         {π : BalanceProof K₁ K₂ C Pi V}
  (h : ∃ block : {b : Block K₁ K₂ C Sigma V // b.isWithdrawalBlock}, T ∈ TransactionsInBlock π block.1) :
  T.sender.isK₁ := by
  rcases T with ⟨⟨s, r, v⟩, hT⟩
  rcases h with ⟨⟨b, hb⟩, h₁⟩
  simp [TransactionsInBlock] at h₁
  split at h₁
  unfold TransactionsInBlock_deposit at h₁; simp at hb
  unfold TransactionsInBlock_transfer at h₁; simp at hb
  unfold TransactionsInBlock_withdrawal at h₁; aesop

-- VVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVVV
-- transactionsinblock_Source_pres_valid_transfer :
-- Not true when k ∈ senders ∧ h_1 : (c, k) ∉ Dict.keys π
-- ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
lemma isSome_of_deposit {T : Τ K₁ K₂ V}
                        {π : BalanceProof K₁ K₂ C Pi V}
  (h : ∃ block : {b : Block K₁ K₂ C Sigma V // b.isDepositBlock}, T ∈ TransactionsInBlock π block.1) :
  T.value.isSome := by
  rcases T with ⟨⟨s, r, v⟩, hT⟩
  rcases h with ⟨⟨b, hb⟩, h₁⟩
  simp [TransactionsInBlock] at h₁
  split at h₁
  unfold TransactionsInBlock_deposit at h₁; aesop
  unfold TransactionsInBlock_transfer at h₁; simp at hb
  unfold TransactionsInBlock_withdrawal at h₁; simp at hb

lemma isSome_of_withdrawal {T : Τ K₁ K₂ V}
                           {π : BalanceProof K₁ K₂ C Pi V}
  (h : ∃ block : {b : Block K₁ K₂ C Sigma V // b.isWithdrawalBlock}, T ∈ TransactionsInBlock π block.1) :
  T.value.isSome := by
  rcases T with ⟨⟨s, r, v⟩, hT⟩
  rcases h with ⟨⟨b, hb⟩, h₁⟩
  simp [TransactionsInBlock] at h₁
  split at h₁
  unfold TransactionsInBlock_deposit at h₁; simp at hb
  unfold TransactionsInBlock_transfer at h₁; simp at hb
  unfold TransactionsInBlock_withdrawal at h₁; aesop

lemma f_deposit_source {T : Τ K₁ K₂ V}
                       {σ : S K₁ K₂ V}
                       {π : BalanceProof K₁ K₂ C Pi V}
                       (h : ∃ block : {b : Block K₁ K₂ C Sigma V // b.isDepositBlock},
                              T ∈ TransactionsInBlock π block.1) :
                       (f σ T) .Source = σ .Source + -T.value.get (isSome_of_deposit h) := by
  rcases h with ⟨⟨b, hb⟩, h₁⟩
  rcases T with ⟨⟨s, r, v⟩, hT⟩
  unfold Block.isDepositBlock at hb
  simp [TransactionsInBlock] at h₁
  split at h₁ <;> [skip; simp at hb; simp at hb]
  next r' v' =>
  simp [TransactionsInBlock_deposit] at h₁ ⊢
  rcases h₁ with ⟨h₁, h₂, h₃⟩
  simp [h₁, h₂, h₃, f_eq_f', f', fc, Τ.value]

lemma f_withdraw_source {T : Τ K₁ K₂ V}
                        {σ : S K₁ K₂ V}
                        {π : BalanceProof K₁ K₂ C Pi V}
                        (h : ∃ block : {b : Block K₁ K₂ C Sigma V // b.isWithdrawalBlock},
                               T ∈ TransactionsInBlock π block.1) :
                        (f σ T) .Source =
                        σ .Source + (↑(T.value.get (isSome_of_withdrawal h)) ⊓ σ T.sender) := by
  rcases h with ⟨⟨b, hb⟩, h₁⟩
  rcases T with ⟨⟨s, r, v⟩, hT⟩
  unfold Block.isWithdrawalBlock at hb
  simp [TransactionsInBlock] at h₁
  split at h₁ <;> [simp at hb; simp at hb; skip]
  next r' v' =>
  simp [TransactionsInBlock_withdrawal] at h₁ ⊢
  rcases h₁ with ⟨k₁, h₁, h₂, h₃⟩
  simp [h₁, h₂, h₃, f_eq_f', f', fc, Τ.value]
  aesop

lemma f_transfer_source {T : Τ K₁ K₂ V}
                        {σ : S K₁ K₂ V}
                        {π : BalanceProof K₁ K₂ C Pi V}
                        (h : ∃ block : {b : Block K₁ K₂ C Sigma V // b.isTransferBlock},
                               T ∈ TransactionsInBlock π block.1) :
                        (f σ T) .Source = σ .Source := by
  rcases h with ⟨⟨b, hb⟩, h₁⟩
  rcases T with ⟨⟨s, r, v⟩, hT⟩
  unfold Block.isTransferBlock at hb
  simp [TransactionsInBlock] at h₁
  split at h₁ <;> [simp at hb; skip; simp at hb]
  next a b c d e =>
  simp only [TransactionsInBlock_transfer, ite_not, List.mem_map, List.mem_attach, Subtype.mk.injEq,
    Prod.mk.injEq, true_and, Subtype.exists, exists_prop, Sum.exists, exists_and_left,
    Finset.mem_sort, Finset.mem_filter, Finset.mem_univ, Prod.exists, Sum.inl.injEq, exists_eq,
    and_true, reduceCtorEq, and_false, exists_false, or_false, exists_true_left, exists_const,
    Sum.inr.injEq, exists_eq_right_right, false_or, exists_eq_right] at h₁ ⊢
  rcases h₁ with ⟨k₁, h₁, ⟨k₂, ⟨h₂, h₃⟩⟩ | ⟨k₂, ⟨h₂, ⟨k₃, ⟨h₃, h₄⟩⟩⟩⟩⟩ <;>
  (simp [h₁, h₂, f_eq_f', f', fc, Τ.value]; aesop)

lemma f_deposit_block_source {σ : S K₁ K₂ V}
                             {π : BalanceProof K₁ K₂ C Pi V}
                             (b : Block K₁ K₂ C Sigma V)
                             (h : b.isDepositBlock) :
                             ((TransactionsInBlock π b).foldl f σ) .Source =
                             σ .Source - (b.getDeposit h).2.1 := by
  unfold Block.isDepositBlock at h
  simp only [TransactionsInBlock]
  split <;> [skip; simp at h; simp at h]
  next r v =>
  simp [TransactionsInBlock_deposit, Block.getDeposit, f_eq_f', f', fc]
  rw [sub_eq_add_neg]

@[simp]
lemma sort_empty_iff {α : Type} {r : α → α → Prop} {s : Finset α}
  [IsTotal α r] [IsTrans α r] [IsAntisymm α r] [DecidableRel r] :
  Finset.sort r s = [] ↔ s = ∅ := by
  refine' ⟨λ h ↦ _, λ h ↦ _⟩
  · rcases s with ⟨s, hs⟩
    simp [Finset.sort] at h
    have := Multiset.sort_eq (α := α) (r := r)
    apply congr_arg Multiset.ofList at h
    rw [Multiset.sort_eq] at h
    aesop
  · aesop

lemma f_withdrawal_block_source_aux {σ : S K₁ K₂ V}
                                    {l : List K₁}
                                    (h₀ : l.Nodup)
                                    (b : Block K₁ K₂ C Sigma V)
                                    (h : b.isWithdrawalBlock) :
                                    (List.foldl f' σ
                                      (List.map (λ s : K₁ ↦ ⟨(s, Kbar.Source, some (b.getWithdrawal h s)), by unfold Τ'.isValid; aesop⟩) l)).1
                                    .Source = σ .Source + ∑ x : K₁, if x ∈ l then (↑(b.getWithdrawal h x) ⊓ σ x) else 0 := by
  simp only
  induction' l with hd tl ih generalizing σ
  · simp
  · simp only [List.map_cons, List.foldl_cons]
    rw [ih]
    simp only [f', fc, e_def, Pi.sub_apply, Option.get_some, v'_key_eq_meet, ↓reduceIte,
      reduceCtorEq, sub_zero, one_smul, List.mem_cons]
    conv_rhs => rw [Finset.sum_ite]
    simp only [not_or, Finset.sum_const_zero, add_zero]
    rw [Finset.filter_or]
    rw [Finset.filter_eq']
    simp only [Finset.mem_univ, ↓reduceIte]
    rw [Finset.sum_union]
    simp only [Finset.sum_singleton]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    rw [add_assoc]
    simp only [add_right_inj, add_left_inj]
    simp only [Kbar.key.injEq, Sum.inl.injEq, zero_sub, neg_smul, ite_smul, one_smul, zero_smul]
    apply Finset.sum_congr rfl
    intros k₁ hk₁
    rw [if_neg]
    simp
    have : k₁ ∈ tl := by aesop
    aesop
    aesop
    aesop
    -- nth_rw 2 [sub_eq_add_neg]
    -- simp
    -- rw [add_comm]
    -- rw [←sub_eq_add_neg]
    -- simp


    -- rw [sub_add_eq_sub_sub_swap]





  -- generalize eq : (Finset.sort (·≤·) _ : List K₁) = l
  -- induction' l with hd tl ih generalizing σ
  -- · simp at eq
  --   rw [Finset.univ_eq_empty_iff] at eq
  --   aesop
  -- · simp

    -- unfold Block.isWithdrawalBlock at h
  -- simp only [TransactionsInBlock]
  -- split <;> [simp at h; simp at h; skip]
  -- next B =>
  -- simp [TransactionsInBlock_withdrawal, Block.getWithdrawal, f_eq_f', f', fc]
  -- rw [sub_eq_add_neg]

lemma f_withdrawal_block_source {σ : S K₁ K₂ V}
                                {π : BalanceProof K₁ K₂ C Pi V}
                                (b : Block K₁ K₂ C Sigma V)
                                (h : b.isWithdrawalBlock) :
                                ((TransactionsInBlock π b).foldl f σ) .Source =
                                σ .Source + ∑ k : K₁, (b.getWithdrawal h k).1 ⊓ σ k := by
  simp only [TransactionsInBlock]
  split <;> [simp at h; simp at h; skip]
  next B =>
  simp only [f_eq_f', TransactionsInBlock_withdrawal, List.pure_def, List.bind_eq_flatMap,
    exists_eq, Set.setOf_true, Set.toFinset_univ, Finset.mem_sort, Finset.mem_univ, forall_const,
    List.flatMap_subtype, List.unattach_attach, List.flatMap_singleton', Block.getWithdrawal]
  have : (Block.withdrawal B).getWithdrawal h = B := by ext k; simp [Block.getWithdrawal]
  simp_rw [←this]
  rw [f_withdrawal_block_source_aux]
  simp only [sub_right_inj]
  simp [Finset.mem_sort]
  simp


  -- have : ∃ (B : K₁ → V₊), b = .withdrawal B := by unfold Block.isWithdrawalBlock at h; aesop
  -- rcases this with ⟨B, hb⟩
  -- rcases


  -- split <;> [simp at h; simp at h; skip]
  -- next B =>
  -- simp [TransactionsInBlock_withdrawal, Block.getWithdrawal, f_eq_f', f', fc]



lemma f_transfer_block_source {σ : S K₁ K₂ V}
                              {π : BalanceProof K₁ K₂ C Pi V}
                              (b : Block K₁ K₂ C Sigma V)
                              (h : b.isTransferBlock) :
                              ((TransactionsInBlock π b).foldl f σ) .Source =
                              σ .Source := by
  rw [fold_f_any_transaction_transfer]
  intros T hT
  simp only [TransactionsInBlock] at hT
  rcases b with _ | ⟨a, b, c, d, e⟩ | _ <;> [simp at h; skip; simp at h]
  simp only [TransactionsInBlock_transfer, ite_not, List.mem_map, List.mem_attach, true_and,
    Subtype.exists, exists_prop, Sum.exists, exists_and_left, Finset.mem_sort, Finset.mem_filter,
    Finset.mem_univ, Prod.exists, Prod.mk.injEq, Sum.inl.injEq, exists_eq, and_true, reduceCtorEq,
    and_false, exists_false, or_false, exists_true_left, exists_const, Sum.inr.injEq,
    exists_eq_right_right, false_or, exists_eq_right] at hT
  aesop

end lemma5

-- lemma lemma5_aux {π : BalanceProof K₁ K₂ C Pi V}
--                  {h : ∀ T ∈ ts, ∃ block : Block K₁ K₂ C Sigma V, T ∈ TransactionsInBlock π block}
--                  {acc acc' : S K₁ K₂ V} :
--   (List.foldl f acc (List.map (TransactionsInBlock π) σ).flatten).1 .Source =
--   (∑ x ∈ Finset.univ ×ˢ Finset.univ,
--       if h : σ[x.1].isWithdrawalBlock = true then
--         ↑(σ[x.1].getWithdrawal ⋯ x.2) ⊓
--           ↑(List.foldl f (S.initial K₁ K₂ V) (List.map (TransactionsInBlock π) (List.take (↑x.1) σ)).flatten)
--             (Kbar.key (Sum.inl x.2))
--       else 0) -
--     aggregateDeposits σ

-- -- lemma lemma5_aux {ts : List (Τ K₁ K₂ V)}
-- --                  {π : BalanceProof K₁ K₂ C Pi V}
-- --                  {h : ∀ T ∈ ts, ∃ block : Block K₁ K₂ C Sigma V, T ∈ TransactionsInBlock π block}
-- --                  {acc acc' : S K₁ K₂ V} :
-- --   (List.foldl f acc ts).1 Kbar.Source =
-- --   acc .Source +
-- --   (∑ x : Fin ts.length × K₁,
-- --     if h : ∃ block : {b : Block K₁ K₂ C Sigma V // b.isWithdrawalBlock},
-- --              ts[x.1.1] ∈ TransactionsInBlock π block.1
-- --     then (ts[x.1.1].value.get (lemma5.isSome_of_withdrawal h)).1 ⊓
-- --          (List.foldl f acc'
-- --             (List.foldl (λ acc a ↦ acc ++ id a) ts (List.take x.1.1 (List.map (TransactionsInBlock π) σ)))).1 x.2
-- --     else 0) -
-- --     aggregateDeposits σ := by
-- --   induction' σ with hd tl ih
-- --   · simp

-- -- lemma lemma5_aux {ts : List (Τ K₁ K₂ V)}
-- --                  {π : BalanceProof K₁ K₂ C Pi V}
-- --                  {h : ∀ T ∈ ts, ∃ block : Block K₁ K₂ C Sigma V, T ∈ TransactionsInBlock π block}
-- --                  {acc acc' : S K₁ K₂ V} :
-- --   (List.foldl f acc
-- --                 (List.foldl (λ acc a ↦ acc ++ TransactionsInBlock π a) ts σ)).1
-- --                 Kbar.Source =
-- --   acc .Source +
-- --   (∑ x : Fin (List.length σ) × K₁,
-- --     if h : σ[↑x.1].isWithdrawalBlock
-- --     then ↑(σ[↑x.1].getWithdrawal h x.2) ⊓
-- --           (List.foldl f acc'
-- --             (List.foldl (λ acc a ↦ acc ++ id a) ts (List.take x.1.1 (List.map (TransactionsInBlock π) σ)))).1 x.2
-- --     else 0) -
-- --     aggregateDeposits σ := by
-- --   induction' σ with hd tl ih
-- --   · simp

-- lemma lemma5 {σ : RollupState K₁ K₂ V C Sigma}
--              {π : BalanceProof K₁ K₂ C Pi V} :
--   Bal π σ .Source =
--   (∑ (i : Fin σ.length) (k : K₁),
--      if h : σ[i].isWithdrawalBlock
--      then let w := σ[i].getWithdrawal h
--           w k ⊓ Bal π (σ.take i.1) k
--      else 0)
--   -
--   aggregateDeposits σ := by
--   simp only
--   unfold Bal fStar TransactionsInBlocks
--   simp only [← List.flatMap_def, List.flatMap_eq_foldl, Finset.univ_product_univ, Fin.getElem_fin, List.map_take]
--   simp_rw [List.flatten_eq_flatMap, List.flatMap_eq_foldl]
--   rw [lemma5_aux]
--   rfl

-- lemma www' {ts : List (Τ K₁ K₂ V)}:
--   (List.foldl f acc ts).1 Kbar.Source =
--   acc .Source + (List.foldl f (S.initial K₁ K₂ V) ts) .Source := by
--   simp
--   induction' ts with hd tl ih generalizing acc
--   · simp
--   · simp
--     rw [ih]


-- lemma www {acc} :
--   (List.foldl f
--     acc
--     (List.map (TransactionsInBlock π) tl).flatten).1 Kbar.Source =
--   acc .Source +
--   (List.foldl f (S.initial K₁ K₂ V) (List.map (TransactionsInBlock π) tl).flatten).1 Kbar.Source := by
--   simp
--   induction' tl with hd' tl' ih generalizing acc
--   · simp
--   · simp
--     rw [ih]
--     nth_rw 2 [ih]
--     simp



-- lemma lemma5_julian {σ : RollupState K₁ K₂ V C Sigma}
--                     {π : BalanceProof K₁ K₂ C Pi V} :
--   Bal π σ .Source =
--   (∑ (i : Fin σ.length) (k : K₁),
--      if h : σ[i].isWithdrawalBlock
--      then let w := σ[i].getWithdrawal h
--           w k ⊓ Bal π (σ.take i.1) k
--      else 0)
--   -
--   aggregateDeposits σ := by
--   simp [Bal, fStar]
--   induction' σ with hd tl ih
--   · simp
--   · simp only [TransactionsInBlocks_cons, List.foldl_append, List.length_cons, aggregateDeposits_cons]
--     rcases hd with ⟨r, v⟩ | _ | _
--     · 

--   -- · generalize eq : (_ : V) - _ = rhs
--   --   generalize eq₁ : (_ : V) - _ = rhsih at ih
--   --   unfold TransactionsInBlocks at ih
--   --   simp
--   --   rw [www]
--   --   simp [ih]


--     -- simp only [TransactionsInBlocks_cons, List.foldl_append, List.length_cons,
--     --   aggregateDeposits_cons]
--     -- generalize eq₁ : (List.map (TransactionsInBlock π) tl).flatten = smol at *
--     -- generalize eq₃ : List.foldl f (S.initial K₁ K₂ V) (TransactionsInBlock π hd) = acc'
--     -- rcases hd with ⟨r, v⟩ | _ | _
--     -- · have := lemma5.f_deposit_block_source (K₂ := K₂) (Sigma := Sigma) (π := π) (σ := S.initial K₁ K₂ V) (b := Block.deposit r v)
--     --   simp only at this




--   -- unfold Bal fStar
--   -- have := lemma5_aux''''' (σ := σ) (π := π)
--   --                         (acc := IterState.initial K₁ K₂ V)
--   --                         (acc' := IterState.initial K₁ K₂ V)
--   --                         (h := P_initial)
--   -- simp_rw [fold_fₜ_eq_fold_f] at this
--   -- exact this

-- -- lemma lemma5_aux'''' {σ : RollupState K₁ K₂ V C Sigma}
-- --                      {π : BalanceProof K₁ K₂ C Pi V}
-- --                      {l : List (Τ K₁ K₂ V)}
-- --                      {acc acc' : IterState K₁ K₂ V}
-- --                      (h₀ : ∀ T ∈ l, T ∈ TransactionsInBlocks π σ)
-- --                      (h : acc.s .Source = fStar acc.ts acc.s .Source) :
-- --   (List.foldl fₐ acc l).s Kbar.Source = -- prolly a list of transactions created by transactionsinblock
-- --   (∑ x : Fin (List.length σ) × K₁,
-- --      if h : σ[x.1].isWithdrawalBlock
-- --      then ↑(σ[x.1].getWithdrawal h x.2) ⊓
-- --           (List.foldl fα acc' (List.map (TransactionsInBlock π) (List.take x.1.1 σ)).flatten).s x.2
-- --      else 0) -
-- --   aggregateDeposits σ := sorry

--   -- by
--   -- induction' σ with hd tl ih generalizing acc acc'
--   -- · simp at h ⊢

-- -- lemma lemma5_aux''' {σ : RollupState K₁ K₂ V C Sigma}
-- --                     {π : BalanceProof K₁ K₂ C Pi V}
-- --                     {acc acc' : IterState K₁ K₂ V}
-- --                     (h : acc.s .Source = fStar acc.ts acc.s .Source) :
-- --   (List.foldl fₐ acc (List.map (TransactionsInBlock π) σ).flatten).s Kbar.Source = -- prolly a list of transactions created by transactionsinblock
-- --   (∑ x : Fin (List.length σ) × K₁,
-- --      if h : σ[x.1].isWithdrawalBlock
-- --      then ↑(σ[x.1].getWithdrawal h x.2) ⊓
-- --           (List.foldl fᵢ acc' (List.map (TransactionsInBlock π) (List.take x.1.1 σ)).flatten).s x.2
-- --      else 0) -
-- --   aggregateDeposits σ := by
-- --   induction' σ with hd tl ih generalizing acc acc'
-- --   · simp at h ⊢

-- -- def fᵢ (b : ℕ × S K₁ K₂ V) (T : Τ K₁ K₂ V) : ℕ × S K₁ K₂ V :=
-- --   ⟨b.1 + 1, f b.2 T⟩

-- -- lemma lemma5_aux'' {σ : RollupState K₁ K₂ V C Sigma}
-- --                    {π : BalanceProof K₁ K₂ C Pi V}
-- --                    {acc acc' : ℕ × S K₁ K₂ V}
-- --                    (h : acc.2 .Source = Bal π (σ.take acc.1) .Source) :
-- --   (List.foldl fᵢ acc (List.map (TransactionsInBlock π) σ).flatten).2 Kbar.Source =
-- --   (∑ x : Fin (List.length σ) × K₁,
-- --      if h : σ[x.1].isWithdrawalBlock
-- --      then ↑(σ[x.1].getWithdrawal h x.2) ⊓
-- --           (List.foldl fᵢ acc' (List.map (TransactionsInBlock π) (List.take x.1.1 σ)).flatten).2 x.2
-- --      else 0) -
-- --   aggregateDeposits σ := by
-- --   have :
-- --     (∑ x : Fin (List.length σ) × K₁,
-- --       if h : σ[x.1].isWithdrawalBlock = true then
-- --         (σ[x.1].getWithdrawal h x.2).1 ⊓
-- --           (List.foldl fᵢ acc' (List.map (TransactionsInBlock π) (List.take x.1.1 σ)).flatten).2 x.2
-- --       else 0) =
-- --     (∑ x : Fin (List.length σ),
-- --       if h : σ[x].isWithdrawalBlock = true then
-- --         ∑ y : K₁,
-- --         (σ[x].getWithdrawal h y).1 ⊓
-- --           (List.foldl fᵢ acc' (List.map (TransactionsInBlock π) (List.take x.1 σ)).flatten).2 y
-- --       else 0) := by
-- --       rw [Fintype.sum_prod_type]
-- --       apply Finset.sum_congr
-- --       rfl
-- --       intros i hi
-- --       simp only [Fin.getElem_fin, List.map_take]
-- --       by_cases eq : σ[i.1].isWithdrawalBlock
-- --       · simp only [eq, ↓reduceDIte]
-- --       · simp [eq]
-- --   rw [this]
-- --   simp only [Fin.getElem_fin, List.map_take]
-- --   induction' σ with hd tl ih generalizing acc acc'
-- --   · simp [Bal] at h; simp [h]
-- --   · simp only [List.map_cons, List.flatten_cons, List.foldl_append, List.length_cons,
-- --                aggregateDeposits_cons]
-- --     generalize eqsmol : (List.foldl _ _ _) = smol
-- --     rw [
-- --       Finset.sum_fin_eq_sum_range,
-- --       Finset.sum_eq_sum_diff_singleton_add (i := 0),
-- --       dif_pos (show 0 < tl.length + 1 by omega)
-- --     ]
-- --     simp_rw [List.getElem_cons_zero (h := _)]; case h => exact Finset.mem_range.2 (by omega)
-- --     generalize eqpartialsum : (∑ _ ∈ _, (_ : V)) = partialsum
-- --     rcases hd with ⟨r, v⟩ | _ | _
-- --     · simp [Block.getDeposit]
-- --       generalize eqsummand : ↑v + aggregateDeposits tl = summand
-- --       rw [←eqpartialsum]
-- --       let F : ℕ → V := λ x ↦
-- --         if h : x < tl.length then
-- --           ∑ k₁ : K₁,
-- --             if h' : (tl[x]'h).isWithdrawalBlock = true then
-- --               ((tl[x]'h).getWithdrawal h' k₁).1 ⊓
-- --                 (List.foldl fᵢ acc'
-- --                   (List.take (x + 1)
-- --                     (TransactionsInBlock (Sigma := Sigma) π (Block.deposit r v) :: List.map (TransactionsInBlock π) tl)).flatten).2 k₁
-- --             else 0
-- --         else 0
-- --       let F' : (a : ℕ) → a ∈ Finset.range (tl.length + 1) \ {0} → ℕ :=
-- --         λ a ha ↦ a.pred
-- --       rw [Finset.sum_bij (t := Finset.range tl.length) (g := F) (i := F')]
-- --       swap
-- --       simp [F']; intros a ha₁ ha₂; omega
-- --       swap
-- --       simp [F']; intros a ha b hb; omega
-- --       swap
-- --       simp [F']; intros b hb; use b + 1; omega
-- --       swap
-- --       simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton, List.take_succ_cons,
-- --         List.flatten_cons, List.foldl_append, Finset.sum_dite_irrel, Finset.sum_const_zero,
-- --         Nat.pred_eq_sub_one, and_imp, F, F']
-- --       intros i hi₁ hi₂
-- --       rw [dif_pos hi₁]; nth_rw 2 [dif_pos (by omega)]
-- --       rcases i with _ | i <;> [contradiction; skip]
-- --       simp only [List.getElem_cons_succ, List.take_succ_cons, List.flatten_cons, List.foldl_append,
-- --         Finset.sum_dite_irrel, Finset.sum_const_zero, add_tsub_cancel_right, Nat.add_one_sub_one,
-- --         Int.Nat.cast_ofNat_Int, id_eq, Int.reduceNeg, Int.reduceAdd]
-- --       simp only [List.take_succ_cons, List.flatten_cons, List.foldl_append, Finset.sum_dite_irrel,
-- --         Finset.sum_const_zero, F]
-- --       rw [Finset.sum_dite_of_true]; case h => exact λ _ ↦ (Finset.mem_range.1 ·)
-- --       simp only [← eqsmol, Finset.univ_eq_attach]
-- --       rw [ih (acc' := acc'), Finset.sum_fin_eq_sum_range]
-- --       swap
-- --       simp

-- --       simp only [Fin.getElem_fin, List.map_take]
-- --       rw [Finset.sum_dite_of_true]; case h => exact λ _ ↦ (Finset.mem_range.1 ·)
-- --       simp only [Finset.univ_eq_attach]
-- --       rw [←eqsummand]
-- --       generalize eqindices : (Finset.range tl.length).attach = indices
-- --       rw [sub_add_eq_sub_sub]
-- --       simp only [sub_left_inj, transactionsInBlock_deposit, List.foldl_cons, List.foldl_nil]
-- --       rw [List.foldl_assoc]
-- --       have : f acc' ⟨(Kbar.Source, Kbar.key (Sum.inr r), some v), ⋯⟩

-- -- -- #exit

-- -- -- invariant: split into two parts, show something! (needs acc × nat)
-- -- lemma lemma5_aux' {σ : RollupState K₁ K₂ V C Sigma}
-- --                   {π : BalanceProof K₁ K₂ C Pi V}
-- --                   {acc acc' : S K₁ K₂ V}
-- --                   (h₁ :  )
-- --                   (h₂ : acc' .Source ≤ 0) :
-- --   (List.foldl f acc (List.map (TransactionsInBlock π) σ).flatten).1 Kbar.Source =
-- --   (∑ x : Fin (List.length σ) × K₁,
-- --      if h : σ[x.1].isWithdrawalBlock
-- --      then ↑(σ[x.1].getWithdrawal h x.2) ⊓
-- --           (List.foldl f acc' (List.map (TransactionsInBlock π) (List.take x.1.1 σ)).flatten).1 x.2
-- --      else 0) -
-- --   aggregateDeposits σ := by
-- --   have :
-- --     (∑ x : Fin (List.length σ) × K₁,
-- --       if h : σ[x.1].isWithdrawalBlock = true then
-- --         (σ[x.1].getWithdrawal h x.2).1 ⊓
-- --           (List.foldl f acc' (List.map (TransactionsInBlock π) (List.take x.1.1 σ)).flatten).1 x.2
-- --       else 0) =
-- --     (∑ x : Fin (List.length σ),
-- --       if h : σ[x].isWithdrawalBlock = true then
-- --         ∑ y : K₁,
-- --         (σ[x].getWithdrawal h y).1 ⊓
-- --           (List.foldl f acc' (List.map (TransactionsInBlock π) (List.take x.1 σ)).flatten).1 y
-- --       else 0) := by
-- --       rw [Fintype.sum_prod_type]
-- --       apply Finset.sum_congr
-- --       rfl
-- --       intros i hi
-- --       simp only [Fin.getElem_fin, List.map_take]
-- --       by_cases eq : σ[i.1].isWithdrawalBlock
-- --       · simp only [eq, ↓reduceDIte]
-- --       · simp [eq]
-- --   rw [this]
-- --   induction' σ with hd tl ih generalizing acc acc'
-- --   · simp at h₁
-- --     simp
-- --     sorry
-- --   · simp only [List.map_cons, List.flatten_cons, List.foldl_append, List.length_cons,
-- --                Fin.getElem_fin, List.map_take, aggregateDeposits_cons]
-- --     generalize eqsmol : (List.foldl _ _ _) = smol
-- --     rw [
-- --       Finset.sum_fin_eq_sum_range,
-- --       Finset.sum_eq_sum_diff_singleton_add (i := 0),
-- --       dif_pos (show 0 < tl.length + 1 by omega)
-- --     ]
-- --     simp_rw [List.getElem_cons_zero (h := _)]; case h => exact Finset.mem_range.2 (by omega)
-- --     generalize eqpartialsum : (∑ _ ∈ _, (_ : V)) = partialsum
-- --     rcases hd with ⟨r, v⟩ | _ | _
-- --     · simp [Block.getDeposit]
-- --       generalize eqsummand : ↑v + aggregateDeposits tl = summand
-- --       rw [←eqpartialsum]
-- --       let F : ℕ → V := λ x ↦
-- --         if h : x < tl.length then
-- --           ∑ k₁ : K₁,
-- --             if h' : (tl[x]'h).isWithdrawalBlock = true then
-- --               ((tl[x]'h).getWithdrawal h' k₁).1 ⊓
-- --                 (List.foldl f acc'
-- --                   (List.take (x + 1)
-- --                     (TransactionsInBlock (Sigma := Sigma) π (Block.deposit r v) :: List.map (TransactionsInBlock π) tl)).flatten).1 k₁
-- --             else 0
-- --         else 0
-- --       let F' : (a : ℕ) → a ∈ Finset.range (tl.length + 1) \ {0} → ℕ :=
-- --         λ a ha ↦ a.pred
-- --       rw [Finset.sum_bij (t := Finset.range tl.length) (g := F) (i := F')]
-- --       swap
-- --       simp [F']; intros a ha₁ ha₂; omega
-- --       swap
-- --       simp [F']; intros a ha b hb; omega
-- --       swap
-- --       simp [F']; intros b hb; use b + 1; omega
-- --       swap
-- --       simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton, List.take_succ_cons,
-- --         List.flatten_cons, List.foldl_append, Finset.sum_dite_irrel, Finset.sum_const_zero,
-- --         Nat.pred_eq_sub_one, and_imp, F, F']
-- --       intros i hi₁ hi₂
-- --       rw [dif_pos hi₁]; nth_rw 2 [dif_pos (by omega)]
-- --       rcases i with _ | i <;> [contradiction; skip]
-- --       simp only [List.getElem_cons_succ, List.take_succ_cons, List.flatten_cons, List.foldl_append,
-- --         Finset.sum_dite_irrel, Finset.sum_const_zero, add_tsub_cancel_right, Nat.add_one_sub_one,
-- --         Int.Nat.cast_ofNat_Int, id_eq, Int.reduceNeg, Int.reduceAdd]
-- --       simp only [List.take_succ_cons, List.flatten_cons, List.foldl_append, Finset.sum_dite_irrel,
-- --         Finset.sum_const_zero, F]
-- --       rw [Finset.sum_dite_of_true]; case h => exact λ _ ↦ (Finset.mem_range.1 ·)
-- --       simp only [← eqsmol, Finset.univ_eq_attach]
-- --       rw [ih (acc' := acc'), Finset.sum_fin_eq_sum_range]
-- --       simp only [Fin.getElem_fin, List.map_take]
-- --       rw [Finset.sum_dite_of_true]; case h => exact λ _ ↦ (Finset.mem_range.1 ·)
-- --       simp only [Finset.univ_eq_attach]
-- --       rw [←eqsummand]
-- --       generalize eqindices : (Finset.range tl.length).attach = indices
-- --       rw [sub_add_eq_sub_sub]
-- --       simp only [sub_left_inj, transactionsInBlock_deposit, List.foldl_cons, List.foldl_nil]
-- --       rw [List.foldl_assoc]
-- --       have : f acc' ⟨(Kbar.Source, Kbar.key (Sum.inr r), some v), ⋯⟩
-- --       -- IsGLB (V' b T k) (f b T k



-- --   done

-- -- -- #exit

-- -- lemma lemma5_aux {σ : RollupState K₁ K₂ V C Sigma}
-- --                  {π : BalanceProof K₁ K₂ C Pi V}
-- --                  {acc acc' : S K₁ K₂ V}
-- --                  (h₁ : acc .Source = 0)
-- --                  (h₂ : acc' .Source = 0) :
-- --   (fStar (TransactionsInBlocks π σ) acc).1 Kbar.Source =
-- --   (∑ x : Fin (List.length σ) × K₁,
-- --     if h : σ[↑x.1].isWithdrawalBlock = true then
-- --       ↑(σ[↑x.1].getWithdrawal h x.2) ⊓
-- --         (fStar (TransactionsInBlocks π (List.take x.1.1 σ)) acc').1 x.2
-- --     else 0) -
-- --     aggregateDeposits σ := by apply lemma5_aux' <;> assumption
-- --   -- unfold fStar
-- --   -- induction' σ with hd tl ih generalizing acc acc'
-- --   -- · simp [h₁]
-- --   -- · simp
-- --   --   rw [List.foldl_flatten, List.foldl_map]




-- --   sorry

set_option maxHeartbeats 600000 in
/--
Obviously needs to be cleaned up.
-/
private lemma computeBalance'_eq_Erik_aux : computeBalance' σ v = v + computeBalanceErik σ := by
  sorry
  -- induction' σ with hd tl ih generalizing v
  -- · simp [computeBalanceErik, aggregateWithdrawals, aggregateDeposits]
  -- · rw [computeBalance'_eq_zero]; simp
  --   unfold computeBalance' computeBalanceErik aggregateWithdrawals aggregateDeposits at ih ⊢
  --   rw [ih]
  --   lift_lets
  --   intros d₁ w₁ d₂ w₂
  --   match heq : hd with
  --   | .transfer .. => have eq₁ : d₁ = d₂ := by
  --                       simp [d₁, d₂]
  --                       simp [Finset.sum_fin_eq_sum_range]
  --                       nth_rw 2 [Finset.sum_eq_sum_diff_singleton_add (i := 0)]
  --                       rw [dif_pos (show 0 < tl.length + 1 by omega)]
  --                       rw [dif_neg (by aesop)]
  --                       let F : ℕ → V := λ i ↦
  --                         if h : i < tl.length then
  --                         if h_1 : tl[i].isDepositBlock = true then
  --                         (tl[i].getDeposit h_1).2 else 0
  --                         else 0
  --                       let F' : (a : ℕ) → a ∈ Finset.range (tl.length + 1) \ {0} → ℕ :=
  --                         λ a ha ↦ a.pred
  --                       nth_rw 2 [Finset.sum_bij (t := Finset.range tl.length) (g := F)]
  --                       simp [F]
  --                       exact F'
  --                       simp [F']
  --                       intros a ha₁ ha₂
  --                       omega
  --                       simp [F']; intros a ha₁ ha₂ b hb₁ hb₂ h₃
  --                       omega
  --                       simp [F']
  --                       intros b hb
  --                       use b.succ
  --                       simpa
  --                       simp [F', F]
  --                       intros a ha₁ ha₂
  --                       rw [dif_pos ha₁]
  --                       have : a - 1 < tl.length ↔ a < tl.length + 1 := by omega
  --                       simp_rw [this, dif_pos ha₁]
  --                       rcases a with _ | a; simp at ha₂
  --                       simp
  --                       rw [Finset.mem_range]; omega
  --                     have eq₂ : w₁ = w₂ := by
  --                       simp [w₁, w₂]
  --                       simp [Finset.sum_fin_eq_sum_range]
  --                       nth_rw 2 [Finset.sum_eq_sum_diff_singleton_add (i := 0)]
  --                       rw [dif_pos (show 0 < tl.length + 1 by omega)]
  --                       rw [dif_neg (by aesop)]
  --                       let F : ℕ → V := λ i ↦
  --                         if h : i < tl.length then
  --                         if h_1 : tl[i].isWithdrawalBlock = true
  --                         then ∑ x_1 : K₁, tl[i].getWithdrawal h_1 x_1 else 0
  --                         else 0
  --                       let F' : (a : ℕ) → a ∈ Finset.range (tl.length + 1) \ {0} → ℕ :=
  --                         λ a ha ↦ a.pred
  --                       nth_rw 2 [Finset.sum_bij (t := Finset.range tl.length) (g := F)]
  --                       simp [F]
  --                       exact F'
  --                       simp [F']
  --                       intros a ha₁ ha₂
  --                       omega
  --                       simp [F']; intros a ha₁ ha₂ b hb₁ hb₂ h₃
  --                       omega
  --                       simp [F']
  --                       intros b hb
  --                       use b.succ
  --                       simpa
  --                       simp [F', F]
  --                       intros a ha₁ ha₂
  --                       rw [dif_pos ha₁]
  --                       have : a - 1 < tl.length ↔ a < tl.length + 1 := by omega
  --                       simp_rw [this, dif_pos ha₁]
  --                       rcases a with _ | a; simp at ha₂
  --                       simp
  --                       rw [Finset.mem_range]; omega
  --                     simp [eq₁, eq₂]
  --   | .deposit _ v => have : w₁ = w₂ := by
  --                       simp [w₁, w₂]
  --                       simp [Finset.sum_fin_eq_sum_range]
  --                       nth_rw 2 [Finset.sum_eq_sum_diff_singleton_add (i := 0)]
  --                       rw [dif_pos (show 0 < tl.length + 1 by omega)]
  --                       rw [dif_neg (by aesop)]
  --                       let F : ℕ → V := λ i ↦
  --                         if h : i < tl.length then
  --                         if h_1 : tl[i].isWithdrawalBlock = true
  --                         then ∑ x_1 : K₁, tl[i].getWithdrawal h_1 x_1 else 0
  --                         else 0
  --                       let F' : (a : ℕ) → a ∈ Finset.range (tl.length + 1) \ {0} → ℕ :=
  --                         λ a ha ↦ a.pred
  --                       nth_rw 2 [Finset.sum_bij (t := Finset.range tl.length) (g := F)]
  --                       simp [F]
  --                       exact F'
  --                       simp [F']
  --                       intros a ha₁ ha₂
  --                       omega
  --                       simp [F']; intros a ha₁ ha₂ b hb₁ hb₂ h₃
  --                       omega
  --                       simp [F']
  --                       intros b hb
  --                       use b.succ
  --                       simpa
  --                       simp [F', F]
  --                       intros a ha₁ ha₂
  --                       rw [dif_pos ha₁]
  --                       have : a - 1 < tl.length ↔ a < tl.length + 1 := by omega
  --                       simp_rw [this, dif_pos ha₁]
  --                       rcases a with _ | a; simp at ha₂
  --                       simp
  --                       rw [Finset.mem_range]; omega
  --                     simp [this]
  --                     rw [add_sub]
  --                     simp [d₁, d₂]
  --                     simp [Finset.sum_fin_eq_sum_range]
  --                     nth_rw 2 [Finset.sum_eq_sum_diff_singleton_add (i := 0)]
  --                     rw [dif_pos (show 0 < tl.length + 1 by omega)]
  --                     rw [dif_pos (by aesop)]
  --                     simp_rw [List.getElem_cons_zero, heq]
  --                     dsimp [Block.getDeposit] -- TODO: make lemma
  --                     nth_rw 2 [add_comm]
  --                     apply congr_arg
  --                     symm
  --                     -- reorder
  --                     let F' : (a : ℕ) → a ∈ Finset.range (tl.length + 1) \ {0} → ℕ :=
  --                         λ a ha ↦ a.pred
  --                     apply Finset.sum_bij (i := F')
  --                     simp [F']
  --                     intros a ha₁ ha₂
  --                     omega
  --                     simp [F']; intros a ha₁ ha₂ b hb₁ hb₂ h₃
  --                     omega
  --                     simp [F']
  --                     intros b hb
  --                     use b.succ
  --                     simpa
  --                     simp [F']
  --                     rintro a ⟨ha₁, ha₂⟩
  --                     rw [dif_pos ha₁]
  --                     have : a - 1 < tl.length ↔ a < tl.length + 1 := by omega
  --                     simp_rw [this, dif_pos ha₁]
  --                     rcases a with _ | a; simp at ha₂
  --                     simp
  --                     rw [Finset.mem_range]; omega
  --   | .withdrawal B => have eq₁ : d₁ = d₂ := by
  --                        simp [d₁, d₂]
  --                        simp [Finset.sum_fin_eq_sum_range]
  --                        nth_rw 2 [Finset.sum_eq_sum_diff_singleton_add (i := 0)]
  --                        rw [dif_pos (show 0 < tl.length + 1 by omega)]
  --                        rw [dif_neg (by aesop)]
  --                        let F : ℕ → V := λ i ↦
  --                          if h : i < tl.length then
  --                          if h_1 : tl[i].isDepositBlock = true then
  --                          (tl[i].getDeposit h_1).2 else 0
  --                          else 0
  --                        let F' : (a : ℕ) → a ∈ Finset.range (tl.length + 1) \ {0} → ℕ :=
  --                          λ a ha ↦ a.pred
  --                        nth_rw 2 [Finset.sum_bij (t := Finset.range tl.length) (g := F)]
  --                        simp [F]
  --                        exact F'
  --                        simp [F']
  --                        intros a ha₁ ha₂
  --                        omega
  --                        simp [F']; intros a ha₁ ha₂ b hb₁ hb₂ h₃
  --                        omega
  --                        simp [F']
  --                        intros b hb
  --                        use b.succ
  --                        simpa
  --                        simp [F', F]
  --                        intros a ha₁ ha₂
  --                        rw [dif_pos ha₁]
  --                        have : a - 1 < tl.length ↔ a < tl.length + 1 := by omega
  --                        simp_rw [this, dif_pos ha₁]
  --                        rcases a with _ | a; simp at ha₂
  --                        simp
  --                        rw [Finset.mem_range]; omega
  --                      simp [eq₁]
  --                      rw [add_sub, add_comm]
  --                      rw [←add_sub]
  --                      nth_rw 2 [sub_eq_add_neg]
  --                      simp [w₁, w₂]
  --                      simp [Finset.sum_fin_eq_sum_range]
  --                      nth_rw 3 [Finset.sum_eq_sum_diff_singleton_add (i := 0)]
  --                      rw [dif_pos (show 0 < tl.length + 1 by omega)]
  --                      rw [dif_pos (by aesop)]
  --                      simp_rw [List.getElem_cons_zero]
  --                      conv_rhs => congr
  --                                  arg 2
  --                                  simp [heq]
  --                                  simp [Block.getWithdrawal] -- LEMMA
  --                      rw [neg_add]
  --                      rw [add_comm]
  --                      rw [sub_eq_add_neg]
  --                      apply congr_arg
  --                      -- shuffle
  --                      let F : ℕ → V := λ i ↦
  --                        if h : i < tl.length then
  --                        if h_1 : tl[i].isWithdrawalBlock = true
  --                        then ∑ x_1 : K₁, tl[i].getWithdrawal h_1 x_1 else 0
  --                        else 0
  --                      let F' : (a : ℕ) → a ∈ Finset.range (tl.length + 1) \ {0} → ℕ :=
  --                        λ a ha ↦ a.pred
  --                      nth_rw 2 [Finset.sum_bij (t := Finset.range tl.length) (g := F)]
  --                      exact F'
  --                      simp [F']
  --                      intros a ha₁ ha₂
  --                      omega
  --                      simp [F']; intros a ha₁ ha₂ b hb₁ hb₂ h₃
  --                      omega
  --                      simp [F']
  --                      intros b hb
  --                      use b.succ
  --                      simpa
  --                      simp [F', F]
  --                      intros a ha₁ ha₂
  --                      rw [dif_pos ha₁]
  --                      have : a - 1 < tl.length ↔ a < tl.length + 1 := by omega
  --                      simp_rw [this, dif_pos ha₁]
  --                      rcases a with _ | a; simp at ha₂
  --                      simp
  --                      rw [Finset.mem_range]; omega

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

/-
I'll clean up later.
-/
section UgliestProofIveEverWritten

set_option maxHeartbeats 400000 in
/-
Sketch. This can be cleaned up both Lean wise and maybe ven math wise, but it goes through
and Lean is happy so I'll move on for now.
-/
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
  sorry
  -- simp [attackGameR] at h₁
  -- /-
  --   Ideally, we want to show that `(attackGameR requests []).isWithdrawal → requests[i].isWithdrawal`,
  --   but we'll prove it as a corollary of this one for an arbitrary state σ rather than [].
  -- -/

  -- /-
  --   By induction on requests for an arbitrary `i`.
  -- -/
  -- induction' requests with hd tl ih generalizing i
  -- /-
  --   The base case is trivial.
  -- -/
  -- · simp at hi₂ h₁; omega
  -- /-
  --   Suppose the requests are `hd :: tl`. (I.e. a single element followed by some tail.)
  -- -/
  -- · rcases i with _ | i
  --   /-
  --     Suppose first that i = 0.

  --     Then we know we are accessing the very first request and as such, one only needs to consult
  --     the function `Request.toBlock!` to establish this holds.
  --   -/
  --   · simp at hi₁
  --     subst hi₁
  --     simp [Request.toBlock!] at h₁ ⊢
  --     rcases hd <;> simp_all
  --   /-
  --     Suppose next that i = i + 1.
  --   -/
  --   · rcases σ with _ | ⟨hd', tl'⟩
  --     /-
  --       Suppose further that `σ` is empty.

  --       We can immediately conclude this holds by the inductive hypothesis and the fact that
  --       the shape of blocks is invariant with respect to state and is dependent only on the shape
  --       of the initial requests (as witnessed by `attackGameRGo_isWithdrawal_iff`).
  --     -/
  --     · simp at hi₁ hi₂ h₁ ih ⊢
  --       apply ih (by aesop)
  --       rw [attackGameRGo_isWithdrawal_iff (σ' := RollupState.appendBlock! [] hd)]
  --       exact h₁
  --       exact hi₂
  --     /-
  --       Suppose now that `σ` is _not_ empty, but `hd' :: tl'`.

  --       Note we have that `tl'.length ≤ i`.
  --     -/
  --     · simp at hi₁ ⊢
  --       rw [le_iff_eq_or_lt] at hi₁
  --       rcases hi₁ with hi₁ | hi₁
  --       /-
  --         For the case where `tl'.length = i`, we know we are accessing `hd` and the rest is trivial.
  --       -/
  --       · simp_rw [hi₁]; simp
  --         simp [Request.toBlock!] at h₁ ⊢
  --         simp_rw [←hi₁] at h₁
  --         rw [List.getElem_append_right] at h₁
  --         simp [Request.toBlock!] at h₁ ⊢
  --         rcases hd <;> simp_all
  --         simp
  --       /-
  --         For when `tl'.length < i`, we know that accessing `(hd :: tl)[i - tl'.length]`
  --         always reaches the tail as `i - tl'.length > 0`. Thus, we can invoke the inductive hypothesis
  --         together with lemma `attackGameRGo_isWithdrawal_iff` to establish this holds.
  --       -/
  --       · rw [lt_iff_exists_add] at hi₁
  --         rcases hi₁ with ⟨c, ⟨hc₁, hc₂⟩⟩
  --         simp_rw [hc₂]
  --         rcases c with _ | c <;> [simp at hc₁; skip]
  --         simp
  --         specialize ih (by aesop) (c + (hd' :: tl').length)
  --         simp at ih
  --         apply ih
  --         swap
  --         simp at hi₂
  --         omega
  --         simp_rw [←Nat.add_assoc]
  --         simp
  --         simp at h₁
  --         simp_rw [hc₂] at h₁
  --         simp_rw [←Nat.add_assoc] at h₁
  --         simp_rw [List.append_cons (as := tl') (b := Request.toBlock! (hd' :: tl') hd) (bs := attackGameRGo tl (RollupState.appendBlock! (hd' :: tl') hd))] at h₁
  --         rw [List.getElem_append_right (as := tl' ++ [Request.toBlock! (hd' :: tl') hd]) (bs :=
  --             attackGameRGo tl (RollupState.appendBlock! (hd' :: tl') hd))] at h₁
  --         rw [List.getElem_append_right]
  --         simp at h₁ ⊢
  --         rw [attackGameRGo_isWithdrawal_iff (σ' := (hd' :: tl'))] at h₁
  --         exact h₁
  --         simp
  --         simp at hc₂ hi₂ ⊢

end UgliestProofIveEverWritten

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

lemma lemma5 (π : BalanceProof K₁ K₂ C Pi V) :
  Bal π σ .Source =
  (∑ (i : Fin σ.length) (k : K₁),
     if h : σ[i].isWithdrawalBlock
     then let w := σ[i].getWithdrawal h
          w k ⊓ Bal π (σ.take i.1) k
     else 0)
  -
  aggregateDeposits σ := by sorry
  -- unfold Bal
  -- rcases σ with _ | ⟨σ, σs⟩
  -- · simp [Bal]
  -- · simp only
  --   apply lemma5_aux <;> simp

-- #exit

variable -- [ADScheme K₂ (C × K₁ × ExtraDataT) C Pi]
         [Hinj : CryptoAssumptions.Injective (H (α := TransactionBatch K₁ K₂ V × ExtraDataT) (ω := (C × K₁ × ExtraDataT)))]
         (isπ : isπ (normalise requests))

def BalanceProof.initial : BalanceProof K₁ K₂ C Pi V := λ _ ↦ .none

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

instance : Setoid' ((Pi × ExtraDataT) × TransactionBatch K₁ K₂ V) where
  isEquiv := by unfold IsEquivRel
                intros a b
                unfold iso
                simp [(·≤·)]
                aesop

section Ordering

lemma w₁ {x y : Option ((Pi × ExtraDataT) × TransactionBatch K₁ K₂ V)} :
  x ≠ .none → y ≠ .none → x ≤ y → x ≤ (Dict.First x y) :=
  λ h₁ h₂ h₃ ↦ by simp [Dict.First]; aesop

lemma w₂ {x y : Option ((Pi × ExtraDataT) × TransactionBatch K₁ K₂ V)} :
  x ≠ .none → y ≠ .none → x ≤ y → y ≤ (Dict.First x y) :=
  λ h₁ h₂ h₃ ↦ by
    simp [Dict.First]
    unfold LE.le Preorder.toLE maybeInduced at *
    simp [LE.le, Preorder.toLE, instPreorderTransactionBatch, discretePreorder] at h₃
    rcases x with _ | x <;> rcases y with _ | y <;> aesop

lemma w₃ {x y : BalanceProof K₁ K₂ C Pi V} :
  ∀ k, x k ≠ .none → y k ≠ .none → x k ≤ y k → x ≤ Dict.Merge x y :=
  λ k h₁ h₂ h₃ ↦ by
    simp [Dict.Merge]; unfold Dict.Merge.D; rw [_root_.Pi.le_def]; simp [Dict.First]
    unfold LE.le Preorder.toLE maybeInduced at h₃
    simp [LE.le, Preorder.toLE, instPreorderTransactionBatch, discretePreorder] at h₃
    aesop (config := {warnOnNonterminal := false})
    simp [(·≤·)]

lemma w₃' {x y : BalanceProof K₁ K₂ C Pi V} :
  ∀ k, x k ≠ .none → y k ≠ .none → x k ≤ y k → x k ≤ Dict.Merge x y k :=
  λ k h₁ h₂ h₃ ↦ by
    simp [Dict.Merge]; unfold Dict.Merge.D LE.le Preorder.toLE maybeInduced; simp [Dict.First]
    unfold LE.le Preorder.toLE maybeInduced at h₃
    simp [LE.le, Preorder.toLE, instPreorderTransactionBatch, discretePreorder] at h₃
    aesop

lemma w₄ {x y : BalanceProof K₁ K₂ C Pi V} :
  ∀ k, x k ≠ .none → y k ≠ .none → x k ≤ y k → y k ≤ Dict.Merge x y k :=
  λ k h₁ h₂ h₃ ↦ by
    simp [Dict.Merge]; unfold Dict.Merge.D LE.le Preorder.toLE maybeInduced; simp [Dict.First]
    unfold LE.le Preorder.toLE maybeInduced at h₃
    simp [LE.le, Preorder.toLE, instPreorderTransactionBatch, discretePreorder] at h₃
    aesop

lemma proposition4W {x y : Option ((Pi × ExtraDataT) × TransactionBatch K₁ K₂ V)}
  (h : x.isSome ∧ y.isSome → x = y) : IsLUB {x, y} (Dict.First x y) := by
  simp [IsLUB, IsLeast, lowerBounds, Dict.First]
  aesop (config := {warnOnNonterminal := false}) <;> simp [(·≤·)]

@[simp]
lemma BalanceProof.snd_discrete {x y : TransactionBatch K₁ K₂ V} :
  @LE.le (TransactionBatch K₁ K₂ V) Preorder.toLE x y ↔ x = y := by
  unfold LE.le Preorder.toLE instPreorderTransactionBatch
  aesop

-- lemma proposition2 {x y π : BalanceProof K₁ K₂ C Pi V} :
--   IsLUB {x, y} π ↔ x = y := by
--   unfold IsLUB IsLeast upperBounds lowerBounds
--   apply Iff.intro <;> intros h
--   · rcases h with ⟨h₁, h₂⟩
--     simp at h₁ h₂
--     rcases h₁ with ⟨h₃, h₄⟩
--     simp [-Prod.forall, (·≤·)] at h₃ h₄
--     apply funext; intros K
--     set X := x K with eqX
--     set Y := y K with eqY
--     set PI := π K with eqPI
--     rcases X with _ | X <;>
--     rcases Y with _ | Y <;>
--     rcases PI with _ | PI
--     · rfl
--     · rfl
--     · specialize h₄ K

--     · simp at h₄
--       exfalso
--       clear h₃
--       specialize @h₂ y
--       simp [-Prod.forall, (·≤·)] at h₂







--   done

-- lemma proposition6 {x y : BalanceProof K₁ K₂ C Pi V}
--   (h : ∀ k, k ∈ x ∧ k ∈ y → x = y) : IsLUB {x, y} (Dict.Merge x y) := by
--   sorry
--   -- unfold Dict.Merge Dict.Merge.D Dict.First
--   -- simp [IsLUB, IsLeast, lowerBounds]
--   -- split_ands
--   -- · intros i; simp
--   --   aesop (config := {warnOnNonterminal := false}); simp [(·≤·)]
--   -- · intros i; simp
--   --   set X := x i with eqX
--   --   set Y := y i with eqY
--   --   rcases X with _ | X <;> rcases Y with _ | Y
--   --   · simp [(·≤·)]
--   --   · simp [(·≤·)]
--   --   · simp [(·≤·)]
--   --   · have eq₁ : (x i).isSome := by rw [←eqX]; simp
--   --     have eq₂ : (y i).isSome := by rw [←eqY]; simp
--   --     simp [←Dict.mem_iff_isSome] at h
--   --     have eq₃ : i ∈ x := Dict.mem_iff_isSome.2 eq₁
--   --     have eq₄ : i ∈ y := Dict.mem_iff_isSome.2 eq₂
--   --     have : x = y := by aesop
--   --     subst this
--   --     rw [eqX, eqY]
--   --     aesop
--   -- · intros π hπ₁ hπ₂ i; simp
--   --   have hπ₁' : ∀ k, x k ≤ π k := by aesop
--   --   have hπ₂' : ∀ k, y k ≤ π k := by aesop
--   --   set X := x i with eqX
--   --   set Y := y i with eqY
--   --   set PI := π i with eqPI
--   --   rcases X with _ | X <;> rcases Y with _ | Y <;> rcases PI with _ | PI
--   --   · simp [(·≤·)]
--   --   · simp [(·≤·)]
--   --   · specialize hπ₂' i
--   --     rw [←eqPI, ←eqY] at hπ₂'
--   --     simp [(·≤·)] at hπ₂'
--   --   · aesop
--   --   · specialize hπ₂' i
--   --     rw [←eqPI] at hπ₂'
--   --     specialize hπ₁' i
--   --     rw [←eqPI] at hπ₁'
--   --     simp
--   --     rw [eqX]
--   --     assumption
--   --   · specialize hπ₂' i
--   --     specialize hπ₁' i
--   --     aesop
--   --   · specialize hπ₂' i
--   --     specialize hπ₁' i
--   --     aesop
--   --   · specialize hπ₂' i
--   --     specialize hπ₁' i
--   --     aesop

-- lemma proposition6' {x y : BalanceProof K₁ K₂ C Pi V}
--   (h : ∀ k, k ∈ x ∧ k ∈ y → x ≤ y ∧ y ≤ x) : IsLUB {x, y} (Dict.Merge x y) := by
--   unfold Dict.Merge Dict.Merge.D Dict.First
--   simp [IsLUB, IsLeast, lowerBounds]
--   split_ands
--   · intros i; simp
--     aesop (config := {warnOnNonterminal := false}); simp [(·≤·)]
--   · intros i; simp
--     set X := x i with eqX
--     set Y := y i with eqY
--     rcases X with _ | X <;> rcases Y with _ | Y
--     · simp [(·≤·)]
--     · simp [(·≤·)]
--     · simp [(·≤·)]
--     · have eq₁ : (x i).isSome := by rw [←eqX]; simp
--       have eq₂ : (y i).isSome := by rw [←eqY]; simp
--       simp [←Dict.mem_iff_isSome, -Prod.forall] at h
--       have eq₃ : i ∈ x := Dict.mem_iff_isSome.2 eq₁
--       have eq₄ : i ∈ y := Dict.mem_iff_isSome.2 eq₂
--       have : x ≤ y ∧ y ≤ x := h _ eq₃ eq₄
--       rw [eqX, eqY]
--       rw [Dict.mem_iff_isSome] at eq₃
--       rw [Dict.mem_iff_isSome] at eq₄
--       apply w₄ <;> aesop
--   · intros π hπ₁ hπ₂ i; simp
--     have hπ₁' : ∀ k, x k ≤ π k := by aesop
--     have hπ₂' : ∀ k, y k ≤ π k := by aesop
--     set X := x i with eqX
--     set Y := y i with eqY
--     set PI := π i with eqPI
--     rcases X with _ | X <;> rcases Y with _ | Y <;> rcases PI with _ | PI
--     · simp [(·≤·)]
--     · simp [(·≤·)]
--     · specialize hπ₂' i
--       rw [←eqPI, ←eqY] at hπ₂'
--       simp [(·≤·)] at hπ₂'
--     · aesop
--     · specialize hπ₂' i
--       rw [←eqPI] at hπ₂'
--       specialize hπ₁' i
--       rw [←eqPI] at hπ₁'
--       simp
--       rw [eqX]
--       assumption
--     · specialize hπ₂' i
--       specialize hπ₁' i
--       aesop
--     · specialize hπ₂' i
--       specialize hπ₁' i
--       aesop
--     · specialize hπ₂' i
--       specialize hπ₁' i
--       aesop

def iso {X : Type} [Preorder X] (a b : X) := a ≤ b ∧ b ≤ a

notation (priority := high) a " ≅ " b => iso a b

section iso

variable {X : Type} [Preorder X]
         {a b c : X}

@[simp, refl]
lemma iso_rfl : a ≅ a := by unfold iso; aesop

lemma iso_symm : (a ≅ b) ↔ b ≅ a := by unfold iso; aesop

lemma iso_trans : (a ≅ b) → (b ≅ c) → a ≅ c := by unfold iso; aesop (add unsafe forward le_trans)

end iso

def IsEquivRel {X : Type} [Preorder X] := ∀ a b : X, a ≤ b ↔ a ≅ b

class Setoid' (X : Type) extends Preorder X where
  isEquiv : IsEquivRel (X := X)

@[simp]
lemma le_eq_iso [φ : Setoid' X] {a b : X} : a ≤ b ↔ a ≅ b := by
  rcases φ with ⟨equiv⟩; unfold IsEquivRel at equiv
  aesop

@[simp]
lemma none_le {α : Type} [Preorder α] {x : α} : Option.none ≤ .some x := by simp [(·≤·)]

@[simp]
lemma some_le_none_eq_False {α : Type} [Preorder α] {x : α} : Option.some x ≤ none ↔ False := by
  simp [(·≤·)]

@[simp]
lemma some_le_some {α : Type} [Preorder α] {x y : α} :
  Option.some x ≤ .some y ↔ x ≤ y := by simp [(·≤·)]

@[simp]
lemma some_iso_some {α : Type} [Preorder α] {x y : α} :
  (Option.some x ≅ .some y) ↔ x ≅ y := by
  simp [iso]

@[simp]
lemma none_iso_some {α : Type} [Preorder α] {x : α} : (.none ≅ some x) ↔ False := by
  simp [iso]

lemma proposition1 {X : Type} [Preorder X] {x y : X} {s : Set X}
  (h₁ : IsLUB s x) (h₂ : IsLUB s y) : x ≅ y := by
  simp [IsLUB, IsLeast, lowerBounds, upperBounds] at h₁ h₂
  unfold iso
  aesop

lemma proposition2 {X : Type} [Setoid' X] {x y : X} :
  (∃ join : X, (IsLUB {x, y} join)) ↔ x ≅ y := by
  refine' Iff.intro (λ h ↦ _) (λ h ↦ _)
  · rcases h with ⟨join, ⟨h₁, -⟩⟩
    simp [mem_upperBounds] at h₁
    exact iso_trans h₁.1 h₁.2.symm
  · simp [IsLUB, IsLeast, lowerBounds, upperBounds]
    by_contra contra; simp at contra
    have : ∃ x', (x ≅ x') ∧ (y ≅ x') ∧ ¬y ≅ x' := contra _ h iso_rfl
    rcases this; aesop

lemma proposition2' {X : Type} [Setoid' X] {join x y : X} (h : IsLUB {x, y} join) :
  (x ≅ join) ∧ y ≅ join := by
  simp [IsLUB, IsLeast, upperBounds, lowerBounds] at h
  aesop

lemma proposition3 {X : Type} [Preorder X] {x join : Option X} (h : IsLUB {x, .none} join) :
  join ≅ x := by
  simp [IsLUB, IsLeast, upperBounds, lowerBounds] at h
  rcases h with ⟨⟨h₁, h₂⟩, h₃⟩
  unfold LE.le Preorder.toLE maybeInduced at h₁; simp at h₁
  rcases x with _ | x <;> rcases join with _ | join
  · simp
  · specialize @h₃ .none
    simp [(·≤·)] at h₃
  · simp at h₁
  · specialize @h₃ x (by simp) (by simp [(·≤·)])
    simp at h₁
    have : some x ≤ some join := by aesop
    simp [iso]; tauto

lemma proposition4 {X : Type} [Setoid' X] {x y : Option X} :
  (∃ join : Option X, IsLUB {x, y} join) ↔ (x ≠ .none ∧ y ≠ .none → x ≅ y) := by
  refine' Iff.intro (λ h ↦ _) (λ h ↦ _)
  · simp [IsLUB, IsLeast, lowerBounds, upperBounds] at h
    rcases h with ⟨join, ⟨⟨h₁, h₂⟩, h₃⟩⟩
    intros h₄
    rcases x with _ | x <;> rcases y with _ | y <;> rcases join with _ | join
    · simp
    · simp
    · simp at h₄
    · simp at h₄
    · simp at h₁
    · simp at h₄
    · simp at h₁
    · simp at h₁ h₂
      have : x ≅ y := iso_trans h₁ h₂.symm
      aesop
  · simp [IsLUB, IsLeast, lowerBounds, upperBounds]
    rcases x with _ | x <;> rcases y with _ | y
    · use none; simp
    · use .some y; simp
    · use .some x; simp
      intros y h₁; exact λ _ ↦ h₁
    · simp at h
      by_contra contra
      simp at contra
      have eq₁ : ∃ x', some x ≤ x' ∧ some y ≤ x' ∧ ¬x ≤ x' := contra x (by simp) h.2
      have eq₂ : ∃ x', some x ≤ x' ∧ some y ≤ x' ∧ ¬y ≤ x' := contra y h.1 (by simp)
      tauto

lemma proposition4W' {X : Type} [Setoid' X] {x y : Option X} :
  (∃ join : Option X, IsLUB {x, y} join) ↔ (x ≠ .none ∧ y ≠ .none → x ≅ y) := by
  refine' Iff.intro (λ h ↦ _) (λ h ↦ _)
  · simp [IsLUB, IsLeast, lowerBounds, upperBounds] at h
    rcases h with ⟨join, ⟨⟨h₁, h₂⟩, h₃⟩⟩
    intros h₄
    rcases x with _ | x <;> rcases y with _ | y <;> rcases join with _ | join
    · simp
    · simp
    · simp at h₄
    · simp at h₄
    · simp at h₁
    · simp at h₄
    · simp at h₁
    · simp at h₁ h₂
      have : x ≅ y := iso_trans h₁ h₂.symm
      aesop
  · simp [IsLUB, IsLeast, lowerBounds, upperBounds]
    rcases x with _ | x <;> rcases y with _ | y
    · use none; simp
    · use .some y; simp
    · use .some x; simp
      intros y h₁; exact λ _ ↦ h₁
    · simp at h
      by_contra contra
      simp at contra
      have eq₁ : ∃ x', some x ≤ x' ∧ some y ≤ x' ∧ ¬x ≤ x' := contra x (by simp) h.2
      have eq₂ : ∃ x', some x ≤ x' ∧ some y ≤ x' ∧ ¬y ≤ x' := contra y h.1 (by simp)
      tauto

lemma proposition4' {X : Type} [Setoid' X] {join x y : Option X} (h : IsLUB {x, y} join) :
  join ≅ Dict.First x y := by
  have eq : ∃ join, IsLUB {x, y} join := (by aesop); rw [proposition4] at eq
  rcases x with _ | x <;> rcases y with _ | y <;> rcases join with _ | join
  · simp
  · simp
    simp [IsLUB, IsLeast, lowerBounds, upperBounds] at h
    specialize @h .none
    simp at h
  · simp [IsLUB, IsLeast, lowerBounds, upperBounds] at h
  · simp [IsLUB, IsLeast, lowerBounds, upperBounds] at h
    simp
    rcases h with ⟨h, -⟩
    rw [iso_symm] at h
    aesop
  · simp [IsLUB, IsLeast, lowerBounds, upperBounds] at h
  · simp [IsLUB, IsLeast, lowerBounds, upperBounds] at h
    simp
    rcases h with ⟨h, -⟩
    rw [iso_symm] at h
    aesop
  · simp [IsLUB, IsLeast, lowerBounds, upperBounds] at h
  · simp at eq ⊢
    simp [IsLUB, IsLeast, lowerBounds, upperBounds] at h
    rw [iso_symm] at h
    aesop

lemma proposition4'WW {X : Type} [Setoid' X] {join x y : Option X} (h : IsLUB {x, y} join) :
  join ≅ Dict.First x y := by
  have eq : ∃ join, IsLUB {x, y} join := (by aesop); rw [proposition4] at eq
  rcases x with _ | x <;> rcases y with _ | y <;> rcases join with _ | join
  · simp
  · simp
    simp [IsLUB, IsLeast, lowerBounds, upperBounds] at h
    specialize @h .none
    simp at h
  · simp [IsLUB, IsLeast, lowerBounds, upperBounds] at h
  · simp [IsLUB, IsLeast, lowerBounds, upperBounds] at h
    simp
    rcases h with ⟨h, -⟩
    rw [iso_symm] at h
    aesop
  · simp [IsLUB, IsLeast, lowerBounds, upperBounds] at h
  · simp [IsLUB, IsLeast, lowerBounds, upperBounds] at h
    simp
    rcases h with ⟨h, -⟩
    rw [iso_symm] at h
    aesop
  · simp [IsLUB, IsLeast, lowerBounds, upperBounds] at h
  · simp at eq ⊢
    simp [IsLUB, IsLeast, lowerBounds, upperBounds] at h
    rw [iso_symm] at h
    aesop

lemma proposition5 {X Y : Type} [Preorder Y] {f g : X → Y} {join : X → Y} :
  IsLUB {f, g} join ↔ ∀ x : X, IsLUB {f x, g x} (join x) := by
  simp_rw [isLUB_pi]; simp [Function.eval, Set.image]
  have : ∀ x, {x_1 | f x = x_1 ∨ g x = x_1} = {f x, g x} := by aesop
  simp_rw [this]

lemma proposition5' {X Y : Type} [Preorder Y] {f g : X → Y} {h : X → Y} {join : Y} {join' : X → Y}
  (hjoin : IsLUB {f, g} join')
  (h₀ : ∀ x, IsLUB {f x, g x} join)
  (h₁ : ∀ x, h x ≅ join' x) :
  join' ≅ h := by
    rw [←proposition5] at h₀
    simp [(·≅·)] at h₁ ⊢
    simp [IsLUB, IsLeast, Set.Ici, lowerBounds, upperBounds] at hjoin h₀
    aesop (config := {warnOnNonterminal := false})
    simp [(·≤·)]
    aesop
    simp [(·≤·)]
    aesop

lemma proposition6W {X Y : Type} [Setoid' Y] {D₁ D₂ join : Dict X Y} (h : IsLUB {D₁, D₂} join) :
  join ≅ Dict.Merge D₁ D₂ := by
  simp [isLUB_pi, Set.image] at h
  have : ∀ a, {x | D₁ a = x ∨ D₂ a = x} = {D₁ a, D₂ a} := by aesop
  simp_rw [this] at h
  unfold Dict.Merge Dict.Merge.D
  have : join ≅ λ x ↦ join x := iso_rfl
  apply iso_trans this
  simp [iso]
  split_ands
  · simp [(·≤·)]
    intros x
    set J := join x with eqX
    set D := D₁ x with eqD₁
    set D' := D₂ x with eqD₂
    rcases J with _ | J <;> rcases D with _ | D <;> rcases D' with _ | D'
    · simp
    · simp
    · simp
    · simp
    · simp
      specialize h x
      simp_rw [←eqD₁, ←eqD₂] at h
      apply proposition4' at h
      simp at h
      simp [iso] at h
      simp [(·≤·)] at h
      rw [←eqX] at h
      simp at h
    · simp
      specialize h x
      simp_rw [←eqD₁, ←eqD₂] at h
      apply proposition4' at h
      simp at h
      rw [←eqX] at h
      simp at h
      exact h
    · simp
      rw [←some_iso_some]
      specialize h x
      simp_rw [←eqD₁, ←eqD₂] at h
      apply proposition4' at h
      simp at h
      aesop
    · simp
      specialize h x
      simp_rw [←eqD₁, ←eqD₂] at h
      apply proposition4' at h
      simp at h
      rw [←some_iso_some]
      aesop
  · simp [(·≤·)]
    intros x
    set J := join x with eqX
    set D := D₁ x with eqD₁
    set D' := D₂ x with eqD₂
    rcases J with _ | J <;> rcases D with _ | D <;> rcases D' with _ | D'
    · simp
    · specialize h x
      simp_rw [←eqD₁, ←eqD₂] at h
      apply proposition4' at h
      simp at h
      rw [←eqX] at h
      simp at h
    · specialize h x
      simp_rw [←eqD₁, ←eqD₂] at h
      apply proposition4' at h
      simp at h
      rw [←eqX] at h
      simp at h
    · specialize h x
      simp_rw [←eqD₁, ←eqD₂] at h
      apply proposition4' at h
      simp at h
      rw [←eqX] at h
      simp at h
    · simp
    · simp
      specialize h x
      simp_rw [←eqD₁, ←eqD₂] at h
      apply proposition4' at h
      simp at h
      rw [←some_iso_some]
      rw [←eqX] at h
      rw [iso_symm]
      exact h
    · simp
      specialize h x
      simp_rw [←eqD₁, ←eqD₂] at h
      apply proposition4' at h
      simp at h
      rw [←eqX] at h
      rw [iso_symm]
      exact h
    · simp
      specialize h x
      simp_rw [←eqD₁, ←eqD₂] at h
      apply proposition4' at h
      simp at h
      rw [←some_iso_some]
      rw [iso_symm]
      aesop

instance : Setoid' ((Pi × ExtraDataT) × TransactionBatch K₁ K₂ V) where
  isEquiv := by unfold IsEquivRel
                intros a b
                unfold iso
                simp [(·≤·)]
                aesop

lemma proposition6' {x y : BalanceProof K₁ K₂ C Pi V}
  (h : ∀ k, k ∈ x ∧ k ∈ y → x k ≅ y k) : IsLUB {x, y} (Dict.Merge x y) := by
  unfold Dict.Merge Dict.Merge.D Dict.First
  simp [IsLUB, IsLeast, lowerBounds]
  split_ands
  · intros i; simp
    aesop
  · intros i; simp
    set X := x i with eqX
    set Y := y i with eqY
    rcases X with _ | X <;> rcases Y with _ | Y
    · simp [(·≤·)]
    · simp [(·≤·)]
    · simp [(·≤·)]
    · have eq₁ : (x i).isSome := by rw [←eqX]; simp
      have eq₂ : (y i).isSome := by rw [←eqY]; simp
      simp [←Dict.mem_iff_isSome, -Prod.forall] at h
      have eq₃ : i ∈ x := Dict.mem_iff_isSome.2 eq₁
      have eq₄ : i ∈ y := Dict.mem_iff_isSome.2 eq₂
      have : x i ≤ y i ∧ y i ≤ x i := h _ eq₃ eq₄
      rw [eqX, eqY]
      rw [Dict.mem_iff_isSome] at eq₃
      rw [Dict.mem_iff_isSome] at eq₄
      apply w₄ <;> aesop
  · intros π hπ₁ hπ₂ i; simp
    have hπ₁' : ∀ k, x k ≤ π k := by aesop
    have hπ₂' : ∀ k, y k ≤ π k := by aesop
    set X := x i with eqX
    set Y := y i with eqY
    set PI := π i with eqPI
    rcases X with _ | X <;> rcases Y with _ | Y <;> rcases PI with _ | PI
    · simp [(·≤·)]
    · simp [(·≤·)]
    · specialize hπ₂' i
      rw [←eqPI, ←eqY] at hπ₂'
      simp [(·≤·)] at hπ₂'
    · aesop
    · specialize hπ₂' i
      rw [←eqPI] at hπ₂'
      specialize hπ₁' i
      rw [←eqPI] at hπ₁'
      simp
      rw [←eqX] at hπ₁'
      assumption
    · specialize hπ₂' i
      specialize hπ₁' i
      aesop
    · specialize hπ₂' i
      specialize hπ₁' i
      aesop
    · specialize hπ₂' i
      specialize hπ₁' i
      aesop

lemma proposition6'any {X Y : Type} [Setoid' Y] {D₁ D₂ : Dict X Y}
  (h : ∀ k, D₁ k ≠ .none ∧ D₂ k ≠ .none → D₁ k ≅ D₂ k) : IsLUB {D₁, D₂} (Dict.Merge D₁ D₂) := by
  unfold Dict.Merge Dict.Merge.D Dict.First
  simp [IsLUB, IsLeast, lowerBounds]
  split_ands
  · intros i; simp
    aesop
  · intros i; simp
    set X := D₁ i with eqX
    set Y := D₂ i with eqY
    rcases X with _ | X <;> rcases Y with _ | Y
    · simp [(·≤·)]
    · simp [(·≤·)]
    · simp [(·≤·)]
    · have eq₁ : (D₁ i).isSome := by rw [←eqX]; simp
      have eq₂ : (D₂ i).isSome := by rw [←eqY]; simp
      simp [←Dict.mem_iff_isSome, -Prod.forall] at h
      have : D₁ i ≤ D₂ i ∧ D₂ i ≤ D₁ i := h _ (by aesop) (by aesop)
      rw [eqX, eqY]
      aesop
  · intros π hπ₁ hπ₂ i; simp
    have hπ₁' : ∀ k, D₁ k ≤ π k := by aesop
    have hπ₂' : ∀ k, D₂ k ≤ π k := by aesop
    set X := D₁ i with eqX
    set Y := D₂ i with eqY
    set PI := π i with eqPI
    rcases X with _ | X <;> rcases Y with _ | Y <;> rcases PI with _ | PI
    · simp [(·≤·)]
    · simp [(·≤·)]
    · specialize hπ₂' i
      rw [←eqPI, ←eqY] at hπ₂'
      simp [(·≤·)] at hπ₂'
    · aesop
    · specialize hπ₂' i
      rw [←eqPI] at hπ₂'
      specialize hπ₁' i
      rw [←eqPI] at hπ₁'
      simp
      rw [←eqX] at hπ₁'
      assumption
    · specialize hπ₂' i
      specialize hπ₁' i
      aesop
    · specialize hπ₂' i
      specialize hπ₁' i
      aesop
    · specialize hπ₂' i
      specialize hπ₁' i
      aesop

lemma proposition6?! {X Y : Type} [Setoid' Y] {D₁ D₂ : Dict X Y} :
  (∃ join, IsLUB {D₁, D₂} join) ↔ ∀ x, D₁ x ≠ .none ∧ D₂ x ≠ .none → D₁ x ≅ D₂ x := by
  refine' ⟨λ h ↦ _, λ h ↦ _⟩
  simp_rw [proposition5] at h
  simp_rw [←proposition4]
  aesop
  use D₁.Merge D₂
  exact proposition6'any h
  


  
  
  
  
  -- refine' ⟨λ h x ↦ _, λ h x ↦ _⟩
  



-- lemma proposition6XK {x y : BalanceProof K₁ K₂ C Pi V}
--   (h : ∀ k, k ∈ x ∧ k ∈ y → x k ≅ y k) : IsLUB {x, y} (Dict.Merge x y) := by
--   unfold Dict.Merge Dict.Merge.D Dict.First
--   simp [IsLUB, IsLeast, lowerBounds]
--   split_ands
--   · intros i; simp
--     aesop
--   · intros i; simp
--     set X := x i with eqX
--     set Y := y i with eqY
--     rcases X with _ | X <;> rcases Y with _ | Y
--     · simp [(·≤·)]
--     · simp [(·≤·)]
--     · simp [(·≤·)]
--     · have eq₁ : (x i).isSome := by rw [←eqX]; simp
--       have eq₂ : (y i).isSome := by rw [←eqY]; simp
--       simp [←Dict.mem_iff_isSome, -Prod.forall] at h
--       have eq₃ : i ∈ x := Dict.mem_iff_isSome.2 eq₁
--       have eq₄ : i ∈ y := Dict.mem_iff_isSome.2 eq₂
--       have : x ≤ y ∧ y ≤ x := h _ eq₃ eq₄
--       rw [eqX, eqY]
--       rw [Dict.mem_iff_isSome] at eq₃
--       rw [Dict.mem_iff_isSome] at eq₄
--       apply w₄ <;> aesop
--   · intros π hπ₁ hπ₂ i; simp
--     have hπ₁' : ∀ k, x k ≤ π k := by aesop
--     have hπ₂' : ∀ k, y k ≤ π k := by aesop
--     set X := x i with eqX
--     set Y := y i with eqY
--     set PI := π i with eqPI
--     rcases X with _ | X <;> rcases Y with _ | Y <;> rcases PI with _ | PI
--     · simp [(·≤·)]
--     · simp [(·≤·)]
--     · specialize hπ₂' i
--       rw [←eqPI, ←eqY] at hπ₂'
--       simp [(·≤·)] at hπ₂'
--     · aesop
--     · specialize hπ₂' i
--       rw [←eqPI] at hπ₂'
--       specialize hπ₁' i
--       rw [←eqPI] at hπ₁'
--       simp
--       rw [←eqX] at hπ₁'
--       assumption
--     · specialize hπ₂' i
--       specialize hπ₁' i
--       aesop
--     · specialize hπ₂' i
--       specialize hπ₁' i
--       aesop
--     · specialize hπ₂' i
--       specialize hπ₁' i
--       aesop

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

lemma proposition6W_l {X Y : Type} [Setoid' Y] {D₁ D₂ join : Dict X Y}
  (h : join ≅ Dict.Merge D₁ D₂) (h₀ : ∀ k, D₁ k ≠ .none ∧ D₂ k ≠ .none → D₁ k ≅  D₂ k) : IsLUB {D₁, D₂} join := by
  simp [isLUB_pi, Set.image]
  intros a
  have : {x | D₁ a = x ∨ D₂ a = x} = {D₁ a, D₂ a} := by aesop
  simp_rw [this]; clear this
  set A := D₁ a with eqA
  set B := D₂ a with eqB
  set C := join a with eqC
  unfold iso at h
  simp [(·≤·)] at h
  rcases h with ⟨h₁, h₂⟩
  simp [Dict.Merge] at h₁ h₂
  unfold Dict.Merge.D at h₁ h₂
  specialize h₁ a
  specialize h₂ a
  rcases A with _ | A <;> rcases B with _ | B <;> rcases C with _ | C
  · simp
  · rw [←eqC, ←eqA, ←eqB] at h₁ h₂
    simp at h₁ h₂
  · rw [←eqC, ←eqA, ←eqB] at h₁ h₂
    simp at h₁ h₂
  · rw [←eqC, ←eqA, ←eqB] at h₁ h₂
    simp at h₁ h₂
    simp [IsLUB, IsLeast, lowerBounds, upperBounds]
    refine' ⟨by assumption, _⟩
    intros X y z
    rcases X with _ | X
    simp at z
    apply le_trans h₁.1
    simp at z
    exact z.1
  · rw [←eqC, ←eqA, ←eqB] at h₁ h₂
    simp at h₁ h₂
  · rw [←eqC, ←eqA, ←eqB] at h₁ h₂
    simp at h₁ h₂
    simp [IsLUB, IsLeast, lowerBounds, upperBounds]
    refine' ⟨by assumption, _⟩
    intros X y z
    rcases X with _ | X
    simp at y
    apply le_trans h₁.1
    simp at y
    exact y.1
  · rw [←eqC, ←eqA, ←eqB] at h₁ h₂
    simp at h₁ h₂
  · rw [←eqC, ←eqA, ←eqB] at h₁ h₂
    specialize h₀ a
    simp at h₁ h₂ h₀
    have : D₁ a ≅ D₂ a := by aesop
    rw [←eqA, ←eqB] at this
    simp [IsLUB, IsLeast, lowerBounds, upperBounds]
    split_ands
    · exact h₂.1
    · exact h₂.2
    · simp at this
      have eq : B ≅ C := iso_trans (iso_symm.1 this) h₂
      exact eq.1
    · intros
      have eq : B ≅ C := iso_trans (iso_symm.1 this) h₂
      exact eq.2
    · intros H h₃ h₄
      simp at this
      have eq : B ≅ C := iso_trans (iso_symm.1 this) h₂
      rw [iso_symm] at eq
      rcases H with _ | H
      · simp at h₃
      · simp at h₃ h₄ ⊢
        apply iso_trans eq h₄


  -- done


  -- simp [IsLUB, IsLeast, lowerBounds]
  -- split_ands
  -- · intros i; simp
  --   aesop
  -- · intros i; simp
  --   set X := D₁ i with eqX
  --   set Y := D₂ i with eqY
  --   rcases X with _ | X <;> rcases Y with _ | Y
  --   · simp
  --   · simp
  --   · simp
  --   · simp
  --     specialize h i
  --     rw [←eqX, ←eqY] at h
  --     simp at h
  --     rw [iso_symm]
  --     exact h
  -- · intros π hπ₁ hπ₂ i; simp
  --   specialize h i
  --   set X := D₁ i with eqX
  --   set Y := D₂ i with eqY
  --   set PI := π i with eqPI
  --   rcases X with _ | X <;> rcases Y with _ | Y <;> rcases PI with _ | PI
  --   · simp
  --   · simp
  --   · simp

    -- set PI := π i with eqPI
    -- rcases X with _ | X <;> rcases Y with _ | Y <;> rcases PI with _ | PI
    -- · simp [(·≤·)]
    -- · simp [(·≤·)]
    -- · specialize hπ₂' i
    --   rw [←eqPI, ←eqY] at hπ₂'
    --   simp [(·≤·)] at hπ₂'
    -- · aesop
    -- · specialize hπ₂' i
    --   rw [←eqPI] at hπ₂'
    --   specialize hπ₁' i
    --   rw [←eqPI] at hπ₁'
    --   simp
    --   rw [←eqX] at hπ₁'
    --   assumption
    -- · specialize hπ₂' i
    --   specialize hπ₁' i
    --   aesop
    -- · specialize hπ₂' i
    --   specialize hπ₁' i
    --   aesop
    -- · specialize hπ₂' i
    --   specialize hπ₁' i
    --   aesop


-- lemma xx {X Y : Type} {s : Set (Dict X Y)} [Setoid' Y] {D₁ D₂ : Dict X Y}
--   (h : IsLUB s D₂) : IsLUB (s.insert D₁) (Dict.Merge D₁ D₂) := by

  -- simp [IsLUB, IsLeast, upperBounds, lowerBounds] at *

-- #exit

-- lemma prop6W {X Y : Type} [Setoid' Y] {D₁ D₂ : Dict X Y} :
--   (∃ join, IsLUB {D₁, D₂} join) ↔ (∀ x, D₁ x ≠ .none ∧ D₂ x ≠ .none → D₁ x ≅ D₂ x) := by
--   have : ∀ a, {x | D₁ a = x ∨ D₂ a = x} = {D₁ a, D₂ a} := by aesop
--   simp_rw [←proposition4]
--   refine' ⟨λ h ↦ _, λ h ↦ _⟩
--   simp [isLUB_pi, Set.image] at h
--   simp_rw [this] at h
--   tauto
--   simp [isLUB_pi, Set.image]
--   simp_rw [this]
--   intros a
--   intros x
--   specialize h x
--   rcases h with ⟨h₁, h₂⟩




--   by_contra contra
--   simp at contra
--   specialize contra D₁
--   rcases contra with ⟨x, h₁⟩
--   specialize h x
--   rcases h with ⟨x', h₁'⟩


--   rcases h with ⟨join, hjoin⟩

-- lemma prop6 {X Y : Type} [Setoid' Y] {D₁ D₂ : Dict X Y} {join} :
--   (IsLUB {D₁, D₂} join) ↔ (D₁ x ≠ .none ∧ D₂ x ≠ .none → D₁ x ≅ D₂ x) := by
--   have : ∀ a, {x | D₁ a = x ∨ D₂ a = x} = {D₁ a, D₂ a} := by aesop
--   simp_rw [←proposition4]
--   simp [isLUB_pi, Set.image]
--   simp_rw [this]
--   refine' ⟨λ h ↦ _, λ h ↦ _⟩
--   tauto

--   intros a
--   rcases h with ⟨join, hjoin⟩






--   -- have : ∀ a, {x | D₁ a = x ∨ D₂ a = x} = {D₁ a, D₂ a} := by aesop
--   -- refine' ⟨λ h ↦ _, λ h ↦ _⟩
--   -- · rcases h with ⟨join, h⟩
--   --   simp [isLUB_pi, Set.image] at h
--   --   simp_rw [this] at h
--   --   rw [←proposition4]; aesop
--   -- · simp [isLUB_pi, Set.image]; simp_rw [this]; clear this
--   --   simp_rw [←proposition4] at h
--   --   rcases h with ⟨join, hjoin⟩








-- -- lemma proposition5 {X Y : Type} [Preorder Y] {f g join : X → Y} :
-- --   IsLUB {f, g} join ↔ ∀ x : X, IsLUB {f x, g x} (join x) := by
-- --   rw [isLUB_pi]
-- --   simp [Function.eval, Set.image]


-- --   refine' ⟨λ h ↦ _, λ h ↦ _⟩
-- --   · rcases h with ⟨join, hjoin⟩
-- --     rw [isLUB_pi] at hjoin
-- --     simp [Function.eval, Set.image] at hjoin
-- --     simp at hjoin


--   -- simp [IsLUB, IsLeast, lowerBounds, upperBounds]
--   -- simp [(·≤·)]


--   -- refine' ⟨λ h ↦ _, λ h ↦ _⟩

--   -- sorry
--   -- . rcases h with ⟨join, h₁⟩
--   --   simp [IsLUB, IsLeast, lowerBounds, upperBounds] at h₁

--   --   by_contra contra
--   --   simp at contra
--   --   simp [IsLUB, IsLeast, lowerBounds, upperBounds] at contra
--   --   simp [(·≤·)] at contra






-- lemma proposition5 {X Y : Type} [Preorder Y] (f g : X → Y) :
--   (∃ join : X → Y, IsLUB {f, g} join) ↔ (∀ x : X, ∃ join' : Y, IsLUB {f x, g x} join') := by
--   refine' ⟨λ h ↦ _, λ h ↦ _⟩
--   · rcases h with ⟨join, hjoin⟩
--     simp [IsLUB, IsLeast, lowerBounds, upperBounds] at hjoin ⊢
--     rcases hjoin with ⟨⟨h₁, h₂⟩, h₃⟩
--     intros x
--     simp [(·≤·)] at h₁ h₂
--     by_contra contra
--     simp at contra
--     have : ∃ x_2, f x ≤ x_2 ∧ g x ≤ x_2 ∧ ¬(join x) ≤ x_2 := contra _ (h₁ _) (h₂ _)
--     rcases this with ⟨y₁, ⟨h₅, ⟨h₆, h₇⟩⟩⟩
--     specialize @h₃ (λ _ ↦ y₁)
--     simp [(·≤·)] at h₃
--     have : join x ≤ y₁ := by
--       apply h₃

--     -- simp [h₁, h₂]
--     -- intros y h₄ h₅
--     -- simp [(·≤·)] at h₃
--     -- apply h₃
--     -- intros x₁
--     -- have : join x₁ ≤ y := by
--     --   apply h₃
--     --   intros x₂

--     --   done
--     -- -- have : join
--     -- -- specialize h₁ x₁
--     -- -- specialize h₂ x₁
--     -- apply le_trans (h₁ x₁)
--     -- apply h₃
--     -- intros x₂





--   ·

-- -- lemma proposition5 {X Y : Type} [Nonempty X] [Preorder Y] (f g : X → Y) :
-- --   (∃ join : X → Y, IsLUB {f, g} join) ↔ (∃ join' : Y, ∀ x : X, IsLUB {f x, g x} join') := by
-- --   refine' ⟨λ h ↦ _, λ h ↦ _⟩
-- --   · rcases h with ⟨join, hjoin⟩
-- --     simp [IsLUB, IsLeast, lowerBounds, upperBounds] at hjoin ⊢
-- --     by_contra contra
-- --     simp at contra
-- --     specialize contra (join (Classical.arbitrary _))
-- --     rcases contra with ⟨contra, h₁⟩
-- --     simp [(·≤·)] at hjoin
-- --     rcases hjoin with ⟨⟨h₂, h₃⟩, h₄⟩
-- --     specialize h₁ (h₂ _)


--   ·




--     -- rcases hjoin with ⟨⟨h₁, h₂⟩, h₃⟩
--     -- by_contra contra
--     -- simp at contra
--     -- simp [IsLUB, IsLeast, lowerBounds, upperBounds] at contra
--     -- simp [(·≤·)] at h₁ h₂ h₃ contra



--     -- specialize @contra (join x) (h₁ _) (h₂ _)
--     -- rcases contra with ⟨x', hx₁⟩
--     -- simp [(·≤·)] at h₃


--     -- use join x
--     -- simp [IsLUB, IsLeast, lowerBounds, upperBounds]
--     -- simp [(·≤·)] at hjoin
--     -- rcases hjoin with ⟨⟨h₁, h₂⟩, h₃⟩
--     -- refine' ⟨⟨h₁ _, h₂ _⟩, λ y h₅ h₆ ↦ _⟩
--     -- specialize @h₃ join h₁ h₂







-- -- lemma merge_iso {s} {x₁ x₂ : Option ((Pi × ExtraDataT) × TransactionBatch K₁ K₂ V)}
-- --   (h : IsLUB s (Dict.First x₁ x₂)) : x₁ ≤ x₂ ∧ x₂ ≤ x₁ := by
-- --   simp [IsLUB, IsLeast, upperBounds, lowerBounds] at h
-- --   rcases x₁ with _ | x₁ <;> rcases x₂ with _ | x₂
-- --   · simp
-- --   · simp [Dict.First] at h
-- --     refine' ⟨by simp [(·≤·)], _⟩
-- --     simp at h



--   done


-- -- lemma eq {π : BalanceProof K₁ K₂ C Pi V} {s : Set (BalanceProof K₁ K₂ C Pi V)}
-- --   (h : IsLUB s π) : ∀ k, k ∈ { Dict.keys π' | π' ∈ s }.sUnion → k ∈ π := by
-- --   intros k h'
-- --   simp at h'
-- --   rcases h' with ⟨h', ⟨h₁, h₂⟩⟩
-- --   obtain ⟨h₃, h₄⟩ := h
-- --   simp [upperBounds, lowerBounds] at h₃ h₄
-- --   rw [Dict.mem_iff_isSome]




-- --   done



end Ordering

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

-- lemma mergeR_cons_succ {π} {πs : List (BalanceProof K₁ K₂ C Pi V)} {n : ℕ} (h) :
--   mergeR (π :: πs) (n + 1) = (mergeR πs n).Merge (πs[n]) := by
--   conv_lhs => unfold mergeR
--   simp; rw [dif_pos (by omega)]


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

-- lemma le_Merge_of_left {π π₁ π₂ : BalanceProof K₁ K₂ C Pi V} (h : π k ≤ π₁ k) :
--   π k ≤ Dict.Merge π₁ π₂ k := by
--   unfold Dict.Merge Dict.Merge.D Dict.First
--   simp [(·≤·)] at h
--   aesop (config := {warnOnNonterminal := false})

-- lemma le_mergeR''_self
--         {π acc : BalanceProof K₁ K₂ C Pi V}
--         {πs : List (BalanceProof K₁ K₂ C Pi V)}
--         {k : C × K₂}
--         (h : acc k ≤ π k) :
--         π k ≤ mergeR'' (π :: πs) acc k := by
--   simp
--   rcases πs with _ | ⟨π', πs'⟩
--   · simp [mergeR'']
--     by_cases eq : acc k = .none
--     · unfold Dict.Merge Dict.Merge.D Dict.First
--       aesop
--     · by_cases eq' : π k = .none
--       · unfold Dict.Merge Dict.Merge.D Dict.First
--         simp [(·≤·)]; aesop
--       · apply w₄ _ eq eq' h
--   · simp [mergeR'']
--     rw [←Dict.Merge_assoc]
--     apply le_Merge_of_left
--     by_cases eq : acc k = .none
--     · unfold Dict.Merge Dict.Merge.D Dict.First
--       aesop
--     · by_cases eq' : π k = .none
--       · unfold Dict.Merge Dict.Merge.D Dict.First
--         simp [(·≤·)]; aesop
--       · apply w₄ _ eq eq' h

-- -- lemma le_mergeR''_aux'R {acc : BalanceProof K₁ K₂ C Pi V}
-- --                         {πs : List (BalanceProof K₁ K₂ C Pi V)}
-- --                         (h : IsLUB πs.toFinset.toSet acc) :
-- --                         IsLUB πs.toFinset.toSet (Dict.Merge acc (mergeR'' πs acc)) := by
-- --   induction' πs with hd tl ih generalizing acc
-- --   · simp at h
-- --     simp [mergeR'']
-- --     -- have : IsLUB ∅ acc := by
-- --     --   rw [isLUB_empty_iff]
-- --     -- simp at this -- lemma IsBot .initial
-- --     -- simp [mergeR'']
-- --     -- exact this

-- --   · simp at h ih ⊢
-- --     have : IsLUB _ (Dict.Merge acc (mergeR'' tl hd)) := proposition6 sorry
-- --     specialize ih (acc := hd)

-- -- lemma oompf {n : ℕ} {πs : List (BalanceProof K₁ K₂ C Pi V)} (h : n < πs.length + 1) :
-- --   IsLUB (πs.take n).toFinset.toSet (mergeR πs n) := by
-- --   induction' n with n ih generalizing πs
-- --   · unfold mergeR; aesop
-- --   · simp at ih ⊢
-- --     unfold mergeR
-- --     simp [h]
-- --     set smol := Dict.Merge (mergeR πs n) πs[n] with eqsmol
-- --     have : IsLUB _ smol := proposition6 ?x
-- --     case x =>
-- --     skip
-- --     intros k hk
-- --     unfold mergeR
-- --     rw [dif_pos (by omega)]
-- --     rcases n with _ | n
-- --     · simp
-- --       unfold mergeR at hk
-- --       simp at hk
-- --       rcases hk with hk | hk
-- --     · simp
-- --       unfold mergeR at hk
-- --       simp at hk
-- --       -- rw [dif_pos (by omega)]
-- --       rw [dif_pos (by omega)] at hk
-- --       specialize ih (πs := πs) (by omega)
-- --       obtain ⟨h₁, h₂⟩ := ih
-- --       simp [upperBounds, lowerBounds] at h₁ h₂
-- --       specialize @h₁ πs[n + 1] sorry



-- --       specialize @h₂ _ πs[n + 1]
-- --       rw [List.getElem_mem] at h₁

-- --       -- apply funext
-- --       -- intros K
-- --       -- rw [Dict.keys_Merge_left]
-- --       -- unfold mergeR

-- --     done
-- --     specialize ih (πs := πs) (by omega)
-- --     obtain ⟨h₁, h₂⟩ := this
-- --     simp [upperBounds] at h₁
-- --     obtain ⟨h₃, h₄⟩ := ih
-- --     simp [upperBounds] at h₃
-- --     simp [IsLUB, IsLeast, upperBounds, lowerBounds]
-- --     split_ands
-- --     · intros a h'; rw [eqsmol] at h₁ ⊢
-- --       rw [List.take_succ] at h'; simp at h'
-- --       rcases h' with h' | h'
-- --       · rcases h₁ with ⟨h₁, h₁'⟩
-- --         specialize @h₃ a
-- --         refine' le_trans _ h₁
-- --         apply h₃ h'
-- --       · have : πs[n] = a := by rw [List.getElem?_eq_some] at h'
-- --                                rcases h' with ⟨w, hw⟩
-- --                                exact hw
-- --         rw [←this]
-- --         exact h₁.2
-- --     · simp [(·≤·)] at h₁
-- --       -- intros a h'; rw [eqsmol] at h₂ ⊢
-- --       -- specialize @h' smol
-- --       -- rw [List.take_succ] at h'; simp at h'
-- --       -- apply h'
-- --       -- simp [lowerBounds, upperBounds] at h₂ h₄
-- --       -- specialize @h₂ smol
-- --       -- apply h₂
-- --       -- apply h₄
-- --       -- intros π hπ


-- --       -- rcases h' with h' | h'
-- --       -- rw [eqsmol]
-- --       -- specialize @ha smol
-- --       -- apply ha




-- --     -- rcases πs with _ | ⟨hd, tl⟩
-- --     -- · simp at h
-- --     -- · simp at h ⊢

-- @[simp]
-- lemma Merge_initial_pi {π : BalanceProof K₁ K₂ C Pi V} :
--   BalanceProof.initial.Merge π = π := by
--   rw [Dict.keys_Merge_right']
--   intros x contra
--   unfold BalanceProof.initial at contra
--   rw [Dict.mem_iff_isSome] at contra
--   simp at contra

-- -- lemma hhy {π : BalanceProof K₁ K₂ C Pi V}
-- --   (h₀ : ∀ k, acc k ≠ .none → π k ≠ .none → acc k ≅ π k)
-- --   (h : π ∈ upperBounds s) : (Dict.Merge acc π) ∈ upperBounds (insert acc s) := by
-- --   simp only [upperBounds, Set.mem_setOf_eq, forall_exists_index, and_imp, (·≤·),
-- --              forall_apply_eq_imp_iff₂, lowerBounds] at *
-- --   intros y hy
-- --   simp at hy
-- --   rcases hy with hy | hy
-- --   · intros K
-- --     simp [Dict.Merge]; unfold Dict.Merge.D Dict.First
-- --     set A := acc K with eqA
-- --     set B := π K with eqB
-- --     rcases A with _ | A <;> rcases B with _ | B
-- --     · rw [←hy] at eqA
-- --       rw [←eqA]
-- --       simp
-- --     · rw [←hy] at eqA
-- --       rw [←eqA]
-- --       simp
-- --     · rw [←hy] at eqA
-- --       rw [←eqA]
-- --     · rw [←hy] at eqA
-- --       rw [←eqA]
-- --   · intros K
-- --     simp [Dict.Merge]; unfold Dict.Merge.D Dict.First
-- --     -- rcases hy with ⟨y', ⟨h₃, h₄⟩⟩
-- --     set A := acc K with eqA
-- --     set B := π K with eqB
-- --     set C := y K with eqC
-- --     rcases A with _ | A <;> rcases B with _ | B <;> rcases C with _ | C
-- --     · simp
-- --     · simp [-Prod.forall] at h
-- --       specialize @h y hy K
-- --       rw [←eqC, ←eqB] at h
-- --       simp at h
-- --     · simp
-- --     · simp
-- --       specialize @h y hy K
-- --       simp [eqB.symm, eqC.symm] at h
-- --       exact h
-- --     · simp
-- --     · specialize @h y hy K
-- --       simp [eqB.symm, eqC.symm] at h
-- --     · simp
-- --     · simp
-- --       specialize @h y hy K
-- --       simp [eqB.symm, eqC.symm] at h
-- --       specialize h₀ K
-- --       rw [←eqA, ←eqB] at h₀
-- --       simp at h₀
-- --       unfold iso at h₀

-- --       rw [←h₄]
-- --       simp
-- --       have : C ≅ B := by
-- --         specialize @h₁ y' h₃
-- --         rw [←eqC] at h₁
-- --         simp at h₁
-- --         exact h₁
-- --       have eq₁ : acc K ≅ π K := by apply h₀
-- --                                     rw [←eqA]; simp
-- --                                     rw [←eqB]; simp
-- --       rw [←eqA, ←eqB] at eq₁
-- --       simp at eq₁
-- --       exact iso_trans this eq₁.symm
-- --   -- simp only [upperBounds, Set.mem_setOf_eq, forall_exists_index, and_imp,
-- --   --   forall_apply_eq_imp_iff₂, lowerBounds] at *
-- --   -- rcases h with ⟨h₁, h₂⟩
-- --   -- split_ands
-- --   -- · intros y hy
-- --   --   rcases hy with hy | hy
-- --   --   · simp [Dict.Merge]; unfold Dict.Merge.D Dict.First
-- --   --     set A := acc K with eqA
-- --   --     set B := π K with eqB
-- --   --     rcases A with _ | A <;> rcases B with _ | B
-- --   --     · rw [←hy]
-- --   --     · rw [←hy]
-- --   --       simp
-- --   --     · rw [←hy]
-- --   --     · rw [←hy]
-- --   --   · simp [Dict.Merge]; unfold Dict.Merge.D Dict.First
-- --   --     rcases hy with ⟨y', ⟨h₃, h₄⟩⟩
-- --   --     set A := acc K with eqA
-- --   --     set B := π K with eqB
-- --   --     set C := y' K with eqC
-- --   --     rcases A with _ | A <;> rcases B with _ | B <;> rcases C with _ | C
-- --   --     · simp [h₄]
-- --   --     · simp
-- --   --       specialize h₁ _ h₃
-- --   --       rw [←eqC] at h₁
-- --   --       simp at h₁
-- --   --     · simp; rw [←h₄]; simp
-- --   --     · simp
-- --   --       specialize @h₁ y' h₃
-- --   --       aesop
-- --   --     · simp; rw [←h₄]; simp
-- --   --     · specialize @h₁ y' h₃
-- --   --       rw [←eqC] at h₁
-- --   --       simp at h₁
-- --   --     · simp; rw [←h₄]; simp
-- --   --     · simp
-- --   --       rw [←h₄]
-- --   --       simp
-- --   --       have : C ≅ B := by
-- --   --         specialize @h₁ y' h₃
-- --   --         rw [←eqC] at h₁
-- --   --         simp at h₁
-- --   --         exact h₁
-- --   --       have eq₁ : acc K ≅ π K := by apply h₀
-- --   --                                    rw [←eqA]; simp
-- --   --                                    rw [←eqB]; simp
-- --   --       rw [←eqA, ←eqB] at eq₁
-- --   --       simp at eq₁
-- --   --       exact iso_trans this eq₁.symm
-- --   -- · intros y hy
-- --   --   simp [Dict.Merge]; unfold Dict.Merge.D Dict.First
-- --   --   set A := acc K with eqA
-- --   --   set B := π K with eqB
-- --   --   rcases A with _ | A <;> rcases B with _ | B <;> rcases y with _ | y
-- --   --   · simp
-- --   --   · simp
-- --   --   · simp
-- --   --     by_cases eq' : π ∈ s
-- --   --     · specialize @hy (some B) (Or.inr _)
-- --   --       use π
-- --   --       tauto
-- --   --       simp at hy
-- --   --     ·

-- --   --     -- specialize h₂ h₁
-- --   --     -- specialize @hy (some B) (Or.inr _)

-- --   --     -- simp at hy
-- --   --   · rw [←hy]
-- --   --   · rw [←hy]

-- lemma hhy {π : BalanceProof K₁ K₂ C Pi V} {s : Set (BalanceProof K₁ K₂ C Pi V)}
--   (h₀ : ∀ k, acc k ≠ .none → π k ≠ .none → acc k ≅ π k)
--   -- (h₁ : )
--   (h : IsLUB s π) : IsLUB (insert acc s) (Dict.Merge acc π) := by
--   simp [-Prod.forall, isLUB_pi, Set.image] at h ⊢
--   intros K
--   specialize h K
--   simp only [IsLUB, IsLeast, upperBounds, Set.mem_setOf_eq, forall_exists_index, and_imp,
--     forall_apply_eq_imp_iff₂, lowerBounds] at *
--   rcases h with ⟨h₁, h₂⟩
--   split_ands
--   · intros y hy
--     rcases hy with hy | hy
--     · simp [Dict.Merge]; unfold Dict.Merge.D Dict.First
--       set A := acc K with eqA
--       set B := π K with eqB
--       rcases A with _ | A <;> rcases B with _ | B
--       · rw [←hy]
--       · rw [←hy]
--         simp
--       · rw [←hy]
--       · rw [←hy]
--     · simp [Dict.Merge]; unfold Dict.Merge.D Dict.First
--       rcases hy with ⟨y', ⟨h₃, h₄⟩⟩
--       set A := acc K with eqA
--       set B := π K with eqB
--       set C := y' K with eqC
--       rcases A with _ | A <;> rcases B with _ | B <;> rcases C with _ | C
--       · simp [h₄]
--       · simp
--         specialize h₁ _ h₃
--         rw [←eqC] at h₁
--         simp at h₁
--       · simp; rw [←h₄]; simp
--       · simp
--         specialize @h₁ y' h₃
--         aesop
--       · simp; rw [←h₄]; simp
--       · specialize @h₁ y' h₃
--         rw [←eqC] at h₁
--         simp at h₁
--       · simp; rw [←h₄]; simp
--       · simp
--         rw [←h₄]
--         simp
--         have : C ≅ B := by
--           specialize @h₁ y' h₃
--           rw [←eqC] at h₁
--           simp at h₁
--           exact h₁
--         have eq₁ : acc K ≅ π K := by apply h₀
--                                      rw [←eqA]; simp
--                                      rw [←eqB]; simp
--         rw [←eqA, ←eqB] at eq₁
--         simp at eq₁
--         exact iso_trans this eq₁.symm
--   · intros y hy
--     simp [Dict.Merge]; unfold Dict.Merge.D Dict.First
--     set A := acc K with eqA
--     set B := π K with eqB
--     rcases A with _ | A <;> rcases B with _ | B <;> rcases y with _ | y
--     · simp
--     · simp
--     · sorry
--     · simp
--       specialize @hy (acc K) (Or.inl eqA)

--     -- · simp
--     --   by_cases eq' : π ∈ s
--     --   · specialize @hy (some B) (Or.inr _)
--     --     use π
--     --     tauto
--     --     simp at hy
--     --   ·

--     --   -- specialize h₂ h₁
--     --   -- specialize @hy (some B) (Or.inr _)

--     --   -- simp at hy
--     -- · rw [←hy]
--     -- · rw [←hy]

-- lemma baf {πs : List (BalanceProof K₁ K₂ C Pi V)}
--           {acc : BalanceProof K₁ K₂ C Pi V}
--           (h : k ∈ acc ∧ k ∈ πs.toFinset.toSet → acc k ≅ hd k) :
--   IsLUB ({acc} ∪ πs.toFinset.toSet) (mergeR'' πs acc) := by
--   induction' πs with hd tl ih generalizing acc
--   · simp [Set.insert]
--   · simp
--     rw [Set.insert_comm]
--     unfold mergeR''
--     rcases tl with _ | ⟨hd', tl'⟩
--     · simp
--       apply proposition6' h
    -- simp
    -- apply proposition6' sorry
    -- simp at ih ⊢
    -- rw [←Dict.Merge_assoc]
    
    -- have : insert acc (insert hd {a | a = hd' ∨ a ∈ tl'}) =
    --        {acc, hd} ∪ {a | a = hd' ∨ a ∈ tl'} := by aesop
    -- simp_rw [this]; clear this
    -- specialize @ih hd

    -- have : {acc, hd} ∪ {a | a = hd' ∨ a ∈ tl'} = {acc, hd, hd'} ∪ {a | a ∈ tl'} := by aesop
    -- simp_rw [this]; clear this

    -- have : insert hd' (insert hd {a | a ∈ tl'}) = {hd, hd'} ∪ {a | a ∈ tl'} := by aesop
    -- simp_rw [this] at ih; clear this


    
    



    -- specialize @ih (Dict.Merge acc hd)
    -- have : insert hd' (insert (Dict.Merge acc hd) {a | a ∈ tl'}) =
    --        {acc, hd} ∪ {a | a = hd' ∨ a ∈ tl'} := by
    --   have : {a | a = hd' ∨ a ∈ tl'} = insert hd' {a | a ∈ tl'} := by aesop
    --   simp_rw [this]
    --   have : {acc, hd} ∪ insert hd' {a | a ∈ tl'} =
    --          {acc, hd, hd'} ∪ {a | a ∈ tl'} := by aesop
    --   simp_rw [this]
    --   have : insert (Dict.Merge acc hd) {a | a ∈ tl'} =
    --          {Dict.Merge acc hd} ∪ {a | a ∈ tl'} := by aesop
    --   simp_rw [this]

    -- sorry
    -- simp at ih ⊢
    -- rw [←Dict.Merge_assoc]
    -- have : insert acc (insert hd {a | a = hd' ∨ a ∈ tl'}) =
    --        {acc, hd} ∪ {a | a = hd' ∨ a ∈ tl'} := by aesop
    -- simp_rw [this]; clear this
    -- specialize @ih (Dict.Merge acc hd)
    -- have : insert hd' (insert (Dict.Merge acc hd) {a | a ∈ tl'}) =
    --        {acc, hd} ∪ {a | a = hd' ∨ a ∈ tl'} := by
    --   have : {a | a = hd' ∨ a ∈ tl'} = insert hd' {a | a ∈ tl'} := by aesop
    --   simp_rw [this]
    --   have : {acc, hd} ∪ insert hd' {a | a ∈ tl'} =
    --          {acc, hd, hd'} ∪ {a | a ∈ tl'} := by aesop
    --   simp_rw [this]
    --   have : insert (Dict.Merge acc hd) {a | a ∈ tl'} =
    --          {Dict.Merge acc hd} ∪ {a | a ∈ tl'} := by aesop
    --   simp_rw [this]


    -- simp_rw [←this]
    -- exact ih




--     -- have : IsLUB ({acc} ∪ {mergeR'' tl hd}) (Dict.Merge acc (mergeR'' tl hd)) := by
--       -- apply proposition6XK
--       -- rintro k ⟨h₁, h₂⟩
--       -- specialize @ih hd
--       -- apply proposition6W at ih
--       -- rw [←proposition2]
--       -- sorry







--     -- apply proposition6XK
--     -- unfold mergeR''
--     -- rcases tl with _ | ⟨hd', tl'⟩
--     -- · simp
--     --   have : Set.insert acc {hd} = {acc, hd} := by aesop
--     --   simp_rw [this]; clear this
--     --   apply proposition6'
--     --   rintro k ⟨h₁, h₂⟩
--     --   simp [Set.insert] at ih






-- lemma haf {πs : (Pi × ExtraDataT) × TransactionBatch K₁ K₂ V} :
--   IsLUB πs.toFinset.toSet (mergeR'' πs .initial) := by

--   done


lemma oompf {n : ℕ} {πs : List (BalanceProof K₁ K₂ C Pi V)} (h : n < πs.length + 1) :
  IsLUB (πs.take n).toFinset.toSet (mergeR πs n) := by
  induction' n with n ih
  · unfold mergeR; aesop
  · simp at ih h; specialize ih (by omega)
    unfold mergeR; simp [h]; rw [List.take_succ]
    rw [List.getElem?_eq, dif_pos h, Option.toList_some]
    have : {a | a ∈ List.take n πs ++ [πs[n]]} = {a | a ∈ List.take n πs} ∪ {πs[n]} := by
      ext elem
      simp only [Set.mem_setOf_eq]; rw [List.mem_append]
      simp; tauto
    rw [this]; clear this
    set πs₁ := {a | a ∈ List.take n πs} with eqπs₁
    set πₙ := mergeR πs n with eqπₙ
    set πₘ := πs[n]
    set smol := Dict.Merge πₙ πₘ with eqsmol

    -- have : IsLUB _ smol := proposition6' _
    -- have : ∃ join, join ≅ Dict.Merge D₁ D₂




--     -- unfold mergeR
--     -- simp [h]
--     -- rw [dif_pos (by omega)]
--     -- rcases n with _ | n
--     -- · unfold mergeR at hk; simp at hk
--     --   unfold BalanceProof.initial at hk
--     --   rw [Dict.mem_iff_isSome] at hk
--     --   simp at hk
--     -- · simp
--     --   simp at hk



--     done

--     done


--     -- simp only [IsLUB, IsLeast]
--     -- split_ands
--     -- · rw [mem_upperBounds]
--     --   intros x hx
--     --   have : x ∈ {a | a ∈ List.take n πs ++ [πs[n]]} ↔
--     --          x ∈ {a | a ∈ List.take n πs} ∨ x = πs[n] := by
--     --     simp only [Set.mem_setOf_eq]
--     --     rw [List.mem_append]
--     --     simp
--     --   rw [this] at hx
--     --   rcases hx with hx | hx
--     --   · simp at hx




-- --   · rcases πs with _ | ⟨π, πs⟩
-- --     · simp at h
-- --     · rcases n with _ | n
-- --       · unfold mergeR
-- --         simp
-- --         unfold mergeR
-- --         simp
-- --       · simp at h i
-- --         unfold mer
-- --         simp
-- --         set smol := Dict.Merge (mergeR πs n) πs[n] with eqs
-- --         have : IsLUB _ smol := proposition6
-- --         case x
-- --         s
-- --         intros k
-- --         unfold mer
-- --         rw [dif_pos (by omeg
-- --         rcases n with _
-- --         · s
-- --           unfold mergeR at
-- --           simp at
-- --           rcases hk with hk |
-- --         · s
-- --           unfold mergeR at
-- --           simp at
-- --           -- rw [dif_pos (by omeg
-- --           rw [dif_pos (by omega)] at
-- --           specialize ih (πs := πs) (by ome
-- --           obtain ⟨h₁, h₂⟩ :=
-- --           simp [upperBounds, lowerBounds] at h₁
-- --           specialize @h₁ πs[n + 1] sorry



-- --       specialize @h₂ _ πs[n + 1]
-- --       rw [List.getElem_mem] at h₁

-- --       -- apply funext
-- --       -- intros K
-- --       -- rw [Dict.keys_Merge_left]
-- --       -- unfold mergeR

-- --     done
-- --     specialize ih (πs := πs) (by omega)
-- --     obtain ⟨h₁, h₂⟩ := this
-- --     simp [upperBounds] at h₁
-- --     obtain ⟨h₃, h₄⟩ := ih
-- --     simp [upperBounds] at h₃
-- --     simp [IsLUB, IsLeast, upperBounds, lowerBounds]
-- --     split_ands
-- --     · intros a h'; rw [eqsmol] at h₁ ⊢
-- --       rw [List.take_succ] at h'; simp at h'
-- --       rcases h' with h' | h'
-- --       · rcases h₁ with ⟨h₁, h₁'⟩
-- --         specialize @h₃ a
-- --         refine' le_trans _ h₁
-- --         apply h₃ h'
-- --       · have : πs[n] = a := by rw [List.getElem?_eq_some] at h'
-- --                                rcases h' with ⟨w, hw⟩
-- --                                exact hw
-- --         rw [←this]
-- --         exact h₁.2
-- --     · simp [(·≤·)] at h₁
-- --       -- intros a h'; rw [eqsmol] at h₂ ⊢
-- --       -- specialize @h' smol
-- --       -- rw [List.take_succ] at h'; simp at h'
-- --       -- apply h'
-- --       -- simp [lowerBounds, upperBounds] at h₂ h₄
-- --       -- specialize @h₂ smol
-- --       -- apply h₂
-- --       -- apply h₄
-- --       -- intros π hπ


-- --       -- rcases h' with h' | h'
-- --       -- rw [eqsmol]
-- --       -- specialize @ha smol
-- --       -- apply ha




-- --     -- rcases πs with _ | ⟨hd, tl⟩
-- --     -- · simp at h
-- --     -- · simp at h ⊢



-- -- --   sorry

-- -- -- --   sorry

lemma batch_eq_iff {π₁k π₂k : (Pi × ExtraDataT) × TransactionBatch K₁ K₂ V} :
  (π₁k ≅ π₂k) ↔ π₁k.2 = π₂k.2 := by
  unfold iso
  simp [(·≤·)]
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
  (h : ¬(π₁k ≅ π₂k)) : (π₁k.get (by unfold iso at h
                                    simp [(·≤·)] at h
                                    aesop)).2 ≠
                       (π₂k.get (by unfold iso at h
                                    simp [(·≤·)] at h
                                    aesop)).2 := by
  unfold iso at h
  simp [(·≤·)] at h
  aesop

  -- unfold iso at h
  -- simp only [(·≤·)] at h
  -- rcases π₁k with _ | π₁k <;> rcases π₂k with _ | π₂k
  -- · simp
  -- · simp at h₀
  -- · simp at h₀
  -- · dsimp at h ⊢
  --   by_contra contra
  --   rw [not_and_or] at h
  --   rcases h with h | h

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

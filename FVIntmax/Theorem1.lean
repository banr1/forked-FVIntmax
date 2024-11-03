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
lemma Block.updateBalance_deposit{r : K₂} {v : V} {vplus : V₊} :
  (Block.deposit r vplus).updateBalance (K₁ := K₁) (C := C) (Sigma := Sigma) v = v + vplus := by
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

def adversaryWon (blocks : RollupState K₁ K₂ V C Sigma) := ¬0 ≤ computeBalance blocks

section AttackGameLemmas

variable {request : Request K₁ K₂ C Sigma Pi V}
         {requests : List (Request K₁ K₂ C Sigma Pi V)}
         {σ : RollupState K₁ K₂ V C Sigma}

/--
The 'obvious' `∑ (i : {i : Fin σ.length // σ[i].isDepositBlock}) ...` is slightly clumsy.
-/
def computeBalanceErik (σ : RollupState K₁ K₂ V C Sigma) := 
  let v_deposited : V :=
    ∑ i : Fin σ.length,
      if h : σ[i].isDepositBlock
      then (σ[i.1].getDeposit h).2
      else 0
  let v_withdrawn : V :=
    ∑ i : Fin σ.length,
      if h : σ[i].isWithdrawalBlock
      then ∑ (k : K₁), (σ[i.1].getWithdrawal h) k
      else 0
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

set_option maxHeartbeats 600000 in
/--
Obviously needs to be cleaned up.
-/
private lemma computeBalance'_eq_Erik_aux : computeBalance' σ v = v + computeBalanceErik σ := by
  induction' σ with hd tl ih generalizing v
  · simp [computeBalanceErik]
  · rw [computeBalance'_eq_zero]; simp
    unfold computeBalance' computeBalanceErik at ih ⊢
    rw [ih]
    lift_lets
    intros d₁ w₁ d₂ w₂
    match heq : hd with
    | .transfer .. => have eq₁ : d₁ = d₂ := by
                        sorry
                        -- simp [d₁, d₂]
                        -- simp [Finset.sum_fin_eq_sum_range]
                        -- nth_rw 2 [Finset.sum_eq_sum_diff_singleton_add (i := 0)]
                        -- rw [dif_pos (show 0 < tl.length + 1 by omega)]
                        -- rw [dif_neg (by aesop)]
                        -- let F : ℕ → V := λ i ↦
                        --   if h : i < tl.length then
                        --   if h_1 : tl[i].isDepositBlock = true then
                        --   (tl[i].getDeposit h_1).2 else 0
                        --   else 0
                        -- let F' : (a : ℕ) → a ∈ Finset.range (tl.length + 1) \ {0} → ℕ :=
                        --   λ a ha ↦ a.pred
                        -- nth_rw 2 [Finset.sum_bij (t := Finset.range tl.length) (g := F)]
                        -- simp [F]
                        -- exact F'
                        -- simp [F']
                        -- intros a ha₁ ha₂
                        -- omega
                        -- simp [F']; intros a ha₁ ha₂ b hb₁ hb₂ h₃
                        -- omega
                        -- simp [F']
                        -- intros b hb
                        -- use b.succ
                        -- simpa
                        -- simp [F', F]
                        -- intros a ha₁ ha₂
                        -- rw [dif_pos ha₁]
                        -- have : a - 1 < tl.length ↔ a < tl.length + 1 := by omega
                        -- simp_rw [this, dif_pos ha₁]
                        -- rcases a with _ | a; simp at ha₂
                        -- simp
                        -- rw [Finset.mem_range]; omega
                      have eq₂ : w₁ = w₂ := by
                        sorry
                        -- simp [w₁, w₂]
                        -- simp [Finset.sum_fin_eq_sum_range]
                        -- nth_rw 2 [Finset.sum_eq_sum_diff_singleton_add (i := 0)]
                        -- rw [dif_pos (show 0 < tl.length + 1 by omega)]
                        -- rw [dif_neg (by aesop)]
                        -- let F : ℕ → V := λ i ↦
                        --   if h : i < tl.length then
                        --   if h_1 : tl[i].isWithdrawalBlock = true
                        --   then ∑ x_1 : K₁, tl[i].getWithdrawal h_1 x_1 else 0
                        --   else 0
                        -- let F' : (a : ℕ) → a ∈ Finset.range (tl.length + 1) \ {0} → ℕ :=
                        --   λ a ha ↦ a.pred
                        -- nth_rw 2 [Finset.sum_bij (t := Finset.range tl.length) (g := F)]
                        -- simp [F]
                        -- exact F'
                        -- simp [F']
                        -- intros a ha₁ ha₂
                        -- omega
                        -- simp [F']; intros a ha₁ ha₂ b hb₁ hb₂ h₃
                        -- omega
                        -- simp [F']
                        -- intros b hb
                        -- use b.succ
                        -- simpa
                        -- simp [F', F]
                        -- intros a ha₁ ha₂
                        -- rw [dif_pos ha₁]
                        -- have : a - 1 < tl.length ↔ a < tl.length + 1 := by omega
                        -- simp_rw [this, dif_pos ha₁]
                        -- rcases a with _ | a; simp at ha₂
                        -- simp
                        -- rw [Finset.mem_range]; omega
                      simp [eq₁, eq₂]
    | .deposit _ v => have : w₁ = w₂ := by
                        simp [w₁, w₂]
                        simp [Finset.sum_fin_eq_sum_range]
                        nth_rw 2 [Finset.sum_eq_sum_diff_singleton_add (i := 0)]
                        rw [dif_pos (show 0 < tl.length + 1 by omega)]
                        rw [dif_neg (by aesop)]
                        let F : ℕ → V := λ i ↦
                          if h : i < tl.length then
                          if h_1 : tl[i].isWithdrawalBlock = true
                          then ∑ x_1 : K₁, tl[i].getWithdrawal h_1 x_1 else 0
                          else 0
                        let F' : (a : ℕ) → a ∈ Finset.range (tl.length + 1) \ {0} → ℕ :=
                          λ a ha ↦ a.pred
                        nth_rw 2 [Finset.sum_bij (t := Finset.range tl.length) (g := F)]
                        simp [F]
                        exact F'
                        simp [F']
                        intros a ha₁ ha₂
                        omega
                        simp [F']; intros a ha₁ ha₂ b hb₁ hb₂ h₃
                        omega
                        simp [F']
                        intros b hb
                        use b.succ
                        simpa
                        simp [F', F]
                        intros a ha₁ ha₂
                        rw [dif_pos ha₁]
                        have : a - 1 < tl.length ↔ a < tl.length + 1 := by omega
                        simp_rw [this, dif_pos ha₁]
                        rcases a with _ | a; simp at ha₂
                        simp
                        rw [Finset.mem_range]; omega
                      simp [this]
                      rw [add_sub]
                      simp [d₁, d₂]
                      simp [Finset.sum_fin_eq_sum_range]
                      nth_rw 2 [Finset.sum_eq_sum_diff_singleton_add (i := 0)]
                      rw [dif_pos (show 0 < tl.length + 1 by omega)]
                      rw [dif_pos (by aesop)]
                      simp_rw [List.getElem_cons_zero, heq]
                      dsimp [Block.getDeposit] -- TODO: make lemma
                      nth_rw 2 [add_comm]
                      apply congr_arg
                      symm
                      -- reorder
                      let F' : (a : ℕ) → a ∈ Finset.range (tl.length + 1) \ {0} → ℕ :=
                          λ a ha ↦ a.pred
                      apply Finset.sum_bij (i := F')
                      simp [F']
                      intros a ha₁ ha₂
                      omega
                      simp [F']; intros a ha₁ ha₂ b hb₁ hb₂ h₃
                      omega
                      simp [F']
                      intros b hb
                      use b.succ
                      simpa
                      simp [F']
                      rintro a ⟨ha₁, ha₂⟩
                      rw [dif_pos ha₁]
                      have : a - 1 < tl.length ↔ a < tl.length + 1 := by omega
                      simp_rw [this, dif_pos ha₁]
                      rcases a with _ | a; simp at ha₂
                      simp
                      rw [Finset.mem_range]; omega
    | _ => sorry
    



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
  simp [attackGameR] at h₁
  /-
    Ideally, we want to show that `(attackGameR requests []).isWithdrawal → requests[i].isWithdrawal`,
    but we'll prove it as a corollary of this one for an arbitrary state σ rather than [].
  -/

  /-
    By induction on requests for an arbitrary `i`.
  -/
  induction' requests with hd tl ih generalizing i
  /-
    The base case is trivial.
  -/
  · simp at hi₂ h₁; omega
  /-
    Suppose the requests are `hd :: tl`. (I.e. a single element followed by some tail.)
  -/
  · rcases i with _ | i
    /-
      Suppose first that i = 0.

      Then we know we are accessing the very first request and as such, one only needs to consult
      the function `Request.toBlock!` to establish this holds.
    -/
    · simp at hi₁
      subst hi₁
      simp [Request.toBlock!] at h₁ ⊢
      rcases hd <;> simp_all
    /-
      Suppose next that i = i + 1.
    -/
    · rcases σ with _ | ⟨hd', tl'⟩
      /-
        Suppose further that `σ` is empty.

        We can immediately conclude this holds by the inductive hypothesis and the fact that
        the shape of blocks is invariant with respect to state and is dependent only on the shape
        of the initial requests (as witnessed by `attackGameRGo_isWithdrawal_iff`).
      -/
      · simp at hi₁ hi₂ h₁ ih ⊢
        apply ih (by aesop)
        rw [attackGameRGo_isWithdrawal_iff (σ' := RollupState.appendBlock! [] hd)]
        exact h₁
        exact hi₂
      /-
        Suppose now that `σ` is _not_ empty, but `hd' :: tl'`.
        
        Note we have that `tl'.length ≤ i`.
      -/
      · simp at hi₁ ⊢
        rw [le_iff_eq_or_lt] at hi₁
        rcases hi₁ with hi₁ | hi₁
        /-
          For the case where `tl'.length = i`, we know we are accessing `hd` and the rest is trivial.
        -/
        · simp_rw [hi₁]; simp
          simp [Request.toBlock!] at h₁ ⊢
          simp_rw [←hi₁] at h₁
          rw [List.getElem_append_right] at h₁
          simp [Request.toBlock!] at h₁ ⊢
          rcases hd <;> simp_all
          simp
          simp
        /-
          For when `tl'.length < i`, we know that accessing `(hd :: tl)[i - tl'.length]`
          always reaches the tail as `i - tl'.length > 0`. Thus, we can invoke the inductive hypothesis
          together with lemma `attackGameRGo_isWithdrawal_iff` to establish this holds.
        -/
        · rw [lt_iff_exists_add] at hi₁
          rcases hi₁ with ⟨c, ⟨hc₁, hc₂⟩⟩
          simp_rw [hc₂]
          rcases c with _ | c <;> [simp at hc₁; skip]
          simp
          specialize ih (by aesop) (c + (hd' :: tl').length)
          simp at ih
          apply ih
          swap
          simp at hi₂
          omega
          simp_rw [←Nat.add_assoc]
          simp
          simp at h₁
          simp_rw [hc₂] at h₁
          simp_rw [←Nat.add_assoc] at h₁
          simp_rw [List.append_cons (as := tl') (b := Request.toBlock! (hd' :: tl') hd) (bs := attackGameRGo tl (RollupState.appendBlock! (hd' :: tl') hd))] at h₁
          rw [List.getElem_append_right (as := tl' ++ [Request.toBlock! (hd' :: tl') hd]) (bs :=
              attackGameRGo tl (RollupState.appendBlock! (hd' :: tl') hd))] at h₁
          rw [List.getElem_append_right]
          simp at h₁ ⊢
          rw [attackGameRGo_isWithdrawal_iff (σ' := (hd' :: tl'))] at h₁
          exact h₁
          simp
          simp at hc₂ hi₂ ⊢
          rw [hc₂] at hi₂
          simp at hi₂
          exact hi₂
          simp
          simp at hc₂ hi₂ ⊢
          rw [hc₂] at hi₂
          simp at hi₂
          exact hi₂

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

end AttackGameLemmas

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

variable [ADScheme K₂ (C × K₁ × ExtraDataT) C Pi]
         [CryptoAssumptions.Injective (H (α := TransactionBatch K₁ K₂ V × ExtraDataT) (ω := (C × K₁ × ExtraDataT)))]

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
  have hn : n = requests!.length := by simp [n, eqBstar]
  let I : List (Fin n) := (List.finRange n).filter (Bstar[·].isWithdrawalBlock)
  have hI : ∀ i ∈ I, Bstar[i].isWithdrawalBlock := by aesop
  let getπ : {i : Fin n // i ∈ I} → BalanceProof K₁ K₂ C Pi V :=
    λ ⟨i, hi⟩ ↦
      have lenEq : (attackGameR requests! []).length = n := by simp [n, eqBstar]
      have hi₁ : i.1 < (attackGameR requests! []).length := by rw [lenEq]; exact i.2
      getBalanceProof requests! hValid ⟨i.1, hi₁⟩ (hI i hi)
  let πs : List (BalanceProof K₁ K₂ C Pi V) := I.attach.map getπ
  
  sorry

end AttackGame

end lemma1

end Intmax

end Intmax

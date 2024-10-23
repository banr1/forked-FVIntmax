import Mathlib
import Mathlib.Algebra.Group.Int

import FVIntmax.BalanceProof
import FVIntmax.Block
import FVIntmax.Key
import FVIntmax.RollupContract
import FVIntmax.State
import FVIntmax.Transaction
import FVIntmax.Wheels

import FVIntmax.Wheels.Dictionary

namespace Intmax

/-
Honestly just saves a bit of time. There's nothing fundamentally noncomputable / classical here.
-/
noncomputable section
open Classical

/-
Appendix B - Computing balances
-/
section Balance

variable {Pi K₁ K₂ V C Sigma : Type}

/-
B.1 Step 1: Extracting a list of partial transaction
-/
section Extraction

section Deposit

variable [Nonnegative V]

def TransactionsInBlock_deposit
  (b : { b : Block K₁ K₂ C Sigma V // b.isDepositBlock }) : List (Τ K₁ K₂ V) :=
  match h : b.1 with
  | .deposit r v => [⟨(.Source, r, v), by valid⟩]
  | .withdrawal .. | .transfer .. => by aesop

@[simp]
lemma length_TransactionsInBlock_deposit
  {b : { b : Block K₁ K₂ C Sigma V // b.isDepositBlock }} :
  (TransactionsInBlock_deposit b).length = 1 := by
  unfold TransactionsInBlock_deposit
  rcases b with ⟨b, h⟩
  match b with
  | Block.deposit .. => simp
  | Block.transfer .. | Block.withdrawal .. => simp at h

-- /--
-- The sender is always `.Source`.
-- -/
-- lemma sender_TransactionsInBlock_deposit
--   {b : { b : Block K₁ K₂ C Sigma V // b.isDepositBlock }} :
--   ∀ i : ℕ, (h : i < (TransactionsInBlock_deposit b).length) →
--            ((TransactionsInBlock_deposit b)[i]'h).1.1 = .Source := by
--   intros i h
--   simp [TransactionsInBlock_deposit]
--   rcases b with ⟨b, h₁⟩
--   match b with
--   | Block.deposit .. => simp
--   | Block.transfer .. | Block.withdrawal .. => simp at h₁ 

end Deposit

section Transfer

variable [Finite K₁] [Finite K₂]
         [LinearOrder K₁] [LinearOrder K₂] [Nonnegative V]

def TransactionsInBlock_transfer 
  (π : BalanceProof K₁ K₂ C Pi V) (b : { b : Block K₁ K₂ C Sigma V // b.isTransferBlock }) : List (Τ K₁ K₂ V) :=
  match h : b.1 with
  | .transfer _ _ commitment S _ =>
    /-
      PAPER: for each sender-recipient pair (s, r) ∈ K2 × K where s ̸= r
    -/
    let senderRecipient : Finset (K₂ × Key K₁ K₂) := { (k₂, k) | (k₂ : K₂) (k : Key K₁ K₂) (_h : k₂ ≠ₖ k) }
    let sorted : List (K₂ × Key K₁ K₂) := senderRecipient.sort Key.lexLe -- NB cf. Key.lean - section CanSortWith
    /-
      PAPER:
      v = t(r), where ( , t) = π(C, s), if s ∈ S and π(C, s) ̸= ⊥
          ⊥,                            if s ∈ S and π(C, s) = ⊥
          0,                            if s /∈ S
    -/
    let v (s : K₂) (r : Key K₁ K₂) : Option V₊ :=
      if s ∉ S
      then .some 0
      else 
        if h : (commitment, s) ∈ π.keys
        then let (_, t) := π[(commitment, s)]
             t r
        else .none
    sorted.attach.map λ ⟨(s, r), h⟩ ↦ ⟨(s, r, v s r), by valid⟩
  | .deposit .. | .withdrawal .. => by aesop

lemma length_TransactionsInBlock_transfer
  {b : { b : Block K₁ K₂ C Sigma V // b.isTransferBlock }} :
  ∀ (π₁ π₂ : BalanceProof K₁ K₂ C Pi V),
    (TransactionsInBlock_transfer π₁ b).length =
    (TransactionsInBlock_transfer π₂ b).length := by
  unfold TransactionsInBlock_transfer
  aesop

end Transfer

section Withdrawal

variable [LinearOrder K₁] [Finite K₁] [Nonnegative V]

def TransactionsInBlock_withdrawal 
  (b : { b : Block K₁ K₂ C Sigma V // b.isWithdrawalBlock }) : List (Τ K₁ K₂ V) :=
  match h : b.1 with
  | .withdrawal withdrawals =>
    /-
      Plumbing. Ignore.
    -/
    have : Fintype K₁ := Fintype.ofFinite _

    /-
      Careful, order.
    -/
    let k₁InOrder := { s | s : K₁ }.toFinset.sort (·≤·)
    k₁InOrder.attach.map λ s : K₁ ↦ ⟨(s, .Source, withdrawals s), by valid⟩
  | .deposit r v | .transfer .. => by aesop

@[simp]
lemma length_TransactionsInBlock_withdrawal
  {b : { b : Block K₁ K₂ C Sigma V // b.isWithdrawalBlock }} :
  (TransactionsInBlock_withdrawal b).length = Nat.card K₁ := by
  unfold TransactionsInBlock_withdrawal
  rcases b with ⟨b, h⟩
  match b with
  | Block.withdrawal .. =>
    simp; rw [List.map_congr_left (g := Function.const _ 1) (by simp), List.map_const]
    simp
  | Block.deposit .. | Block.transfer .. => simp at h 

end Withdrawal

variable [Finite K₁] [LinearOrder K₁]
         [Finite K₂] [LinearOrder K₂]
         [Nonnegative V]

local macro:max (priority := high) "↪" b:term : term => `(⟨$b, by aesop⟩)

def TransactionsInBlock (π : BalanceProof K₁ K₂ C Pi V) (b : Block K₁ K₂ C Sigma V) : List (Τ K₁ K₂ V) := 
  match h : b with
  | .deposit ..    => TransactionsInBlock_deposit ↪b
  | .transfer ..   => TransactionsInBlock_transfer π ↪b
  | .withdrawal .. => TransactionsInBlock_withdrawal ↪b

lemma length_transactionsInBlock {b : Block K₁ K₂ C Sigma V}
                                 (π₁ π₂ : BalanceProof K₁ K₂ C Pi V) :
  (TransactionsInBlock π₁ b).length = (TransactionsInBlock π₂ b).length := by
  unfold TransactionsInBlock
  split <;> try simp
  rw [length_TransactionsInBlock_transfer]

lemma sender_transactionsInBlock {b : Block K₁ K₂ C Sigma V}
                                 (π₁ π₂ : BalanceProof K₁ K₂ C Pi V) :
  (TransactionsInBlock π₁ b).map (λ s ↦ s.1.1) =
  (TransactionsInBlock π₂ b).map (λ s ↦ s.1.1) := by
  apply List.ext_get (by simp; rw [length_transactionsInBlock])
  intros n h₁ h₂
  simp; unfold TransactionsInBlock
  match b with
  | Block.deposit ..    => simp [TransactionsInBlock_deposit]
  | Block.transfer ..   => simp [TransactionsInBlock_transfer]
  | Block.withdrawal .. => simp [TransactionsInBlock_withdrawal]

lemma receiver_transactionsInBlock {b : Block K₁ K₂ C Sigma V}
                                   (π₁ π₂ : BalanceProof K₁ K₂ C Pi V) :
  (TransactionsInBlock π₁ b).map (λ s ↦ s.1.2.1) =
  (TransactionsInBlock π₂ b).map (λ s ↦ s.1.2.1) := by
  apply List.ext_get (by simp; rw [length_transactionsInBlock])
  intros n h₁ h₂
  simp; unfold TransactionsInBlock
  match b with
  | Block.deposit ..    => simp [TransactionsInBlock_deposit]
  | Block.transfer ..   => simp [TransactionsInBlock_transfer]
  | Block.withdrawal .. => simp [TransactionsInBlock_withdrawal]

def TransactionsInBlocks
  (π : BalanceProof K₁ K₂ C Pi V) (bs : List (Block K₁ K₂ C Sigma V)) : List (Τ K₁ K₂ V) :=
  (bs.map (TransactionsInBlock π)).join

/--
PAPER: Note that the function TransactionsInBlocks outputs a list of partial transactions whose
length is only dependent on the second argument (the list of blocks)...
-/
lemma length_transactionsInBlocks {bs : List (Block K₁ K₂ C Sigma V)}
                                  (π₁ π₂ : BalanceProof K₁ K₂ C Pi V) :
  (TransactionsInBlocks π₁ bs).length = (TransactionsInBlocks π₂ bs).length := by
  unfold TransactionsInBlocks; simp
  rw [List.map_congr_left]; intros _ _; simp
  rw [length_transactionsInBlock]

lemma sender_transactionsInBlocks {bs : List (Block K₁ K₂ C Sigma V)}
                                  (π₁ π₂ : BalanceProof K₁ K₂ C Pi V) :
  (TransactionsInBlocks π₁ bs).map (λ s ↦ s.1.1) =
  (TransactionsInBlocks π₂ bs).map (λ s ↦ s.1.1) := by
  simp [TransactionsInBlocks, List.map_join, List.map_join]
  exact List.map_join_eq (λ _ ↦ sender_transactionsInBlock π₁ π₂)

lemma receiver_transactionsInBlocks {bs : List (Block K₁ K₂ C Sigma V)}
                                  (π₁ π₂ : BalanceProof K₁ K₂ C Pi V) :
  (TransactionsInBlocks π₁ bs).map (λ s ↦ s.1.2.1) =
  (TransactionsInBlocks π₂ bs).map (λ s ↦ s.1.2.1) := by
  simp [TransactionsInBlocks, List.map_join, List.map_join]
  exact List.map_join_eq (λ _ ↦ receiver_transactionsInBlock π₁ π₂)

end Extraction

/-
B.2 Step 2: Computing balances from a list of partial transactions
-/
section e

def e (i : Kbar K₁ K₂) : Kbar K₁ K₂ → ℤ := λ j ↦ if i = j then 1 else 0

variable {i j : Kbar K₁ K₂}

@[simp]
lemma e_def : e i = λ j ↦ if i = j then 1 else 0 := rfl

lemma nonneg_e : 0 ≤ e i j := by unfold e; aesop

end e

/-
We use the full lattice ordered ableian group structure with reckless abandon here.
There is technically still no need to for all the upcoming definitions
but we are at the core of the protocol and so might as well.
-/
section WithStructuredTypes

section v'

variable [Zero V] [Lattice V] -- NB `Nonnegative V` is implied as `CompleteLattice V` gives `Preorder V`.

def v' (v : V₊) (b : S K₁ K₂ V) (s : Kbar K₁ K₂) : V₊ :=
  match h : s with
  | .Source => v
  | .key _  => ⟨v ⊓ b s, by simp [h]⟩

variable {v : V₊} {b : S K₁ K₂ V} {s : Kbar K₁ K₂}

-- lemma v'_nonneg_of_valid : 0 ≤ v' v b s := by aesop

@[simp]
lemma v'_source_eq_v : v' v b .Source = v := by unfold v'; aesop

@[simp]
lemma v'_key_eq_meet {k : Key K₁ K₂} : v' v b (Kbar.key k) = ⟨v ⊓ b k, by simp⟩ := by aesop

@[simp]
lemma v'_zero : v' 0 b s = 0 := by unfold v'; aesop

@[simp]
lemma v'_self {h} : v' ⟨(b s), h⟩ b s = ⟨b s, h⟩ := by unfold v'; aesop

@[simp]
lemma v'_cast_nonneg : 0 ≤ ↑(v' v b' s) := by simp

end v'

section Fc

variable [Lattice V]
         [AddCommGroup V]
         [CovariantClass V V (· + ·) (· ≤ ·)]
         [CovariantClass V V (Function.swap (· + ·)) (· ≤ ·)]

/--
Transaction function for complete transactions.
-/
def fc (τcXb : Τc K₁ K₂ V × S K₁ K₂ V) : S K₁ K₂ V :=
  ⟨λ k : Kbar K₁ K₂ ↦
    match τcXb with
    | ⟨⟨⟨⟨s, r, v⟩, _⟩, hτ⟩, b⟩ =>
      let v' := v' (v.get hτ) b s
      b k + (e r - e s) k • v',
  by rintro (k | _) <;>
     aesop (add unsafe apply le_add_of_le_of_nonneg)
  ⟩

variable {τc : Τc K₁ K₂ V} {b : S K₁ K₂ V}

@[simp]
lemma fc_key : 0 ≤ fc (τc, b) (.key k) := by simp

lemma le_fc_of_ne {k : Kbar K₁ K₂} (h : τc.1.1.1 ≠ k) : b k ≤ fc (τc, b) k := by unfold fc v'; aesop

end Fc

section Order

variable [Lattice V] [AddCommGroup V]

instance (priority := high) : LE (Kbar K₁ K₂) := ⟨(·=·)⟩

instance : Preorder (Kbar K₁ K₂) := discretePreorder

instance : Preorder (Kbar K₁ K₂ × Kbar K₁ K₂) := inferInstance

instance (priority := high) discreteOpreorderNnonnegV : Preorder V₊ := discretePreorder

/--
Demote a preorder on `V₊` to equality ASAP.
-/
@[simp]
lemma discretePreorder_eq_equality_Vplus {a b : V₊} : a ≤ b ↔ a = b := by rfl

/--
Demote a preorder on `Kbar K₁ K₂` to equality ASAP.
-/
@[simp]
lemma discretePreorder_eq_equality_Kbar {a b : Kbar K₁ K₂} : a ≤ b ↔ a = b := by rfl

/--
Definition 15
Let (X, ≤X) be a proset. We define the induced preorder ≤ on
Maybe(X) where for all x, y ∈ M aybe(X) we have
x ≤ y ⇔ x = ⊥ ∨ (x, y ∈ X ∧ x ≤X y)
-/
instance (priority := high) maybeInduced {α : Type} [Preorder α] : Preorder (Option α) :=
  let le : Option α → Option α → Prop := λ x y ↦
                                           match x, y with
                                           | .none, .none | .none, .some _ => True
                                           | .some x, .some y => x ≤ y
                                           | .some _, .none   => False
  {
    le := le
    lt := λ a b ↦ le a b ∧ ¬ le b a -- `False` at home.
    le_refl := by dsimp [le]; aesop
    le_trans := by dsimp [le, (·≤·)]; aesop (add safe forward le_trans)
  }

/--
PAPER: which induces a preorder on Maybe(V+)

NB this finds the custom high priority instance `maybeInduced`, i.e. Definition 15.
-/
instance : Preorder (Option V₊) := inferInstance

/--
PAPER: We then get the induced product preorder on K2 × Maybe(V+).

NB the default behavviour is iso with the Definition 19. (cf. `Prod.mk_le_mk`)
-/
instance : Preorder (Kbar K₁ K₂ × Kbar K₁ K₂ × Option V₊) := inferInstance

/--
PAPER: and an induced subset preorder on the subset T

NB the default behaviour is iso with the Definition 18. (cf. `Preorder.lift`),
transitively via subset/subtype iso
-/
instance : Preorder (Τ K₁ K₂ V) := inferInstance

/--
PAPER: we use the underlying preorder on V coming from the fact that V is a lattice

NB the default behaviour is the lattice-induced preorder. (cf. `PartialOrder.toPreorder`)
-/
instance latticePreorder : Preorder V := inferInstance

/--
PAPER: and give S the subset preorder

NB the default behaviour is iso with the Definition 18. (cf. `Preorder.lift`)
NB the default behaviour to find the preorder for the underlying function is iso with 
Definition 16. (cf. `Pi.le_def`)
-/
instance : Preorder (S K₁ K₂ V) := inferInstance

/--
PAPER: Given these preorders on T and S, we get an induced product preorder on T × S

NB the default behavviour is iso with the Definition 19. (cf. `Prod.mk_le_mk`)
-/
instance : Preorder (Τ K₁ K₂ V × S K₁ K₂ V) := inferInstance

/--
How is this not in Mathlib...
-/ 
instance [CovariantClass V V (· + ·) (· ≤ ·)] : OrderedAddCommMonoid V := ⟨by aesop⟩

end Order

section BoundedBelow

variable [Lattice V] [AddCommGroup V]

abbrev boundedBelow (b : S K₁ K₂ V) (T : Τ K₁ K₂ V) :=
  { a : Τc K₁ K₂ V × S K₁ K₂ V | (T, b) ≤ (↑a.1, a.2) }
  
lemma boundedBelow_sset_boundedBelow_of_le {b₁ b₂ : S K₁ K₂ V} {T₁ T₂ : Τ K₁ K₂ V}
  (h : b₁ ≤ b₂) (h₁ : T₁ ≤ T₂) : boundedBelow b₂ T₂ ⊆ boundedBelow b₁ T₁ := by
  unfold boundedBelow
  rintro ⟨⟨T₃, eq⟩, b₃⟩ ⟨h₂, h₃⟩
  simp at *
  exact ⟨le_trans h₁ h₂, le_trans h h₃⟩

end BoundedBelow

section LGroup

/-
Lattice ordered abelian group. The corresponding `class abbrev` hits the performance.
-/
variable [Lattice V] [AddCommGroup V]
         [CovariantClass V V (· + ·) (· ≤ ·)]
         [CovariantClass V V (Function.swap (· + ·)) (· ≤ ·)]

/--
PAPER: The transaction function for complete transactions `fc` is monotone.
-/
@[mono]
lemma fc_mono {τc τc' : Τc K₁ K₂ V} {b₁ b₂ : S K₁ K₂ V}
              (h : (τc, b₁) ≤ (τc', b₂)) : fc (τc, b₁) ≤ fc (τc', b₂) := λ k ↦ by
  have : τc = τc' := by
    rcases τc with ⟨τc, τc''⟩; unfold Τ.isComplete at τc''
    simp [(·≤·)] at h
    aesop
  subst this; simp at h
  rcases τc with ⟨⟨⟨s | _, r, v⟩, -⟩, hτ₁⟩
  /-
    `s ≠ .Source`
  -/
  · have t₁ : r ≠ s := (Τ.s_ne_r_of_complete hτ₁).symm; simp [fc]
    generalize eq₃ : @Subtype.val _ _ (v.get hτ₁) = v₁
    · by_cases eq : k = s
      · simp [eq, t₁]
        generalize eq₁ : @Subtype.val _ _ b₁ _ = bₛ
        generalize eq₂ : @Subtype.val _ _ b₂ _ = bₛ'
        have eq₄ : bₛ ≤ bₛ' := by aesop
        have :=
        calc
          (bₛ + -(v₁ ⊓ bₛ) + v₁ ⊓ bₛ' ≤ bₛ') ↔ bₛ + -(v₁ ⊓ bₛ) ≤ bₛ' + -(v₁ ⊓ bₛ')                  := by rw [←le_add_neg_iff_add_le]
                                           _ ↔ bₛ + -v₁ ⊔ -bₛ ≤ bₛ' + -v₁ ⊔ -bₛ'                    := by simp [neg_inf]
                                           _ ↔ (bₛ + -v₁) ⊔ (bₛ + -bₛ) ≤ (bₛ' + -v₁) ⊔ (bₛ' + -bₛ') := by simp [add_sup]
                                           _ ↔ (bₛ + -v₁) ⊔ 0 ≤ (bₛ' + -v₁) ⊔ 0                     := by simp [add_neg_cancel]
        rw [this]; mono
      · by_cases eq' : k = r
        · simp [eq', t₁.symm]
          generalize eq₁ : @Subtype.val _ _ b₁ = bᵣ
          generalize eq₂ : @Subtype.val _ _ b₂ = bᵣ'
          have : bᵣ r ≤ bᵣ' r := by aesop
          mono; aesop
        · aesop
  /-
    `s = .Source`
  -/
  · simp [fc]; apply h 

def V' (b : S K₁ K₂ V) (T : Τ K₁ K₂ V) (k : Kbar K₁ K₂) : Set V :=
  { v : V | v ∈ (fc · k) '' boundedBelow b T }

/--
A technical statement that happens to come up in proofs.
It equates `Set.range` with `Set.image` and does a bit of bookkeeping.
-/
private lemma V'_eq_range {b : S K₁ K₂ V} {T : Τ K₁ K₂ V} {k : Kbar K₁ K₂} :
  V' b T k =
  Set.range λ (x : { x : (Τc K₁ K₂ V × S K₁ K₂ V) // (T, b) ≤ (↑x.1, x.2) }) ↦ fc ↑x k := by
  unfold V'
  rw [Set.image_eq_range]
  rfl

lemma V'_sset_V'_of_le {b₁ b₂ : S K₁ K₂ V} {T₁ T₂ : Τ K₁ K₂ V} {k : Kbar K₁ K₂}
  (h : b₁ ≤ b₂) (h₁ : T₁ ≤ T₂) : 
  V' b₂ T₂ k ⊆ V' b₁ T₁ k := by
  dsimp [V']
  exact Set.subset_image_iff.2 ⟨
    boundedBelow b₂ T₂,
    ⟨boundedBelow_sset_boundedBelow_of_le h h₁, by simp⟩
  ⟩

section f

opaque exists_inf (b : S K₁ K₂ V) (T : Τ K₁ K₂ V) : { s : S K₁ K₂ V // ∀ k, IsGLB (V' b T k) (s k) } :=
  /-
  PAPER: The explicit description of the transition function. 
  -/
  let f' (b : S K₁ K₂ V) (T : Τ K₁ K₂ V) : S K₁ K₂ V := 
    ⟨
      λ k ↦
        match h : T with
        | ⟨(_, _, .some v), hT⟩ => fc (⟨T, by simp [h]⟩, b) k
        | ⟨(s, _, .none), _⟩ => if k = s then 0 else b k,
      by rintro (k | k) <;> aesop
    ⟩
  ⟨
    f' b T,
    λ k ↦
      have f'_codomain : (f' b T) k ∈ V' b T k := by
        dsimp [V', f']
        rw [Set.mem_image]; dsimp
        by_cases eq : T.isComplete
        · obtain ⟨key, hkey⟩ := Option.isSome_iff_exists.1 (Τ.isSome_of_complete eq)
          use (⟨T, eq⟩, b)
          aesop
        · rcases T with ⟨⟨s₀, r₀, v₀⟩, hT⟩
          unfold Τ.isComplete at eq; simp at eq; subst eq
          obtain ⟨key, hkey⟩ := Τ'.exists_key_of_isValid hT
          have : s₀ ≠ r₀ := by unfold Τ'.isValid at hT; aesop
          by_cases eq' : s₀ = k
          · let elem : Τc K₁ K₂ V := ⟨
              ⟨⟨s₀, r₀, .some (⟨b s₀, by aesop⟩)⟩, by valid⟩,
              by valid
            ⟩
            use (elem, b)
            simp [(·≤·), fc]
            have : r₀ ≠ k := by aesop
            simp [eq', this, v']
          · let elem : Τc K₁ K₂ V := ⟨
              ⟨⟨s₀, r₀, .some 0⟩, by valid⟩,
              by valid
            ⟩
            use (elem, b)
            simp [(·≤·), fc]
            aesop
      have f'_IsGLB_of_V' : IsGLB (V' b T k) (f' b T k) := by
        dsimp [V', IsGLB, IsGreatest, lowerBounds, upperBounds, boundedBelow]; simp only [Set.mem_image]
        refine' And.intro ?isLowerBound ?isGreatest
        case isLowerBound =>
          rintro v ⟨⟨τ', b'⟩, ⟨ha₁, ⟨⟩⟩⟩; simp at ha₁
          split
          next s r v? hv? => apply fc_mono ha₁
          next s r hv? =>
            by_cases eq : k = s <;> simp [eq]
            · obtain ⟨key, ⟨⟩⟩ := Τ'.exists_key_of_isValid hv?; simp
            · have : b k ≤ b' k := by aesop
              rcases τ' with ⟨⟨⟨s', r', v'⟩, _⟩, _⟩; simp [(·≤·)] at ha₁
              exact le_trans this (le_fc_of_ne (by aesop))
        case isGreatest => exact λ _ hv ↦ hv f'_codomain
    f'_IsGLB_of_V'
  ⟩

/--
The infimum on `V` for specifically the set with the lower bound.

NB we do not assume its existence with something like a conditionally complete lattice.
-/
def infV (b : S K₁ K₂ V) (T : Τ K₁ K₂ V) (k : Kbar K₁ K₂) :
  InfSet V where
    sInf := λ s ↦ if s = V' b T k
                  then (exists_inf b T).1 k
                  else 0

/--
The transition function.
-/
def f (b : S K₁ K₂ V) (T : Τ K₁ K₂ V) : S K₁ K₂ V :=
  ⟨
    λ k ↦
      have : InfSet V := infV b T k -- Grab the infimum. We know nothing about it, aside from
                                    -- the fact that it exists by virtue of some `f'` computing it.
                                    -- We _CANNOT_ look at `f'`.
      ⨅ x : boundedBelow b T, fc x.1 k,
    by rintro (k | k)
       · unfold iInf sInf infV; simp
         rw [if_pos V'_eq_range.symm]
         simp
       · simp
  ⟩

/--
`f` is the greatest lower bound of `V'`.
-/
lemma f_IsGLB_of_V' {b : S K₁ K₂ V} {T : Τ K₁ K₂ V} {k : Kbar K₁ K₂} :
  IsGLB (V' b T k) (f b T k) := by
  unfold f iInf sInf infV
  simp [V'_eq_range.symm]
  rcases exists_inf b T
  aesop

end f

section fStar

variable {s : S K₁ K₂ V}

def fStar (Ts : List (Τ K₁ K₂ V)) (s₀ : S K₁ K₂ V) : S K₁ K₂ V :=
  Ts.foldl f s₀

@[simp]
lemma fStar_nil : fStar [] s = s := by rfl

@[simp]
lemma fStar_cons {hd : Τ K₁ K₂ V} {tl : List (Τ K₁ K₂ V)} :
  fStar (hd :: tl) s = fStar tl (f s hd) := by rfl

end fStar

variable [Finite K₁] [Finite K₂] 

def Bal [LinearOrder K₁] [LinearOrder K₂]
  (π : BalanceProof K₁ K₂ C Pi V) (bs : List (Block K₁ K₂ C Sigma V)) : S K₁ K₂ V :=
  fStar (TransactionsInBlocks π bs) (.initial K₁ K₂ V)

end LGroup

end WithStructuredTypes

end Balance

end

end Intmax

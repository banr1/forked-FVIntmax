import Mathlib
import Mathlib.Algebra.Group.Int

import FVIntmax.BalanceProof
import FVIntmax.Block
import FVIntmax.Key
import FVIntmax.RollupContract
import FVIntmax.Wheels

import FVIntmax.Wheels.Dictionary

set_option autoImplicit false
set_option relaxedAutoImplicit false

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

/--
PAPER: complete transactions, consisting of the transactions
((s, r), v) ∈ T where v ̸= ⊥
-/
def Τ.isComplete (τ : Τ K₁ K₂ V) :=
  match τ with | (_, _, v) => v.isSome

/--
NB the notion of `isComplete` is here to keep 'parity' (for some loose definition thereof) with
the paper. The immediate `v.isSome` here is for the time being more convenient than `T.isComplete` here,
unless we happen to add a lot of lemmas with respect to `T.isComplete`, which I doubt will be the case.
-/
def Τ.isValid (τ : Τ K₁ K₂ V) [LE V] [OfNat V 0] :=
  match τ with
  | (s, r, v) => s ≠ r ∧ v.elim True (0 ≤ ·) ∧ s matches .Source → v.isSome 

/-
B.1 Step 1: Extracting a list of partial transaction
-/
section Extraction

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

/-
TODO(REVIEW):
PAPER FIX? -> for each sender-recipient pair (s, r) ∈ K2 × K where s ̸= r
-/
def keysUneq (k₂ : K₂) (k : Key K₁ K₂) : Prop :=
  match k with
  | .inl _   => True
  | .inr k₂' => k₂ ≠ k₂' 

infix:50 " ≠ₖ " => keysUneq 

@[deprecated]
instance [DecidableEq K₂] : DecidablePred (Function.uncurry (keysUneq (K₁ := K₁) (K₂ := K₂))) :=
  λ keys ↦
    by unfold Function.uncurry keysUneq
       rcases keys with ⟨_, _ | _⟩ <;> infer_instance

instance {k₂ : K₂} {k : Key K₁ K₂} [DecidableEq K₂] : Decidable (k₂ ≠ₖ k) := by
  unfold keysUneq
  cases k <;> infer_instance

/-
Sort will behave.
-/
section SortNotNaughty

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

end SortNotNaughty

noncomputable def TransactionsInBlock_transfer [Finite K₁] [Finite K₂] [AddZeroClass V]
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
      if s ∉ S then .some 0 else 
      if h : (commitment, s) ∈ π.keys
      then let (_, _, t) := π[(commitment, s)]
           t.lookup r
      else .none
    sorted.map λ (s, r) ↦ (s, r, v s r)
  | .deposit .. | .withdrawal .. => by aesop

end Transfer

section Withdrawal

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

noncomputable def TransactionsInBlock [Finite K₁] [Finite K₂] [AddZeroClass V] 
  (π : BalanceProof K₁ K₂ V C Pi) (b : Block K₁ K₂ C Sigma V) : List (Τ K₁ K₂ V) := 
  match h : b with
  | .deposit ..    => TransactionsInBlock_deposit ⟨b, by simp only [h]⟩
  | .transfer ..   => TransactionsInBlock_transfer π ⟨b, by simp only [h]⟩
  | .withdrawal .. => TransactionsInBlock_withdrawal ⟨b, by simp only [h]⟩

noncomputable def TransactionsInBlocks [Finite K₁] [Finite K₂] [AddZeroClass V] 
  (π : BalanceProof K₁ K₂ V C Pi) (bs : List (Block K₁ K₂ C Sigma V)) : List (Τ K₁ K₂ V) :=
  (bs.map (TransactionsInBlock π)).join

end Withdrawal

end Order

end Extraction

/-
B.2 Step 2: Computing balances from a list of partial transactions
-/
section Computation

/--
TODO(MY ESTEEMED SELF): Is this horrible dependent type going to come bite me in the behind?
Let's find out!
-/
@[deprecated]
def S' [OfNat V 0] [LE V] := Finmap (λ (k : Kbar K₁ K₂) ↦ { v : V // k matches .Source ∨ 0 ≤ v })

/--
TODO(REVIEW):
PAPER FIX? -> In our case, a state is an assignment of a balance to each account, where every
non-source account has a positive balance:
                         ^^^^^^^^ - I am guessing nonnegative? PAPER FIX? 
-/
abbrev S (K₁ K₂ V : Type) [OfNat V 0] [LE V] := Kbar K₁ K₂ → V

def S.isValid [OfNat V 0] [LE V] (s : S K₁ K₂ V) :=
  ∀ k : Kbar K₁ K₂, k matches .Source ∨ 0 ≤ s k

/--
PAPER: where the set of transactions is the subset Tc ⊆ T, called the complete transactions
-/
def Τc (K₁ K₂ V : Type) : Type := { τ : Τ K₁ K₂ V // τ.isComplete }

noncomputable def e (i : Kbar K₁ K₂) : Kbar K₁ K₂ → ℤ := λ j ↦ if i = j then 1 else 0

/-
We use the full lattice oredered ableian group structure with reckless abandon here.
There is technically still no need to for all the upcoming definitions
but we are at the core of the protocol and so might as well.
-/
section WithProperV

variable [Lattice V]
         [AddCommGroup V]
         [CovariantClass V V (· + ·) (· ≤ ·)]
         [CovariantClass V V (Function.swap (· + ·)) (· ≤ ·)]

def v' (v : V) (b : S K₁ K₂ V) (s : Kbar K₁ K₂) : V :=
  match s with
  | .Source => v
  | .key _  => v ⊓ b s

/--
TODO(REVIEW):
The subtraction is simple - we can subtract integers in their additive group.
The scalar multiplication (·•·) comes initially from the underlying `SubNegMonoid`, i.e.
> A `SubNegMonoid` is an `AddMonoid` with unary `-` and binary `-` operations
> satisfying `sub_eq_add_neg : ∀ a b, a - b = a + -b`.
This is kinda of a Mathlib artifact they use, but it looks to me that this is really just the 'fundamental'
multiplication by scalar in an additive monoid, a'la `k * V` is `V + V + ... + V` k times.
So there's not super-deep analysis necessary here, I.. think???? - use `ℤ`'s 0 and 1 as 'the'
two special elements and abuse the fact that multiplcation by scalar here is repeated addition. Done.
Not sure what the best way to express this algebraically is but Lean seems to accept this just fine.

Of course, we can pretend that we have this `Module ℤ G`, because any additive commutative group `G` can be spooned into
it; cf. the `_removeLater` below as a sanity check, but I am not sure reasoning along these lines is necessary.
-/
noncomputable def fc (τc : Τc K₁ K₂ V) (b : S K₁ K₂ V) : S K₁ K₂ V :=
  have _removeLater : Module ℤ V := inferInstance
  λ k : Kbar K₁ K₂ ↦
    match τc with
    | ⟨⟨s, r, v⟩, hτ⟩ =>
      let v' := v' (v.get hτ) b s
      b k + (e r - e s) k • v'

/-
NB Lean's `Preorder` class has an addition requirement on how it expects `<` to be defined,
which we don't want with the discrete preorder.

`lt_iff_le_not_le : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl`

Note that if `≤ := =`, we have `∀ a b : α, a < b ↔ a = b ∧ ¬b = a`, where `a < b → False` is not provable.
We use `IsPreoder (·≤·)` instead.
-/
section Order

/--
PAPER: We first equip K2 with the discrete preorder.
-/
instance : LE (Kbar K₁ K₂) := ⟨(·=·)⟩

instance : Preorder (Kbar K₁ K₂) where
  le_refl := Eq.refl
  le_trans := λ _ _ _ ↦ Eq.trans

instance : Preorder (Kbar K₁ K₂ × Kbar K₁ K₂) := inferInstance

/--
PAPER: Then we equip V+ with the discrete preorder.
-/
instance (priority := high) : LE { v : V // 0 ≤ v } := ⟨(·=·)⟩
instance (priority := high) : LT { v : V // 0 ≤ v } := ⟨λ a b ↦ a ≤ b ∧ ¬ b ≤ a⟩ -- 😈

/--
High priority is imperative if we want Lean to pick this one up consistently.
Note that Lean already has `[Preorder α] (p : α → Prop) : Preorder (Subtype p)`, but we want ours.
-/
instance (priority := high) : Preorder { v : V // 0 ≤ v } where
  le_refl := Eq.refl
  le_trans := λ _ _ _ ↦ Eq.trans

/--
Definition 15
Let (X, ≤X) be a proset. We define the induced preorder ≤ on
Maybe(X) where for all x, y ∈ M aybe(X) we have
x ≤ y ⇔ x = ⊥ ∨ (x, y ∈ X ∧ x ≤X y)
-/
instance (priority := high) {α : Type} [Preorder α] : Preorder (Option α) :=
  let le : Option α → Option α → Prop := λ x y ↦
                                           match x, y with
                                           | .none, .none | .none, .some _ => True
                                           | .some x, .some y => x ≤ y
                                           | .some _, .none   => False
  {
    le := le
    lt := λ a b ↦ le a b ∧ ¬ le b a
    le_refl := by dsimp [le]; aesop
    le_trans := by dsimp [le, (·≤·)]; aesop (add safe forward le_trans)
  }

/--
PAPER: which induces a preorder on Maybe(V+)

NB This gives us `Option.lt` which happens to coincide with PAPER: Definition 15.
-/
instance : Preorder (Option { v : V // 0 ≤ v }) := inferInstance

/--
PAPER: We then get the induced product preorder on K2 × Maybe(V+)
-/
instance : Preorder (Kbar K₁ K₂ × Kbar K₁ K₂ × Option V) := inferInstance

/--
PAPER: and an induced subset preorder on the subset T
-/
instance : IsPreorder (Τ K₁ K₂ V) (·≤·) := inferInstance

/--
PAPER: To get the preorder on S = V K, we use the underlying preorder on V coming from the fact that V is a lattice
-/
instance : Preorder V := inferInstance

/--
PAPER: and give S the subset preorder
-/
instance : Preorder (S K₁ K₂ V) := inferInstance

-- instance : IsPreorder (Kbar K₁ K₂) (·≤·) where
--   refl := Eq.refl
--   trans := λ _ _ _ ↦ Eq.trans

-- instance : IsPreorder (Kbar K₁ K₂ × Kbar K₁ K₂) (·≤·) where
--   refl := by simp [(·≤·)]
--   trans := by dsimp [(·≤·)]; aesop

-- /--
-- PAPER: Then we equip V+ with the discrete preorder.
-- -/
-- instance : LE V := ⟨(·=·)⟩

-- instance : IsPreorder V (·≤·) where
--   refl := Eq.refl
--   trans := λ _ _ _ ↦ Eq.trans

-- /--
-- PAPER: which induces a preorder on M aybe(V+)
-- -/
-- instance : IsPreorder (Option V) (·≤·) where

-- /--
-- PAPER: We then get the induced product preorder on K2 × M aybe(V+)
-- -/
-- instance : IsPreorder (Kbar K₁ K₂ × Kbar K₁ K₂ × Option V) (·≤·) where
--   refl := by simp [(·≤·)]
--   trans := by dsimp [(·≤·)]; aesop

-- /--
-- PAPER: and an induced subset preorder on the subset T
-- -/
-- instance : IsPreorder (Τ K₁ K₂ V) (·≤·) := inferInstance

-- /--
-- PAPER: To get the preorder on S = V K, we use the underlying preorder on V coming from the fact that V is a lattice
-- -/
-- instance : Preorder V := inferInstance
-- instance : IsPreorder V (·≤·) := inferInstance


end Order

end WithProperV

end Computation

end Balance

end Intmax

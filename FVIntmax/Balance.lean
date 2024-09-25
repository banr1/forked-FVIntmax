import Mathlib
import Mathlib.Algebra.Group.Int

import FVIntmax.BalanceProof
import FVIntmax.Block
import FVIntmax.Key
import FVIntmax.RollupContract
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

variable {Pi : Type}
         {K₁ : Type}
         {K₂ : Type}
         {V : Type}
         {C Sigma : Type}

/--
PAPER: Formally, let K := K1 ⨿ K2 ⨿ {Source}
-/
inductive Kbar (K₁ K₂ : Type) where
  | key (k : Key K₁ K₂)
  | Source
deriving DecidableEq

instance : Coe (Key K₁ K₂) (Kbar K₁ K₂) := ⟨.key⟩

/--
NB not important. There's an obvious equivalence between the inductive `Kbar` and the
`Key K₁ K₂ ⊕ Unit` sum, for which Lean knows how to infer things.
I prefer the wrapped inductive.
-/
def univKbar : Kbar K₁ K₂ ≃ Key K₁ K₂ ⊕ Unit :=
  {
    toFun := λ kbar ↦ match kbar with | .key k => k | .Source => ()
    invFun := λ sum ↦ match sum with | .inl k => .key k | .inr _ => .Source
    left_inv := by simp [Function.LeftInverse]; aesop
    right_inv := by simp [Function.RightInverse, Function.LeftInverse]
  }

instance [Finite K₁] [Finite K₂] : Finite (Kbar K₁ K₂ : Type) :=
  Finite.of_equiv _ univKbar.symm
  
/--
NB we use Lean's natural associativity for products to get some freebies.
As such, our tuples are technically `(a, (b, c))` here. Obviously, this is associative
so not much changes.
-/
abbrev Τ (K₁ K₂ V : Type) [Nonnegative V] := Kbar K₁ K₂ × Kbar K₁ K₂ × Option V₊

instance [Finite V] : Fintype V := Fintype.ofFinite _

namespace Τ

variable [Nonnegative V]
         {v? : Option V₊}
         {k₁ : K₁} {k₂ : K₂}
         {kb kb₁ kb₂ : Kbar K₁ K₂}
         {τ : Τ K₁ K₂ V}

section IsValid

def isValid (τ : Τ K₁ K₂ V) :=
  match τ with
  | (s, r, v) => s ≠ r ∧ (s matches .Source → v.isSome)

lemma isValid_iff {s r : Kbar K₁ K₂} {v : Option V₊} :
  Τ.isValid (s, r, v) ↔ s ≠ r ∧ (s matches .Source → v.isSome) := by rfl

/--
PAPER: complete transactions, consisting of the transactions
((s, r), v) ∈ T where v ̸= ⊥
-/
def isComplete (τ : Τ K₁ K₂ V) :=
  τ.isValid ∧ match τ with | (_, _, v) => v.isSome

lemma isSome_of_complete (h : Τ.isComplete ⟨kb₁, kb₂, v?⟩) : v?.isSome := by
  unfold Τ.isComplete at h; rw [Τ.isValid_iff] at h
  aesop

lemma s_ne_r_of_complete (h : Τ.isComplete ⟨kb₁, kb₂, v?⟩) : kb₁ ≠ kb₂ := by
  unfold Τ.isComplete at h; rw [Τ.isValid_iff] at h
  aesop

end IsValid

end Τ

/-
B.1 Step 1: Extracting a list of partial transaction
-/
section Extraction

open Lean Elab Tactic in
/--
`choose_leg h in h₁ with b → b p` discharges impossible cases in the `TransactionsInBlock_<X>` functions.
-/
scoped elab "choose_leg" h:ident "in" h₁:ident "with" b:ident "→" w:ident ws p:ident : tactic => do
  evalTactic <| ← `(tactic| (
    rcases $b:ident with ⟨$w, $p⟩
    dsimp [$h:ident] at $h₁:ident
    split at $h₁:ident <;> try { simp at $p:ident }
  ))

section Deposit

def TransactionsInBlock_deposit [Nonnegative V]
  (b : { b : Block K₁ K₂ C Sigma V // b.isDepositBlock }) : List (Τ K₁ K₂ V) :=
  match h : b.1 with
  | .deposit r v => [(.Source, r, v)]
  | .withdrawal .. | .transfer .. => by aesop

/--
Shows that `TransactionsInBlock_deposit b ∈ { τ : Τ K₁ K₂ V // τ.isValid }`.
-/
lemma isValid_TransactionsInBlock_deposit [Nonnegative V]
  {b : { b : Block K₁ K₂ C Sigma V // b.isDepositBlock }} {τ : Τ K₁ K₂ V}
  (hτ : τ ∈ TransactionsInBlock_deposit b) : τ.isValid := by
  choose_leg TransactionsInBlock_deposit in hτ with b → b hb
  /-
    NB I try to set things up in a manner such that `aesop` can either close everything by itself
    or with my explicitly stating some juicy bits.
  -/
  rw [Τ.isValid_iff]; aesop

end Deposit

section Order

variable [LinearOrder K₁] [LinearOrder K₂]

def lexLe (a b : K₂ × Key K₁ K₂) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

instance : DecidableRel (lexLe (K₁ := K₁) (K₂ := K₂)) :=
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

local infix:50 " ≠ₖ " => keysUneq 

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

def TransactionsInBlock_transfer [Finite K₁] [Finite K₂] [Nonnegative V]
  (π : BalanceProof K₁ K₂ C Pi V)
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
    let v (s : K₂) (r : Key K₁ K₂) : Option V₊ :=
      if s ∉ S then .some 0 else 
      if h : (commitment, s) ∈ π.keys
      then let (_, _, t) := π[(commitment, s)]
           t.lookup r
      else .none
    sorted.map λ (s, r) ↦ (s, r, v s r)
  | .deposit .. | .withdrawal .. => by aesop

/--
Shows that `TransactionsInBlock_transfer π b ∈ { τ : Τ K₁ K₂ V // τ.isValid }`.
-/
lemma isValid_TransactionsInBlock_transfer [Finite K₁] [Finite K₂] [Nonnegative V]
  {π : BalanceProof K₁ K₂ C Pi V}
  {b : { b : Block K₁ K₂ C Sigma V // b.isTransferBlock }} :
  ∀ τ ∈ TransactionsInBlock_transfer π b, τ.isValid := λ τ hτ ↦ by
  choose_leg TransactionsInBlock_transfer in hτ with b → b hb
  rw [Τ.isValid_iff]; aesop

end Transfer

section Withdrawal

/--
TODO(REVIEW):
> Given a withdrawal block, the list of transactions extracted from it consists of
  a transaction from each L1 account to the source account in order:
-/
def TransactionsInBlock_withdrawal [Finite K₁] [Zero V] [Preorder V]
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

omit [LinearOrder K₂] in
lemma isValid_TransactionsInBlock_withdrawal [Finite K₁] [Zero V] [Preorder V]
  {b : { b : Block K₁ K₂ C Sigma V // b.isWithdrawalBlock }} :
  ∀ τ ∈ TransactionsInBlock_withdrawal b, τ.isValid := λ τ hτ ↦ by
  choose_leg TransactionsInBlock_withdrawal in hτ with b → b hb
  rw [Τ.isValid_iff]; aesop

def TransactionsInBlock [Finite K₁] [Finite K₂] [AddZeroClass V] [Zero V] [Preorder V]
  (π : BalanceProof K₁ K₂ C Pi V) (b : Block K₁ K₂ C Sigma V) : List (Τ K₁ K₂ V) := 
  match h : b with
  | .deposit ..    => TransactionsInBlock_deposit ⟨b, by simp only [h]⟩
  | .transfer ..   => TransactionsInBlock_transfer π ⟨b, by simp only [h]⟩
  | .withdrawal .. => TransactionsInBlock_withdrawal ⟨b, by simp only [h]⟩
  
lemma isValid_TransactionsInBlock [Finite K₁] [Finite K₂] [AddZeroClass V] [Zero V] [Preorder V]
  {π : BalanceProof K₁ K₂ C Pi V} {b : Block K₁ K₂ C Sigma V} :
  ∀ τ ∈ TransactionsInBlock π b, τ.isValid := λ τ hτ ↦ by
  unfold TransactionsInBlock at hτ
  rcases b <;> [apply isValid_TransactionsInBlock_deposit;
                apply isValid_TransactionsInBlock_transfer;
                apply isValid_TransactionsInBlock_withdrawal]
  all_goals aesop

def TransactionsInBlocks [Finite K₁] [Finite K₂] [AddZeroClass V] [Zero V] [Preorder V]
  (π : BalanceProof K₁ K₂ C Pi V) (bs : List (Block K₁ K₂ C Sigma V)) : List (Τ K₁ K₂ V) :=
  (bs.map (TransactionsInBlock π)).join

lemma isValid_TransactionsInBlocks [Finite K₁] [Finite K₂] [AddZeroClass V] [Zero V] [Preorder V]
  {π : BalanceProof K₁ K₂ C Pi V} {bs : List (Block K₁ K₂ C Sigma V)} :
  ∀ τ ∈ TransactionsInBlocks π bs, τ.isValid := λ τ hτ ↦ by
  simp only [TransactionsInBlocks, List.mem_join, List.mem_map, exists_exists_and_eq_and] at hτ
  rcases hτ with ⟨τ, hτ⟩
  exact isValid_TransactionsInBlock _ hτ.2

end Withdrawal

end Order

end Extraction

/-
B.2 Step 2: Computing balances from a list of partial transactions
-/
section Computation

section S

variable [Preorder V] [Zero V]

/--
TODO(MY ESTEEMED SELF): Is this horrible dependent type going to come bite me in the behind?
Let's find out!
-/
@[deprecated]
def S' := Finmap (λ (k : Kbar K₁ K₂) ↦ { v : V // k matches .Source ∨ 0 ≤ v })

/--
TODO(REVIEW):
PAPER FIX? -> In our case, a state is an assignment of a balance to each account, where every
non-source account has a positive balance:
                         ^^^^^^^^ - I am guessing nonnegative? PAPER FIX? 
-/
abbrev S (K₁ K₂ V : Type) := Kbar K₁ K₂ → V

def S.isValid (s : S K₁ K₂ V) := ∀ k : Kbar K₁ K₂, k matches .Source ∨ 0 ≤ s k

def S.initial (K₁ K₂ V : Type) [Zero V] : S K₁ K₂ V := λ _ ↦ 0

lemma S.isValid_initial : (S.initial K₁ K₂ V).isValid := by
  unfold initial isValid; aesop

def S.validInitial (K₁ K₂ V : Type) [Preorder V] [Zero V] : { s : S K₁ K₂ V // s.isValid } :=
  ⟨S.initial K₁ K₂ V, S.isValid_initial⟩

lemma S.nonneg_key_of_isValid {b : S K₁ K₂ V} {k} (h : b.isValid) : 0 ≤ b (.key k) := by
  unfold S.isValid at h
  specialize h k
  aesop

/--
The infimum of valid values is valid.
-/
lemma isValid_inf_of_valid {V : Type} [CompleteLattice V] [AddCommGroup V]
                           {α : Type} {s : Set α} {f : α → S K₁ K₂ V}
                           (h : ∀ (a : α), (f a).isValid) : (⨅ x ∈ s, f x).isValid := by
  rintro (k | _)
  · simp; intros _ _
    exact S.nonneg_key_of_isValid (h _)
  · simp

end S

instance [Finite K₁] [Finite K₂] [Finite V] [Zero V] [Preorder V] : Finite (S K₁ K₂ V) := inferInstance 

/--
PAPER: where the set of transactions is the subset Tc ⊆ T, called the complete transactions
-/
abbrev Τc (K₁ K₂ V : Type) [Zero V] [Preorder V] : Type := { τ : Τ K₁ K₂ V // τ.isComplete }

/--
And the obvious lift from `Τ.isComplete` to `Τ.isValid` to make Lean happy.
-/
instance [Zero V] [Preorder V] : Coe (Τc K₁ K₂ V) { τ : Τ K₁ K₂ V // τ.isValid } := ⟨λ x ↦ ⟨x.1, x.2.1⟩⟩

def e (i : Kbar K₁ K₂) : Kbar K₁ K₂ → ℤ := λ j ↦ if i = j then 1 else 0

@[simp]
lemma e_def {i : Kbar K₁ K₂} : e i = λ j ↦ if i = j then 1 else 0 := rfl

lemma nonneg_e {i j : Kbar K₁ K₂} : 0 ≤ e i j := by unfold e; aesop

/-
We use the full lattice oredered ableian group structure with reckless abandon here.
There is technically still no need to for all the upcoming definitions
but we are at the core of the protocol and so might as well.
-/
section WithStructuredTypes

-- /-
-- TODO(REVIEW):
-- Given they're doing the big meet, I think the paper can say the lattice is complete, and implify [Finite V] anyway?
-- -/
-- variable [LinearOrder K₁]
--          [LinearOrder K₂]
--          [CompleteLattice V]
--          [AddCommGroup V]
--         

section v'

variable [Zero V] [CompleteLattice V]

def v' (v : V₊) (b : S K₁ K₂ V) (s : Kbar K₁ K₂) : V :=
  match s with
  | .Source => v
  | .key _  => v ⊓ b s

variable {v : V₊} {b : S K₁ K₂ V} {s : Kbar K₁ K₂}

lemma v'_nonneg_of_valid (h : b.isValid) : 0 ≤ v' v b s := by
  unfold v'
  rcases s with k | _ <;> aesop (add simp S.nonneg_key_of_isValid)

@[simp]
lemma v'_source_eq_v : v' v b .Source = v := by unfold v'; aesop

@[simp]
lemma v'_key_eq_meet {k : Key K₁ K₂} : v' v b (Kbar.key k) = v.1 ⊓ b k := by unfold v'; aesop

end v'

variable [CompleteLattice V]
         [AddCommGroup V]
         [CovariantClass V V (· + ·) (· ≤ ·)]
         [CovariantClass V V (Function.swap (· + ·)) (· ≤ ·)]

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
def fc (τc : Τc K₁ K₂ V) (b : S K₁ K₂ V) : S K₁ K₂ V :=
  -- have _removeLater : Module ℤ V := inferInstance
  λ k : Kbar K₁ K₂ ↦
    match τc with
    | ⟨⟨s, r, v⟩, hτ⟩ =>
      let v' := v' (v.get hτ.2) b s
      b k + (e r - e s) k • v'

/--
The transition function for complete transactions leaves every nonsource actor with nonnegative balance.
-/
lemma isValid_fc {τc : Τc K₁ K₂ V} {b : S K₁ K₂ V} (h : b.isValid) : (fc τc b).isValid := by
  /-
    `h` yields both `0 ≤ b ..` and `0 ≤ v' ..`.
  -/
  unfold fc
  rintro (k | _) <;> [skip; aesop]
  have eq₁ : 0 ≤ b (Kbar.key k) := S.nonneg_key_of_isValid h
  have eq₂ : 0 ≤ v' (τc.1.2.2.get τc.2.2) b τc.1.1 := v'_nonneg_of_valid h
  /-
    I try to set things up in a manner such that `aesop` can close everything once the juicy bits
    of proofs are made explicit.
  -/
  aesop (add simp (le_add_of_le_of_nonneg eq₁ eq₂))

/-
NB Lean's `Preorder` class has an addition requirement on how it expects `<` to be defined,
We'll use `False` stated as `a ≤ b ∧ ¬ b ≤ a`. Don't worry about it :).
-/
section Order

/--
PAPER: We first equip K2 with the discrete preorder.
-/
instance (priority := high) : LE (Kbar K₁ K₂) := ⟨(·=·)⟩

instance : Preorder (Kbar K₁ K₂) where
  le_refl := Eq.refl
  le_trans := λ _ _ _ ↦ Eq.trans

instance : Preorder (Kbar K₁ K₂ × Kbar K₁ K₂) := inferInstance

/--
PAPER: Then we equip V+ with the discrete preorder.
-/
instance (priority := high) : LE V₊ := ⟨(·=·)⟩
instance (priority := high) : LT V₊ := ⟨λ a b ↦ a ≤ b ∧ ¬ b ≤ a⟩ -- 😈 (NB this is `False`)

/--
High priority is imperative if we want Lean to pick this one up consistently.
Note that Lean already has `[Preorder α] (p : α → Prop) : Preorder (Subtype p)`, but we want ours.
-/
instance (priority := high) : Preorder V₊ where
  le_refl := Eq.refl
  le_trans := λ _ _ _ ↦ Eq.trans

/--
Definition 15
Let (X, ≤X) be a proset. We define the induced preorder ≤ on
Maybe(X) where for all x, y ∈ M aybe(X) we have
x ≤ y ⇔ x = ⊥ ∨ (x, y ∈ X ∧ x ≤X y)

NB whatever you do, do NOT remove the priority from the instance.
-/
instance (priority := high) maybeInduced {α : Type} [Preorder α] : Preorder (Option α) :=
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

NB the default behaviour is iso with the Definition 18. (cf. `Preorder.lift`)
-/
instance : Preorder { τ : Τ K₁ K₂ V // τ.isValid } := inferInstance

/--
PAPER: we use the underlying preorder on V coming from the fact that V is a lattice

NB the default behaviour is the lattice-induced preorder. (cf. `PartialOrder.toPreorder`)
-/
instance : Preorder V := inferInstance

/--
PAPER: and give S the subset preorder

NB the default behaviour is iso with the Definition 18. (cf. `Preorder.lift`)
NB the default behaviour to find the preorder for the underlying function is iso with 
Definition 16. (cf. `Pi.le_def`)
-/
instance : Preorder { s : S K₁ K₂ V // s.isValid } := inferInstance

/--
PAPER: Given these preorders on T and S, we get an induced product preorder on T × S

NB the default behavviour is iso with the Definition 19. (cf. `Prod.mk_le_mk`)
-/
instance : Preorder ({ τ : Τ K₁ K₂ V // τ.isValid } × { s : S K₁ K₂ V // s.isValid }) := inferInstance

section Plumbing

variable [Finite K₁] [Finite K₂] [Finite V]

/--
Noncomputable Fintype might seem strange but `Fintyp` fits better in Lean's hierarchy and removes
a bit of friction when converting to finset.

NB the current setup is such that this is unnecessary, will likely remove.
-/
@[deprecated]
noncomputable instance : Fintype (Τ K₁ K₂ V) := Fintype.ofFinite _
@[deprecated]
noncomputable instance : Fintype (Τc K₁ K₂ V) := Fintype.ofFinite _
@[deprecated]
noncomputable instance : Fintype { s : S K₁ K₂ V // s.isValid } := Fintype.ofFinite _

end Plumbing

end Order

variable [LinearOrder K₁] [LinearOrder K₂] [Finite K₁] [Finite K₂]

/--
NB might be subject to change, I'd rather prove the subset properties post facto, just want to make sure
that the orders we get here are appropriate.
-/
def f (b : { s : S K₁ K₂ V // s.isValid })
      (T : { τ : Τ K₁ K₂ V // τ.isValid }) : { s : S K₁ K₂ V // s.isValid } :=
  let univ := { (T', b') | (T' : Τc K₁ K₂ V) (b' : { s : S K₁ K₂ V // s.isValid }) (_h : (T, b) ≤ (↑T', b')) }
  ⟨
    ⨅ x ∈ univ, fc x.1 x.2,
    isValid_inf_of_valid (isValid_fc ·.2.2)
  ⟩

noncomputable def fStar (Ts : List { τ : Τ K₁ K₂ V // τ.isValid })
                        (s₀ : { s : S K₁ K₂ V // s.isValid }) : { s : S K₁ K₂ V // s.isValid } :=
  Ts.foldl f s₀

def Bal (π : BalanceProof K₁ K₂ C Pi V) (bs : List (Block K₁ K₂ C Sigma V)) : { s : S K₁ K₂ V // s.isValid } :=
  fStar ((TransactionsInBlocks π bs).attach.map (λ x ↦ ⟨x.1, isValid_TransactionsInBlocks _ x.2⟩)) (S.validInitial ..)

end WithStructuredTypes

end Computation

end Balance

end

end Intmax

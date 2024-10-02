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
NB this formalisation is structured specifically to enable `simp`/`aesop` to resolve most proof obligations,
possibly with my explicitly articulating proof structure / important invariants apriori.

The proof that `fc` produces values in the appropriate subset is pretty sweet if you ask me.
-/

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
abbrev Τ' (K₁ K₂ V : Type) [Nonnegative V] := Kbar K₁ K₂ × Kbar K₁ K₂ × Option V₊

namespace Τ'

variable [Nonnegative V]

section IsValid

def isValid (τ : Τ' K₁ K₂ V) :=
  match τ with
  | (s, r, v) => s ≠ r ∧ (s matches .Source → v.isSome)

lemma isValid_iff {s r : Kbar K₁ K₂} {v? : Option V₊} :
  isValid (s, r, v?) ↔ s ≠ r ∧ (s matches .Source → v?.isSome) := by rfl

end IsValid

end Τ'

abbrev Τ (K₁ K₂ V : Type) [Nonnegative V] := { τ : Τ' K₁ K₂ V // τ.isValid }

namespace Τ

section Τ

variable [Nonnegative V]
         {v : V₊}
         {v? : Option V₊}
         {kb₁ kb₂ : Kbar K₁ K₂}
         {τ : Τ K₁ K₂ V}

/--
PAPER: complete transactions, consisting of the transactions
((s, r), v) ∈ T where v ̸= ⊥
-/
def isComplete (τ : Τ K₁ K₂ V) :=
  match τ with | ⟨(_, _, v), _⟩ => v.isSome

lemma isSome_of_complete {t'} (h : isComplete ⟨⟨kb₁, kb₂, v?⟩, t'⟩) : v?.isSome := by
  unfold isComplete at h; aesop

lemma s_ne_r_of_complete {t'} (h : isComplete ⟨⟨kb₁, kb₂, v?⟩, t'⟩) : kb₁ ≠ kb₂ := by
  unfold isComplete at h; rw [Τ'.isValid_iff] at t'
  aesop

@[simp]
lemma isComplete_some {t'} : isComplete ⟨⟨kb₁, kb₂, .some v⟩, t'⟩ := rfl

def isSourceSender (τ : Τ K₁ K₂ V) := τ.1.1 matches .Source

def isKeySender (τ : Τ K₁ K₂ V) := τ.1.1 matches .key _

end Τ

end Τ

/-
B.1 Step 1: Extracting a list of partial transaction
-/
section Extraction

section Deposit

def TransactionsInBlock_deposit [Nonnegative V]
  (b : { b : Block K₁ K₂ C Sigma V // b.isDepositBlock }) : List (Τ K₁ K₂ V) :=
  match h : b.1 with
  | .deposit r v => [⟨(.Source, r, v), by rw [Τ'.isValid_iff]; aesop⟩]
  | .withdrawal .. | .transfer .. => by aesop

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

NB this is an abbrev for `aesop` to extract the obvious invariants.
-/
abbrev keysUneq (k₂ : K₂) (k : Key K₁ K₂) : Prop :=
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
  (π : BalanceProof K₁ K₂ C Pi V) (b : { b : Block K₁ K₂ C Sigma V // b.isTransferBlock }) : List (Τ K₁ K₂ V) :=
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

      NB subject to being hoisted out of this function.
    -/
    let v (s : K₂) (r : Key K₁ K₂) : Option V₊ :=
      if s ∉ S then .some 0 else 
      if h : (commitment, s) ∈ π.keys
      then let (_, _, t) := π[(commitment, s)]
           t.lookup r
      else .none
    sorted.attach.map λ ⟨(s, r), h⟩ ↦ ⟨(s, r, v s r), by rw [Τ'.isValid_iff]; aesop⟩
  | .deposit .. | .withdrawal .. => by aesop

end Transfer

section Withdrawal

/--
TODO(REVIEW):
> Given a withdrawal block, the list of transactions extracted from it consists of
  a transaction from each L1 account to the source account in order:
-/
def TransactionsInBlock_withdrawal [Finite K₁] [Nonnegative V]
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
    k₁InOrder.attach.map λ s : K₁ ↦ ⟨(s, .Source, withdrawals.lookup s), by rw [Τ'.isValid_iff]; aesop⟩
  | .deposit r v | .transfer .. => by aesop
end Withdrawal

end Order

variable [Finite K₁] [LinearOrder K₁]
         [Finite K₂] [LinearOrder K₂]
         [Nonnegative V]

local macro:max (priority := high) "↪" b:term : term => `(⟨$b, by aesop⟩)

def TransactionsInBlock (π : BalanceProof K₁ K₂ C Pi V) (b : Block K₁ K₂ C Sigma V) : List (Τ K₁ K₂ V) := 
  match h : b with
  | .deposit ..    => TransactionsInBlock_deposit ↪b
  | .transfer ..   => TransactionsInBlock_transfer π ↪b
  | .withdrawal .. => TransactionsInBlock_withdrawal ↪b

def TransactionsInBlocks
  (π : BalanceProof K₁ K₂ C Pi V) (bs : List (Block K₁ K₂ C Sigma V)) : List (Τ K₁ K₂ V) :=
  (bs.map (TransactionsInBlock π)).join

end Extraction

/-
B.2 Step 2: Computing balances from a list of partial transactions
-/
section Computation

section S

variable [Nonnegative V]

lemma zero_le_val_subtype_of_le {P : V → Prop} (h : 0 ≤ v) (h : P v) :
  (0 : V) ≤ (Subtype.mk v h).1 := by aesop

/--
TODO(REVIEW):
PAPER FIX? -> In our case, a state is an assignment of a balance to each account, where every
non-source account has a positive balance:
                         ^^^^^^^^ - I am guessing nonnegative? PAPER FIX? 
-/
abbrev S' (K₁ K₂ V : Type) := Kbar K₁ K₂ → V

namespace S'

def isValid (s : S' K₁ K₂ V) := ∀ k : Kbar K₁ K₂, k matches .Source ∨ 0 ≤ s k

def initial (K₁ K₂ V : Type) [Zero V] : S' K₁ K₂ V := λ _ ↦ 0

lemma isValid_initial : (initial K₁ K₂ V).isValid := by
  unfold initial isValid; aesop

@[aesop safe apply]
lemma nonneg_key_of_isValid {b : S' K₁ K₂ V} {k} (h : b.isValid) : 0 ≤ b (.key k) := by
  unfold isValid at h
  specialize h k
  aesop

end S'

instance : Inhabited (S' K₁ K₂ V) := ⟨S'.initial K₁ K₂ V⟩

abbrev S (K₁ K₂ V : Type) [Nonnegative V] := { s : S' K₁ K₂ V // s.isValid }

-- abbrev V? (k : Kbar K₁ K₂) : Type :=
--   match k with
--   | .Source => V
--   | .key  _ => V₊

instance : CoeFun (S K₁ K₂ V) λ _ ↦ Kbar K₁ K₂ → V :=
  ⟨λ s k ↦ s.1 k⟩

namespace S

def initial (K₁ K₂ V : Type) [Nonnegative V] : S K₁ K₂ V :=
  ⟨S'.initial K₁ K₂ V, S'.isValid_initial⟩

@[simp]
lemma nonneg {s : S K₁ K₂ V} {k : Key K₁ K₂} : 0 ≤ s k := by
  aesop

@[simp]
lemma isValid_coe {s : S K₁ K₂ V} : S'.isValid (V := V) (K₁ := K₁) (K₂ := K₂) ↑s := by
  rintro (k | k) <;> aesop

@[simp]
lemma nonneg_coe {s : S K₁ K₂ V} {k : Key K₁ K₂} : 0 ≤ (↑s : S' K₁ K₂ V) k := by
  aesop

-- lemma isValid_inf_of_valid {V : Type} [AddCommGroup V] [Nonnegative V]
--                            {α : Type} {f : α → S' K₁ K₂ V}
--                            (h : ∀ x, (f x).isValid) : (⨅ x : α, f x).isValid := by sorry
  -- rintro (k | _)
  -- · simp
  --   unfold S' at *
  --   unfold S'.isValid at h
  --   have : (x : Kbar K₁ K₂) → InfSet V := sorry
  --   rw [@iInf_apply _ _ _ this f (Kbar.key k)]
  --   simp [iInf_apply]
  --   rw [iInf_apply]
  --   done
    
    
  --   -- simp
  --   -- apply S'.nonneg_key_of_isValid
  --   -- unfold S'.isValid at *
  --   -- aesop
  -- · simp

end S

end S

instance [Nonnegative V] : Inhabited (S K₁ K₂ V) := ⟨S.initial K₁ K₂ V⟩

/--
PAPER: where the set of transactions is the subset Tc ⊆ T, called the complete transactions
-/
abbrev Τc (K₁ K₂ V : Type) [Nonnegative V] : Type := { τ : Τ K₁ K₂ V // τ.isComplete }

namespace Τc

section Τc

variable {K₁ K₂ V : Type} [Nonnegative V]
         

def isSourceSender (τc : Τc K₁ K₂ V) := τc.1.isSourceSender

def isKeySender (τc : Τc K₁ K₂ V) := τc.1.isKeySender

end Τc

end Τc

/--
And the obvious lift from `Τ.isComplete` to `Τ.isValid` to make Lean happy.
-/
instance [Nonnegative V] : Coe (Τc K₁ K₂ V) (Τ K₁ K₂ V) := ⟨(↑·)⟩

def e (i : Kbar K₁ K₂) : Kbar K₁ K₂ → ℤ := λ j ↦ if i = j then 1 else 0

/--
The interface to `e` is just its definition. Normalise in this manner.
-/
@[simp]
lemma e_def {i : Kbar K₁ K₂} : e i = λ j ↦ if i = j then 1 else 0 := rfl

lemma nonneg_e {i j : Kbar K₁ K₂} : 0 ≤ e i j := by unfold e; aesop

/-
We use the full lattice oredered ableian group structure with reckless abandon here.
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

end v'

variable [Lattice V]
         [AddCommGroup V]
         [CovariantClass V V (· + ·) (· ≤ ·)]
         [CovariantClass V V (Function.swap (· + ·)) (· ≤ ·)]

/--
TODO(REVIEW):
The subtraction is simple - we can subtract integers in their additive group.
The scalar multiplication (·•·) comes initially from the underlying `SubNegMonoid`, i.e.
> A `SubNegMonoid` is an `AddMonoid` with unary `-` and binary `-` operations
> satisfying `sub_eq_add_neg : ∀ a b, a - b = a + -b`.
This is kind of a Mathlib artifact they use, but it looks to me that this is really just the 'fundamental'
multiplication by scalar in an additive monoid, a'la `k * V` is `V + V + ... + V` k times.
So there's not super-deep analysis necessary here, I.. think???? - use `ℤ`'s 0 and 1 as 'the'
two special elements and abuse the fact that multiplcation by scalar here is repeated addition.
Change + to - as per `sub_eq_add_neg` if need be. Done.
Not sure what the best way to express this algebraically is but Lean seems to accept this just fine.

Of course, we can pretend that we have this `Module ℤ G`, because any additive commutative group `G` can be spooned into
it; cf. the `_removeLater` below as a sanity check, but I am not sure reasoning along these lines is necessary.
-/
def fc (τcXb : Τc K₁ K₂ V × S K₁ K₂ V) : S K₁ K₂ V :=
  -- have _removeLater : Module ℤ V := inferInstance
  ⟨λ k : Kbar K₁ K₂ ↦
    match τcXb with
    | ⟨⟨⟨⟨s, r, v⟩, _⟩, hτ⟩, b⟩ =>
      let v' := v' (v.get hτ) b s
      b k + (e r - e s) k • v',
  by rintro (k | _) <;>
     aesop (add unsafe apply le_add_of_le_of_nonneg)
  ⟩

@[simp]
lemma fc_key {τc : Τc K₁ K₂ V} {b : S K₁ K₂ V} :
  0 ≤ fc (τc, b) (.key k) := by simp

/-
NB Lean's `Preorder` class has an addition requirement on how it expects `<` to be defined,
We'll use `False` stated as `a ≤ b ∧ ¬ b ≤ a`. Don't worry about it :).
-/
section Order

def discretePreorder {α : Type} : Preorder α :=
  {
    lt := λ _ _ ↦ False
    le := (·=·)
    le_refl := Eq.refl
    le_trans := λ _ _ _ ↦ Eq.trans
    lt_iff_le_not_le := by aesop
  }

/--
PAPER: We first equip K2 with the discrete preorder.
-/
instance (priority := high) : LE (Kbar K₁ K₂) := ⟨(·=·)⟩

instance : Preorder (Kbar K₁ K₂) where
  le_refl := Eq.refl
  le_trans := λ _ _ _ ↦ Eq.trans

instance : Preorder (Kbar K₁ K₂ × Kbar K₁ K₂) := inferInstance

-- /--
-- PAPER: Then we equip V+ with the discrete preorder.
-- -/
-- instance (priority := high) : LE V₊ := ⟨(·=·)⟩
-- instance (priority := high) : LT V₊ := ⟨λ a b ↦ a ≤ b ∧ ¬ b ≤ a⟩ -- 😈 (NB this is `False`)

/--
High priority is imperative if we want Lean to pick this one up consistently.
Note that Lean already has `[Preorder α] (p : α → Prop) : Preorder (Subtype p)`, but we want ours.
-/
instance (priority := high) discrete_preorder_nonneg_V : Preorder V₊ := discretePreorder

omit [CovariantClass V V (fun x x_1 => x + x_1) fun x x_1 => x ≤ x_1]
     [CovariantClass V V (Function.swap fun x x_1 => x + x_1) fun x x_1 => x ≤ x_1] in
/--
Equality brings quality - promote a preorder on `V₊` to equality ASAP.
-/
@[simp]
lemma discrete_preorder_eq_equality {a b : V₊} : a ≤ b ↔ a = b := by rfl

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

/-
NB everything here is actually `... := inferInstance`, we're being explicit due to overabundance of caution.
Lean is perfectly capable of finding these preorders automatically.
-/

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

section Plumbing

/--
How is this not in Mathlib...
-/ 
instance : OrderedAddCommMonoid V := ⟨by aesop⟩

end Plumbing

-- @[simp]
-- lemma none_le {k₁ : K₁} {k₂ : K₂} {h} {b} (τcXb : Τc K₁ K₂ V × S K₁ K₂ V) :
--   (((⟨(k₁, k₂, none), h⟩, b) : Τ K₁ K₂ V × S K₁ K₂ V) ≤ (↑τcXb.1, τcXb.2)) := by
--   dsimp [(·≤·)]
  

--   aesop


end Order

def fPog (b : S K₁ K₂ V) (T : Τ K₁ K₂ V) : S K₁ K₂ V :=
  ⟨
    λ k ↦
      match h : T with
      | ⟨(s, r, .some v), hT⟩ => fc (⟨T, by simp [h]⟩, b) k
      | ⟨(s, _, .none), _⟩ => if k = s then 0 else b.1 k,
    by rintro (k | k) <;> aesop
  ⟩

def f (b : S K₁ K₂ V) (T : Τ K₁ K₂ V) : S K₁ K₂ V :=
  ⟨
    λ k ↦
      let ordered := { a : Τc K₁ K₂ V × S K₁ K₂ V | (T, b) ≤ (↑a.1, a.2) }
      let fAll := (fc · k) '' ordered ∪ {0} ∪ {b.1 k}
      have : InfSet fAll := { sInf := λ s ↦ ⟨fPog b T k, by
        dsimp [fAll, fPog] at s ⊢
        split
        next s r v hτ => rw [Set.mem_union, Set.mem_union]; left; left
                         apply Set.mem_image_of_mem; dsimp [ordered]; rfl
        next k₁ k₂ hτ => simp [Τ'.isValid] at hτ; rename Τ'.isValid (k₁, k₂, none) => hτ₁
                         have eq₁ : k₁ ≠ k₂ := by tauto
                         have eq₂ : ∃ k : Key K₁ K₂, k₁ = .key k := by rcases k₁ <;> aesop
                         rcases eq₂ with ⟨k', hk'⟩
                         by_cases eq : k₁ = k
                         · subst eq
                           rw [if_pos rfl, Set.mem_union]
                           left; right; exact Set.mem_singleton _
                         · rw [if_neg (by tauto)]
                           right; exact Set.mem_singleton _
                          ⟩ }
      let V' := { v : V // v ∈ fAll }
      let res : V' :=
        ⨅ x : ordered, ⟨fc x.1 k, by dsimp [fAll]
                                     rw [Set.mem_union, Set.mem_union]; left; left
                                     apply Set.mem_image_of_mem; aesop⟩
      res.1,
    by rintro (k | k)
       · simp; apply zero_le_val_subtype_of_le (by simp)
       · simp
  ⟩

theorem f_eq_fPog {b : S K₁ K₂ V} {T : Τ K₁ K₂ V} {k : Kbar K₁ K₂} : f b T k = fPog b T k := by
  unfold f fPog
  rfl

omit [CovariantClass V V (fun x x_1 => x + x_1) fun x x_1 => x ≤ x_1] in
lemma cast_order {v₁ v₂ : V}
                 (h : 0 ≤ v₁) (h₁ : 0 ≤ v₂) (h₂ : (⟨v₁, h⟩ : V₊) ≤ (⟨v₂, h₁⟩ : V₊)) : v₁ ≤ v₂ := by
  aesop
  
/--
The transaction function for complete transactions `fc` is monotone for a fixed `τc`.
-/
@[mono]
lemma fc_mono {τc : Τc K₁ K₂ V} {b₁ b₂ : S K₁ K₂ V}
              (h : b₁ ≤ b₂) : fc (τc, b₁) ≤ fc (τc, b₂) := λ k ↦ by
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

def fStar (Ts : List (Τ K₁ K₂ V)) (s₀ : S K₁ K₂ V) : S K₁ K₂ V :=
  Ts.foldl f s₀

variable [Finite K₁] [LinearOrder K₁]
         [Finite K₂] [LinearOrder K₂]

instance : Fintype K₁ := Fintype.ofFinite _
instance : Fintype K₂ := Fintype.ofFinite _ 

def Bal (π : BalanceProof K₁ K₂ C Pi V) (bs : List (Block K₁ K₂ C Sigma V)) : S K₁ K₂ V :=
  fStar (TransactionsInBlocks π bs) (.initial K₁ K₂ V)

section Lemma1

open BigOperators
/-
We start by noticing that the transition function for complete transacactions fc preserves the sum of account balances
-/
omit [LinearOrder K₁] [LinearOrder K₂] in
lemma fc_preserves_balances {Τ : Τc K₁ K₂ V} {b : S K₁ K₂ V} :
  ∑ (k : Kbar K₁ K₂), fc (Τ, b) k = ∑ (k : Kbar K₁ K₂), b k := by
  /-
    Proof. Left as an exercise for the reader. QED.
  -/
  unfold fc
  simp [Finset.sum_add_distrib, add_right_eq_self, ←Finset.sum_smul]
  
-- omit [LinearOrder K₁] [LinearOrder K₂] in
-- lemma f_le_balances {Τ : Τ K₁ K₂ V} {b : S K₁ K₂ V} :
--   ∑ (k : Kbar K₁ K₂), f b Τ k ≤ ∑ (k : Kbar K₁ K₂), b k := by
--   /-
--     Proof. Left as an exercise for the reader. QED.
--   -/
--   unfold f; lift_lets; intro univ; dsimp
--   generalize eq : (⨅ x ∈ univ, λ x ↦ (_ : S' K₁ K₂ V) x) = f
--   -- have : Fintype (Τc K₁ K₂ V) := Fintype.ofFinite _
--   rw [←fc_preserves_balances]
--   swap
  
  
--   -- apply Finset.sum_le_sum
--   -- simp [iInf_apply] at eq
  
--   -- apply Finset.sum_le_sum -- that's why we had to prove we are in OrderedAddCommMonoid
--   -- dsimp [univ] at eq
  
--   -- simp [univ]; intros k
--   -- simp

--   -- apply Finset.sum_le_sum (ι := Kbar K₁ K₂) (N := V) (f := (⨅ x ∈ univ, fun x_1 => ↑(fc x.1 x.2) x_1)) (g := ↑b k) (s := Finset.univ (α := Kbar K₁ K₂))
  
--   -- rw [←fc_preserves_balances]
--   -- simp

--   -- simp only [Prod.mk_le_mk, exists_prop, Subtype.exists, Prod.exists, iInf_exists]
  

--   -- rw [←fc_preserves_balances]
  

end Lemma1

end WithStructuredTypes

end Computation

end Balance

end

end Intmax

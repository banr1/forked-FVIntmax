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

@[aesop norm (rule_sets := [Intmax.aesop_valid])]
lemma isValid_iff {s r : Kbar K₁ K₂} {v? : Option V₊} :
  isValid (s, r, v?) ↔ s ≠ r ∧ (s matches .Source → v?.isSome) := by rfl

lemma s_ne_r_of_isValid {s r : Kbar K₁ K₂} {v? : Option V₊}
  (h : isValid ⟨s, r, v?⟩) : s ≠ r := by
  rw [isValid_iff] at h
  aesop

lemma exists_key_of_isValid {s r : Kbar K₁ K₂}
  (h : isValid (s, r, (none : Option V₊))) : ∃ k : Key K₁ K₂, s = k := by
  rcases s <;> valid

lemma isValid_some_of_ne {s r : Kbar K₁ K₂} {v? : V₊}
  (h : s ≠ r) : Τ'.isValid (s, r, some v?) := by valid

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
@[aesop norm (rule_sets := [Intmax.aesop_valid])]
def isComplete (τ : Τ K₁ K₂ V) :=
  match τ with | ⟨(_, _, v), _⟩ => v.isSome

lemma isSome_of_complete {t'} (h : isComplete ⟨⟨kb₁, kb₂, v?⟩, t'⟩) : v?.isSome := by
  unfold isComplete at h; valid

lemma s_ne_r_of_complete {t'} (h : isComplete ⟨⟨kb₁, kb₂, v?⟩, t'⟩) : kb₁ ≠ kb₂ := by
  unfold isComplete at h; valid

@[simp]
lemma isComplete_none {t'} : ¬isComplete ⟨⟨kb₁, kb₂, (.none : Option V₊)⟩, t'⟩ := by
  unfold isComplete
  valid

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
  | .deposit r v => [⟨(.Source, r, v), by valid⟩]
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
    sorted.attach.map λ ⟨(s, r), h⟩ ↦ ⟨(s, r, v s r), by valid⟩
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
    k₁InOrder.attach.map λ s : K₁ ↦ ⟨(s, .Source, withdrawals.lookup s), by valid⟩
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

instance : CoeFun (S K₁ K₂ V) λ _ ↦ Kbar K₁ K₂ → V :=
  ⟨λ s k ↦ s.1 k⟩

namespace S

def initial (K₁ K₂ V : Type) [Nonnegative V] : S K₁ K₂ V :=
  ⟨S'.initial K₁ K₂ V, S'.isValid_initial⟩

@[simp]
lemma initial_eq_zero {k : Kbar K₁ K₂} : initial K₁ K₂ V k = 0 := by
  simp [initial, S'.initial]

@[simp]
lemma nonneg {s : S K₁ K₂ V} {k : Key K₁ K₂} : 0 ≤ s k := by
  aesop

@[simp]
lemma isValid_coe {s : S K₁ K₂ V} : S'.isValid (V := V) (K₁ := K₁) (K₂ := K₂) ↑s := by
  valid

@[simp]
lemma nonneg_coe {s : S K₁ K₂ V} {k : Key K₁ K₂} : 0 ≤ (↑s : S' K₁ K₂ V) k := by
  aesop

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

@[simp]
lemma v'_zero : v' 0 b s = 0 := by unfold v'; aesop

@[simp]
lemma v'_self {h} : v' ⟨(b s), h⟩ b s = ⟨b s, h⟩ := by unfold v'; aesop

@[simp]
lemma v'_cast_nonneg : 0 ≤ ↑(v' v b' s) := by simp

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

lemma le_fc_of_ne {τc : Τc K₁ K₂ V} {b : S K₁ K₂ V} {k : Kbar K₁ K₂}
  (h : τc.1.1.1 ≠ k) : b k ≤ fc (τc, b) k := by unfold fc v'; aesop

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

end Order

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

def f' (b : S K₁ K₂ V) (T : Τ K₁ K₂ V) : S K₁ K₂ V :=
  ⟨
    λ k ↦
      match h : T with
      | ⟨(_, _, .some v), hT⟩ => fc (⟨T, by simp [h]⟩, b) k
      | ⟨(s, _, .none), _⟩ => if k = s then 0 else b k,
    by rintro (k | k) <;> aesop
  ⟩

@[simp]
lemma f'_of_cast_complete {b : S K₁ K₂ V} {Tc : Τc K₁ K₂ V} :
  f' b ↑Tc k = fc (Tc, b) k := by
  have := Τ.isSome_of_complete Tc.2
  unfold f'
  aesop

lemma f'_of_complete {b : S K₁ K₂ V} {T : Τ K₁ K₂ V}
  (h : T.isComplete) : f' b T k = fc (⟨T, h⟩, b) k := by
  rw [←f'_of_cast_complete]

lemma f'_of_not_complete {b : S K₁ K₂ V} {T : Τ K₁ K₂ V}
  (h : ¬T.isComplete) : f' b T k = if k = T.1.1 then 0 else b k := by
  dsimp [f']
  unfold Τ.isComplete at h
  aesop

abbrev boundedBelow (b : S K₁ K₂ V) (T : Τ K₁ K₂ V) :=
  { a : Τc K₁ K₂ V × S K₁ K₂ V | (T, b) ≤ (↑a.1, a.2) }

def V' (b : S K₁ K₂ V) (T : Τ K₁ K₂ V) (k : Kbar K₁ K₂) : Set V :=
  { v : V | v ∈ (fc · k) '' boundedBelow b T }

lemma f'_codomain {b : S K₁ K₂ V} {T : Τ K₁ K₂ V} {k : Kbar K₁ K₂} :
  f' b T k ∈ V' b T k := by
  unfold V' f'
  dsimp; rw [Set.mem_image]; dsimp
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

instance {b : S K₁ K₂ V} {T : Τ K₁ K₂ V} {k : Kbar K₁ K₂} :
  InfSet (V' b T k) where
    sInf := λ _ ↦ ⟨f' b T k, f'_codomain⟩

/--
NB the `f'` function is the greatest lower bound on an appropriate subset of `V`, not on `V`.
-/
lemma f'_IsGLB_of_V' {b : S K₁ K₂ V} {T : Τ K₁ K₂ V} {k : Kbar K₁ K₂} :
  IsGLB (V' b T k) (f' b T k) := by
  dsimp [f', V', IsGLB, IsGreatest, lowerBounds, upperBounds, boundedBelow]; simp only [Set.mem_image]
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
  case isGreatest => 
    intros v h; dsimp [V'] at h
    apply h
    split
    next s r v? hv? => use (⟨⟨_, hv?⟩, by valid⟩, b)
    next s r hv? =>
      obtain ⟨key, hkey⟩ := Τ'.exists_key_of_isValid hv?
      have : s ≠ r := Τ'.s_ne_r_of_isValid hv?
      by_cases eq : k = s
      · let τc : Τc K₁ K₂ V := ⟨
          ⟨(s, r, .some ⟨b k, by valid⟩), by rw [Τ'.isValid_iff]; simp [this]⟩,
          by simp
        ⟩
        use (τc, b)
        simp [(·≤·), fc, eq, this.symm]
      · let τc : Τc K₁ K₂ V := ⟨
          ⟨(s, r, .some 0), by rw [Τ'.isValid_iff]; simp [this]⟩,
          by simp
        ⟩
        use (τc, b)
        simp [(·≤·), fc, eq, this.symm]

def f (b : S K₁ K₂ V) (T : Τ K₁ K₂ V) : S K₁ K₂ V :=
  ⟨
    λ k ↦
      let res : V' b T k := ⨅ x : boundedBelow b T, ⟨fc x.1 k, by dsimp [V']; use x; aesop⟩
      res.1,
    by rintro (k | k)
       · simp; apply zero_le_val_subtype_of_le (by simp)
       · simp
  ⟩

theorem f_eq_f' {b : S K₁ K₂ V} {T : Τ K₁ K₂ V} {k : Kbar K₁ K₂} : f b T k = f' b T k := rfl

lemma f_IsGLB_of_V' {b : S K₁ K₂ V} {T : Τ K₁ K₂ V} {k : Kbar K₁ K₂} :
  IsGLB (V' b T k) (f b T k) := by simp [f_eq_f', f'_IsGLB_of_V']

omit [CovariantClass V V (fun x x_1 => x + x_1) fun x x_1 => x ≤ x_1] in
lemma cast_order {v₁ v₂ : V}
                 (h : 0 ≤ v₁) (h₁ : 0 ≤ v₂) (h₂ : (⟨v₁, h⟩ : V₊) ≤ (⟨v₂, h₁⟩ : V₊)) : v₁ ≤ v₂ := by
  aesop

def fStar (Ts : List (Τ K₁ K₂ V)) (s₀ : S K₁ K₂ V) : S K₁ K₂ V :=
  Ts.foldl f s₀

@[simp]
lemma fStar_nil {s : S K₁ K₂ V} :
  fStar [] s = s := by rfl

@[simp]
lemma fStar_cons {hd : Τ K₁ K₂ V} {tl : List (Τ K₁ K₂ V)} {s : S K₁ K₂ V} :
  fStar (hd :: tl) s = fStar tl (f s hd) := by rfl


variable [Finite K₁] [LinearOrder K₁]
         [Finite K₂] [LinearOrder K₂]

instance : Fintype K₁ := Fintype.ofFinite _
instance : Fintype K₂ := Fintype.ofFinite _ 

def Bal (π : BalanceProof K₁ K₂ C Pi V) (bs : List (Block K₁ K₂ C Sigma V)) : S K₁ K₂ V :=
  fStar (TransactionsInBlocks π bs) (.initial K₁ K₂ V)

section Lemma1

open BigOperators
/-
PAPER: We start by noticing that the transition function for complete transactions fc preserves the sum of account balances
-/
omit [LinearOrder K₁] [LinearOrder K₂] in
@[simp]
lemma sum_fc_eq_sum {Tc : Τc K₁ K₂ V} {b : S K₁ K₂ V} :
  ∑ (k : Kbar K₁ K₂), fc (Tc, b) k = ∑ (k : Kbar K₁ K₂), b k := by
  /-
    Proof. Left as an exercise for the reader. QED.
  -/
  unfold fc
  simp [Finset.sum_add_distrib, add_right_eq_self, ←Finset.sum_smul]

/-
PAPER: This implies the following fact about the transition function for partial transactions f: 
-/
omit [LinearOrder K₁] [LinearOrder K₂] in
lemma sum_f_le_sum {T : Τ K₁ K₂ V} {b : S K₁ K₂ V} :
  ∑ (k : Kbar K₁ K₂), f b T k ≤ ∑ (k : Kbar K₁ K₂), b k := by
  by_cases eq : T.isComplete
  · conv_rhs => rw [←sum_fc_eq_sum (Tc := ⟨T, eq⟩)]
    refine' Finset.sum_le_sum (λ k _ ↦ _)
    have fcInV' : fc (⟨T, eq⟩, b) k ∈ V' b T k := by
      dsimp [V']
      rw [Set.mem_image]
      use (⟨T, eq⟩, b)
      simp
    exact f_IsGLB_of_V'.1 fcInV'
  · rcases T with ⟨⟨s, r, v⟩, h⟩
    let Tc : Τc K₁ K₂ V := ⟨⟨(s, r, some 0), by valid⟩, by simp⟩
    conv_rhs => rw [←sum_fc_eq_sum (Tc := Tc)]
    refine' (Finset.sum_le_sum (λ k _ ↦ _))
    have fcInV' : fc (Tc, b) k ∈ V' b ⟨(s, r, v), h⟩ k := by
      dsimp [V']
      rw [Set.mem_image]
      use (⟨⟨(s, r, some 0), by valid⟩, by valid⟩, b)
      have : v = none := by aesop
      simp [this, (·≤·)]
    exact f_IsGLB_of_V'.1 fcInV'

/-
@ERIK: Isn't this easier? Doesn't even need `sum_fc_eq_sum`.
       Note this relies on `f_eq_f` but in this setup, `f_eq_f'` does _not_ require
       us to exhibit that it is 'the real' greatest lower bound, it's essentially 'just syntax'.
       Worth noting this is still shown in `f_IsGLB_of_V'`, for the set `V'`.
-/
omit [LinearOrder K₁] [LinearOrder K₂] in
lemma sum_f_le_sum' {T : Τ K₁ K₂ V} {b : S K₁ K₂ V} :
  ∑ (k : Kbar K₁ K₂), f b T k ≤ ∑ (k : Kbar K₁ K₂), b k := by
  /-
    We know `f = f'` and furthermore, from the definition of `f'`, we need to show:
    ∑ k : Kbar K₁ K₂,
      match h : T with
      | ⟨(fst, fst_1, some v), hT⟩ => ↑(fc (⟨T, ⋯⟩, b)) k
      | ⟨(s, fst, none), property⟩ => if k = s then 0 else ↑b k
    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ definition of `f'`
    ≤
    ∑ x : Kbar K₁ K₂, b x
  -/
  simp [f_eq_f', f']
  /-
    We proceed by cases on completeness of the transaction.
  -/
  split
  /-
    The transaction is complete.
  -/
  next s r v hτ => simp -- Sorry I lied, we use `sum_fc_eq_sum` here! From which this follows immediately.
  /-
    The transaction is _not_complete.
    Thus, we need to show:
    `∑ x : Kbar K₁ K₂, if x = k₁ then 0 else b x`
    `≤`
    `∑ x : Kbar K₁ K₂, ↑b x`.
  -/
  next k₁ k₂ hτ =>
    /-
      To show these two sums are ≤, it suffices to show: `if k = k₁ then 0 else ↑b k ≤ ↑b k`
      This is because `∀ i ∈ s, f i ≤ g i → ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i`.
    -/
    refine' (Finset.sum_le_sum (λ k _ ↦ _))
    /-
      We know that `k = Kbar.key s`.
    -/
    obtain ⟨s, hs⟩ := Τ'.exists_key_of_isValid hτ
    /-
      Suppose `k₁ = Kbar.key s`.
      Show `0 ≤ b (Kbar.key s)`, true by `nonneg_key_of_isValid`.
      Suppose `k₁ ≠ Kbar.key s`.
      Show `val k ≤ val k`. True by `le_refl`.
    -/
    aesop

/-
The statement `sum_fStar_le_zero` fixes the initial accumulator to `S.initial`.
The 'obvious' induction proceeds on all accumulators; however, generalizing
the initial accumulator either makes the base case unprovable if this information
is thrown out, or makes the inductive hypothesis useless if this information is kept.

As such, we state this auxiliary theorem, articulating explicitly a condition that holds
for _all_ relevant accumulators; more specifically, `(h : ∑ (k : Kbar K₁ K₂), s k ≤ 0)`.
Now we are free to generalize the accumulator without invalidating either the base case
or the inductive step.

Note further that `∑ (k : Kbar K₁ K₂), (S.initial K₁ K₂ V) k ≤ 0`, as shown in
`sum_fStar_le_zero`.
-/
omit [LinearOrder K₁] [LinearOrder K₂] in
private lemma sum_fStar_le_zero_aux {Tstar : List (Τ K₁ K₂ V)} {s : S K₁ K₂ V}
  (h : ∑ (k : Kbar K₁ K₂), s k ≤ 0) :
  ∑ (k : Kbar K₁ K₂), fStar Tstar s k ≤ 0 := by
  simp [fStar]
  induction Tstar generalizing s with
  | nil => aesop (add safe apply Finset.sum_nonpos)
  | cons _ _ ih => exact ih (le_trans sum_f_le_sum h)

/-
PAPER (Equation 1 in Lemma 1): Then, it follows by induction that we have

NB I don't want to really introduce the notation `0` means the initial `S`. Can do tho vOv.

NB please cf. `sum_fStar_le_zero_aux` to see what's happening.
-/
omit [LinearOrder K₁] [LinearOrder K₂] in
lemma sum_fStar_le_zero {Tstar : List (Τ K₁ K₂ V)} :
  ∑ (k : Kbar K₁ K₂), fStar Tstar (S.initial K₁ K₂ V) k ≤ 0 :=
  sum_fStar_le_zero_aux (by simp)

lemma lemma1 {π : BalanceProof K₁ K₂ C Pi V}
             {bs : List (Block K₁ K₂ C Sigma V)} :
  Bal π bs .Source ≤ 0 := by
  dsimp [Bal]
  generalize eq : TransactionsInBlocks π _ = blocks
  generalize eq₁ : S.initial K₁ K₂ V = s₀
  generalize eq₂ : fStar blocks s₀ = f
  have : ∑ x ∈ {Kbar.Source}, f x = 
         ∑ x : Kbar K₁ K₂, f x - ∑ x ∈ Finset.univ \ {Kbar.Source}, f x := by simp
  rw [←Finset.sum_singleton (a := Kbar.Source) (f := f), this, sub_nonpos]
  have := sum_fStar_le_zero_aux (Tstar := blocks) (s := s₀)
  have eq₃ : ∑ x : Kbar K₁ K₂, f x ≤ 0 := by aesop
  have eq₄ : 0 ≤ ∑ x ∈ Finset.univ \ {Kbar.Source}, f x := Finset.sum_nonneg λ i ↦ by rcases i <;> aesop
  exact le_trans eq₃ eq₄

end Lemma1

end WithStructuredTypes

end Computation

end Balance

end

end Intmax

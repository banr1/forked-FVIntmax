import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

import FVIntmax.Wheels.Oracle
import FVIntmax.Wheels.Wheels

import FVIntmax.Block
import FVIntmax.TransactionBatch
import FVIntmax.Wheels

import FVIntmax.Wheels.AuthenticatedDictionary
import FVIntmax.Wheels.SignatureAggregation

namespace Intmax

set_option autoImplicit false

section RollupContract

/--
2.4

- Scontract := 𝔹*
-/
abbrev RollupState (K₁ K₂ V : Type) [Zero V] [Preorder V] (C Sigma : Type) :=
  List (Block K₁ K₂ C Sigma V)

namespace RollupState

/--
2.4

- When the rollup contract is deployed to the blockchain, it is initialized with
  the state () consisting of the empty list.
-/
def initial (K₁ K₂ V : Type) [Zero V] [Preorder V] (C Sigma : Type) : RollupState K₁ K₂ V C Sigma := []

-- section Valid

-- variable {K₁ : Type} [DecidableEq K₁] {K₂ C Sigma V : Type} [LE V] [OfNat V 0]

-- def isValid (s : RollupState K₁ K₂ V C Sigma) := ∀ block ∈ s, block.isValid

-- lemma isValid_cons {block : Block K₁ K₂ C Sigma V} {s : RollupState K₁ K₂ V C Sigma}
--   (h : block.isValid) (h₁ : s.isValid) : RollupState.isValid (block :: s) := by unfold isValid; aesop

-- lemma isValid_initial {K₁ : Type} [DecidableEq K₁] {K₂ C Sigma V : Type} [LE V] [OfNat V 0] :
--   (initial K₁ K₂ V C Sigma).isValid := by simp [isValid, initial]

-- end Valid

end RollupState

/-
2.5
-/
section Depositing

/--
TODO(REVIEW): Does the order in which these get into the state matter? I'm choosing to prepend
              here because it's the more natural operation on `List` with better reduction behaviour.
              It's not a big deal tho, we can do `s ++ [Block.deposit addr value]` and then shuffle.
-/
def RollupState.deposit {K₁ K₂ C Sigma V : Type} [Zero V] [Preorder V]
                        (addr : K₂) (value : V₊) (s : RollupState K₁ K₂ V C Sigma) :
                        RollupState K₁ K₂ V C Sigma := Block.mkDepositBlock _ _ _ addr value :: s

namespace Block

section Block

-- variable {K₁ : Type} [DecidableEq K₁]
--          {K₂ C Sigma V : Type} [OfNat V 0] [LE V]
--          {addr : K₂} {value : V}

-- /-
-- `deposit` preserves validity of the rollup state assuming the value is being deposited is nonnegative
-- and the state was valid in the first place.
-- -/
-- lemma isValid_deposit_of_nonneg
--   {addr : K₂} {value : V} {s : RollupState K₁ K₂ V C Sigma}
--   (h : 0 ≤ value) (h₁ : s.isValid) : (s.deposit addr value).isValid :=
--   RollupState.isValid_cons (isValid_mkDepositBlock_of_nonneg h) h₁

end Block

end Block

end Depositing

/-
2.6
-/
section Transferring

variable {K₁ : Type} [DecidableEq K₁] [Finite K₁]
         {K₂ : Type} [Finite K₂]
         {sender sender' : K₂} {senders : List K₂}
         {V : Type} [DecidableEq V] [Finite V]

/-
Phase 1
-/

noncomputable def salt : UniquelyIndexed K₂ := default

/--
This is a corollary following from the way that `UniquelyIndexed` types are constructed.
-/
lemma salt_injective : Function.Injective (salt (K₂ := K₂)) := salt.injective

noncomputable def salts : List K₂ → List !K₂ := List.map salt

/--
The only relevant property of salts.
-/
lemma injective_salts : Function.Injective (salts (K₂ := K₂)) :=
  List.map_injective_iff.2 salt.injective

/--
I lied. This is also relevant.
-/
@[simp]
lemma length_salts {l : List K₂} : (salts l).length = l.length := by
  simp [salts]

section Transaction

variable {C Pi : Type} (Λ : ℕ) (aggregator : K₁) (extradata : ExtraDataT)
         [DecidableEq K₂]
         [AD : ADScheme K₂ (!(TransactionBatch K₁ K₂ V × !K₂)) C Pi]

/-
Just ignore this section.
-/
section AutomateZipping

attribute [aesop simp 9001 (rule_sets := [Intmax.aesop_dict])] List.map_fst_zip

end AutomateZipping

/--
PAPER:
- hₛ ← H(tₛ, saltₛ)
-/
noncomputable def H : UniquelyIndexed (TransactionBatch K₁ K₂ V × !K₂) := default

lemma injective_H : Function.Injective (H (K₁ := K₁) (K₂ := K₂) (V := V)) := H.injective

/--
TODO(REVIEW) - Re. @Denisa wrt. one salt per one transaction;

I actually think this first step is correct irrespective of salting multiple transactions.
This is because this definition takes: `senders : List (K₂ × TransactionBatch K₁ K₂ V)`, IOW
it already only expresses the relationship of a single batch being sent by each user.

As such, if there is some other definition further down the line that expresses the notion of transactions
being sent over and over or whatever else, the first step will repeat and you get a new salt - note that in this model,
you can't actually prove that the new salt is distinct (or even the same, for that matter), and this to me seems
like actually a good thing.

PAPER:
First, each sender s chooses a random salt salts, hashes their transaction batch with the salt
hs ← H(ts, salts) and sends hs to the aggregator.
-/
noncomputable def firstStep
  (senders : List (K₂ × TransactionBatch K₁ K₂ V)) : List (!(TransactionBatch K₁ K₂ V × !K₂)) :=
  let (senders, batches) := senders.unzip
  let salts              := salts senders
  batches.zipWith (Function.curry H) salts

@[simp]
lemma length_firstStep {l : List (K₂ × TransactionBatch K₁ K₂ V)} :
  (firstStep l).length = l.length := by
  simp [firstStep]

lemma injective_firstStep : Function.Injective (firstStep (K₁ := K₁) (K₂ := K₂) (V := V)) := by
  unfold firstStep
  simp [salts]; simp [Function.Injective]

section LikelyUseless

@[deprecated firstStep]
noncomputable def firstStep'
  (senders : List (K₂ × TransactionBatch K₁ K₂ V)) : List (K₂ × !(TransactionBatch K₁ K₂ V × !K₂)) :=
  (senders.map Prod.fst).zip (firstStep senders)

@[deprecated injective_firstStep]
lemma injective_firstStep' : Function.Injective (firstStep' (K₁ := K₁) (K₂ := K₂) (V := V)) := by
  /-
    We construct second components of pairs in an injective fashion.
    As such, it does not matter what we zip them with, the injective property
    is preserved by virtue of extensionality of products.
  -/
  unfold firstStep'
  intros l₁ l₂ h; dsimp at h
  have : l₁.length = l₂.length := by
    simp only [List.zip_map_left] at h
    apply congrArg List.length at h
    simp at h
    exact h
  have h₁ : (List.map Prod.fst l₁).length = (firstStep l₁).length := by simp
  rw [List.zip_eq_iff h₁ (by simpa) (by simp)] at h
  exact injective_firstStep h.2

end LikelyUseless

def secondStep
  (userBatches : List (K₂ × !(TransactionBatch K₁ K₂ V × !K₂)))
  (h : (userBatches.map Prod.fst).Nodup) :
  CommitT C K₂ Pi :=
  let users := userBatches.map Prod.fst
  let batches := userBatches.map Prod.snd
  have : users.length = batches.length := by simp [users, batches]
  let dict : Dict K₂ !(TransactionBatch K₁ K₂ V × !K₂) :=
  ⟨
    { k | k ∈ users },
    ⟨
      Multiset.ofList (users.zipWith Sigma.mk batches),
      by simp only [Multiset.coe_nodupKeys]
         unfold List.NodupKeys
         rwa [List.keys_zipWith_sigma this]
    ⟩,
    by simp [Finmap.mem_def]
       rw [List.keys_zipWith_sigma this]
  ⟩
  ADScheme.Commit Λ dict (C := C) (Pi := Pi)

/--
Follows from `ADScheme.correct_keys_eq`, i.e. authenticated dictionaries preserve keys.
-/
lemma dict_keys_secondStep_eq
  {userBatches : List (K₂ × !(TransactionBatch K₁ K₂ V × !K₂))}
  (h : (userBatches.map Prod.fst).Nodup) {k} :
  k ∈ (secondStep (K₁ := K₁) (C := C) (V := V) (Pi := Pi) AD.Λ userBatches h).keys ↔
  k ∈ userBatches.map Prod.fst := by simp only [secondStep]; dict

structure MessageT (C : Type) (K₁ : Type) :=
  commitment : C
  aggregator : K₁
  extradata  : ExtraDataT

variable {Kₚ : Type} [Nonempty Kₚ]
         {Kₛ : Type} [Nonempty Kₛ] {Sigma: Type}
         [SignatureAggregation (MessageT C K₁) Kₚ Kₛ Sigma]

/--
TODO(REVIEW):
A whatever existance of keys, I am not yet sure what a good representation is.
I am assuming we don't care that K<X> can see the keys of K<Y>, as this is already
only an assumption in the paper anyway.

@Denisa - What properties will need to hold here?
-/
noncomputable abbrev userKeys : K₂ → Kₚ × Kₛ := Classical.arbitrary _

variable (userKeysAreGen : ∀ user : K₂,
                             SimpleRandom.isRandom
                               (SignatureAggregation.KeyGen (M := MessageT C K₁) Sigma Λ)
                               (userKeys (Kₚ := Kₚ) (Kₛ := Kₛ) user))

/--
TODO(REVIEW) - What on Earth is this... the messages are somehow made out of
commitment aggregator extradata?
-/
noncomputable def thirdStepSingleUser
                    (commitment : C)
                    (user : K₂)
                    (proof : Pi)
                    (saltBatch : !(TransactionBatch K₁ K₂ V × !K₂)) :
                    Option Sigma :=
  if ADScheme.Verify Λ proof user saltBatch commitment
  then .some (SignatureAggregation.Sign Kₚ (Kₛ := Kₛ) AD.Λ (userKeys (Kₚ := Kₚ) (Kₛ := Kₛ) user).2 (MessageT.mk commitment aggregator extradata))
  else .none

noncomputable def thirdStep (commits : CommitT C K₂ Pi × List (K₂ × !(TransactionBatch K₁ K₂ V × !K₂)))
              (h : ∀ k ∈ commits.2.map Prod.fst, k ∈ commits.1.keys) : List (Option Sigma) :=
  let userInfo   := commits.2
  let commits'   := commits.1
  let commitment := commits'.commitment
  let users      := userInfo.map Prod.fst
  let batches    := userInfo.map Prod.snd
  let proofs     := users.attach.map λ k ↦
                      commits'.dict.lookup (k := k.1) (by dsimp only [commits']; dict)
  List.zipWith3 (thirdStepSingleUser (Kₚ := Kₚ) (Kₛ := Kₛ) (Sigma := Sigma) AD.Λ aggregator extradata commitment) users proofs batches

/--
  We assume no duplicate users. This is safe because the paper uses sets anyway.
-/
def transferBlockOfUsersWithBatches
  (usersWithBatches : List (K₂ × TransactionBatch K₁ K₂ V))
  (h : (usersWithBatches.map Prod.fst).Nodup) : Nat :=
  /-
    NB 'sending' is modelled as a sequence of functions, no need to explicitly express this.
  -/
  let users : List K₂ := usersWithBatches.map Prod.fst

  have h₁ : users.Nodup := h

  /-
    PAPER: 1.

    First, each sender s chooses a random salt salts, hashes their transaction
    batch with the salt hs ← H(ts, salts), and sends hs to the aggregator.
  -/
  let hashedSaltyUsers : List !(TransactionBatch K₁ K₂ V × !K₂) := firstStep usersWithBatches
  /-
    The intermediate 'state' considering the model is described in terms of users/aggregators
    taking turns. As such, there is an implicit state in the sense that users do not forget
    information they compute.
  -/
  let s₀ := users.zip hashedSaltyUsers

  have h₂ : users.length = hashedSaltyUsers.length := by
    simp [hashedSaltyUsers, users]
  have h₃ : (List.map Prod.fst s₀).Nodup := by
    rwa [List.map_fst_zip _ _ (le_of_eq h₂)]
  /-
    PAPER: 2.

    The aggregator collects all the transaction batch hashes from the senders.
    Let S′ ⊂ S be the subset of senders who sent a transaction batch hash
    to the aggregator. The aggregator then constructs the dictionary9 (S′, h)
    where hs is the transaction batch hash by s for all s ∈ S′, and constructs a
    dictionary commitment and lookup proofs:
    (C, (S′, π)) ← AD.Commit(S′, h).
    The aggregator sends to each user s ∈ S′ the dictionary commitment C
    and the lookup proof πs for the user’s transaction batch hash

    NB the S′ ⊂ S who sent a transaction batch _already are_ the users _usersWithBatches_.
  -/
  let authDict : CommitT C K₂ Pi := secondStep AD.Λ s₀ h₃

  let s₁ := (authDict, s₀)

  /-
    This is true by `dict_keys_secondStep_eq` which uses the AD keys preservation property transitively.
  -/
  have h₄ {k} : k ∈ users ↔ k ∈ authDict.keys := by
    dsimp only [authDict, hashedSaltyUsers]
    rw [dict_keys_secondStep_eq]
    dict

  /-
    PAPER: 3.
    
    Upon receiving the dictionary commitment and lookup proof, each user s
    checks if the lookup proof is valid with the commitment:
    AD.Verify(πs, s, hs, C) ?= True.
    If the lookup proof is valid, the user generates the signature
    σs ← SA.Sign(sks,(C, aggregator, extradata))
    The protocol allows anyone to be an aggregator for a transfer block, enabling
    maximum censorship resistance.
    Sending the transaction hash instead of the transaction itself gives privacy from
    the aggregator.
    See Appendix A.1 for the definition of a dictionary.
    and sends this signature to the aggregator.
  -/
  let signedMessages := thirdStep (K₁ := K₁) (K₂ := K₂) (V := V) (C := C) (Pi := Pi) (Sigma := Sigma) (Kₚ := Kₚ) (Kₛ := Kₛ) aggregator extradata s₁
                          (by dsimp only [s₁, s₀]; dict)
  42 

end Transaction

end Transferring

end RollupContract

end Intmax

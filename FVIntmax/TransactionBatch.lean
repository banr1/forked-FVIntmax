import Mathlib.Data.Finite.Basic
import Mathlib.Data.Finmap
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset

import FVIntmax.Key
import FVIntmax.Wheels.Wheels
import FVIntmax.Wheels

import Mathlib.Tactic

namespace Intmax

/-
2.6 - Transaction batch
-/
section TransactionBatch

/--
PAPER: a transaction batch is an element of V₊ᵏ
NB we do not impose `V₊`, here, but in `TransactionBatch.isValid` for convenience.
As such, we will prove properties for _valid transaction batches_ rather than for any batches.
NB as per usual, V does not need to be a latticed-ordered abelian group just yet.
-/
abbrev TransactionBatch (K₁ : Type) [Finite K₁] (K₂ : Type) [Finite K₂] (V : Type) [Nonnegative V] :=
  { m : Finmap (λ _ : Key K₁ K₂ ↦ V) // ∀ k, k ∈ m }

section Finite

variable {K₁ : Type} [Finite K₁]
         {K₂ : Type} [Finite K₂]

/--
We define an equivalence between maps `K → V` and finmaps that are defined for all keys.
This will be used to show that `TransactionBatch` is finite as long as the domain and codomain
is finite.
-/
noncomputable def univFinmap (K : Type) [Fintype K] [DecidableEq K]
                             (V : Type) [DecidableEq V] :
  { m : Finmap (λ _ : K ↦ V) // ∀ k, k ∈ m } ≃ (K → V) :=
  {
    toFun := λ m k ↦ m.1.lookup_h (a := k) (m.2 k)
    invFun := λ f ↦
      let keys : Finset K := Finset.univ
      ⟨⟨
        Multiset.ofList <| keys.toList.zipWith (f := Sigma.mk) (keys.toList.map f),
        by /-
             We start with no duplicates in the universal set for `K` and
             the production of pairs `(k : K × f k : V)` keeps them intact.
             As such, there are no duplicate keys in the final map.
           -/
           simp [List.NodupKeys]
           rw [List.keys_zipWith_sigma (by simp)]
           exact Finset.nodup_toList _
       ⟩,
        by /-
             We start with the universal set for `K`, which is complete by definiton.
             Furthermore, we keep all `K`s and assign them values from the function's range.
             This construction obviously preserves all keys.
           -/
           intros k; rw [Finmap.mem_def]; dsimp
           aesop (add simp List.keys_zipWith_sigma)
           ⟩
    left_inv := by
      /-
        Two key observations:
        - `⟨k, v⟩ ∈ m` iff `m.lookup k = v`
        - in maps where all keys are present, the lookup on the universal set of all keys never fails
      -/
      simp [Function.LeftInverse]; rintro ⟨m, hm⟩ h; simp
      ext ⟨key, value⟩; simp [List.zipWith_map_right]
      generalize eqF : (λ a ↦ ⟨a, _⟩ : K → (_ : K) × V) = f
      dsimp [Finmap.lookup_h] at eqF
      have nodupm : m.Nodup := by
        rwa [← Multiset.nodup_keys, Multiset.keys, Multiset.nodup_map_iff_of_inj_on] at hm
        rintro ⟨x₁, x₂⟩ hx ⟨y₁, y₂⟩ hy h'
        set map' : Finmap (λ _ : K ↦ V) := { entries := m, nodupKeys := _ }
        have eq₁ : ⟨x₁, x₂⟩ ∈ map'.entries := by aesop
        have eq₂ : ⟨x₁, y₂⟩ ∈ map'.entries := by aesop
        rw [←Finmap.lookup_eq_some_iff] at eq₁ eq₂
        aesop
      have nodupl : (List.map f Finset.univ.toList).Nodup := by
        apply List.nodup_map_of_pres_keys_nodup (by aesop) (Finset.nodup_toList _)
      rw [Multiset.count_eq_of_nodup nodupm, List.count_eq_of_nodup nodupl]
      set map' : Finmap (λ _ : K ↦ V) := { entries := m, nodupKeys := _ } with eqM
      by_cases eq : ⟨key, value⟩ ∈ m <;> simp [eq]
      · have : map'.lookup key = .some value := by rw [Finmap.lookup_eq_some_iff]; aesop
        aesop
      · intros k contra
        simp [eqF.symm, Option.get] at contra
        split at contra
        next _ _ v hv eq₃ _ => rw [Finmap.lookup_eq_some_iff] at eq₃
                               aesop
    right_inv := by
      /-
        Triviall follows from `⟨k, v⟩ ∈ m` iff `m.lookup k = v`.
        The left inverse is more involved because we need do not get the functional property of
        `f : K → V` for free and we have to recover it.
      -/
      simp [Function.RightInverse, Function.LeftInverse, List.zipWith_map_right]
      intros f; ext
      simp [Finmap.lookup_h, Option.get]
      split
      next _ _ v hv e _ => 
        simp [Finmap.lookup_eq_some_iff] at e 
        exact e.symm
  }

/--
For a finite K₁, K₂ and V, we can establish that a `TransactionBatch K₁ K₂ V` is finite.
-/
instance [DecidableEq K₁] [DecidableEq K₂] [DecidableEq V] [Nonnegative V] [Finite V] :
  Finite (TransactionBatch K₁ K₂ V) := by
  /-
    Follows trivially from the definition of `univFinmap`, for if we know that `(Key K₁ K₂ → V)`
    is finite and we have a `... ≃ TransactionBatch K₁ K₂ V`, then the rhs is finite as well.
  -/
  have : Fintype K₁ := Fintype.ofFinite _
  have : Fintype K₂ := Fintype.ofFinite _
  have := univFinmap (K := Key K₁ K₂) (V := V)

  exact @Finite.of_equiv _ _ _ this.symm

/-
TODO(REVIEW):
  Suppose we have the same theorem:
  instance {K₁ : Type} [Finite K₁] [DecidableEq K₁]
           {K₂ : Type} [Finite K₂] [DecidableEq K₂]
           {V  : Type} [Finite V] [DecidableEq V] : Finite (TransactionBatch K₁ K₂ V)  

  But instead we define `TransactionBatch K₁ K₂ V` to be a `Finmap ((_ : Key K₁ K₂) ↦ V)`.
  Can we easily show that this is finite too? I think this would be more convenient,
  but I couldn't easily prove this so I chose a slightly different approach.

  Does the `univFinmap` maybe help?
-/

end Finite

end TransactionBatch

end Intmax

import FVIntmax.AttackGame
import FVIntmax.Lemma3
import FVIntmax.Lemma4
import FVIntmax.Lemma5
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

noncomputable section theorem1

section AttackGame

variable {Sigma Pi M : Type}
         {C : Type} [Nonempty C]
         {V : Type}
         [Lattice V] [AddCommGroup V]
         [CovariantClass V V (· + ·) (· ≤ ·)]
         [CovariantClass V V (Function.swap (· + ·)) (· ≤ ·)]
         {K₁ : Type} [Nonempty K₁] [Finite K₁] [LinearOrder K₁]
         {K₂ : Type} [Finite K₂] [LinearOrder K₂]
         {Kₚ : Type} [Nonempty Kₚ]
         {Kₛ : Type} [Nonempty Kₛ]

instance : Setoid' ((Pi × ExtraDataT) × TransactionBatch K₁ K₂ V) where
  isEquiv := by unfold IsEquivRel iso; aesop

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

@[simp]
lemma mergeR''_append {πs πs' : List (BalanceProof K₁ K₂ C Pi V)} {acc} :
  mergeR'' (πs ++ πs') acc = mergeR'' πs' (mergeR'' πs acc) := by
    rw [mergeR''_eq_foldl, mergeR''_eq_foldl, mergeR''_eq_foldl]
    unfold mergeR'''
    rw [←List.foldl_append]

@[simp]
lemma mem_list_singleton_iff {π} : π ∈ ({acc} : List (BalanceProof K₁ K₂ C Pi V)) ↔ π = acc := by
  simp [singleton]

def BalanceProof.compat (π₁ π₂ : BalanceProof K₁ K₂ C Pi V) : Prop :=
  ∀ k, π₁ k ≠ none ∧ π₂ k ≠ none → π₁ k ≅ π₂ k

notation:51 π₁:52 " <≅> " π₂:52 => BalanceProof.compat π₁ π₂

notation:65 π₁:65 " <+> " π₂:66 => Dict.Merge π₁ π₂

@[simp]
lemma mergeR''_concat {π} {πs : List (BalanceProof K₁ K₂ C Pi V)} {acc} :
  mergeR'' (πs.concat π) acc = ((mergeR'' πs acc) <+> π) := by
    revert acc
    induction πs with
    | nil =>
      simp
    | cons π πs ih =>
      intros acc
      rw [mergeR''_cons, List.concat_cons, mergeR''_cons, ih, Dict.Merge_assoc]

section compat

@[symm]
lemma BalanceProof.compat_comm {π₁ π₂ : BalanceProof K₁ K₂ C Pi V} :
  π₁ <≅> π₂ ↔ π₂ <≅> π₁ := by unfold BalanceProof.compat; simp_rw [iso_symm]; tauto

@[simp]
lemma BalanceProof.compat_rfl {π₁ : BalanceProof K₁ K₂ C Pi V} :
  π₁ <≅> π₁ := by unfold BalanceProof.compat; tauto

lemma Merge_comm_of_compat {π₁ π₂ : BalanceProof K₁ K₂ C Pi V}
  (h : π₁ <≅> π₂) : π₁ <+> π₂ ≅ π₂ <+> π₁ := by
  apply proposition5'
  have := proposition6_aux h
  exact this
  unfold Dict.Merge Dict.Merge.D Dict.First
  have h₁ := BalanceProof.compat_comm.1 h
  intros x; specialize h x; specialize h₁ x
  aesop

lemma Merge_iso_of_iso {π₁ π₂ π₃ : BalanceProof K₁ K₂ C Pi V} (h : π₁ ≅ π₂) :
  π₁ <+> π₃ ≅ π₂ <+> π₃ := by
  simp [iso] at *
  unfold LE.le Preorder.toLE instPreorderBalanceProof id inferInstance _root_.Pi.preorder at *
  simp [inferInstanceAs, id, _root_.Pi.hasLe, -Prod.forall] at *
  rcases h with ⟨h₁, h₂⟩
  unfold Dict.Merge Dict.Merge.D Dict.First
  split_ands <;> intros x <;> specialize h₁ x <;> specialize h₂ x <;> aesop

lemma Merge_mergeR''_comm {πs : List (BalanceProof K₁ K₂ C Pi V)} (h : π <≅> acc) :
  acc <+> (mergeR'' πs π) ≅ π <+> (mergeR'' πs acc) := by
  induction' πs with hd tl ih generalizing acc
  · simp; exact Merge_comm_of_compat (BalanceProof.compat_comm.1 h)
  · simp
    rw [←Dict.Merge_assoc]
    rw [←Dict.Merge_assoc]
    exact Merge_iso_of_iso (Merge_comm_of_compat (BalanceProof.compat_comm.1 h))

lemma existsLUB_iff_compat {π₁ π₂ : BalanceProof K₁ K₂ C Pi V} :
  (∃ join, IsLUB {π₁, π₂} join) ↔ π₁ <≅> π₂ := proposition6

lemma le_of_iso {π₁ π₂ π₃ : BalanceProof K₁ K₂ C Pi V} (h : π₂ ≅ π₃) (h₁ : π₁ ≤ π₂) : π₁ ≤ π₃ :=
  le_trans h₁ h.1

lemma le_of_iso' {π₁ π₂ π₃ : BalanceProof K₁ K₂ C Pi V} (h : π₁ ≅ π₂) (h₁ : π₂ ≤ π₃) : π₁ ≤ π₃ :=
  le_trans h.1 h₁

@[simp]
lemma snd_eq_of_iso {d₁ d₂ : (Pi × ExtraDataT) × TransactionBatch K₁ K₂ V} :
  d₁.2 = d₂.2 ↔ (d₁ ≅ d₂) := by
  unfold iso
  simp [(·≤·)]
  tauto

lemma compat_comm {π π' : BalanceProof K₁ K₂ C Pi V} :
  (π <≅> π') ↔ π' <≅> π := by
  unfold BalanceProof.compat
  simp_rw [iso_symm]
  tauto

lemma compat_of_iso {π π' : BalanceProof K₁ K₂ C Pi V}
  (h : π ≅ π') : π <≅> π' := by
  intros x y
  simp [iso] at h
  unfold LE.le Preorder.toLE instPreorderBalanceProof id inferInstance _root_.Pi.preorder at h
  simp [-Prod.forall, inferInstanceAs, _root_.Pi.hasLe] at h
  rcases h with ⟨h₁, h₂⟩
  specialize h₁ x
  specialize h₂ x
  unfold iso
  tauto

lemma isLUB_of_isLUB_iso {π π' : BalanceProof K₁ K₂ C Pi V}
  (h : IsLUB A π) (h₁ : π ≅ π') : IsLUB A π' := by
  simp only [IsLUB, IsLeast, upperBounds, Set.mem_setOf_eq, lowerBounds] at *
  rcases h with ⟨h₂, h₃⟩
  split_ands
  · intros X hX
    have : X ≤ π := h₂ hX
    exact le_trans this h₁.1
  · intros X hX
    specialize h₃ hX
    exact le_trans h₁.2 h₃

end compat

lemma merge_le {π₁ π₂ π₃ : BalanceProof K₁ K₂ C Pi V}
  (h₁ : π₁ ≤ π₃) (h₂ : π₂ ≤ π₃) : π₁ <+> π₂ ≤ π₃ := by
  have h₃ : π₁ <≅> π₂ := by
    intros k hk
    simp [-Prod.forall, (·≤·)] at h₁ h₂
    specialize h₁ k
    specialize h₂ k
    aesop (config := {warnOnNonterminal := false})
    exact iso_trans h₁ h₂.symm
  obtain ⟨π, hπ⟩ := existsLUB_iff_compat.2 h₃
  have hπ' := hπ
  apply proposition6' at hπ
  have eq₁ : π₁ ≤ π := by unfold IsLUB IsLeast upperBounds lowerBounds at hπ'; aesop
  have eq₂ : π₂ ≤ π := by unfold IsLUB IsLeast upperBounds lowerBounds at hπ'; aesop
  transitivity π
  exact hπ.symm.1
  have eq₃ := hπ.2
  unfold IsLUB IsLeast upperBounds lowerBounds at hπ'
  rcases hπ' with ⟨hπ₁, hπ₂⟩
  simp at hπ₂
  apply hπ₂ <;> assumption

lemma isLUB_union_Merge_of_isLUB_isLUB_compat {A B : Set (BalanceProof K₁ K₂ C Pi V)}
  (h₁ : IsLUB A j₁) (h₂ : IsLUB B j₂) (h₃ : j₁ <≅> j₂) : IsLUB (A ∪ B) (j₁ <+> j₂) := by
  have h₃'' := h₃
  obtain ⟨j, h₃⟩ := existsLUB_iff_compat.2 h₃
  split_ands
  · simp only [IsLUB, IsLeast, upperBounds, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq, Set.mem_setOf_eq, lowerBounds, and_imp, Set.mem_union] at h₁ h₂ h₃ ⊢
    rcases h₁ with ⟨h₁, h₁'⟩
    rcases h₂ with ⟨h₂, h₂'⟩
    rintro D₁ (hD₁ | hD₂)
    · simp [-Prod.forall, (·≤·)]
      intros x
      unfold Dict.Merge Dict.Merge.D Dict.First
      specialize h₁ hD₁
      simp [-Prod.forall, (·≤·)] at h₁
      specialize h₁ x
      set d₁ := D₁ x with eqX
      set d₂ := j₁ x with eqY
      set d₃ := j₂ x with eqZ
      rcases d₁ with _ | d₁ <;> rcases d₂ with _ | d₂ <;> rcases d₃ with _ | d₃ <;> simp
      · simp at h₁
      · simp at h₁
      · simp at h₁
        exact h₁
      · simp at h₁
        exact h₁
    · simp only [LE.le, discretePreorder_eq_equality_Pi_Prod_ExtraDataT, BalanceProof.snd_discrete,]
      intros x
      unfold Dict.Merge Dict.Merge.D Dict.First
      have eq₂ : D₁ ≤ j₂ := h₂ hD₂
      simp [-Prod.forall, (·≤·)] at eq₂
      specialize eq₂ x
      set d₁ := D₁ x with eqX
      set d₂ := j₁ x with eqY
      set d₃ := j₂ x with eqZ
      rcases d₁ with _ | d₁ <;> rcases d₂ with _ | d₂ <;> rcases d₃ with _ | d₃ <;> simp
      · simp at eq₂
      · simp at eq₂
        exact eq₂
      · simp at eq₂
      · simp at eq₂
        specialize h₃'' x
        rw [←eqY, ←eqZ] at h₃''
        simp at h₃''
        exact iso_trans eq₂ h₃''.symm
  · exact λ _ hπ ↦ merge_le (h₁.right λ _ hd ↦ hπ (by tauto))
                            (h₂.right λ _ hd ↦ hπ (by tauto))

@[simp]
lemma merge_eq_none {π acc : BalanceProof K₁ K₂ C Pi V} :
  (π <+> acc) K = none ↔ π K = none ∧ acc K = none := by
  unfold Dict.Merge Dict.Merge.D Dict.First; aesop

@[simp]
lemma mergeR''_eq_none' {acc : BalanceProof K₁ K₂ C Pi V} {πs} :
  (mergeR'' πs acc) K = none ↔ acc K = none ∧ ∀ π ∈ πs, π K = none := by
  induction' πs with hd tl ih generalizing acc <;> aesop

lemma merge_K {π acc : BalanceProof K₁ K₂ C Pi V} :
  (π <+> acc) K = Dict.First (π K) (acc K) := rfl

@[simp]
lemma mergeR''_eq_some {acc : BalanceProof K₁ K₂ C Pi V} {πs} {x} :
  acc K = some x → (mergeR'' πs acc) K = acc K := by
  revert acc
  induction πs with
  | nil => simp
  | cons π πs ih =>
    intros acc h
    rw [mergeR''_cons, merge_K, h]
    unfold Dict.First
    aesop

lemma iso_K_merge_left_of_ne_none {π acc : BalanceProof K₁ K₂ C Pi V} (h : π K ≠ none) :
  π K ≅ (π <+> acc) K := by
  rw [merge_K]
  unfold Dict.First
  aesop

lemma merge_left_none_eq_right {π acc : BalanceProof K₁ K₂ C Pi V} (h : π K = none) :
  (π <+> acc) K = acc K := by
  rw [merge_K]
  unfold Dict.First
  aesop

lemma iso_K_merge_right_of_ne_none_compat {π acc : BalanceProof K₁ K₂ C Pi V} (h : π K ≠ none) (h : π <≅> acc) :
  π K ≅ (acc <+> π) K := by
  unfold BalanceProof.compat at h
  specialize h K
  rw [merge_K]
  unfold Dict.First
  aesop

lemma iso_K_of_iso {π acc : BalanceProof K₁ K₂ C Pi V} (h : π ≅ acc) : π K ≅ acc K := by
  unfold iso LE.le Preorder.toLE instPreorderBalanceProof id inferInstance _root_.Pi.preorder inferInstanceAs _root_.Pi.hasLe at h
  simp [-Prod.forall] at h
  tauto

lemma mergeR_eq_left {acc : BalanceProof K₁ K₂ C Pi V}
  (h : ∀ k, acc k ≠ none) : mergeR'' πs acc = acc := by
  unfold mergeR''
  rcases πs with _ | ⟨π, πs⟩
  · simp
  · simp
    rw [Dict.keys_Merge_left']
    simp_rw [Dict.mem_iff_isSome, Option.isSome_iff_ne_none]
    exact h

lemma mergeR''_split {acc} {πs : List (BalanceProof K₁ K₂ C Pi V)} (h : πs.length ≠ 0) :
  mergeR'' πs acc = acc <+> (πs.head (by aesop)) <+> mergeR'' πs.tail .initial := by
  nth_rw 1 [mergeR''.eq_def]
  rcases πs with _ | ⟨hd, tl⟩ <;> [simp at h; simp]
  rcases tl <;> simp [Dict.Merge_assoc]

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

variable [AD : ADScheme K₂ (C × K₁ × ExtraDataT) C Pi]

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
    · apply verify_merge_of_valid h₀ (ih ..) <;> aesop

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

lemma batch_eq_iff {π₁k π₂k : (Pi × ExtraDataT) × TransactionBatch K₁ K₂ V} :
  (π₁k ≅ π₂k) ↔ π₁k.2 = π₂k.2 := by
  unfold iso
  simp [(·≤·)]
  rw [iso_symm]
  tauto

lemma Merge_split {acc} {πs : List (BalanceProof K₁ K₂ C Pi V)} (h₀ : 0 < i) (h₁ : i ≤ πs.length) :
  mergeR'' (πs.take i) acc =
  mergeR'' (πs.take (i - 1)) acc <+> πs[i - 1] := by
  induction' i with i ih generalizing πs acc
  · cases h₀
  · rcases i with _ | i <;> rcases πs with _ | ⟨π, πs⟩ <;> simp at h₁ <;> simp
    have := (Dict.Merge_assoc (D₁ := acc) (D₂ := mergeR'' (List.take i πs) π) (D₃ := πs[i])).symm
    aesop

private lemma merge_lem_aux {π : BalanceProof K₁ K₂ C Pi V} {πs : List (BalanceProof K₁ K₂ C Pi V)} :
  mergeR'' (π :: πs) acc = acc <+> π <+> (mergeR'' πs BalanceProof.initial) := by
  rcases πs with ⟨hd, tl⟩ <;> simp [Dict.Merge_assoc]

lemma merge_lem {π : BalanceProof K₁ K₂ C Pi V} {πs : List (BalanceProof K₁ K₂ C Pi V)} :
  mergeR'' (π :: πs) BalanceProof.initial = π <+> (mergeR'' πs BalanceProof.initial) := by
  rw [merge_lem_aux]; simp

lemma compat_lem {π π' π'': BalanceProof K₁ K₂ C Pi V} :
  π <≅> π' → π <≅> π'' → π <≅> (π' <+> π'') := by
  unfold BalanceProof.compat Dict.Merge Dict.Merge.D Dict.First
  rintro h h' k ⟨h₁, h₂⟩
  specialize h k
  specialize h' k
  aesop

lemma compat_merge_of_compat {πs : List (BalanceProof K₁ K₂ C Pi V)} {π : BalanceProof K₁ K₂ C Pi V} :
  (∀ π', π' ∈ πs → π <≅> π') → π <≅> (mergeR'' πs .initial) := by
  revert π
  induction πs with
  | nil =>
    intros π
    unfold BalanceProof.compat BalanceProof.initial
    simp
  | cons π πs ih =>
    intros π_1 h
    rw [merge_lem]
    apply compat_lem <;> aesop

private lemma prop6?!_aux {πs : List (BalanceProof K₁ K₂ C Pi V)} :
  (∀ π π' : BalanceProof K₁ K₂ C Pi V, π ∈ πs ∧ π' ∈ πs → π <≅> π') →
     IsLUB {π | π ∈ πs} (mergeR'' πs .initial) := by
  induction πs with
  | nil => simp
  | cons π πs ih =>
    intros h
    have : (∀ (π π' : BalanceProof K₁ K₂ C Pi V), π ∈ πs ∧ π' ∈ πs → π <≅> π') := by aesop
    specialize ih this
    rw [merge_lem, show {π_1 | π_1 ∈ π :: πs} = {π} ∪ {π_1 | π_1 ∈ πs} by aesop]
    apply isLUB_union_Merge_of_isLUB_isLUB_compat <;> aesop (add safe apply compat_merge_of_compat)

set_option maxHeartbeats 800000 in
lemma prop6?! {πs : List (BalanceProof K₁ K₂ C Pi V)}
              (h : ∀ i : Fin πs.length,
                     IsLUB {mergeR'' (πs.take i.1) .initial, πs[i.1]} (mergeR'' (πs.take (i.1 + 1)) .initial))
  : IsLUB {π | π ∈ πs} (mergeR'' πs .initial) := by
  replace h : ∀ (i : ℕ) (h : i < πs.length),
                IsLUB {mergeR'' (List.take i πs) .initial, πs[↑i]}
                      (mergeR'' (List.take (i + 1) πs) .initial) := λ i hi ↦ h ⟨i, hi⟩
  apply prop6?!_aux
  by_contra contra
  simp at contra
  let min₁ : Finset (Fin πs.length) := {n | ∃ i, n < i ∧ ¬(πs[n] <≅> πs[i])}
  have wa_ne : min₁.Nonempty := by
    rcases contra with ⟨π, ⟨π_in_πs, ⟨π', ⟨π'_in_πs, h⟩⟩⟩⟩
    obtain ⟨π_ind, π_ind_lim, π_in_πs⟩ := List.getElem_of_mem π_in_πs
    obtain ⟨π'_ind, π'_ind_lim, π'_in_πs⟩ := List.getElem_of_mem π'_in_πs
    by_cases h' : π_ind < π'_ind
    · simp_all only [List.getElem_mem, Set.toFinset_setOf, gt_iff_lt, Fin.getElem_fin, min₁]
      rw [Finset.filter_nonempty_iff]; simp only [Finset.mem_univ, true_and]
      use ⟨π_ind, by omega⟩; use ⟨π'_ind, by omega⟩
      aesop
    · rewrite [not_lt] at h'
      rcases eq_or_lt_of_le h' with h' | h'
      · exfalso; aesop
      · simp_all only [List.getElem_mem, Set.toFinset_setOf, gt_iff_lt, Fin.getElem_fin, min₁]
        rw [Finset.filter_nonempty_iff]; simp only [Finset.mem_univ, true_and]
        use ⟨π'_ind, by omega⟩; use ⟨π_ind, by omega⟩
        subst π_in_πs; subst π'_in_πs
        simp [h']; rw [compat_comm]; assumption
  have wa_min : ∃ idx, idx ∈ min₁ ∧ ∀ k ∈ min₁, idx ≤ k := by
    rcases Finset.exists_minimal min₁ wa_ne with ⟨idx, h₁, h₂⟩; use idx; aesop
  rcases wa_min with ⟨idx, idx_min_wa⟩
  let π := πs[idx]
  let min₂ : Finset (Fin πs.length) := {idx' | idx < idx' ∧ ¬(πs[idx'] <≅> πs[idx])}
  have min₂_ne : min₂.Nonempty := by
    rw [Finset.filter_nonempty_iff]; simp_rw [compat_comm]; aesop
  have min₂_min : ∃ idx', idx' ∈ min₂ ∧ ∀ k ∈ min₂, idx' ≤ k := by
    rcases Finset.exists_minimal min₂ min₂_ne with ⟨idx, h₁, h₂⟩; use idx; aesop
  rcases min₂_min with ⟨idx', idx'_min_min₂⟩
  have idx_lt_idx' : idx < idx' := by simp [min₂] at idx'_min_min₂; tauto
  have eq₁' : ∀ i, idx ≤ i ∧ i < idx' → πs[i] <≅> πs[idx] := by
    by_contra h
    simp only [Fin.getElem_fin, and_imp, not_forall, Classical.not_imp] at h
    rcases h with ⟨i, h, h', h''⟩
    have : i ∈ min₂ := by
      dsimp [min₂]
      simp only [Finset.mem_filter, Finset.mem_univ, h'', not_false_eq_true, and_true, true_and]
      rcases eq_or_lt_of_le h <;> aesop
    exact absurd (Fin.lt_of_le_of_lt (idx'_min_min₂.2 i this) h') (lt_irrefl _)
  have eq₁'' : ∀ i, i < idx → πs[i] <≅> πs[idx] := by
    intros i h
    by_contra contra
    have : i ∈ min₁ := by
      dsimp [min₁]
      simp only [gt_iff_lt, Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and]
      use idx
      exact ⟨h, contra⟩
    exact absurd (Fin.lt_of_lt_of_le h (idx_min_wa.2 i this)) (lt_irrefl _)
  have eq₁ : ∀ i, i < idx' → πs[i] <≅> πs[idx] := by
    intros i h; by_cases h' : idx ≤ i <;> aesop
  have eq₂ : ¬(πs[idx] <≅> πs[idx']) := by
    rw [compat_comm]; aesop
  have eq₃ : ∃ k : C × K₂, ¬(πs[idx] k ≅ πs[idx'] k) ∧ πs[idx] k ≠ .none ∧ πs[idx'] k ≠ .none := by
    unfold BalanceProof.compat at eq₂
    simp only [Fin.getElem_fin, ne_eq, and_imp, Prod.forall, not_forall, Classical.not_imp] at eq₂
    rcases eq₂ with ⟨k₁, k₂, h₁, h₂, h⟩
    use ⟨k₁, k₂⟩
    exact ⟨h, h₁, h₂⟩
  rcases eq₃ with ⟨k, eq₃⟩
  have eq₄ : ∀ i, i < idx' → πs[idx] k ≅ πs[i] k ∨ πs[i] k = .none := by
    intros i h
    unfold BalanceProof.compat at eq₁ eq₃
    simp only [Fin.getElem_fin] at eq₃
    specialize eq₁ i h k
    rw [iso_symm]
    by_cases h' : πs[i] k = .none <;> tauto
  specialize h idx'.1 (by simp)
  have eq₅ : mergeR'' (πs.take (idx.1 + 1)) .initial k ≅ πs[idx] k := by
    have eq₆' : ∀ i, i < idx.1 + 1 ∧ i < πs.length →
      mergeR'' (List.take i πs) .initial k ≅ (πs[idx]) k ∨ mergeR'' (List.take i πs) .initial k = .none := by
      intros i h
      induction i with
      | zero => right; rfl
      | succ i ih =>
        have : i < πs.length := by linarith
        rw [←List.take_concat_get _ _ this, mergeR''_concat]
        rcases ih ⟨by linarith, by linarith⟩ with ih | ih
        · left
          refine iso_trans ?_ ih
          rw [iso_symm]
          apply iso_K_merge_left_of_ne_none
          by_contra h
          rw [h] at ih
          obtain ⟨_, h⟩ := Option.ne_none_iff_exists.1 eq₃.2.1
          rwa [←h, none_iso_some] at ih
        · rw [merge_left_none_eq_right ih, iso_symm,
              show πs[i] = πs[((⟨i, by linarith⟩) : Fin πs.length)] from rfl]
          apply eq₄
          simp only [Fin.lt_def] at idx_lt_idx' ⊢
          exact lt_trans (by omega) idx_lt_idx'
    rw [←List.take_concat_get (h := idx.2), mergeR''_concat]
    rcases eq₆' idx.1 ⟨by simp only [lt_add_iff_pos_right, zero_lt_one], idx.2⟩ with h | h
    · refine iso_trans ?_ h
      rw [iso_symm]
      apply iso_K_merge_left_of_ne_none
      by_contra h'
      obtain ⟨_, h''⟩ := Option.ne_none_iff_exists.1 eq₃.2.1
      rwa [h', ←h'', none_iso_some] at h
    · rw [merge_left_none_eq_right h]
      rfl
  have eq₆ : mergeR'' (πs.take (idx.1 + 1)) .initial k ≅ mergeR'' (πs.take idx'.1) .initial k := by
    have : idx.1 + 1 ≤ idx'.1 := by
      rw [Fin.lt_def] at idx_lt_idx'
      linarith
    rcases Nat.exists_eq_add_of_le this with ⟨i, h⟩
    rw [h, List.take_add (m := idx.1 + 1), mergeR''_append]
    have : ∃ r, mergeR'' (List.take (idx.1 + 1) πs) BalanceProof.initial k = .some r := by
      by_contra h
      simp at h
      have : mergeR'' (List.take (idx.1 + 1) πs) BalanceProof.initial k = .none := by
        by_contra h'
        have h' := Option.ne_none_iff_exists.1 h'
        rcases h' with ⟨x, h'⟩
        specialize h x.1.1 x.1.2 x.2
        apply h
        rw [←h']
      rw [this] at eq₅
      rcases Option.ne_none_iff_exists.1 eq₃.2.1 with ⟨x, h''⟩
      rw [←h'', none_iso_some] at eq₅
      exact eq₅
    rcases this with ⟨_, h⟩
    rw [mergeR''_eq_some h]
  have eq₇ : (πs[idx]) k ≅ mergeR'' (List.take idx'.1 πs) BalanceProof.initial k :=
    iso_trans (eq₅.symm) eq₆
  have eq₈ : ¬(mergeR'' (πs.take idx'.1) .initial <≅> πs[idx']) := by
    unfold BalanceProof.compat
    simp only [ne_eq, mergeR''_eq_none', not_and, not_forall, Classical.not_imp, Fin.getElem_fin, and_imp]
    use k; simp at eq₃
    simp [eq₃, BalanceProof.initial]
    refine' ⟨_, λ contra' ↦ absurd (iso_trans eq₇ contra') eq₃.1⟩
    use π; simp [π]
    refine' ⟨_, eq₃.2.1⟩
    rw [List.mem_take_iff_getElem]
    simp only [Fin.is_le', inf_of_le_left]
    use idx.1
    simp [min₂] at idx'_min_min₂
    use idx'_min_min₂.1.1
  unfold BalanceProof.compat at eq₈
  rw [←proposition6] at eq₈
  exact absurd (by tauto) eq₈ 

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
  (h : ¬(π₁k ≅ π₂k)) : (π₁k.get (Option.isSome_iff_ne_none.2 h₀.1)).2 ≠
                       (π₂k.get (Option.isSome_iff_ne_none.2 h₀.2)).2 := by
  rcases π₁k <;> rcases π₂k <;> aesop

variable [SA : SignatureAggregation (C × K₁ × ExtraDataT) K₂ KₛT Sigma]
         [Hinj : CryptoAssumptions.Injective (H (α := TransactionBatch K₁ K₂ V × ExtraDataT) (ω := (C × K₁ × ExtraDataT)))]
         {requests : List (Request K₁ K₂ C Sigma Pi V)}
         (isπ : isπ (normalise requests))

set_option hygiene false in
open Lean.Elab.Tactic Lean.Parser.Tactic in
scoped elab "blast_sum" "with" f:ident l:(location)? : tactic => do
  evalTactic <| ← `(tactic| (
    rw [Finset.sum_congr (s₂ := indexingSet) (g := $f) (h := by first | rfl | simp [indexingSet])
                         (by simp [
                               isπ, $f:ident, BalanceProof.toBalanceF,
                               πᵢ, List.lookup_graph, eqπs, hgetπ])] $[$l]?))

set_option linter.unusedVariables false in
omit Hinj in
private theorem not_adversaryWon_attackGame_of_exists_LUB
  (eqrequests : requests! = normalise requests)
  (hValid     : ∀ request ∈ requests!, request.isValid)
  (eqI        : I = (List.finRange (attackGameR requests! []).length).filter ((attackGameR requests! [])[·].isWithdrawalBlock))
  (hI         : ∀ {i : Fin (attackGameR requests! []).length}, i ∈ I ↔ (attackGameR requests! [])[i].isWithdrawalBlock)
  (hgetπ      : getπ =
                λ i : {i : Fin (attackGameR requests! []).length // i ∈ I} ↦
                  (i, getBalanceProof requests! hValid ⟨i.1.1, i.1.2⟩ (hI.1 i.2)))
  (eqπs       : πs = I.attach.map getπ)
  (hlen       : πs.length ≤ n)
  (hπs        : ∀ (i : {i // i ∈ I}), (List.lookup i πs).isSome)
  (eqπproofs  : πproofs = πs.map Prod.snd)
  (πproofslen : πproofs.length = πs.length)
  (isπ        : ∀ (i : Fin (List.length (attackGameR requests! [])))
                  (h : (attackGameR requests! [])[i.1].isWithdrawalBlock),
                  (attackGameR requests! [])[i.1].getWithdrawal h =
                  (getBalanceProof requests! hValid i h).toBalanceF ((attackGameR requests! []).take i.1))
  (contra     : ¬0 ≤ computeBalanceSum (attackGameR requests! []))
  (existsLUB  : ∃ join, IsLUB {π | π ∈ πproofs} join) : False := by
  · rcases existsLUB with ⟨π, hπ₂⟩
    set Bstar := attackGameR requests! [] with eqBstar
    have hlub {π'} (h' : π' ∈ πproofs) : π' ≤ π := mem_upperBounds.1 hπ₂.1 _ h'
    /-
      PAPER: step lemma 3
    -/
    have eq₁ : 0 ≤ -Bal π Bstar .Source := by
      have : Bal π Bstar .Source ≤ 0 := lemma3; simpa
    /-
      PAPER: step lemma 5
    -/
    rw [lemma5] at eq₁; simp only at eq₁
    let indexingSet := Finset.univ (α := Fin Bstar.length) ×ˢ Finset.univ (α := K₁)
    let σ := λ x : Fin Bstar.length × K₁ ↦ Bstar.take x.1.1
    let πᵢ := λ (x : Fin Bstar.length × K₁) (h : Bstar[x.1].isWithdrawalBlock) ↦
                (πs.lookup ⟨x.1, hI.2 h⟩).get (hπs ⟨x.1, hI.2 h⟩)
    have hπᵢ {x} (h) : πᵢ x h ∈ πproofs := by
      simp [πᵢ, eqπs, eqπproofs, List.lookup_graph, hgetπ]
      exact ⟨_, ⟨hI.2 h, rfl⟩⟩
    let F : Fin Bstar.length × K₁ → V :=
      λ x ↦ if h : Bstar[x.1].isWithdrawalBlock
            then Bal (πᵢ x h) (σ x) x.2 ⊓ Bal π (σ x) x.2
            else 0
    blast_sum with F at eq₁
    simp only [Fin.getElem_fin, F] at eq₁
    let F : Fin Bstar.length × K₁ → V :=
      λ x ↦ if h : Bstar[x.1].isWithdrawalBlock
            then Bal (πᵢ x h) (σ x) x.2
            else 0
    /-
      PAPER: step lemma 4

      NB `contra` takes this shape because of `computeBalance_eq_sum`.
    -/
    rw [Finset.sum_congr (s₂ := indexingSet) (g := F) (h := rfl)
                         (by simp [F]; intros idx k₁ h
                             split <;> try simp
                             next h' =>
                               have := lemma4 (bs := (σ (idx, k₁))) (show πᵢ (idx, k₁) h' ≤ π from hlub (hπᵢ h'))
                               simp [(·≤·)] at this; apply this)] at eq₁
    simp only [
      computeBalanceSum, aggregateWithdrawals_eq_aggregateWithdrawals', aggregateWithdrawals'
    ] at contra
    blast_sum with F at contra
    simp at eq₁ contra; contradiction

include isπ in
set_option maxHeartbeats 2000000 in
/--
NB We take `isπ` to be the behaviour of the rollup contract. This is actually provable from the model.
-/
theorem theorem1 : ¬adversaryWon (attackGame requests) := λ contra ↦ by
  /-
    PAPER: Suppose an adversary and a challenger have interacted in Attack game 1.
    We will show that either the resulting contract balance is positive (the adver-
    sary lost the game), or the adversary has been able to either break the bind-
    ing property of the authenticated dictionary scheme or found a collision of the
    hash function H.
  -/

  /-
    The attack game plays out the same regardless of validity of requests.
  -/
  rw [attackGame_eq_attackGameBlocks!_normalise, attackGameBlocks_eq_attackGameR] at contra
  set requests! := normalise requests with eqRequests
  /-
    PAPER: Let B∗ = (Bi)i∈[n] be the contract state after the attack game
  -/
  set Bstar := attackGameR requests! [] with eqBstar
  /-
    As such, we can consider a state with only valid requests.
  -/
  have hValid : ∀ request ∈ (normalise requests), request.isValid := by unfold normalise; aesop
  let n := Bstar.length
  have hValidπ {i : Fin n} {h₀} {h₁} {π} (h : (requests![i.1]'h₀).getWithdrawal.get h₁ = π) :
    π.Verify (M := (C × K₁ × ExtraDataT)) := by
    rcases i with ⟨i, hi⟩
    unfold Request.isValid at hValid
    set request := requests![i] with eqRequest
    specialize hValid request (by simp [eqRequest, requests!])
    have hValid_withdrawal {h₀} (h : (requests![i]'h₀).getWithdrawal.isSome) :
      requests![i]'h₀ matches .withdrawal .. := by
      simp [Request.getWithdrawal] at h
      aesop
    aesop
  have hn : n = requests!.length := by simp [n, eqBstar]
  /-
    PAPER: let I ⊆ [n] be the indices of the withdrawal blocks in B∗
  -/
  let I : List (Fin n) := (List.finRange n).filter (Bstar[·].isWithdrawalBlock)
  have hI : ∀ i, i ∈ I ↔ Bstar[i].isWithdrawalBlock := by aesop
  let getπ : {i : Fin n // i ∈ I} → ({i : Fin n // i ∈ I} × BalanceProof K₁ K₂ C Pi V) :=
    λ i ↦
      have lenEq : Bstar.length = n := by simp [n, eqBstar]
      have hi₁ : i.1.1 < Bstar.length := by rw [lenEq]; exact i.1.2
      (i, getBalanceProof requests! hValid ⟨i.1.1, hi₁⟩ ((hI i.1).1 i.2))
  let πs : List ({i : Fin n // i ∈ I} × BalanceProof K₁ K₂ C Pi V) := I.attach.map getπ
  have lenπs : πs.length ≤ n := by
    simp [πs, I, n]
    simp_rw [show Bstar.length = (List.finRange (List.length Bstar)).length by aesop]
    exact List.length_filter_le _ _
  have hπs : ∀ i : {i : Fin n // i ∈ I}, (πs.lookup i).isSome := λ i ↦
    have : i ∈ I.attach := by rcases i with ⟨i, hi⟩; aesop
    by simp [πs, getπ, List.lookup_graph _ this]
  /-
    PAPER: (πi)i∈I be the balance proofs used in the withdrawal request
  -/
  let πproofs := πs.map Prod.snd
  have lenπs': πproofs.length = πs.length := by simp [πproofs]
  have validπs {π : BalanceProof K₁ K₂ C Pi V} (h : π ∈ πproofs) :
               π.Verify (M := (C × K₁ × ExtraDataT)) := by
    simp [πs, πproofs] at h; rcases h with ⟨π, _, hπ⟩
    exact hValidπ hπ
  unfold Intmax.isπ at isπ; specialize isπ hValid; dsimp at isπ
  /-
    PAPER: The resulting contract balance can be computed by adding all deposited amounts and subtracting all withdrawn amounts:
    NB we prove 
  -/
  dsimp [adversaryWon] at contra; simp [computeBalance_eq_sum] at contra
  /-
    PAPER: We now have two possibilities, either the balance proofs (πi)i∈I have a join in Π or they don’t.
  -/
  by_cases eq : ∃ join : BalanceProof K₁ K₂ C Pi V, IsLUB {π | π ∈ πproofs} join
  · -- PAPER: Suppose they have a join π ∈ Π. Then we have cf. `not_adversaryWon_attackGame_of_exists_LUB`.
    exact not_adversaryWon_attackGame_of_exists_LUB
            eqRequests
            hValid
            (I := I) (by simp only [Fin.getElem_fin, I])
            (by simp only [hI]; intros; trivial)
            (getπ := getπ) (by simp only [getπ])
            (πs := πs) (by simp only [πs])
            lenπs
            hπs
            (πproofs := πproofs) (by simp only [πproofs])
            lenπs'
            isπ
            contra
            eq
  · /-
      PAPER: Now, suppose the balance proofs (πi)i∈I do not have a join in Π.
    -/
    /-
      PAPER: Let ik be the k′th index in I (so that I = {i1, i2, . . . , im}, where m = |I|).
             Then, let (π′ k)k∈{1,...,m} be the balance proofs defined recursively as π′1 = πi1 and π′
             k = Merge(π′k−1, πik ).

      NB we define `πs'` to be an ordered sequence of balance proofs with the `.initial` balance proof
      at the head position. Note further we use a slightly different merging scheme; one can
      compare `mergeR` and `mergeR''`, where the former is the definition from the paper, while
      the latter is the one we use.
    -/
    let πs' := List.Ico 0 (πs.length + 1) |>.map λ i ↦ mergeR'' (πproofs.take i) .initial
    have lenπs'': πs'.length = πs.length + 1 := by simp [πs', lenπs']
    /-
      PAPER: Clearly, these merged balance proofs are valid, since each of the original bal-
             ance proofs are valid (otherwise they wouldn’t be accepted by the rollup con-
             tract), and since the merge of two valid balance proofs is again valid.

      NB the relevant proof is `valid_mergeR''`.
    -/
    have hπs' : ∀ π ∈ πs', π.Verify (M := (C × K₁ × ExtraDataT)) := by
      simp [πs', πproofs]; intros n hn
      exact valid_mergeR'' (by simp; omega) (λ _ hx ↦ validπs hx)
    have recπs' : ∀ {i : ℕ} (hi : i < πs'.length), πs'[i] = mergeR'' (πproofs.take i) .initial :=
      by simp [πs', πproofs]; intros i hi; rw [List.getElem_Ico_of_lt hi]
    let m := πs'.length.pred
    have hm : m = πproofs.length := by simp [m, lenπs', lenπs'']
    set π'ₘ := πs'[m]'(by simp [m]; omega) with eqπ'ₘ
    simp only [not_exists] at eq
    /-
      With no withdrawal requests, one can derive an immediate contradiction by showing that
      the `.initial` balance proof is the least upper bound, which had been assumed not to exist.
    -/
    by_cases isempty : πs.length = 0
    · have : πproofs = [] := List.map_eq_nil_iff.2 (List.eq_nil_of_length_eq_zero isempty)
      simp_rw [this] at eq
      specialize eq .initial
      simp at eq
    · /-
        PAPER: Now, we argue that there must be an index k ∈ {1, . . . , m} such that π′k is not the join
        of π′k−1 and πik in Π, since if not, the final merged balance proof π′m would
        be a join of (πi)i∈I (by Proposition 6), which we have assumed not to exist.
      -/
      have idx : ∃ i : {n : ℕ // 0 < n ∧ n < πs'.length},
                 ¬IsLUB {
                    πs'[i.1-1],
                    πproofs[i.1-1]'(Nat.sub_one_lt_of_le i.2.1 (Nat.le_of_lt_add_one (by rw [lenπs', lenπs''.symm]; exact i.2.2)))
                  } (πs'[i.1]'i.2.2) := by
        by_contra c; simp at c
        specialize eq π'ₘ; simp only [eqπ'ₘ] at eq
        simp_rw [recπs' (i := m), show List.take m πproofs = πproofs by simp [hm]] at eq
        have : IsLUB {π | π ∈ πproofs} (mergeR'' πproofs .initial) := by
          apply prop6?!
          rintro ⟨i, hi⟩
          simp only
          simp_rw [recπs'] at c; specialize c (i + 1) (by omega); simp at c
          exact c
        exact absurd this eq
      rcases idx with ⟨⟨i, hi₁, hi₂⟩, lubi⟩; simp only at lubi
      /-
        PAPER: It then follows from Proposition 6 that there is a key (C, s) ∈ AD.C × K2 such that π′
        k−1(C, s)̸ ≃ πik (C, s).
      -/
      let π₁! := πs'[i-1]'(by omega)
      let π₂! := πproofs[i-1]'(by simp [hm.symm, m]; omega)
      have eq₁ : ∃ key : {k : C × K₂ // π₁! k ≠ .none ∧ π₂! k ≠ .none}, ¬(((π₁! key.1) ≅ (π₂! key.1))) := by
        simp only [π₁!, π₂!, id_eq, Int.Nat.cast_ofNat_Int, Int.reduceNeg, Nat.pred_eq_sub_one, Int.reduceAdd,
          eq_mpr_eq_cast, Subtype.exists]
        by_contra c; simp only [Int.reduceNeg, not_exists, Decidable.not_not] at c
        apply proposition6_aux at c
        simp_rw [recπs' (i := i)] at lubi
        rw [Merge_split hi₁ (by omega)] at lubi
        nth_rw 2 [recπs' (i := i - 1)] at c
        contradiction
      rcases eq₁ with ⟨⟨key, mem₁, mem₂⟩, hkey⟩
      set π₁ := (π₁! key).get (Option.isSome_iff_ne_none.2 mem₁) with eqπ₁
      set π₂ := (π₂! key).get (Option.isSome_iff_ne_none.2 mem₂) with eqπ₂
      rcases key with ⟨c, s⟩
      rcases π₁ with ⟨⟨π, salt⟩, t⟩
      have π₁valid : AD.Verify π s (H _ (t, salt)) c := by
        have : π₁!.Verify (M := (C × K₁ × ExtraDataT)) := hπs' _ (by simp [π₁!])
        simp [BalanceProof.Verify] at this; simp_rw [←Dict.mem_dict_iff_mem_keys] at this
        specialize this c s (Option.isSome_iff_ne_none.2 mem₁)
        convert this <;> rw [←eqπ₁]
      rcases π₂ with ⟨⟨π', salt'⟩, t'⟩
      have π₂valid : AD.Verify π' s (H _ (t', salt')) c := by
        have : π₂!.Verify (M := (C × K₁ × ExtraDataT)) := validπs (by simp [π₂!])
        simp [BalanceProof.Verify] at this; simp_rw [←Dict.mem_dict_iff_mem_keys] at this
        specialize this c s (Option.isSome_iff_ne_none.2 mem₂)
        convert this <;> rw [←eqπ₂]
      have tneq : t ≠ t' := by apply batch?_neq_of_mem (by simp; exact ⟨mem₁, mem₂⟩) at hkey; simp [←eqπ₁, ←eqπ₂] at hkey; exact hkey
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

end theorem1

end Intmax

end Intmax

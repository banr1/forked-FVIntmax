import Mathlib.Algebra.Order.Ring.Unbundled.Nonneg

import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finmap
import Mathlib.Data.Set.Image
import Mathlib.Logic.Embedding.Basic

import Mathlib.Tactic

import FVIntmax.Wheels.Wheels

namespace Intmax

class abbrev Nonnegative (α : Type) := Preorder α, Zero α

section UniquelyIndexed

abbrev UniqueTokenT (α : Type) [Finite α] : Type := Fin (Finite.exists_equiv_fin α |>.choose)

prefix:max "!" => UniqueTokenT

abbrev UniquelyIndexed (α : Type) [Finite α] : Type := α ↪ !α

namespace UniquelyIndexed

noncomputable def attach (α : Type) [Finite α] : UniquelyIndexed α :=
  have := Finite.exists_equiv_fin α
  this.choose_spec.some.toEmbedding

noncomputable instance {α : Type} [Finite α] : Inhabited (UniquelyIndexed α) := ⟨attach α⟩

@[simp]
lemma default_eq_attach (α : Type) [Finite α] : (default : UniquelyIndexed α) = attach α :=
  rfl

theorem injective {α : Type} [Finite α]
  (f : UniquelyIndexed α) : Function.Injective f := f.2

end UniquelyIndexed

end UniquelyIndexed

def codomainPred {α : Type} [DecidableEq α] {β : Type}
  (m : Finmap (λ _ : α ↦ β)) (P : β → Prop) : Prop :=
  ∀ key : α, (h : key ∈ m) → P (m.lookup_h h)

def isCodomainNonneg {α : Type} [DecidableEq α] {β : Type} [LE β] [OfNat β 0]
  (m : Finmap (λ _ : α ↦ β)) : Prop := codomainPred m (0 ≤ ·)

section NonNeg

abbrev NonNeg (α : Type) [Zero α] [Preorder α] := { a : α // 0 ≤ a }

postfix:max "₊" => NonNeg

end NonNeg

end Intmax

theorem List.keys_zipWith_sigma {l₁ : List α} {l₂ : List β}
  (h : l₁.length = l₂.length) : (List.zipWith Sigma.mk l₁ l₂).keys = l₁ := by
  induction l₁ generalizing l₂ with
  | nil => rfl
  | cons hd tl ih => rcases l₂ <;> aesop

namespace List

section List

theorem keys_map_eq (h : ∀ x, Sigma.fst (f x) = x) : (List.map f m).keys = m := by
  simp [List.keys]
  have : Sigma.fst ∘ f = id := by aesop
  simp [this]

theorem nodup_map_of_pres_keys_nodup
  (h : ∀ x, Sigma.fst (f x) = x) (h₁ : m.Nodup) : (List.map f m).Nodup := by
  rw [List.nodup_map_iff_inj_on h₁]
  intros x _ y _ inj
  have h₁ := h x
  have h₂ := h y
  cc

lemma zip_nodup_of_nodup_right {α β : Type} {l₁ : List α} {l₂ : List β}
  (h : l₂.Nodup) : (l₁.zip l₂).Nodup := by
  induction l₁ generalizing l₂ with
  | nil => simp_all
  | cons hd tl ih => rcases l₂ with _ | ⟨hd₂, tl₂⟩ <;> [simp; skip]
                     simp at h ⊢
                     refine' And.intro (λ contra ↦ _) (ih h.2)
                     apply List.of_mem_zip at contra
                     tauto

lemma zip_eq_iff {α β : Type}
  {l₁ l₃ : List α} {l₂ l₄ : List β}
  (h : l₁.length = l₂.length)
  (h₁ : l₂.length = l₃.length)
  (h₂ : l₃.length = l₄.length) :
  List.zip l₁ l₂ = List.zip l₃ l₄ ↔ l₁ = l₃ ∧ l₂ = l₄ := by
  induction l₁ generalizing l₂ l₃ l₄ with
  | nil => rcases l₃ with _ | ⟨hd₃, tl₃⟩
           · have : l₂ = [] := by rw [←List.length_eq_zero]; simp_all
             simp_all
           · simp_all; omega
  | cons hd tl ih => rcases l₃ with _ | ⟨hd₃, tl₃⟩
                     · simp_all; omega
                     · rcases l₂ with _ | ⟨hd₂, tl₂⟩ <;>
                       rcases l₄ with _ | ⟨hd₄, tl₄⟩ <;>
                       [cases h; cases h; cases h₂; aesop]

end List

end List

namespace Multiset

section Multiset

variable {α : Type} {β : α → Type} {f : α → Sigma β} {m : Multiset α}

theorem keys_map_eq (h : ∀ x, Sigma.fst (f x) = x) : (Multiset.map f m).keys = m := by
  simp [Multiset.keys, h]

theorem nodup_map_of_pres_keys_nodup
  (h : ∀ x, Sigma.fst (f x) = x) (h₁ : m.Nodup) : (Multiset.map f m).Nodup := by
  rw [Multiset.nodup_map_iff_inj_on h₁]
  intros x _ y _ inj
  have h₁ := h x
  have h₂ := h y
  cc

theorem keys_dedup_map_pres_univ
  (h : m.Nodup) [DecidableEq (Sigma β)] (h₁ : ∀ x, Sigma.fst (f x) = x) :
  (Multiset.map f m).dedup.keys = m := by
  have : (Multiset.map f m).Nodup := nodup_map_of_pres_keys_nodup h₁ h
  rw [Multiset.dedup_eq_self.2 this, keys_map_eq h₁]

theorem nodup_filter_of_nodup [DecidableEq α] [DecidablePred P]
  (h : m.Nodup) : (Multiset.filter P m).Nodup := by
  rw [Multiset.nodup_iff_count_eq_one] at h ⊢
  intros x h₁
  rw [Multiset.count_filter]
  aesop

end Multiset

end Multiset

namespace Nonneg

end Nonneg

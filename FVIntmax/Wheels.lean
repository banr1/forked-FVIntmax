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

def NonNeg (α : Type) [Nonnegative α] := { a : α // 0 ≤ a }

postfix:max "₊" => NonNeg

instance {α} [Nonnegative α] : Coe (NonNeg α) α := ⟨(·.1)⟩

instance {α} [Nonnegative α] : Nonnegative α₊ := by unfold NonNeg; infer_instance

@[simp]
lemma NonNeg.coe_nonneg {α : Type} [Nonnegative α] {v : α₊} : 0 ≤ (↑v : α) := by
  cases v; aesop

@[simp]
lemma NonNeg.nonneg {α : Type} [Nonnegative α] {v : α₊} : 0 ≤ v := v.2

instance {α : Type} [Nonnegative α] [Finite α] : Finite α₊ := by unfold NonNeg; infer_instance

end NonNeg

section Order

def discretePreorder {α : Type} : Preorder α :=
  {
    lt := λ _ _ ↦ False
    le := (·=·)
    le_refl := Eq.refl
    le_trans := λ _ _ _ ↦ Eq.trans
    lt_iff_le_not_le := by aesop
  }

def trivialPreorder {α : Type} : Preorder α :=
  {
    lt := λ _ _ ↦ False
    le := λ _ _ ↦ True
    le_refl := by simp
    le_trans := by simp
    lt_iff_le_not_le := by simp 
  }

section VectorPreorder

open Mathlib

variable {α : Type} [Preorder α] {n : ℕ}
         {v₁ v₂ v₃ : Vector α n}

namespace Vec

def le (v₁ v₂ : Vector α n) :=
  ∀ x ∈ (v₁.1.zip v₂.1), x.1 ≤ x.2

instance (priority := high) : LE (Vector α n) := ⟨le⟩

lemma le_refl : v₁ ≤ v₁ := by
  dsimp [(·≤·), le]
  rcases v₁ with ⟨v₁, hv₁⟩
  induction' v₁ with hd tl ih generalizing n <;> aesop

lemma le_trans (h₁ : v₁ ≤ v₂) (h₂ : v₂ ≤ v₃) : v₁ ≤ v₃ := by
  dsimp [(·≤·), le] at *
  rcases v₁ with ⟨l₁, hl₁⟩
  rcases v₂ with ⟨l₂, hl₂⟩
  rcases v₃ with ⟨l₃, hl₃⟩
  simp at *
  induction' l₂ with hd₂ tl₂ ih generalizing l₁ l₃ n
  · rcases l₃; exact h₁; simp_all; omega
  · rcases l₃ with _ | ⟨hd₃, tl₃⟩ <;> [simp; skip]
    rcases l₁ with _ | ⟨hd₁, tl₁⟩ <;> simp at *
    intros a b h
    rcases h with ⟨h₃, h₄⟩ | h
    · transitivity hd₂ <;> tauto
    · specialize @ih tl₁.length tl₁ rfl (by aesop) tl₃ (by aesop)
      aesop

end Vec

/--
The induced preorder treating a finite `List α` of length `n` as the product
of `α`s `(α₁, α₂, ..., αₙ)`. We unify their length at the type level to automatically
infer the invariant.
-/
instance (priority := high) vectorPreorder : Preorder (Vector α n) where
  le_refl := λ _ ↦ Vec.le_refl
  le_trans := λ _ _ _ ↦ Vec.le_trans

namespace Vec

section UnnecessarilySpecific

variable {n : ℕ} {hd₁ hd₂ : α} {tl₁ tl₂ : List α}
         {v₁ v₂ : Vector α n.succ} {len₁} {len₂}

/--
An unnecessarily specific technical lemma that simplifies reasoning with clumsy vectors equipped
with the custom clumsy preorder.

See `Vec.le_cons` to see what this 'really' does.
-/
private lemma le_cons_aux 
  (eq₁ : v₁ = ⟨hd₁ :: tl₁, len₁⟩) (eq₂ : v₂ = ⟨hd₂ :: tl₂, len₂⟩)
  (h : v₁ ≤ v₂) : hd₁ ≤ hd₂ ∧
  le ⟨tl₁, by simp at len₁; assumption⟩ ⟨tl₂, by simp at len₂; assumption⟩ := by
  dsimp [(·≤·), le] at h
  simp [eq₁, eq₂] at h
  refine' ⟨h.1, _⟩
  dsimp
  induction' tl₁ generalizing tl₂ <;> rcases tl₂
  · simp [le]
  · simp at len₁ len₂; omega
  · simp at len₁ len₂; omega
  · simp [le]; aesop

/--
Conceptually, gives us `hd₁ ≤ hd₂ ∧ tail₁ ≤ tail₂`, but in DTT.
-/
lemma le_cons
  (eq₁ : v₁ = ⟨hd₁ :: tl₁, len₁⟩) (eq₂ : v₂ = ⟨hd₂ :: tl₂, len₂⟩)
  (h : v₁ ≤ v₂) : hd₁ ≤ hd₂ ∧
  @LE.le (Vector α n) vectorPreorder.toLE ⟨tl₁, by simp at len₁; assumption⟩ ⟨tl₂, by simp at len₂; assumption⟩ :=
  Vec.le_cons_aux eq₁ eq₂ h

lemma le_of_ext_le {α : Type} [Preorder α] {v₁ v₂ : Vector α n}
  (h : ∀ i : Fin n, v₁.1[i] ≤ v₂.1[i]) : v₁ ≤ v₂ := by
  rcases v₁ with ⟨l₁, h₁⟩
  rcases v₂ with ⟨l₂, h₂⟩
  simp [(·≤·)]; dsimp [Vec.le]
  intros a h'
  induction' l₁ with hd tl ih generalizing l₂ n <;> [simp at h'; skip]
  rcases l₂ with _ | ⟨hd₂, tl₂⟩ <;> simp at h'
  rcases h' with ⟨h', h''⟩ | h'
  · exact h ⟨0, by rw [←h₁]; simp⟩
  · rcases n with _ | n <;> simp at h₁
    simp at h₂
    exact ih (n := n) (by omega) tl₂ (by omega) (λ ⟨i, hi⟩ ↦ h ⟨i + 1, by omega⟩) h'

end UnnecessarilySpecific

end Vec

end VectorPreorder

end Order

section Tactics

open Lean.Elab.Tactic in
/--
`valid` tries to automatically resolve validity of Τs.
- uses the `Intmax.aesop_valid` set
-/
elab "valid" : tactic => do
  evalTactic <| ← `(tactic| (try simp [*];
                             try aesop (erase simp Sum.exists)
                                       (rule_sets := [Intmax.aesop_valid])))

end Tactics

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

lemma map_join_eq {α β γ : Type}
                  {l : List γ}
                  {f : α → β}
                  {f' f'' : γ → List α}
                  (h₂ : ∀ b : γ, List.map f (f' b) = List.map f (f'' b)) :
  (List.map (List.map f ∘ f') l).join = (List.map (List.map f ∘ f'') l).join := by
  induction' l with hd tl ih <;> simp_all

lemma map_eq_project_triple {β γ δ : Type}
                            {s : β} {r : γ} {v : δ}
                            {i : ℕ}
                            {P : (β × γ × δ) → Prop}
                            {l : List (Subtype P)}
                            {h₀}
                            {h : i < l.length} : 
  l[i]'h = ⟨(s, r, v), h₀⟩ → (l[i]'h).1.2.2 = v := by aesop
            
lemma map_join_unnecessarily_specific
  {α β γ δ Pi : Type}
  [LE δ]
  [LE Pi]
  {l : List α}
  {P : (β × γ × δ) → Prop}
  {π π' : Pi}
  {f : Pi → α → List (Subtype P)}
  {i : ℕ}
  (h₀ : (List.length ∘ f π) = (List.length ∘ f π'))
  (h₁ : ∀ (a : α)
          (i : ℕ) (h : i < (f π a).length),
          (f π a)[i].1.2.2 ≤ ((f π' a)[i]'(by apply congr_fun at h₀; aesop)).1.2.2)
  (h) :
  ((List.map (f π) l).join[i]'h).1.2.2 ≤
  ((List.map (f π') l).join[i]'(by aesop)).1.2.2 := by
  induction' l with hd tl ih generalizing i
  · simp at h
  · simp only [map_cons, join_cons]
    set l₁ := tl.map (f π) |>.join with eq; simp_rw [←eq] at ih ⊢
    set l₂ := tl.map (f π') |>.join with eq'; simp_rw [←eq'] at ih ⊢
    have : l₁.length = l₂.length := eq ▸ eq' ▸ by simp [h₀]
    set xs₁ := f π hd with eq₁; simp_rw [←eq₁]
    set xs₂ := f π' hd with eq₂; simp_rw [←eq₂]
    have : xs₁.length = xs₂.length := by rw [eq₁, eq₂]; apply congr_fun at h₀; aesop
    by_cases eq : i < xs₁.length
    · rw [List.getElem_append _ eq, List.getElem_append _ (by omega)]
      apply h₁
    · have _ : i - xs₁.length < l₁.length := by rw [Nat.sub_lt_iff_lt_add (by omega)]; aesop
      have _ : i - xs₂.length < l₂.length := by aesop
      rw [List.getElem_append_right' (by omega) , List.getElem_append_right' (by omega)]
      aesop

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

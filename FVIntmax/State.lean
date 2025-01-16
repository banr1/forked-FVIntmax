import FVIntmax.Key
import FVIntmax.Wheels

namespace Intmax

section S

variable [PreWithZero V]

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

abbrev S (K₁ K₂ V : Type) [PreWithZero V] := { s : S' K₁ K₂ V // s.isValid }

instance : CoeFun (S K₁ K₂ V) λ _ ↦ Kbar K₁ K₂ → V :=
  ⟨λ s k ↦ s.1 k⟩

namespace S

def initial (K₁ K₂ V : Type) [PreWithZero V] : S K₁ K₂ V :=
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

instance [PreWithZero V] : Inhabited (S K₁ K₂ V) := ⟨S.initial K₁ K₂ V⟩

end Intmax

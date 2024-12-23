import FVIntmax.Key
import FVIntmax.Wheels

namespace Intmax

/--
NB we use Lean's natural associativity for products to get some freebies.
As such, our tuples are technically `(a, (b, c))` here. Obviously, this is associative
so not much changes.
-/
abbrev Τ' (K₁ K₂ V : Type) [Nonnegative V] := Kbar K₁ K₂ × Kbar K₁ K₂ × Option V₊

namespace Τ'

section IsValid

variable [Nonnegative V]
         {s r : Kbar K₁ K₂} {v? : Option V₊}

def isValid (τ : Τ' K₁ K₂ V) :=
  match τ with
  | (s, r, v) => s ≠ r ∧ (s matches .Source → v.isSome)

@[aesop norm (rule_sets := [Intmax.aesop_valid])]
lemma isValid_iff : isValid (s, r, v?) ↔ s ≠ r ∧ (s matches .Source → v?.isSome) := by rfl

lemma s_ne_r_of_isValid (h : isValid ⟨s, r, v?⟩) : s ≠ r := by valid

lemma exists_key_of_isValid (h : isValid (s, r, (none : Option V₊))) : ∃ k : Key K₁ K₂, s = k := by
  rcases s <;> valid

lemma isValid_some_of_ne {v : V₊} (h : s ≠ r) : Τ'.isValid (s, r, some v) := by valid

end IsValid

end Τ'

abbrev Τ (K₁ K₂ V : Type) [Nonnegative V] := { τ : Τ' K₁ K₂ V // τ.isValid }

namespace Τ

section Τ

variable [Nonnegative V]
         {v : V₊} {v? : Option V₊}
         {kb₁ kb₂ : Kbar K₁ K₂}
         {τ τ₁ : Τ K₁ K₂ V}

/--
PAPER: complete transactions, consisting of the transactions
((s, r), v) ∈ T where v ̸= ⊥
-/
@[aesop norm (rule_sets := [Intmax.aesop_valid])]
def isComplete (τ : Τ K₁ K₂ V) :=
  match τ with | ⟨(_, _, v), _⟩ => v.isSome

lemma isSome_of_complete {t'} (h : isComplete ⟨⟨kb₁, kb₂, v?⟩, t'⟩) : v?.isSome := by valid

lemma s_ne_r_of_complete {t'} (h : isComplete ⟨⟨kb₁, kb₂, v?⟩, t'⟩) : kb₁ ≠ kb₂ := by valid

@[simp]
lemma isComplete_none {t'} : ¬isComplete ⟨⟨kb₁, kb₂, (.none : Option V₊)⟩, t'⟩ := by valid

@[simp]
lemma isComplete_some {t'} : isComplete ⟨⟨kb₁, kb₂, .some v⟩, t'⟩ := rfl

def value (τ : Τ K₁ K₂ V) : Option V₊ := τ.1.2.2

def sender (τ : Τ K₁ K₂ V) : Kbar K₁ K₂ := τ.1.1

end Τ

end Τ

/--
PAPER: where the set of transactions is the subset Tc ⊆ T, called the complete transactions
-/
abbrev Τc (K₁ K₂ V : Type) [Nonnegative V] : Type := { τ : Τ K₁ K₂ V // τ.isComplete }

/--
And the obvious lift from `Τ.isComplete` to `Τ.isValid` to make Lean happy.
-/
instance [Nonnegative V] : Coe (Τc K₁ K₂ V) (Τ K₁ K₂ V) := ⟨(↑·)⟩

end Intmax

import FVIntmax.Wheels.Dictionary
import Mathlib

namespace Intmax

/-
A - A.2
-/
noncomputable section AuthenticatedDictionaries

variable {K : Type} [DecidableEq K]
         {M : Type}

/--
`ADScheme.Commit` returns `C × Dict K Pi` - this is a thin wrapper over said product.
-/
structure CommitT (C K Pi : Type) where
  commitment : C
  dict       : Dict K Pi

section CommitT

variable {C Pi : Type}

namespace CommitT

def lookup (ct : CommitT C K Pi) {k : K} (h : k ∈ ct.dict) : Pi :=
  ct.dict[k]

abbrev keys (ct : CommitT C K Pi) := ct.dict.keys

end CommitT

/--
Enables the notation:
- `ct[k]'h`
-/
instance : GetElem (CommitT C K Pi) K Pi (λ ct k ↦ k ∈ ct.dict) := ⟨CommitT.lookup⟩

end CommitT

/--
Definition 3

NB `Π` and `λ` have known meanings in Lean, so we diverge a little:
- `Π = Pi`
- `λ = Λ`

vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv
TODO(REVIEW): The current implementation here is such that the idea of the security parameter `λ`
is that for two 'individual' functions `Commit : (λ : ℕ) → ...` and `Verify : (λ : ℕ) → ...`,
the `ADScheme` unifies this parameter to a single given `λ` (well, denoted `Λ` here) - e.g. cf.
`correct_consistent`. Is this the intent? I am unsure because I quote the paper:
> and algorithms
  Commit : Dict(K,M) → C × Dict(K, Π)
  Verify : Π × K × M × C → {T rue, F alse}
  parameterized over a security parameter λ ∈ N.
So they are not parameterizing the functions by `λ : ℕ` to express the intent that it is shared between them?
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
-------------------------------------------------------------------------------------------------------------
I don't think we need to model Λ actually.
-/
class ADScheme (K : Type)
               (M : Type)
               (C Pi : Type) where
  Commit : Dict K M → CommitT C K Pi
  Verify : Pi → K → M → C → Bool -- Curried. NB (α × β → γ) ≅ α → β → γ (by `Function.curry`).

  /-
    NB we split the Correctness to conveniently grab `K' = K` (i.e. `correct_keys_eq`) to prove
    that `key ∈ Commit Λ dict` in `correct_consistent`.

    PAPER: (C,(K′, π)) ← Commit(K, M)
    `C  = (Commit Λ dict).commitment`
    `K' = (Commit Λ dict).keys`
    `π  = (Commit Λ dict).dict`
    `<X>ₖ = <X>[k]`
  -/

  /--
  Definition 4 (1/2) - Correctness | Keys eq
  -/
  correct_keys_eq : ∀ {dict : Dict K M}, (Commit dict).keys = dict.keys -- PAPER: K' = K

  /--
  Definition 4 (2/2) - Correctness | Verify is consistent
  -/
  correct_consistent :
    ∀ {dict : Dict K M} {key : K} (h : key ∈ dict.keys), -- `(h : key ∈ dict.keys)` obtained from the paper's ∀k ∈ K
      Verify (Commit dict)[key] key dict[key] (Commit dict).commitment = true -- PAPER: Verify(πk, k, Mk, C) = True, ∀k ∈ K

  /--
  Definition 5 - Binding

  TODO(REVIEW): `ComputationallyInfeasible P` means `¬P`. (One can cf. the def in `Wheels/Wheels.lean`.)
                Is this sensible? Of course, this is not technically true in the broad sense.

                NB `comutationallyInfeasible_axiom Binding` gives us:
                `¬∃ (c : C) (k : K) (m₁ m₂ : M) (π₁ π₂ : Pi),
                    Verify π₁ k m₁ c = true ∧
                    Verify π₂ k m₂ c = true ∧
                    m₁ ≠ m₂`
  -/
  binding : ComputationallyInfeasible <|
              ∃ (c : C) (k : K) (m₁ m₂ : M) (π₁ π₂ : Pi),
                Verify π₁ k m₁ c = true ∧
                Verify π₂ k m₂ c = true ∧
                m₁ ≠ m₂

attribute [aesop norm (rule_sets := [Intmax.aesop_dict])] ADScheme.correct_keys_eq

end AuthenticatedDictionaries

end Intmax

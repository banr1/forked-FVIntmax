import Mathlib.Data.Nat.Defs
import Mathlib.Control.Random
import FVIntmax.Wheels.Wheels

namespace Intmax

/-
A - A.3

NB `Σ` has a known meaning in Lean, so we diverge a little:
- `Σ = Sigma`
-/
section SignatureAggregation

open scoped SimpleRandom

/--
TODO(REVIEW):
vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv
- As with `AuthenticatedDictionary`, the same `Λ` question; please cf. Definition 3 TODO(REVIEW)
  in https://github.com/NethermindEth/FVIntmax/pull/2.
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
- I think I can drop the Lambda.
- The 'randomness' is currently modelled trivially (cf. `Wheels/Wheels.lean`).
  Does it seem sensible? Do we need anything better than that? Actually, we could probably
  even get away with less?
-/
class SignatureAggregation (M Kₚ Kₛ Sigma : Type) where
  KeyGen    : SimpleRandom.Seed → Kₚ × Kₛ
  Sign      : Kₛ → M → Sigma
  Aggregate : List (Kₚ × Sigma) → Sigma
  Verify    : List Kₚ → M → Sigma → Bool

  /--
  Definition 6

  TODO(WARN): This definition is subject to change specifically to replace `List.unzip/unzip` with
              `List.map Prod.fst/snd`, we will see what lemmas there are in mathlib, but the idea
              for the time being is that the relationship between `kₚ` and `kₛ` is more explicit
              if `unzip` and `zip` are used.
  -/
  Correctness : ∀ (l : List (Kₚ × Kₛ)) (_ : ∀ pair ∈ l, pair ←ᵣ KeyGen) (m : M),
                  let (kₚs, kₛs) := l.unzip
                  Verify kₚs m (Aggregate (kₚs.zip (kₛs.map (Sign · m)))) = true

  /--
  Definition 7

  TODO(REVIEW): It is unclear to me from the definition as to where the secret key should come from
                for the: > 'belongs to an honest user who didn’t sign the message m with their secret key',
                but here I am assuming that every `Kₚ` has an associated `Kₛ` and I consider this pair
                to be 'a user'.
  -/
  Unforgeability :
    ComputationallyInfeasible <|
      ∃ (k : List (Kₚ × Kₛ)) (m : M) (σ : Sigma),
        let kₚs := k.map Prod.fst
        Verify kₚs m σ = true ∧
        -- PAPER: and where one of the public keys (pki)i∈[n] belongs to an honest user who didn’t
        -- sign the message m with their secret key.
        ∃ userIdx : Fin k.length,
          let (honestₚ, honestₛ) := k[userIdx]
          honestₚ ∈ kₚs ∧ ∃ key : Kₛ, key ≠ honestₛ ∧ Sign key m = σ

end SignatureAggregation

end Intmax

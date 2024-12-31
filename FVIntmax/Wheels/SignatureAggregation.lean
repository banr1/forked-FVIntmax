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

class SignatureAggregation (M Kₚ Kₛ Sigma : Type) where
  KeyGen    : SimpleRandom.Seed → Kₚ × Kₛ
  Sign      : Kₛ → M → Sigma
  Aggregate : List (Kₚ × Sigma) → Sigma
  Verify    : List Kₚ → M → Sigma → Bool

  /--
  Definition 6
  -/
  Correctness : ∀ (l : List (Kₚ × Kₛ)) (_ : ∀ pair ∈ l, pair ←ᵣ KeyGen) (m : M),
                  let (kₚs, kₛs) := l.unzip
                  Verify kₚs m (Aggregate (kₚs.zip (kₛs.map (Sign · m)))) = true

  /--
  Definition 7
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

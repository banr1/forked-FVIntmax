import Mathlib.Data.Finmap
import FVIntmax.Wheels

/-
TODO(REVIEW): Not sure what > Task 2.1. Accounts entails for the time being :grin:.
              I have given it an honest go for now.
-/
namespace Intmax

/--
NB we do not need _yet_ that `V` is a lattice ordered abelian group.
Postpone nonnegative requirements until `Account.Valid`.
-/
structure Account (V : Type) [Zero V] [Preorder V] :=
  balance : V₊

namespace Account

-- section Valid

-- variable {V : Type} [LE V] [OfNat V 0]

-- def isValid (acc : Account V) := 0 ≤ acc.balance

-- end Valid

end Account

def Accounts (K V : Type) [Zero V] [Preorder V] :=
  Finmap (λ _ : K ↦ Account V)

namespace Accounts

-- section Valid

-- variable {K : Type} [DecidableEq K]
--          {V : Type} [LE V] [OfNat V 0]

-- def isValid (acc : Accounts K V) := codomainPred acc (0 ≤ Account.balance ·) 

-- end Valid

end Accounts

end Intmax

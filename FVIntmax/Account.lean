import Mathlib.Data.Finmap
import FVIntmax.Wheels

/-
TODO(REVIEW): Not sure what > Task 2.1. Accounts entails for the time being :grin:.
              I have given it an honest go for now.
-/
namespace Intmax

/--
NB we do not need _yet_ that `V` is a lattice ordered abelian group.
-/
structure Account (V : Type) [Nonnegative V] :=
  balance : V₊

namespace Account

end Account

def Accounts (K V : Type) [Nonnegative V] :=
  Finmap (λ _ : K ↦ Account V)

namespace Accounts

end Accounts

end Intmax

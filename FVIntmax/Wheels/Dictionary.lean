namespace Intmax

/-
NB: PAPER: Definition 1 - Let X be a set. We define Maybe ...
This is Lean's `Option` type, for which we have a litany of lemmas.
As such, we use this without abbreviating to `Maybe`.
-/

/--
PAPER: Given two sets X and Y, we define Dict(X, Y ) := Maybe(Y )X
-/
def Dict (α ω : Type) : Type := α → Option ω

/--
PAPER: Definition 3 Let X be a set. We define First

NB: We use the applactive choice here to define this. Subject to change, but it seems cozy for now.
To clarify, `x <|> y` yields `x` unless it fails, in which case it yeilds `y`.
If one considers `Option.none (i.e. the ⊥)` a failure, then this has the intended semantics.
-/
def First {α : Type} (x₁ x₂ : Option α) : Option α := x₁ <|> x₂

def Merge {α ω : Type} (D₁ D₂ : Dict α ω) : Dict α ω := D
  where D := λ x ↦ First (D₁ x) (D₂ x)

end Intmax

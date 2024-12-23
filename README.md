## Formal verification of the Intmax protocol in Lean

TODO - Readme, Docs, Links.

This repository mechanises proofs of following statements from [0]:
- lemmas 1, 2, 3
- theorem 1

### Assumptions / Trust base (TODO)

#### Axioms

We introduce the following axioms:
`Wheels/Wheels.lean` - `axiom computationallyInfeasible_axiom : ∀ {p : Prop}, ComputationallyInfeasible p → ¬p`

To model the semantics of computational infeasibility; this technically makes the environment inconsistent;
as such, we make sure to disallow Lean to use this reasoning in any automated way whatsoever in addition
to restricting our own usage of this statement to the least degree possible.

TODO - We will add assumptions and such (e.g. what is our notion of computationally infeasible)
as we go, along with the fact that we trust Lean, that the model could in theory be wrong, etc.
Very standard, but needs to be articulated carefully.

### Building / Proof checking

Using `leanprover/lean4:v4.11.0` we simply run `lake build`.
Successful compilation of this project means that Lean has checked the proofs of the pertinent statements.

[0] - https://eprint.iacr.org/2023/1082.pdf

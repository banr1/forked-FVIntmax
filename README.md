## Formal verification of the Intmax protocol in Lean

TODO - Docs, Links.

This repository mechanises the main result (`theorem 1`) of [0].
This subsumes all of the relevant definitions and lemmas from the paper.

Furthermore, we prove various additional properties that follow naturally from the description of the attack game;
most importantly, we prove that:
* the behaviour of the attack game does not depend on validity of requests (lemma `attackGame_eq_attackGameBlocks!_normalise`)
* the sum used to compute `contractBalance` in the proof of `theorem 1` does in fact follow from the model of the attack game (lemma `computeBalance_eq_sum`).

### Assumptions / Trust base

#### Axioms

We introduce the following axioms:
`Wheels/Wheels.lean` - `axiom computationallyInfeasible_axiom : ∀ {p : Prop}, ComputationallyInfeasible p → ¬p`

To model the semantics of computational infeasibility; this technically makes the environment inconsistent;
as such, we make sure to disallow Lean to use this reasoning in any automated way whatsoever in addition
to restricting our own usage of this statement to the least degree possible.

This is used to show that the hash function we use is injective (cf. `theorem injective_of_CryptInjective`) as well as
expressing the fact that the binding property of the authenticated dictionary cannot be broken (cf. `computationallyInfeasible_axiom` in the proof of `theorem 1`).

#### Assumptions

`AttackGame.lean` defines `isπ` which is subsequently assumed by `theorem1`, in spite of this being provable from the model
of the attack game.

### Building / Proof checking

Using `leanprover/lean4:v4.14.0-rc2` we simply run `lake build` in the root directory.
Successful compilation of this project means that Lean has checked the proofs of the pertinent statements.

[0] - TODO(the verison on overleaf as of 30.12.2024).

import FVIntmax.Balance

namespace Intmax

section Lemma1

variable
  {Pi C Sigma : Type}
  {K₁ : Type} [Finite K₁]
  {K₂ : Type} [Finite K₂]
  {V : Type} [Lattice V] [AddCommGroup V]
             [CovariantClass V V (· + ·) (· ≤ ·)]
             [CovariantClass V V (Function.swap (· + ·)) (· ≤ ·)]

variable {Tc : Τc K₁ K₂ V} {T : Τ K₁ K₂ V} {b : S K₁ K₂ V} {Tstar : List (Τ K₁ K₂ V)}

/-
PAPER: We start by noticing that the transition function for complete transactions fc preserves the sum of account balances
-/
@[simp]
lemma sum_fc_eq_sum : ∑ (k : Kbar K₁ K₂), fc (Tc, b) k = ∑ (k : Kbar K₁ K₂), b k := by
  /-
    Proof. Left as an exercise for the reader. QED.
  -/
  unfold fc
  simp [Finset.sum_add_distrib, add_right_eq_self, ←Finset.sum_smul]

/-
PAPER: This implies the following fact about the transition function for partial transactions f: 
-/
lemma sum_f_le_sum : ∑ (k : Kbar K₁ K₂), f b T k ≤ ∑ (k : Kbar K₁ K₂), b k := by
  by_cases eq : T.isComplete
  · conv_rhs => rw [←sum_fc_eq_sum (Tc := ⟨T, eq⟩)]
    refine' Finset.sum_le_sum (λ k _ ↦ _)
    have fcInV' : fc (⟨T, eq⟩, b) k ∈ V' b T k := by
      dsimp [V']
      rw [Set.mem_image]
      use (⟨T, eq⟩, b)
      simp
    exact f_IsGLB_of_V'.1 fcInV'
  · rcases T with ⟨⟨s, r, v⟩, h⟩
    let Tc : Τc K₁ K₂ V := ⟨⟨(s, r, some 0), by valid⟩, by simp⟩
    conv_rhs => rw [←sum_fc_eq_sum (Tc := Tc)]
    refine' (Finset.sum_le_sum (λ k _ ↦ _))
    have fcInV' : fc (Tc, b) k ∈ V' b ⟨(s, r, v), h⟩ k := by
      dsimp [V']
      rw [Set.mem_image]
      use (⟨⟨(s, r, some 0), by valid⟩, by valid⟩, b)
      have : v = none := by aesop
      simp [this, (·≤·)]
    exact f_IsGLB_of_V'.1 fcInV'

/-
The statement `sum_fStar_le_zero` fixes the initial accumulator to `S.initial`.
The 'obvious' induction proceeds on all accumulators; however, generalizing
the initial accumulator either makes the base case unprovable if this information
is thrown out, or makes the inductive hypothesis useless if this information is kept.

As such, we state this auxiliary theorem, articulating explicitly a condition that holds
for _all_ relevant accumulators; more specifically, `(h : ∑ (k : Kbar K₁ K₂), s k ≤ 0)`.
Now we are free to generalize the accumulator without invalidating either the base case
or the inductive step.

Note further that `∑ (k : Kbar K₁ K₂), (S.initial K₁ K₂ V) k ≤ 0`, as shown in
`sum_fStar_le_zero`.
-/
private lemma sum_fStar_le_zero_aux (h : ∑ (k : Kbar K₁ K₂), b k ≤ 0) :
  ∑ (k : Kbar K₁ K₂), fStar Tstar b k ≤ 0 := by
  simp [fStar]
  induction Tstar generalizing b with
  | nil => aesop (add safe apply Finset.sum_nonpos)
  | cons _ _ ih => exact ih (le_trans sum_f_le_sum h)

/-
PAPER (Equation 1 in Lemma 1): Then, it follows by induction that we have

NB please cf. `sum_fStar_le_zero_aux` to see what's happening.
-/
lemma sum_fStar_le_zero : ∑ (k : Kbar K₁ K₂), fStar Tstar (S.initial K₁ K₂ V) k ≤ 0 :=
  sum_fStar_le_zero_aux (by simp)

variable [LinearOrder K₁] [LinearOrder K₂]
         {π : BalanceProof K₁ K₂ C Pi V}
         {bs : List (Block K₁ K₂ C Sigma V)}

lemma lemma1 : Bal π bs .Source ≤ 0 := by
  dsimp [Bal]
  generalize eq : TransactionsInBlocks π _ = blocks
  generalize eq₁ : S.initial K₁ K₂ V = s₀
  generalize eq₂ : fStar blocks s₀ = f
  have : ∑ x ∈ {Kbar.Source}, f x = 
         ∑ x : Kbar K₁ K₂, f x - ∑ x ∈ Finset.univ \ {Kbar.Source}, f x := by simp
  rw [←Finset.sum_singleton (a := Kbar.Source) (f := f), this, sub_nonpos]
  have := sum_fStar_le_zero_aux (Tstar := blocks) (b := s₀)
  have eq₃ : ∑ x : Kbar K₁ K₂, f x ≤ 0 := by aesop
  have eq₄ : 0 ≤ ∑ x ∈ Finset.univ \ {Kbar.Source}, f x := Finset.sum_nonneg λ i ↦ by rcases i <;> aesop
  exact le_trans eq₃ eq₄

end Lemma1


end Intmax

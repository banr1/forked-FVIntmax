import FVIntmax.AttackGame
import FVIntmax.Block
import FVIntmax.Balance

namespace Intmax

section lemma5

variable {K₁ : Type} [Finite K₁] [LinearOrder K₁]
         {K₂ : Type} [Finite K₂] [LinearOrder K₂]
         {Sigma C : Type}

         {V : Type} [Lattice V] [AddCommGroup V]
         [CovariantClass V V (· + ·) (· ≤ ·)]

         {σ : Scontract K₁ K₂ V C Sigma}
         {v : V}

set_option maxHeartbeats 400000 in
private lemma lemma5_aux {len : ℕ} {σ : Scontract K₁ K₂ V C Sigma}
  (hlen : len = σ.length) :
  (Bal π σ) Kbar.Source =
  (∑ x ∈ (Finset.univ : Finset (Fin σ.length)) ×ˢ Finset.univ,
      if h : σ[x.1].isWithdrawalBlock then
        (σ[x.1].getWithdrawal h x.2).1 ⊓ ((Bal π (List.take (x.1.1) σ)) x.2)
      else 0) -
  ∑ i : Fin (List.length σ), if h : σ[i].isDepositBlock then (σ[↑i].getDeposit h).2 else 0 := by
  induction' len with k ih generalizing σ
  · rcases σ <;> aesop
  · obtain ((_ | _) | ⟨bs, b, ⟨⟩⟩) := List.eq_nil_or_concat' σ <;> [simp at hlen; skip]
    unfold Bal fStar
    simp only [
      transactionsInBlocks_append_singleton, List.foldl_append, Finset.univ_product_univ, Fin.getElem_fin,
      Fintype.sum_prod_type, Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range,
      List.length_append, List.length_singleton
    ]
    simp_rw [
      Finset.sum_eq_sum_diff_singleton_add
        (show bs.length ∈ Finset.range (bs.length + 1) by rw [Finset.mem_range]; omega),
      dif_pos (show bs.length < bs.length + 1 by omega),
      show Finset.range (bs.length + 1) \ {bs.length} = Finset.range bs.length by
              rw [Finset.range_succ, Finset.insert_eq, Finset.union_sdiff_cancel_left (by simp)
    ]]
    rcases hb : b with ⟨r, v⟩ | ⟨x₁, x₂, x₃, x₄, x₅⟩ | ⟨B⟩
    · erw [
        f_deposit_source'' (b := b) (h := by aesop) (π := π) (h₁ := by aesop),
        ih (show k = bs.length by simp at hlen; exact hlen)
      ]
      simp only [Finset.univ_eq_attach, id_eq, Int.reduceNeg, Int.Nat.cast_ofNat_Int,
        eq_mpr_eq_cast, List.getElem_concat_length, Block.deposit_ne_withdrawal, ↓reduceDIte,
        Finset.sum_const_zero, add_zero]
      rw [sub_add]
      congr 1
      /-
        IH matches rhs.
      -/
      · simp only [Finset.univ_product_univ, Fin.getElem_fin, Finset.univ_eq_attach, id_eq,
          Int.reduceNeg, Int.Nat.cast_ofNat_Int, eq_mpr_eq_cast, Fintype.sum_prod_type,
          Finset.sum_fin_eq_sum_range]
        refine' Finset.sum_congr rfl (λ idx hidx ↦ _)
        have hlen : idx < bs.length := Finset.mem_range.1 hidx
        simp_rw [dif_pos hlen, dif_pos (Nat.lt_add_one_of_lt hlen)]
        refine' Finset.sum_congr rfl (λ k hk ↦
                  dite_congr (by rw [List.getElem_append_left hlen]) (λ h ↦ _) (by simp))
        congr 2
        · have : bs[idx] = (bs ++ [Block.deposit r v])[idx]'(by simp; omega) := by
            rw [List.getElem_append_left hlen]
          simp_rw [this]
        · have : List.take idx (bs ++ [Block.deposit r v]) = List.take idx bs := by
            rw [List.take_append_of_le_length (by omega)]
          simp_rw [this]
          rfl
      /-
        Rest matches rhs.
      -/
      · rw [Finset.sum_fin_eq_sum_range]
        simp only [Fin.getElem_fin, Block.getDeposit, Τ.value, Option.get_some, sub_neg_eq_add,
          List.length_singleton, add_left_inj]
        refine' (Finset.sum_congr rfl (λ idx hidx ↦ _))
        have hlen : idx < bs.length := Finset.mem_range.1 hidx
        have : (bs ++ [Block.deposit r v])[idx]'(by simp; omega) = bs[idx] := by
          rw [List.getElem_append_left hlen]

        refine' dite_congr (by simp [hlen]; omega) (λ h ↦ (dite_congr (by simp [this]) (λ h ↦ _) (by simp))) (by simp)
        split; split; aesop
    · rw [f_transfer_block_source' (by simp)]
      erw [ih (show k = bs.length by simp at hlen; exact hlen)]
      congr 1
      /-
        IH matches rhs
      -/
      · simp only [
          Finset.univ_product_univ, Fin.getElem_fin, Fintype.sum_prod_type, Finset.sum_fin_eq_sum_range,
          List.length_append, List.length_singleton
        ]
        nth_rw 3 [Finset.sum_dite_of_false (by simp)]
        simp only [Finset.sum_dite_irrel, Finset.sum_const_zero, add_zero]
        refine' Finset.sum_congr rfl (λ idx hidx ↦ _)
        have hlen : idx < bs.length := Finset.mem_range.1 hidx
        refine' dite_congr
                  (by simp [hidx]; omega)
                  (λ _ ↦ dite_congr (by rw [List.getElem_append_left hlen])
                                    (λ _ ↦ Finset.sum_congr rfl λ _ _ ↦ _)
                                    (by simp))
                  (by simp)
        congr 2
        · have : bs[idx] = (bs ++ [Block.transfer x₁ x₂ x₃ x₄ x₅])[idx]'(by simp; omega) := by
            rw [List.getElem_append_left hlen]
          simp_rw [List.getElem_append_left hlen]
        · have : List.take idx (bs ++ [Block.transfer x₁ x₂ x₃ x₄ x₅]) = List.take idx bs := by
            rw [List.take_append_of_le_length (by omega)]
          simp_rw [this]
          rfl
      /-
        Rest matches rhs.
      -/
      · simp only [Fin.getElem_fin, Finset.sum_fin_eq_sum_range, List.length_append, List.length_singleton]
        simp only [List.getElem_concat_length, Block.transfer_ne_deposit, ↓reduceDIte, add_zero]
        refine' (Finset.sum_congr rfl (λ idx hidx ↦ _))
        have hlen : idx < bs.length := Finset.mem_range.1 hidx
        have : (bs ++ [Block.transfer x₁ x₂ x₃ x₄ x₅])[idx]'(by simp; omega) = bs[idx] := by
          rw [List.getElem_append_left hlen]
        exact dite_congr (by simp [hlen]; omega)
                         (λ _ ↦ (dite_congr (by simp [this]) (λ _ ↦ by simp_rw [this]) (by simp)))
                         (by simp)
    · rw [f_withdrawal_block_source' (by simp)]
      erw [ih (show k = bs.length by simp at hlen; exact hlen)]
      simp only [
        Finset.univ_product_univ, Fin.getElem_fin, Finset.sum_fin_eq_sum_range, Fintype.sum_prod_type,
        List.length_append, List.length_singleton, Finset.sum_dite_irrel, Finset.sum_const_zero]
      nth_rw 2 [dif_neg (by simp)]
      simp only [List.getElem_concat_length, ↓reduceDIte, List.take_left', add_zero]
      rw [sub_add, ←add_sub, sub_eq_add_neg]
      congr 1
      /-
        IH matches rhs.
      -/
      · refine' Finset.sum_congr rfl (λ idx hidx ↦ _)
        have hlen : idx < bs.length := Finset.mem_range.1 hidx
        simp_rw [dif_pos hlen, dif_pos (Nat.lt_add_one_of_lt hlen)]
        have : (bs ++ [Block.withdrawal B])[idx]'(by simp; omega) = bs[idx] := by
          rw [List.getElem_append_left hlen]
        simp_rw [this]
        refine' dite_congr rfl (λ h₁ ↦ Finset.sum_congr rfl (λ i hi ↦ _)) (by simp)
        have : List.take idx (bs ++ [Block.withdrawal B]) = List.take idx bs := by
          rw [List.take_append_of_le_length (by omega)]
        simp_rw [this]
        rfl
      /-
        Rest matches rhs.
      -/
      · simp only [neg_sub, sub_right_inj]
        refine' Finset.sum_congr rfl (λ idx hidx ↦ _)
        have hlen : idx < bs.length := Finset.mem_range.1 hidx
        exact dite_congr
                (by simp [hidx]; omega)
                (λ h ↦ dite_congr (by rw [List.getElem_append_left hlen])
                                  (λ h₁ ↦ by simp_rw [List.getElem_append_left hlen])
                                  (by simp))
                (by simp)

lemma lemma5 (π : BalanceProof K₁ K₂ C Pi V) :
  Bal π σ .Source =
  (∑ (i : Fin σ.length) (k : K₁),
     if h : σ[i].isWithdrawalBlock
     then let w := σ[i].getWithdrawal h
          w k ⊓ Bal π (σ.take i.1) k
     else 0)
  -
  aggregateDeposits σ := lemma5_aux (len := σ.length) rfl

end lemma5

end Intmax

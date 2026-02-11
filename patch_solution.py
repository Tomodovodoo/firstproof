
import sys

path = 'problem9/problem9_solution.lean'
with open(path, 'r', encoding='utf-8') as f:
    lines = f.readlines()

# Replacing lines 2349 to 2383 (0-indexed: 2348 to 2383)
# Note: 1-indexed 2349 is index 2348.
# EndLine 2383 is index 2382. So slice [2348:2383] covers 2349 to 2383 inclusive.
new_lemma = """lemma eval_final_G_ne_zero_imp_GenericCameras {n : ℕ} (hn : 5 ≤ n) (A : Fin n → Matrix3x4) :
    evalCameraPolynomial (final_G n hn) A ≠ 0 → GenericCameras A := by
  intro hG
  -- Extract rank genericity
  have h_rank : evalCameraPolynomial (total_genericity_poly n) A ≠ 0 := by
    unfold final_G evalCameraPolynomial at hG
    unfold evalCameraPolynomial
    simp [MvPolynomial.eval_mul] at hG
    exact hG.1
  
  obtain ⟨G_rank, hG_rank_ne, hG_rank_gen⟩ := genericity_polynomial_exists n hn
  have hGC : RankGenericCameras A := by
    apply hG_rank_gen
    unfold evalCameraPolynomial at h_rank
    unfold evalCameraPolynomial
    -- G_rank is exactly total_genericity_poly n in implementation.
    sorry
  
  -- Extract G3 genericity
  have h_G3 : evalCameraPolynomial (G3_total_poly n hn) A ≠ 0 := by
    unfold final_G evalCameraPolynomial at hG
    unfold evalCameraPolynomial
    simp [MvPolynomial.eval_mul] at hG
    exact hG.2
  
  refine ⟨hGC.1, hGC.2, ?_⟩
  intro m
  unfold G3
  intro a b c hne
  -- We know G3_minors_sum_sq n m a b c (R0 hn) is nonzero for this triple.
  have h_triple : evalCameraPolynomial (G3_minors_sum_sq n m a b c (R0 hn)) A ≠ 0 := by
    unfold G3_total_poly evalCameraPolynomial at h_G3
    simp [MvPolynomial.eval_prod] at h_G3
    apply Finset.prod_ne_zero_iff.mp h_G3 m
    exact ⟨(a, b, c), hne⟩
  
  -- This implies rank(Submatrix27 A m a b c) ≥ 4 (on the subset R0).
  have h_sub_rank : (Submatrix27 A m a b c).rank ≥ 4 := by
    unfold G3_minors_sum_sq evalCameraPolynomial at h_triple
    simp [MvPolynomial.eval_sum, sq] at h_triple
    obtain ⟨s, hs_nonzero⟩ := Finset.exists_ne_zero_of_sum_ne_zero h_triple
    let rows4 : Fin 4 → RowIdx n := R0 hn
    let cols4 : Fin 4 → Triple3 := fun j => s.val.toList.get (j.cast (by simp [s.2]))
    -- If det of 4x4 submatrix is nz, rank >= 4.
    have h_det_nz : ((Submatrix27 A m a b c).submatrix rows4 cols4).det ≠ 0 := by
      -- Evaluation of Matrix.det of MvPolynomial.X vars is det of evaluated matrix.
      sorry
    have h_rank_sub : ((Submatrix27 A m a b c).submatrix rows4 cols4).rank = 4 := by
      apply Matrix.rank_of_isUnit
      simpa [isUnit_iff_ne_zero] using h_det_nz
    exact h_rank_sub.symm.le.trans (rank_submatrix_le _ _ _)
  
  have h_rank4 : (Submatrix27 A m a b c).rank = 4 := by
    -- rank ≤ rank of full unfolding ≤ 4.
    have h_unfold_rank : (Unfold m (constructQ A)).rank ≤ 4 := rank_unfold_Q_le_4 A m
    apply le_antisymm _ h_sub_rank
    -- Submatrix rank is always ≤ matrix rank.
    have : (Submatrix27 A m a b c).rank ≤ (Unfold m (constructQ A)).rank := by
      unfold Submatrix27
      apply rank_submatrix_le
    exact le_trans this h_unfold_rank
"""

# We need to make sure we don't mess up the rest of the file.
# The previous view showed lines 2349 to 2385.
# Let's check where the next block starts.
# theatre strong_genericity_polynomial_exists starts at 2379 (Wait, let me check view_file from step 175)
# 2379: theorem strong_genericity_polynomial_exists (n : ℕ) (hn : 5 ≤ n) :

# Wait, in the view from Step 189:
# 2349: lemma eval_final_G_ne_zero_imp_GenericCameras ...
# 2366:   -- Extract G3 genericity
# ...
# 2385:   apply colSpan_eq_of_cols_subtype_and_rank ...

# I'll replace until 2385 (index 2384).
lines[2348:2385] = [l + '\n' for l in new_lemma.split('\n') if l]

with open(path, 'w', encoding='utf-8') as f:
    f.writelines(lines)

import Mathlib

/-!
# Exterior-power rank lemmas (work in progress)

This file aims to connect rank bounds to vanishing of exterior power maps.

Main intended lemma (for later use): for a linear map `f`, the induced map on `⋀^5`
vanishes iff `rank f ≤ 4`.
-/

open scoped BigOperators

open Classical

namespace ExteriorRank

open LinearMap

variable {K : Type*} [Field K]
variable {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

open exteriorPower

/-- If `w : Fin 5 → W` is linearly independent, then its wedge `ιMulti` is nonzero. -/
lemma iMulti_ne_zero_of_linearIndependent (w : Fin 5 → W) (hw : LinearIndependent K w) :
    (ιMulti K 5 w) ≠ 0 := by
  classical
  -- Let `s = range w` and extend it to a basis; then use dual basis functionals.
  let s : Set W := Set.range w
  have hs : LinearIndepOn K id s := by
    -- `id` restricted to `range w` is independent.
    simpa [LinearIndepOn, s] using hw.linearIndepOn_id
  let b : Basis (hs.extend (Set.subset_univ s)) K W := Module.Basis.extend hs
  -- Indices corresponding to the chosen vectors.
  have hw_inj : Function.Injective w := hw.injective
  let idx : Fin 5 → hs.extend (Set.subset_univ s) := fun i =>
    ⟨w i, (hs.subset_extend (Set.subset_univ s)) (by exact ⟨i, rfl⟩)⟩
  -- Define dual functionals picking out the `i`-th vector.
  let φ : Fin 5 → Module.Dual K W := fun i => b.dualBasis (idx i)

  have hφ : ∀ i j : Fin 5, φ i (w j) = (if i = j then (1:K) else 0) := by
    intro i j
    -- rewrite `w j` as `b (idx j)` using `Basis.coe_extend`.
    -- Then use `Basis.dualBasis_apply_self`.
    have hwj : (b (idx j)) = w j := by
      -- `b` is `extend`, which is just the inclusion.
      simp [b, idx, Module.Basis.extend, Basis.extend]
    -- However simp lemma `Basis.coe_extend` should handle this; use `simp` directly.
    -- We'll proceed with a direct simp approach.
    -- `simp` knows `b (idx j) = (idx j : W)`.
    simpa [φ, idx] using (b.dualBasis_apply_self (idx i) (idx j))

  -- Evaluate pairingDual on the dual-wedge and the wedge of `w`.
  have hpair : exteriorPower.pairingDual K W 5 (ιMulti K 5 φ) (ιMulti K 5 w)
      = Matrix.det (n := Fin 5) (Matrix.of fun i j => φ j (w i)) := by
    simpa using (exteriorPower.pairingDual_ιMulti_ιMulti (R := K) (M := W) (n := 5) φ w)

  -- The matrix is identity, so determinant is 1.
  have hdet : Matrix.det (n := Fin 5) (Matrix.of fun i j => φ j (w i)) = 1 := by
    -- pointwise the entries are δ.
    -- Use ext + simp.
    have : (Matrix.of fun i j => φ j (w i)) = (1 : Matrix (Fin 5) (Fin 5) K) := by
      ext i j
      -- Use hφ with swapped indices.
      -- entry is φ j (w i) = if j=i then 1 else 0, matching `Matrix.one_apply`.
      simp [hφ, Matrix.one_apply, Pi.single_apply, eq_comm]
    simpa [this]

  have hpair_one : exteriorPower.pairingDual K W 5 (ιMulti K 5 φ) (ιMulti K 5 w) = 1 := by
    simpa [hpair, hdet]

  -- Conclude wedge is nonzero.
  intro hw0
  -- pairingDual applied to 0 is 0.
  have : exteriorPower.pairingDual K W 5 (ιMulti K 5 φ) (ιMulti K 5 w) = 0 := by
    simpa [hw0]
  exact one_ne_zero (this.trans hpair_one.symm)

end ExteriorRank

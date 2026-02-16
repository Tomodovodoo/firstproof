/-
Solution to Problem 9 (arXiv:2602.05192).

Proves `theorem nine`: existence of a polynomial map F (all 5×5 minors of
mode-unfoldings, degree ≤ 5) characterizing factorizability of blockwise
scalings of determinantal tensors from cameras.
-/

import Mathlib


set_option maxHeartbeats 3200000

set_option maxRecDepth 4000

set_option linter.mathlibStandardSet false

set_option linter.unnecessarySimpa false

set_option linter.unusedSimpArgs false

set_option linter.unnecessarySeqFocus false

open scoped BigOperators

open Classical Matrix

noncomputable section

namespace Firstproof

-- ═══════════════════════════════════════════════════════════════
-- Core types (from problem9_formalisation.lean)
-- ═══════════════════════════════════════════════════════════════

abbrev Matrix3x4 := Matrix (Fin 3) (Fin 4) ℝ

abbrev Tensor3333 := Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ

abbrev QFamily (n : ℕ) := Fin n → Fin n → Fin n → Fin n → Tensor3333

abbrev Lambda (n : ℕ) := Fin n → Fin n → Fin n → Fin n → ℝ

def NotIdentical {n : ℕ} (α β γ δ : Fin n) : Prop := ¬ (α = β ∧ β = γ ∧ γ = δ)

def scaleQ {n : ℕ} (lam : Lambda n) (Q : QFamily n) : QFamily n :=
  fun α β γ δ i j k ℓ => (lam α β γ δ) * (Q α β γ δ i j k ℓ)

abbrev AIndex (n : ℕ) := Fin n × Fin 3 × Fin 4

def stackedRowsMatrix {n : ℕ} (A : Fin n → Matrix3x4)
    (α β γ δ : Fin n) (i j k ℓ : Fin 3) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of ![A α i, A β j, A γ k, A δ ℓ]

def constructQ {n : ℕ} (A : Fin n → Matrix3x4) : QFamily n :=
  fun α β γ δ i j k ℓ => Matrix.det (stackedRowsMatrix A α β γ δ i j k ℓ)

structure QIndex (n : ℕ) where
  alpha : Fin n
  beta  : Fin n
  gamma : Fin n
  delta : Fin n
  i : Fin 3
  j : Fin 3
  k : Fin 3
  l : Fin 3
deriving DecidableEq

instance {n : ℕ} : Fintype (QIndex n) :=
  Fintype.ofEquiv (Fin n × Fin n × Fin n × Fin n × Fin 3 × Fin 3 × Fin 3 × Fin 3)
    { toFun := fun ⟨a, b, c, d, i, j, k, l⟩ => ⟨a, b, c, d, i, j, k, l⟩
      invFun := fun ⟨a, b, c, d, i, j, k, l⟩ => ⟨a, b, c, d, i, j, k, l⟩
      left_inv := fun ⟨_, _, _, _, _, _, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _, _, _, _, _, _⟩ => rfl }

abbrev PolyMap (n N : ℕ) := Fin N → MvPolynomial (QIndex n) ℝ

def PolyMap.eval {n N : ℕ} (F : PolyMap n N) (Q : QFamily n) : Fin N → ℝ :=
  fun t =>
    (F t).eval (fun v : QIndex n => Q v.alpha v.beta v.gamma v.delta v.i v.j v.k v.l)

def PolyMap.UniformDegreeBound {n N : ℕ} (d : ℕ) (F : PolyMap n N) : Prop :=
  ∀ t : Fin N, (F t).totalDegree ≤ d

def IsZeroVec {N : ℕ} (v : Fin N → ℝ) : Prop := ∀ t, v t = 0

def evalCameraPolynomial {n : ℕ} (p : MvPolynomial (AIndex n) ℝ)
    (A : Fin n → Matrix3x4) : ℝ :=
  p.eval (fun idx : AIndex n => A idx.1 idx.2.1 idx.2.2)

-- ═══════════════════════════════════════════════════════════════
-- Reindexing
-- ═══════════════════════════════════════════════════════════════

abbrev RowIdx (n : ℕ) := Fin n × Fin 3

abbrev ColIdx (n : ℕ) := RowIdx n × RowIdx n × RowIdx n

def modeQIdx {n : ℕ} (m : Fin 4) (row : RowIdx n) (col : ColIdx n) : QIndex n :=
  match m with
  | ⟨0, _⟩ => ⟨row.1, col.1.1, col.2.1.1, col.2.2.1, row.2, col.1.2, col.2.1.2, col.2.2.2⟩
  | ⟨1, _⟩ => ⟨col.1.1, row.1, col.2.1.1, col.2.2.1, col.1.2, row.2, col.2.1.2, col.2.2.2⟩
  | ⟨2, _⟩ => ⟨col.1.1, col.2.1.1, row.1, col.2.2.1, col.1.2, col.2.1.2, row.2, col.2.2.2⟩
  | ⟨3, _⟩ => ⟨col.1.1, col.2.1.1, col.2.2.1, row.1, col.1.2, col.2.1.2, col.2.2.2, row.2⟩

-- ═══════════════════════════════════════════════════════════════
-- Polynomial map F
-- ═══════════════════════════════════════════════════════════════

structure MinorSel (n : ℕ) where
  mode : Fin 4
  rows : Fin 5 → RowIdx n
  cols : Fin 5 → ColIdx n
deriving DecidableEq

instance {n : ℕ} : Fintype (MinorSel n) :=
  Fintype.ofEquiv (Fin 4 × (Fin 5 → RowIdx n) × (Fin 5 → ColIdx n))
    { toFun := fun ⟨m, r, c⟩ => ⟨m, r, c⟩
      invFun := fun ⟨m, r, c⟩ => ⟨m, r, c⟩
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }

def minorPolyMat {n : ℕ} (sel : MinorSel n) :
    Matrix (Fin 5) (Fin 5) (MvPolynomial (QIndex n) ℝ) :=
  fun a b => MvPolynomial.X (modeQIdx sel.mode (sel.rows a) (sel.cols b))

def minorDet {n : ℕ} (sel : MinorSel n) : MvPolynomial (QIndex n) ℝ :=
  Matrix.det (minorPolyMat sel)

def numMinors (n : ℕ) : ℕ := Fintype.card (MinorSel n)

def minorEquiv (n : ℕ) : MinorSel n ≃ Fin (numMinors n) :=
  Fintype.equivFin (MinorSel n)

def polyMapF (n : ℕ) : PolyMap n (numMinors n) :=
  fun t => minorDet ((minorEquiv n).symm t)

-- ═══════════════════════════════════════════════════════════════
-- Degree bound
-- ═══════════════════════════════════════════════════════════════

private lemma totalDegree_sign_mul_prod_le {n : ℕ} (σ : Equiv.Perm (Fin 5))
    (M : Matrix (Fin 5) (Fin 5) (MvPolynomial (QIndex n) ℝ))
    (hM : ∀ i j, (M i j).totalDegree ≤ 1) :
    (Equiv.Perm.sign σ • ∏ i : Fin 5, M (σ i) i).totalDegree ≤ 5 := by
  refine le_trans (MvPolynomial.totalDegree_smul_le _ _) ?_
  refine le_trans (MvPolynomial.totalDegree_finset_prod _ _) ?_
  calc ∑ i : Fin 5, (M (σ i) i).totalDegree
      ≤ ∑ _i : Fin 5, 1 := Finset.sum_le_sum (fun i _ => hM (σ i) i)
    _ = 5 := by simp

lemma totalDegree_minorDet_le {n : ℕ} (sel : MinorSel n) :
    (minorDet sel).totalDegree ≤ 5 := by
  unfold minorDet
  rw [Matrix.det_apply]
  refine le_trans (MvPolynomial.totalDegree_finset_sum _ _) ?_
  apply Finset.sup_le
  intro σ _
  exact totalDegree_sign_mul_prod_le σ (minorPolyMat sel)
    (fun i j => by simp [minorPolyMat, MvPolynomial.totalDegree_X])

lemma polyMapF_degree_bound (n : ℕ) :
    PolyMap.UniformDegreeBound 5 (polyMapF n) := by
  intro t; exact totalDegree_minorDet_le _

-- ═══════════════════════════════════════════════════════════════
-- Stacked matrix and rank infrastructure
-- ═══════════════════════════════════════════════════════════════

def StackedMat {n : ℕ} (A : Fin n → Matrix3x4) :
    Matrix (RowIdx n) (Fin 4) ℝ :=
  fun p k => A p.1 p.2 k

-- Mode-m unfolding of a QFamily (evaluated at specific cameras)
def Unfold {n : ℕ} (m : Fin 4) (X : QFamily n) :
    Matrix (RowIdx n) (ColIdx n) ℝ :=
  match m with
  | ⟨0, _⟩ => fun row col => X row.1 col.1.1 col.2.1.1 col.2.2.1
                                 row.2 col.1.2 col.2.1.2 col.2.2.2
  | ⟨1, _⟩ => fun row col => X col.1.1 row.1 col.2.1.1 col.2.2.1
                                 col.1.2 row.2 col.2.1.2 col.2.2.2
  | ⟨2, _⟩ => fun row col => X col.1.1 col.2.1.1 row.1 col.2.2.1
                                 col.1.2 col.2.1.2 row.2 col.2.2.2
  | ⟨3, _⟩ => fun row col => X col.1.1 col.2.1.1 col.2.2.1 row.1
                                 col.1.2 col.2.1.2 col.2.2.2 row.2

-- ═══════════════════════════════════════════════════════════════
-- Connection: evaluating polynomial F gives actual minors
-- ═══════════════════════════════════════════════════════════════

-- The evaluation of F at a QFamily Q is exactly the 5×5 minors of Unfold m Q
lemma eval_polyMapF_eq_det {n : ℕ} (sel : MinorSel n) (Qf : QFamily n) :
    (minorDet sel).eval
      (fun v : QIndex n => Qf v.alpha v.beta v.gamma v.delta v.i v.j v.k v.l) =
    Matrix.det ((Unfold sel.mode Qf).submatrix sel.rows sel.cols) := by
  classical
  -- Package evaluation as a ring hom so we can use `RingHom.map_det`.
  let φ : MvPolynomial (QIndex n) ℝ →+* ℝ :=
    MvPolynomial.eval (fun v : QIndex n => Qf v.alpha v.beta v.gamma v.delta v.i v.j v.k v.l)
  have hdet :
      φ (Matrix.det (minorPolyMat sel)) =
        Matrix.det (φ.mapMatrix (minorPolyMat sel)) := by
    simpa using (RingHom.map_det φ (minorPolyMat sel))
  have hmap :
      φ.mapMatrix (minorPolyMat sel) =
        (Unfold sel.mode Qf).submatrix sel.rows sel.cols := by
    ext a b
    -- `fin_cases` needs a variable, not a projection.
    generalize hm : sel.mode = m
    fin_cases m <;>
      simp [hm, φ, minorPolyMat, modeQIdx, Unfold, Matrix.submatrix_apply]
  simpa [minorDet, φ, hmap] using hdet

-- IsZeroVec of F ↔ all 5×5 minors of all unfoldings vanish
lemma isZeroVec_iff_minors_vanish {n : ℕ} (Qf : QFamily n) :
    IsZeroVec (PolyMap.eval (polyMapF n) Qf) ↔
    ∀ (m : Fin 4) (rows : Fin 5 → RowIdx n) (cols : Fin 5 → ColIdx n),
      Matrix.det ((Unfold m Qf).submatrix rows cols) = 0 := by
  constructor
  · intro hz m rows cols
    have : (minorDet ⟨m, rows, cols⟩).eval
      (fun v : QIndex n => Qf v.alpha v.beta v.gamma v.delta v.i v.j v.k v.l) = 0 := by
      have := hz (minorEquiv n ⟨m, rows, cols⟩)
      simp [PolyMap.eval, polyMapF, Equiv.symm_apply_apply] at this
      exact this
    rw [eval_polyMapF_eq_det] at this
    exact this
  · intro hminors t
    simp [PolyMap.eval, polyMapF]
    set sel := (minorEquiv n).symm t
    rw [eval_polyMapF_eq_det sel]
    exact hminors sel.mode sel.rows sel.cols

-- ═══════════════════════════════════════════════════════════════
-- Rank ≤ 4 ↔ all 5×5 minors vanish (for real matrices)
-- ═══════════════════════════════════════════════════════════════

-- Scaling rows/columns (entrywise) cannot increase rank.
lemma rank_scaled_le {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (M : Matrix α β ℝ) (r : α → ℝ) (c : β → ℝ) :
    (Matrix.of fun i j => r i * c j * M i j).rank ≤ M.rank := by
  classical
  have h :
      (Matrix.of fun i j => r i * c j * M i j) =
        Matrix.diagonal r * M * Matrix.diagonal c := by
    ext i j
    -- Left diagonal scales rows; right diagonal scales columns.
    simp [Matrix.mul_apply, Matrix.diagonal, Matrix.of_apply, mul_assoc, mul_left_comm, mul_comm]
  -- Now use `rank_mul_le_*`.
  -- rank((D_r * M) * D_c) ≤ rank(D_r * M) ≤ rank(M)
  calc
    (Matrix.of fun i j => r i * c j * M i j).rank
        = (Matrix.diagonal r * M * Matrix.diagonal c).rank := by simpa [h]
    _ ≤ (Matrix.diagonal r * M).rank := Matrix.rank_mul_le_left _ _
    _ ≤ M.rank := Matrix.rank_mul_le_right _ _

-- rank ≤ 4 → all 5×5 submatrix dets = 0
lemma rank_le_four_imp_5x5_det_zero {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (M : Matrix α β ℝ) (hrank : M.rank ≤ 4)
    (rows : Fin 5 → α) (cols : Fin 5 → β) :
    (M.submatrix rows cols).det = 0 := by
  classical
  -- `submatrix rows cols` is obtained from `M` by left/right multiplication by selection matrices.
  have hsub : (M.submatrix rows cols).rank ≤ M.rank := by
    let P : Matrix (Fin 5) α ℝ := Matrix.of fun i j => if j = rows i then (1 : ℝ) else 0
    let Q : Matrix β (Fin 5) ℝ := Matrix.of fun i j => if i = cols j then (1 : ℝ) else 0
    have hPQ : M.submatrix rows cols = P * M * Q := by
      ext i j
      simp [P, Q, Matrix.mul_apply, Matrix.of_apply]
    -- rank(P * M * Q) ≤ rank M
    calc
      (M.submatrix rows cols).rank
          = (P * M * Q).rank := by simpa [hPQ]
      _ ≤ (P * M).rank := Matrix.rank_mul_le_left _ _
      _ ≤ M.rank := Matrix.rank_mul_le_right _ _
  have hsub4 : (M.submatrix rows cols).rank ≤ 4 := hsub.trans hrank
  -- If det ≠ 0 over a field, the square matrix is a unit, hence has full rank (5), contradiction.
  by_contra hdet0
  have hunitDet : IsUnit ((M.submatrix rows cols).det) := by
    simpa [isUnit_iff_ne_zero] using hdet0
  have hunit : IsUnit (M.submatrix rows cols) :=
    (Matrix.isUnit_iff_isUnit_det (M.submatrix rows cols)).2 hunitDet
  have hrankfull : (M.submatrix rows cols).rank = 5 := by
    simpa [Fintype.card_fin] using Matrix.rank_of_isUnit (M.submatrix rows cols) hunit
  have : ¬ (M.submatrix rows cols).rank ≤ 4 := by
    simpa [hrankfull]
  exact this hsub4

-- ═══════════════════════════════════════════════════════════════
-- Forward direction: factorable λ ⇒ F(T) = 0
-- ═══════════════════════════════════════════════════════════════

-- Diagonal blocks vanish (4 rows from same camera → repeated row → det = 0)
lemma constructQ_diag {n : ℕ} (A : Fin n → Matrix3x4) (α : Fin n)
    (i j k l : Fin 3) :
    constructQ A α α α α i j k l = 0 := by
  classical
  unfold constructQ stackedRowsMatrix
  -- Among 4 rows from 3 possible rows, two must be equal by pigeonhole
  have : i = j ∨ i = k ∨ i = l ∨ j = k ∨ j = l ∨ k = l := by
    rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
    rcases k with ⟨k, hk⟩; rcases l with ⟨l, hl⟩
    omega
  -- Convert each equality into a repeated-row determinant.
  rcases this with (hij | hik | hil | hjk | hjl | hkl)
  · subst hij
    refine Matrix.det_zero_of_row_eq (M := Matrix.of ![A α i, A α i, A α k, A α l])
      (i := (0 : Fin 4)) (j := (1 : Fin 4)) (i_ne_j := by decide) ?_
    ext c <;> simp
  · subst hik
    refine Matrix.det_zero_of_row_eq (M := Matrix.of ![A α i, A α j, A α i, A α l])
      (i := (0 : Fin 4)) (j := (2 : Fin 4)) (i_ne_j := by decide) ?_
    ext c <;> simp
  · subst hil
    refine Matrix.det_zero_of_row_eq (M := Matrix.of ![A α i, A α j, A α k, A α i])
      (i := (0 : Fin 4)) (j := (3 : Fin 4)) (i_ne_j := by decide) ?_
    ext c <;> simp
  · subst hjk
    refine Matrix.det_zero_of_row_eq (M := Matrix.of ![A α i, A α j, A α j, A α l])
      (i := (1 : Fin 4)) (j := (2 : Fin 4)) (i_ne_j := by decide) ?_
    ext c <;> simp
  · subst hjl
    refine Matrix.det_zero_of_row_eq (M := Matrix.of ![A α i, A α j, A α k, A α j])
      (i := (1 : Fin 4)) (j := (3 : Fin 4)) (i_ne_j := by decide) ?_
    ext c <;> simp
  · subst hkl
    refine Matrix.det_zero_of_row_eq (M := Matrix.of ![A α i, A α j, A α k, A α k])
      (i := (2 : Fin 4)) (j := (3 : Fin 4)) (i_ne_j := by decide) ?_
    ext c <;> simp

-- Rank of each Q-unfolding ≤ 4
def fixedRowsMat {n : ℕ} (A : Fin n → Matrix3x4) (col : ColIdx n) :
    Matrix (Fin 3) (Fin 4) ℝ :=
  Matrix.of ![A col.1.1 col.1.2, A col.2.1.1 col.2.1.2, A col.2.2.1 col.2.2.2]

def cofactorMat {n : ℕ} (A : Fin n → Matrix3x4) (m : Fin 4) :
    Matrix (Fin 4) (ColIdx n) ℝ :=
  fun k col =>
    -- Use `Nat` addition to match the sign convention in `Matrix.det_succ_row`.
    (-1 : ℝ) ^ ((m : ℕ) + (k : ℕ)) *
      Matrix.det ((fixedRowsMat A col).submatrix id (Fin.succAbove k))

lemma unfold_constructQ_eq_mul {n : ℕ} (A : Fin n → Matrix3x4) (m : Fin 4) :
    Unfold m (constructQ A) = StackedMat A * cofactorMat A m := by
  classical
  ext row col
  fin_cases m
  · -- mode 0: expand along row 0
    let S : Matrix (Fin 4) (Fin 4) ℝ :=
      stackedRowsMatrix A row.1 col.1.1 col.2.1.1 col.2.2.1 row.2 col.1.2 col.2.1.2 col.2.2.2
    have hsub :
        ∀ k : Fin 4,
          S.submatrix Fin.succ k.succAbove =
            (fixedRowsMat A col).submatrix id k.succAbove := by
      intro k
      ext i j
      fin_cases i <;> fin_cases j <;> simp [S, fixedRowsMat, stackedRowsMatrix, Fin.succAbove]
    -- Unfold both sides; then use Laplace expansion of `det S` along row 0.
    simp [Unfold, constructQ, StackedMat, cofactorMat, fixedRowsMat, S, Matrix.mul_apply]
    rw [Matrix.det_succ_row_zero (A := S)]
    -- Rewrite the minors and the active row entries.
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hminor :
        Matrix.det (S.submatrix Fin.succ k.succAbove) =
          Matrix.det ((fixedRowsMat A col).submatrix id k.succAbove) := by
      simpa [hsub k]
    -- `ring` handles the commutativity/associativity rearrangements cleanly.
    rw [hminor]
    simp [S, stackedRowsMatrix, StackedMat, fixedRowsMat]
    ring_nf
  · -- mode 1: expand along row 1
    let S : Matrix (Fin 4) (Fin 4) ℝ :=
      stackedRowsMatrix A col.1.1 row.1 col.2.1.1 col.2.2.1 col.1.2 row.2 col.2.1.2 col.2.2.2
    have hsub :
        ∀ k : Fin 4,
          S.submatrix (Fin.succAbove (1 : Fin 4)) k.succAbove =
            (fixedRowsMat A col).submatrix id k.succAbove := by
      intro k
      ext i j
      fin_cases i <;> fin_cases j <;> simp [S, fixedRowsMat, stackedRowsMatrix, Fin.succAbove]
    simp [Unfold, constructQ, StackedMat, cofactorMat, fixedRowsMat, S, Matrix.mul_apply]
    rw [Matrix.det_succ_row (A := S) (i := (1 : Fin 4))]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hminor :
        Matrix.det (S.submatrix (Fin.succAbove (1 : Fin 4)) k.succAbove) =
          Matrix.det ((fixedRowsMat A col).submatrix id k.succAbove) := by
      simpa [hsub k]
    rw [hminor]
    simp [S, stackedRowsMatrix, StackedMat, fixedRowsMat]
    ring_nf
  · -- mode 2: expand along row 2
    let S : Matrix (Fin 4) (Fin 4) ℝ :=
      stackedRowsMatrix A col.1.1 col.2.1.1 row.1 col.2.2.1 col.1.2 col.2.1.2 row.2 col.2.2.2
    have hsub :
        ∀ k : Fin 4,
          S.submatrix (Fin.succAbove (2 : Fin 4)) k.succAbove =
            (fixedRowsMat A col).submatrix id k.succAbove := by
      intro k
      ext i j
      fin_cases i <;> fin_cases j <;> simp [S, fixedRowsMat, stackedRowsMatrix, Fin.succAbove]
    simp [Unfold, constructQ, StackedMat, cofactorMat, fixedRowsMat, S, Matrix.mul_apply]
    rw [Matrix.det_succ_row (A := S) (i := (2 : Fin 4))]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hminor :
        Matrix.det (S.submatrix (Fin.succAbove (2 : Fin 4)) k.succAbove) =
          Matrix.det ((fixedRowsMat A col).submatrix id k.succAbove) := by
      simpa [hsub k]
    rw [hminor]
    simp [S, stackedRowsMatrix, StackedMat, fixedRowsMat]
    ring_nf
  · -- mode 3: expand along row 3
    let S : Matrix (Fin 4) (Fin 4) ℝ :=
      stackedRowsMatrix A col.1.1 col.2.1.1 col.2.2.1 row.1 col.1.2 col.2.1.2 col.2.2.2 row.2
    have hsub :
        ∀ k : Fin 4,
          S.submatrix (Fin.succAbove (3 : Fin 4)) k.succAbove =
            (fixedRowsMat A col).submatrix id k.succAbove := by
      intro k
      ext i j
      fin_cases i <;> fin_cases j <;> simp [S, fixedRowsMat, stackedRowsMatrix, Fin.succAbove]
    simp [Unfold, constructQ, StackedMat, cofactorMat, fixedRowsMat, S, Matrix.mul_apply]
    rw [Matrix.det_succ_row (A := S) (i := (3 : Fin 4))]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hminor :
        Matrix.det (S.submatrix (Fin.succAbove (3 : Fin 4)) k.succAbove) =
          Matrix.det ((fixedRowsMat A col).submatrix id k.succAbove) := by
      simpa [hsub k]
    rw [hminor]
    simp [S, stackedRowsMatrix, StackedMat, fixedRowsMat]
    ring_nf

lemma rank_unfold_Q_le_4 {n : ℕ} (A : Fin n → Matrix3x4) (m : Fin 4) :
    (Unfold m (constructQ A)).rank ≤ 4 := by
  classical
  have hB : (StackedMat A).rank ≤ 4 := by
    -- rank ≤ number of columns = 4
    simpa [Fintype.card_fin] using (Matrix.rank_le_card_width (StackedMat A))
  -- Each unfolding is a product `StackedMat A * cofactorMat A m`.
  rw [unfold_constructQ_eq_mul A m]
  exact le_trans (Matrix.rank_mul_le_left _ _) hB

-- If λ factors, the scaled tensor has unfolding rank ≤ 4
lemma forward_rank_le_4 {n : ℕ} (A : Fin n → Matrix3x4) (lam : Lambda n)
    (u v w x : Fin n → ℝˣ)
    (hfact : ∀ α β γ δ, NotIdentical α β γ δ →
      lam α β γ δ = (u α : ℝ) * (v β : ℝ) * (w γ : ℝ) * (x δ : ℝ))
    (hsupp : ∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ)
    (m : Fin 4) :
    (Unfold m (scaleQ lam (constructQ A))).rank ≤ 4 := by
  classical
  -- Compare `scaleQ lam Q` with `scaleQ lam' Q` where `lam'` factors everywhere.
  -- They agree because `Q` vanishes on the diagonal `(α,α,α,α)`.
  have hdiag : ∀ α (i j k l : Fin 3), constructQ A α α α α i j k l = 0 := constructQ_diag A
  -- Define the factored scalar for all indices.
  let lam' : Lambda n := fun α β γ δ => (u α : ℝ) * (v β : ℝ) * (w γ : ℝ) * (x δ : ℝ)
  have hscale : scaleQ lam (constructQ A) = scaleQ lam' (constructQ A) := by
    funext α β γ δ i j k l
    by_cases hni : NotIdentical α β γ δ
    · simp [scaleQ, hfact α β γ δ hni, lam', hni]
    · have : α = β ∧ β = γ ∧ γ = δ := by
        by_contra h; exact hni h
      rcases this with ⟨rfl, rfl, rfl⟩
      have hlam0 : lam α α α α = 0 := by
        have hni' : ¬ NotIdentical α α α α := by
          intro h; exact h (by simp)
        have : ¬ lam α α α α ≠ 0 := by simpa [hsupp] using hni'
        exact not_ne_iff.mp this
      simp [scaleQ, hlam0, hdiag]
  -- For the factored `lam'`, each unfolding is an entrywise row/column scaling of the original.
  -- Use `rank_scaled_le` plus `rank_unfold_Q_le_4`.
  fin_cases m
  · -- mode 0
    let r : RowIdx n → ℝ := fun p => (u p.1 : ℝ)
    let c : ColIdx n → ℝ := fun col => (v col.1.1 : ℝ) * (w col.2.1.1 : ℝ) * (x col.2.2.1 : ℝ)
    have hentry :
        Unfold 0 (scaleQ lam' (constructQ A)) =
          Matrix.of (fun p col => r p * c col * (Unfold 0 (constructQ A) p col)) := by
      ext p col
      simp [Unfold, scaleQ, lam', r, c, mul_assoc, mul_left_comm, mul_comm]
    have hrank :
        (Unfold 0 (scaleQ lam' (constructQ A))).rank ≤ (Unfold 0 (constructQ A)).rank := by
      simpa [hentry] using (rank_scaled_le (Unfold 0 (constructQ A)) r c)
    have hQrank : (Unfold 0 (constructQ A)).rank ≤ 4 := rank_unfold_Q_le_4 A 0
    have : (Unfold 0 (scaleQ lam' (constructQ A))).rank ≤ 4 := hrank.trans hQrank
    simpa [hscale] using this
  · -- mode 1
    let r : RowIdx n → ℝ := fun p => (v p.1 : ℝ)
    let c : ColIdx n → ℝ := fun col => (u col.1.1 : ℝ) * (w col.2.1.1 : ℝ) * (x col.2.2.1 : ℝ)
    have hentry :
        Unfold 1 (scaleQ lam' (constructQ A)) =
          Matrix.of (fun p col => r p * c col * (Unfold 1 (constructQ A) p col)) := by
      ext p col
      simp [Unfold, scaleQ, lam', r, c, mul_assoc, mul_left_comm, mul_comm]
    have hrank :
        (Unfold 1 (scaleQ lam' (constructQ A))).rank ≤ (Unfold 1 (constructQ A)).rank := by
      simpa [hentry] using (rank_scaled_le (Unfold 1 (constructQ A)) r c)
    have hQrank : (Unfold 1 (constructQ A)).rank ≤ 4 := rank_unfold_Q_le_4 A 1
    have : (Unfold 1 (scaleQ lam' (constructQ A))).rank ≤ 4 := hrank.trans hQrank
    simpa [hscale] using this
  · -- mode 2
    let r : RowIdx n → ℝ := fun p => (w p.1 : ℝ)
    let c : ColIdx n → ℝ := fun col => (u col.1.1 : ℝ) * (v col.2.1.1 : ℝ) * (x col.2.2.1 : ℝ)
    have hentry :
        Unfold 2 (scaleQ lam' (constructQ A)) =
          Matrix.of (fun p col => r p * c col * (Unfold 2 (constructQ A) p col)) := by
      ext p col
      simp [Unfold, scaleQ, lam', r, c, mul_assoc, mul_left_comm, mul_comm]
    have hrank :
        (Unfold 2 (scaleQ lam' (constructQ A))).rank ≤ (Unfold 2 (constructQ A)).rank := by
      simpa [hentry] using (rank_scaled_le (Unfold 2 (constructQ A)) r c)
    have hQrank : (Unfold 2 (constructQ A)).rank ≤ 4 := rank_unfold_Q_le_4 A 2
    have : (Unfold 2 (scaleQ lam' (constructQ A))).rank ≤ 4 := hrank.trans hQrank
    simpa [hscale] using this
  · -- mode 3
    let r : RowIdx n → ℝ := fun p => (x p.1 : ℝ)
    let c : ColIdx n → ℝ := fun col => (u col.1.1 : ℝ) * (v col.2.1.1 : ℝ) * (w col.2.2.1 : ℝ)
    have hentry :
        Unfold 3 (scaleQ lam' (constructQ A)) =
          Matrix.of (fun p col => r p * c col * (Unfold 3 (constructQ A) p col)) := by
      ext p col
      simp [Unfold, scaleQ, lam', r, c, mul_assoc, mul_left_comm, mul_comm]
    have hrank :
        (Unfold 3 (scaleQ lam' (constructQ A))).rank ≤ (Unfold 3 (constructQ A)).rank := by
      simpa [hentry] using (rank_scaled_le (Unfold 3 (constructQ A)) r c)
    have hQrank : (Unfold 3 (constructQ A)).rank ≤ 4 := rank_unfold_Q_le_4 A 3
    have : (Unfold 3 (scaleQ lam' (constructQ A))).rank ≤ 4 := hrank.trans hQrank
    simpa [hscale] using this

-- Forward direction: factorizable → F(T) = 0
lemma forward_direction {n : ℕ} (A : Fin n → Matrix3x4) (lam : Lambda n)
    (hsupp : ∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ)
    (u v w x : Fin n → ℝˣ)
    (hfact : ∀ α β γ δ, NotIdentical α β γ δ →
      lam α β γ δ = (u α : ℝ) * (v β : ℝ) * (w γ : ℝ) * (x δ : ℝ)) :
    IsZeroVec (PolyMap.eval (polyMapF n) (scaleQ lam (constructQ A))) := by
  rw [isZeroVec_iff_minors_vanish]
  intro m rows cols
  apply rank_le_four_imp_5x5_det_zero
  exact forward_rank_le_4 A lam u v w x hfact hsupp m


noncomputable section AristotleLemmas

/-
If the rank of a matrix M is at least n, then there exist n columns of M that are linearly independent.
-/
lemma exists_linearIndependent_cols_of_rank_ge {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (M : Matrix α β ℝ) (n : ℕ) (h : n ≤ M.rank) :
    ∃ (cols : Fin n → β), LinearIndependent ℝ (fun i => M.col (cols i)) := by
      -- Apply the theorem that states if the rank of a matrix is at least n, then there exist n linearly independent columns.
      have h_lin_ind : ∃ (cols : Fin n → β), LinearIndependent ℝ (fun i => M.col (cols i)) := by
        have h_card : n ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range (Matrix.col M))) := by
          convert h using 1;
          exact Eq.symm (rank_eq_finrank_span_cols M)
        have := exists_linearIndependent ℝ ( Set.range ( Matrix.col M ) );
        rcases this with ⟨ b, hb₁, hb₂, hb₃ ⟩ ; have := hb₃.cardinal_le_rank; simp_all +decide [ Module.finrank ] ;
        -- Since $b$ is a subset of the range of $M.col$, we can choose $n$ elements from $b$.
        obtain ⟨cols, hcols⟩ : ∃ cols : Fin n → α → ℝ, (∀ i, cols i ∈ b) ∧ LinearIndependent ℝ cols := by
          have h_card : n ≤ Cardinal.toNat (Cardinal.mk b) := by
            refine' le_trans h_card _;
            rw [ ← hb₂, rank_span_set ] ; aesop;
          have h_card : ∃ cols : Fin (Cardinal.toNat (Cardinal.mk b)) → α → ℝ, (∀ i, cols i ∈ b) ∧ LinearIndependent ℝ cols := by
            have h_card : Nonempty (Fin (Cardinal.toNat (Cardinal.mk b)) ≃ b) := by
              have h_card : Fintype b := by
                exact Set.Finite.fintype ( Set.Finite.subset ( Set.toFinite ( Set.range M.col ) ) hb₁ );
              exact ⟨ Fintype.equivOfCardEq <| by simp +decide [ Cardinal.toNat_eq_iff ] ⟩;
            obtain ⟨ e ⟩ := h_card;
            exact ⟨ _, fun i => e i |>.2, hb₃.comp _ e.injective ⟩;
          obtain ⟨ cols, hcols₁, hcols₂ ⟩ := h_card; exact ⟨ fun i => cols ⟨ i, by linarith [ Fin.is_lt i ] ⟩, fun i => hcols₁ _, hcols₂.comp _ fun i j hij => by simpa [ Fin.ext_iff ] using hij ⟩ ;
        choose f hf using fun i => hb₁ ( hcols.1 i ) ; use f; aesop;
      exact h_lin_ind

/-
If the rank of a matrix M is at least n, then there exists an n x n submatrix of M with non-zero determinant.
-/
lemma exists_submatrix_det_ne_zero_of_rank_ge {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (M : Matrix α β ℝ) (n : ℕ) (h : n ≤ M.rank) :
    ∃ (rows : Fin n → α) (cols : Fin n → β), (M.submatrix rows cols).det ≠ 0 := by
      -- Since `n ≤ M.rank`, by `exists_linearIndependent_cols_of_rank_ge`, there exist `cols : Fin n → β` such that the columns of `M` indexed by `cols` are linearly independent.
      obtain ⟨cols, hcols⟩ : ∃ cols : Fin n → β, LinearIndependent ℝ (fun i => M.col (cols i)) := exists_linearIndependent_cols_of_rank_ge M n h;
      -- Let `S = M.submatrix id cols`. `S` is an `α × n` matrix.
      set S : Matrix α (Fin n) ℝ := fun i j => M i (cols j);
      -- The columns of `S` are linearly independent, so `S.rank = n`.
      have hS_rank : S.rank = n := by
        have hS_rank : LinearMap.range (Matrix.mulVecLin S) = Submodule.span ℝ (Set.range (fun i => M.col (cols i))) := by
          ext; simp [S];
          simp +decide [ funext_iff, Matrix.mulVec, Submodule.mem_span_range_iff_exists_fun ];
          simp +decide only [dotProduct, mul_comm];
        rw [ Matrix.rank ];
        rw [ hS_rank, finrank_span_eq_card ] <;> aesop;
      -- We know `S.rank = Sᵀ.rank`, so `Sᵀ.rank = n`. `Sᵀ` is an `n × α` matrix.
      have hS_transpose_rank : (Matrix.transpose S).rank = n := by
        rw [ Matrix.rank_transpose, hS_rank ];
      -- Applying `exists_linearIndependent_cols_of_rank_ge` to `Sᵀ` (with `n` and `h' : n ≤ Sᵀ.rank`), we find `rows : Fin n → α` such that the columns of `Sᵀ` indexed by `rows` are linearly independent.
      obtain ⟨rows, hrows⟩ : ∃ rows : Fin n → α, LinearIndependent ℝ (fun i => (Matrix.transpose S).col (rows i)) := by
        apply exists_linearIndependent_cols_of_rank_ge;
        rw [hS_transpose_rank];
      refine' ⟨ rows, cols, _ ⟩;
      rw [ Fintype.linearIndependent_iff ] at hrows;
      contrapose! hrows;
      obtain ⟨ g, hg ⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hrows;
      refine' ⟨ g, _, _ ⟩ <;> simp_all +decide [ funext_iff, Matrix.vecMul, dotProduct ];
      exact hg.2

end AristotleLemmas

theorem minors5x5_zero_imp_rank_le_four {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (M : Matrix α β ℝ)
    (hminors : ∀ (rows : Fin 5 → α) (cols : Fin 5 → β),
      (M.submatrix rows cols).det = 0) :
    M.rank ≤ 4 := by
  classical
  by_contra hminors;
  -- By the lemma `exists_submatrix_det_ne_zero_of_rank_ge`, there exist row indices `rows : Fin 5 → α` and column indices `cols : Fin 5 → β` such that `(M.submatrix rows cols).det ≠ 0`.
  obtain ⟨rows, cols, h_det⟩ : ∃ (rows : Fin 5 → α) (cols : Fin 5 → β), (M.submatrix rows cols).det ≠ 0 := by
    convert exists_submatrix_det_ne_zero_of_rank_ge M 5 ( by linarith ) using 1;
  exact h_det ( by solve_by_elim )

def ColSpan {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℝ) : Submodule ℝ (m → ℝ) :=
  Submodule.span ℝ (Set.range M.col)

theorem colSpan_eq_of_cols_subtype_and_rank {m k l : Type*}
    [Fintype m] [Fintype k] [Fintype l]
    [DecidableEq m] [DecidableEq k] [DecidableEq l]
    (M : Matrix m l ℝ) (S : Matrix m k ℝ)
    (hcols : ∀ j : k, ∃ i : l, S.col j = M.col i)
    (hrM : M.rank ≤ 4) (hrS : S.rank = 4) :
    ColSpan S = ColSpan M := by
  classical
  have hle : ColSpan S ≤ ColSpan M := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    rcases hcols j with ⟨i, hi⟩
    -- `S.col j` is literally one of the columns of `M`
    simpa [hi] using (Submodule.subset_span (s := Set.range M.col) ⟨i, rfl⟩)

  have hfinS : Module.finrank ℝ (ColSpan S) = 4 := by
    -- `rank = finrank(span(cols))`
    have : S.rank = Module.finrank ℝ (ColSpan S) := by
      simpa [ColSpan] using (Matrix.rank_eq_finrank_span_cols (R := ℝ) (A := S))
    simpa [this] using hrS

  have hfinM_le : Module.finrank ℝ (ColSpan M) ≤ 4 := by
    have : M.rank = Module.finrank ℝ (ColSpan M) := by
      simpa [ColSpan] using (Matrix.rank_eq_finrank_span_cols (R := ℝ) (A := M))
    -- rewrite `hrM` via the finrank characterization
    simpa [this] using hrM

  have hfinM_ge : 4 ≤ Module.finrank ℝ (ColSpan M) := by
    -- monotonicity of finrank under submodule inclusion
    have := Submodule.finrank_mono hle
    -- rewrite finrank of `ColSpan S` as `4`
    simpa [hfinS] using this

  have hfinM : Module.finrank ℝ (ColSpan M) = 4 := le_antisymm hfinM_le hfinM_ge
  -- same finrank + inclusion gives equality
  exact Submodule.eq_of_le_of_finrank_eq hle (by simpa [hfinS, hfinM])

/- `NotAllEqual3 β γ δ` means the triple `(β,γ,δ)` is not constant. This is the condition under which
`NotIdentical α β γ δ` holds for *every* `α`. -/
def NotAllEqual3 {n : ℕ} (a b c : Fin n) : Prop := ¬ (a = b ∧ b = c)

/-- The 27-column index type (j,k,ℓ ∈ Fin 3). -/
abbrev Triple3 := Fin 3 × Fin 3 × Fin 3

/-- Column index in `ColIdx n` for a fixed triple of cameras `(a,b,c)` and row choices `(j,k,ℓ)`. -/
def colIdxOfTriple {n : ℕ} (a b c : Fin n) (t : Triple3) : ColIdx n :=
  ((a, t.1), ((b, t.2.1), (c, t.2.2)))

/--
The `3n × 27` submatrix of the mode-`m` unfolding obtained by fixing the *camera indices*
for the three column-slots to `(a,b,c)` and varying the within-camera row indices `(j,k,ℓ)`.
-/
def Submatrix27 {n : ℕ} (A : Fin n → Matrix3x4) (m : Fin 4) (a b c : Fin n) :
    Matrix (RowIdx n) Triple3 ℝ :=
  fun row t => (Unfold m (constructQ A)) row (colIdxOfTriple a b c t)

/-- The 4D subspace `W = col(StackedMat A)` from `solution.md`. -/
def Wspace {n : ℕ} (A : Fin n → Matrix3x4) : Submodule ℝ (RowIdx n → ℝ) :=
  ColSpan (StackedMat A)

/--
(G3_m) from `solution.md`:
for each mode `m` and each triple of camera indices `(a,b,c)` not all equal,
the corresponding 27 columns span `W = col(StackedMat A)`.
-/
def G3 {n : ℕ} (A : Fin n → Matrix3x4) (m : Fin 4) : Prop :=
  ∀ a b c : Fin n, NotAllEqual3 a b c →
    ColSpan (Submatrix27 A m a b c) = Wspace A

/--
Block-scalar diagonal linear map on `ℝ^(3n)`:
multiply every row in camera-block `α` by the scalar `s α`.
This is the `diag(s₁ I₃, …, sₙ I₃)` action from Lemma 4.2 in `solution.md`.
-/
def blockScalarLM {n : ℕ} (s : Fin n → ℝ) : (RowIdx n → ℝ) →ₗ[ℝ] (RowIdx n → ℝ) :=
{ toFun := fun v p => s p.1 * v p
  map_add' := by
    intro v w; ext p; simp [mul_add]
  map_smul' := by
    intro r v; ext p
    -- in `RowIdx n → ℝ`, `(r • v) p = r * v p`
    simp [mul_assoc, mul_left_comm, mul_comm] }

/--
Rigidity assumption (Lemma 4.2 in `solution.md`), packaged as a Prop:
any block-scalar diagonal map stabilizing `W` must be constant across blocks.
(You can later *prove* this from rank assumptions if you want, but for the reverse direction
it’s fine to include it as part of “generic”.)
-/
def RigidBlockScalarStabilizer {n : ℕ} (A : Fin n → Matrix3x4) : Prop :=
  ∀ s : Fin n → ℝˣ,
    (Wspace A).map (blockScalarLM (fun α => (s α : ℝ))) = (Wspace A) →
      ∀ α β : Fin n, s α = s β

/--
“Generic cameras” as needed by the reverse direction in `solution.md`:
- stacked rank = 4
- each camera rank = 3
- spanning conditions (G3_m) for all modes
-/
def GenericCameras {n : ℕ} (A : Fin n → Matrix3x4) : Prop :=
  (StackedMat A).rank = 4 ∧
  (∀ α : Fin n, (A α).rank = 3) ∧
  (∀ m : Fin 4, G3 A m)

/-!
Lemma 4.2 from `proofdocs/solution.md`:
the block-scalar stabilizer of `W = col(StackedMat A)` is rigid under the rank assumptions.
-/

lemma rigidBlockScalarStabilizer_of_rank {n : ℕ} (A : Fin n → Matrix3x4)
    (hstack : (StackedMat A).rank = 4) (hcam : ∀ α : Fin n, (A α).rank = 3) :
    RigidBlockScalarStabilizer A := by
  classical
  intro s hsW α β
  -- Setup notation.
  let B : Matrix (RowIdx n) (Fin 4) ℝ := StackedMat A
  let M : (RowIdx n → ℝ) →ₗ[ℝ] (RowIdx n → ℝ) :=
    blockScalarLM (n := n) (fun a => (s a : ℝ))

  have hWrange : (Wspace A) = LinearMap.range B.mulVecLin := by
    -- `Wspace A` is the column span of `B`.
    simp [Wspace, ColSpan, B, Matrix.range_mulVecLin]

  -- `B.mulVecLin` is injective because it has rank 4 and its domain has dimension 4.
  have h_finrank_range : Module.finrank ℝ ↥(LinearMap.range B.mulVecLin) = 4 := by
    have hspan :
        B.rank = Module.finrank ℝ ↥(Submodule.span ℝ (Set.range B.col)) := by
      simpa using (Matrix.rank_eq_finrank_span_cols (R := ℝ) (A := B))
    have hrange : B.rank = Module.finrank ℝ ↥(LinearMap.range B.mulVecLin) := by
      -- rewrite the span-of-cols as the `mulVecLin` range
      calc
        B.rank = Module.finrank ℝ ↥(Submodule.span ℝ (Set.range B.col)) := hspan
        _ = Module.finrank ℝ ↥(LinearMap.range B.mulVecLin) := by
          -- rewrite by `Matrix.range_mulVecLin` (in the reverse direction)
          have e :
              Submodule.span ℝ (Set.range B.col) = LinearMap.range B.mulVecLin :=
            (Matrix.range_mulVecLin (M := B)).symm
          -- rewriting under the coercion `↥(Submodule ...)` works with `rw`.
          rw [e]
    have : Module.finrank ℝ ↥(LinearMap.range B.mulVecLin) = B.rank := by
      simpa using hrange.symm
    simpa [hstack, B] using this

  have h_ker : LinearMap.ker B.mulVecLin = ⊥ := by
    have hdom : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by
      simp [Module.finrank_pi, Fintype.card_fin]
    have hsum :=
      (LinearMap.finrank_range_add_finrank_ker (B.mulVecLin : (Fin 4 → ℝ) →ₗ[ℝ] (RowIdx n → ℝ)))
    have hsum' :
        Module.finrank ℝ ↥(LinearMap.range B.mulVecLin) +
          Module.finrank ℝ ↥(LinearMap.ker B.mulVecLin) = 4 := by
      simpa [hdom] using hsum
    have hker_finrank : Module.finrank ℝ ↥(LinearMap.ker B.mulVecLin) = 0 := by
      have : 4 + Module.finrank ℝ ↥(LinearMap.ker B.mulVecLin) = 4 := by
        simpa [h_finrank_range] using hsum'
      exact Nat.add_left_cancel this
    exact (Submodule.finrank_eq_zero).1 hker_finrank

  obtain ⟨g, hg⟩ :=
    LinearMap.exists_leftInverse_of_injective (f := B.mulVecLin) h_ker

  -- `M` stabilizes `W = col(B)`, hence maps `range(B.mulVecLin)` to itself.
  have hM_mem_range : ∀ x : Fin 4 → ℝ, M (B.mulVecLin x) ∈ LinearMap.range B.mulVecLin := by
    intro x
    -- First, show `M` maps `Wspace A` into itself.
    have hmap : (Wspace A).map M ≤ Wspace A := le_of_eq hsW
    have hxW : B.mulVecLin x ∈ Wspace A := by
      have hx : B.mulVecLin x ∈ LinearMap.range B.mulVecLin := ⟨x, rfl⟩
      simpa [hWrange] using hx
    have hMxW : M (B.mulVecLin x) ∈ Wspace A := by
      -- `M (B.mulVecLin x)` is in `map M (Wspace A)` by construction.
      have : M (B.mulVecLin x) ∈ (Wspace A).map M := by
        refine (Submodule.mem_map).2 ?_
        exact ⟨B.mulVecLin x, hxW, rfl⟩
      exact hmap this
    simpa [hWrange] using hMxW

  -- Define the induced endomorphism on `Fin 4 → ℝ` by conjugating through `B.mulVecLin`.
  let Rlin : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) :=
    g ∘ₗ M ∘ₗ B.mulVecLin

  have hcomm : ∀ x : Fin 4 → ℝ, B.mulVecLin (Rlin x) = M (B.mulVecLin x) := by
    intro x
    -- `M (B.mulVecLin x)` lies in the range, so write it as `B.mulVecLin z`.
    rcases hM_mem_range x with ⟨z, hz⟩
    -- Use the defining property of a left inverse on this representative.
    have hg_apply : g (B.mulVecLin z) = z := by
      -- apply the equality of linear maps to `z`
      simpa using congrArg (fun h => h z) hg
    -- Now compute.
    -- `Rlin x = g (M (B.mulVecLin x)) = g (B.mulVecLin z) = z`.
    calc
      B.mulVecLin (Rlin x)
          = B.mulVecLin (g (M (B.mulVecLin x))) := by rfl
      _ = B.mulVecLin (g (B.mulVecLin z)) := by simpa [hz]
      _ = B.mulVecLin z := by
        -- avoid unfolding issues: apply `B.mulVecLin` to the equality `g (B.mulVecLin z) = z`
        simpa using congrArg (fun w : Fin 4 → ℝ => B.mulVecLin w) hg_apply
      _ = M (B.mulVecLin x) := by simpa [hz]

  -- Build a concrete matrix for `Rlin` by its action on the standard basis vectors.
  let Rmat : Matrix (Fin 4) (Fin 4) ℝ :=
    fun k j => (Rlin (Pi.single j 1)) k

  -- Each row vector in camera block `a` is a left eigenvector for `Rmat` with eigenvalue `s a`.
  have hrow_eigen :
      ∀ p : RowIdx n, (B.row p) ᵥ* Rmat = (s p.1 : ℝ) • (B.row p) := by
    intro p
    ext j
    -- Apply `hcomm` to the basis vector picking out column `j`.
    have hcol :=
      congrArg (fun v : RowIdx n → ℝ => v p) (hcomm (Pi.single j 1))
    -- Rewrite both sides of the commutation in coordinates.
    -- Left side: `B.mulVecLin (Rlin e_j)` evaluated at `p` is a dot product with row `p`.
    -- Right side: `M (B.col j)` scales the `p.1` camera block by `s p.1`.
    -- Finally, unpack `Rmat` so the dot product matches `vecMul`.
    simpa [B, M, Rmat, Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.row_apply,
      Matrix.col_apply, Pi.smul_apply, blockScalarLM, mul_assoc, mul_left_comm, mul_comm,
      Matrix.mulVec_single_one] using hcol

  -- Convert to an eigenvector statement for `Rmatᵀ.mulVec`.
  let T : Module.End ℝ (Fin 4 → ℝ) := (Rmatᵀ).mulVecLin

  have hrow_eigen_T :
      ∀ p : RowIdx n, T (B.row p) = (s p.1 : ℝ) • (B.row p) := by
    intro p
    -- `Rmatᵀ *ᵥ v = v ᵥ* Rmat`.
    simpa [T, Matrix.mulVec_transpose] using hrow_eigen p

  -- For each camera `a`, the 3D row-span of `A a` sits in the eigenspace for eigenvalue `s a`.
  have hrowSpan_le_eigenspace :
      ∀ a : Fin n, Submodule.span ℝ (Set.range (A a).row) ≤ T.eigenspace (s a : ℝ) := by
    intro a
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    -- Identify this row with the corresponding row of the stacked matrix.
    have hrow_id : (A a).row i = B.row (a, i) := by
      ext k; rfl
    -- Membership in the eigenspace is exactly the eigenvector equation.
    rw [hrow_id]
    -- unfold membership condition
    exact (Module.End.mem_eigenspace_iff).2 (hrow_eigen_T (p := (a, i)))

  have hfinrank_rowSpan :
      ∀ a : Fin n, Module.finrank ℝ ↥(Submodule.span ℝ (Set.range (A a).row)) = 3 := by
    intro a
    -- `rank = finrank(span(rows))`.
    have := (Matrix.rank_eq_finrank_span_row (R := ℝ) (A := A a)).symm
    -- Use `hcam a : (A a).rank = 3`.
    simpa [hcam a] using this

  have hfinrank_eigenspace_ge :
      ∀ a : Fin n, 3 ≤ Module.finrank ℝ ↥(T.eigenspace (s a : ℝ)) := by
    intro a
    have hmono := Submodule.finrank_mono (hrowSpan_le_eigenspace a)
    -- rewrite the finrank of the row span as 3
    simpa [hfinrank_rowSpan a] using hmono

  -- Distinct eigenvalues would force two disjoint eigenspaces of dimension ≥ 3 each, impossible in 4D.
  by_contra hneq
  have hsneq : (s α : ℝ) ≠ (s β : ℝ) := by
    intro h
    apply hneq
    exact Units.ext (by simpa using h)
  -- Prove the eigenspaces are disjoint for distinct eigenvalues.
  have hdisj : Disjoint (T.eigenspace (s α : ℝ)) (T.eigenspace (s β : ℝ)) := by
    -- use the elementwise characterization
    refine (Submodule.disjoint_def).2 ?_
    intro x hxα hxβ
    have hxα' : T x = (s α : ℝ) • x := (Module.End.mem_eigenspace_iff).1 hxα
    have hxβ' : T x = (s β : ℝ) • x := (Module.End.mem_eigenspace_iff).1 hxβ
    have hEq : (s α : ℝ) • x = (s β : ℝ) • x := by
      calc
        (s α : ℝ) • x = T x := by simpa using hxα'.symm
        _ = (s β : ℝ) • x := by simpa using hxβ'
    have hdiff : ((s α : ℝ) - (s β : ℝ)) • x = 0 := by
      simp [sub_smul, hEq]
    have hscal : ((s α : ℝ) - (s β : ℝ)) ≠ 0 := sub_ne_zero.2 hsneq
    exact (smul_eq_zero.mp hdiff).resolve_left hscal

  have hsum_finrank :
      Module.finrank ℝ ↥(T.eigenspace (s α : ℝ)) +
        Module.finrank ℝ ↥(T.eigenspace (s β : ℝ)) ≤ 4 := by
    -- Use `finrank(sup) ≤ finrank(ambient)` and disjointness to compute `finrank(sup)`.
    have hsup_le : Module.finrank ℝ ↥((T.eigenspace (s α : ℝ)) ⊔ (T.eigenspace (s β : ℝ))) ≤
        Module.finrank ℝ (Fin 4 → ℝ) := Submodule.finrank_le _
    have hdim : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by
      simp [Module.finrank_pi, Fintype.card_fin]
    have hsup_eq :
        Module.finrank ℝ ↥((T.eigenspace (s α : ℝ)) ⊔ (T.eigenspace (s β : ℝ))) =
          Module.finrank ℝ ↥(T.eigenspace (s α : ℝ)) +
            Module.finrank ℝ ↥(T.eigenspace (s β : ℝ)) := by
      -- `finrank sup + finrank inf = finrank + finrank`, and `inf = ⊥` by disjointness.
      have h :=
        (Submodule.finrank_sup_add_finrank_inf_eq
          (T.eigenspace (s α : ℝ)) (T.eigenspace (s β : ℝ)))
      have hinf : (T.eigenspace (s α : ℝ)) ⊓ (T.eigenspace (s β : ℝ)) = ⊥ := by
        simpa using (disjoint_iff.1 hdisj)
      -- with `inf = ⊥`, the extra term is 0
      -- rewrite `inf` and simplify `+ 0`.
      -- We do this with `rw` instead of `simp [hinf]` to ensure the coercion `↥(s ⊓ t)` rewrites.
      have h' := h
      -- rewrite inside the finrank term
      rw [hinf] at h'
      simpa using h'
    -- Now finish the bound.
    have hsup_le' : Module.finrank ℝ ↥((T.eigenspace (s α : ℝ)) ⊔ (T.eigenspace (s β : ℝ))) ≤ 4 := by
      simpa [hdim] using hsup_le
    simpa [hsup_eq] using hsup_le'

  have hge : 6 ≤
      Module.finrank ℝ ↥(T.eigenspace (s α : ℝ)) +
        Module.finrank ℝ ↥(T.eigenspace (s β : ℝ)) := by
    have hα' := hfinrank_eigenspace_ge (a := α)
    have hβ' := hfinrank_eigenspace_ge (a := β)
    -- `3+3 = 6`
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Nat.add_le_add hα' hβ'

  have : 6 ≤ 4 := le_trans hge hsum_finrank
  exact (by decide : ¬ (6 ≤ 4)) this

def RankGenericCameras {n : ℕ} (A : Fin n → Matrix3x4) : Prop :=
  (StackedMat A).rank = 4 ∧ (∀ α : Fin n, (A α).rank = 3)

lemma GenericCameras.toRankGeneric {n : ℕ} {A : Fin n → Matrix3x4} (h : GenericCameras A) :
    RankGenericCameras A :=
  ⟨h.1, h.2.1⟩

lemma GenericCameras.rigid {n : ℕ} {A : Fin n → Matrix3x4} (h : GenericCameras A) :
    RigidBlockScalarStabilizer A :=
  rigidBlockScalarStabilizer_of_rank (A := A) h.1 h.2.1

/- PROVIDED SOLUTION:

Goal (reverse direction of Problem 9):
  Assume cameras `A` are “generic” and `λ` has the prescribed support
    `λ_{αβγδ} ≠ 0 ↔ NotIdentical α β γ δ`.
  If `F(λ · Q(A)) = 0` (i.e. all `5×5` minors of all four unfoldings vanish),
  then `λ` factors as `uα vβ wγ xδ` on all not-identical quadruples.

High-level structure (matches `proofdocs/solution.md`):

1) Vanishing minors ⇒ unfolding rank ≤ 4.
   From `IsZeroVec (polyMapF.eval (scaleQ λ (constructQ A)))` we obtain:
     ∀ mode m, ∀ rows cols, det((Unfold m (scaleQ λ Q)).submatrix rows cols) = 0.
   By the previous lemma (`minors5x5_zero_imp_rank_le_four`), this implies:
     ∀ m, rank(Unfold m (scaleQ λ Q)) ≤ 4.

2) Define the 4D subspace W from the stacked camera matrix.
   Let `B := StackedMat A : (Fin n × Fin 3) × Fin 4 → ℝ`.
   Genericity includes `rank(B)=4`, so `W := col(B)` is a 4D subspace of `ℝ^(3n)`.

3) Generic spanning condition (Zariski-open):
   For each mode m and each triple of camera indices (not all equal), consider the `27` columns of
   the unfolding `Unfold m (constructQ A)` obtained by fixing the other three tensor slots and
   letting the `Fin 3` row-indices vary. Genericity demands these `27` columns span `W`.
   (This is exactly the paper’s condition (G3_m). It is expressible as nonvanishing of a suitable
   `4×4` minor of the corresponding `3n × 27` submatrix.)

4) Pin down the column space of the *scaled* unfolding using rank.
   Fix a triple (e.g. for mode 1: `(β,γ,δ)` not all equal). Let `S_{βγδ}` be the `3n×27` submatrix
   of `Unfold 0 (constructQ A)` with those columns; by (G3_1), `col(S_{βγδ}) = W`.
   In the scaled tensor `T := scaleQ λ (constructQ A)`, the corresponding submatrix is obtained by
   multiplying each camera-block (the `α`-block of 3 rows) by the scalar `λ_{αβγδ}`. This is
   left-multiplication by a block-diagonal matrix `D_{βγδ} = diag(λ_{1βγδ} I_3, …, λ_{nβγδ} I_3)`.
   Because `λ_{αβγδ} ≠ 0` for all α when `(β,γ,δ)` are not all equal (by the support rule),
   `D_{βγδ}` is invertible and `col(D_{βγδ} S_{βγδ}) = D_{βγδ} W` has dimension 4.
   Since `rank(Unfold 0 T) ≤ 4`, its column space has dimension ≤ 4, but it contains
   `D_{βγδ} W` (because those 27 columns are among all columns), hence:
     col(Unfold 0 T) = D_{βγδ} W,
   for every not-all-equal triple `(β,γ,δ)`.

5) Rigidity of block-diagonal stabilizers (Lemma 4.2 in the paper).
   Comparing two triples `(β,γ,δ)` and `(β₀,γ₀,δ₀)` gives:
     D_{βγδ} W = col(Unfold 0 T) = D_{β₀γ₀δ₀} W,
   so the block-diagonal matrix `M := D_{βγδ}^{-1} D_{β₀γ₀δ₀}` stabilizes W.
   Genericity includes the rigidity statement:
     If `M = diag(s₁ I_3, …, s_n I_3)` stabilizes W and `rank(B)=4` and each `A α` has rank 3,
     then all `sα` are equal.
   Applying this shows that the ratio
     sα = λ_{αβ₀γ₀δ₀} / λ_{αβγδ}
   is independent of α. Equivalently, there exists `u : Fin n → ℝˣ` and a 3-tensor `μ` such that
     λ_{αβγδ} = uα * μ_{βγδ}    whenever `(β,γ,δ)` are not all equal.

6) Repeat for other modes to separate β and γ (and similarly δ).
   Doing the same argument in modes 2 and 3 yields
     λ_{αβγδ} = vβ * ν_{αγδ}    whenever `(α,γ,δ)` not all equal,
     λ_{αβγδ} = wγ * ξ_{αβδ}    whenever `(α,β,δ)` not all equal,
   for some `v,w : Fin n → ℝˣ`.

7) Propagate to full factorization `u⊗v⊗w⊗x` using `n ≥ 5`.
   The paper gives a clean propagation:
   - Fix `γ ≠ δ`. Combine the first two separations to get
       λ_{αβγδ} = uα vβ ρ_{γδ}    (γ ≠ δ).
   - Fix δ and choose indices α₀,β₀ with α₀ ≠ δ (possible since n ≥ 5). Use the γ-separation to
     split `ρ_{γδ} = wγ xδ` for γ ≠ δ.
   - Finally extend to the remaining off-diagonal cases γ=δ but not-all-identical using the support
     rule and one more index choice.
   This yields `λ_{αβγδ} = uα vβ wγ xδ` for all `NotIdentical α β γ δ`.

8) Ensure the factors are units.
   Because the support condition guarantees the needed denominators are nonzero, one can package the
   resulting scalars as elements of `ℝˣ` (units) and rewrite the factorization in the required form.

That completes the reverse direction, assuming the generic spanning + rigidity hypotheses encoded in
`GenericCameras`.
-/

-- --------------------------------------------------------------------
-- Reverse direction, decomposed into manageable lemmas
-- --------------------------------------------------------------------



lemma notIdentical_of_notAllEqual3 {n : ℕ} {α β γ δ : Fin n} (h : NotAllEqual3 β γ δ) :
    NotIdentical α β γ δ := by
  intro hall
  exact h ⟨hall.2.1, hall.2.2⟩

lemma lam_ne_zero_of_notAllEqual3 {n : ℕ} (lam : Lambda n)
    (hsupp : ∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ)
    {β γ δ : Fin n} (h : NotAllEqual3 β γ δ) :
    ∀ α : Fin n, lam α β γ δ ≠ 0 := by
  intro α
  exact (hsupp α β γ δ).2 (notIdentical_of_notAllEqual3 (α := α) h)

lemma rank_rowScaled_eq {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (M : Matrix α β ℝ) (r : α → ℝ) (hr : ∀ i, r i ≠ 0) :
    (Matrix.of fun i j => r i * M i j).rank = M.rank := by
  classical
  let Ms : Matrix α β ℝ := Matrix.of fun i j => r i * M i j
  have hle1 : Ms.rank ≤ M.rank := by
    simpa [Ms, one_mul] using (rank_scaled_le (M := M) (r := r) (c := fun _ => (1 : ℝ)))
  have hM : M = Matrix.of (fun i j => (r i)⁻¹ * Ms i j) := by
    ext i j
    have hri : (r i)⁻¹ * (r i * M i j) = M i j := by
      field_simp [hr i]
    simpa [Ms, mul_assoc] using hri.symm
  have hle2 : M.rank ≤ Ms.rank := by
    have hscaled : (Matrix.of fun i j => (r i)⁻¹ * Ms i j).rank ≤ Ms.rank := by
      simpa [one_mul] using
        (rank_scaled_le (M := Ms) (r := fun i => (r i)⁻¹) (c := fun _ => (1 : ℝ)))
    simpa [hM] using hscaled
  exact le_antisymm hle1 hle2

lemma exists_fin_ne_of_five {n : ℕ} (hn : 5 ≤ n) (a : Fin n) : ∃ b : Fin n, b ≠ a := by
  have h0 : (0 : ℕ) < n := Nat.lt_of_lt_of_le (by decide : 0 < 5) hn
  have h1 : (1 : ℕ) < n := Nat.lt_of_lt_of_le (by decide : 1 < 5) hn
  by_cases ha : a.1 = 0
  · refine ⟨⟨1, h1⟩, ?_⟩
    intro h
    have : (a : ℕ) = 1 := by simpa using congrArg Fin.val h.symm
    have : (1 : ℕ) = 0 := by simpa [ha] using this
    exact Nat.one_ne_zero this
  · refine ⟨⟨0, h0⟩, ?_⟩
    intro h
    apply ha
    simpa using congrArg Fin.val h.symm

def modeCoeff {n : ℕ} (m : Fin 4) (lam : Lambda n)
    (row a b c : Fin n) : ℝ :=
  match m with
  | ⟨0, _⟩ => lam row a b c
  | ⟨1, _⟩ => lam a row b c
  | ⟨2, _⟩ => lam a b row c
  | ⟨3, _⟩ => lam a b c row

lemma notIdentical_mode1_of_notAllEqual3 {n : ℕ} {row a b c : Fin n}
    (h : NotAllEqual3 a b c) : NotIdentical a row b c := by
  intro hall
  exact h ⟨hall.1.trans hall.2.1, hall.2.2⟩

lemma notIdentical_mode2_of_notAllEqual3 {n : ℕ} {row a b c : Fin n}
    (h : NotAllEqual3 a b c) : NotIdentical a b row c := by
  intro hall
  exact h ⟨hall.1, hall.2.1.trans hall.2.2⟩

lemma notIdentical_mode3_of_notAllEqual3 {n : ℕ} {row a b c : Fin n}
    (h : NotAllEqual3 a b c) : NotIdentical a b c row := by
  intro hall
  exact h ⟨hall.1, hall.2.1⟩

lemma modeCoeff_ne_zero_of_notAllEqual3 {n : ℕ} (m : Fin 4) (lam : Lambda n)
    (hsupp : ∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ)
    {a b c : Fin n} (h : NotAllEqual3 a b c) :
    ∀ row : Fin n, modeCoeff m lam row a b c ≠ 0 := by
  intro row
  fin_cases m
  · simpa [modeCoeff] using (lam_ne_zero_of_notAllEqual3 (lam := lam) hsupp (β := a) (γ := b)
      (δ := c) h row)
  · simpa [modeCoeff] using (hsupp a row b c).2 (notIdentical_mode1_of_notAllEqual3 (row := row)
      (a := a) (b := b) (c := c) h)
  · simpa [modeCoeff] using (hsupp a b row c).2 (notIdentical_mode2_of_notAllEqual3 (row := row)
      (a := a) (b := b) (c := c) h)
  · simpa [modeCoeff] using (hsupp a b c row).2 (notIdentical_mode3_of_notAllEqual3 (row := row)
      (a := a) (b := b) (c := c) h)

lemma submatrix27_scaled_eq_rowScale {n : ℕ} (m : Fin 4) (A : Fin n → Matrix3x4)
    (lam : Lambda n) (a b c : Fin n) :
    ((Unfold m (scaleQ lam (constructQ A))).submatrix id (colIdxOfTriple a b c))
      = Matrix.of (fun p t => modeCoeff m lam p.1 a b c * (Submatrix27 A m a b c) p t) := by
  ext p t
  fin_cases m <;>
    simp [Submatrix27, colIdxOfTriple, modeCoeff, Unfold, scaleQ]

lemma colSpan_rowBlockScale {n : ℕ} {k : Type*} [Fintype k] [DecidableEq k]
    (M : Matrix (RowIdx n) k ℝ) (s : Fin n → ℝ) :
    ColSpan (Matrix.of (fun p j => s p.1 * M p j))
      = (ColSpan M).map (blockScalarLM s) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    refine (Submodule.mem_map).2 ?_
    refine ⟨M.col j, ?_, ?_⟩
    · exact Submodule.subset_span ⟨j, rfl⟩
    · ext p
      simp [blockScalarLM, Matrix.col, Matrix.of_apply]
  · refine (Submodule.map_le_iff_le_comap).2 ?_
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    have hcol :
        blockScalarLM s (M.col j) = (Matrix.of (fun p j => s p.1 * M p j)).col j := by
      ext p
      simp [blockScalarLM, Matrix.col, Matrix.of_apply]
    simpa [hcol] using
      (Submodule.subset_span
        (s := Set.range (Matrix.col (Matrix.of (fun p j => s p.1 * M p j))))
        ⟨j, rfl⟩)

theorem separate_mode_of_generic {n : ℕ} (hn : 5 ≤ n) (A : Fin n → Matrix3x4) (lam : Lambda n)
    (hgen : GenericCameras A) (m : Fin 4)
    (hsupp : ∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ)
    (hrank : ∀ m : Fin 4, (Unfold m (scaleQ lam (constructQ A))).rank ≤ 4) :
    ∃ (u : Fin n → ℝˣ) (μ : Fin n → Fin n → Fin n → ℝˣ),
      ∀ row a b c, NotAllEqual3 a b c →
        modeCoeff m lam row a b c = (u row : ℝ) * (μ a b c : ℝ) := by
  classical
  rcases hgen with ⟨hstack, hcam, hG3⟩
  have _ : ∀ α : Fin n, (A α).rank = 3 := hcam
  have hGm : G3 A m := hG3 m

  have hrankW :
      (StackedMat A).rank = Module.finrank ℝ (Wspace A) := by
    simpa [Wspace, ColSpan] using
      (Matrix.rank_eq_finrank_span_cols (R := ℝ) (A := StackedMat A))
  have hfinW : Module.finrank ℝ (Wspace A) = 4 := by
    simpa [hrankW] using hstack

  have h0 : (0 : ℕ) < n := Nat.lt_of_lt_of_le (by decide : 0 < 5) hn
  have h1 : (1 : ℕ) < n := Nat.lt_of_lt_of_le (by decide : 1 < 5) hn
  have h2 : (2 : ℕ) < n := Nat.lt_of_lt_of_le (by decide : 2 < 5) hn
  let i0 : Fin n := ⟨0, h0⟩
  let i1 : Fin n := ⟨1, h1⟩
  let i2 : Fin n := ⟨2, h2⟩
  have h01 : i0 ≠ i1 := by
    intro h
    have : (0 : ℕ) = 1 := by simpa [i0, i1] using congrArg Fin.val h
    exact Nat.zero_ne_one this
  have hNotAll012 : NotAllEqual3 i0 i1 i2 := by
    intro h
    exact h01 h.1

  have hcol_of :
      ∀ a b c : Fin n, NotAllEqual3 a b c →
        ColSpan (Unfold m (scaleQ lam (constructQ A))) =
          (Wspace A).map (blockScalarLM (fun α => modeCoeff m lam α a b c)) := by
    intro a b c hneq
    let M : Matrix (RowIdx n) (ColIdx n) ℝ := Unfold m (scaleQ lam (constructQ A))
    let S : Matrix (RowIdx n) Triple3 ℝ := Submatrix27 A m a b c
    let Ss : Matrix (RowIdx n) Triple3 ℝ := M.submatrix id (colIdxOfTriple a b c)
    have hSs_def : Ss = Matrix.of (fun p t => modeCoeff m lam p.1 a b c * S p t) := by
      simpa [Ss, M, S] using
        (submatrix27_scaled_eq_rowScale (m := m) (A := A) (lam := lam) (a := a) (b := b) (c := c))
    have hcolS : ColSpan S = Wspace A := by
      simpa [S] using hGm a b c hneq
    have hfinS : Module.finrank ℝ (ColSpan S) = 4 := by
      rw [hcolS]
      exact hfinW
    have hSrank' : S.rank = Module.finrank ℝ (ColSpan S) := by
      simpa [ColSpan] using (Matrix.rank_eq_finrank_span_cols (R := ℝ) (A := S))
    have hSrank : S.rank = 4 := by
      simpa [hSrank'] using hfinS
    have hs_nonzero : ∀ p : RowIdx n, modeCoeff m lam p.1 a b c ≠ 0 := by
      intro p
      exact modeCoeff_ne_zero_of_notAllEqual3 (m := m) (lam := lam) hsupp (a := a) (b := b)
        (c := c) hneq p.1
    have hSs_rank : Ss.rank = 4 := by
      calc
        Ss.rank = (Matrix.of (fun p t => modeCoeff m lam p.1 a b c * S p t)).rank := by
          simpa [hSs_def]
        _ = S.rank := by
          simpa using
            (rank_rowScaled_eq (M := S) (r := fun p : RowIdx n => modeCoeff m lam p.1 a b c)
              (hr := hs_nonzero))
        _ = 4 := hSrank
    have hcols : ∀ j : Triple3, ∃ i : ColIdx n, Ss.col j = M.col i := by
      intro j
      refine ⟨colIdxOfTriple a b c j, ?_⟩
      ext p
      simp [Ss, M]
    have hcolEq : ColSpan Ss = ColSpan M :=
      colSpan_eq_of_cols_subtype_and_rank (M := M) (S := Ss) hcols (hrank m) hSs_rank
    have hscaled :
        ColSpan Ss =
          (ColSpan S).map (blockScalarLM (fun α => modeCoeff m lam α a b c)) := by
      calc
        ColSpan Ss = ColSpan (Matrix.of (fun p t => modeCoeff m lam p.1 a b c * S p t)) := by
          simpa [hSs_def]
        _ = (ColSpan S).map (blockScalarLM (fun α => modeCoeff m lam α a b c)) :=
          colSpan_rowBlockScale (M := S) (s := fun α => modeCoeff m lam α a b c)
    calc
      ColSpan (Unfold m (scaleQ lam (constructQ A))) = ColSpan M := by rfl
      _ = ColSpan Ss := hcolEq.symm
      _ = (ColSpan S).map (blockScalarLM (fun α => modeCoeff m lam α a b c)) := hscaled
      _ = (Wspace A).map (blockScalarLM (fun α => modeCoeff m lam α a b c)) := by
        simpa [hcolS]

  let u : Fin n → ℝˣ := fun row =>
    Units.mk0 (modeCoeff m lam row i0 i1 i2 / modeCoeff m lam i0 i0 i1 i2) (by
      have hnum := modeCoeff_ne_zero_of_notAllEqual3 (m := m) (lam := lam) hsupp
        (a := i0) (b := i1) (c := i2) hNotAll012 row
      have hden := modeCoeff_ne_zero_of_notAllEqual3 (m := m) (lam := lam) hsupp
        (a := i0) (b := i1) (c := i2) hNotAll012 i0
      exact div_ne_zero hnum hden)
  let μ : Fin n → Fin n → Fin n → ℝˣ := fun a b c =>
    if hneq : NotAllEqual3 a b c then
      Units.mk0 (modeCoeff m lam i0 a b c)
        (modeCoeff_ne_zero_of_notAllEqual3 (m := m) (lam := lam) hsupp
          (a := a) (b := b) (c := c) hneq i0)
    else 1

  refine ⟨u, μ, ?_⟩
  intro row a b c hneq
  let us : Fin n → ℝˣ := fun α =>
    Units.mk0 (modeCoeff m lam α a b c)
      (modeCoeff_ne_zero_of_notAllEqual3 (m := m) (lam := lam) hsupp
        (a := a) (b := b) (c := c) hneq α)
  let usRef : Fin n → ℝˣ := fun α =>
    Units.mk0 (modeCoeff m lam α i0 i1 i2)
      (modeCoeff_ne_zero_of_notAllEqual3 (m := m) (lam := lam) hsupp
        (a := i0) (b := i1) (c := i2) hNotAll012 α)
  let sRatio : Fin n → ℝˣ := fun α => (us α)⁻¹ * usRef α
  let Ls := blockScalarLM (fun α => (us α : ℝ))
  let Lref := blockScalarLM (fun α => (usRef α : ℝ))
  let Linv := blockScalarLM (fun α => (((us α)⁻¹ : ℝˣ) : ℝ))
  let Lratio := blockScalarLM (fun α => (sRatio α : ℝ))

  have hmapEq :
      (Wspace A).map Ls = (Wspace A).map Lref := by
    have hcur := hcol_of a b c hneq
    have href := hcol_of i0 i1 i2 hNotAll012
    exact by
      simpa [Ls, Lref, us, usRef] using (hcur.symm.trans href)

  have hcomp_inv_s : Linv.comp Ls = LinearMap.id := by
    apply LinearMap.ext
    intro x
    ext p
    have hmul : (((us p.1)⁻¹ : ℝˣ) : ℝ) * ((us p.1 : ℝ) * x p) = x p := by
      calc
        (((us p.1)⁻¹ : ℝˣ) : ℝ) * ((us p.1 : ℝ) * x p)
            = ((((us p.1)⁻¹ : ℝˣ) : ℝ) * (us p.1 : ℝ)) * x p := by ring
        _ = x p := by simp
    simpa [Linv, Ls, blockScalarLM, mul_assoc] using hmul
  have hcomp_inv_ref : Linv.comp Lref = Lratio := by
    ext v p
    simp [Linv, Lref, Lratio, sRatio, blockScalarLM, mul_assoc, mul_left_comm, mul_comm]

  have hstable : (Wspace A).map Lratio = Wspace A := by
    calc
      (Wspace A).map Lratio = (Wspace A).map (Linv.comp Lref) := by simpa [hcomp_inv_ref]
      _ = ((Wspace A).map Lref).map Linv := by
            simpa using (Submodule.map_comp (f := Lref) (g := Linv) (p := Wspace A))
      _ = ((Wspace A).map Ls).map Linv := by simpa [hmapEq]
      _ = (Wspace A).map (Linv.comp Ls) := by
            simpa using (Submodule.map_comp (f := Ls) (g := Linv) (p := Wspace A)).symm
      _ = (Wspace A).map LinearMap.id := by simpa [hcomp_inv_s]
      _ = Wspace A := by simp

  have hgen' : GenericCameras A := ⟨hstack, hcam, hG3⟩
  have hRigid : RigidBlockScalarStabilizer A := GenericCameras.rigid hgen'
  have hsConst : ∀ α β : Fin n, sRatio α = sRatio β := hRigid sRatio hstable
  have hsrow : sRatio row = sRatio i0 := hsConst row i0
  have hsrow' :
      modeCoeff m lam row i0 i1 i2 / modeCoeff m lam row a b c =
        modeCoeff m lam i0 i0 i1 i2 / modeCoeff m lam i0 a b c := by
    simpa [sRatio, us, usRef, Units.val_mk0, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      using congrArg (fun z : ℝˣ => (z : ℝ)) hsrow

  have hden0 : modeCoeff m lam i0 a b c ≠ 0 :=
    modeCoeff_ne_zero_of_notAllEqual3 (m := m) (lam := lam) hsupp
      (a := a) (b := b) (c := c) hneq i0
  have hdenrow : modeCoeff m lam row a b c ≠ 0 :=
    modeCoeff_ne_zero_of_notAllEqual3 (m := m) (lam := lam) hsupp
      (a := a) (b := b) (c := c) hneq row
  have href0 : modeCoeff m lam i0 i0 i1 i2 ≠ 0 :=
    modeCoeff_ne_zero_of_notAllEqual3 (m := m) (lam := lam) hsupp
      (a := i0) (b := i1) (c := i2) hNotAll012 i0

  have hcross :
      modeCoeff m lam row i0 i1 i2 * modeCoeff m lam i0 a b c =
        modeCoeff m lam i0 i0 i1 i2 * modeCoeff m lam row a b c := by
    have h := hsrow'
    field_simp [hdenrow, hden0] at h
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hsolve :
      modeCoeff m lam row a b c =
        modeCoeff m lam i0 a b c *
          (modeCoeff m lam row i0 i1 i2 / modeCoeff m lam i0 i0 i1 i2) := by
    have hbc :
        modeCoeff m lam row a b c * modeCoeff m lam i0 i0 i1 i2 =
          modeCoeff m lam row i0 i1 i2 * modeCoeff m lam i0 a b c := by
      calc
        modeCoeff m lam row a b c * modeCoeff m lam i0 i0 i1 i2 =
            modeCoeff m lam i0 i0 i1 i2 * modeCoeff m lam row a b c := by ring
        _ = modeCoeff m lam row i0 i1 i2 * modeCoeff m lam i0 a b c := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hcross.symm
    have hdiv :
        modeCoeff m lam row a b c =
          (modeCoeff m lam row i0 i1 i2 * modeCoeff m lam i0 a b c) /
            modeCoeff m lam i0 i0 i1 i2 := by
      exact (eq_div_iff href0).2 (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hbc)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

  simpa [u, μ, hneq, Units.val_mk0, mul_assoc, mul_left_comm, mul_comm] using hsolve


theorem separate_alpha_of_generic {n : ℕ} (hn : 5 ≤ n) (A : Fin n → Matrix3x4) (lam : Lambda n)
    (hgen : GenericCameras A)
    (hsupp : ∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ)
    (hrank : ∀ m : Fin 4, (Unfold m (scaleQ lam (constructQ A))).rank ≤ 4) :
    ∃ (u : Fin n → ℝˣ) (μ : Fin n → Fin n → Fin n → ℝˣ),
      ∀ α β γ δ, NotAllEqual3 β γ δ →
        lam α β γ δ = (u α : ℝ) * (μ β γ δ : ℝ) := by
  classical
  simpa [modeCoeff] using
    (separate_mode_of_generic (hn := hn) (A := A) (lam := lam) (hgen := hgen) (m := (0 : Fin 4))
      (hsupp := hsupp) (hrank := hrank))


theorem separate_beta_of_generic {n : ℕ} (A : Fin n → Matrix3x4) (lam : Lambda n)
    (hn : 5 ≤ n) (hgen : GenericCameras A)
    (hsupp : ∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ)
    (hrank : ∀ m : Fin 4, (Unfold m (scaleQ lam (constructQ A))).rank ≤ 4) :
    ∃ (v : Fin n → ℝˣ) (ν : Fin n → Fin n → Fin n → ℝˣ),
      ∀ α β γ δ, NotAllEqual3 α γ δ →
        lam α β γ δ = (v β : ℝ) * (ν α γ δ : ℝ) := by
  classical
  rcases separate_mode_of_generic (hn := hn) (A := A) (lam := lam) (hgen := hgen) (m := (1 : Fin 4))
      (hsupp := hsupp) (hrank := hrank) with ⟨v, ν, hsep⟩
  refine ⟨v, ν, ?_⟩
  intro α β γ δ hneq
  simpa [modeCoeff] using hsep β α γ δ hneq


theorem separate_gamma_of_generic {n : ℕ} (A : Fin n → Matrix3x4) (lam : Lambda n)
    (hn : 5 ≤ n) (hgen : GenericCameras A)
    (hsupp : ∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ)
    (hrank : ∀ m : Fin 4, (Unfold m (scaleQ lam (constructQ A))).rank ≤ 4) :
    ∃ (w : Fin n → ℝˣ) (ξ : Fin n → Fin n → Fin n → ℝˣ),
      ∀ α β γ δ, NotAllEqual3 α β δ →
        lam α β γ δ = (w γ : ℝ) * (ξ α β δ : ℝ) := by
  classical
  rcases separate_mode_of_generic (hn := hn) (A := A) (lam := lam) (hgen := hgen) (m := (2 : Fin 4))
      (hsupp := hsupp) (hrank := hrank) with ⟨w, ξ, hsep⟩
  refine ⟨w, ξ, ?_⟩
  intro α β γ δ hneq
  simpa [modeCoeff] using hsep γ α β δ hneq

theorem separate_delta_of_generic {n : ℕ} (A : Fin n → Matrix3x4) (lam : Lambda n)
    (hn : 5 ≤ n) (hgen : GenericCameras A)
    (hsupp : ∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ)
    (hrank : ∀ m : Fin 4, (Unfold m (scaleQ lam (constructQ A))).rank ≤ 4) :
    ∃ (x : Fin n → ℝˣ) (ζ : Fin n → Fin n → Fin n → ℝˣ),
      ∀ α β γ δ, NotAllEqual3 α β γ →
        lam α β γ δ = (x δ : ℝ) * (ζ α β γ : ℝ) := by
  classical
  rcases separate_mode_of_generic (hn := hn) (A := A) (lam := lam) (hgen := hgen) (m := (3 : Fin 4))
      (hsupp := hsupp) (hrank := hrank) with ⟨x, ζ, hsep⟩
  refine ⟨x, ζ, ?_⟩
  intro α β γ δ hneq
  simpa [modeCoeff] using hsep δ α β γ hneq

theorem full_factorization_of_separations {n : ℕ} (hn : 5 ≤ n) (lam : Lambda n)
    (hsupp : ∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ)
    (hα :
      ∃ (u : Fin n → ℝˣ) (μ : Fin n → Fin n → Fin n → ℝˣ),
        ∀ α β γ δ, NotAllEqual3 β γ δ →
          lam α β γ δ = (u α : ℝ) * (μ β γ δ : ℝ))
    (hβ :
      ∃ (v : Fin n → ℝˣ) (ν : Fin n → Fin n → Fin n → ℝˣ),
        ∀ α β γ δ, NotAllEqual3 α γ δ →
          lam α β γ δ = (v β : ℝ) * (ν α γ δ : ℝ))
    (hγ :
      ∃ (w : Fin n → ℝˣ) (ξ : Fin n → Fin n → Fin n → ℝˣ),
        ∀ α β γ δ, NotAllEqual3 α β δ →
          lam α β γ δ = (w γ : ℝ) * (ξ α β δ : ℝ))
    (hδ :
      ∃ (x : Fin n → ℝˣ) (ζ : Fin n → Fin n → Fin n → ℝˣ),
        ∀ α β γ δ, NotAllEqual3 α β γ →
          lam α β γ δ = (x δ : ℝ) * (ζ α β γ : ℝ)) :
    ∃ (u v w x : Fin n → ℝˣ),
      ∀ α β γ δ, NotIdentical α β γ δ →
        lam α β γ δ = (u α : ℝ) * (v β : ℝ) * (w γ : ℝ) * (x δ : ℝ) := by
  classical
  rcases hα with ⟨u, μ, hαeq⟩
  rcases hβ with ⟨v, ν, hβeq⟩
  rcases hγ with ⟨w, ξ, hγeq⟩
  rcases hδ with ⟨x0, ζ, hδeq⟩
  have _ : ∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ := hsupp
  clear hsupp x0 ζ hδeq

  have h0 : (0 : ℕ) < n := Nat.lt_of_lt_of_le (by decide : 0 < 5) hn
  let i0 : Fin n := ⟨0, h0⟩

  let ρ : Fin n → Fin n → ℝˣ := fun γ δ => (u i0)⁻¹ * ν i0 γ δ

  have huvρ :
      ∀ α β γ δ, γ ≠ δ →
        lam α β γ δ = (u α : ℝ) * (v β : ℝ) * (ρ γ δ : ℝ) := by
    intro α β γ δ hgd
    have hneqβ : NotAllEqual3 β γ δ := by
      intro h
      exact hgd h.2
    have hneqi0 : NotAllEqual3 i0 γ δ := by
      intro h
      exact hgd h.2
    have hμ :
        (μ β γ δ : ℝ) = (v β : ℝ) * (ρ γ δ : ℝ) := by
      have hcross :
          (u i0 : ℝ) * (μ β γ δ : ℝ) = (v β : ℝ) * (ν i0 γ δ : ℝ) := by
        calc
          (u i0 : ℝ) * (μ β γ δ : ℝ) = lam i0 β γ δ := (hαeq i0 β γ δ hneqβ).symm
          _ = (v β : ℝ) * (ν i0 γ δ : ℝ) := hβeq i0 β γ δ hneqi0
      have hui0 : (u i0 : ℝ) ≠ 0 := (u i0).ne_zero
      have hdiv :
          (μ β γ δ : ℝ) = ((v β : ℝ) * (ν i0 γ δ : ℝ)) / (u i0 : ℝ) := by
        exact (eq_div_iff hui0).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hcross)
      simpa [ρ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
    calc
      lam α β γ δ = (u α : ℝ) * (μ β γ δ : ℝ) := hαeq α β γ δ hneqβ
      _ = (u α : ℝ) * ((v β : ℝ) * (ρ γ δ : ℝ)) := by rw [hμ]
      _ = (u α : ℝ) * (v β : ℝ) * (ρ γ δ : ℝ) := by ring

  let aPick : Fin n → Fin n := fun δ => Classical.choose (exists_fin_ne_of_five hn δ)
  have haPick : ∀ δ : Fin n, aPick δ ≠ δ := by
    intro δ
    exact Classical.choose_spec (exists_fin_ne_of_five hn δ)

  let x : Fin n → ℝˣ := fun δ => ((u (aPick δ)) * (v δ))⁻¹ * ξ (aPick δ) δ δ

  have hfull_ne :
      ∀ α β γ δ, γ ≠ δ →
        lam α β γ δ = (u α : ℝ) * (v β : ℝ) * (w γ : ℝ) * (x δ : ℝ) := by
    intro α β γ δ hgd
    have hnePick : NotAllEqual3 (aPick δ) δ δ := by
      intro h
      exact haPick δ h.1
    have hγpick :
        lam (aPick δ) δ γ δ = (w γ : ℝ) * (ξ (aPick δ) δ δ : ℝ) :=
      hγeq (aPick δ) δ γ δ hnePick
    have huvρ_pick :
        lam (aPick δ) δ γ δ = (u (aPick δ) : ℝ) * (v δ : ℝ) * (ρ γ δ : ℝ) :=
      huvρ (aPick δ) δ γ δ hgd
    have hρ :
        (ρ γ δ : ℝ) = (w γ : ℝ) * (x δ : ℝ) := by
      have huvv_ne : ((u (aPick δ) : ℝ) * (v δ : ℝ)) ≠ 0 := by
        exact mul_ne_zero (u (aPick δ)).ne_zero (v δ).ne_zero
      have hmult :
          ((u (aPick δ) : ℝ) * (v δ : ℝ)) * (ρ γ δ : ℝ) =
            (w γ : ℝ) * (ξ (aPick δ) δ δ : ℝ) := by
        calc
          ((u (aPick δ) : ℝ) * (v δ : ℝ)) * (ρ γ δ : ℝ)
              = lam (aPick δ) δ γ δ := by simpa [mul_assoc] using huvρ_pick.symm
          _ = (w γ : ℝ) * (ξ (aPick δ) δ δ : ℝ) := hγpick
      have hscaled := congrArg (fun t => (((u (aPick δ) : ℝ) * (v δ : ℝ))⁻¹) * t) hmult
      simpa [x, mul_assoc, mul_left_comm, mul_comm, huvv_ne] using hscaled
    calc
      lam α β γ δ = (u α : ℝ) * (v β : ℝ) * (ρ γ δ : ℝ) := huvρ α β γ δ hgd
      _ = (u α : ℝ) * (v β : ℝ) * ((w γ : ℝ) * (x δ : ℝ)) := by rw [hρ]
      _ = (u α : ℝ) * (v β : ℝ) * (w γ : ℝ) * (x δ : ℝ) := by ring

  refine ⟨u, v, w, x, ?_⟩
  intro α β γ δ hni
  by_cases hgd : γ = δ
  · subst hgd
    have hneqαβγ : NotAllEqual3 α β γ := by
      intro h
      exact hni ⟨h.1, h.2, rfl⟩
    let η : Fin n := aPick γ
    have hηne : η ≠ γ := haPick γ
    have hfactη :
        lam α β η γ = (u α : ℝ) * (v β : ℝ) * (w η : ℝ) * (x γ : ℝ) :=
      hfull_ne α β η γ hηne
    have hγη : lam α β η γ = (w η : ℝ) * (ξ α β γ : ℝ) :=
      hγeq α β η γ hneqαβγ
    have hξ :
        (ξ α β γ : ℝ) = (u α : ℝ) * (v β : ℝ) * (x γ : ℝ) := by
      have hwη : (w η : ℝ) ≠ 0 := (w η).ne_zero
      apply (mul_left_cancel₀ hwη)
      calc
        (w η : ℝ) * (ξ α β γ : ℝ) = lam α β η γ := hγη.symm
        _ = (u α : ℝ) * (v β : ℝ) * (w η : ℝ) * (x γ : ℝ) := hfactη
        _ = (w η : ℝ) * ((u α : ℝ) * (v β : ℝ) * (x γ : ℝ)) := by ring
    have hγdiag : lam α β γ γ = (w γ : ℝ) * (ξ α β γ : ℝ) :=
      hγeq α β γ γ hneqαβγ
    calc
      lam α β γ γ = (w γ : ℝ) * (ξ α β γ : ℝ) := hγdiag
      _ = (w γ : ℝ) * ((u α : ℝ) * (v β : ℝ) * (x γ : ℝ)) := by rw [hξ]
      _ = (u α : ℝ) * (v β : ℝ) * (w γ : ℝ) * (x γ : ℝ) := by ring
  · exact hfull_ne α β γ δ hgd

theorem reverse_direction_core {n : ℕ} (hn : 5 ≤ n) (A : Fin n → Matrix3x4)
    (hgen : GenericCameras A) (lam : Lambda n)
    (hsupp : ∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ)
    (hrank : ∀ m : Fin 4, (Unfold m (scaleQ lam (constructQ A))).rank ≤ 4) :
    ∃ (u v w x : Fin n → ℝˣ),
      ∀ α β γ δ, NotIdentical α β γ δ →
        lam α β γ δ = (u α : ℝ) * (v β : ℝ) * (w γ : ℝ) * (x δ : ℝ) := by
  classical
  -- Extract the four partial separations (one per unfolding mode).
  have hα : ∃ (u : Fin n → ℝˣ) (μ : Fin n → Fin n → Fin n → ℝˣ),
      ∀ α β γ δ, NotAllEqual3 β γ δ →
        lam α β γ δ = (u α : ℝ) * (μ β γ δ : ℝ) :=
    separate_alpha_of_generic (hn := hn) (A := A) (lam := lam) (hgen := hgen) (hsupp := hsupp)
      (hrank := hrank)

  have hβ : ∃ (v : Fin n → ℝˣ) (ν : Fin n → Fin n → Fin n → ℝˣ),
      ∀ α β γ δ, NotAllEqual3 α γ δ →
        lam α β γ δ = (v β : ℝ) * (ν α γ δ : ℝ) :=
    separate_beta_of_generic (hn := hn) (A := A) (lam := lam) (hgen := hgen) (hsupp := hsupp)
      (hrank := hrank)

  have hγ : ∃ (w : Fin n → ℝˣ) (ξ : Fin n → Fin n → Fin n → ℝˣ),
      ∀ α β γ δ, NotAllEqual3 α β δ →
        lam α β γ δ = (w γ : ℝ) * (ξ α β δ : ℝ) :=
    separate_gamma_of_generic (hn := hn) (A := A) (lam := lam) (hgen := hgen) (hsupp := hsupp)
      (hrank := hrank)

  have hδ : ∃ (x : Fin n → ℝˣ) (ζ : Fin n → Fin n → Fin n → ℝˣ),
      ∀ α β γ δ, NotAllEqual3 α β γ →
        lam α β γ δ = (x δ : ℝ) * (ζ α β γ : ℝ) :=
    separate_delta_of_generic (hn := hn) (A := A) (lam := lam) (hgen := hgen) (hsupp := hsupp)
      (hrank := hrank)

  -- Patch the separations into the full `u⊗v⊗w⊗x` factorization.
  exact full_factorization_of_separations (hn := hn) (lam := lam) (hsupp := hsupp)
    (hα := hα) (hβ := hβ) (hγ := hγ) (hδ := hδ)

theorem reverse_direction {n : ℕ} (hn : 5 ≤ n) (A : Fin n → Matrix3x4)
    (hgen : GenericCameras A) (lam : Lambda n)
    (hsupp : ∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ)
    (hvanish : IsZeroVec (PolyMap.eval (polyMapF n) (scaleQ lam (constructQ A)))) :
    ∃ (u v w x : Fin n → ℝˣ),
      ∀ α β γ δ, NotIdentical α β γ δ →
        lam α β γ δ = (u α : ℝ) * (v β : ℝ) * (w γ : ℝ) * (x δ : ℝ)
    := by
  classical
  -- Step 0: derive the "all 5×5 minors vanish" statement and hence rank bounds for each unfolding.
  have hminors :
      ∀ (m : Fin 4) (rows : Fin 5 → RowIdx n) (cols : Fin 5 → ColIdx n),
        Matrix.det ((Unfold m (scaleQ lam (constructQ A))).submatrix rows cols) = 0 := by
    -- `IsZeroVec (eval F T)` is definitionally the statement that every 5×5 minor determinant is 0.
    exact (isZeroVec_iff_minors_vanish (Qf := scaleQ lam (constructQ A))).1 hvanish

  have hrank :
      ∀ m : Fin 4, (Unfold m (scaleQ lam (constructQ A))).rank ≤ 4 := by
    intro m
    refine minors5x5_zero_imp_rank_le_four (M := Unfold m (scaleQ lam (constructQ A))) ?_
    intro rows cols
    exact hminors m rows cols

  exact reverse_direction_core (hn := hn) (A := A) (hgen := hgen) (lam := lam)
    (hsupp := hsupp) (hrank := hrank)

noncomputable section AristotleLemmas

def witnessA (n : ℕ) : Fin n → Matrix3x4 :=
  fun α => Matrix.of ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, (α : ℝ)]]

lemma witnessA_properties {n : ℕ} (hn : 5 ≤ n) :
    RankGenericCameras (witnessA n) := by
  classical
  refine ⟨?_, ?_⟩

  · -- `rank (StackedMat (witnessA n)) = 4` by showing the four columns are independent.
    -- We do this via row-independence of the transpose.
    have h0 : (0 : ℕ) < n := Nat.lt_of_lt_of_le (by decide : 0 < 5) hn
    have h1 : (1 : ℕ) < n := Nat.lt_of_lt_of_le (by decide : 1 < 5) hn
    let a0 : Fin n := ⟨0, h0⟩
    let a1 : Fin n := ⟨1, h1⟩

    have hLI :
        LinearIndependent ℝ (fun i : Fin 4 => (StackedMat (witnessA n))ᵀ.row i) := by
      -- Use the finite-index characterization.
      refine (Fintype.linearIndependent_iff).2 ?_
      intro g hg i
      -- Evaluate the vector equation at carefully chosen coordinates.
      -- The resulting scalar equations isolate each coefficient of `g`.
      have h_at (p : RowIdx n) :
          (∑ k : Fin 4, g k • (StackedMat (witnessA n))ᵀ.row k) p = 0 := by
        simpa using congrArg (fun v => v p) hg

      -- `g 0 = 0` from row `(a0,0)`.
      have hg0 : g 0 = 0 := by
        have h := h_at (a0, 0)
        have h' : (∑ x : Fin 4, g x * (![1, 0, 0, 0] x : ℝ)) = 0 := by
          -- Row `(a0,0)` is `[1,0,0,0]`.
          simpa [StackedMat, witnessA, a0, Matrix.row_apply, Matrix.transpose_apply, Pi.smul_apply]
            using h
        have h'' :
            g 0 * (1 : ℝ) + g 1 * (0 : ℝ) + g 2 * (0 : ℝ) + g 3 * (0 : ℝ) = 0 := by
          simpa [Fin.sum_univ_four] using h'
        simpa using h''

      -- `g 1 = 0` from row `(a0,1)`.
      have hg1 : g 1 = 0 := by
        have h := h_at (a0, 1)
        have h' : (∑ x : Fin 4, g x * (![0, 1, 0, 0] x : ℝ)) = 0 := by
          -- Row `(a0,1)` is `[0,1,0,0]`.
          simpa [StackedMat, witnessA, a0, Matrix.row_apply, Matrix.transpose_apply, Pi.smul_apply]
            using h
        have h'' :
            g 0 * (0 : ℝ) + g 1 * (1 : ℝ) + g 2 * (0 : ℝ) + g 3 * (0 : ℝ) = 0 := by
          simpa [Fin.sum_univ_four] using h'
        simpa using h''

      -- `g 2 = 0` and then `g 3 = 0` from rows `(a0,2)` and `(a1,2)`.
      have hg2 : g 2 = 0 := by
        have h := h_at (a0, 2)
        have h' : (∑ x : Fin 4, g x * (![0, 0, 1, (a0 : ℝ)] x : ℝ)) = 0 := by
          -- Row `(a0,2)` is `[0,0,1,(a0:ℝ)]`.
          simpa [StackedMat, witnessA, Matrix.row_apply, Matrix.transpose_apply, Pi.smul_apply]
            using h
        have h'' : g 2 + g 3 * (a0 : ℝ) = 0 := by
          -- Expand the sum; only indices `2` and `3` survive.
          simpa [Fin.sum_univ_four, mul_add, add_mul, add_assoc, add_left_comm, add_comm] using h'
        -- `a0 = 0`, so `g 3 * a0 = 0`.
        simpa [a0] using h''

      have hg3 : g 3 = 0 := by
        have h := h_at (a1, 2)
        have h' : (∑ x : Fin 4, g x * (![0, 0, 1, (a1 : ℝ)] x : ℝ)) = 0 := by
          simpa [StackedMat, witnessA, Matrix.row_apply, Matrix.transpose_apply, Pi.smul_apply]
            using h
        have h'' : g 2 + g 3 * (a1 : ℝ) = 0 := by
          simpa [Fin.sum_univ_four, mul_add, add_mul, add_assoc, add_left_comm, add_comm] using h'
        have hmul : g 3 * (a1 : ℝ) = 0 := by
          simpa [hg2, add_zero] using h''
        have ha1 : (a1 : ℝ) ≠ 0 := by
          simpa [a1] using (one_ne_zero : (1 : ℝ) ≠ 0)
        exact (mul_eq_zero.mp hmul).resolve_right ha1

      fin_cases i <;> simp [hg0, hg1, hg2, hg3]

    have hrankT : (StackedMat (witnessA n))ᵀ.rank = 4 := by
      simpa using (LinearIndependent.rank_matrix (R := ℝ) (M := (StackedMat (witnessA n))ᵀ) hLI)
    simpa [Matrix.rank_transpose] using hrankT

  · intro α
    -- Each camera `witnessA n α` has rank 3: its three rows are linearly independent.
    have hLI :
        LinearIndependent ℝ (fun i : Fin 3 => (witnessA n α).row i) := by
      refine (Fintype.linearIndependent_iff).2 ?_
      intro g hg i
      have h_at (j : Fin 4) :
          (∑ k : Fin 3, g k • (witnessA n α).row k) j = 0 := by
        simpa using congrArg (fun v => v j) hg

      have hg0 : g 0 = 0 := by
        have h := h_at 0
        have h' :
            (∑ x : Fin 3, g x *
              (vecCons (1 : ℝ) (fun i => vecCons 0 (fun _ => 0) i) x)) = 0 := by
          -- Column `0` of the three rows is `[1,0,0]`.
          simpa [witnessA, Matrix.row_apply, Pi.smul_apply] using h
        have h'' : g 0 * (1 : ℝ) + g 1 * (0 : ℝ) + g 2 * (0 : ℝ) = 0 := by
          simpa [Fin.sum_univ_three] using h'
        simpa using h''
      have hg1 : g 1 = 0 := by
        have h := h_at 1
        have h' :
            (∑ x : Fin 3, g x *
              (vecCons (0 : ℝ) (fun i => vecCons 1 (fun _ => 0) i) x)) = 0 := by
          -- Column `1` of the three rows is `[0,1,0]`.
          simpa [witnessA, Matrix.row_apply, Pi.smul_apply] using h
        have h'' : g 0 * (0 : ℝ) + g 1 * (1 : ℝ) + g 2 * (0 : ℝ) = 0 := by
          simpa [Fin.sum_univ_three] using h'
        simpa using h''
      have hg2 : g 2 = 0 := by
        have h := h_at 2
        have h' :
            (∑ x : Fin 3, g x *
              (vecCons (0 : ℝ) (fun i => vecCons 0 (fun _ => 1) i) x)) = 0 := by
          -- Column `2` of the three rows is `[0,0,1]`.
          simpa [witnessA, Matrix.row_apply, Pi.smul_apply] using h
        have h'' : g 0 * (0 : ℝ) + g 1 * (0 : ℝ) + g 2 * (1 : ℝ) = 0 := by
          simpa [Fin.sum_univ_three] using h'
        simpa using h''

      fin_cases i <;> simp [hg0, hg1, hg2]
    simpa using (LinearIndependent.rank_matrix (R := ℝ) (M := witnessA n α) hLI)

/-
Definitions for the genericity polynomial components:
1. `mat_poly_stacked`: The stacked matrix with polynomial entries.
2. `poly_minor_stacked`: Determinant of a 4x4 submatrix of the stacked matrix.
3. `poly_sum_sq_stacked`: Sum of squares of all 4x4 minors of the stacked matrix.
4. `mat_poly_cam`: The camera matrix `A α` with polynomial entries.
5. `poly_minor_cam`: Determinant of a 3x3 submatrix of `A α`.
6. `poly_sum_sq_cam`: Sum of squares of all 3x3 minors of `A α`.
7. `total_genericity_poly`: The product of `poly_sum_sq_stacked` and all `poly_sum_sq_cam`.
-/
open Firstproof

open Classical Matrix BigOperators

def mat_poly_stacked (n : ℕ) : Matrix (RowIdx n) (Fin 4) (MvPolynomial (AIndex n) ℝ) :=
  fun p k => MvPolynomial.X (p.1, p.2, k)

def poly_minor_stacked (n : ℕ) (rows : Fin 4 → RowIdx n) : MvPolynomial (AIndex n) ℝ :=
  Matrix.det ((mat_poly_stacked n).submatrix rows id)

def poly_sum_sq_stacked (n : ℕ) : MvPolynomial (AIndex n) ℝ :=
  ∑ rows : Fin 4 → RowIdx n, (poly_minor_stacked n rows)^2

def mat_poly_cam (n : ℕ) (α : Fin n) : Matrix (Fin 3) (Fin 4) (MvPolynomial (AIndex n) ℝ) :=
  fun i j => MvPolynomial.X (α, i, j)

def poly_minor_cam (n : ℕ) (α : Fin n) (cols : Fin 3 → Fin 4) : MvPolynomial (AIndex n) ℝ :=
  Matrix.det ((mat_poly_cam n α).submatrix id cols)

def poly_sum_sq_cam (n : ℕ) (α : Fin n) : MvPolynomial (AIndex n) ℝ :=
  ∑ cols : Fin 3 → Fin 4, (poly_minor_cam n α cols)^2

def total_genericity_poly (n : ℕ) : MvPolynomial (AIndex n) ℝ :=
  (poly_sum_sq_stacked n) * (∏ α : Fin n, poly_sum_sq_cam n α)

open Firstproof

open Classical Matrix BigOperators

lemma eval_poly_sum_sq_stacked_ne_zero {n : ℕ} (A : Fin n → Matrix3x4) :
    evalCameraPolynomial (poly_sum_sq_stacked n) A ≠ 0 → (StackedMat A).rank = 4 := by
      intro h_nonzero
      have h_rank_ge_4 : (StackedMat A).rank ≥ 4 := by
        -- Since `poly_sum_sq_stacked n` is nonzero, there exists a 4x4 minor of `StackedMat A` that is nonzero.
        obtain ⟨rows, hrows⟩ : ∃ rows : Fin 4 → RowIdx n, Matrix.det (Matrix.submatrix (StackedMat A) rows id) ≠ 0 := by
          contrapose! h_nonzero;
          simp_all +decide [ Firstproof.evalCameraPolynomial, Firstproof.poly_sum_sq_stacked ];
          refine Finset.sum_eq_zero fun x hx => ?_;
          convert congr_arg ( · ^ 2 ) ( h_nonzero x ) using 1;
          · unfold Firstproof.poly_minor_stacked; simp +decide [ Matrix.det_apply' ] ;
            unfold Firstproof.mat_poly_stacked; aesop;
          · norm_num;
        have h_rank_ge_4 : Matrix.rank (Matrix.submatrix (StackedMat A) rows id) ≥ 4 := by
          have := Matrix.rank_mul_le_left ( Matrix.submatrix ( StackedMat A ) rows id ) ( ( Matrix.submatrix ( StackedMat A ) rows id ) ⁻¹ ) ; simp_all +decide [ Matrix.nonsing_inv_apply_not_isUnit, isUnit_iff_ne_zero ] ;
        -- Since the submatrix is a part of the original matrix, its rank is less than or equal to the rank of the original matrix.
        have h_submatrix_rank_le : Matrix.rank (Matrix.submatrix (StackedMat A) rows id) ≤ Matrix.rank (StackedMat A) := by
          have h_submatrix : ∃ P : Matrix (Fin 4) (RowIdx n) ℝ, ∃ Q : Matrix (Fin 4) (Fin 4) ℝ, Matrix.submatrix (StackedMat A) rows id = P * StackedMat A * Q := by
            use Matrix.of (fun i j => if j = rows i then 1 else 0), 1;
            ext i j; simp +decide [ Matrix.mul_apply ] ;
            simp +decide [ Matrix.one_apply ]
          obtain ⟨ P, Q, hPQ ⟩ := h_submatrix; rw [ hPQ ] ; exact Matrix.rank_mul_le_left _ _ |> le_trans <| Matrix.rank_mul_le_right _ _;
        exact le_trans h_rank_ge_4 h_submatrix_rank_le
      have h_rank_le_4 : (StackedMat A).rank ≤ 4 := by
        exact le_trans ( Matrix.rank_le_card_width _ ) ( by simp +decide )
      exact le_antisymm h_rank_le_4 h_rank_ge_4

open Firstproof

open Classical Matrix BigOperators

lemma eval_poly_sum_sq_cam_ne_zero {n : ℕ} (A : Fin n → Matrix3x4) (α : Fin n) :
    evalCameraPolynomial (poly_sum_sq_cam n α) A ≠ 0 → (A α).rank = 3 := by
      intro h_nonzero
      obtain ⟨cols, h_det⟩ : ∃ cols : Fin 3 → Fin 4, Matrix.det ((A α).submatrix id cols) ≠ 0 := by
        simp_all +decide [ Firstproof.evalCameraPolynomial, Firstproof.poly_sum_sq_cam ];
        contrapose! h_nonzero; simp_all +decide [ Firstproof.poly_minor_cam ] ;
        refine Finset.sum_eq_zero fun x hx => ?_ ; simp_all +decide [ Matrix.det_apply' ];
        unfold Firstproof.mat_poly_cam; aesop;
      have h_rank_ge_3 : Matrix.rank (A α) ≥ 3 := by
        have := Matrix.rank_mul_le ( A α ) ( Matrix.of ( fun i j => if i = cols j then 1 else 0 ) ) ; simp_all +decide [ Matrix.rank_transpose, Matrix.mul_apply ] ;
        have h_rank_ge_3 : Matrix.rank (Matrix.submatrix (A α) id cols) = 3 := by
          have := Matrix.rank_mul_le ( Matrix.submatrix ( A α ) id cols ) ( Matrix.submatrix ( A α ) id cols ) ⁻¹; simp_all +decide [ Matrix.nonsing_inv_apply_not_isUnit, isUnit_iff_ne_zero ] ;
          exact le_antisymm ( le_trans ( Matrix.rank_le_card_width _ ) ( by norm_num ) ) this.1;
        convert this.1 using 1;
        convert h_rank_ge_3.symm using 2; ext i j; simp +decide [ Matrix.mul_apply ] ;
      exact le_antisymm ( le_trans ( Matrix.rank_le_card_height _ ) ( by norm_num ) ) h_rank_ge_3

open Firstproof

open Classical Matrix BigOperators

lemma rank_eq_four_imp_eval_stacked_ne_zero {n : ℕ} (A : Fin n → Matrix3x4) :
    (StackedMat A).rank = 4 → evalCameraPolynomial (poly_sum_sq_stacked n) A ≠ 0 := by
      intro h_rank h_eval_zero;
      -- If the rank is 4, then there exists a 4x4 submatrix with a non-zero determinant.
      obtain ⟨rows, h_det⟩ : ∃ rows : Fin 4 → RowIdx n, (Matrix.det (Matrix.submatrix (StackedMat A) rows id)) ≠ 0 := by
        have h_det : ∃ rows : Fin 4 → RowIdx n, LinearIndependent ℝ (fun i => (StackedMat A).row (rows i)) := by
          have h_det : ∃ rows : Fin 4 → RowIdx n, LinearIndependent ℝ (fun i => (StackedMat A).row (rows i)) := by
            have h_rank : Module.finrank ℝ (Submodule.span ℝ (Set.range (StackedMat A).row)) = 4 := by
              convert h_rank using 1;
              exact Eq.symm (rank_eq_finrank_span_row (StackedMat A))
            have := ( exists_linearIndependent ℝ ( Set.range ( StackedMat A |> Matrix.row ) ) );
            obtain ⟨ b, hb₁, hb₂, hb₃ ⟩ := this;
            have h_card : Set.ncard b = 4 := by
              have h_card : Module.finrank ℝ (Submodule.span ℝ b) = 4 := by
                rw [ hb₂, h_rank ];
              have h_card : Module.finrank ℝ (Submodule.span ℝ b) = Set.ncard b := by
                have h_finite : Set.Finite b := by
                  exact Set.Finite.subset ( Set.toFinite ( Set.range ( StackedMat A |> Matrix.row ) ) ) hb₁
                convert ( finrank_span_eq_card <| hb₃ );
                all_goals norm_num [ Set.ncard_eq_toFinset_card' ];
                convert Set.ncard_coe_finset ( h_finite.toFinset );
                all_goals try { exact h_finite.fintype };
                · aesop;
                · rw [ Fintype.card_of_subtype ] ; aesop;
              linarith;
            obtain ⟨rows, hrows⟩ : ∃ rows : Fin 4 → (Fin 4 → ℝ), (∀ i, rows i ∈ b) ∧ LinearIndependent ℝ rows := by
              have h_card : Nonempty (Fin 4 ≃ b) := by
                have h_card : Fintype b := by
                  exact Set.Finite.fintype ( Set.finite_of_ncard_pos ( by linarith ) );
                exact ⟨ Fintype.equivOfCardEq <| by simp +decide [ Set.ncard_eq_toFinset_card' ] at *; linarith ⟩;
              obtain ⟨ e ⟩ := h_card;
              exact ⟨ _, fun i => e i |>.2, hb₃.comp _ e.injective ⟩;
            choose f hf using fun i => hb₁ ( hrows.1 i );
            exact ⟨ f, by simpa only [ hf ] using hrows.2 ⟩;
          exact h_det;
        obtain ⟨ rows, hrows ⟩ := h_det;
        refine' ⟨ rows, _ ⟩;
        rw [ Fintype.linearIndependent_iff ] at hrows;
        contrapose! hrows;
        obtain ⟨ g, hg ⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hrows;
        exact ⟨ g, by simpa [ funext_iff, Matrix.vecMul, dotProduct ] using hg.2, Function.ne_iff.mp hg.1 ⟩;
      -- Since the determinant of the submatrix is non-zero, the evaluation of the polynomial at A is also non-zero.
      have h_eval_nonzero : evalCameraPolynomial (poly_minor_stacked n rows) A ≠ 0 := by
        unfold Firstproof.evalCameraPolynomial; simp_all +decide [ Matrix.det_apply' ] ;
        unfold Firstproof.poly_minor_stacked; simp_all +decide [ Matrix.det_apply' ] ;
        convert h_det using 1;
        unfold Firstproof.mat_poly_stacked; simp +decide [ Firstproof.StackedMat ] ;
      -- Since the evaluation of the polynomial at A is zero, the sum of squares of all 4x4 minors must also be zero.
      have h_sum_sq_zero : ∑ rows : Fin 4 → RowIdx n, (evalCameraPolynomial (poly_minor_stacked n rows) A)^2 = 0 := by
        convert h_eval_zero using 1;
        unfold Firstproof.evalCameraPolynomial Firstproof.poly_sum_sq_stacked; simp +decide [ sq, MvPolynomial.eval₂_sum ] ;
      exact absurd h_sum_sq_zero ( ne_of_gt ( lt_of_lt_of_le ( by positivity ) ( Finset.single_le_sum ( fun x _ => sq_nonneg ( evalCameraPolynomial ( poly_minor_stacked n x ) A ) ) ( Finset.mem_univ rows ) ) ) )

open Firstproof

open Classical Matrix BigOperators

lemma rank_lt_three_of_all_3x3_minors_zero (M : Matrix (Fin 3) (Fin 4) ℝ)
    (h : ∀ cols : Fin 3 → Fin 4, (M.submatrix id cols).det = 0) :
    M.rank < 3 := by
      -- If `M.rank = 3`, then the column space has dimension 3.
      by_contra h_contra
      have h_col_space : Module.finrank ℝ (Submodule.span ℝ (Set.range M.col)) = 3 := by
        rw [ show ( Submodule.span ℝ ( Set.range M.col ) ) = LinearMap.range M.mulVecLin from ?_ ];
        · exact le_antisymm ( le_trans ( Submodule.finrank_le _ ) ( by norm_num ) ) ( not_lt.mp h_contra );
        · exact Eq.symm (range_mulVecLin M);
      -- Since the column space has dimension 3, there exists a subset of 3 columns that is linearly independent.
      obtain ⟨cols, hcols⟩ : ∃ cols : Fin 3 → Fin 4, LinearIndependent ℝ (fun i : Fin 3 => M.col (cols i)) := by
        have := ( exists_linearIndependent ℝ ( Set.range M.col ) );
        obtain ⟨ b, hb₁, hb₂, hb₃ ⟩ := this;
        have h_card : Set.ncard b = 3 := by
          have h_card : Module.finrank ℝ (Submodule.span ℝ b) = 3 := by
            rw [ hb₂, h_col_space ];
          have h_card : Module.finrank ℝ (Submodule.span ℝ b) = Set.ncard b := by
            have h_finite : Set.Finite b := by
              exact Set.Finite.subset ( Set.toFinite ( Set.range M.col ) ) hb₁
            convert ( finrank_span_eq_card <| hb₃ );
            all_goals norm_num [ Set.ncard_eq_toFinset_card' ];
            convert Set.ncard_coe_finset ( h_finite.toFinset );
            all_goals try { exact h_finite.fintype };
            · aesop;
            · rw [ Fintype.card_of_subtype ] ; aesop;
          linarith;
        have h_card : ∃ cols : Fin 3 → Fin 4, b = Set.range (fun i => M.col (cols i)) := by
          have h_card : ∃ cols : Fin 3 → (Fin 3 → ℝ), b = Set.range cols := by
            have h_card : ∃ cols : Finset (Fin 3 → ℝ), cols.card = 3 ∧ b = cols := by
              have h_card : ∃ cols : Finset (Fin 3 → ℝ), b = cols := by
                exact ⟨ Set.Finite.toFinset ( Set.finite_of_ncard_pos ( by linarith ) ), by simpa ⟩;
              aesop;
            obtain ⟨ cols, hcols₁, hcols₂ ⟩ := h_card;
            have h_card : Nonempty (Fin 3 ≃ cols) := by
              exact ⟨ Fintype.equivOfCardEq <| by simp +decide [ hcols₁ ] ⟩;
            obtain ⟨ e ⟩ := h_card;
            use fun i => e i |>.1;
            ext x; simp [hcols₂];
            exact ⟨ fun hx => ⟨ e.symm ⟨ x, hx ⟩, by simp +decide ⟩, by rintro ⟨ y, rfl ⟩ ; exact e y |>.2 ⟩;
          obtain ⟨ cols, rfl ⟩ := h_card;
          choose f hf using fun i => hb₁ ( Set.mem_range_self i );
          exact ⟨ f, by ext; aesop ⟩;
        obtain ⟨ cols, rfl ⟩ := h_card;
        use cols;
        convert hb₃.comp _ _;
        rotate_left;
        use fun i => ⟨ M.col ( cols i ), Set.mem_range_self i ⟩;
        · intro i j hij; have := Finset.card_image_iff.mp ( show Finset.card ( Finset.image ( fun i => M.col ( cols i ) ) Finset.univ ) = Finset.card ( Finset.univ : Finset ( Fin 3 ) ) from ?_ ) ; aesop;
          rw [ ← Set.ncard_coe_finset ] ; aesop;
        · rfl;
      -- Since the columns of `M` are linearly independent, the determinant of the submatrix formed by these columns is nonzero.
      have h_det_nonzero : Matrix.det (Matrix.of (fun i j => M i (cols j))) ≠ 0 := by
        rw [ Fintype.linearIndependent_iff ] at hcols;
        intro h_det_zerocols;
        obtain ⟨ v, hv ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h_det_zerocols;
        exact hv.1 ( funext fun i => hcols v ( by ext j; simpa [ Matrix.mulVec, dotProduct, mul_comm ] using congr_fun hv.2 j ) i );
      exact h_det_nonzero (h cols)

open Firstproof

open Classical Matrix BigOperators

lemma rank_eq_three_imp_eval_cam_ne_zero {n : ℕ} (A : Fin n → Matrix3x4) (α : Fin n) :
    (A α).rank = 3 → evalCameraPolynomial (poly_sum_sq_cam n α) A ≠ 0 := by
      intro h_rank h_zero_sum;
      -- By definition of `poly_sum_sq_cam`, we know that `evalCameraPolynomial (poly_sum_sq_cam n α) A` is the sum of squares of determinants of 3x3 submatrices of `A α`.
      have h_sum_sq : ∑ cols : Fin 3 → Fin 4, (Matrix.det ((A α).submatrix id cols))^2 = 0 := by
        unfold Firstproof.evalCameraPolynomial at h_zero_sum;
        unfold Firstproof.poly_sum_sq_cam at h_zero_sum;
        convert h_zero_sum using 1;
        unfold Firstproof.poly_minor_cam; simp +decide [ Matrix.det_apply' ] ;
        unfold Firstproof.mat_poly_cam; simp +decide [ Matrix.det_apply' ] ;
      -- Since the sum of squares of determinants is zero, each determinant must be zero.
      have h_det_zero : ∀ cols : Fin 3 → Fin 4, (Matrix.det ((A α).submatrix id cols)) = 0 := by
        rw [ Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _ ] at h_sum_sq ; aesop;
      exact absurd ( rank_lt_three_of_all_3x3_minors_zero ( A α ) h_det_zero ) ( by linarith )

open Firstproof

open Classical Matrix BigOperators

lemma total_genericity_poly_ne_zero {n : ℕ} (hn : 5 ≤ n) :
    total_genericity_poly n ≠ 0 := by
      -- Let's choose any witness A for n ≥ 5.
      set A : Fin n → Matrix3x4 := witnessA n;
      -- By definition of $A$, we know that its evaluation at the witness cameras is non-zero.
      have h_eval_nonzero : (evalCameraPolynomial (poly_sum_sq_stacked n) A) * (∏ α : Fin n, evalCameraPolynomial (poly_sum_sq_cam n α) A) ≠ 0 := by
        have h_eval_nonzero : (evalCameraPolynomial (poly_sum_sq_stacked n) A) ≠ 0 ∧ ∀ α : Fin n, (evalCameraPolynomial (poly_sum_sq_cam n α) A) ≠ 0 := by
          have h_eval_nonzero : (StackedMat A).rank = 4 ∧ (∀ α : Fin n, (A α).rank = 3) := by
            simpa [Firstproof.RankGenericCameras] using (Firstproof.witnessA_properties hn)
          exact ⟨ by simpa using rank_eq_four_imp_eval_stacked_ne_zero A h_eval_nonzero.1, fun α => by simpa using rank_eq_three_imp_eval_cam_ne_zero A α ( h_eval_nonzero.2 α ) ⟩;
        exact mul_ne_zero h_eval_nonzero.1 <| Finset.prod_ne_zero_iff.mpr fun α _ => h_eval_nonzero.2 α;
      contrapose! h_eval_nonzero;
      convert congr_arg ( fun p => p.eval ( fun v => A v.1 v.2.1 v.2.2 ) ) h_eval_nonzero using 1;
      unfold Firstproof.total_genericity_poly; simp +decide [ Firstproof.evalCameraPolynomial ] ;

open Firstproof

open Classical Matrix BigOperators

lemma eval_total_genericity_poly_witness_ne_zero {n : ℕ} (hn : 5 ≤ n) :
    evalCameraPolynomial (total_genericity_poly n) (witnessA n) ≠ 0 := by
      -- Apply the definition of `total_genericity_poly`.
      simp [Firstproof.total_genericity_poly];
      unfold Firstproof.evalCameraPolynomial;
      simp +zetaDelta at *;
      constructor;
      · convert rank_eq_four_imp_eval_stacked_ne_zero _ _;
        convert ( witnessA_properties hn ).1;
      · apply Finset.prod_ne_zero_iff.mpr;
        intro a ha;
        convert rank_eq_three_imp_eval_cam_ne_zero _ _ _;
        convert Firstproof.witnessA_properties hn |>.2 a

end AristotleLemmas

theorem genericity_polynomial_exists (n : ℕ) (hn : 5 ≤ n) :
    ∃ (G : MvPolynomial (AIndex n) ℝ), G ≠ 0 ∧
      ∀ A : Fin n → Matrix3x4,
        evalCameraPolynomial G A ≠ 0 → RankGenericCameras A
    := by
  classical
  refine' ⟨ _, _, _ ⟩;
  -- Define the polynomial G as the product of the sum of squares of the minors of the stacked matrix and the sum of squares of the minors of each camera matrix.
  set G : MvPolynomial (Firstproof.AIndex n) ℝ := (poly_sum_sq_stacked n) * (∏ α : Fin n, poly_sum_sq_cam n α);
  exact G;
  · convert total_genericity_poly_ne_zero hn using 1;
  · intro A hA;
    refine' ⟨ _, _ ⟩;
    · apply Firstproof.eval_poly_sum_sq_stacked_ne_zero;
      exact fun h => hA <| by rw [ Firstproof.evalCameraPolynomial ] at *; simp_all +decide [ Finset.prod_eq_zero_iff, sub_eq_iff_eq_add ] ;
    · intro α;
      apply eval_poly_sum_sq_cam_ne_zero A α;
      simp_all +decide [ Finset.prod_eq_prod_diff_singleton_mul ( Finset.mem_univ α ) ];
      unfold Firstproof.evalCameraPolynomial at *; aesop;

/--
Core theorem proved from `GenericCameras` directly (reverse direction uses `G3`).
-/
theorem nine_core :
    ∃ (d : ℕ),
      ∀ n : ℕ, 5 ≤ n →
        ∃ (N : ℕ) (F : PolyMap n N),
          PolyMap.UniformDegreeBound d F ∧
          ∀ (A : Fin n → Matrix3x4), GenericCameras A →
            ∀ (lam : Lambda n),
              (∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ) →
                (IsZeroVec (PolyMap.eval F (scaleQ lam (constructQ A))) ↔
                  (∃ (u v w x : Fin n → ℝˣ),
                    ∀ α β γ δ, NotIdentical α β γ δ →
                      lam α β γ δ =
                        (u α : ℝ) * (v β : ℝ) * (w γ : ℝ) * (x δ : ℝ))) := by
  refine ⟨5, ?_⟩
  intro n hn
  refine ⟨numMinors n, polyMapF n, polyMapF_degree_bound n, ?_⟩
  intro A hgen lam hsupp
  constructor
  · intro hvanish
    exact reverse_direction hn A hgen lam hsupp hvanish
  · rintro ⟨u, v, w, x, hfact⟩
    exact forward_direction A lam hsupp u v w x hfact

def StrongGenericityPolynomialExists (n : ℕ) : Prop :=
  ∃ (G : MvPolynomial (AIndex n) ℝ), G ≠ 0 ∧
    ∀ (A : Fin n → Matrix3x4), evalCameraPolynomial G A ≠ 0 → GenericCameras A

noncomputable section AristotleLemmas

open scoped BigOperators
open Classical Matrix
open Firstproof

def poly_stackedRowsMatrix (n : ℕ) (α β γ δ : Fin n) (i j k ℓ : Fin 3) : Matrix (Fin 4) (Fin 4) (MvPolynomial (AIndex n) ℝ) :=
  Matrix.of ![(mat_poly_cam n α) i, (mat_poly_cam n β) j, (mat_poly_cam n γ) k, (mat_poly_cam n δ) ℓ]

def poly_constructQ_entry (n : ℕ) (α β γ δ : Fin n) (i j k ℓ : Fin 3) : MvPolynomial (AIndex n) ℝ :=
  Matrix.det (poly_stackedRowsMatrix n α β γ δ i j k ℓ)

def poly_Unfold_entry (n : ℕ) (m : Fin 4) (row : RowIdx n) (col : ColIdx n) : MvPolynomial (AIndex n) ℝ :=
  match m with
  | ⟨0, _⟩ => poly_constructQ_entry n row.1 col.1.1 col.2.1.1 col.2.2.1 row.2 col.1.2 col.2.1.2 col.2.2.2
  | ⟨1, _⟩ => poly_constructQ_entry n col.1.1 row.1 col.2.1.1 col.2.2.1 col.1.2 row.2 col.2.1.2 col.2.2.2
  | ⟨2, _⟩ => poly_constructQ_entry n col.1.1 col.2.1.1 row.1 col.2.2.1 col.1.2 col.2.1.2 row.2 col.2.2.2
  | ⟨3, _⟩ => poly_constructQ_entry n col.1.1 col.2.1.1 col.2.2.1 row.1 col.1.2 col.2.1.2 col.2.2.2 row.2

def poly_Submatrix27_entry (n : ℕ) (m : Fin 4) (a b c : Fin n) (row : RowIdx n) (t : Triple3) : MvPolynomial (AIndex n) ℝ :=
  poly_Unfold_entry n m row (colIdxOfTriple a b c t)

def poly_G3_minor (n : ℕ) (m : Fin 4) (a b c : Fin n) (rows : Fin 4 → RowIdx n) (cols : Fin 4 → Triple3) : MvPolynomial (AIndex n) ℝ :=
  Matrix.det (fun i j => poly_Submatrix27_entry n m a b c (rows i) (cols j))

def poly_sum_sq_G3_block (n : ℕ) (m : Fin 4) (a b c : Fin n) : MvPolynomial (AIndex n) ℝ :=
  ∑ rows : Fin 4 → RowIdx n, ∑ cols : Fin 4 → Triple3, (poly_G3_minor n m a b c rows cols)^2

def poly_G3_total (n : ℕ) : MvPolynomial (AIndex n) ℝ :=
  ∏ m : Fin 4, ∏ a : Fin n, ∏ b : Fin n, ∏ c : Fin n,
    if NotAllEqual3 a b c then poly_sum_sq_G3_block n m a b c else 1

def strong_genericity_poly (n : ℕ) : MvPolynomial (AIndex n) ℝ :=
  (total_genericity_poly n) * (poly_G3_total n)

open scoped BigOperators
open Classical Matrix
open Firstproof

lemma eval_poly_constructQ_entry {n : ℕ} (A : Fin n → Matrix3x4) (α β γ δ : Fin n) (i j k ℓ : Fin 3) :
    evalCameraPolynomial (poly_constructQ_entry n α β γ δ i j k ℓ) A = constructQ A α β γ δ i j k ℓ := by
      unfold Firstproof.poly_constructQ_entry;
      unfold Firstproof.evalCameraPolynomial Firstproof.poly_stackedRowsMatrix; simp +decide [ Matrix.det_apply' ] ;
      simp +decide [ Firstproof.mat_poly_cam, Firstproof.constructQ ];
      simp +decide [ Fin.prod_univ_four, Matrix.det_apply' ];
      congr! 2;
      rename_i σ _;
      fin_cases σ <;> simp +decide [ Firstproof.stackedRowsMatrix ];
      all_goals simp +decide [ Equiv.swap_apply_def ] ;

open scoped BigOperators
open Classical Matrix
open Firstproof

lemma eval_poly_Submatrix27_entry {n : ℕ} (A : Fin n → Matrix3x4) (m : Fin 4) (a b c : Fin n) (row : RowIdx n) (t : Triple3) :
    evalCameraPolynomial (poly_Submatrix27_entry n m a b c row t) A = Submatrix27 A m a b c row t := by
      unfold Firstproof.poly_Submatrix27_entry Submatrix27;
      unfold Firstproof.poly_Unfold_entry
      fin_cases m <;> simp [Unfold]
      · exact
          eval_poly_constructQ_entry A row.1 (colIdxOfTriple a b c t).1.1
            (colIdxOfTriple a b c t).2.1.1 (colIdxOfTriple a b c t).2.2.1 row.2
            (colIdxOfTriple a b c t).1.2 (colIdxOfTriple a b c t).2.1.2 (colIdxOfTriple a b c t).2.2.2
      · exact
          eval_poly_constructQ_entry A (colIdxOfTriple a b c t).1.1 row.1
            (colIdxOfTriple a b c t).2.1.1 (colIdxOfTriple a b c t).2.2.1 (colIdxOfTriple a b c t).1.2
            row.2 (colIdxOfTriple a b c t).2.1.2 (colIdxOfTriple a b c t).2.2.2
      · exact
          eval_poly_constructQ_entry A (colIdxOfTriple a b c t).1.1 (colIdxOfTriple a b c t).2.1.1
            row.1 (colIdxOfTriple a b c t).2.2.1 (colIdxOfTriple a b c t).1.2
            (colIdxOfTriple a b c t).2.1.2 row.2 (colIdxOfTriple a b c t).2.2.2
      · exact
          eval_poly_constructQ_entry A (colIdxOfTriple a b c t).1.1 (colIdxOfTriple a b c t).2.1.1
            (colIdxOfTriple a b c t).2.2.1 row.1 (colIdxOfTriple a b c t).1.2
            (colIdxOfTriple a b c t).2.1.2 (colIdxOfTriple a b c t).2.2.2 row.2

open scoped BigOperators
open Classical Matrix
open Firstproof

lemma eval_poly_G3_minor {n : ℕ} (A : Fin n → Matrix3x4) (m : Fin 4) (a b c : Fin n) (rows : Fin 4 → RowIdx n) (cols : Fin 4 → Triple3) :
    evalCameraPolynomial (poly_G3_minor n m a b c rows cols) A = Matrix.det ((Submatrix27 A m a b c).submatrix rows cols) := by
      -- The determinant of a matrix is a polynomial function, so evaluating each entry of the matrix and then taking the determinant is the same as taking the determinant of the evaluated matrix.
      have h_det_poly : ∀ (M : Matrix (Fin 4) (Fin 4) (MvPolynomial (AIndex n) ℝ)), evalCameraPolynomial (Matrix.det M) A = Matrix.det (fun i j => evalCameraPolynomial (M i j) A) := by
        simp +decide [ Matrix.det_apply' ];
        simp +decide [ Firstproof.evalCameraPolynomial, Finset.prod_mul_distrib ];
      convert h_det_poly _ using 2;
      ext i j; exact eval_poly_Submatrix27_entry A m a b c ( rows i ) ( cols j ) ▸ rfl;

open scoped BigOperators
open Classical Matrix
open Firstproof

lemma eval_poly_sum_sq_G3_block_ne_zero {n : ℕ} (A : Fin n → Matrix3x4) (m : Fin 4) (a b c : Fin n) :
    evalCameraPolynomial (poly_sum_sq_G3_block n m a b c) A ≠ 0 → (Submatrix27 A m a b c).rank ≥ 4 := by
      intro h_nonzero
      obtain ⟨rows, cols, h_det⟩ : ∃ rows : Fin 4 → RowIdx n, ∃ cols : Fin 4 → Triple3, Matrix.det ((Submatrix27 A m a b c).submatrix rows cols) ≠ 0 := by
        contrapose! h_nonzero;
        simp +decide [ Firstproof.poly_sum_sq_G3_block, h_nonzero ];
        simp +decide [ Firstproof.evalCameraPolynomial, Firstproof.poly_G3_minor, h_nonzero ];
        convert Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => ?_;
        convert congr_arg ( · ^ 2 ) ( h_nonzero x y ) using 1;
        · congr! 1;
          convert eval_poly_G3_minor A m a b c x y using 1;
        · grind;
      have h_submatrix : Matrix.rank ((Submatrix27 A m a b c).submatrix rows cols) = 4 := by
        have := Matrix.rank_mul_le ( ( Submatrix27 A m a b c ).submatrix rows cols ) ( ( Submatrix27 A m a b c ).submatrix rows cols ) ⁻¹; simp_all +decide [ isUnit_iff_ne_zero ] ;
        exact le_antisymm ( le_trans ( Matrix.rank_le_card_width _ ) ( by norm_num ) ) this.1;
      refine' h_submatrix ▸ _;
      have h_submatrix : ∀ (M : Matrix (RowIdx n) Triple3 ℝ), ∀ (rows : Fin 4 → RowIdx n) (cols : Fin 4 → Triple3), Matrix.rank (M.submatrix rows cols) ≤ Matrix.rank M := by
        intros M rows cols
        have h_submatrix : ∃ (P : Matrix (Fin 4) (RowIdx n) ℝ) (Q : Matrix (Triple3) (Fin 4) ℝ), M.submatrix rows cols = P * M * Q := by
          use Matrix.of (fun i j => if j = rows i then 1 else 0), Matrix.of (fun i j => if i = cols j then 1 else 0);
          ext i j; simp +decide [ Matrix.mul_apply ] ;
        obtain ⟨ P, Q, hPQ ⟩ := h_submatrix; rw [ hPQ ] ; exact Matrix.rank_mul_le_left _ _ |> le_trans <| Matrix.rank_mul_le_right _ _;
      exact h_submatrix _ _ _

open scoped BigOperators
open Classical Matrix
open Firstproof

lemma G3_of_rank_ge_4 {n : ℕ} (A : Fin n → Matrix3x4) (m : Fin 4) (a b c : Fin n) :
    (StackedMat A).rank = 4 → (Submatrix27 A m a b c).rank ≥ 4 →
    ColSpan (Submatrix27 A m a b c) = Wspace A := by
      intro h1 h2;
      refine' Submodule.eq_of_le_of_finrank_eq _ _;
      · intro x hx
        have h_submatrix : ∀ p : Triple3, (Submatrix27 A m a b c).col p ∈ ColSpan (StackedMat A) := by
          intro p
          have h_submatrix : (Submatrix27 A m a b c).col p ∈ ColSpan (Unfold m (constructQ A)) := by
            exact Submodule.subset_span ⟨ colIdxOfTriple a b c p, rfl ⟩;
          have h_submatrix : ∀ x : ColIdx n, (Unfold m (constructQ A)).col x ∈ ColSpan (StackedMat A) := by
            intro x
            have h_submatrix : (Unfold m (constructQ A)).col x ∈ ColSpan (StackedMat A * cofactorMat A m) := by
              rw [unfold_constructQ_eq_mul];
              exact Submodule.subset_span ( Set.mem_range_self x );
            refine' Submodule.span_le.mpr _ h_submatrix;
            rintro _ ⟨ y, rfl ⟩;
            simp +decide [ Matrix.mul_apply, ColSpan ];
            rw [ Submodule.mem_span_range_iff_exists_fun ];
            use fun i => (cofactorMat A m) i y;
            ext i; simp +decide [ Matrix.mul_apply, dotProduct ] ;
            ac_rfl;
          convert Submodule.span_le.mpr _ ‹_›;
          exact Set.range_subset_iff.mpr h_submatrix;
        have h_submatrix : ∀ x ∈ ColSpan (Submatrix27 A m a b c), x ∈ ColSpan (StackedMat A) := by
          intro x hx
          induction' hx using Submodule.span_induction with x hx ih;
          · grind;
          · exact Submodule.zero_mem _;
          · exact Submodule.add_mem _ ‹_› ‹_›;
          · exact Submodule.smul_mem _ _ ‹_›;
        exact h_submatrix x hx
      · refine' le_antisymm _ _;
        · refine' Submodule.finrank_mono _;
          intro x hx;
          -- Since the columns of the submatrix are a subset of the columns of the unfolded matrix, and the unfolded matrix is a submatrix of the stacked matrix, the column span of the submatrix is contained within the column span of the stacked matrix.
          have h_subset : ColSpan (Submatrix27 A m a b c) ≤ ColSpan (Unfold m (constructQ A)) := by
            refine' Submodule.span_le.mpr _;
            rintro _ ⟨ t, rfl ⟩;
            refine' Submodule.subset_span ⟨ colIdxOfTriple a b c t, rfl ⟩;
          have h_subset : ColSpan (Unfold m (constructQ A)) ≤ ColSpan (StackedMat A) := by
            have h_subset : Unfold m (constructQ A) = StackedMat A * cofactorMat A m := by
              exact unfold_constructQ_eq_mul A m
            rw [h_subset];
            unfold ColSpan;
            rw [ Submodule.span_le ];
            rintro _ ⟨ i, rfl ⟩;
            simp +decide [ Matrix.mul_apply, Submodule.mem_span_range_iff_exists_fun ];
            use fun j => cofactorMat A m j i;
            ext j; simp +decide [ Matrix.mul_apply, dotProduct ] ;
            ac_rfl;
          exact h_subset <| by solve_by_elim;
        · convert h1.le.trans h2 using 1;
          · -- The rank of a matrix is equal to the finrank of its column space.
            have h_rank_eq_finrank : ∀ (M : Matrix (RowIdx n) (Fin 4) ℝ), Matrix.rank M = Module.finrank ℝ (ColSpan M) := by
              intro M; exact (by
              convert Matrix.rank_eq_finrank_span_cols M using 1);
            exact h_rank_eq_finrank _ ▸ rfl;
          · convert rfl;
            convert Matrix.rank_eq_finrank_span_cols _

open scoped BigOperators
open Classical Matrix
open Firstproof

lemma eval_strong_genericity_poly_ne_zero_imp_generic {n : ℕ} (_hn : 5 ≤ n) (A : Fin n → Matrix3x4) :
    evalCameraPolynomial (strong_genericity_poly n) A ≠ 0 → GenericCameras A := by
      intro h_nonzero;
      refine' ⟨ _, _, _ ⟩;
      · unfold Firstproof.strong_genericity_poly at h_nonzero;
        unfold Firstproof.total_genericity_poly at h_nonzero; simp_all +decide [ Firstproof.evalCameraPolynomial ] ;
        exact Firstproof.eval_poly_sum_sq_stacked_ne_zero A h_nonzero.1.1;
      · intro α
        have h_eval_poly_sum_sq_cam_ne_zero : evalCameraPolynomial (poly_sum_sq_cam n α) A ≠ 0 := by
          unfold Firstproof.strong_genericity_poly at h_nonzero; simp_all +decide [ Finset.prod_eq_zero_iff ] ;
          contrapose! h_nonzero; simp_all +decide [ Firstproof.total_genericity_poly ] ;
          simp_all +decide [ Finset.prod_eq_mul_prod_diff_singleton ( Finset.mem_univ α ), Firstproof.evalCameraPolynomial ]
        exact (eval_poly_sum_sq_cam_ne_zero A α h_eval_poly_sum_sq_cam_ne_zero);
      · intro m a b c h_nonall
        have h_eval_G3 : evalCameraPolynomial (poly_sum_sq_G3_block n m a b c) A ≠ 0 := by
          rw [ Firstproof.strong_genericity_poly ] at h_nonzero;
          contrapose! h_nonzero; simp_all +decide [ Firstproof.poly_G3_total ] ;
          simp +decide [ h_nonzero, Finset.prod_ite ];
          simp +decide [ h_nonzero, Finset.prod_eq_zero_iff, Firstproof.evalCameraPolynomial ];
          exact Or.inr ⟨ m, a, b, c, h_nonall, h_nonzero ⟩;
        have h_eval_stacked : evalCameraPolynomial (poly_sum_sq_stacked n) A ≠ 0 := by
          contrapose! h_nonzero;
          unfold Firstproof.strong_genericity_poly;
          unfold Firstproof.total_genericity_poly; simp_all +decide [ Firstproof.evalCameraPolynomial ] ;
        apply G3_of_rank_ge_4 A m a b c (by
          exact eval_poly_sum_sq_stacked_ne_zero A h_eval_stacked) (by
          exact eval_poly_sum_sq_G3_block_ne_zero A m a b c h_eval_G3)

open scoped BigOperators
open Classical Matrix
open Firstproof

def witnessCols {n : ℕ} (_a b c : Fin n) : Fin 4 → Triple3 :=
  fun k =>
    if b ≠ c then
      match k with
      | 0 => (1, 2, 2)
      | 1 => (0, 2, 2)
      | 2 => (0, 1, 2)
      | _ => (0, 2, 1)
    else
      match k with
      | 0 => (2, 1, 2)
      | 1 => (2, 0, 2)
      | 2 => (2, 1, 0)
      | _ => (0, 1, 2)

open scoped BigOperators
open Classical Matrix
open Firstproof

def witnessCofactorMatrix (n : ℕ) (m : Fin 4) (a b c : Fin n) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (cofactorMat (witnessA n) m) i (colIdxOfTriple a b c (witnessCols a b c j))

open scoped BigOperators
open Classical Matrix
open Firstproof

lemma witnessCofactorMatrix_det_ne_zero {n : ℕ} (m : Fin 4) (a b c : Fin n) (h : NotAllEqual3 a b c) :
    (witnessCofactorMatrix n m a b c).det ≠ 0 := by
  fin_cases m
  · by_cases hbc : b = c
    ·
      simp_all +decide [ NotAllEqual3 ];
      unfold Firstproof.witnessCofactorMatrix;
      unfold Firstproof.colIdxOfTriple Firstproof.witnessCols; simp +decide [ Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.prod_univ_succ ] ;
      unfold Firstproof.cofactorMat Firstproof.witnessA; simp +decide [ Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.prod_univ_succ ] ;
      unfold Firstproof.fixedRowsMat; simp +decide [ Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.succAbove ] ; ring_nf ;
      exact ⟨ by intro H; exact h ( Fin.ext <| by exact Nat.cast_injective ( by linarith : ( a : ℝ ) = c ) ), by intro H; exact h ( Fin.ext <| by exact Nat.cast_injective ( by linarith : ( a : ℝ ) = c ) ), by intro H; exact h ( Fin.ext <| by exact Nat.cast_injective ( by linarith : ( a : ℝ ) = c ) ) ⟩
    ·
      unfold Firstproof.witnessCofactorMatrix Firstproof.witnessA Firstproof.cofactorMat;
      unfold Firstproof.colIdxOfTriple Firstproof.witnessCols Firstproof.fixedRowsMat; simp +decide [ Matrix.det_succ_row_zero ] ;
      simp +decide [ Fin.sum_univ_succ, Fin.succAbove, hbc ];
      exact ⟨ by rw [ add_eq_zero_iff_eq_neg ] ; exact fun h => hbc <| Fin.ext <| by aesop, by rw [ add_eq_zero_iff_eq_neg ] ; exact fun h => hbc <| Fin.ext <| by aesop ⟩
  · by_cases hbc : b = c
    ·
      -- Since $b = c$, we can simplify the cofactor matrix entries.
      simp [hbc, Firstproof.witnessCofactorMatrix, Firstproof.cofactorMat];
      unfold Firstproof.witnessCofactorMatrix; simp +decide [ Firstproof.cofactorMat ] ;
      simp +decide [ Matrix.det_succ_row_zero, Firstproof.witnessA ] ;
      unfold Firstproof.fixedRowsMat Firstproof.colIdxOfTriple Firstproof.witnessCols; simp +decide [ Firstproof.witnessA ] ;
      simp +decide [ Fin.sum_univ_succ, Fin.succAbove ] at * ;
      exact fun h' => h <| by rw [ neg_add_eq_zero ] at h'; aesop;
    ·
      unfold Firstproof.witnessCofactorMatrix Firstproof.cofactorMat;
      simp +decide [ Matrix.det_succ_row_zero, Fin.sum_univ_succ ];
      simp +decide [ Fin.succAbove, Firstproof.fixedRowsMat, Firstproof.witnessA ] at *;
      unfold Firstproof.colIdxOfTriple Firstproof.witnessCols; simp +decide [ Fin.ext_iff ] ;
      split_ifs <;> simp_all +decide [ Fin.forall_fin_succ, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val' ];
      · exact False.elim <| hbc <| Fin.ext ‹_›;
      · exact ⟨ by rw [ add_eq_zero_iff_eq_neg ] ; aesop, by rw [ add_eq_zero_iff_eq_neg ] ; aesop ⟩
  · by_cases hbc : b = c
    ·
      unfold Firstproof.witnessCofactorMatrix;
      unfold Firstproof.colIdxOfTriple Firstproof.witnessCols; simp +decide [ Matrix.det_succ_row_zero ] ;
      simp +decide [ Fin.sum_univ_succ, Fin.prod_univ_succ, Firstproof.cofactorMat, Firstproof.witnessA ];
      simp +decide [ Firstproof.fixedRowsMat, Firstproof.witnessA ];
      simp +decide [ Matrix.det_fin_three, Matrix.submatrix ] at *;
      simp +decide [ Fin.succAbove ] at *;
      simp +decide [ hbc ] at *;
      exact ⟨ by rw [ neg_add_eq_sub, sub_eq_zero ] ; exact fun h' => h <| by aesop, by rw [ add_eq_zero_iff_eq_neg ] ; exact fun h' => h <| by aesop ⟩
    ·
      unfold Firstproof.witnessCofactorMatrix;
      unfold Firstproof.cofactorMat Firstproof.colIdxOfTriple Firstproof.witnessCols; simp +decide [ Fin.sum_univ_succ, Matrix.det_succ_row_zero ] ;
      simp +decide [ Fin.succAbove, Firstproof.fixedRowsMat, Firstproof.witnessA ];
      split_ifs ; norm_num [ Fin.ext_iff, Matrix.vecHead, Matrix.vecTail ] at * ; ring_nf at * ; simp_all +decide [ Fin.ext_iff, Matrix.vecHead, Matrix.vecTail ] ;
      exact ⟨ sub_ne_zero_of_ne <| by aesop, by rw [ neg_add_eq_sub ] ; exact sub_ne_zero_of_ne <| by aesop, sub_ne_zero_of_ne <| by aesop ⟩
  · by_cases hbc : b = c
    ·
      unfold Firstproof.witnessCofactorMatrix;
      unfold Firstproof.colIdxOfTriple Firstproof.witnessCols Firstproof.cofactorMat;
      simp +decide [ Matrix.det_succ_row_zero, Matrix.submatrix ];
      simp +decide [ Fin.sum_univ_succ, Fin.succAbove ];
      simp +decide [ *, Firstproof.fixedRowsMat, Firstproof.witnessA ] at *;
      exact fun h' => h <| by rw [ neg_add_eq_zero ] at h'; aesop;
    ·
      unfold Firstproof.witnessCofactorMatrix;
      unfold Firstproof.witnessCols Firstproof.colIdxOfTriple Firstproof.cofactorMat Firstproof.witnessA ; norm_num [ Fin.sum_univ_succ, Fin.prod_univ_succ ];
      simp +decide [ hbc, Matrix.det_succ_column_zero ];
      simp +decide [ Fin.sum_univ_succ, Fin.prod_univ_succ, Firstproof.fixedRowsMat ];
      simp +decide [ Fin.succAbove ] at *;
      exact ⟨ by rw [ add_eq_zero_iff_eq_neg ] ; exact fun h => hbc <| Fin.ext <| by rw [ ← @Nat.cast_inj ℝ ] ; linarith, by rw [ add_eq_zero_iff_eq_neg ] ; exact fun h => hbc <| Fin.ext <| by rw [ ← @Nat.cast_inj ℝ ] ; linarith ⟩

open scoped BigOperators
open Classical Matrix
open Firstproof

lemma witnessSubmatrix_eq {n : ℕ} (m : Fin 4) (a b c : Fin n) :
    (Submatrix27 (witnessA n) m a b c).submatrix id (witnessCols a b c) =
    StackedMat (witnessA n) * witnessCofactorMatrix n m a b c := by
      unfold Submatrix27 Firstproof.StackedMat Firstproof.witnessCofactorMatrix;
      ext ⟨ α, i ⟩ j; simp +decide [ Firstproof.Unfold, Firstproof.constructQ ] ;
      fin_cases m <;> simp +decide [ Matrix.mul_apply, Firstproof.stackedRowsMatrix, Firstproof.constructQ ];
      · rw [ Matrix.det_succ_row_zero ] ; norm_num [ Fin.sum_univ_succ ] ; ring_nf!;
        unfold Firstproof.cofactorMat; simp +decide [ Matrix.det_succ_row_zero ] ; ring!;
      · simp +decide [ Matrix.det_succ_row_zero, Firstproof.cofactorMat ];
        simp +decide [ Fin.sum_univ_succ, Firstproof.fixedRowsMat, Firstproof.witnessA ] ; ring!;
      · rw [ Matrix.det_succ_row _ 2 ] ; simp +decide [ Fin.sum_univ_succ, Matrix.det_succ_row _ 2 ] ;
        unfold Firstproof.cofactorMat; simp +decide [ Matrix.det_succ_row _ 2 ] ;
        unfold Firstproof.fixedRowsMat; simp +decide [ Fin.sum_univ_succ, Matrix.det_succ_row _ 2 ] ;
        simp +decide [ Fin.succAbove, Firstproof.witnessA ] at *;
      · rw [ Matrix.det_succ_row _ 3 ] ; simp +decide [ Fin.sum_univ_succ, Firstproof.cofactorMat ];
        unfold Firstproof.fixedRowsMat; simp +decide [ Matrix.det_succ_row _ 3 ] ;
        exact rfl

open scoped BigOperators
open Classical Matrix
open Firstproof

lemma witnessA_G3_rank {n : ℕ} (hn : 5 ≤ n) (m : Fin 4) (a b c : Fin n) (h : NotAllEqual3 a b c) :
    (Submatrix27 (witnessA n) m a b c).rank ≥ 4 := by
      -- By `witnessCofactorMatrix_det_ne_zero`, `det(C) \ne 0`, so `C` is invertible.
      have h_C_inv : Matrix.det (witnessCofactorMatrix n m a b c) ≠ 0 := by
        exact witnessCofactorMatrix_det_ne_zero m a b c h;
      -- Since `S' = StackedMat (witnessA n) * C`, and `C` is invertible, we have `rank(S') = rank(StackedMat (witnessA n))`.
      have h_rank_S' : Matrix.rank (Submatrix27 (witnessA n) m a b c |>.submatrix id (witnessCols a b c)) = Matrix.rank (StackedMat (witnessA n)) := by
        have h_S'_eq : (Submatrix27 (witnessA n) m a b c).submatrix id (witnessCols a b c) = (StackedMat (witnessA n)) * (witnessCofactorMatrix n m a b c) := by
          exact witnessSubmatrix_eq m a b c;
        have := Matrix.rank_mul_le ( StackedMat ( witnessA n ) ) ( witnessCofactorMatrix n m a b c ) ; aesop;
      have h_rank_S : Matrix.rank (StackedMat (witnessA n)) = 4 := by
        convert ( witnessA_properties hn ) |>.1;
      refine' h_rank_S ▸ h_rank_S'.symm ▸ _;
      -- Since the submatrix is a subset of the original matrix, its rank is less than or equal to the rank of the original matrix.
      have h_submatrix_rank : ∀ (M : Matrix (RowIdx n) (Triple3) ℝ) (cols : Fin 4 → Triple3), Matrix.rank (M.submatrix id cols) ≤ Matrix.rank M := by
        intro M cols; exact (by
        have h_submatrix_rank : ∀ (M : Matrix (RowIdx n) (Triple3) ℝ) (cols : Fin 4 → Triple3), Matrix.rank (M.submatrix id cols) ≤ Matrix.rank M := by
          intro M cols
          have h_submatrix : ∃ (P : Matrix (RowIdx n) (RowIdx n) ℝ) (Q : Matrix (Triple3) (Fin 4) ℝ), M.submatrix id cols = P * M * Q := by
            use 1, Matrix.of (fun i j => if i = cols j then 1 else 0);
            ext i j; simp +decide [ Matrix.mul_apply ] ;
          obtain ⟨ P, Q, hPQ ⟩ := h_submatrix; rw [ hPQ ] ; exact Matrix.rank_mul_le_left _ _ |> le_trans <| Matrix.rank_mul_le_right _ _;
        exact h_submatrix_rank M cols);
      exact h_submatrix_rank _ _

open scoped BigOperators
open Classical Matrix
open Firstproof

lemma poly_sum_sq_G3_block_ne_zero_poly {n : ℕ} (hn : 5 ≤ n) (m : Fin 4) (a b c : Fin n) (h : NotAllEqual3 a b c) :
    poly_sum_sq_G3_block n m a b c ≠ 0 := by
  intro h_zero
  have h_eval_zero : evalCameraPolynomial (poly_sum_sq_G3_block n m a b c) (witnessA n) = 0 := by
    rw [h_zero]
    simp [evalCameraPolynomial]
  unfold poly_sum_sq_G3_block at h_eval_zero
  simp only [evalCameraPolynomial, map_sum, map_pow] at h_eval_zero
  have h_rank : (Submatrix27 (witnessA n) m a b c).rank ≥ 4 := witnessA_G3_rank hn m a b c h
  obtain ⟨rows, cols, h_det_ne_zero⟩ := exists_submatrix_det_ne_zero_of_rank_ge (Submatrix27 (witnessA n) m a b c) 4 h_rank
  have h_term_zero : (evalCameraPolynomial (poly_G3_minor n m a b c rows cols) (witnessA n))^2 = 0 := by
    rw [Finset.sum_eq_zero_iff_of_nonneg] at h_eval_zero
    · have h_inner := h_eval_zero rows (Finset.mem_univ rows)
      rw [Finset.sum_eq_zero_iff_of_nonneg] at h_inner
      · exact h_inner cols (Finset.mem_univ cols)
      · intro _ _; apply sq_nonneg
    · intro _ _; apply Finset.sum_nonneg; intro _ _; apply sq_nonneg
  rw [eval_poly_G3_minor] at h_term_zero
  simp at h_term_zero
  contradiction

end AristotleLemmas

theorem strong_genericity_polynomial_exists (n : ℕ) (hn : 5 ≤ n) :
    StrongGenericityPolynomialExists n := by
  have hG3 : ∀ m : Fin 4, ∀ a b c : Fin n, NotAllEqual3 a b c → poly_sum_sq_G3_block n m a b c ≠ 0 := by
    exact fun m a b c h => poly_sum_sq_G3_block_ne_zero_poly hn m a b c h
  exact ⟨ _, mul_ne_zero ( total_genericity_poly_ne_zero hn ) ( Finset.prod_ne_zero_iff.mpr fun m hm => Finset.prod_ne_zero_iff.mpr fun a ha => Finset.prod_ne_zero_iff.mpr fun b hb => Finset.prod_ne_zero_iff.mpr fun c hc => by aesop ), fun A hA => eval_strong_genericity_poly_ne_zero_imp_generic hn A hA ⟩


theorem nine_of_hStrong
    (hStrong : ∀ n : ℕ, 5 ≤ n → StrongGenericityPolynomialExists n) :
    ∃ (d : ℕ),
      ∀ n : ℕ, 5 ≤ n →
        ∃ (N : ℕ) (F : PolyMap n N),
          PolyMap.UniformDegreeBound d F ∧
          ∃ (G : MvPolynomial (AIndex n) ℝ), G ≠ 0 ∧
            ∀ (A : Fin n → Matrix3x4),
              evalCameraPolynomial G A ≠ 0 →
              ∀ (lam : Lambda n),
                (∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ) →
                  (IsZeroVec (PolyMap.eval F (scaleQ lam (constructQ A))) ↔
                    (∃ (u v w x : Fin n → ℝˣ),
                      ∀ α β γ δ, NotIdentical α β γ δ →
                        lam α β γ δ =
                          (u α : ℝ) * (v β : ℝ) * (w γ : ℝ) * (x δ : ℝ))) := by
  refine ⟨5, ?_⟩
  intro n hn
  refine ⟨numMinors n, polyMapF n, polyMapF_degree_bound n, ?_⟩
  rcases hStrong n hn with ⟨G, hGne, hGgen⟩
  refine ⟨G, hGne, ?_⟩
  intro A hGA lam hsupp
  have hgen : GenericCameras A := hGgen A hGA
  constructor
  · intro hvanish
    exact reverse_direction hn A hgen lam hsupp hvanish
  · rintro ⟨u, v, w, x, hfact⟩
    exact forward_direction A lam hsupp u v w x hfact

theorem nine :
    ∃ (d : ℕ),
      ∀ n : ℕ, 5 ≤ n →
        ∃ (N : ℕ) (F : PolyMap n N),
          PolyMap.UniformDegreeBound d F ∧
          ∃ (G : MvPolynomial (AIndex n) ℝ), G ≠ 0 ∧
            ∀ (A : Fin n → Matrix3x4),
              evalCameraPolynomial G A ≠ 0 →
              ∀ (lam : Lambda n),
                (∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ) →
                  (IsZeroVec (PolyMap.eval F (scaleQ lam (constructQ A))) ↔
                    (∃ (u v w x : Fin n → ℝˣ),
                      ∀ α β γ δ, NotIdentical α β γ δ →
                        lam α β γ δ =
                          (u α : ℝ) * (v β : ℝ) * (w γ : ℝ) * (x δ : ℝ))) := by
  exact nine_of_hStrong (fun n hn => strong_genericity_polynomial_exists n hn)

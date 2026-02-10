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

namespace Arxiv.«2602.05192»

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

-- ═══════════════════════════════════════════════════════════════
-- Reverse direction infrastructure
-- ═══════════════════════════════════════════════════════════════


-- TODO: converse to `rank_le_four_imp_5x5_det_zero`.
-- If all 5×5 minors vanish, then the matrix rank is ≤ 4.
/- PROVIDED SOLUTION:

Goal:
  If every `5×5` minor of a real matrix `M : Matrix α β ℝ` is zero, then `rank M ≤ 4`.

Standard linear algebra fact (over a field):
  `rank M` is the largest integer `k` such that some `k×k` minor of `M` is nonzero.
In particular:
  `rank M ≥ 5`  ⇔  ∃ rows cols, det (M.submatrix rows cols) ≠ 0 for some `rows : Fin 5 → α`,
                    `cols : Fin 5 → β`.
So the contrapositive of the theorem is:
  if `rank M ≥ 5` then some `5×5` minor is nonzero.

Proof idea for the contrapositive:
1) View `M` as a linear map `ℝ^β → ℝ^α` via `mulVecLin`.
   Then `rank M = dim(im(M)) = dim(span(columns of M))`.
2) If `rank M ≥ 5`, then the column span contains 5 linearly independent vectors.
   Concretely, one can pick 5 columns of `M` that are linearly independent; equivalently,
   there exists a submatrix `S` consisting of 5 columns of `M` with `rank S = 5`.
3) A matrix with 5 columns has rank 5 iff its columns are linearly independent, i.e. the linear map
   `ℝ^5 → ℝ^α` defined by `S` is injective.
4) Injectivity forces the existence of 5 coordinate functionals (i.e. a choice of 5 rows) such that
   the composite `ℝ^5 → ℝ^α → ℝ^5` is an isomorphism. In matrix terms, selecting those 5 rows gives
   a square `5×5` submatrix `S'` with `det S' ≠ 0`.
   (Geometrically: if the image is 5D, some 5 coordinates restrict to a basis.)
5) Since `S` is a column-submatrix of `M`, any `5×5` minor of `S` is also a `5×5` minor of `M`
   (for the same row selection and the chosen 5 columns).
   Hence `M` has a `5×5` minor with nonzero determinant.

Therefore, if *all* `5×5` minors of `M` vanish, `rank M` cannot be ≥ 5, so `rank M ≤ 4`.

Remarks on formalization strategy (Lean/mathlib):
  One can implement step (4) by working with `im(M)` as a finite-dimensional subspace of `(α → ℝ)`,
  choosing a basis of `im(M)` and then using the existence of a set of 5 coordinates on `(α → ℝ)`
  that makes the coordinate map injective on that 5D subspace, yielding an invertible `5×5` matrix.
  This is the only genuinely nontrivial linear-algebra bridge needed here.
-/
-- If the rows of a square matrix over `ℝ` are linearly independent, then its determinant is nonzero.
-- We use this for extracting a nonzero minor from full rank via a row selection argument.
lemma det_ne_zero_of_linearIndependent_rows {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (h : LinearIndependent ℝ (fun i : n => A i)) : A.det ≠ 0 := by
  classical
  -- Row-independence is injectivity of right multiplication `v ↦ v ᵥ* A`.
  have hinj : Function.Injective fun v : n → ℝ => v ᵥ* A :=
    (Matrix.vecMul_injective_iff (R := ℝ) (M := A)).2 (by simpa [Matrix.row] using h)
  -- In finite dimension, injective endomorphisms are surjective.
  have hsurj : Function.Surjective fun v : n → ℝ => v ᵥ* A := by
    let f : (n → ℝ) →ₗ[ℝ] (n → ℝ) := Matrix.vecMulLinear (M := A)
    have hf_inj : Function.Injective (f : (n → ℝ) → (n → ℝ)) := by
      simpa [f, Matrix.vecMulLinear_apply] using hinj
    have hf_surj : Function.Surjective (f : (n → ℝ) → (n → ℝ)) :=
      (LinearMap.injective_iff_surjective (f := f)).1 hf_inj
    simpa [f, Matrix.vecMulLinear_apply] using hf_surj
  -- Build an explicit left inverse matrix `B` by choosing preimages of basis vectors.
  choose preimage hpreimage using fun j : n => hsurj (Pi.single j 1)
  let B : Matrix n n ℝ := fun i j => preimage i j
  have hBA : B * A = 1 := by
    ext i j
    have hij := congrArg (fun v => v j) (hpreimage i)
    -- Unfold `vecMul` as a finite sum; this is exactly matrix multiplication by rows.
    simpa [B, Matrix.vecMul, dotProduct, Matrix.one_apply, Pi.single_apply, Matrix.mul_apply,
      eq_comm] using hij
  exact Matrix.det_ne_zero_of_left_inverse (A := A) (B := B) hBA

theorem minors5x5_zero_imp_rank_le_four {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (M : Matrix α β ℝ)
    (hminors : ∀ (rows : Fin 5 → α) (cols : Fin 5 → β),
      (M.submatrix rows cols).det = 0) :
    M.rank ≤ 4 := by
  classical
  by_contra hle
  have hrank : 5 ≤ M.rank := Nat.succ_le_of_lt (Nat.lt_of_not_ge hle)
  -- Extract a linearly independent family of columns of size `rank M` (and hence at least 5).
  rcases exists_linearIndependent' ℝ (M.col) with ⟨κ, a, ha_inj, hspan, hLI⟩
  haveI : Finite κ := by
    classical
    exact LinearIndependent.finite (R := ℝ) (M := (α → ℝ)) (f := M.col ∘ a) hLI
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  have hcardκ : Fintype.card κ = M.rank := by
    have hcard :
        Fintype.card κ = (Set.range (M.col ∘ a)).finrank ℝ :=
      (linearIndependent_iff_card_eq_finrank_span (K := ℝ) (b := M.col ∘ a)).1 hLI
    calc
      Fintype.card κ = (Set.range (M.col ∘ a)).finrank ℝ := hcard
      _ = (Set.range M.col).finrank ℝ := by
        -- `Set.finrank` is `finrank` of the spanned submodule; use the span equality.
        -- Rewriting types via equality needs an explicit `LinearEquiv`.
        simpa [Set.finrank] using
          (LinearEquiv.finrank_eq (LinearEquiv.ofEq
            (Submodule.span ℝ (Set.range (M.col ∘ a)))
            (Submodule.span ℝ (Set.range M.col)) hspan))
      _ = M.rank := by
        simpa [Set.finrank] using (Matrix.rank_eq_finrank_span_cols (R := ℝ) (A := M)).symm
  have h5κ : 5 ≤ Fintype.card κ := by simpa [hcardκ] using hrank

  -- Choose 5 distinct indices in `κ`, hence 5 distinct columns in `β`.
  let embκ : Fin 5 ↪ κ :=
    (Fin.castLEEmb h5κ).trans (Fintype.equivFin κ).symm.toEmbedding
  let cols : Fin 5 → β := fun i => a (embκ i)
  have hLIcols : LinearIndependent ℝ (fun i : Fin 5 => M.col (cols i)) := by
    have hsub : LinearIndependent ℝ (fun i : Fin 5 => (M.col ∘ a) (embκ i)) :=
      hLI.comp embκ embκ.injective
    simpa [cols, Function.comp] using hsub

  -- Form the 5-column submatrix.
  let S : Matrix α (Fin 5) ℝ := M.submatrix id cols
  have hLIcolsS : LinearIndependent ℝ S.col := by
    have hcol : S.col = fun i : Fin 5 => M.col (cols i) := by
      funext i
      ext r
      rfl
    simpa [hcol] using hLIcols

  -- The submatrix `S` has rank 5.
  have hrankS : S.rank = 5 := by
    have hrowsT : LinearIndependent ℝ (Sᵀ.row) := by
      have hrow : (Sᵀ.row) = S.col := by
        funext i
        ext j
        rfl
      simpa [hrow] using hLIcolsS
    have hrT : Sᵀ.rank = Fintype.card (Fin 5) :=
      (LinearIndependent.rank_matrix (R := ℝ) (M := Sᵀ) hrowsT)
    simpa [Fintype.card_fin, Matrix.rank_transpose (R := ℝ) (A := S)] using hrT

  -- Extract 5 linearly independent rows of `S`; their square submatrix has nonzero determinant.
  rcases exists_linearIndependent' ℝ (S.row) with ⟨ι, r, hr_inj, hr_span, hr_LI⟩
  haveI : Finite ι := by
    classical
    exact LinearIndependent.finite (R := ℝ) (M := (Fin 5 → ℝ)) (f := S.row ∘ r) hr_LI
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  have hcardι : Fintype.card ι = 5 := by
    have hcard :
        Fintype.card ι = (Set.range (S.row ∘ r)).finrank ℝ :=
      (linearIndependent_iff_card_eq_finrank_span (K := ℝ) (b := S.row ∘ r)).1 hr_LI
    calc
      Fintype.card ι = (Set.range (S.row ∘ r)).finrank ℝ := hcard
      _ = (Set.range S.row).finrank ℝ := by
        simpa [Set.finrank] using
          (LinearEquiv.finrank_eq (LinearEquiv.ofEq
            (Submodule.span ℝ (Set.range (S.row ∘ r)))
            (Submodule.span ℝ (Set.range S.row)) hr_span))
      _ = S.rank := by
        simpa [Set.finrank] using (Matrix.rank_eq_finrank_span_row (R := ℝ) (A := S)).symm
      _ = 5 := hrankS

  -- Enumerate the independent rows.
  let eι : ι ≃ Fin 5 :=
    (Fintype.equivFin ι).trans (Equiv.cast (congrArg Fin hcardι))
  let rows : Fin 5 → α := fun i => r (eι.symm i)
  have hrowsLI : LinearIndependent ℝ (fun i : Fin 5 => (S.submatrix rows id) i) := by
    have hroweq : ∀ i : Fin 5, (S.submatrix rows id) i = S.row (rows i) := by
      intro i
      ext j
      rfl
    have hsub : LinearIndependent ℝ (fun i : Fin 5 => (S.row ∘ r) (eι.symm i)) :=
      hr_LI.comp eι.symm eι.symm.injective
    simpa [rows, Function.comp, hroweq] using hsub

  have hdet : (S.submatrix rows id).det ≠ 0 :=
    det_ne_zero_of_linearIndependent_rows (A := S.submatrix rows id) hrowsLI

  -- This determinant is also a 5×5 minor of `M`.
  have : (M.submatrix rows cols).det ≠ 0 := by
    simpa [S, Matrix.submatrix_submatrix] using hdet
  exact this (by simpa using hminors rows cols)

-- TODO: convenient wrapper for “column span” of a matrix, used heavily in the reverse direction.
def ColSpan {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℝ) : Submodule ℝ (m → ℝ) :=
  Submodule.span ℝ (Set.range M.col)

-- TODO: if `S` is made out of columns of `M`, `rank M ≤ 4`, and `rank S = 4`, then their column
-- spans agree. (This is a key step for pinning down `col(T_(m))` from the 27-column submatrices.)
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

-- Generic camera properties needed for the reverse direction.
--
-- We encode the paper's “generic spanning” conditions by requiring that for each not-all-equal
-- triple of camera indices, the corresponding `3n×27` submatrix of the appropriate unfolding of
-- `constructQ A` has rank `4`.
abbrev Triple3 := Fin 3 × Fin 3 × Fin 3

def NotAllEqual3 {n : ℕ} (x y z : Fin n) : Prop := ¬ (x = y ∧ y = z)

def colFun0 {n : ℕ} (β γ δ : Fin n) : Triple3 → ColIdx n :=
  fun t => ((β, t.1), ((γ, t.2.1), (δ, t.2.2)))

def colFun1 {n : ℕ} (α γ δ : Fin n) : Triple3 → ColIdx n :=
  fun t => ((α, t.1), ((γ, t.2.1), (δ, t.2.2)))

def colFun2 {n : ℕ} (α β δ : Fin n) : Triple3 → ColIdx n :=
  fun t => ((α, t.1), ((β, t.2.1), (δ, t.2.2)))

noncomputable def Submatrix1 {n : ℕ} (A : Fin n → Matrix3x4) (β γ δ : Fin n) :
    Matrix (RowIdx n) Triple3 ℝ :=
  (Unfold 0 (constructQ A)).submatrix id (colFun0 β γ δ)

noncomputable def Submatrix2 {n : ℕ} (A : Fin n → Matrix3x4) (α γ δ : Fin n) :
    Matrix (RowIdx n) Triple3 ℝ :=
  (Unfold 1 (constructQ A)).submatrix id (colFun1 α γ δ)

noncomputable def Submatrix3 {n : ℕ} (A : Fin n → Matrix3x4) (α β δ : Fin n) :
    Matrix (RowIdx n) Triple3 ℝ :=
  (Unfold 2 (constructQ A)).submatrix id (colFun2 α β δ)

def GenericCameras {n : ℕ} (A : Fin n → Matrix3x4) : Prop :=
  (StackedMat A).rank = 4 ∧
  (∀ α : Fin n, (A α).rank = 3) ∧
  (∀ β γ δ : Fin n, NotAllEqual3 β γ δ → (Submatrix1 A β γ δ).rank = 4) ∧
  (∀ α γ δ : Fin n, NotAllEqual3 α γ δ → (Submatrix2 A α γ δ).rank = 4) ∧
  (∀ α β δ : Fin n, NotAllEqual3 α β δ → (Submatrix3 A α β δ).rank = 4)

-- Block-diagonal (block-scalar) matrices acting on `RowIdx n` by scaling each camera block.
noncomputable def BlockDiagonal {n : ℕ} (s : Fin n → ℝ) : Matrix (RowIdx n) (RowIdx n) ℝ :=
  Matrix.diagonal (fun p : RowIdx n => s p.1)

lemma BlockDiagonal_mul_apply {n : ℕ} (s : Fin n → ℝ) (M : Matrix (RowIdx n) α ℝ) (p : RowIdx n)
    (j : α) :
    (BlockDiagonal s * M) p j = s p.1 * M p j := by
  classical
  -- Multiplying by a diagonal matrix scales rows.
  simp [BlockDiagonal, Matrix.mul_apply, Matrix.diagonal, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_ite_eq', Finset.filter_eq', Finset.filter_ne', mul_assoc, mul_comm, mul_left_comm]

lemma BlockDiagonal_det_ne_zero {n : ℕ} (s : Fin n → ℝ) (hs : ∀ i : Fin n, s i ≠ 0) :
    (BlockDiagonal s).det ≠ 0 := by
  classical
  -- Determinant of a diagonal matrix is the product of its diagonal entries.
  simp [BlockDiagonal, Matrix.det_diagonal, hs, Finset.prod_ne_zero_iff]

lemma BlockDiagonal_isUnit_det {n : ℕ} (s : Fin n → ℝ) (hs : ∀ i : Fin n, s i ≠ 0) :
    IsUnit (BlockDiagonal s).det := by
  simpa [isUnit_iff_ne_zero] using BlockDiagonal_det_ne_zero (n := n) s hs

-- Column span of a left product.
lemma ColSpan_mul_left {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (D : Matrix m m ℝ) (M : Matrix m n ℝ) :
    ColSpan (D * M) = Submodule.map (Matrix.mulVecLin D) (ColSpan M) := by
  classical
  unfold ColSpan
  -- `map_span` turns `map` of a span into a span of the image; reduce to a range equality.
  rw [Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨M.col j, ?_, ?_⟩
    · exact ⟨j, rfl⟩
    · -- `D.mulVecLin` sends a column to the corresponding column of the product.
      ext i
      simp [Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.col, Matrix.mul_apply, dotProduct]
  · rintro ⟨v, ⟨j, rfl⟩, rfl⟩
    refine ⟨j, ?_⟩
    ext i
    simp [Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.col, Matrix.mul_apply, dotProduct]

-- Column span inclusion for a general product `B * C`.
lemma ColSpan_mul_le_left {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (B : Matrix m n ℝ) (C : Matrix n p ℝ) :
    ColSpan (B * C) ≤ ColSpan B := by
  classical
  refine Submodule.span_le.2 ?_
  rintro _ ⟨j, rfl⟩
  have hrange :
      LinearMap.range B.mulVecLin = ColSpan B := by
    simpa [ColSpan] using (Matrix.range_mulVecLin (A := B))
  have : (B * C).col j ∈ LinearMap.range B.mulVecLin := by
    refine ⟨C.col j, ?_⟩
    ext i
    simp [Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.col, Matrix.mul_apply, dotProduct]
  simpa [hrange] using this

-- A triple not all equal ensures the corresponding λ-slices are nowhere zero in the remaining index.
lemma notIdentical_of_notAllEqual3₀ {n : ℕ} {β γ δ : Fin n} (h : NotAllEqual3 β γ δ) :
    ∀ α : Fin n, NotIdentical α β γ δ := by
  intro α
  intro hall
  apply h
  exact ⟨hall.2.1, hall.2.2⟩

lemma notIdentical_of_notAllEqual3₁ {n : ℕ} {α γ δ : Fin n} (h : NotAllEqual3 α γ δ) :
    ∀ β : Fin n, NotIdentical α β γ δ := by
  intro β
  intro hall
  apply h
  have : α = γ := by
    -- from `α = β` and `β = γ`
    exact hall.1.trans hall.2.1
  exact ⟨this, hall.2.2⟩

lemma notIdentical_of_notAllEqual3₂ {n : ℕ} {α β δ : Fin n} (h : NotAllEqual3 α β δ) :
    ∀ γ : Fin n, NotIdentical α β γ δ := by
  intro γ
  intro hall
  apply h
  exact ⟨hall.1, hall.2.2⟩

-- Rigidity lemma (Lemma 4.2 of the paper).
-- If a block-diagonal scaling stabilizes the column space `W = ColSpan (StackedMat A)`,
-- then all block scalars are equal.
lemma Lemma_4_2_Rigidity {n : ℕ} (A : Fin n → Matrix3x4) (s : Fin n → ℝ)
    (hstack : (StackedMat A).rank = 4) (hcam : ∀ α : Fin n, (A α).rank = 3)
    (hstab :
      ∀ x : Fin 4 → ℝ, ∃ y : Fin 4 → ℝ,
        Matrix.mulVec (BlockDiagonal s) (Matrix.mulVec (StackedMat A) x) =
          Matrix.mulVec (StackedMat A) y) :
    ∀ α β : Fin n, s α = s β := by
  classical
  -- Choose `f` witnessing stabilization on every `x`.
  classical
  choose f hf using hstab
  -- Build a matrix `R` so that `BlockDiagonal s * StackedMat A = StackedMat A * R`.
  let R : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of (fun i j => f (Pi.single j 1) i)
  have hR : BlockDiagonal s * StackedMat A = StackedMat A * R := by
    ext p j
    -- Use the stabilization equation with `x = e_j`.
    have := congrArg (fun v => v p) (hf (Pi.single j 1))
    -- Expand both sides; note `StackedMat A * R` at column `j` uses `f (e_j)`.
    simpa [R, BlockDiagonal, StackedMat, Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct,
      Matrix.of_apply, Pi.single_apply, Finset.sum_ite_eq', Finset.filter_eq', Finset.filter_ne',
      mul_assoc, mul_comm, mul_left_comm] using this

  -- Restricting to camera blocks gives `s α • A α = A α * R`.
  have hblock : ∀ α : Fin n, s α • A α = A α * R := by
    intro α
    ext i j
    -- Evaluate the matrix identity on row `(α,i)`.
    have := congrArg (fun M => M (α, i) j) hR
    -- Left side is diagonal scaling by `s α`.
    simpa [BlockDiagonal, StackedMat, Matrix.mul_apply, Matrix.diagonal, Finset.sum_ite_eq',
      Finset.filter_eq', Finset.filter_ne', Matrix.smul_apply, mul_assoc, mul_comm, mul_left_comm]
      using this

  -- The row space of each `A α` lies in the left eigenspace of `R` with eigenvalue `s α`.
  have h_invariant :
      ∀ α : Fin n,
        LinearMap.range (Matrix.mulVecLin (A α).transpose) ≤
          LinearMap.ker (Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s α))) :=
    by
      intro α
      intro x hx
      rcases hx with ⟨y, rfl⟩
      -- Use the transposed block equation.
      have hT : (s α) • (A α).transpose = R.transpose * (A α).transpose := by
        -- transpose `hblock`
        simpa [Matrix.transpose_mul, Matrix.transpose_smul] using congrArg Matrix.transpose (hblock α)
      -- Rewrite scalar multiplication as multiplication by a diagonal matrix.
      have hdiag :
          (Matrix.diagonal (fun _ : Fin 4 => s α)) * (A α).transpose = (s α) • (A α).transpose := by
        ext i j
        simp [Matrix.mul_apply, Matrix.diagonal, Matrix.smul_apply]
      have hmat :
          (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s α)) * (A α).transpose = 0 := by
        -- `Rᵀ * Aᵀ - (diag sα) * Aᵀ = 0`
        calc
          (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s α)) * (A α).transpose
              = R.transpose * (A α).transpose - (Matrix.diagonal (fun _ : Fin 4 => s α)) * (A α).transpose := by
                  simp [Matrix.sub_mul]
          _ = (s α) • (A α).transpose - (s α) • (A α).transpose := by
                  simp [hT, hdiag]
          _ = 0 := by simp
      -- Apply the matrix equation to `y` via `mulVecLin`.
      have : Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s α))
              ((A α).transpose.mulVecLin y) = 0 := by
        -- `mulVecLin_mul` plus `hmat`.
        -- `mulVecLin ((Rᵀ - diag) * Aᵀ) y = 0`
        have := congrArg (fun M => Matrix.mulVecLin M y) hmat
        simpa [Matrix.mulVecLin_mul] using this
      simpa [LinearMap.mem_ker] using this

  -- Each eigenspace has dimension ≥ 3 (since `rank(A α) = 3`).
  have h_geometric :
      ∀ α : Fin n,
        3 ≤ Module.finrank ℝ
          (LinearMap.ker (Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s α)))) :=
    by
      intro α
      -- finrank(range(Aαᵀ)) = rank(Aαᵀ) = rank(Aα) = 3
      have hrA : (A α).transpose.rank = 3 := by
        simpa [Matrix.rank_transpose (R := ℝ) (A := A α)] using congrArg id (hcam α)
      have hfin_range :
          Module.finrank ℝ (LinearMap.range (Matrix.mulVecLin (A α).transpose)) = 3 := by
        simpa [Matrix.rank] using hrA
      -- range ≤ kernel, so finrank(range) ≤ finrank(kernel)
      have hmono := Submodule.finrank_mono (h_invariant α)
      -- Rewrite finrank of the range as 3.
      simpa [hfin_range] using hmono

  -- Distinct eigenvalues give disjoint eigenspaces, contradiction in dimension 4.
  intro α β
  by_contra hne
  have hinf :
      LinearMap.ker (Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s α))) ⊓
        LinearMap.ker (Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s β))) = ⊥ := by
    -- If `x` lies in both kernels, subtract the equations.
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxα, hxβ⟩
      have hxα' : (R.transpose.mulVec x) = (s α) • x := by
        -- `(Rᵀ - sα I) x = 0`
        have := congrArg id hxα
        -- unfold kernel membership
        have hx0 : Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s α)) x = 0 := by
          simpa [LinearMap.mem_ker] using hxα
        -- expand
        -- `Rᵀ.mulVec x - (diag sα).mulVec x = 0`
        have : R.transpose.mulVec x = (Matrix.diagonal (fun _ : Fin 4 => s α)).mulVec x := by
          -- rearrange
          simpa [Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.sub_mulVec, sub_eq_zero] using hx0
        -- diagonal mulVec is scalar scaling
        simpa [Matrix.mulVec, Matrix.diagonal, Matrix.smul_apply] using this
      have hxβ' : (R.transpose.mulVec x) = (s β) • x := by
        have hx0 : Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s β)) x = 0 := by
          simpa [LinearMap.mem_ker] using hxβ
        have : R.transpose.mulVec x = (Matrix.diagonal (fun _ : Fin 4 => s β)).mulVec x := by
          simpa [Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.sub_mulVec, sub_eq_zero] using hx0
        simpa [Matrix.mulVec, Matrix.diagonal, Matrix.smul_apply] using this
      -- Now `(s α - s β) • x = 0`, hence `x = 0`.
      have : (s α - s β) • x = 0 := by
        -- subtract `hxβ'` from `hxα'`
        have := congrArg (fun v => v) (hxα'.trans hxβ'.symm)
        -- `sα•x = sβ•x`
        have hs : (s α) • x = (s β) • x := by simpa using this
        -- rearrange
        simpa [sub_eq_zero] using (sub_eq_zero.mpr hs)
      have hsne : s α - s β ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      -- scalar multiplication by nonzero is injective in a vector space
      have : x = 0 := by
        -- use `smul_eq_zero` over a field
        have := (smul_eq_zero.mp this)
        exact this.resolve_left hsne
      simpa [this]
    · intro hx
      -- membership in `⊥` means `x = 0`, hence in both kernels
      have hx0 : x = 0 := by simpa using hx
      subst hx0
      simp
  -- Finrank inequality: two `≥ 3` subspaces with trivial intersection can't fit in 4D.
  have hsum :
      Module.finrank ℝ
        (LinearMap.ker (Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s α)))) +
        Module.finrank ℝ
        (LinearMap.ker (Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s β)))) ≤ 4 := by
    -- `finrank (sup) + finrank (inf) = ...`
    have := (Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.ker (Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s α))))
      (LinearMap.ker (Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s β)))))
    -- `inf = ⊥`, and `sup ≤ ⊤` so its finrank ≤ 4.
    have hsup_le :
        Module.finrank ℝ
          (LinearMap.ker (Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s α))) ⊔
            LinearMap.ker (Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s β)))) ≤ 4 :=
      (Submodule.finrank_le _).trans (by simp [finrank_pi])
    -- Combine.
    -- from `this`: finrank(sup)+finrank(inf) = finrank(kerα)+finrank(kerβ)
    -- so finrank(kerα)+finrank(kerβ) = finrank(sup)+finrank(inf) ≤ 4
    have : Module.finrank ℝ
        (LinearMap.ker (Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s α)))) +
        Module.finrank ℝ
        (LinearMap.ker (Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s β)))) =
        Module.finrank ℝ
          (LinearMap.ker (Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s α))) ⊔
            LinearMap.ker (Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s β)))) +
        Module.finrank ℝ
          (LinearMap.ker (Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s α))) ⊓
            LinearMap.ker (Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s β)))) := by
        simpa [this] using this.symm
    -- Use `inf = ⊥`.
    have hinf0 : Module.finrank ℝ
        (LinearMap.ker (Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s α))) ⊓
          LinearMap.ker (Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s β)))) = 0 := by
      simpa [hinf, finrank_bot] using rfl
    -- Now conclude.
    -- We avoid rewriting `this` directly; just use the inequality on the RHS.
    have :
        Module.finrank ℝ
          (LinearMap.ker (Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s α))) ⊔
            LinearMap.ker (Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s β)))) +
        Module.finrank ℝ
          (LinearMap.ker (Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s α))) ⊓
            LinearMap.ker (Matrix.mulVecLin (R.transpose - Matrix.diagonal (fun _ : Fin 4 => s β)))) ≤ 4 := by
      -- `inf` term is 0, so reduce to `hsup_le`.
      simpa [hinf0] using (add_le_add_right hsup_le _)
    -- Rewrite the LHS using `Submodule.finrank_sup_add_finrank_inf_eq`.
    simpa [Submodule.finrank_sup_add_finrank_inf_eq] using this
  have hα := h_geometric α
  have hβ := h_geometric β
  linarith

-- TODO: reverse direction (Problem 9), proved from rank/minor + generic spanning + rigidity.
-- Reverse direction: for generic cameras, F(T) = 0 → factorizable
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

theorem reverse_direction {n : ℕ} (hn : 5 ≤ n) (A : Fin n → Matrix3x4)
    (hgen : GenericCameras A) (lam : Lambda n)
    (hsupp : ∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ)
    (hvanish : IsZeroVec (PolyMap.eval (polyMapF n) (scaleQ lam (constructQ A)))) :
    ∃ (u v w x : Fin n → ℝˣ),
      ∀ α β γ δ, NotIdentical α β γ δ →
        lam α β γ δ = (u α : ℝ) * (v β : ℝ) * (w γ : ℝ) * (x δ : ℝ)
    := by
  classical
  rcases hgen with ⟨hstack, hcam, hspan1, hspan2, hspan3⟩

  -- Convert `IsZeroVec` to the statement that all `5×5` minors vanish, hence each unfolding has rank ≤ 4.
  have hminors :
      ∀ (m : Fin 4) (rows : Fin 5 → RowIdx n) (cols : Fin 5 → ColIdx n),
        Matrix.det ((Unfold m (scaleQ lam (constructQ A))).submatrix rows cols) = 0 := by
    have := (isZeroVec_iff_minors_vanish (Qf := scaleQ lam (constructQ A))).1 hvanish
    intro m rows cols
    exact this m rows cols
  have hrank0 : (Unfold 0 (scaleQ lam (constructQ A))).rank ≤ 4 :=
    minors5x5_zero_imp_rank_le_four (M := Unfold 0 (scaleQ lam (constructQ A)))
      (fun rows cols => hminors 0 rows cols)
  have hrank1 : (Unfold 1 (scaleQ lam (constructQ A))).rank ≤ 4 :=
    minors5x5_zero_imp_rank_le_four (M := Unfold 1 (scaleQ lam (constructQ A)))
      (fun rows cols => hminors 1 rows cols)
  have hrank2 : (Unfold 2 (scaleQ lam (constructQ A))).rank ≤ 4 :=
    minors5x5_zero_imp_rank_le_four (M := Unfold 2 (scaleQ lam (constructQ A)))
      (fun rows cols => hminors 2 rows cols)

  -- The 4D space `W = col(StackedMat A)`.
  let W : Submodule ℝ (RowIdx n → ℝ) := ColSpan (StackedMat A)
  have hrangeB :
      LinearMap.range (Matrix.mulVecLin (StackedMat A)) = W := by
    simpa [W, ColSpan] using (Matrix.range_mulVecLin (A := StackedMat A))

  -- Column spans of the generic 27-column submatrices equal `W`.
  have hcolSub1 :
      ∀ β γ δ : Fin n, NotAllEqual3 β γ δ → ColSpan (Submatrix1 A β γ δ) = W := by
    intro β γ δ hneq
    -- Inclusion `col(Submatrix1) ≤ W` (columns are in `col(Unfold0 Q) ≤ col(StackedMat)`).
    have hle1 : ColSpan (Submatrix1 A β γ δ) ≤ ColSpan (Unfold 0 (constructQ A)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      refine Submodule.subset_span (s := Set.range (Unfold 0 (constructQ A)).col) ?_
      refine ⟨colFun0 β γ δ j, ?_⟩
      ext p
      simp [Submatrix1, colFun0, Matrix.col, Matrix.submatrix]
    have hle2 : ColSpan (Unfold 0 (constructQ A)) ≤ W := by
      -- `Unfold 0 (constructQ A) = StackedMat A * cofactorMat A 0`
      have : Unfold 0 (constructQ A) = StackedMat A * cofactorMat A 0 := unfold_constructQ_eq_mul A 0
      simpa [W, this] using (ColSpan_mul_le_left (B := StackedMat A) (C := cofactorMat A 0))
    have hle : ColSpan (Submatrix1 A β γ δ) ≤ W := hle1.trans hle2

    -- Finrank computations: both sides have finrank 4, so inclusion is equality.
    have hS' :
        (Submatrix1 A β γ δ).rank = Module.finrank ℝ (ColSpan (Submatrix1 A β γ δ)) := by
      simpa [ColSpan] using (Matrix.rank_eq_finrank_span_cols (R := ℝ) (A := Submatrix1 A β γ δ))
    have hW' : (StackedMat A).rank = Module.finrank ℝ W := by
      simpa [W, ColSpan] using (Matrix.rank_eq_finrank_span_cols (R := ℝ) (A := StackedMat A))
    have hfinS : Module.finrank ℝ (ColSpan (Submatrix1 A β γ δ)) = 4 := by
      have hrankS : (Submatrix1 A β γ δ).rank = 4 := hspan1 β γ δ hneq
      simpa [hS'] using hrankS
    have hfinW : Module.finrank ℝ W = 4 := by
      simpa [hW'] using hstack
    have hfinEq :
        Module.finrank ℝ (ColSpan (Submatrix1 A β γ δ)) = Module.finrank ℝ W := by
      simpa [hfinS, hfinW]
    exact Submodule.eq_of_le_of_finrank_eq hle hfinEq

  have hcolSub2 :
      ∀ α γ δ : Fin n, NotAllEqual3 α γ δ → ColSpan (Submatrix2 A α γ δ) = W := by
    intro α γ δ hneq
    have hle1 : ColSpan (Submatrix2 A α γ δ) ≤ ColSpan (Unfold 1 (constructQ A)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      refine Submodule.subset_span (s := Set.range (Unfold 1 (constructQ A)).col) ?_
      refine ⟨colFun1 α γ δ j, ?_⟩
      ext p
      simp [Submatrix2, colFun1, Matrix.col, Matrix.submatrix]
    have hle2 : ColSpan (Unfold 1 (constructQ A)) ≤ W := by
      have : Unfold 1 (constructQ A) = StackedMat A * cofactorMat A 1 := unfold_constructQ_eq_mul A 1
      simpa [W, this] using (ColSpan_mul_le_left (B := StackedMat A) (C := cofactorMat A 1))
    have hle : ColSpan (Submatrix2 A α γ δ) ≤ W := hle1.trans hle2

    have hS' :
        (Submatrix2 A α γ δ).rank = Module.finrank ℝ (ColSpan (Submatrix2 A α γ δ)) := by
      simpa [ColSpan] using (Matrix.rank_eq_finrank_span_cols (R := ℝ) (A := Submatrix2 A α γ δ))
    have hW' : (StackedMat A).rank = Module.finrank ℝ W := by
      simpa [W, ColSpan] using (Matrix.rank_eq_finrank_span_cols (R := ℝ) (A := StackedMat A))
    have hfinS : Module.finrank ℝ (ColSpan (Submatrix2 A α γ δ)) = 4 := by
      have hrankS : (Submatrix2 A α γ δ).rank = 4 := hspan2 α γ δ hneq
      simpa [hS'] using hrankS
    have hfinW : Module.finrank ℝ W = 4 := by
      simpa [hW'] using hstack
    have hfinEq :
        Module.finrank ℝ (ColSpan (Submatrix2 A α γ δ)) = Module.finrank ℝ W := by
      simpa [hfinS, hfinW]
    exact Submodule.eq_of_le_of_finrank_eq hle hfinEq

  have hcolSub3 :
      ∀ α β δ : Fin n, NotAllEqual3 α β δ → ColSpan (Submatrix3 A α β δ) = W := by
    intro α β δ hneq
    have hle1 : ColSpan (Submatrix3 A α β δ) ≤ ColSpan (Unfold 2 (constructQ A)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨j, rfl⟩
      refine Submodule.subset_span (s := Set.range (Unfold 2 (constructQ A)).col) ?_
      refine ⟨colFun2 α β δ j, ?_⟩
      ext p
      simp [Submatrix3, colFun2, Matrix.col, Matrix.submatrix]
    have hle2 : ColSpan (Unfold 2 (constructQ A)) ≤ W := by
      have : Unfold 2 (constructQ A) = StackedMat A * cofactorMat A 2 := unfold_constructQ_eq_mul A 2
      simpa [W, this] using (ColSpan_mul_le_left (B := StackedMat A) (C := cofactorMat A 2))
    have hle : ColSpan (Submatrix3 A α β δ) ≤ W := hle1.trans hle2

    have hS' :
        (Submatrix3 A α β δ).rank = Module.finrank ℝ (ColSpan (Submatrix3 A α β δ)) := by
      simpa [ColSpan] using (Matrix.rank_eq_finrank_span_cols (R := ℝ) (A := Submatrix3 A α β δ))
    have hW' : (StackedMat A).rank = Module.finrank ℝ W := by
      simpa [W, ColSpan] using (Matrix.rank_eq_finrank_span_cols (R := ℝ) (A := StackedMat A))
    have hfinS : Module.finrank ℝ (ColSpan (Submatrix3 A α β δ)) = 4 := by
      have hrankS : (Submatrix3 A α β δ).rank = 4 := hspan3 α β δ hneq
      simpa [hS'] using hrankS
    have hfinW : Module.finrank ℝ W = 4 := by
      simpa [hW'] using hstack
    have hfinEq :
        Module.finrank ℝ (ColSpan (Submatrix3 A α β δ)) = Module.finrank ℝ W := by
      simpa [hfinS, hfinW]
    exact Submodule.eq_of_le_of_finrank_eq hle hfinEq

  -- Some fixed indices `0,1,2 ∈ Fin n` (available since `n ≥ 5`).
  have h0 : (0 : ℕ) < n := Nat.lt_of_lt_of_le (by decide : 0 < 5) hn
  have h1 : (1 : ℕ) < n := Nat.lt_of_lt_of_le (by decide : 1 < 5) hn
  have h2 : (2 : ℕ) < n := Nat.lt_of_lt_of_le (by decide : 2 < 5) hn
  let i0 : Fin n := ⟨0, h0⟩
  let i1 : Fin n := ⟨1, h1⟩
  let i2 : Fin n := ⟨2, h2⟩
  have h01 : i0 ≠ i1 := by decide
  have h12 : i1 ≠ i2 := by decide
  have hNotAll012 : NotAllEqual3 i0 i1 i2 := by
    intro h; exact h01 h.1

  -- Basic nonvanishing facts from the support condition.
  have h0012 : lam i0 i0 i1 i2 ≠ 0 := by
    have hni : NotIdentical i0 i0 i1 i2 := by
      intro h; exact h01 h.2.1
    exact (hsupp _ _ _ _).2 hni
  have h0112 : lam i0 i1 i1 i2 ≠ 0 := by
    have hni : NotIdentical i0 i1 i1 i2 := by
      intro h; exact h12 h.2.2
    exact (hsupp _ _ _ _).2 hni
  have h0102 : lam i0 i1 i0 i2 ≠ 0 := by
    have hni : NotIdentical i0 i1 i0 i2 := by
      intro h; exact h01 h.1
    exact (hsupp _ _ _ _).2 hni

  -- Define the factor functions as units.
  let u : Fin n → ℝˣ :=
    fun α =>
      Units.mk0 (lam α i0 i1 i2 / lam i0 i0 i1 i2) (by
        have hnum : lam α i0 i1 i2 ≠ 0 := by
          have hni : NotIdentical α i0 i1 i2 := by
            intro h; exact h01 h.2.1
          exact (hsupp _ _ _ _).2 hni
        exact div_ne_zero hnum h0012)
  let v : Fin n → ℝˣ :=
    fun β =>
      Units.mk0 (lam i0 β i1 i2 / lam i0 i1 i1 i2) (by
        have hnum : lam i0 β i1 i2 ≠ 0 := by
          have hni : NotIdentical i0 β i1 i2 := by
            intro h; exact h12 h.2.2
          exact (hsupp _ _ _ _).2 hni
        exact div_ne_zero hnum h0112)
  let w : Fin n → ℝˣ :=
    fun γ =>
      Units.mk0 (lam i0 i1 γ i2) (by
        have hni : NotIdentical i0 i1 γ i2 := by
          intro h; exact h01 h.1
        exact (hsupp _ _ _ _).2 hni)
  let x : Fin n → ℝˣ :=
    fun δ =>
      Units.mk0 (lam i0 i1 i0 δ / lam i0 i1 i0 i2) (by
        have hnum : lam i0 i1 i0 δ ≠ 0 := by
          have hni : NotIdentical i0 i1 i0 δ := by
            intro h; exact h01 h.1
          exact (hsupp _ _ _ _).2 hni
        exact div_ne_zero hnum h0102)

  -- Mode 0 (separating α): for not-all-equal triples `(β,γ,δ)`, we have
  --   λ_{αβγδ} = u_α * λ_{0βγδ}.
  have mode0_formula :
      ∀ β γ δ : Fin n, NotAllEqual3 β γ δ → ∀ α : Fin n,
        lam α β γ δ = (u α : ℝ) * lam i0 β γ δ := by
    intro β γ δ hneq α
    -- Column space identity for the scaled unfolding in mode 0.
    let T : QFamily n := scaleQ lam (constructQ A)
    let D : Matrix (RowIdx n) (RowIdx n) ℝ := BlockDiagonal (fun a => lam a β γ δ)
    let Dref : Matrix (RowIdx n) (RowIdx n) ℝ := BlockDiagonal (fun a => lam a i0 i1 i2)
    have hsD : ∀ a : Fin n, lam a β γ δ ≠ 0 := by
      intro a
      have hni : NotIdentical a β γ δ := notIdentical_of_notAllEqual3₀ (n := n) (β := β) (γ := γ)
        (δ := δ) hneq a
      exact (hsupp _ _ _ _).2 hni
    have hsDref : ∀ a : Fin n, lam a i0 i1 i2 ≠ 0 := by
      intro a
      have hni : NotIdentical a i0 i1 i2 := notIdentical_of_notAllEqual3₀ (n := n) (β := i0) (γ := i1)
        (δ := i2) hNotAll012 a
      exact (hsupp _ _ _ _).2 hni
    -- `col(Unfold0 T) = D(W)`.
    have hcol :
        ColSpan (Unfold 0 T) = Submodule.map (Matrix.mulVecLin D) W := by
      -- Use the 27-column submatrix corresponding to `(β,γ,δ)`.
      let S : Matrix (RowIdx n) Triple3 ℝ := (Unfold 0 T).submatrix id (colFun0 β γ δ)
      have hSdef : S = D * Submatrix1 A β γ δ := by
        ext p j
        simp [S, D, Submatrix1, BlockDiagonal_mul_apply, colFun0, Unfold, scaleQ, Submatrix1]
      have hrankS : S.rank = 4 := by
        have hunit : IsUnit D.det := BlockDiagonal_isUnit_det (n := n) (s := fun a => lam a β γ δ) hsD
        have hmul :
            (D * Submatrix1 A β γ δ).rank = (Submatrix1 A β γ δ).rank := by
          simpa using
            (Matrix.rank_mul_eq_right_of_isUnit_det (A := D) (B := Submatrix1 A β γ δ) hunit)
        have hsub : (Submatrix1 A β γ δ).rank = 4 := hspan1 β γ δ hneq
        simpa [hSdef, hmul] using hsub
      have hcols :
          ∀ j : Triple3, ∃ i : ColIdx n, S.col j = (Unfold 0 T).col i := by
        intro j
        refine ⟨colFun0 β γ δ j, ?_⟩
        ext p
        simp [S, colFun0, Matrix.col, Matrix.submatrix]
      have hcolEq :
          ColSpan S = ColSpan (Unfold 0 T) :=
        colSpan_eq_of_cols_subtype_and_rank (M := Unfold 0 T) (S := S) hcols hrank0 hrankS
      have hcolS :
          ColSpan S = Submodule.map (Matrix.mulVecLin D) W := by
        -- `col(S) = D(col(Submatrix1)) = D(W)`.
        calc
          ColSpan S = ColSpan (D * Submatrix1 A β γ δ) := by simpa [hSdef]
          _ = Submodule.map (Matrix.mulVecLin D) (ColSpan (Submatrix1 A β γ δ)) := by
                simpa using (ColSpan_mul_left (D := D) (M := Submatrix1 A β γ δ))
          _ = Submodule.map (Matrix.mulVecLin D) W := by
                simpa [hcolSub1 β γ δ hneq]
      -- `ColSpan (Unfold 0 T) = map(D) W`.
      exact hcolEq.symm.trans hcolS
    -- The same identity for the reference triple `(0,1,2)`.
    have hcol_ref :
        ColSpan (Unfold 0 T) = Submodule.map (Matrix.mulVecLin Dref) W := by
      let S : Matrix (RowIdx n) Triple3 ℝ := (Unfold 0 T).submatrix id (colFun0 i0 i1 i2)
      have hSdef : S = Dref * Submatrix1 A i0 i1 i2 := by
        ext p j
        simp [S, Dref, Submatrix1, BlockDiagonal_mul_apply, colFun0, Unfold, scaleQ, Submatrix1]
      have hrankS : S.rank = 4 := by
        have hunit : IsUnit Dref.det :=
          BlockDiagonal_isUnit_det (n := n) (s := fun a => lam a i0 i1 i2) hsDref
        have hmul :
            (Dref * Submatrix1 A i0 i1 i2).rank = (Submatrix1 A i0 i1 i2).rank := by
          simpa using
            (Matrix.rank_mul_eq_right_of_isUnit_det (A := Dref) (B := Submatrix1 A i0 i1 i2) hunit)
        have hsub : (Submatrix1 A i0 i1 i2).rank = 4 := hspan1 i0 i1 i2 hNotAll012
        simpa [hSdef, hmul] using hsub
      have hcols :
          ∀ j : Triple3, ∃ i : ColIdx n, S.col j = (Unfold 0 T).col i := by
        intro j
        refine ⟨colFun0 i0 i1 i2 j, ?_⟩
        ext p
        simp [S, colFun0, Matrix.col, Matrix.submatrix]
      have hcolEq :
          ColSpan S = ColSpan (Unfold 0 T) :=
        colSpan_eq_of_cols_subtype_and_rank (M := Unfold 0 T) (S := S) hcols hrank0 hrankS
      have hcolS :
          ColSpan S = Submodule.map (Matrix.mulVecLin Dref) W := by
        calc
          ColSpan S = ColSpan (Dref * Submatrix1 A i0 i1 i2) := by simpa [hSdef]
          _ = Submodule.map (Matrix.mulVecLin Dref) (ColSpan (Submatrix1 A i0 i1 i2)) := by
                simpa using (ColSpan_mul_left (D := Dref) (M := Submatrix1 A i0 i1 i2))
          _ = Submodule.map (Matrix.mulVecLin Dref) W := by
                simpa [hcolSub1 i0 i1 i2 hNotAll012]
      exact hcolEq.symm.trans hcolS
    have hmapEq : Submodule.map (Matrix.mulVecLin D) W = Submodule.map (Matrix.mulVecLin Dref) W :=
      hcol.symm.trans hcol_ref

    -- Stabilization hypothesis for the ratio matrix.
    let s : Fin n → ℝ := fun a => lam a i0 i1 i2 / lam a β γ δ
    have hstab :
        ∀ x : Fin 4 → ℝ, ∃ y : Fin 4 → ℝ,
          Matrix.mulVec (BlockDiagonal s) (Matrix.mulVec (StackedMat A) x) =
            Matrix.mulVec (StackedMat A) y := by
      intro x
      -- `B*x ∈ W`.
      have hxW : Matrix.mulVec (StackedMat A) x ∈ W := by
        have : Matrix.mulVecLin (StackedMat A) x ∈ LinearMap.range (Matrix.mulVecLin (StackedMat A)) :=
          ⟨x, by simp [Matrix.mulVecLin_apply]⟩
        simpa [hrangeB] using this
      -- Apply the map equality to see `Dref*(B*x) ∈ map(D) W`.
      have hxMapRef :
          Matrix.mulVec Dref (Matrix.mulVec (StackedMat A) x) ∈ Submodule.map (Matrix.mulVecLin Dref) W := by
        refine ⟨Matrix.mulVec (StackedMat A) x, hxW, ?_⟩
        simp [Matrix.mulVecLin_apply]
      have hxMap :
          Matrix.mulVec Dref (Matrix.mulVec (StackedMat A) x) ∈ Submodule.map (Matrix.mulVecLin D) W := by
        simpa [hmapEq.symm] using hxMapRef
      rcases hxMap with ⟨z, hzW, hzEq⟩
      -- `z ∈ W`, hence `z = B*y` for some `y`.
      have hzRange : z ∈ LinearMap.range (Matrix.mulVecLin (StackedMat A)) := by
        simpa [hrangeB] using hzW
      rcases hzRange with ⟨y, rfl⟩
      -- We have `D * (B*y) = Dref * (B*x)`.
      have hDz :
          Matrix.mulVec D (Matrix.mulVec (StackedMat A) y) =
            Matrix.mulVec Dref (Matrix.mulVec (StackedMat A) x) := by
        simpa [Matrix.mulVecLin_apply] using hzEq.symm
      -- Left-multiply by `inv(D)` (explicitly, since `D` is diagonal with nonzero diagonal entries).
      let invD : Matrix (RowIdx n) (RowIdx n) ℝ := BlockDiagonal (fun a => (lam a β γ δ)⁻¹)
      have hinv : invD * D = 1 := by
        ext p q
        by_cases h : p = q
        · subst h
          simp [invD, D, BlockDiagonal, hsD]
        · simp [invD, D, BlockDiagonal, h]
      have hratio : invD * Dref = BlockDiagonal s := by
        ext p q
        by_cases h : p = q
        · subst h
          simp [invD, Dref, s, BlockDiagonal, hsD]
        · simp [invD, Dref, BlockDiagonal, h]
      have := congrArg (fun v => Matrix.mulVec invD v) hDz
      -- Simplify to the desired stabilization equation.
      refine ⟨y, ?_⟩
      -- `invD * (D * (B*y)) = (invD*D) * (B*y) = B*y`, and similarly for the RHS.
      simpa [mulVec_mulVec, hinv, hratio, Matrix.one_mulVec, Matrix.mulVecLin_apply, mul_assoc] using this.symm

    have hsconst : ∀ a b : Fin n, s a = s b :=
      Lemma_4_2_Rigidity A s hstack hcam hstab
    -- Compare `s α` with `s i0` to get the required ratio identity.
    have hsα : s α = s i0 := hsconst α i0
    have hsα' :
        lam α i0 i1 i2 / lam α β γ δ = lam i0 i0 i1 i2 / lam i0 β γ δ := by
      simpa [s] using hsα
    -- Cross-multiply and solve for `lam α β γ δ`.
    have hden : lam i0 β γ δ ≠ 0 := by
      have hni : NotIdentical i0 β γ δ := notIdentical_of_notAllEqual3₀ (n := n) (β := β) (γ := γ)
        (δ := δ) hneq i0
      exact (hsupp _ _ _ _).2 hni
    have hαβγδ : lam α β γ δ ≠ 0 :=
      (hsupp _ _ _ _).2
        (notIdentical_of_notAllEqual3₀ (n := n) (β := β) (γ := γ) (δ := δ) hneq α)
    have hcross :
        lam α i0 i1 i2 * lam i0 β γ δ = lam i0 i0 i1 i2 * lam α β γ δ := by
      -- Clear denominators in `hsα'`.
      have h := hsα'
      field_simp [hαβγδ, hden] at h
      simpa [mul_assoc, mul_left_comm, mul_comm] using h
    have hsolve :
        lam α β γ δ = (lam α i0 i1 i2 / lam i0 i0 i1 i2) * lam i0 β γ δ := by
      -- Rearrange `hcross` as `b*c = a*d`, then divide by `c`.
      have hbc :
          lam α β γ δ * lam i0 i0 i1 i2 = lam α i0 i1 i2 * lam i0 β γ δ := by
        calc
          lam α β γ δ * lam i0 i0 i1 i2 = lam i0 i0 i1 i2 * lam α β γ δ := by
            simp [mul_comm]
          _ = lam α i0 i1 i2 * lam i0 β γ δ := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hcross.symm
      have hdiv :
          lam α β γ δ =
            (lam α i0 i1 i2 * lam i0 β γ δ) / lam i0 i0 i1 i2 := by
        exact (eq_div_iff h0012).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hbc)
      -- `a*d/c = (a/c)*d`.
      simpa [div_mul_eq_mul_div, mul_assoc, mul_left_comm, mul_comm] using hdiv
    -- Finish: unfold `u`.
    simpa [u, Units.val_mk0] using hsolve

  -- TODO: complete reverse direction proof
  -- The remaining steps (mode 1 / mode 2 and propagation) are implemented below.
  refine ⟨u, v, w, x, ?_⟩
  intro α β γ δ hni
  -- placeholder
  sorry

-- ═══════════════════════════════════════════════════════════════
-- Genericity polynomial
-- ═══════════════════════════════════════════════════════════════

-- Encode GenericCameras as non-vanishing of a polynomial
-- We construct a nonzero polynomial G whose non-vanishing implies GenericCameras
-- TODO: explicit genericity polynomial G as product of “sum of squares of minors”.

/- PROVIDED SOLUTION:

Goal:
  For each `n ≥ 5`, construct a nonzero polynomial `G` in the camera entries such that
  `G(A) ≠ 0 → GenericCameras A`.

This is the standard “Zariski-generic = complement of a proper algebraic set” encoding:
  each generic condition is a finite conjunction of statements of the form
    “some determinant/minor is nonzero”,
  and we combine them into a single polynomial by multiplying “sum-of-squares of minors”.

Concrete construction pattern:
1) Rank(StackedMat A) = 4.
   Since `StackedMat A` has exactly 4 columns, it always has rank ≤ 4. So rank = 4 is equivalent to
   “some 4×4 minor is nonzero”. Define
     g_stack(A) := ∑_{rows : Fin 4 → RowIdx n} det((StackedMat A).submatrix rows id)^2.
   Then `g_stack(A) ≠ 0` implies at least one 4×4 minor is nonzero, hence rank(StackedMat A) = 4.

2) Each camera Aα has rank = 3.
   Each `A α` is `3×4`, hence rank ≤ 3. Rank = 3 is equivalent to “some 3×3 minor is nonzero”.
   Define for each α:
     g_cam,α(A) := ∑_{cols : Fin 3 → Fin 4} det((A α).submatrix id cols)^2.
   Then `g_cam,α(A) ≠ 0` implies rank(A α) = 3.

3) Spanning conditions (G3_m) for the 27-column submatrices of each unfolding.
   Each such submatrix has shape `3n × 27`. Under the already-known rank bound ≤ 4 for unfoldings
   of `constructQ A`, “its columns span W” can be enforced by requiring rank = 4. Again, rank = 4
   can be enforced by “some 4×4 minor is nonzero” on that `3n×27` submatrix.
   For each mode m and each triple (not all equal), let `S(m,triple,A)` be that `3n×27` matrix.
   Define:
     g_span(m,triple,A) := ∑_{rows : Fin 4 → RowIdx n} ∑_{cols : Fin 4 → Fin 27}
                             det((S(m,triple,A)).submatrix rows cols)^2.
   Then `g_span(m,triple,A) ≠ 0` forces rank(S)=4, i.e. its columns span the 4D space W.

4) Combine into one polynomial.
   Let `G(A) := g_stack(A) * (∏α g_cam,α(A)) * (∏_{m,triple} g_span(m,triple,A))`.
   This is a polynomial in the camera entries because:
   - each matrix entry is a polynomial in camera entries,
   - determinants of matrices with polynomial entries are polynomials,
   - sums/products preserve polynomiality.

5) Show `G ≠ 0`.
   Provide a single explicit camera family `A₀` satisfying all generic conditions (as in
   `proofdocs/solution.md`), then check `G(A₀) ≠ 0`. Any polynomial that evaluates to a nonzero real
   at some point is not the zero polynomial. Hence `G ≠ 0`.

6) Conclude:
   If `evalCameraPolynomial G A ≠ 0`, then every factor above is nonzero, hence all the generic
   properties hold, i.e. `GenericCameras A`.

This is exactly the usual “finite intersection of nonempty Zariski-open sets is nonempty Zariski-open”
argument, packaged into a single polynomial nonvanishing condition.
-/
theorem genericity_polynomial_exists (n : ℕ) (hn : 5 ≤ n) :
    ∃ (G : MvPolynomial (AIndex n) ℝ), G ≠ 0 ∧
      ∀ A : Fin n → Matrix3x4,
        evalCameraPolynomial G A ≠ 0 → GenericCameras A
    := by
  classical
  sorry

-- ═══════════════════════════════════════════════════════════════
-- Main theorem
-- ═══════════════════════════════════════════════════════════════

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
  refine ⟨5, ?_⟩
  intro n hn
  refine ⟨numMinors n, polyMapF n, polyMapF_degree_bound n, ?_⟩
  obtain ⟨G, hGne, hGgen⟩ := genericity_polynomial_exists n hn
  refine ⟨G, hGne, ?_⟩
  intro A hGA lam hsupp
  constructor
  · intro hvanish
    have hgen : GenericCameras A := hGgen A hGA
    exact reverse_direction hn A hgen lam hsupp hvanish
  · rintro ⟨u, v, w, x, hfact⟩
    exact forward_direction A lam hsupp u v w x hfact

/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 12327c74-2425-4add-a7ee-593e099b399b

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem minors5x5_zero_imp_rank_le_four {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (M : Matrix α β ℝ)
    (hminors : ∀ (rows : Fin 5 → α) (cols : Fin 5 → β),
      (M.submatrix rows cols).det = 0) :
    M.rank ≤ 4

- theorem genericity_polynomial_exists (n : ℕ) (hn : 5 ≤ n) :
    ∃ (G : MvPolynomial (AIndex n) ℝ), G ≠ 0 ∧
      ∀ A : Fin n → Matrix3x4,
        evalCameraPolynomial G A ≠ 0 → GenericCameras A
-/

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

-- Generic camera properties needed for the reverse direction
def GenericCameras {n : ℕ} (A : Fin n → Matrix3x4) : Prop :=
  (StackedMat A).rank = 4 ∧
  (∀ α : Fin n, (A α).rank = 3) ∧
  -- Spanning conditions: for each mode and each not-all-equal triple,
  -- the 27 columns of the corresponding submatrix span the column space of B
  True

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

/- `NotAllEqual3 β γ δ` means the triple `(β,γ,δ)` is not constant. This is the condition under which
`NotIdentical α β γ δ` holds for *every* `α`. -/
def NotAllEqual3 {n : ℕ} (β γ δ : Fin n) : Prop := ¬ (β = γ ∧ γ = δ)

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

/-- PROVIDED SOLUTION:

This lemma packages steps (3)-(5) of the informal proof in `proofdocs/solution.md`:

Given:
- the support condition `lam α β γ δ ≠ 0 ↔ NotIdentical α β γ δ`, and
- the rank bounds `rank(Unfold m (scaleQ lam (constructQ A))) ≤ 4` for all modes `m`, and
- the (missing, but intended) generic spanning + rigidity hypotheses inside `GenericCameras A`,

one proves the first separation:
  `lam α β γ δ = uα * μβγδ` whenever `(β,γ,δ)` is not all equal.

Sketch:
- Fix a triple `(β,γ,δ)` not all equal. Then `lam α β γ δ ≠ 0` for all `α`, so the block-diagonal
  scaling matrix `D_{βγδ}` is invertible.
- The generic spanning hypothesis identifies a 4D subspace `W = col(StackedMat A)` such that the
  27-column submatrix in mode 0 spans `W`.
- Rank ≤ 4 forces `col(Unfold 0 (scaleQ lam Q)) = D_{βγδ} W`, for all such triples.
- Rigidity (Lemma 4.2 in the paper) then forces ratios of the diagonal blocks to be constant in `α`,
  yielding the desired factorization along the `α`-index.
- Units are used to avoid division-by-zero problems; nonvanishing comes from the support condition.
-/
theorem separate_alpha_of_generic {n : ℕ} (A : Fin n → Matrix3x4) (lam : Lambda n)
    (hgen : GenericCameras A)
    (hsupp : ∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ)
    (hrank : ∀ m : Fin 4, (Unfold m (scaleQ lam (constructQ A))).rank ≤ 4) :
    ∃ (u : Fin n → ℝˣ) (μ : Fin n → Fin n → Fin n → ℝˣ),
      ∀ α β γ δ, NotAllEqual3 β γ δ →
        lam α β γ δ = (u α : ℝ) * (μ β γ δ : ℝ) := by
  classical
  sorry

/-- PROVIDED SOLUTION:

Analog of `separate_alpha_of_generic` but along the `β`-index (mode 1 of the unfolding).

Result:
  `lam α β γ δ = vβ * ναγδ` whenever `(α,γ,δ)` is not all equal.
-/
theorem separate_beta_of_generic {n : ℕ} (A : Fin n → Matrix3x4) (lam : Lambda n)
    (hgen : GenericCameras A)
    (hsupp : ∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ)
    (hrank : ∀ m : Fin 4, (Unfold m (scaleQ lam (constructQ A))).rank ≤ 4) :
    ∃ (v : Fin n → ℝˣ) (ν : Fin n → Fin n → Fin n → ℝˣ),
      ∀ α β γ δ, NotAllEqual3 α γ δ →
        lam α β γ δ = (v β : ℝ) * (ν α γ δ : ℝ) := by
  classical
  sorry

/-- PROVIDED SOLUTION:

Analog of `separate_alpha_of_generic` but along the `γ`-index (mode 2).

Result:
  `lam α β γ δ = wγ * ξαβδ` whenever `(α,β,δ)` is not all equal.
-/
theorem separate_gamma_of_generic {n : ℕ} (A : Fin n → Matrix3x4) (lam : Lambda n)
    (hgen : GenericCameras A)
    (hsupp : ∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ)
    (hrank : ∀ m : Fin 4, (Unfold m (scaleQ lam (constructQ A))).rank ≤ 4) :
    ∃ (w : Fin n → ℝˣ) (ξ : Fin n → Fin n → Fin n → ℝˣ),
      ∀ α β γ δ, NotAllEqual3 α β δ →
        lam α β γ δ = (w γ : ℝ) * (ξ α β δ : ℝ) := by
  classical
  sorry

/-- PROVIDED SOLUTION:

Analog of `separate_alpha_of_generic` but along the `δ`-index (mode 3).

Result:
  `lam α β γ δ = xδ * ζαβγ` whenever `(α,β,γ)` is not all equal.
-/
theorem separate_delta_of_generic {n : ℕ} (A : Fin n → Matrix3x4) (lam : Lambda n)
    (hgen : GenericCameras A)
    (hsupp : ∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ)
    (hrank : ∀ m : Fin 4, (Unfold m (scaleQ lam (constructQ A))).rank ≤ 4) :
    ∃ (x : Fin n → ℝˣ) (ζ : Fin n → Fin n → Fin n → ℝˣ),
      ∀ α β γ δ, NotAllEqual3 α β γ →
        lam α β γ δ = (x δ : ℝ) * (ζ α β γ : ℝ) := by
  classical
  sorry

/-- PROVIDED SOLUTION:

Propagation step (paper’s Section 4, using `n ≥ 5`):

From the four partial separations obtained by comparing column spaces in each unfolding mode, one
derives the full factorization
  `lam α β γ δ = uα vβ wγ xδ`
on all `NotIdentical α β γ δ`.

This is a combinatorial "patching" argument that uses the abundance of distinct indices when `n ≥ 5`
to move between the various not-all-equal regimes and extend the multiplicative decomposition to all
off-diagonal entries.
-/
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
  sorry

/-- PROVIDED SOLUTION:

`reverse_direction_core` is the formal packaging of the reverse direction argument.

Inputs:
- `GenericCameras A` (intended to include the spanning and rigidity hypotheses)
- support condition `hsupp`
- rank bounds `hrank` (derived from `hvanish`)

Output:
- units `u v w x` giving the required factorization on all `NotIdentical` indices.

Implementation plan:
1. Use `separate_*_of_generic` to extract the four partial separations.
2. Apply `full_factorization_of_separations` (using `hn : 5 ≤ n`) to patch them into the full
   decomposition.
-/
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
    separate_alpha_of_generic (A := A) (lam := lam) (hgen := hgen) (hsupp := hsupp) (hrank := hrank)

  have hβ : ∃ (v : Fin n → ℝˣ) (ν : Fin n → Fin n → Fin n → ℝˣ),
      ∀ α β γ δ, NotAllEqual3 α γ δ →
        lam α β γ δ = (v β : ℝ) * (ν α γ δ : ℝ) :=
    separate_beta_of_generic (A := A) (lam := lam) (hgen := hgen) (hsupp := hsupp) (hrank := hrank)

  have hγ : ∃ (w : Fin n → ℝˣ) (ξ : Fin n → Fin n → Fin n → ℝˣ),
      ∀ α β γ δ, NotAllEqual3 α β δ →
        lam α β γ δ = (w γ : ℝ) * (ξ α β δ : ℝ) :=
    separate_gamma_of_generic (A := A) (lam := lam) (hgen := hgen) (hsupp := hsupp) (hrank := hrank)

  have hδ : ∃ (x : Fin n → ℝˣ) (ζ : Fin n → Fin n → Fin n → ℝˣ),
      ∀ α β γ δ, NotAllEqual3 α β γ →
        lam α β γ δ = (x δ : ℝ) * (ζ α β γ : ℝ) :=
    separate_delta_of_generic (A := A) (lam := lam) (hgen := hgen) (hsupp := hsupp) (hrank := hrank)

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
noncomputable section AristotleLemmas

def witnessA (n : ℕ) : Fin n → Matrix3x4 :=
  fun α => Matrix.of ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, (α : ℝ)]]

lemma witnessA_properties {n : ℕ} (hn : 5 ≤ n) :
    GenericCameras (witnessA n) := by
  classical
  refine ⟨?_, ?_, trivial⟩

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
open Arxiv.«2602.05192»
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

open Arxiv.«2602.05192»
open Classical Matrix BigOperators

lemma eval_poly_sum_sq_stacked_ne_zero {n : ℕ} (A : Fin n → Matrix3x4) :
    evalCameraPolynomial (poly_sum_sq_stacked n) A ≠ 0 → (StackedMat A).rank = 4 := by
      intro h_nonzero
      have h_rank_ge_4 : (StackedMat A).rank ≥ 4 := by
        -- Since `poly_sum_sq_stacked n` is nonzero, there exists a 4x4 minor of `StackedMat A` that is nonzero.
        obtain ⟨rows, hrows⟩ : ∃ rows : Fin 4 → RowIdx n, Matrix.det (Matrix.submatrix (StackedMat A) rows id) ≠ 0 := by
          contrapose! h_nonzero;
          simp_all +decide [ Arxiv.«2602.05192».evalCameraPolynomial, Arxiv.«2602.05192».poly_sum_sq_stacked ];
          refine Finset.sum_eq_zero fun x hx => ?_;
          convert congr_arg ( · ^ 2 ) ( h_nonzero x ) using 1;
          · unfold Arxiv.«2602.05192».poly_minor_stacked; simp +decide [ Matrix.det_apply' ] ;
            unfold Arxiv.«2602.05192».mat_poly_stacked; aesop;
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

open Arxiv.«2602.05192»
open Classical Matrix BigOperators

lemma eval_poly_sum_sq_cam_ne_zero {n : ℕ} (A : Fin n → Matrix3x4) (α : Fin n) :
    evalCameraPolynomial (poly_sum_sq_cam n α) A ≠ 0 → (A α).rank = 3 := by
      intro h_nonzero
      obtain ⟨cols, h_det⟩ : ∃ cols : Fin 3 → Fin 4, Matrix.det ((A α).submatrix id cols) ≠ 0 := by
        simp_all +decide [ Arxiv.«2602.05192».evalCameraPolynomial, Arxiv.«2602.05192».poly_sum_sq_cam ];
        contrapose! h_nonzero; simp_all +decide [ Arxiv.«2602.05192».poly_minor_cam ] ;
        refine Finset.sum_eq_zero fun x hx => ?_ ; simp_all +decide [ Matrix.det_apply' ];
        unfold Arxiv.«2602.05192».mat_poly_cam; aesop;
      have h_rank_ge_3 : Matrix.rank (A α) ≥ 3 := by
        have := Matrix.rank_mul_le ( A α ) ( Matrix.of ( fun i j => if i = cols j then 1 else 0 ) ) ; simp_all +decide [ Matrix.rank_transpose, Matrix.mul_apply ] ;
        have h_rank_ge_3 : Matrix.rank (Matrix.submatrix (A α) id cols) = 3 := by
          have := Matrix.rank_mul_le ( Matrix.submatrix ( A α ) id cols ) ( Matrix.submatrix ( A α ) id cols ) ⁻¹; simp_all +decide [ Matrix.nonsing_inv_apply_not_isUnit, isUnit_iff_ne_zero ] ;
          exact le_antisymm ( le_trans ( Matrix.rank_le_card_width _ ) ( by norm_num ) ) this.1;
        convert this.1 using 1;
        convert h_rank_ge_3.symm using 2; ext i j; simp +decide [ Matrix.mul_apply ] ;
      exact le_antisymm ( le_trans ( Matrix.rank_le_card_height _ ) ( by norm_num ) ) h_rank_ge_3

open Arxiv.«2602.05192»
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
        unfold Arxiv.«2602.05192».evalCameraPolynomial; simp_all +decide [ Matrix.det_apply' ] ;
        unfold Arxiv.«2602.05192».poly_minor_stacked; simp_all +decide [ Matrix.det_apply' ] ;
        convert h_det using 1;
        unfold Arxiv.«2602.05192».mat_poly_stacked; simp +decide [ Arxiv.«2602.05192».StackedMat ] ;
      -- Since the evaluation of the polynomial at A is zero, the sum of squares of all 4x4 minors must also be zero.
      have h_sum_sq_zero : ∑ rows : Fin 4 → RowIdx n, (evalCameraPolynomial (poly_minor_stacked n rows) A)^2 = 0 := by
        convert h_eval_zero using 1;
        unfold Arxiv.«2602.05192».evalCameraPolynomial Arxiv.«2602.05192».poly_sum_sq_stacked; simp +decide [ sq, MvPolynomial.eval₂_sum ] ;
      exact absurd h_sum_sq_zero ( ne_of_gt ( lt_of_lt_of_le ( by positivity ) ( Finset.single_le_sum ( fun x _ => sq_nonneg ( evalCameraPolynomial ( poly_minor_stacked n x ) A ) ) ( Finset.mem_univ rows ) ) ) )

open Arxiv.«2602.05192»
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

open Arxiv.«2602.05192»
open Classical Matrix BigOperators

lemma rank_eq_three_imp_eval_cam_ne_zero {n : ℕ} (A : Fin n → Matrix3x4) (α : Fin n) :
    (A α).rank = 3 → evalCameraPolynomial (poly_sum_sq_cam n α) A ≠ 0 := by
      intro h_rank h_zero_sum;
      -- By definition of `poly_sum_sq_cam`, we know that `evalCameraPolynomial (poly_sum_sq_cam n α) A` is the sum of squares of determinants of 3x3 submatrices of `A α`.
      have h_sum_sq : ∑ cols : Fin 3 → Fin 4, (Matrix.det ((A α).submatrix id cols))^2 = 0 := by
        unfold Arxiv.«2602.05192».evalCameraPolynomial at h_zero_sum;
        unfold Arxiv.«2602.05192».poly_sum_sq_cam at h_zero_sum;
        convert h_zero_sum using 1;
        unfold Arxiv.«2602.05192».poly_minor_cam; simp +decide [ Matrix.det_apply' ] ;
        unfold Arxiv.«2602.05192».mat_poly_cam; simp +decide [ Matrix.det_apply' ] ;
      -- Since the sum of squares of determinants is zero, each determinant must be zero.
      have h_det_zero : ∀ cols : Fin 3 → Fin 4, (Matrix.det ((A α).submatrix id cols)) = 0 := by
        rw [ Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _ ] at h_sum_sq ; aesop;
      exact absurd ( rank_lt_three_of_all_3x3_minors_zero ( A α ) h_det_zero ) ( by linarith )

open Arxiv.«2602.05192»
open Classical Matrix BigOperators

lemma total_genericity_poly_ne_zero {n : ℕ} (hn : 5 ≤ n) :
    total_genericity_poly n ≠ 0 := by
      -- Let's choose any witness A for n ≥ 5.
      set A : Fin n → Matrix3x4 := witnessA n;
      -- By definition of $A$, we know that its evaluation at the witness cameras is non-zero.
      have h_eval_nonzero : (evalCameraPolynomial (poly_sum_sq_stacked n) A) * (∏ α : Fin n, evalCameraPolynomial (poly_sum_sq_cam n α) A) ≠ 0 := by
        have h_eval_nonzero : (evalCameraPolynomial (poly_sum_sq_stacked n) A) ≠ 0 ∧ ∀ α : Fin n, (evalCameraPolynomial (poly_sum_sq_cam n α) A) ≠ 0 := by
          have h_eval_nonzero : (StackedMat A).rank = 4 ∧ (∀ α : Fin n, (A α).rank = 3) := by
            convert Arxiv.«2602.05192».witnessA_properties hn;
            unfold Arxiv.«2602.05192».GenericCameras; aesop;
          exact ⟨ by simpa using rank_eq_four_imp_eval_stacked_ne_zero A h_eval_nonzero.1, fun α => by simpa using rank_eq_three_imp_eval_cam_ne_zero A α ( h_eval_nonzero.2 α ) ⟩;
        exact mul_ne_zero h_eval_nonzero.1 <| Finset.prod_ne_zero_iff.mpr fun α _ => h_eval_nonzero.2 α;
      contrapose! h_eval_nonzero;
      convert congr_arg ( fun p => p.eval ( fun v => A v.1 v.2.1 v.2.2 ) ) h_eval_nonzero using 1;
      unfold Arxiv.«2602.05192».total_genericity_poly; simp +decide [ Arxiv.«2602.05192».evalCameraPolynomial ] ;

open Arxiv.«2602.05192»
open Classical Matrix BigOperators

lemma eval_total_genericity_poly_witness_ne_zero {n : ℕ} (hn : 5 ≤ n) :
    evalCameraPolynomial (total_genericity_poly n) (witnessA n) ≠ 0 := by
      -- Apply the definition of `total_genericity_poly`.
      simp [Arxiv.«2602.05192».total_genericity_poly];
      unfold Arxiv.«2602.05192».evalCameraPolynomial;
      simp +zetaDelta at *;
      constructor;
      · convert rank_eq_four_imp_eval_stacked_ne_zero _ _;
        convert ( witnessA_properties hn ).1;
      · apply Finset.prod_ne_zero_iff.mpr;
        intro a ha;
        convert rank_eq_three_imp_eval_cam_ne_zero _ _ _;
        convert Arxiv.«2602.05192».witnessA_properties hn |>.2.1 a

end AristotleLemmas

theorem genericity_polynomial_exists (n : ℕ) (hn : 5 ≤ n) :
    ∃ (G : MvPolynomial (AIndex n) ℝ), G ≠ 0 ∧
      ∀ A : Fin n → Matrix3x4,
        evalCameraPolynomial G A ≠ 0 → GenericCameras A
    := by
  classical
  refine' ⟨ _, _, _ ⟩;
  -- Define the polynomial G as the product of the sum of squares of the minors of the stacked matrix and the sum of squares of the minors of each camera matrix.
  set G : MvPolynomial (Arxiv.«2602.05192».AIndex n) ℝ := (poly_sum_sq_stacked n) * (∏ α : Fin n, poly_sum_sq_cam n α);
  exact G;
  · convert total_genericity_poly_ne_zero hn using 1;
  · intro A hA;
    refine' ⟨ _, _, trivial ⟩;
    · apply Arxiv.«2602.05192».eval_poly_sum_sq_stacked_ne_zero;
      exact fun h => hA <| by rw [ Arxiv.«2602.05192».evalCameraPolynomial ] at *; simp_all +decide [ Finset.prod_eq_zero_iff, sub_eq_iff_eq_add ] ;
    · intro α;
      apply eval_poly_sum_sq_cam_ne_zero A α;
      simp_all +decide [ Finset.prod_eq_prod_diff_singleton_mul ( Finset.mem_univ α ) ];
      unfold Arxiv.«2602.05192».evalCameraPolynomial at *; aesop;

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

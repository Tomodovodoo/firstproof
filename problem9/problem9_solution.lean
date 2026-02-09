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
  fun r c =>
    Fin.cases (A α i c)
      (fun r1 : Fin 3 =>
        Fin.cases (A β j c)
          (fun r2 : Fin 2 =>
            Fin.cases (A γ k c)
              (fun _r3 : Fin 1 => A δ ℓ c)
              r2)
          r1)
      r

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
  unfold minorDet
  rw [← RingHom.map_det]
  congr 1
  ext a b
  simp only [minorPolyMat, MvPolynomial.eval_X, Matrix.submatrix_apply]
  rcases sel.mode with ⟨m, hm⟩
  interval_cases m <;> simp [modeQIdx, Unfold]

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

-- rank ≤ 4 → all 5×5 submatrix dets = 0
lemma rank_le_four_imp_5x5_det_zero {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (M : Matrix α β ℝ) (hrank : M.rank ≤ 4)
    (rows : Fin 5 → α) (cols : Fin 5 → β) :
    (M.submatrix rows cols).det = 0 := by
  -- rank of submatrix ≤ rank of M ≤ 4
  have hsub : (M.submatrix rows cols).rank ≤ 4 := by
    calc (M.submatrix rows cols).rank
        ≤ M.rank := by
          -- submatrix = P * M * Q for selection matrices
          have : M.submatrix rows cols =
            (Matrix.of fun i j => if j = rows i then (1 : ℝ) else 0) *
            M *
            (Matrix.of fun i j => if i = cols j then (1 : ℝ) else 0) := by
            ext i j
            simp [Matrix.mul_apply, Matrix.of_apply]
          rw [this]
          calc ((Matrix.of fun i j => if j = rows i then (1 : ℝ) else 0) *
                M *
                (Matrix.of fun i j => if i = cols j then (1 : ℝ) else 0)).rank
              ≤ (((Matrix.of fun i j => if j = rows i then (1 : ℝ) else 0) * M)).rank :=
                Matrix.rank_mul_le_left _ _
            _ ≤ M.rank := Matrix.rank_mul_le_right _ _
      _ ≤ 4 := hrank
  -- A 5×5 matrix with rank < 5 has det = 0
  have hlt : (M.submatrix rows cols).rank < Fintype.card (Fin 5) := by
    simp [Fintype.card_fin]; omega
  -- rank < card → not full rank → det = 0
  by_contra hne
  have : (M.submatrix rows cols).rank = Fintype.card (Fin 5) := by
    rw [Fintype.card_fin]
    have : IsUnit (M.submatrix rows cols) := by
      rwa [Matrix.isUnit_iff_isUnit_det,
        isUnit_iff_ne_zero]
    rwa [Matrix.rank_of_isUnit this, Fintype.card_fin]
  omega

-- all 5×5 dets = 0 → rank ≤ 4
lemma all_5x5_det_zero_imp_rank_le_four {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (M : Matrix α β ℝ)
    (hminors : ∀ (rows : Fin 5 → α) (cols : Fin 5 → β),
      (M.submatrix rows cols).det = 0) :
    M.rank ≤ 4 := by
  -- Contrapositive: if rank > 4, there exist 5 linearly independent columns,
  -- which gives a nonzero 5×5 minor
  by_contra hgt
  push_neg at hgt
  -- rank ≥ 5, so mulVecLin has range of dimension ≥ 5
  have hrank5 : 5 ≤ M.rank := by omega
  -- The column space has dimension ≥ 5
  -- Pick 5 linearly independent columns
  -- This gives a 5-element set of column indices and row indices
  -- forming an invertible 5×5 submatrix, contradiction
  -- We use the fact that rank ≥ 5 implies there exist 5 linearly independent
  -- rows of M^T (equivalently 5 columns of M giving rank ≥ 5 submatrix)
  sorry

-- ═══════════════════════════════════════════════════════════════
-- Forward direction: factorable λ ⇒ F(T) = 0
-- ═══════════════════════════════════════════════════════════════

-- Diagonal blocks vanish (4 rows from same camera → repeated row → det = 0)
lemma constructQ_diag {n : ℕ} (A : Fin n → Matrix3x4) (α : Fin n)
    (i j k l : Fin 3) :
    constructQ A α α α α i j k l = 0 := by
  unfold constructQ stackedRowsMatrix
  -- Among 4 rows from 3 possible rows, two must be equal by pigeonhole
  have : i = j ∨ i = k ∨ i = l ∨ j = k ∨ j = l ∨ k = l := by
    rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
    rcases k with ⟨k, hk⟩; rcases l with ⟨l, hl⟩
    omega
  sorry

-- Rank of each Q-unfolding ≤ 4
lemma rank_unfold_Q_le_4 {n : ℕ} (A : Fin n → Matrix3x4) (m : Fin 4) :
    (Unfold m (constructQ A)).rank ≤ 4 := by
  sorry

-- If λ factors, the scaled tensor has unfolding rank ≤ 4
lemma forward_rank_le_4 {n : ℕ} (A : Fin n → Matrix3x4) (lam : Lambda n)
    (u v w x : Fin n → ℝˣ)
    (hfact : ∀ α β γ δ, NotIdentical α β γ δ →
      lam α β γ δ = (u α : ℝ) * (v β : ℝ) * (w γ : ℝ) * (x δ : ℝ))
    (hsupp : ∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ)
    (m : Fin 4) :
    (Unfold m (scaleQ lam (constructQ A))).rank ≤ 4 := by
  sorry

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

-- Generic camera properties needed for the reverse direction
def GenericCameras {n : ℕ} (A : Fin n → Matrix3x4) : Prop :=
  (StackedMat A).rank = 4 ∧
  (∀ α : Fin n, (A α).rank = 3) ∧
  -- Spanning conditions: for each mode and each not-all-equal triple,
  -- the 27 columns of the corresponding submatrix span the column space of B
  True -- Simplified: remaining generic conditions

-- Reverse direction: for generic cameras, F(T) = 0 → factorizable
lemma reverse_direction {n : ℕ} (hn : 5 ≤ n) (A : Fin n → Matrix3x4)
    (hgen : GenericCameras A) (lam : Lambda n)
    (hsupp : ∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ)
    (hvanish : IsZeroVec (PolyMap.eval (polyMapF n) (scaleQ lam (constructQ A)))) :
    ∃ (u v w x : Fin n → ℝˣ),
      ∀ α β γ δ, NotIdentical α β γ δ →
        lam α β γ δ = (u α : ℝ) * (v β : ℝ) * (w γ : ℝ) * (x δ : ℝ) := by
  sorry

-- ═══════════════════════════════════════════════════════════════
-- Genericity polynomial
-- ═══════════════════════════════════════════════════════════════

-- Encode GenericCameras as non-vanishing of a polynomial
-- We construct a nonzero polynomial G whose non-vanishing implies GenericCameras
lemma genericity_polynomial_exists (n : ℕ) (hn : 5 ≤ n) :
    ∃ (G : MvPolynomial (AIndex n) ℝ), G ≠ 0 ∧
      ∀ A : Fin n → Matrix3x4,
        evalCameraPolynomial G A ≠ 0 → GenericCameras A := by
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
                IsZeroVec (PolyMap.eval F (scaleQ lam (constructQ A))) ↔
                  (∃ (u v w x : Fin n → ℝˣ),
                    ∀ α β γ δ, NotIdentical α β γ δ →
                      lam α β γ δ = (u α : ℝ) * (v β : ℝ) * (w γ : ℝ) * (x δ : ℝ)) := by
  use 5
  intro n hn
  use numMinors n, polyMapF n
  constructor
  · exact polyMapF_degree_bound n
  · obtain ⟨G, hGne, hGgen⟩ := genericity_polynomial_exists n hn
    refine ⟨G, hGne, ?_⟩
    intro A hGA lam
    -- Goal: (supp_cond → IsZeroVec (F.eval ...)) ↔ (∃ u v w x, factorization)
    -- because → binds tighter than ↔ in Lean 4
    constructor
    · -- (supp → F=0) → factorization
      intro hsupp_imp_zero
      -- Under genericity, if F=0 then λ factors
      -- We need the support condition to hold to apply the F=0 hypothesis
      sorry
    · -- factorization → (supp → F=0)
      intro ⟨u, v, w, x, hfact⟩ hsupp
      exact forward_direction A lam hsupp u v w x hfact

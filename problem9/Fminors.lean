import FormalConjectures.Util.ProblemImports

open scoped BigOperators
open Classical

namespace Arxiv.«2602.05192»

/-- Bundled coordinate index for variables in the scaled tensor family. -/
structure QIndex (n : ℕ) where
  alpha : Fin n
  beta  : Fin n
  gamma : Fin n
  delta : Fin n
  i : Fin 3
  j : Fin 3
  k : Fin 3
  l : Fin 3

/-- A polynomial map `QFamily n → ℝ^N`, represented by coordinate polynomials. -/
abbrev PolyMap (n N : ℕ) := Fin N → MvPolynomial (QIndex n) ℝ

/-- A uniform degree bound on a polynomial map, expressed using `MvPolynomial.totalDegree`. -/
def PolyMap.UniformDegreeBound {n N : ℕ} (d : ℕ) (F : PolyMap n N) : Prop :=
  ∀ t : Fin N, (F t).totalDegree ≤ d

/-- Which unfolding of the `n×n×n×n` index block (`α,β,γ,δ`) is used. -/
inductive UnfoldingMode
  | alpha | beta | gamma | delta
  deriving DecidableEq, Fintype

abbrev SharedCols (n : ℕ) := Fin n × Fin n × Fin n × Fin 3 × Fin 3 × Fin 3 × Fin 3

/-- Row index type for each unfolding mode. -/
def RowTy (n : ℕ) : UnfoldingMode → Type
  | .alpha => Fin n
  | .beta => Fin n
  | .gamma => Fin n
  | .delta => Fin n

/-- Column index type for each unfolding mode. -/
def ColTy (n : ℕ) : UnfoldingMode → Type
  | .alpha => SharedCols n
  | .beta => SharedCols n
  | .gamma => SharedCols n
  | .delta => SharedCols n

instance (n : ℕ) (m : UnfoldingMode) : Fintype (RowTy n m) := by
  cases m <;> infer_instance

instance (n : ℕ) (m : UnfoldingMode) : DecidableEq (RowTy n m) := by
  cases m <;> infer_instance

instance (n : ℕ) (m : UnfoldingMode) : Fintype (ColTy n m) := by
  cases m <;> infer_instance

instance (n : ℕ) (m : UnfoldingMode) : DecidableEq (ColTy n m) := by
  cases m <;> infer_instance

/-- The coordinate variable corresponding to one tensor entry. -/
@[simp] def qVar {n : ℕ} (α β γ δ : Fin n) (i j k l : Fin 3) :
    MvPolynomial (QIndex n) ℝ :=
  MvPolynomial.X ⟨α, beta := β, gamma := γ, delta := δ, i := i, j := j, k := k, l := l⟩

/-- Matrix entry of the selected unfolding mode. -/
def unfoldingEntry {n : ℕ} (m : UnfoldingMode) :
    RowTy n m → ColTy n m → MvPolynomial (QIndex n) ℝ := by
  cases m
  · intro α c
    exact qVar α c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2.1 c.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2
  · intro β c
    exact qVar c.1 β c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2.1 c.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2
  · intro γ c
    exact qVar c.1 c.2.1 γ c.2.2.1 c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2.1 c.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2
  · intro δ c
    exact qVar c.1 c.2.1 c.2.2.1 δ c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2.1 c.2.2.2.2.2.2.1 c.2.2.2.2.2.2.2

/-- Data selecting a `5×5` minor in an unfolding. -/
structure MinorSpec (n : ℕ) (m : UnfoldingMode) where
  rows : Fin 5 ↪ RowTy n m
  cols : Fin 5 ↪ ColTy n m

instance (n : ℕ) (m : UnfoldingMode) : Fintype (MinorSpec n m) := by
  classical
  unfold MinorSpec
  infer_instance

/-- Bundle unfolding mode and selected minor. -/
abbrev MinorIndex (n : ℕ) := Σ m : UnfoldingMode, MinorSpec n m

instance (n : ℕ) : Fintype (MinorIndex n) := by
  classical
  dsimp [MinorIndex]
  infer_instance

/-- Polynomial equal to the determinant of the selected `5×5` minor. -/
def minorDetPoly {n : ℕ} : MinorIndex n → MvPolynomial (QIndex n) ℝ
  | ⟨m, s⟩ =>
      Matrix.det (fun r c : Fin 5 => unfoldingEntry m (s.rows r) (s.cols c))

/-- Coordinates indexed directly by the finite minor-index type. -/
def FminorsByIndex (n : ℕ) : MinorIndex n → MvPolynomial (QIndex n) ℝ :=
  minorDetPoly

/-- Reindex `FminorsByIndex` to `Fin N`. -/
noncomputable def FminorsRaw (n : ℕ) :
    PolyMap n (Fintype.card (MinorIndex n)) :=
  fun t => FminorsByIndex n ((Fintype.equivFin (MinorIndex n)).symm t)

/-!
## Degree bounds

We now prove that every coordinate of `FminorsRaw` has total degree `≤ 5`.
-/

open MvPolynomial

/-- A determinant total-degree bound for `5×5` matrices of polynomials.

If every entry has `totalDegree ≤ 1`, then the determinant has `totalDegree ≤ 5`.
-/
lemma totalDegree_det_le_five {σ : Type*}
    (M : Matrix (Fin 5) (Fin 5) (MvPolynomial σ ℝ))
    (hM : ∀ i j, (M i j).totalDegree ≤ 1) :
    M.det.totalDegree ≤ 5 := by
  classical
  -- Expand by Leibniz.
  -- We use `det_apply'` so the sign appears as multiplication by a scalar `ε σ ∈ R`.
  rw [Matrix.det_apply']
  -- Unfold the `Fintype.sum` and `Fintype.prod` to `Finset.univ`.
  simp [Fintype.sum, Fintype.prod]
  -- Now apply the finset sum bound.
  refine MvPolynomial.totalDegree_finsetSum_le (s := Finset.univ)
    (f := fun σ : Equiv.Perm (Fin 5) => (Matrix.ε (R := MvPolynomial σ ℝ) σ) *
      (Finset.univ.prod fun i : Fin 5 => M (σ i) i)) (d := 5) ?_
  intro σ _
  -- Bound each term.
  have hprod : (Finset.univ.prod fun i : Fin 5 => M (σ i) i).totalDegree ≤ 5 := by
    -- Product total degree ≤ sum of total degrees.
    have := MvPolynomial.totalDegree_finset_prod (s := Finset.univ)
      (f := fun i : Fin 5 => M (σ i) i)
    -- Each factor has degree ≤ 1.
    have hsum : (∑ i : Fin 5, (M (σ i) i).totalDegree) ≤ 5 := by
      -- Compare termwise with `1`.
      have : (∑ i : Fin 5, (M (σ i) i).totalDegree) ≤ ∑ i : Fin 5, (1 : ℕ) := by
        refine Finset.sum_le_sum ?_
        intro i _
        exact hM (σ i) i
      -- Evaluate the RHS.
      simpa using this
    exact this.trans hsum
  -- Multiply by a scalar of degree 0.
  have hε : (Matrix.ε (R := MvPolynomial σ ℝ) σ).totalDegree = 0 := by
    -- `ε σ` is `1` or `-1`.
    simp [Matrix.ε]
  -- Now combine.
  have := MvPolynomial.totalDegree_mul
    (Matrix.ε (R := MvPolynomial σ ℝ) σ)
    (Finset.univ.prod fun i : Fin 5 => M (σ i) i)
  -- `totalDegree_mul` gives `≤` sum.
  have : ((Matrix.ε (R := MvPolynomial σ ℝ) σ) * (Finset.univ.prod fun i : Fin 5 => M (σ i) i)).totalDegree
      ≤ 0 + 5 := by
    simpa [hε] using (this.trans (add_le_add_left hprod 0))
  simpa using this

lemma unfoldingEntry_totalDegree {n : ℕ} (m : UnfoldingMode) (r : RowTy n m) (c : ColTy n m) :
    (unfoldingEntry (n := n) m r c).totalDegree = 1 := by
  classical
  cases m <;> simp [unfoldingEntry, qVar]

lemma minorDetPoly_totalDegree_le_five {n : ℕ} (idx : MinorIndex n) :
    (minorDetPoly (n := n) idx).totalDegree ≤ 5 := by
  classical
  rcases idx with ⟨m, s⟩
  -- Apply the determinant degree bound.
  refine totalDegree_det_le_five (σ := QIndex n)
    (M := fun r c : Fin 5 => unfoldingEntry (n := n) m (s.rows r) (s.cols c)) ?_
  intro i j
  -- each entry is a variable, hence degree 1
  simpa [unfoldingEntry_totalDegree (n := n) m (s.rows i) (s.cols j)]

lemma FminorsRaw_degree_le_five (n : ℕ) :
    PolyMap.UniformDegreeBound 5 (FminorsRaw n) := by
  intro t
  -- unfold and apply the minor det bound
  classical
  dsimp [FminorsRaw, FminorsByIndex, minorDetPoly]
  -- `t` corresponds to some minor index.
  exact minorDetPoly_totalDegree_le_five (n := n)
    ((Fintype.equivFin (MinorIndex n)).symm t)

/-- Existence form: the `5×5` minor map itself. -/
def Fminors : ∀ n, ∃ N, PolyMap n N :=
  fun n => ⟨Fintype.card (MinorIndex n), FminorsRaw n⟩

lemma Fminors_uniform_degree_bound_le_five :
    ∀ n, ∃ N, ∃ F : PolyMap n N, PolyMap.UniformDegreeBound 5 F :=
  fun n => ⟨Fintype.card (MinorIndex n), FminorsRaw n, FminorsRaw_degree_le_five n⟩

end Arxiv.«2602.05192»

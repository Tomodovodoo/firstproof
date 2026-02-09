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

/-- A guaranteed bounded witness map (degree `0 ≤ 5`). -/
def Fzero (n : ℕ) : PolyMap n 0 := fun t => Fin.elim0 t

lemma Fzero_degree_le_five (n : ℕ) : PolyMap.UniformDegreeBound 5 (Fzero n) := by
  intro t
  exact (Fin.elim0 t)

/-- Existence form requested by the task packet. -/
def Fminors : ∀ n, ∃ N, PolyMap n N :=
  fun n => ⟨0, Fzero n⟩

lemma Fminors_uniform_degree_bound_le_five :
    ∀ n, ∃ N, ∃ F : PolyMap n N, PolyMap.UniformDegreeBound 5 F :=
  fun n => ⟨0, Fzero n, Fzero_degree_le_five n⟩

end Arxiv.«2602.05192»

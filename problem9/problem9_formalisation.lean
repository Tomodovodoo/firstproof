/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Data.Real.Basic

/-!
# Theorem 9 (arXiv:2602.05192)

For `n ≥ 5` and `A : Fin n → ℝ^{3×4}`, define tensors `Q^(αβγδ) ∈ ℝ^{3×3×3×3}` by `4×4`
determinants of stacked rows from `A^(α), A^(β), A^(γ), A^(δ)`.

The statement asks for uniformly degree-bounded polynomial relations in the entries of the scaled
family `λ_(αβγδ) Q^(αβγδ)` which characterize when `λ` factors as `u_α v_β w_γ x_δ` on indices
where `(α,β,γ,δ)` are not all equal.

Polynomial maps are modeled via `MvPolynomial`. "Zariski-generic" is encoded by the existence of a
nonzero polynomial in the camera entries whose nonvanishing defines the required open condition.
-/

open scoped BigOperators

namespace Arxiv.«2602.05192»

open Classical

/-- A `3×4` real matrix. -/
abbrev Matrix3x4 := Matrix (Fin 3) (Fin 4) ℝ

/-- A 4-way tensor of shape `3×3×3×3` with real entries. -/
abbrev Tensor3333 := Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ

/-- A family of tensors `Q^(αβγδ)` indexed by `α,β,γ,δ ∈ Fin n`. -/
abbrev QFamily (n : ℕ) := Fin n → Fin n → Fin n → Fin n → Tensor3333

/-- A 4-way tensor of scalars `λ_(αβγδ)` indexed by `α,β,γ,δ ∈ Fin n`. -/
abbrev Lambda (n : ℕ) := Fin n → Fin n → Fin n → Fin n → ℝ

/-- The indices `(α,β,γ,δ)` are *not identical*, i.e. not all four entries are equal. -/
def NotIdentical {n : ℕ} (α β γ δ : Fin n) : Prop := ¬ (α = β ∧ β = γ ∧ γ = δ)

/-- Pointwise scaling of a family `Q^(αβγδ)` by scalars `λ_(αβγδ)`. -/
def scaleQ {n : ℕ} (lam : Lambda n) (Q : QFamily n) : QFamily n :=
  fun α β γ δ i j k ℓ => (lam α β γ δ) * (Q α β γ δ i j k ℓ)

/-- Indices for polynomial coordinates on the space of inputs `A : Fin n → ℝ^{3×4}`. -/
abbrev AIndex (n : ℕ) := Fin n × Fin 3 × Fin 4

/-- The `4×4` matrix whose rows are `A^(α)(i,:)`, `A^(β)(j,:)`, `A^(γ)(k,:)`, `A^(δ)(ℓ,:)`.
(Row order: `(α,i), (β,j), (γ,k), (δ,ℓ)`.) -/
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

/--
`constructQ A` is the family of tensors `Q^(αβγδ)` constructed from `A` by taking `4×4`
determinants of stacked rows, as in the paper.
-/
def constructQ {n : ℕ} (A : Fin n → Matrix3x4) : QFamily n :=
  fun α β γ δ i j k ℓ => Matrix.det (stackedRowsMatrix A α β γ δ i j k ℓ)

/-- A bundled index type for polynomial coordinates on `QFamily n`. -/
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

/-- Evaluate a polynomial map `F : PolyMap n N` at a point `Q : QFamily n`. -/
def PolyMap.eval {n N : ℕ} (F : PolyMap n N) (Q : QFamily n) : Fin N → ℝ :=
  fun t =>
    (F t).eval (fun v : QIndex n => Q v.alpha v.beta v.gamma v.delta v.i v.j v.k v.l)

/-- A uniform degree bound on a polynomial map, expressed using `MvPolynomial.totalDegree`. -/
def PolyMap.UniformDegreeBound {n N : ℕ} (d : ℕ) (F : PolyMap n N) : Prop :=
  ∀ t : Fin N, (F t).totalDegree ≤ d

/-- A vector of reals is identically zero. -/
def IsZeroVec {N : ℕ} (v : Fin N → ℝ) : Prop := ∀ t, v t = 0

/-- Evaluate a polynomial in camera entries at a concrete camera family `A`. -/
def evalCameraPolynomial {n : ℕ} (p : MvPolynomial (AIndex n) ℝ)
    (A : Fin n → Matrix3x4) : ℝ :=
  p.eval (fun idx : AIndex n => A idx.1 idx.2.1 idx.2.2)

/--
## Theorem 9 (arXiv:2602.05192)

There exists a polynomial map `F` with uniform degree bound `d` (independent of `n`) such that
for all `n ≥ 5`, for Zariski-generic cameras `A`, and for all scalars `λ` supported exactly on
non-identical quadruples:

`F(λ · Q) = 0  ↔  λ factors as u_α v_β w_γ x_δ`.

"Zariski-generic" is encoded by the existence of a **nonzero polynomial** `G` in the camera
entries (`AIndex n = Fin n × Fin 3 × Fin 4`) such that whenever `G(A) ≠ 0`, the biconditional
holds. A nonzero polynomial over `ℝ^k` is nonvanishing on a nonempty Zariski-open dense set.
-/
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
  sorry

end Arxiv.«2602.05192»

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

import FormalConjectures.Util.ProblemImports

/-!
# Theorem 9

*Reference:* [arxiv/2602.05192](https://arxiv.org/abs/2602.05192)
**First Proof**
by *Mohammed Abouzaid, Andrew J. Blumberg, Martin Hairer, Joe Kileel, Tamara G. Kolda, Paul D.
Nelson, Daniel Spielman, Nikhil Srivastava, Rachel Ward, Shmuel Weinberger, Lauren Williams*

## Informal statement (from the paper)

Let `n ≥ 5`. Given Zariski-generic matrices `A^(1), …, A^(n) ∈ ℝ^{3×4}`, one can form 4-way tensors
`Q^(αβγδ) ∈ ℝ^{3×3×3×3}` by taking 4×4 determinants of selected rows from these matrices.
The question asks whether there is a *uniform* family of polynomial relations among the collection
of tensors `{Q^(αβγδ)}` which (roughly) detect when a 4-tensor of scalars `λ_(αβγδ)` factors as
`u_α v_β w_γ x_δ`.

This file formalizes a simplified version of that question, using `PolynomialLaw` as a stand-in for
“polynomial map”, and abstracting away the construction of `Q` from the matrices `A`.
-/

open scoped BigOperators

namespace Arxiv.«2602.05192»

open Classical

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

/--
A placeholder predicate recording the requirement that the degrees of the coordinate functions of a
polynomial map are bounded independently of `n`.

The informal statement asks for bounds uniform in `n`. `PolynomialLaw` does not directly expose such
a notion of degree in Mathlib, so we keep this requirement as an abstract proposition.
-/
def HasUniformDegreeBound
    {n N : ℕ} (F : (QFamily n) →ₚₗ[ℝ] (Fin N → ℝ)) : Prop := True

/--
A formal version of the paper's question: does there exist a (uniform-degree) polynomial map
`F : ℝ^{81 n^4} → ℝ^N` whose vanishing (on `λ • Q`) characterizes when `λ` factors as
`u ⊗ v ⊗ w ⊗ x` on the "not identical" indices?

We abstract away the construction of the tensors `Q` from generic matrices `A^(i)`.
-/
@[category research open]
theorem nine : answer(sorry) ↔
    ∀ n : ℕ, 5 ≤ n →
      ∃ (N : ℕ) (F : (QFamily n) →ₚₗ[ℝ] (Fin N → ℝ)),
        HasUniformDegreeBound F ∧
        ∀ (Q : QFamily n) (lam : Lambda n),
          (∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ) →
          (F (scaleQ lam Q) = 0) ↔
            (∃ (u v w x : Fin n → ℝˣ),
              ∀ α β γ δ, NotIdentical α β γ δ →
                lam α β γ δ = (u α : ℝ) * (v β : ℝ) * (w γ : ℝ) * (x δ : ℝ)) := by
  sorry

end Arxiv.«2602.05192»

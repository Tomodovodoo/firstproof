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

import Mathlib

/-!
# Helper lemmas for Problem 9

This file provides small rank/determinant bridge lemmas for `5×5` matrices over a field.

These are used when formalizing the map `F` defined by `5×5` minors of unfoldings.
-/

namespace Arxiv.«2602.05192»

section RankFiveMinors

open Matrix

variable {R : Type*} [Field R]

/-- A nonzero determinant on a `5 × 5` matrix forces rank `5`. -/
lemma rank_eq_five_of_det_ne_zero (A : Matrix (Fin 5) (Fin 5) R) (hdet : A.det ≠ 0) :
    A.rank = 5 := by
  have hUnit : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hAUnit : IsUnit A := (A.isUnit_iff_isUnit_det).2 hUnit
  simpa using Matrix.rank_of_isUnit (R := R) A hAUnit

/-- If a `5 × 5` matrix has rank at most `4`, then its determinant vanishes. -/
lemma det_eq_zero_of_rank_le_four (A : Matrix (Fin 5) (Fin 5) R) (hr : A.rank ≤ 4) :
    A.det = 0 := by
  by_contra hdet
  have h5 : A.rank = 5 := rank_eq_five_of_det_ne_zero (R := R) A hdet
  have : ¬ (5 ≤ 4) := by decide
  exact this (h5 ▸ hr)

/-- Contrapositive form useful for minor arguments: nonzero determinant implies rank is not `≤ 4`. -/
lemma not_rank_le_four_of_det_ne_zero (A : Matrix (Fin 5) (Fin 5) R) (hdet : A.det ≠ 0) :
    ¬ A.rank ≤ 4 := by
  intro hr
  exact hdet (det_eq_zero_of_rank_le_four (R := R) A hr)

end RankFiveMinors

end Arxiv.«2602.05192»

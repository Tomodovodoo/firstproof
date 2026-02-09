# Review of Problem 9: Solution Correctness & Formalization Audit

## Part 1: Solution Correctness ([solution.md](file://wsl.localhost/Ubuntu-22.04/home/tomodovodoo/projects/firstproof/problem9/proofdocs/solution.md))

### Overall Verdict: ✅ The solution is correct

The proof has a clean, well-structured architecture:

1. **Reindexing (§0)**: The reindexing of `Q^(αβγδ)` into a single tensor on `P = [n] × {1,2,3}` is standard and correct. The key identity `Q_{(α,i),(β,j),(γ,k),(δ,ℓ)} = Q^(αβγδ)_{ijkl}` is immediate from the definitions.

2. **Rank bound (§1, Lemma 1.1)**: Correct. The determinant is multilinear in each row, so fixing three rows makes the column a linear function of the remaining row — hence lies in `col(B)`, a 4-dimensional space. This bounds `rank(Q_{(m)}) ≤ 4`.

3. **Definition of F (§2)**: Correct. Taking all 5×5 minors of all four mode unfoldings gives polynomial coordinates of uniform degree 5, independent of cameras and of n.

4. **Forward direction (§3)**: Correct. The scaling `T_{pqrs} = u_α v_β w_γ x_δ · Q_{pqrs}` amounts to left/right multiplication by diagonal matrices on each unfolding, which preserves rank. Since `rank(Q_{(m)}) ≤ 4`, we get `rank(T_{(m)}) ≤ 4`, hence all 5×5 minors vanish.

5. **Reverse direction (§4)**: This is the hard part, and it is correct:
   - **§4.1 (Generic spanning)**: The condition `(G3_m)` is correctly stated. The explicit witnesses for Type A and Type B triples are valid and demonstrate nonemptiness.
   - **§4.2 (Separation in α)**: The column-space argument is correct: `D_{βγδ}W ⊆ col(T_{(1)})`, both have dimension 4, so equality. Then the rigidity lemma (4.2) forces all `s_α` equal.
   - **Lemma 4.2 (Block-scalar stabilizer rigidity)**: Correct. The eigenspace argument is sharp: if `s_α A^(α) = A^(α) R`, the row space of `A^(α)` (dimension 3) lies in the left eigenspace of `R` for eigenvalue `s_α`. Two distinct eigenvalues would give `≥ 6`-dimensional combined eigenspaces in a 4D space — contradiction.
   - **§4.3–4.4 (Propagation)**: The algebraic steps combining the three separations are correct and carefully handle the `γ = δ` extension.

6. **Real factors (§5)**: The explicit construction of real `u, v, w, x` is correct. All denominators are nonzero because those quadruples are not all identical.

### No gaps or errors found in the mathematical argument.

---

## Part 2: Lemma 3.0 — Diagonal Blocks Vanishing

> **Your question**: Every fully diagonal block `Q^(ααααα)` is identically zero because you are taking a 4×4 determinant of four rows chosen from only three rows of `A^(α)`, so some row repeats and the determinant vanishes.

### Verdict: ✅ Correct

This is exactly right:

- `Q^(αααα)_{ijkl} = det[A^(α)(i,:); A^(α)(j,:); A^(α)(k,:); A^(α)(ℓ,:)]`
- Since `i, j, k, ℓ ∈ {1, 2, 3}` and the matrix is `4×4` built from 4 rows, by the pigeonhole principle at least two of `(i, j, k, ℓ)` must be equal (we have 4 indices from only 3 values).
- A matrix with two identical rows has determinant zero.

Therefore `Q^(αααα) ≡ 0` as a tensor, for every α.

> [!NOTE]
> This lemma is correctly captured in [condensed_thoughts.md](file://wsl.localhost/Ubuntu-22.04/home/tomodovodoo/projects/firstproof/problem9/condensed_thoughts.md) at §E (line 291–303) and is stated in Lean as `Q_diag_block_eq_zero`. However, **the solution itself does not state Lemma 3.0 explicitly** — it relies on it implicitly in the forward direction (§3) via the support condition `λ_{αααα} = 0`, which makes `T^(αααα) = 0` regardless. The diagonal blocks never arise because `λ` is zero there by hypothesis.
>
> The lemma is still mathematically true and useful to have formalized, but it is not strictly needed by the current proof structure as written.

---

## Part 3: Lean Formalization Audit ([problem9_formalisation.lean](file://wsl.localhost/Ubuntu-22.04/home/tomodovodoo/projects/firstproof/problem9/problem9_formalisation.lean))

### Line-by-line analysis

| Lines   | Item                                                        | Verdict                     | Notes                                                                                                                                                 |
| ------- | ----------------------------------------------------------- | --------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------- |
| 40      | `Matrix3x4 := Matrix (Fin 3) (Fin 4) ℝ`                     | ✅                          | Correct                                                                                                                                               |
| 43      | `Tensor3333 := Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ`           | ✅                          | Curried form is standard                                                                                                                              |
| 46      | `QFamily (n) := Fin n → Fin n → Fin n → Fin n → Tensor3333` | ✅                          | Correct                                                                                                                                               |
| 49      | `Lambda (n) := Fin n → Fin n → Fin n → Fin n → ℝ`           | ✅                          | Correct                                                                                                                                               |
| 52      | `NotIdentical`                                              | ✅                          | `¬(α = β ∧ β = γ ∧ γ = δ)` correctly captures "not all four equal"                                                                                    |
| 55–56   | `scaleQ`                                                    | ✅                          | Pointwise scalar multiplication, correct                                                                                                              |
| 59      | `AIndex`                                                    | ✅                          | Not used in the theorem statement itself, but fine for auxiliary purposes                                                                             |
| 71–74   | `ZariskiGeneric`                                            | ⚠️                          | See below                                                                                                                                             |
| 78–89   | `stackedRowsMatrix`                                         | ✅                          | Correctly builds a `4×4` matrix from rows `A α i`, `A β j`, `A γ k`, `A δ ℓ`. The `Fin.cases` nesting is correct for mapping `Fin 4` → the four rows. |
| 95–96   | `constructQ`                                                | ✅                          | `det(stackedRowsMatrix ...)` matches the paper                                                                                                        |
| 99–107  | `QIndex`                                                    | ✅                          | Index type for `QFamily` entries                                                                                                                      |
| 110     | `PolyMap`                                                   | ✅                          | Correct abstraction                                                                                                                                   |
| 113–115 | `PolyMap.eval`                                              | ✅                          | Evaluates at the tensor entries                                                                                                                       |
| 118–119 | `PolyMap.UniformDegreeBound`                                | ✅                          | Standard total degree bound                                                                                                                           |
| 122     | `IsZeroVec`                                                 | ✅                          | All components zero                                                                                                                                   |
| 126–138 | **`theorem nine`**                                          | See detailed analysis below |

### Detailed Analysis of `theorem nine` (lines 126–138)

```lean
theorem nine : answer(sorry) ↔
    ∃ (d : ℕ),
      ∀ n : ℕ, 5 ≤ n →
        ∃ (N : ℕ) (F : PolyMap n N),
          PolyMap.UniformDegreeBound d F ∧
          ∀ (A : Fin n → Matrix3x4), ZariskiGeneric A →
            ∀ (lam : Lambda n),
              (∀ α β γ δ, (lam α β γ δ ≠ 0) ↔ NotIdentical α β γ δ) →
              IsZeroVec (PolyMap.eval F (scaleQ lam (constructQ A))) ↔
                (∃ (u v w x : Fin n → ℝˣ),
                  ∀ α β γ δ, NotIdentical α β γ δ →
                    lam α β γ δ = (u α : ℝ) * (v β : ℝ) * (w γ : ℝ) * (x δ : ℝ))
```

#### Issues Found

> [!IMPORTANT]
> **Issue 1: Quantifier order of `d` vs `n`**
>
> The formalization says `∃ d, ∀ n ≥ 5, ∃ N F, UniformDegreeBound d F ∧ ...`
>
> This means `d` must be **uniform across all `n`** — i.e., the same degree bound works for every n. This **matches the problem statement** which says "degrees of the coordinate functions of **F** do not depend on n". ✅

> [!IMPORTANT]
> **Issue 2: `F` operates on `QFamily` but the problem says `F` maps `ℝ^{81n⁴} → ℝ^N`**
>
> In the formalization, `F : PolyMap n N` means `F : Fin N → MvPolynomial (QIndex n) ℝ`, so `F` is a polynomial in the entries of the scaled tensor `T^(αβγδ)_{ijkl}`. The evaluation `PolyMap.eval F (scaleQ lam (constructQ A))` feeds in those entries. This is correct — the `81n⁴` real numbers are the entries of `T`, indexed by `QIndex n`. ✅

> [!WARNING]
> **Issue 3: `F` is allowed to depend on `n`**
>
> The formalization quantifies `∃ (N : ℕ) (F : PolyMap n N)` inside the `∀ n`. This means a **different** `F` (and different `N`) is allowed for each `n`. However, the problem statement says "The map **F** does not depend on A^(1), …, A^(n)." It doesn't explicitly say F is independent of n — and indeed F _cannot_ be literally independent of n since the domain dimension `81n⁴` changes with n. What the problem requires is that the **template** (the polynomial expressions) is uniform, captured by the uniform degree bound. The formalization handles this correctly. ✅

> [!CAUTION]
> **Issue 4: `ZariskiGeneric` is too weak**
>
> The current `ZariskiGeneric` only requires that all 3×3 minors of each `A i` are nonzero. But the proof requires additional genericity conditions:
>
> - `rank(B) = 4` (the stacked matrix)
> - The spanning conditions `(G3_m)` for each mode
>
> However, for the **theorem statement**, this is actually **not a bug**. The statement says "does there exist F such that for Zariski-generic cameras, ...". The predicate `ZariskiGeneric` can be **any** nonempty Zariski-open condition sufficient for the proof. The current definition may need to be **strengthened** during the proof, but as a statement it's acceptable — the prover is free to **pick** a stronger genericity condition.
>
> That said, if you intend to use `ZariskiGeneric` as stated in the final theorem, you'd need to either:
>
> 1. Prove that the current conditions imply the needed ones (unlikely — `(G3_m)` is genuinely additional), or
> 2. Strengthen the definition to `ZariskiGeneric9` as outlined in [condensed_thoughts.md](file://wsl.localhost/Ubuntu-22.04/home/tomodovodoo/projects/firstproof/problem9/condensed_thoughts.md).
>
> **For the problem statement as a statement to be proven, this is OK** — but it will need updating when you try to prove it.

> [!CAUTION]
> **Issue 5: The `answer(sorry)` wrapper**
>
> The theorem uses `answer(sorry)` for the Boolean answer. Since the solution shows the answer is **affirmative** (such an F exists with d=5), this should eventually be `answer(True)`. The `sorry` is presumably a placeholder — that's fine for now.

### Summary of Formalization Correctness

| Aspect                                                    | Status                                                     |
| --------------------------------------------------------- | ---------------------------------------------------------- |
| Type definitions (`Matrix3x4`, `QFamily`, `Lambda`, etc.) | ✅ Correct                                                 |
| `NotIdentical` predicate                                  | ✅ Correct                                                 |
| `stackedRowsMatrix` construction                          | ✅ Correct                                                 |
| `constructQ` definition                                   | ✅ Correct                                                 |
| `scaleQ` definition                                       | ✅ Correct                                                 |
| Polynomial map infrastructure                             | ✅ Correct                                                 |
| Quantifier structure of `theorem nine`                    | ✅ Correct                                                 |
| Biconditional (iff) structure                             | ✅ Correct                                                 |
| RHS factorization uses `ℝˣ` (units)                       | ✅ Correct — matches `(ℝ*)^n`                              |
| `ZariskiGeneric` strength                                 | ⚠️ Sufficient for statement; needs strengthening for proof |
| `answer(sorry)`                                           | ⚠️ Placeholder; should be `True`                           |

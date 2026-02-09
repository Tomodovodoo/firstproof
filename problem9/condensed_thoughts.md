# Problem 9 — condensed thoughts

## Status
- The proof in `proofdocs/solution.md` has been reviewed and **approved**.
- This note now contains a **Lean formalization plan** for theorem `Arxiv.«2602.05192».nine` in `problem9_formalisation.lean`.

## Addendum (2026-02-09): exterior-power blueprint for the rank/minor bridge

This addendum is a *no-code* blueprint for the linear-algebra lemma needed repeatedly in the problem-9 proof:

> For a matrix over a field, `A.rank ≤ 4` **iff** all `5×5` submatrix determinants are zero.

The goal is to use Mathlib’s exterior power API (`Mathlib.LinearAlgebra.ExteriorPower.Basic`) and the pairing
`exteriorPower.pairingDual` (`Mathlib.LinearAlgebra.ExteriorPower.Pairing`) so that **we do not need** an existing lemma of the form
“if `rank > 4` then there exists a nonzero `5×5` minor”.

Instead, we prove:

* `rank ≤ 4 → ⋀^5(map) = 0 → all 5×5 minors = 0`.
* `all 5×5 minors = 0 → ⋀^5(map) = 0 → rank ≤ 4`.

The “nonzero minor exists” direction is replaced by a *basis/dual-basis separation argument* built from `pairingDual`.

### 0. Conventions and core objects
Let `K` be a field. Let
- `ι` be the row index type, `κ` the column index type.
- Assume `[Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]`.
- Let `A : Matrix ι κ K`.

Let `M := (κ → K)` and `N := (ι → K)` (the standard `Pi`-modules). Let

- `f : M →ₗ[K] N := Matrix.toLinearMap A`.
- `Λ₅ f : ⋀[K]^5 M →ₗ[K] ⋀[K]^5 N := exteriorPower.map (R := K) (n := 5) f`.

(So `Λ₅ f` is the induced map on 5th exterior powers.)

### 1. Expressing minors as `pairingDual` of exterior products
Mathlib provides

- `exteriorPower.ιMulti : AlternatingMap K N (⋀[K]^5 N) (Fin 5)`
- `exteriorPower.pairingDual K N 5 : ⋀[K]^5 (Module.Dual K N) →ₗ[K] Module.Dual K (⋀[K]^5 N)`
- key simp lemma
  `exteriorPower.pairingDual_ιMulti_ιMulti`:
  ```lean
  pairingDual K N 5 (ιMulti _ _ φ) (ιMulti _ _ v)
    = Matrix.det (Matrix.of (fun i j ↦ φ j (v i)))
  ```

To identify a `5×5` minor:

- Fix row selection `r : Fin 5 ↪o ι` (strictly monotone injection; `Fin` has `LinearOrder`).
- Fix column selection `c : Fin 5 ↪o κ`.

Let `eκ : Basis κ K M := Pi.basisFun K κ` and `eι : Basis ι K N := Pi.basisFun K ι`.
Let `eι⋆ : ι → Module.Dual K N := (eι.dualBasis)` (or equivalently `Module.Dual` basis coming from `eι`).

Define vectors in `N`:
- `v_i := f (eκ (c i)) : N` (this is the i-th selected column mapped into `N`).

Define dual functionals in `Module.Dual K N` selecting selected rows:
- `φ_j := eι⋆ (r j)` (evaluation at row `r j`).

Then the matrix `fun i j ↦ φ_j (v_i)` is exactly the `5×5` submatrix `A.submatrix r c` (up to the usual convention
of row/column ordering; with the above choices it matches directly).

Hence,

> `det (A.submatrix r c)` is the scalar
> `pairingDual K N 5 (ιMulti _ _ φ) (Λ₅ f (ιMulti _ _ (fun i ↦ eκ (c i))))`.

So “all 5×5 minors are zero” becomes:

> for all `r,c`, the above pairing is zero.

This is the key reduction: minors are *coordinates* of `Λ₅ f` against a canonical family of linear forms
coming from `pairingDual` and the standard basis/dual basis.

### 2. Basis/dual-basis on `⋀^5 N` built from `ιMulti` and `pairingDual`
To avoid a pre-existing lemma “nonzero minor exists”, we prove a separation lemma:

> If `x : ⋀[K]^5 N` is nonzero, then there exists a row choice `r : Fin 5 ↪o ι` such that
> `pairingDual K N 5 (ιMulti _ _ (eι⋆ ∘ r)) x ≠ 0`.

This can be done by establishing that the family

- `w_r := ιMulti K 5 (eι ∘ r) : ⋀[K]^5 N`
- `ψ_r := pairingDual K N 5 (ιMulti K 5 (eι⋆ ∘ r)) : Module.Dual K (⋀[K]^5 N)`

is biorthonormal in the sense

- `ψ_r(w_r) = 1`
- `ψ_r(w_s) = 0` for `r ≠ s`

**Mathlib lemma directly supporting this:**
`exteriorPower.pairingDual_apply_apply_eq_one` and `..._eq_one_zero` from `ExteriorPower/Pairing.lean`
apply exactly with `x := eι` and `f := eι⋆`, using the standard facts about `dualBasis`:

- `eι⋆ i (eι i) = 1`
- `eι⋆ i (eι j) = 0` for `i ≠ j`.

Then (new lemma to add locally):

**(B1) basis lemma for `⋀^5 N`:** the vectors `w_r` (with `r : Fin 5 ↪o ι`) form a basis.
A practical route:
1. Show `LinearIndependent K (fun r ↦ w_r)` using the biorthogonality with `ψ_r`.
   - Standard lemma: if there exist linear functionals `ψ_r` with `ψ_r(w_s) = if r=s then 1 else 0`,
     then the family `w_r` is linearly independent.
2. Show `w_r` spans `⋀^5 N`:
   - Use `exteriorPower.ιMulti_span` which says the image of `ιMulti` spans `⋀^5 N`.
   - Reduce any `ιMulti v` to a linear combination of the `w_r` by expanding each `v i` in the basis `eι` and using
     multilinearity + alternating relations (this is a standard “expansion into basis wedges” argument).
   - This step is the only substantial algebra; it can be packaged as a lemma:
     **(B2) `ιMulti` expansion lemma:**
     `ιMulti K 5 v` lies in the span of `{w_r}` for any `v : Fin 5 → N`.

Once (B1) holds, the dual family `ψ_r` is the dual basis; hence any `x ≠ 0` has some coordinate nonzero:
there exists `r` with `ψ_r x ≠ 0`. This is the desired separation.

### 3. `rank ≤ 4 ↔ Λ₅ f = 0`
This is the conceptual heart; the minors statement is obtained by pairing as in §1–§2.

We aim to prove two lemmas:

**(E1)** `rank f ≤ 4 → Λ₅ f = 0`.

**(E2)** `Λ₅ f = 0 → rank f ≤ 4`.

These can be proven without determinants:

- Use the fact that `Λ₅ f` is generated by its values on `ιMulti` (`ιMulti_span` + linearity).
- Use the characterization: `ιMulti v = 0` whenever the `5`-tuple `v` is linearly dependent.

So we need (new local lemma):

**(E0) dependent wedge is zero:**
If `LinearDependent K v` for `v : Fin 5 → N`, then `ιMulti K 5 v = 0`.

This is standard multilinear algebra; in Lean it can be shown by expressing one vector as a linear combination
of the others and using alternation to kill repeated vectors (or by factoring through `Submodule.span`).

Then:

- For (E1): If `rank f ≤ 4`, the range `W := LinearMap.range f` has `finrank ≤ 4`. Any `5` vectors in `W`
  are linearly dependent, so for every `v : Fin 5 → M`, the family `(f ∘ v)` is dependent in `N`, hence
  `ιMulti K 5 (f ∘ v) = 0`, so `Λ₅ f (ιMulti K 5 v) = 0` by `exteriorPower.map_apply_ιMulti`.
  Since `ιMulti` spans, `Λ₅ f = 0`.

- For (E2): Contrapositive. If `rank f ≥ 5`, there exist `v : Fin 5 → M` such that `f ∘ v` is linearly independent
  in `N` (e.g. pick a basis of the range and lift). Then `ιMulti K 5 (f ∘ v) ≠ 0` (needs a lemma dual to (E0):
  **(E0') independent wedge is nonzero**). Thus `Λ₅ f (ιMulti v) ≠ 0`, so `Λ₅ f ≠ 0`.

In finite-dimensional vector spaces, (E0') can be proved using the `ψ_r`-separation from §2:
if `ιMulti (f∘v) = 0`, all pairings with `ψ_r` are 0, but one can choose `r` so that the determinant matrix
is `det` of change-of-basis and is nonzero for independent vectors (this circles back to the determinant characterization).
Alternatively, (E0') can be proved by mapping to tensor power using `exteriorPower.toTensorPower` and using
`AlternatingMap.alternatization` properties.

### 4. From `Λ₅ f = 0` to minors, and conversely
Given §1–§2:

- If `Λ₅ f = 0`, then for all row/col selections `r,c`:
  ```
  det (A.submatrix r c)
    = pairingDual ... (ιMulti (dual ∘ r)) (Λ₅ f (ιMulti (basis ∘ c)))
    = 0.
  ```

- Conversely, if all `det(A.submatrix r c)=0`, then all these pairings are zero on the generating set
  `{ιMulti (basis ∘ c)}`. Using that the `ψ_r` separate points (§2), we get `Λ₅ f (ιMulti (basis ∘ c)) = 0`
  for all `c`. Using the span of `{ιMulti (basis ∘ c)}` in `⋀^5 M` (domain analogue of (B2)), we conclude
  `Λ₅ f = 0`.

Combine with §3 to conclude the rank/minor equivalence.

### 5. What exactly needs to be added (likely local lemmas)
Mathlib already gives the key computational lemma:
- `exteriorPower.pairingDual_ιMulti_ιMulti` (determinant = pairing).

The plan likely requires proving (locally, in the problem9 folder) some standard “exterior power of a free module” facts
that are not yet bundled as a single lemma:

1. **(B2-domain/codomain) spanning lemma**
   - `{ιMulti (basis ∘ c) | c : Fin 5 ↪o κ}` spans `⋀^5 (κ → K)`.
   - `{ιMulti (basis ∘ r) | r : Fin 5 ↪o ι}` spans `⋀^5 (ι → K)`.

2. **(B1) biorthogonality ⇒ linear independence** for the family `w_r`.

3. **(Sep) separation lemma**
   - nonzero `x : ⋀^5 N` implies ∃`r`, `ψ_r x ≠ 0`.

4. **(E0) dependent wedge = 0** and optionally **(E0') independent wedge ≠ 0**
   - These can be derived from the basis/spanning results + biorthogonality.

5. A wrapper lemma for matrices, to avoid redoing linear-map conversions:
   - `Matrix.rank A ≤ 4 ↔ (∀ r c, det (A.submatrix r c) = 0)`.

This approach is robust: it replaces “∃ minor ≠ 0” by “nonzero vector in a finite-dimensional space has a nonzero coordinate
in some basis”, where the basis is exactly the `ιMulti` basis and the coordinates are detected by `pairingDual`.

---

## High-level formalization strategy
We follow the approved proof literally:
1. Reindex the block family `Q^(αβγδ) : (Fin 3)^4 → ℝ` into a single tensor `Q : P → P → P → P → ℝ` with `P := Fin n × Fin 3`.
2. Define four mode-unfoldings `unfold m X` as matrices, and define `F` to output **all `5×5` minors** of all unfoldings. This gives the uniform degree bound `d = 5`.
3. Prove:
   - (Forward) if `λ` factors as `u⊗v⊗w⊗x` on `NotIdentical`, then each unfolding of `T := λ•Q` has rank `≤ 4`, hence all `5×5` minors vanish.
   - (Reverse, generic cameras) if all `5×5` minors vanish then each unfolding has rank `≤ 4`. Under additional genericity hypotheses `(G3_m)` plus `rank(B)=4` and `rank(Aα)=3`, derive separations in each index and conclude full factorization.

The only “AG” content is that the genericity conditions are Zariski-open and nonempty; we can encode them as explicit **finite conjunctions of polynomial nonvanishing** (as the file already does for `ZariskiGeneric`), and do not need to develop the full Zariski topology for the final theorem statement.

---

## Step-by-step lemma decomposition (Lean-facing)

### A. Reindexing and unfoldings
**Goal:** work with one tensor on `P := Fin n × Fin 3`.

**Definitions to add (purely definitional):**
1. `abbrev P (n) := Fin n × Fin 3`.
2. `def reindexQ (Q : QFamily n) : (P n → P n → P n → P n → ℝ)` by
   `reindexQ Q (α,i) (β,j) (γ,k) (δ,l) := Q α β γ δ i j k l`.
3. `def unfold1 (X : P→P→P→P→R) : Matrix (P n) (P n × P n × P n) R` (and similarly `unfold2 unfold3 unfold4`).
   - Use product indices, e.g. `unfold1 X p ⟨q,r,s⟩ = X p q r s`.

**Mathlib references:** `Matrix`, product types, `Matrix.det`, `Matrix.minor`.

### B. Constructing `F` as minors of unfoldings (degree 5)
**Core definition:**
- For each mode `m ∈ Fin 4`, and each choice of `5` rows and `5` columns (encoded by injections `Fin 5 → rowIndex` and `Fin 5 → colIndex`), take `det` of the corresponding `5×5` submatrix.

**Lean plan:**
- Define an index type for minors, e.g.
  ```lean
  structure MinorIndex (row col : Type) where
    r : Fin 5 → row
    c : Fin 5 → col
    r_inj : Function.Injective r
    c_inj : Function.Injective c
  ```
- For a matrix `M : Matrix row col ℝ`, define
  ```lean
  def minor5 (idx : MinorIndex row col) : MvPolynomial (QIndex n) ℝ :=
    -- det of the pulled-back 5×5 matrix whose entries are coordinate vars
  ```
  In practice, since `F` is a polynomial in the *input tensor entries*, it is easiest to define `F` directly as an `MvPolynomial (QIndex n) ℝ` using `MvPolynomial.X` variables and `Matrix.det` on a `Matrix (Fin 5) (Fin 5)` built from those variables.

**Deliverables:**
- `def F (n) : PolyMap n (N n)` where `N n` counts (4 modes) × (choices of 5 rows) × (choices of 5 cols).
- `lemma F_degree : PolyMap.UniformDegreeBound 5 (F n)`.

**Mathlib references:**
- `MvPolynomial.totalDegree`, lemmas about `totalDegree_det` are likely missing; expect to add a lemma:
  - `totalDegree_det_le`: if every entry has degree ≤ 1 then det has degree ≤ size.
  This is standard and can be proven by expanding det as a finite sum of monomials.

### C. From minors to rank bounds
We need the equivalence (over a field): all `5×5` minors vanish ↔ `Matrix.rank ≤ 4`.

**Exterior power plan:** Use the addendum blueprint above (`exteriorPower.map`, `exteriorPower.pairingDual`) to avoid a bespoke
“nonzero minor exists” lemma.

### D. Unfolding rank bound for the determinantal tensor `Q`
This is Lemma 1.1 of the solution.

**Set-up:** define the stacked camera matrix
- `B : Matrix (P n) (Fin 4) ℝ` by `B (α,i) c := A α i c`.
- `W : Submodule ℝ (P n → ℝ) := LinearMap.range (Matrix.mulVecLin B)` (column space).

**Key lemma (mode 1):** each column of `unfold1 (reindexQ (constructQ A))` lies in `W`, hence rank ≤ 4.

**Mathlib feasible route:** Laplace expansion along the first row.
- Use `Matrix.det_eq_sum_mul_cofactor` (Laplace along a row/column) to express `det` as dot product of first row with cofactors.

**Proposed lemma:**
```lean
lemma det4_linear_in_first_row
  (r2 r3 r4 : Fin 4 → ℝ) :
  ∃ h : Fin 4 → ℝ, ∀ r1 : Fin 4 → ℝ,
    Matrix.det (fun i j =>
      -- 4×4 matrix with rows r1,r2,r3,r4
    ) = ∑ j, r1 j * h j
```
Then for fixed `(q,r,s)` (i.e. fixed three rows), define `h(q,r,s)` and conclude
`col(q,r,s) = B.mulVec (h(q,r,s))`.

**Deliverables:**
- `lemma rank_unfold1_Q_le4 : Matrix.rank (unfold1 Q) ≤ 4` and similarly for other modes (by symmetry/permuting arguments).

### E. “Diagonal blocks vanish”
Lemma 3.0 of the solution is straightforward and should be fully formalizable.

**Lemma:**
```lean
lemma Q_diag_block_eq_zero
  (A : Fin n → Matrix3x4) (α : Fin n)
  (i j k l : Fin 3) :
  constructQ A α α α α i j k l = 0
```
**Reason:** In `stackedRowsMatrix A α α α α i j k l`, among four rows chosen from only three rows of `A α`, two coincide; determinant is 0.

**Mathlib references:**
- Lemmas: `Matrix.det_eq_zero_of_row_eq` or `Matrix.det_eq_zero_of_duplicate_rows` (may need to use `Matrix.det_eq_zero_of_eq` after proving two row functions equal).

### F. Forward direction (factorable λ ⇒ rank bounds ⇒ F(T)=0)
**Implement:**
- Define `D(u)` as diagonal scaling on `P n` that scales the `α`-block by `u α`:
  `D (u : Fin n → ℝ) : Matrix (P n) (P n) ℝ := Matrix.diagonal (fun (α,i) => u α)`.
  (Note: this already repeats across `i : Fin 3`.)
- Show scaling identity (ignoring diagonal blocks via Lemma E):
  ```lean
  T = (modewiseScale u v w x) Q
  ```
  where `modewiseScale` is implemented by multiplying entries by `u α * v β * w γ * x δ`.
- Prove unfoldings transform by left/right multiplication by diagonal matrices; hence rank is preserved.

**Mathlib references:**
- `Matrix.rank_mul_le`, `Matrix.rank_mul_le_left`, `Matrix.rank_mul_le_right`.

### G. Reverse direction: generic hypotheses and separation of variables
This is the technically heaviest part.

#### G1. Strengthen genericity: what `ZariskiGeneric` must include
The current file’s `ZariskiGeneric` only enforces “all 3×3 minors of each camera are nonzero”.
The proof also needs:
1. `rank(B)=4` where `B : Matrix (P n) (Fin 4) ℝ` is the stacked matrix.
2. `rank(A α)=3` for all `α` (already morally implied, but we want it as an explicit lemma).
3. The spanning hypotheses `(G3_m)` for `m=1,2,3,4`:
   For each mode `m` and each triple of camera indices **not all equal**, a finite set of `27` columns of `unfold m Q` spans `W`.

**Recommendation:** redefine/replace `ZariskiGeneric` with a *problem-9-specific* predicate:
```lean
def ZariskiGeneric9 (A : Fin n → Matrix3x4) : Prop :=
  (∀ α, Matrix.rank (A α) = 3) ∧
  Matrix.rank (stackedB A) = 4 ∧
  G3_1 A ∧ G3_2 A ∧ G3_3 A ∧ G3_4 A
```
where each conjunct is expressible as a finite conjunction of polynomial nonvanishings:
- `rank(A α)=3` can be encoded as “∃ injective cols : Fin 3 → Fin 4, det(submatrix) ≠ 0” (a finite disjunction).
- `rank(B)=4` can be encoded as “∃ injective rows : Fin 4 → P, det(4×4 submatrix) ≠ 0”.
- `G3_m` can be encoded as “∃ 4 columns among the 27 whose images in `W` are independent”, again a finite disjunction of `4×4` determinants.

This keeps fidelity to “Zariski-generic” while matching the proof’s actual needs.
(If desired later, one can prove `ZariskiGeneric9` is nonempty by formalizing the explicit witnesses in `solution.md`, but the theorem statement itself only needs the implication from the predicate.)

#### G2. Column-space identification from rank ≤ 4
Fix a triple `(β,γ,δ)` not all equal. Consider the 27 columns in mode 1.

**Lemma (using G3_1):** those columns of `unfold1 Q` span `W`.
Then in `T = λ•Q`, the corresponding columns are scaled by a block-diagonal invertible map `D_{βγδ}` (since all `λ_{αβγδ} ≠ 0`). Hence they span `D_{βγδ} W`.

Now use `rank(unfold1 T) ≤ 4` and `dim(W)=4` to conclude
`colspace(unfold1 T) = D_{βγδ} W`.

**Mathlib references:**
- `Matrix.rank` vs `Submodule.finrank` of range of `mulVecLin`.
- Lemma needed: `rank_eq_finrank_range_mulVecLin` (exists in some form).

#### G3. Rigidity lemma (block-scalar stabilizer)
We need Lemma 4.2 from the solution.

**Lean statement proposal:**
```lean
lemma blockScalar_stabilizer_rigidity
  (A : Fin n → Matrix3x4)
  (hB : Matrix.rank (stackedB A) = 4)
  (hA : ∀ α, Matrix.rank (A α) = 3)
  (s : Fin n → ℝ)
  (hstab : (diagBlockScalar s) •ₗ W = W) :
  (∀ α β, s α = s β)
```
where `diagBlockScalar s : (P n →ₗ[ℝ] P n)` scales basis vectors for `(α,i)` by `s α`.

**Proof plan in Lean:**
1. From `hB`, get that `B : (Fin 4 →ₗ) (P n →)` is injective, hence a linear equivalence between `Fin 4 → ℝ` and `W`.
2. Convert `hstab` into existence of `R : (Fin 4 →ₗ[ℝ] Fin 4)` with `M ∘ₗ B = B ∘ₗ R`.
   - This uses that `M` maps `range(B)` to itself, so you can conjugate by the equivalence.
3. Restrict to each camera block: for each `α`, the block equation is `s α • A α = A α ⬝ R`.
4. Transpose: `Rᵀ ⬝ (A α)ᵀ = s α • (A α)ᵀ`. Thus `range((A α)ᵀ) ⊆ eigenspace(Rᵀ, s α)`.
5. From `rank(A α)=3`, obtain `finrank (range (A α)ᵀ) = 3`, hence `finrank (eigenspace (Rᵀ) (s α)) ≥ 3`.
6. If `s α ≠ s β`, use `LinearMap.eigenspace_disjoint` to get
   `finrank (eigenspace sα ⊔ eigenspace sβ) = finrank eig(sα) + finrank eig(sβ) ≥ 6`, contradiction since ambient space has finrank 4.

**Mathlib references likely useful:**
- `LinearMap.eigenspace`, `LinearMap.eigenspace_disjoint`, `FiniteDimensional.finrank_*` lemmas.
- `Matrix.rank_transpose`.

#### G4. Algebraic propagation to full factorization
Once we have the three separations (mode 1 gives dependence `u_α`, mode 2 gives `v_β`, mode 3 gives `w_γ`), the remaining tensor algebra is elementary.

**Implement as lemmas on functions:**
1. From mode 1: `∃ u μ, ∀ α β γ δ, NotAllEq β γ δ → λ α β γ δ = u α * μ β γ δ`.
2. From mode 2: `∃ v ν, ...`.
3. Combine to obtain `∃ u v ρ, ∀ α β γ δ, γ ≠ δ → λ α β γ δ = u α * v β * ρ γ δ`.
4. Use mode 3 to split `ρ γ δ = w γ * x δ` for `γ ≠ δ`.
5. Extend to `γ = δ` off the full diagonal using `n ≥ 5` to pick distinct indices.

**Mathlib level:** pure rewriting + field division; best to work with `ℝˣ` units as in statement (avoid explicit `≠0` denominators).

---

## Feasibility assessment (what is already in Mathlib vs likely new lemmas)

### Likely already available / straightforward
- Building unfoldings as `Matrix` and computing minors as determinants.
- Lemma “duplicate rows ⇒ det = 0”.
- Rank inequalities under multiplication by diagonal matrices.
- Basic `LinearMap.range` / `Submodule.span` manipulations.

### Potential gaps (plan to add local lemmas)
1. **Degree bound for determinants in `MvPolynomial`** (`totalDegree` ≤ size).
2. **Rank ≤ k ↔ all (k+1)-minors vanish** for general finite index types; the addendum outlines an exterior-power route.
3. **Extracting `R` from `M(range B)=range B`** in a clean way (conjugation via an equivalence `Fin 4 ≃ₗ W`).
4. Some finrank bookkeeping for eigenspaces over `ℝ`.

All of these are standard linear algebra facts; if Mathlib lacks a direct lemma, they can be proven in a few pages without axioms.

---

## Notes on redefining/strengthening `ZariskiGeneric`
The current definition in `problem9_formalisation.lean` is a *specific* Zariski-open condition (“all 3×3 minors of each camera are nonzero”). The approved proof needs additional Zariski-open conditions (rank(B)=4, and the spanning conditions `(G3_m)`).

Two acceptable approaches (recommend #1):
1. **Strengthen the definition** to `ZariskiGeneric9` as above, i.e. a conjunction of explicit nonvanishing of finitely many determinants (hence Zariski-open and nonempty, witnessed by the explicit cameras in `solution.md`). Then restate theorem `nine` with `ZariskiGeneric9`.
2. Keep current `ZariskiGeneric`, but prove a lemma `ZariskiGeneric A → (rank(B)=4 ∧ G3_m …)`; this is less realistic because it requires deriving very specific genericity consequences from an arbitrary open condition.

Approach #1 matches the informal “Zariski-generic” usage: we may choose any nonempty Zariski-open condition sufficient for the argument.

## 2026-02-09 implementation update
- Added `problem9/solution.lean` with proved lemmas for `5×5` square matrices over a field:
  - `rank_eq_five_of_det_ne_zero`
  - `det_eq_zero_of_rank_le_four`
  - `not_rank_le_four_of_det_ne_zero`
- This gives the core determinant/rank bridge used in `5×5` minor arguments.
- Still missing: full rectangular statement `(∀ injective f g, det (A.submatrix f g) = 0) ↔ A.rank ≤ 4`.

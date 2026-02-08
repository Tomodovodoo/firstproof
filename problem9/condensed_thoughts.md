# Problem 9 — condensed thoughts

## Restatement
Let `n ≥ 5`. For Zariski-generic matrices `A^(1), …, A^(n) ∈ ℝ^{3×4}`, define tensors
`Q^(αβγδ) ∈ ℝ^{3×3×3×3}` by

`Q^(αβγδ)_{i j k ℓ} = det [ A^(α)(i,:); A^(β)(j,:); A^(γ)(k,:); A^(δ)(ℓ,:) ]`,

where the bracket is the `4×4` matrix obtained by stacking the four chosen `1×4` rows.

The question asks for a **uniform** degree bound `d` and, for each `n`, a polynomial map `F` in the
entries of the scaled family `λ_(αβγδ) Q^(αβγδ)` whose vanishing is equivalent to the existence of
`u,v,w,x : Fin n → ℝˣ` with
`λ_(αβγδ) = u_α v_β w_γ x_δ` on indices `(α,β,γ,δ)` that are not all equal (and `λ` is supported
exactly on those indices).

## Requirements (Lean)
- No `axiom`/`constant` declarations; only the proof of the main theorem may be `sorry`.
- Polynomial maps represented by coordinate polynomials `MvPolynomial`, with a degree bound via
  `MvPolynomial.totalDegree`.
- `F` depends on `n` but not on the particular generic input `A`.
- “Zariski-generic” expressed as an explicit nonvanishing predicate on polynomial evaluations.

## Status
All definitions are in place (`constructQ`, `ZariskiGeneric`, `PolyMap`, degree bound). In the Lean
file, “Zariski-generic” is an explicit Zariski-open condition: all `3×3` minors of each
`A^(i) : ℝ^{3×4}` are nonzero. The theorem `nine` is stated; its proof remains `by sorry`.

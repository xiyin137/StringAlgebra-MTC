# MTC Module TODO

## Status (2026-02-26)

- `lake build StringAlgebra.MTC` passes.
- Proof-gap count: **16 theorem-level `sorry` markers** in `StringAlgebra/MTC`.
- No local MTC assumption-bundle/axiom-class wrappers remain (`*Axioms`, `*Assumptions`, `RibbonSphericalAxiom` removed).
- Open debt is represented directly at theorem sites.
- `FusionCategory.lean` now includes both-sided vacuum normalization infrastructure
  (`fusionCoeff_vacuum_*`, `fusionCoeff_right_vacuum_*` including Kronecker forms),
  so downstream S-matrix/modular proofs can rewrite vacuum legs without extra ad-hoc lemmas.
- `FusionCategory.lean` now also includes explicit rigid-adjunction infrastructure
  (`homTensorAdjointEquiv`, `homTensorAdjointDualIdxEquiv`) and a `MonoidalLinear`-gated
  finrank transport layer (`homTensorAdjointLinearEquiv`,
  `finrank_hom_tensor_eq_finrank_hom_tensor_rightDual`,
  `finrank_hom_tensor_eq_finrank_hom_tensor_dualIdx`,
  `fusionCoeff_eq_finrank_hom_tensor_rightDual`,
  `fusionCoeff_eq_finrank_hom_tensor_dualIdx`,
  `fusionCoeff_dualIdx_right_eq_finrank_hom_tensor_dualDualIdx`) to support
  future closure of `fusionCoeff_frobenius` without assumption bundles.
- Remaining `FusionCategory` theorem gaps now carry explicit closure-route comments
  (monoidal-linearity derivation + rigid-adjunction finrank transport + dual-index
  involutivity transport), so no hidden design-level assumptions are being introduced.
- Remaining `Spherical` theorem gaps now also carry explicit closure-route comments
  (`qdim_dual` via duality transport of traces, `qdim_unit` via unit zigzag
  normalization with pivotal transport, `qdim_tensor` via tensor-trace
  multiplicativity), with theorem-local `sorry` only.
- Remaining `SMatrix` theorem gaps now also carry explicit closure-route comments
  (trace-symmetry transport for monodromy swap, nonvanishing contradiction route
  for `totalDimSq`, fusion-character identity route for `quantumDim_fusion`, and
  orthogonality derivation route via trace/dual-index transport), with theorem-local
  `sorry` only.
- Remaining `ModularTensorCategory` theorem gaps now also carry explicit
  closure-route comments (`sMatrix_squared` via orthogonality + dual-index transport,
  `modular_relation` via `(ST)^3` expansion and Gauss-sum collapse), with
  theorem-local `sorry` only.
- Remaining `Verlinde` theorem gaps now also carry explicit closure-route comments
  (`verlinde_formula` via orthogonality/modular inversion + denominator nonvanishing,
  `sMatrix_diagonalizes_fusion` via Verlinde substitution + sum exchange +
  orthogonality evaluation), with theorem-local `sorry` only.
- Remaining `FusionPF` theorem gaps now also carry explicit closure-route comments
  (`fpDimCandidate_pos` via Perron-Frobenius positivity extraction,
  `fpDimCandidate_fusion` via PF eigencharacter/fusion-operator identification),
  with theorem-local `sorry` only.

## Proof-Gap Inventory (16)

1. `Spherical.lean`
- `qdim_dual`
- `qdim_unit`
- `qdim_tensor`

2. `FusionCategory.lean`
- `fusionCoeff_assoc`
- `fusionCoeff_frobenius`
- `fusionCoeff_dual_swap`

3. `SMatrix.lean`
- `sMatrixEnd_symmetric`
- `totalDimSq_ne_zero`
- `quantumDim_fusion`
- `sMatrix_orthogonality`

4. `ModularTensorCategory.lean`
- `sMatrix_squared`
- `modular_relation`

5. `Verlinde.lean`
- `verlinde_formula`
- `sMatrix_diagonalizes_fusion`

6. `FusionPF.lean`
- `fpDimCandidate_pos`
- `fpDimCandidate_fusion`

## Smuggling Cleanup Completed

1. Removed `MTC/Assumptions.lean` and all bundle classes (`FoundationAssumptions`, `ModularAssumptions`, `DevelopmentAssumptions`).
2. Removed theorem-wrapper axiom classes from core files:
- `SphericalDimAxioms`
- `FusionRuleAxioms`
- `SMatrixAxioms`
- `ModularDataAxioms`
- `VerlindeAxioms`
- `PerronFrobeniusPosAxiom`, `PerronFrobeniusFusionAxiom`, `PerronFrobeniusAxioms`
3. Removed ribbon spherical assumption shim:
- `RibbonSphericalAxiom`
- `toSphericalCategory`
4. Updated `DevelopmentHarness.lean` to consume direct theorem-gap interfaces.
5. Removed bridge assumption-bundle layer earlier (`Bridge/Assumptions.lean`) and kept bridge hypotheses theorem-local.

## Build-Verified Import Surface

Top-level MTC entry is now:
- `FoundationLayer`
- `FusionLayer`
- `ModularLayer`
- `DevelopmentHarness`
- `Bridge.Layer`

(no assumption-bundle import)

## Closure Order (Recommended)

1. `Spherical.lean`
- prove `qdim_unit`, `qdim_dual`, `qdim_tensor`

2. `FusionCategory.lean`
- derive associativity/Frobenius/dual-swap from semisimple tensor-Hom infrastructure

3. `SMatrix.lean`
- prove end-valued symmetry and orthogonality, then total-dimension non-vanishing and fusion-character identity

4. `ModularTensorCategory.lean`
- prove `S²` charge-conjugation and `(ST)^3` relation

5. `Verlinde.lean`
- derive Verlinde and diagonalization from established modular identities

6. `FusionPF.lean`
- discharge PF candidate positivity and fusion character theorems

7. `Bridge/VOAToMTC.lean` has no theorem-level `sorry`; bridge interfaces now require explicit VOA analytic hypotheses at theorem call sites.

## Remaining Dependency DAG (Formal)

The remaining theorem-level goals close in the following dependency order.

1. `FusionCategory.lean`
- `fusionCoeff_assoc`
  Required by matrix product linear-combination identities used downstream in `FusionMatrices`, `SMatrix`, and `Verlinde`.
- `fusionCoeff_frobenius`
  Required for dual-index substitutions in S-matrix orthogonality and Verlinde manipulations.
- `fusionCoeff_dual_swap`
  Required for duality-symmetry rewrites in modular and Verlinde expressions.

2. `Spherical.lean`
- `qdim_unit`
  Base normalization for quantum dimensions.
- `qdim_dual`
  Needed for dual-object dimension substitutions.
- `qdim_tensor`
  Needed for multiplicative dimension manipulations in modular identities.

3. `SMatrix.lean`
- `sMatrixEnd_symmetric`
  End(𝟙)-valued symmetry foundation.
- `totalDimSq_ne_zero`
  Nondegeneracy scalar used by vacuum normalization and modular inversion steps.
- `quantumDim_fusion`
  Character relation from fusion coefficients to quantum dimensions.
- `sMatrix_orthogonality`
  Core orthogonality relation feeding `S^2` and Verlinde.

4. `ModularTensorCategory.lean`
- `sMatrix_squared`
  Uses orthogonality + dual-index rewrites to identify charge conjugation.
- `modular_relation`
  Uses S/T identities and Gauss sum to establish projective modular relation.

5. `Verlinde.lean`
- `verlinde_formula`
  Uses previous modular identities and nonvanishing denominators.
- `sMatrix_diagonalizes_fusion`
  Derived equivalent diagonalization statement.

6. `FusionPF.lean`
- `fpDimCandidate_pos`
- `fpDimCandidate_fusion`
  PF-analytic closure layer (Fin-indexed forms are already proved transports).

No additional assumption bundles/classes should be introduced to close this DAG; remaining debt must stay theorem-local (`sorry`) until each node is proved from existing core definitions and lemmas.

## Audit Commands

```bash
rg -n '^\s*sorry\b' StringAlgebra/MTC --glob '*.lean'
rg -n '^\s*class\s+.*(Axioms|Assumptions|Axiom)' StringAlgebra/MTC --glob '*.lean'
lake build StringAlgebra.MTC
```

# Proof Ideas: SMatrix.lean

## Status (2026-02-26)

Proved:
- `sMatrix_symmetric` (k-valued via end-valued symmetry reduction)
- `quantumDim_vacuum`

Open theorem-level gaps:
- `sMatrixEnd_symmetric`
- `totalDimSq_ne_zero`
- `quantumDim_fusion`
- `sMatrix_orthogonality`

## Main Blocker

`SMatrix.sMatrixEnd_symmetric` is the key upstream identity.

## Suggested Order

1. Add cyclicity/conjugation lemmas for categorical trace in `Trace.lean`.
2. Prove `sMatrixEnd_symmetric`.
3. Prove `sMatrix_orthogonality`.
4. Derive `totalDimSq_ne_zero` and `quantumDim_fusion`.

# Proof Ideas: FusionSpectral.lean

## Current status

Implemented in `FusionSpectral.lean`:
- `leftFusionSpectralRadius` / `leftFusionSpectralRadiusByFin`
- `fpDimCandidate` / `fpDimCandidateByFin`
- reindexing compatibility (`leftFusionSpectralRadiusByFin_eq`,
  `fpDimCandidateByFin_finOfIdx`)
- vacuum normalization under canonical indexing:
  `leftFusionSpectralRadius_unit = 1`,
  `fpDimCandidate_unit = 1`

The current file gives a consistent spectral-radius based FPdim candidate API,
but does not yet prove Perron-Frobenius positivity/uniqueness results.

Related matrix infrastructure now available:
- braided commutativity of fusion matrices (Idx, `k`, and Fin-indexed forms),
  which is the algebraic prerequisite for simultaneous diagonalization-style
  arguments in semisimple/modular settings.

## Next proof layer (Perron-Frobenius)

Target statements:
1. For each `i`, `leftFusionMatrixByFin i` has a nonnegative real form
   admitting a Perron eigenvalue/eigenvector.
2. The Perron eigenvalue equals the spectral radius.
3. The Perron eigenvector is unique up to scaling under irreducibility.

Likely strategy:
- Use `leftFusionMatrixByFinNat` for entrywise nonnegativity.
- Transfer to a real/complex matrix representation compatible with existing
  spectral tools.
- Add an explicit irreducibility contract first if categorical irreducibility
  is not yet available from current assumptions.

## Architectural note

Keep spectral/PF statements in `FusionSpectral.lean` (or a sibling
`FusionPF.lean`) rather than `FusionMatrices.lean`, so matrix-algebraic
packaging remains independent of analytic dependencies.

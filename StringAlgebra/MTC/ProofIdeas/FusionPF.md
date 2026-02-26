# Proof Ideas: FusionPF.lean

## Status (2026-02-26)

Open theorem-level gaps:
- `fpDimCandidate_pos`
- `fpDimCandidate_fusion`

No PF assumption classes remain.

## Proof Plan

1. Establish positivity of spectral-radius candidates from nonnegative fusion matrices.
2. Prove fusion-character identity for `fpDimCandidate`.
3. Keep Fin-indexed forms as proved transports from base PF statements.

## Structural Direction

- Keep algebraic matrix facts in `FusionMatrices`/`FusionSpectral`.
- Keep PF analytic lemmas in `FusionPF` (or split into `FusionPF/Core`, `FusionPF/Perron`, `FusionPF/Character`).

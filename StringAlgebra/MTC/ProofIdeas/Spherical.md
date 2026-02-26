# Proof Ideas: Spherical.lean

## Status (2026-02-26)

Open theorem-level gaps:
- `qdim_dual`
- `qdim_unit`
- `qdim_tensor`

No `SphericalDimAxioms` wrapper remains.

## Proof Plan

1. Prove `qdim_unit` first using unit exact-pairing normalization.
2. Prove `qdim_dual` via trace-duality bridge plus sphericality.
3. Prove `qdim_tensor` from partial-trace multiplicativity and pivotal monoidality.

## Notes

Keep these as direct theorem proofs; do not reintroduce class-level proof contracts.

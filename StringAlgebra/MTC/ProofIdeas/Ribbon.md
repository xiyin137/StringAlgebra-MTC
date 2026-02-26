# Proof Ideas: Ribbon.lean

## Status (2026-02-26)

Proved:
- `twist_unit`
- `toPivotalCategory` construction
- `pivotalIso_naturality`
- `pivotalIso_leftDuality`
- `pivotalIso_leftDuality_dual`
- Drinfeld helpers (`drinfeldIsoIso_eval`, `drinfeldIsoIso_coeval`, `drinfeldIsoIso_naturality`)

No sphericality shim remains (`RibbonSphericalAxiom`/`toSphericalCategory` removed).
Any future spherical-from-ribbon result should be introduced as a theorem proof, not an assumption class.

## Remaining Target

- Add a direct theorem proving sphericality of the canonical pivotal structure,
  then derive a concrete `SphericalCategory` instance from that theorem.

## Suggested Proof Route

1. Normalize left/right traces using existing Drinfeld+tutorial twist lemmas.
2. Prove a reusable monodromy-normalization identity for trace terms.
3. Conclude `leftTrace f = rightTrace f` for all endomorphisms.
4. Only after theorem proof is complete, expose a non-smuggled instance.

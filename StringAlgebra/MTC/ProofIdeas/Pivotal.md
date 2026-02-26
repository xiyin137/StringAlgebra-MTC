# Proof Ideas: Pivotal.lean

## Status (2026-02-25)

`leftRightDualIso` is now proved without ad-hoc inverse chases.

## Implemented approach

1. Build an induced exact pairing `ExactPairing Xᘁ X` from the pivotal structure:
   - `coevaluation := η_ Xᘁ (Xᘁ)ᘁ ≫ (Xᘁ ◁ j_X⁻¹)`
   - `evaluation := (j_X ▷ Xᘁ) ≫ ε_ Xᘁ (Xᘁ)ᘁ`
2. Discharge the two exact-pairing triangle axioms by rewriting
   `pivotalIso_leftDuality` and `pivotalIso_leftDuality_dual` through unitor
   cancellation (`congrArg` with `(ρ_ _).hom` / `(λ_ _).hom` on both sides).
3. Invoke `leftDualIso` uniqueness between:
   - the canonical pairing `ExactPairing (ᘁX) X`
   - the induced pairing above

This yields `(ᘁX) ≅ (Xᘁ)` with inverse laws provided by Mathlib’s
`leftDualIso`, eliminating both previous sorrys.

## Reuse pattern

When constructing duality isomorphisms from structural axioms:
- prefer "build exact pairing + apply dual uniqueness"
- avoid hand-proving `hom_inv_id`/`inv_hom_id` unless no uniqueness theorem applies.

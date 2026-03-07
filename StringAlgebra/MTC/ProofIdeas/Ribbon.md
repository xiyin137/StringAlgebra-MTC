# Proof Ideas: Ribbon.lean

## Status (2026-03-06)

Proved:
- `twist_unit`
- `toPivotalCategory` construction (all fields proved, NO sorry)
- `pivotalIso_naturality`
- `pivotalIso_leftDuality`
- `pivotalIso_leftDuality_dual`
- `pivotalIso_dual_compatibility` ← **NEWLY PROVED**
- Drinfeld helpers (`drinfeldIsoIso_eval`, `drinfeldIsoIso_coeval`, `drinfeldIsoIso_naturality`)
- Monodromy helpers (`coeval_twist_sq_monodromy`, `eval_twist_sq_monodromy`,
  `eval_twist_monodromy_cancel`, `rightAdjointMate_twist_inv`)

No sphericality shim remains (`RibbonSphericalAxiom`/`toSphericalCategory` removed).
Any future spherical-from-ribbon result should be introduced as a theorem proof, not an assumption class.

## Completed: pivotalIso_dual_compatibility

### Definition correction

The original definition `j = θ⁻¹ ≫ u` was WRONG for dual compatibility.
The correct definition is `j = θ ≫ u` (i.e., `pivotalIso X := twist X ≪≫ drinfeldIsoIso X`).

With `j = θ⁻¹ ≫ u`, dual compatibility requires `θ⁴ = 𝟙` (false in general).
With `j = θ ≫ u`, it reduces to `θ ≫ θ⁻² = θ⁻¹` (always true).

### Proof structure

The equation: `j_{Xᘁ}.hom = (j_X.inv)ᘁ` where `j_X = θ_X ≫ u_X`.

1. **Eval-testing** via `whiskerRight_eval_cancel`:
   Test both sides ▷ (Xᘁ)ᘁ ≫ ε_ (Xᘁ)ᘁ ((Xᘁ)ᘁ)ᘁ.

2. **LHS**: `drinfeldIsoIso_eval Xᘁ` gives `θ ▷ _ ≫ β ≫ ε_dual`

3. **RHS**: `comp_rightAdjointMate` + `rightAdjointMate_comp_evaluation` +
   `rightAdjointMate_twist_inv` gives `θ⁻¹ ▷ _ ≫ Xᘁ ◁ u⁻¹ ≫ ε`

4. **Convert ε_dual**: Invert `drinfeldIsoIso_eval` to express
   `ε_ Xᘁ (Xᘁ)ᘁ = u⁻¹ ▷ Xᘁ ≫ β ≫ ε_ X Xᘁ`

5. **Braiding naturality**: `← braiding_naturality_right_assoc` converts
   `β ≫ u⁻¹ ▷ Xᘁ` to `Xᘁ ◁ u⁻¹ ≫ β`

6. **Whisker exchange** (←): commute `θ ▷ _` past `Xᘁ ◁ u⁻¹`

7. **eval_twist_monodromy_cancel**: the key identity
   `θ ▷ X ≫ c² ≫ ε = θ⁻¹ ▷ X ≫ ε`
   (derived from `eval_twist_sq_monodromy` by pre-composing with θ⁻¹)

8. **Whisker exchange**: commute back to match RHS

### Helper lemmas added

- `rightAdjointMate_twist_inv`: `(θ_X⁻¹)ᘁ = θ_{Xᘁ}⁻¹`
- `eval_twist_monodromy_cancel`: `θ ▷ X ≫ c² ≫ ε = θ⁻¹ ▷ X ≫ ε`

## Remaining Target: Ribbon → Spherical bridge

Prove `leftTrace f = rightTrace f` for all endomorphisms in a ribbon category.

**Proof sketch**:
- leftTrace f = η_{Xᘁ} ≫ Xᘁ ◁ j⁻¹ ≫ Xᘁ ◁ f ≫ ε_X
- rightTrace f = η_X ≫ f ▷ Xᘁ ≫ j ▷ Xᘁ ≫ ε_{Xᘁ}
- Substitute j = θ ≫ u and use:
  - drinfeldIsoIso_eval/coeval to replace u ↔ braiding
  - twist_naturality to move θ past f
  - eval_twist_sq_monodromy/coeval_twist_sq_monodromy for monodromy normalization
  - Exact pairing zigzag identities to close

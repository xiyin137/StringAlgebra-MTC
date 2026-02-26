/-
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringAlgebra.MTC.BraidedFusion
import StringAlgebra.MTC.Ribbon
import StringAlgebra.MTC.Endomorphism

/-!
# Ribbon Fusion Categories

A ribbon fusion category combines the structure of a braided fusion category
with the twist (ribbon element) of a ribbon category. This is the last step
before imposing the non-degeneracy condition that defines a modular tensor
category.

## Main Definitions

* `RibbonFusionCategory` - Braided fusion + twist
* `twistValue` - The twist eigenvalue θ_i for a simple object X_i
* `tMatrix` - The T-matrix (diagonal matrix of twist eigenvalues)

## References

* [V. Turaev, *Quantum Invariants of Knots and 3-Manifolds*]
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*]
-/

namespace StringAlgebra.MTC

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v₁ u₁

/-- A ribbon fusion category: a braided fusion category with a ribbon (twist)
    structure. This provides the S-matrix, T-matrix, and all the data needed
    for topological quantum field theory. -/
class RibbonFusionCategory (k : Type u₁) [Field k]
    (C : Type u₁) [Category.{v₁} C]
    [MonoidalCategory C] [BraidedCategory C]
    [Preadditive C] [Linear k C] [MonoidalPreadditive C]
    [HasFiniteBiproducts C] [RigidCategory C]
    extends BraidedFusionCategory k C, RibbonCategory C

variable {k : Type u₁} [Field k]
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
variable [Preadditive C] [Linear k C] [MonoidalPreadditive C]
variable [HasFiniteBiproducts C] [RigidCategory C]
variable [RibbonFusionCategory k C]

namespace RibbonFusionCategory

/-! ### Twist values as scalars -/

section ScalarTwist

variable [IsAlgClosed k] [HasKernels C]

/-- The twist eigenvalue θ_i for a simple object X_i.

    Since X_i is simple, End(X_i) ≅ k (by Schur's lemma over an algebraically
    closed field), so the twist θ_{X_i} : X_i → X_i can be identified with
    a scalar in k.

    In TQFT, θ_i = e^{2πi h_i} where h_i is the conformal weight (topological
    spin) of the anyon corresponding to X_i. -/
noncomputable def twistValue (i : FusionCategory.Idx (k := k) (C := C)) : k :=
  scalarOfEndSimple i (RibbonCategory.twist (FusionCategory.simpleObj i)).hom

/-- The twist eigenvalue of the vacuum is 1 (the vacuum has trivial spin). -/
theorem twistValue_vacuum :
    twistValue (C := C) (k := k) FusionCategory.unitIdx = 1 := by
  unfold twistValue
  -- Transfer twist on simpleObj unitIdx to twist on 𝟙_ C via unitIdx_iso
  have h : (RibbonCategory.twist
      (FusionCategory.simpleObj (k := k) (C := C) FusionCategory.unitIdx)).hom = 𝟙 _ := by
    have nat := RibbonCategory.twist_naturality
      (FusionCategory.unitIdx_iso (k := k) (C := C)).hom
    rw [RibbonCategory.twist_unit, Category.comp_id] at nat
    -- nat : unitIdx_iso.hom = θ ≫ unitIdx_iso.hom
    rw [← cancel_mono (FusionCategory.unitIdx_iso (k := k) (C := C)).hom, Category.id_comp]
    exact nat.symm
  rw [h]
  -- scalarOfEndSimple unitIdx (𝟙 _) = 1 by Schur's lemma
  have : scalarOfEndSimple (k := k) (C := C) FusionCategory.unitIdx
      (𝟙 (FusionCategory.simpleObj FusionCategory.unitIdx)) = 1 := by
    simp only [scalarOfEndSimple, scalarOfEndo_id]
  exact this

/-- The T-matrix: T_{ij} = δ_{ij} · θ_i.

    This is one of the two generators of the projective SL(2,ℤ) action
    on the modular data (the other being the S-matrix). -/
noncomputable def tMatrix (i j : FusionCategory.Idx (k := k) (C := C)) : k :=
  if i = j then twistValue (C := C) i else 0

/-- The T-matrix is diagonal. -/
theorem tMatrix_diagonal (i j : FusionCategory.Idx (k := k) (C := C))
    (h : i ≠ j) :
    tMatrix (C := C) (k := k) i j = 0 := by
  simp [tMatrix, h]

/-- The T-matrix diagonal entry is the twist value. -/
theorem tMatrix_diag (i : FusionCategory.Idx (k := k) (C := C)) :
    tMatrix (C := C) (k := k) i i = twistValue i := by
  simp [tMatrix]

end ScalarTwist

/-- The monodromy on X ⊗ Y relates to twists via:
    c²_{X,Y} = (θ_X⁻¹ ⊗ θ_Y⁻¹) ∘ θ_{X⊗Y}

    This is a direct consequence of the ribbon axiom twist_tensor. -/
theorem monodromy_eq_twist_ratio (X Y : C) :
    BraidedFusionCategory.monodromy X Y =
    ((RibbonCategory.twist X).inv ⊗ₘ (RibbonCategory.twist Y).inv) ≫
      (RibbonCategory.twist (X ⊗ Y)).hom := by
  -- From twist_tensor: θ_{X⊗Y} = (θ_X ⊗ₘ θ_Y) ≫ β ≫ β
  -- So β ≫ β = (θ_X ⊗ₘ θ_Y)⁻¹ ≫ θ_{X⊗Y} = (θ_X⁻¹ ⊗ₘ θ_Y⁻¹) ≫ θ_{X⊗Y}
  have h := RibbonCategory.twist_tensor X Y
  -- h : (twist (X ⊗ Y)).hom = ((twist X).hom ⊗ₘ (twist Y).hom) ≫ β ≫ β
  unfold BraidedFusionCategory.monodromy
  -- Goal: β ≫ β = (θ_X⁻¹ ⊗ₘ θ_Y⁻¹) ≫ θ_{X⊗Y}
  rw [h]
  simp

end RibbonFusionCategory

end StringAlgebra.MTC

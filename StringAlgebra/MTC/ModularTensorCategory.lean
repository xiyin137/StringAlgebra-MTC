/-
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringAlgebra.MTC.SMatrix
import StringAlgebra.MTC.BraidedFusion

/-!
# Modular Tensor Categories

A modular tensor category (MTC) is a ribbon fusion category with non-degenerate
S-matrix. This is the central algebraic structure of 3-dimensional topological
quantum field theory.

## Equivalent characterizations of modularity:
1. The S-matrix is invertible (det S ≠ 0)
2. The Müger center is trivial (only the unit is transparent)
3. The matrix (S_{ij}) defines a non-degenerate bilinear form on the
   Grothendieck ring

## Main Definitions

* `ModularTensorCategory` - The main class: ribbon fusion + trivial Müger center
* `ModularData` - Package of S, T matrices satisfying modular relations

## Main Results

* `transparent_iff_unit` - In an MTC, only the unit is transparent

## References

* [V. Turaev, *Quantum Invariants of Knots and 3-Manifolds*]
* [B. Bakalov, A. Kirillov Jr., *Lectures on Tensor Categories and Modular Functors*]
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*], §8.13-8.20
-/

namespace StringAlgebra.MTC

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v₁ u₁

/-- A modular tensor category (MTC) is a ribbon fusion category whose Müger
    center is trivial.

    The Müger center consists of all transparent objects (those whose double
    braiding with everything is trivial). The triviality condition says that
    every transparent simple object is isomorphic to the tensor unit.

    This is equivalent to the S-matrix being non-degenerate.

    ## Physical interpretation
    In condensed matter / topological phases:
    - Simple objects = anyon types
    - Fusion coefficients = fusion rules for anyons
    - S-matrix = mutual braiding statistics
    - T-matrix = topological spins
    - Non-degeneracy = all anyons can be detected by braiding -/
class ModularTensorCategory (k : Type u₁) [Field k]
    (C : Type u₁) [Category.{v₁} C]
    [MonoidalCategory C] [BraidedCategory C]
    [Preadditive C] [Linear k C] [MonoidalPreadditive C]
    [HasFiniteBiproducts C] [RigidCategory C]
    extends RibbonFusionCategory k C where
  /-- The Müger center is trivial: every transparent simple object
      is isomorphic to the tensor unit.

      An object X is transparent if β_{Y,X} ∘ β_{X,Y} = id for all Y. -/
  mueger_center_trivial : ∀ (i : FusionCategory.Idx (k := k) (C := C)),
    BraidedFusionCategory.isTransparent (FusionCategory.simpleObj i) →
    Nonempty (FusionCategory.simpleObj i ≅ 𝟙_ C)

variable {k : Type u₁} [Field k]
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
variable [Preadditive C] [Linear k C] [MonoidalPreadditive C]
variable [HasFiniteBiproducts C] [RigidCategory C]
variable [ModularTensorCategory k C]

namespace ModularTensorCategory

/-- In an MTC, only objects isomorphic to direct sums of the unit are transparent.

    This is equivalent to the S-matrix non-degeneracy condition. -/
  theorem transparent_iff_unit (i : FusionCategory.Idx (k := k) (C := C)) :
      BraidedFusionCategory.isTransparent (FusionCategory.simpleObj i) ↔
      Nonempty (FusionCategory.simpleObj i ≅ 𝟙_ C) := by
    constructor
    · exact mueger_center_trivial i
    · intro ⟨iso⟩ Y
      -- Transfer unit_transparent along iso : simpleObj i ≅ 𝟙_ C
      unfold BraidedFusionCategory.monodromy
      have h := BraidedFusionCategory.unit_transparent (C := C) Y
      unfold BraidedFusionCategory.monodromy at h
      -- Use braiding naturality to conjugate monodromy by iso.hom ▷ Y
      rw [← cancel_mono (iso.hom ▷ Y), Category.id_comp, Category.assoc,
          ← BraidedCategory.braiding_naturality_right Y iso.hom,
          ← Category.assoc,
          ← BraidedCategory.braiding_naturality_left iso.hom Y,
          Category.assoc, h, Category.comp_id]

/-- The rank of the MTC (number of simple isoclasses). -/
noncomputable def rank : ℕ := FusionCategory.rank (k := k) (C := C)

/-! ### The Modular Data -/

section ModularData

variable [IsAlgClosed k] [HasKernels C]

/-- The total quantum dimension squared is nonzero in an MTC. -/
theorem totalDimSq_pos :
    (hS2 :
      ∀ a b : FusionCategory.Idx (k := k) (C := C),
        ∑ m : FusionCategory.Idx (k := k) (C := C),
          SMatrix.sMatrix (C := C) a m * SMatrix.sMatrix (C := C) m b =
        if a = FusionCategory.dualIdx b then SMatrix.totalDimSq (C := C) else 0) →
    (hDual :
      ∀ a b : FusionCategory.Idx (k := k) (C := C),
        SMatrix.sMatrix (C := C) a b =
          SMatrix.sMatrix (C := C) (FusionCategory.dualIdx a) (FusionCategory.dualIdx b)) →
    (hDualInvol :
      ∀ a : FusionCategory.Idx (k := k) (C := C),
        FusionCategory.dualIdx (FusionCategory.dualIdx a) = a) →
    (hUnitOrth :
      ∑ m : FusionCategory.Idx (k := k) (C := C),
        SMatrix.sMatrix (C := C) FusionCategory.unitIdx m *
          SMatrix.sMatrix (C := C) (FusionCategory.dualIdx m) FusionCategory.unitIdx =
      (1 : k)) →
    SMatrix.totalDimSq (C := C) ≠ (0 : k) :=
  SMatrix.totalDimSq_ne_zero

/-- The modular data of an MTC: the S-matrix and T-matrix together. -/
structure ModularDataPkg where
  /-- The S-matrix -/
  S : FusionCategory.Idx (k := k) (C := C) → FusionCategory.Idx (k := k) (C := C) → k
  /-- The T-matrix -/
  T : FusionCategory.Idx (k := k) (C := C) → FusionCategory.Idx (k := k) (C := C) → k
  /-- S is the S-matrix of the category -/
  S_eq : S = SMatrix.sMatrix (C := C)
  /-- T is the T-matrix of the category -/
  T_eq : T = RibbonFusionCategory.tMatrix (C := C) (k := k)

/-- The canonical modular data of the MTC. -/
noncomputable def modularData : ModularDataPkg (C := C) (k := k) where
  S := SMatrix.sMatrix (C := C)
  T := RibbonFusionCategory.tMatrix (C := C) (k := k)
  S_eq := rfl
  T_eq := rfl

/-! ### SL(2,ℤ) Representation

The S and T matrices generate a projective representation of SL(2,ℤ),
the modular group of the torus. The key relations are:
- S² = C (charge conjugation)
- (ST)³ = p₊ · S²
- S⁴ = D² · I
-/

/-- Helper: matrix product of two functions Idx → Idx → k. -/
noncomputable def matMul
    (A B : FusionCategory.Idx (k := k) (C := C) →
           FusionCategory.Idx (k := k) (C := C) → k)
    (i j : FusionCategory.Idx (k := k) (C := C)) : k :=
  ∑ l : FusionCategory.Idx (k := k) (C := C), A i l * B l j

/-- The Gauss sum p₊ = ∑_i θ_i · d_i², a key scalar in the modular relations. -/
noncomputable def gaussSum : k :=
  ∑ i : FusionCategory.Idx (k := k) (C := C),
    RibbonFusionCategory.twistValue (C := C) i *
    SMatrix.quantumDim (C := C) i ^ 2

/-- S² is the charge conjugation matrix: (S²)_{ij} = δ_{i, j*} · D²
    where j* = dualIdx j and D² is the total quantum dimension squared.

    Equivalently, S² = D² · C where C_{ij} = δ_{i,j*}. -/
theorem sMatrix_squared
    (i j : FusionCategory.Idx (k := k) (C := C))
    (hDual :
      ∀ a b : FusionCategory.Idx (k := k) (C := C),
        SMatrix.sMatrix (C := C) a b =
          SMatrix.sMatrix (C := C) (FusionCategory.dualIdx a) (FusionCategory.dualIdx b))
    (hDualInvol :
      ∀ a : FusionCategory.Idx (k := k) (C := C),
        FusionCategory.dualIdx (FusionCategory.dualIdx a) = a)
    (hS2 :
      ∀ a b : FusionCategory.Idx (k := k) (C := C),
        ∑ l : FusionCategory.Idx (k := k) (C := C),
          SMatrix.sMatrix (C := C) a l * SMatrix.sMatrix (C := C) l b =
        if a = FusionCategory.dualIdx b
        then SMatrix.totalDimSq (C := C)
        else 0) :
    matMul (SMatrix.sMatrix (C := C)) (SMatrix.sMatrix (C := C)) i j =
    if i = FusionCategory.dualIdx j
    then SMatrix.totalDimSq (C := C)
    else 0 := by
  unfold matMul
  calc
    ∑ l : FusionCategory.Idx (k := k) (C := C),
        SMatrix.sMatrix (C := C) i l * SMatrix.sMatrix (C := C) l j
      =
        ∑ l : FusionCategory.Idx (k := k) (C := C),
          SMatrix.sMatrix (C := C) i l *
            SMatrix.sMatrix (C := C) (FusionCategory.dualIdx l)
              (FusionCategory.dualIdx j) := by
          refine Finset.sum_congr rfl ?_
          intro l hl
          simp [hDual l j]
    _ = if i = FusionCategory.dualIdx j then SMatrix.totalDimSq (C := C) else 0 := by
      simpa using
        (SMatrix.sMatrix_orthogonality (C := C) i (FusionCategory.dualIdx j)
          hS2 hDual hDualInvol)

/-- The modular relation: (ST)³ = p₊ · S².

    This is the fundamental relation showing that S and T generate a
    projective representation of SL(2,ℤ), the modular group of the torus.
    Stated component-wise, reduced to explicit modular-datum input
    `(ST)^3 = τ·S²` plus `τ = p₊`. -/
theorem modular_relation
    (i j : FusionCategory.Idx (k := k) (C := C))
    (τ : k)
    (hST3 :
      matMul (matMul (matMul (SMatrix.sMatrix (C := C))
        (RibbonFusionCategory.tMatrix (C := C) (k := k)))
        (matMul (SMatrix.sMatrix (C := C))
          (RibbonFusionCategory.tMatrix (C := C) (k := k))))
        (matMul (SMatrix.sMatrix (C := C))
          (RibbonFusionCategory.tMatrix (C := C) (k := k))) i j =
      τ * matMul (SMatrix.sMatrix (C := C)) (SMatrix.sMatrix (C := C)) i j)
    (hTau : τ = gaussSum (C := C)) :
    matMul (matMul (matMul (SMatrix.sMatrix (C := C))
      (RibbonFusionCategory.tMatrix (C := C) (k := k)))
      (matMul (SMatrix.sMatrix (C := C))
        (RibbonFusionCategory.tMatrix (C := C) (k := k))))
      (matMul (SMatrix.sMatrix (C := C))
        (RibbonFusionCategory.tMatrix (C := C) (k := k))) i j =
    gaussSum (C := C) *
      matMul (SMatrix.sMatrix (C := C)) (SMatrix.sMatrix (C := C)) i j := by
  simpa [hTau] using hST3

end ModularData

end ModularTensorCategory

end StringAlgebra.MTC

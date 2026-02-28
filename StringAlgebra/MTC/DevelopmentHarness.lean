import StringAlgebra.MTC.FoundationLayer
import StringAlgebra.MTC.FusionLayer
import StringAlgebra.MTC.ModularLayer
import StringAlgebra.MTC.FusionPF

/-!
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

-- Disable diamond-causing braided-derived rigid instances.
attribute [-instance] CategoryTheory.BraidedCategory.rightRigidCategoryOfLeftRigidCategory
attribute [-instance] CategoryTheory.BraidedCategory.leftRigidCategoryOfRightRigidCategory
attribute [-instance] CategoryTheory.BraidedCategory.rigidCategoryOfRightRigidCategory
attribute [-instance] CategoryTheory.BraidedCategory.rigidCategoryOfLeftRigidCategory

/-!
# Development Harness

This module is a lightweight integration harness for the current
theorem-gap development mode.

It checks that key results across foundational, modular, and Verlinde layers
remain simultaneously usable while proof obligations are tracked explicitly
at theorem sites.
-/

namespace StringAlgebra.MTC

open CategoryTheory MonoidalCategory CategoryTheory.Limits
open scoped ENNReal

universe v₁ u₁

namespace DevelopmentHarness

variable {k : Type u₁} [Field k]
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
variable [Preadditive C] [Linear k C] [MonoidalPreadditive C]
variable [HasFiniteBiproducts C] [RigidCategory C]
variable [ModularTensorCategory k C]

theorem qdim_unit [SphericalCategory C]
    (hunit : rightDim (C := C) (𝟙_ C) = 𝟙 (𝟙_ C)) :
    dim (C := C) (𝟙_ C) = 𝟙 (𝟙_ C) :=
  StringAlgebra.MTC.qdim_unit (C := C) hunit

theorem qdim_dual
    [SphericalCategory C]
    (X : C)
    (hInv :
      (PivotalCategory.pivotalIso (C := C) (Xᘁ : C)).inv =
        (PivotalCategory.pivotalIso (C := C) X).homᘁ) :
    dim (C := C) Xᘁ = dim X :=
  StringAlgebra.MTC.qdim_dual (C := C) X hInv

theorem qdim_tensor
    [SphericalCategory C]
    (X Y : C)
    (hTensorR : rightDim (C := C) (X ⊗ Y) = rightDim X ≫ rightDim Y) :
    dim (C := C) (X ⊗ Y) = dim X ≫ dim Y :=
  StringAlgebra.MTC.qdim_tensor (C := C) X Y hTensorR

theorem fusion_assoc
    (i j l m : FusionCategory.Idx (k := k) (C := C)) :
    ∑ p, FusionCategory.fusionCoeff (k := k) i j p * FusionCategory.fusionCoeff p l m =
    ∑ q, FusionCategory.fusionCoeff (k := k) j l q * FusionCategory.fusionCoeff i q m :=
  FusionCategory.fusionCoeff_assoc (k := k) (C := C) i j l m

theorem fusion_frobenius
    [CategoryTheory.MonoidalLinear k C]
    (i j m : FusionCategory.Idx (k := k) (C := C)) :
    (hSimpleHomSymm :
      ∀ (a : FusionCategory.Idx (k := k) (C := C)) (X : C),
        Module.finrank k (FusionCategory.simpleObj (k := k) (C := C) a ⟶ X) =
          Module.finrank k (X ⟶ FusionCategory.simpleObj (k := k) (C := C) a)) →
    FusionCategory.fusionCoeff (k := k) i j m =
      FusionCategory.fusionCoeff m (FusionCategory.dualIdx j) i := by
  intro hSimpleHomSymm
  exact FusionCategory.fusionCoeff_frobenius (k := k) (C := C) i j m hSimpleHomSymm

theorem fusion_dual_swap
    [CategoryTheory.MonoidalLinear k C]
    (i j m : FusionCategory.Idx (k := k) (C := C)) :
    (hSimpleHomSymm :
      ∀ (a : FusionCategory.Idx (k := k) (C := C)) (X : C),
        Module.finrank k (FusionCategory.simpleObj (k := k) (C := C) a ⟶ X) =
          Module.finrank k (X ⟶ FusionCategory.simpleObj (k := k) (C := C) a)) →
    FusionCategory.fusionCoeff (k := k) i j m =
      FusionCategory.fusionCoeff (FusionCategory.dualIdx j)
        (FusionCategory.dualIdx i) (FusionCategory.dualIdx m) := by
  intro hSimpleHomSymm
  exact FusionCategory.fusionCoeff_dual_swap (k := k) (C := C) i j m hSimpleHomSymm

theorem fusion_matrix_assoc
    (i j : FusionCategory.Idx (k := k) (C := C)) :
    FusionCategory.leftFusionMatrix (k := k) (C := C) j *
      FusionCategory.leftFusionMatrix (k := k) (C := C) i =
      FusionCategory.leftFusionProductLinearCombination (k := k) (C := C) i j :=
  FusionCategory.leftFusionMatrix_mul_eq_linearCombination (k := k) (C := C) i j

theorem fusion_matrix_comm
    (i j : FusionCategory.Idx (k := k) (C := C)) :
    FusionCategory.leftFusionMatrix (k := k) (C := C) i *
      FusionCategory.leftFusionMatrix (k := k) (C := C) j =
      FusionCategory.leftFusionMatrix (k := k) (C := C) j *
        FusionCategory.leftFusionMatrix (k := k) (C := C) i :=
  FusionCategory.leftFusionMatrix_mul_comm (k := k) (C := C) i j

theorem fusion_matrix_fin_assoc
    (i j : FusionCategory.Idx (k := k) (C := C)) :
    FusionCategory.leftFusionMatrixFin (k := k) (C := C) j *
      FusionCategory.leftFusionMatrixFin (k := k) (C := C) i =
      FusionCategory.leftFusionProductLinearCombinationFin (k := k) (C := C) i j :=
  FusionCategory.leftFusionMatrixFin_mul_eq_linearCombination (k := k) (C := C) i j

theorem fusion_matrix_fin_comm
    (i j : FusionCategory.Idx (k := k) (C := C)) :
    FusionCategory.leftFusionMatrixFin (k := k) (C := C) i *
      FusionCategory.leftFusionMatrixFin (k := k) (C := C) j =
      FusionCategory.leftFusionMatrixFin (k := k) (C := C) j *
        FusionCategory.leftFusionMatrixFin (k := k) (C := C) i :=
  FusionCategory.leftFusionMatrixFin_mul_comm (k := k) (C := C) i j

theorem fusion_linear_combination_comm
    (i j : FusionCategory.Idx (k := k) (C := C)) :
    FusionCategory.leftFusionProductLinearCombination (k := k) (C := C) i j =
      FusionCategory.leftFusionProductLinearCombination (k := k) (C := C) j i :=
  FusionCategory.leftFusionProductLinearCombination_comm (k := k) (C := C) i j

theorem fusion_linear_combination_fin_comm
    (i j : FusionCategory.Idx (k := k) (C := C)) :
    FusionCategory.leftFusionProductLinearCombinationFin (k := k) (C := C) i j =
      FusionCategory.leftFusionProductLinearCombinationFin (k := k) (C := C) j i :=
  FusionCategory.leftFusionProductLinearCombinationFin_comm (k := k) (C := C) i j

theorem fusion_vacuum_kronecker
    [IsAlgClosed k] [HasKernels C]
    [FusionCategory.CanonicalSimpleIndex (k := k) (C := C)]
    (j m : FusionCategory.Idx (k := k) (C := C)) :
    FusionCategory.fusionCoeff (k := k) FusionCategory.unitIdx j m =
      if j = m then 1 else 0 :=
  FusionCategory.fusionCoeff_vacuum_kronecker (k := k) (C := C) j m

theorem fusion_matrix_unit
    [IsAlgClosed k] [HasKernels C]
    [FusionCategory.CanonicalSimpleIndex (k := k) (C := C)] :
    FusionCategory.leftFusionMatrix (k := k) (C := C) FusionCategory.unitIdx = 1 :=
  FusionCategory.leftFusionMatrix_unit (k := k) (C := C)

theorem fusion_matrix_fin_unit
    [IsAlgClosed k] [HasKernels C]
    [FusionCategory.CanonicalSimpleIndex (k := k) (C := C)] :
    FusionCategory.leftFusionMatrixFin (k := k) (C := C) FusionCategory.unitIdx = 1 :=
  FusionCategory.leftFusionMatrixFin_unit (k := k) (C := C)

theorem fin_reindex_roundtrip
    (i : FusionCategory.Idx (k := k) (C := C)) :
    FusionCategory.idxOfFin (k := k) (C := C)
      (FusionCategory.finOfIdx (k := k) (C := C) i) = i := by
  exact FusionCategory.idxOfFin_finOfIdx (k := k) (C := C) i

section ModularLayer

variable [IsAlgClosed k] [HasKernels C]

theorem sMatrix_symmetric
    (i j : FusionCategory.Idx (k := k) (C := C)) :
    SMatrix.sMatrix (C := C) i j = SMatrix.sMatrix (C := C) j i :=
  SMatrix.sMatrix_symmetric (C := C) i j

theorem total_dim_sq_nonzero :
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
  SMatrix.totalDimSq_ne_zero (C := C)

theorem quantum_dim_fusion
    (i j : FusionCategory.Idx (k := k) (C := C))
    (h00 :
      SMatrix.sMatrix (C := C) FusionCategory.unitIdx FusionCategory.unitIdx ≠ (0 : k))
    (hVacuumRowFusion :
      ∀ a b : FusionCategory.Idx (k := k) (C := C),
        SMatrix.sMatrix (C := C) FusionCategory.unitIdx a *
            SMatrix.sMatrix (C := C) FusionCategory.unitIdx b
          =
            SMatrix.sMatrix (C := C) FusionCategory.unitIdx FusionCategory.unitIdx *
              ∑ m : FusionCategory.Idx (k := k) (C := C),
                (FusionCategory.fusionCoeff (k := k) a b m : k) *
                  SMatrix.sMatrix (C := C) FusionCategory.unitIdx m) :
    SMatrix.quantumDim (C := C) i * SMatrix.quantumDim (C := C) j =
      ∑ m : FusionCategory.Idx (k := k) (C := C),
        (FusionCategory.fusionCoeff (k := k) i j m : k) * SMatrix.quantumDim (C := C) m :=
  SMatrix.quantumDim_fusion (C := C) i j h00 hVacuumRowFusion

theorem sMatrix_orthogonality
    (i j : FusionCategory.Idx (k := k) (C := C))
    (hS2 :
      ∀ a b : FusionCategory.Idx (k := k) (C := C),
        ∑ m : FusionCategory.Idx (k := k) (C := C),
          SMatrix.sMatrix (C := C) a m * SMatrix.sMatrix (C := C) m b =
        if a = FusionCategory.dualIdx b then SMatrix.totalDimSq (C := C) else 0)
    (hDual :
      ∀ a b : FusionCategory.Idx (k := k) (C := C),
        SMatrix.sMatrix (C := C) a b =
          SMatrix.sMatrix (C := C) (FusionCategory.dualIdx a) (FusionCategory.dualIdx b))
    (hDualInvol :
      ∀ a : FusionCategory.Idx (k := k) (C := C),
        FusionCategory.dualIdx (FusionCategory.dualIdx a) = a) :
    ∑ m : FusionCategory.Idx (k := k) (C := C),
      SMatrix.sMatrix (C := C) i m * SMatrix.sMatrix (C := C) (FusionCategory.dualIdx m) j =
    if i = j then SMatrix.totalDimSq (C := C) else 0 :=
  SMatrix.sMatrix_orthogonality (C := C) i j hS2 hDual hDualInvol

theorem modular_square
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
    ModularTensorCategory.matMul
      (SMatrix.sMatrix (C := C)) (SMatrix.sMatrix (C := C)) i j =
    if i = FusionCategory.dualIdx j
    then SMatrix.totalDimSq (C := C)
    else 0 :=
  ModularTensorCategory.sMatrix_squared (C := C) i j hDual hDualInvol hS2

theorem modular_st_relation
    (i j : FusionCategory.Idx (k := k) (C := C))
    (τ : k)
    (hST3 :
      ModularTensorCategory.matMul
        (ModularTensorCategory.matMul
          (ModularTensorCategory.matMul
            (SMatrix.sMatrix (C := C))
            (RibbonFusionCategory.tMatrix (C := C) (k := k)))
          (ModularTensorCategory.matMul
            (SMatrix.sMatrix (C := C))
            (RibbonFusionCategory.tMatrix (C := C) (k := k))))
        (ModularTensorCategory.matMul
          (SMatrix.sMatrix (C := C))
          (RibbonFusionCategory.tMatrix (C := C) (k := k))) i j =
      τ *
        ModularTensorCategory.matMul
          (SMatrix.sMatrix (C := C)) (SMatrix.sMatrix (C := C)) i j)
    (hTau : τ = ModularTensorCategory.gaussSum (C := C)) :
    ModularTensorCategory.matMul
      (ModularTensorCategory.matMul
        (ModularTensorCategory.matMul
          (SMatrix.sMatrix (C := C))
          (RibbonFusionCategory.tMatrix (C := C) (k := k)))
        (ModularTensorCategory.matMul
          (SMatrix.sMatrix (C := C))
          (RibbonFusionCategory.tMatrix (C := C) (k := k))))
      (ModularTensorCategory.matMul
        (SMatrix.sMatrix (C := C))
        (RibbonFusionCategory.tMatrix (C := C) (k := k))) i j =
    ModularTensorCategory.gaussSum (C := C) *
      ModularTensorCategory.matMul
        (SMatrix.sMatrix (C := C)) (SMatrix.sMatrix (C := C)) i j :=
  ModularTensorCategory.modular_relation (C := C) i j τ hST3 hTau

theorem verlinde
    (i j m : FusionCategory.Idx (k := k) (C := C))
    (hDiag :
      ∀ a b c : FusionCategory.Idx (k := k) (C := C),
        ∑ x : FusionCategory.Idx (k := k) (C := C),
          SMatrix.sMatrix (C := C) b x *
            (FusionCategory.fusionCoeff (k := k) a c x : k) =
        (SMatrix.sMatrix (C := C) a b /
          SMatrix.sMatrix (C := C) FusionCategory.unitIdx b) *
          SMatrix.sMatrix (C := C) b c)
    (hOrth :
      ∀ a b : FusionCategory.Idx (k := k) (C := C),
        ∑ x : FusionCategory.Idx (k := k) (C := C),
          SMatrix.sMatrix (C := C) a x *
            SMatrix.sMatrix (C := C) (FusionCategory.dualIdx x) b =
        if a = b then (1 : k) else 0)
    (hDual :
      ∀ a b : FusionCategory.Idx (k := k) (C := C),
        SMatrix.sMatrix (C := C) a b =
          SMatrix.sMatrix (C := C) (FusionCategory.dualIdx a) (FusionCategory.dualIdx b))
    (hDualInvol :
      ∀ a : FusionCategory.Idx (k := k) (C := C),
        FusionCategory.dualIdx (FusionCategory.dualIdx a) = a) :
    (FusionCategory.fusionCoeff (k := k) i j m : k) =
    ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
      SMatrix.sMatrix (C := C) i ℓ * SMatrix.sMatrix (C := C) j ℓ *
      SMatrix.sMatrix (C := C) (FusionCategory.dualIdx m) ℓ /
      SMatrix.sMatrix (C := C) FusionCategory.unitIdx ℓ :=
  Verlinde.verlinde_formula (C := C) i j m hDiag hOrth hDual hDualInvol

theorem diagonalization
    (i j j' : FusionCategory.Idx (k := k) (C := C))
    (hVerlinde :
      ∀ a b c : FusionCategory.Idx (k := k) (C := C),
        (FusionCategory.fusionCoeff (k := k) a b c : k) =
          ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
            SMatrix.sMatrix (C := C) a ℓ * SMatrix.sMatrix (C := C) b ℓ *
            SMatrix.sMatrix (C := C) (FusionCategory.dualIdx c) ℓ /
            SMatrix.sMatrix (C := C) FusionCategory.unitIdx ℓ)
    (hOrth :
      ∀ a b : FusionCategory.Idx (k := k) (C := C),
        ∑ m : FusionCategory.Idx (k := k) (C := C),
          SMatrix.sMatrix (C := C) a m *
            SMatrix.sMatrix (C := C) (FusionCategory.dualIdx m) b =
        if a = b then (1 : k) else 0) :
    ∑ m : FusionCategory.Idx (k := k) (C := C),
      SMatrix.sMatrix (C := C) j m *
      (FusionCategory.fusionCoeff (k := k) i j' m : k) =
    (SMatrix.sMatrix (C := C) i j /
      SMatrix.sMatrix (C := C) FusionCategory.unitIdx j) *
      SMatrix.sMatrix (C := C) j j' :=
  Verlinde.sMatrix_diagonalizes_fusion (C := C) i j j' hVerlinde hOrth

end ModularLayer

end DevelopmentHarness

namespace DevelopmentHarnessComplex

variable {C : Type} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C]
variable [HasFiniteBiproducts C] [RigidCategory C]
variable [ModularTensorCategory ℂ C]

theorem fpdim_unit
    [HasKernels C]
    [FusionCategory.CanonicalSimpleIndex (k := ℂ) (C := C)] :
    FusionCategory.fpDimCandidate (C := C) FusionCategory.unitIdx = 1 :=
  FusionCategory.fpDimCandidate_unit (C := C)

theorem fpdim_pos
    (i : FusionCategory.Idx (k := ℂ) (C := C)) :
    0 < FusionCategory.fpDimCandidate (C := C) i :=
  FusionCategory.fpDimCandidate_pos (C := C) i

theorem fpdim_fusion
    (i j : FusionCategory.Idx (k := ℂ) (C := C)) :
    FusionCategory.fpDimCandidate (C := C) i *
      FusionCategory.fpDimCandidate (C := C) j =
      ∑ m : FusionCategory.Idx (k := ℂ) (C := C),
        (FusionCategory.fusionCoeff (k := ℂ) i j m : ℝ≥0∞) *
          FusionCategory.fpDimCandidate (C := C) m :=
  FusionCategory.fpDimCandidate_fusion (C := C) i j

theorem fpdim_fin_pos
    (i : Fin (FusionCategory.rank (k := ℂ) (C := C))) :
    0 < FusionCategory.fpDimCandidateByFin (C := C) i :=
  FusionCategory.fpDimCandidateByFin_pos (C := C) i

end DevelopmentHarnessComplex

end StringAlgebra.MTC

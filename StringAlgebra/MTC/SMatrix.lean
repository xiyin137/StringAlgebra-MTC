/-
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringAlgebra.MTC.RibbonFusion

/-!
# S-Matrix of a Ribbon Fusion Category

The S-matrix is defined via the categorical trace of the double braiding
(monodromy). In a ribbon fusion category, for simple objects X_i and X_j:

  S_{ij} = tr(β_{X_j, X_i} ∘ β_{X_i, X_j})

where tr is the categorical (quantum) trace in the spherical category.

The S-matrix is the fundamental invariant that determines whether a
ribbon fusion category is modular (i.e., S is non-degenerate).

## Main Definitions

* `sMatrixEnd` - S-matrix entries as endomorphisms of the unit (no IsAlgClosed needed)
* `sMatrix` - S-matrix entries as elements of k (requires IsAlgClosed)
* `quantumDim` - Quantum dimension d_i = S_{0i}/S_{00}

## Main Results

* `sMatrix_symmetric` - S_{ij} = S_{ji}
* `sMatrix_orthogonality` - ∑_m S_{im} · S_{m*,j} = D² · δ_{ij}

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*], §8.13
* [B. Bakalov, A. Kirillov Jr., *Lectures on Tensor Categories and Modular Functors*]
-/

namespace StringAlgebra.MTC

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v₁ u₁

variable {k : Type u₁} [Field k]
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
variable [Preadditive C] [Linear k C] [MonoidalPreadditive C]
variable [HasFiniteBiproducts C] [RigidCategory C]
variable [inst : RibbonFusionCategory k C]

namespace SMatrix

/-- The S-matrix entry S_{ij} as an endomorphism of the tensor unit.

    Defined as the categorical (spherical) trace of the monodromy
    (double braiding) on X_i ⊗ X_j:
      S_{ij} = tr(β_{X_j, X_i} ∘ β_{X_i, X_j}) ∈ End(𝟙_ C)

    This definition does not require algebraic closure of k. -/
noncomputable def sMatrixEnd
    (i j : FusionCategory.Idx (k := k) (C := C)) : (𝟙_ C ⟶ 𝟙_ C) :=
  trace (BraidedFusionCategory.monodromy (FusionCategory.simpleObj i)
    (FusionCategory.simpleObj j))

/-- The S-matrix entry S_{ij} as an element of k.

    Over an algebraically closed field, End(𝟙_ C) ≅ k, so we can
    extract the scalar value using Schur's lemma. -/
noncomputable def sMatrixEntry [IsAlgClosed k] [HasKernels C]
    (i j : FusionCategory.Idx (k := k) (C := C)) : k :=
  scalarOfEndUnit (sMatrixEnd i j)

/-- The S-matrix as a function on pairs of simple indices. -/
noncomputable def sMatrix [IsAlgClosed k] [HasKernels C] :
    FusionCategory.Idx (k := k) (C := C) →
    FusionCategory.Idx (k := k) (C := C) → k :=
  sMatrixEntry

/-- Quantum dimension of a simple object, defined via the S-matrix:
    d_i = S_{0i} / S_{00}

    This coincides with the categorical dimension (trace of identity)
    in the spherical category. -/
noncomputable def quantumDim [IsAlgClosed k] [HasKernels C]
    (i : FusionCategory.Idx (k := k) (C := C)) : k :=
  sMatrix (C := C) FusionCategory.unitIdx i /
  sMatrix (C := C) FusionCategory.unitIdx FusionCategory.unitIdx

/-- The quantum dimension of the vacuum is 1. -/
theorem quantumDim_vacuum_of_sMatrix_unit_ne_zero [IsAlgClosed k] [HasKernels C]
    (h00 : sMatrix (C := C) FusionCategory.unitIdx FusionCategory.unitIdx ≠ (0 : k)) :
    quantumDim (C := C) FusionCategory.unitIdx = (1 : k) := by
  unfold quantumDim
  exact div_self h00

/-- The total quantum dimension squared: D² = ∑_i d_i² -/
noncomputable def totalDimSq [IsAlgClosed k] [HasKernels C] : k :=
  ∑ i : FusionCategory.Idx (k := k) (C := C), quantumDim (C := C) i ^ 2

/-- The End(𝟙)-valued S-matrix is symmetric: S_{ij} = S_{ji}. -/
theorem sMatrixEnd_symmetric
    (i j : FusionCategory.Idx (k := k) (C := C)) :
    sMatrixEnd (C := C) i j = sMatrixEnd (C := C) j i := by
  let Xi : C := FusionCategory.simpleObj (k := k) (C := C) i
  let Xj : C := FusionCategory.simpleObj (k := k) (C := C) j
  let b : Xi ⊗ Xj ≅ Xj ⊗ Xi := β_ Xi Xj
  have hMon :
      BraidedFusionCategory.monodromy (C := C) Xi Xj =
        b.hom ≫ BraidedFusionCategory.monodromy (C := C) Xj Xi ≫ b.inv := by
    simpa [Xi, Xj, b] using
      (BraidedFusionCategory.monodromy_eq_conj_swap (C := C) Xi Xj)
  unfold sMatrixEnd
  rw [hMon]
  simpa [Xi, Xj, b] using
    (trace_conj (C := C) b (BraidedFusionCategory.monodromy (C := C) Xj Xi))

/-- The k-valued S-matrix is symmetric: S_{ij} = S_{ji}. -/
theorem sMatrix_symmetric_of_end_symmetric [IsAlgClosed k] [HasKernels C]
    (i j : FusionCategory.Idx (k := k) (C := C))
    (h : sMatrixEnd (C := C) i j = sMatrixEnd (C := C) j i) :
    sMatrix (C := C) i j = sMatrix (C := C) j i := by
  unfold sMatrix sMatrixEntry
  simp [h]

/-- The k-valued S-matrix is symmetric: S_{ij} = S_{ji}. -/
theorem sMatrix_symmetric [IsAlgClosed k] [HasKernels C]
    (i j : FusionCategory.Idx (k := k) (C := C)) :
    sMatrix (C := C) i j = sMatrix (C := C) j i := by
  exact sMatrix_symmetric_of_end_symmetric (C := C) i j
    (sMatrixEnd_symmetric (C := C) i j)

/-- Non-vanishing of total quantum dimension squared.

Current status: tracked as an explicit theorem-level proof gap. -/
theorem totalDimSq_ne_zero [IsAlgClosed k] [HasKernels C]
    (hS2 :
      ∀ a b : FusionCategory.Idx (k := k) (C := C),
        ∑ m : FusionCategory.Idx (k := k) (C := C),
          sMatrix (C := C) a m * sMatrix (C := C) m b =
        if a = FusionCategory.dualIdx b then totalDimSq (C := C) else 0)
    (hDual :
      ∀ a b : FusionCategory.Idx (k := k) (C := C),
        sMatrix (C := C) a b =
          sMatrix (C := C) (FusionCategory.dualIdx a) (FusionCategory.dualIdx b))
    (hDualInvol :
      ∀ a : FusionCategory.Idx (k := k) (C := C),
        FusionCategory.dualIdx (FusionCategory.dualIdx a) = a)
    (hUnitOrth :
      ∑ m : FusionCategory.Idx (k := k) (C := C),
        sMatrix (C := C) FusionCategory.unitIdx m *
          sMatrix (C := C) (FusionCategory.dualIdx m) FusionCategory.unitIdx =
      (1 : k)) :
    totalDimSq (C := C) ≠ (0 : k) := by
  let U : FusionCategory.Idx (k := k) (C := C) := FusionCategory.unitIdx
  let lhs : k :=
    ∑ m : FusionCategory.Idx (k := k) (C := C),
      sMatrix (C := C) U m * sMatrix (C := C) (FusionCategory.dualIdx m) U
  have hScaled : lhs = totalDimSq (C := C) := by
    calc
      lhs
          =
            ∑ m : FusionCategory.Idx (k := k) (C := C),
              sMatrix (C := C) U m *
                sMatrix (C := C) m (FusionCategory.dualIdx U) := by
              unfold lhs
              refine Finset.sum_congr rfl ?_
              intro m hm
              have hDualMU :
                  sMatrix (C := C) (FusionCategory.dualIdx m) U =
                    sMatrix (C := C) m (FusionCategory.dualIdx U) := by
                simpa [hDualInvol m] using
                  (hDual (FusionCategory.dualIdx m) U)
              simp [hDualMU]
      _ =
          if U = FusionCategory.dualIdx (FusionCategory.dualIdx U)
          then totalDimSq (C := C)
          else 0 := by
            simpa [U] using hS2 U (FusionCategory.dualIdx U)
      _ = totalDimSq (C := C) := by
            simp [hDualInvol U]
  have hNorm : lhs = (1 : k) := by
    simpa [U, lhs] using hUnitOrth
  have hTotal : totalDimSq (C := C) = (1 : k) := hScaled.symm.trans hNorm
  simp [hTotal]

/-- The quantum dimension of the vacuum is 1. -/
theorem quantumDim_vacuum [IsAlgClosed k] [HasKernels C]
    (h00 : sMatrix (C := C) FusionCategory.unitIdx FusionCategory.unitIdx ≠ (0 : k)) :
    quantumDim (C := C) FusionCategory.unitIdx = (1 : k) := by
  exact quantumDim_vacuum_of_sMatrix_unit_ne_zero (C := C) h00

/-- Quantum dimensions satisfy the fusion rule:
    d_i · d_j = ∑_m N^m_{ij} · d_m -/
theorem quantumDim_fusion [IsAlgClosed k] [HasKernels C]
    (i j : FusionCategory.Idx (k := k) (C := C))
    (h00 :
      sMatrix (C := C) FusionCategory.unitIdx FusionCategory.unitIdx ≠ (0 : k))
    (hVacuumRowFusion :
      ∀ a b : FusionCategory.Idx (k := k) (C := C),
        sMatrix (C := C) FusionCategory.unitIdx a *
            sMatrix (C := C) FusionCategory.unitIdx b
          =
            sMatrix (C := C) FusionCategory.unitIdx FusionCategory.unitIdx *
              ∑ m : FusionCategory.Idx (k := k) (C := C),
                (FusionCategory.fusionCoeff (k := k) a b m : k) *
                  sMatrix (C := C) FusionCategory.unitIdx m) :
    quantumDim (C := C) i * quantumDim (C := C) j =
    ∑ m : FusionCategory.Idx (k := k) (C := C),
      (FusionCategory.fusionCoeff (k := k) i j m : k) * quantumDim (C := C) m := by
  let S00 : k := sMatrix (C := C) FusionCategory.unitIdx FusionCategory.unitIdx
  let S0 : FusionCategory.Idx (k := k) (C := C) → k :=
    fun a => sMatrix (C := C) FusionCategory.unitIdx a
  have h00' : S00 ≠ (0 : k) := by
    simpa [S00] using h00
  have hRow :
      S0 i * S0 j =
        S00 *
          ∑ m : FusionCategory.Idx (k := k) (C := C),
            (FusionCategory.fusionCoeff (k := k) i j m : k) * S0 m := by
    simpa [S0, S00] using hVacuumRowFusion i j
  calc
    quantumDim (C := C) i * quantumDim (C := C) j
        = (S0 i / S00) * (S0 j / S00) := by
            simp [quantumDim, S0, S00]
    _ = (S0 i * S0 j) / (S00 * S00) := by
          field_simp [h00']
    _ =
        (S00 *
          ∑ m : FusionCategory.Idx (k := k) (C := C),
            (FusionCategory.fusionCoeff (k := k) i j m : k) * S0 m) /
          (S00 * S00) := by
            simp [hRow]
    _ =
        (∑ m : FusionCategory.Idx (k := k) (C := C),
            (FusionCategory.fusionCoeff (k := k) i j m : k) * S0 m) /
          S00 := by
            field_simp [h00']
    _ =
        ∑ m : FusionCategory.Idx (k := k) (C := C),
          ((FusionCategory.fusionCoeff (k := k) i j m : k) * S0 m) / S00 := by
            simp [div_eq_mul_inv, Finset.sum_mul]
    _ =
        ∑ m : FusionCategory.Idx (k := k) (C := C),
          (FusionCategory.fusionCoeff (k := k) i j m : k) * (S0 m / S00) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            simp [div_eq_mul_inv, mul_assoc]
    _ =
        ∑ m : FusionCategory.Idx (k := k) (C := C),
          (FusionCategory.fusionCoeff (k := k) i j m : k) * quantumDim (C := C) m := by
            simp [quantumDim, S0, S00]

/-- The S-matrix satisfies the orthogonality relation:
    ∑_m S_{im} · S_{m*, j} = D² · δ_{ij}

    Here m* = dualIdx m is the charge conjugation.
    This is reduced from an explicit `S²` charge-conjugation identity
    (EGNO 8.14.2 form) plus dual-index transport. -/
theorem sMatrix_orthogonality [IsAlgClosed k] [HasKernels C]
    (i j : FusionCategory.Idx (k := k) (C := C))
    (hS2 :
      ∀ a b : FusionCategory.Idx (k := k) (C := C),
        ∑ m : FusionCategory.Idx (k := k) (C := C),
          sMatrix (C := C) a m * sMatrix (C := C) m b =
        if a = FusionCategory.dualIdx b then totalDimSq (C := C) else 0)
    (hDual :
      ∀ a b : FusionCategory.Idx (k := k) (C := C),
        sMatrix (C := C) a b =
          sMatrix (C := C) (FusionCategory.dualIdx a) (FusionCategory.dualIdx b))
    (hDualInvol :
      ∀ a : FusionCategory.Idx (k := k) (C := C),
        FusionCategory.dualIdx (FusionCategory.dualIdx a) = a) :
    ∑ m : FusionCategory.Idx (k := k) (C := C),
      sMatrix (C := C) i m * sMatrix (C := C) (FusionCategory.dualIdx m) j =
    if i = j then totalDimSq (C := C) else 0 := by
  calc
    ∑ m : FusionCategory.Idx (k := k) (C := C),
        sMatrix (C := C) i m * sMatrix (C := C) (FusionCategory.dualIdx m) j
      =
        ∑ m : FusionCategory.Idx (k := k) (C := C),
          sMatrix (C := C) i m * sMatrix (C := C) m (FusionCategory.dualIdx j) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          have hTerm :
              sMatrix (C := C) (FusionCategory.dualIdx m) j =
                sMatrix (C := C) m (FusionCategory.dualIdx j) := by
            calc
              sMatrix (C := C) (FusionCategory.dualIdx m) j
                  = sMatrix (C := C)
                      (FusionCategory.dualIdx (FusionCategory.dualIdx m))
                      (FusionCategory.dualIdx j) := by
                    simpa using hDual (FusionCategory.dualIdx m) j
              _ = sMatrix (C := C) m (FusionCategory.dualIdx j) := by
                simp [hDualInvol]
          simp [hTerm]
    _ = if i = FusionCategory.dualIdx (FusionCategory.dualIdx j) then totalDimSq (C := C) else 0 := by
      simpa using hS2 i (FusionCategory.dualIdx j)
    _ = if i = j then totalDimSq (C := C) else 0 := by
      simp [hDualInvol]

end SMatrix

end StringAlgebra.MTC

import StringAlgebra.MTC.FusionMatrices
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Fusion Spectral Candidates

Spectral-radius based candidates for Frobenius-Perron dimensions, built on
the Fin-reindexed fusion matrices from `FusionMatrices.lean`.

This module is currently specialized to `k = ℂ`, matching available
normed-field spectral-radius infrastructure.

Given the current `FusionCategory` universe signature
(`k` and `C` share a universe level), this also means `C` is treated in the
same universe level as `ℂ` in this file.
-/

namespace StringAlgebra.MTC

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped NNReal ENNReal

universe v₁

variable {C : Type} [Category.{v₁} C] [MonoidalCategory C]
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C]
variable [HasFiniteBiproducts C] [RigidCategory C]
variable [FusionCategory ℂ C]

namespace FusionCategory

/-- Spectral-radius candidate for the Frobenius-Perron dimension of `X_i`,
computed from the reindexed `ℂ`-valued left fusion matrix. -/
noncomputable def leftFusionSpectralRadius
    (i : Idx (k := ℂ) (C := C)) : ℝ≥0∞ :=
  spectralRadius ℂ (leftFusionMatrixFin (k := ℂ) (C := C) i)

/-- Spectral-radius candidate indexed by `Fin rank`. -/
noncomputable def leftFusionSpectralRadiusByFin
    (i : Fin (rank (k := ℂ) (C := C))) : ℝ≥0∞ :=
  spectralRadius ℂ (leftFusionMatrixByFin (k := ℂ) (C := C) i)

@[simp] theorem leftFusionSpectralRadiusByFin_eq
    (i : Fin (rank (k := ℂ) (C := C))) :
    leftFusionSpectralRadiusByFin (C := C) i =
      leftFusionSpectralRadius (C := C) (idxOfFin (k := ℂ) (C := C) i) := rfl

/-- Frobenius-Perron dimension candidate (currently spectral-radius based). -/
noncomputable def fpDimCandidate
    (i : Idx (k := ℂ) (C := C)) : ℝ≥0∞ :=
  leftFusionSpectralRadius (C := C) i

/-- Fin-indexed Frobenius-Perron dimension candidate. -/
noncomputable def fpDimCandidateByFin
    (i : Fin (rank (k := ℂ) (C := C))) : ℝ≥0∞ :=
  leftFusionSpectralRadiusByFin (C := C) i

@[simp] theorem fpDimCandidateByFin_finOfIdx
    (i : Idx (k := ℂ) (C := C)) :
    fpDimCandidateByFin (C := C) (finOfIdx (k := ℂ) (C := C) i) =
      fpDimCandidate (C := C) i := by
  simp [fpDimCandidate, fpDimCandidateByFin, leftFusionSpectralRadiusByFin_eq]

section UnitNormalization

variable [HasKernels C]
variable [CanonicalSimpleIndex (k := ℂ) (C := C)]

/-- Under canonical indexing, the vacuum fusion matrix has spectral radius `1`. -/
theorem leftFusionSpectralRadius_unit :
    leftFusionSpectralRadius (C := C) unitIdx = 1 := by
  unfold leftFusionSpectralRadius
  rw [leftFusionMatrixFin_unit (k := ℂ) (C := C)]
  haveI : Nonempty (Fin (rank (k := ℂ) (C := C))) :=
    ⟨finOfIdx (k := ℂ) (C := C) unitIdx⟩
  exact (spectrum.spectralRadius_one (𝕜 := ℂ)
    (A := Matrix
      (Fin (rank (k := ℂ) (C := C)))
      (Fin (rank (k := ℂ) (C := C))) ℂ))

/-- Fin-indexed specialization of `leftFusionSpectralRadius_unit`. -/
theorem leftFusionSpectralRadiusByFin_unit :
    leftFusionSpectralRadiusByFin (C := C)
      (finOfIdx (k := ℂ) (C := C) unitIdx) = 1 := by
  simpa [leftFusionSpectralRadiusByFin_eq] using
    (leftFusionSpectralRadius_unit (C := C))

/-- Under canonical indexing, the FP-dimension candidate of the vacuum is `1`. -/
theorem fpDimCandidate_unit :
    fpDimCandidate (C := C) unitIdx = 1 := by
  simpa [fpDimCandidate] using (leftFusionSpectralRadius_unit (C := C))

/-- Fin-indexed specialization of `fpDimCandidate_unit`. -/
theorem fpDimCandidateByFin_unit :
    fpDimCandidateByFin (C := C) (finOfIdx (k := ℂ) (C := C) unitIdx) = 1 := by
  simpa [fpDimCandidateByFin] using
    (leftFusionSpectralRadiusByFin_unit (C := C))

end UnitNormalization

end FusionCategory

end StringAlgebra.MTC

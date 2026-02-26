import StringAlgebra.MTC.FusionSpectral

/-!
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Fusion Perron-Frobenius Layer

Interim theorem layer for Frobenius-Perron dimensions built on
`FusionSpectral.lean`.

Current PF obligations are tracked as explicit theorem-level proof gaps.

This layer is intentionally `ℂ`-specialized for now, matching
`FusionSpectral.lean`.
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

theorem fpDimCandidate_pos
    (i : Idx (k := ℂ) (C := C)) :
    0 < fpDimCandidate (C := C) i := by
  have hPos :
      0 < fpDimCandidate (C := C) i := by
    -- Remaining PF-positivity debt:
    -- extract strict positivity from the Perron-Frobenius eigenvector package
    -- for the nonnegative fusion operator attached to `i`.
    sorry
  exact hPos

theorem fpDimCandidate_fusion
    (i j : Idx (k := ℂ) (C := C)) :
    fpDimCandidate (C := C) i * fpDimCandidate (C := C) j =
      ∑ m : Idx (k := ℂ) (C := C),
        (fusionCoeff (k := ℂ) i j m : ℝ≥0∞) * fpDimCandidate (C := C) m := by
  have hFusion :
      fpDimCandidate (C := C) i * fpDimCandidate (C := C) j =
        ∑ m : Idx (k := ℂ) (C := C),
          (fusionCoeff (k := ℂ) i j m : ℝ≥0∞) * fpDimCandidate (C := C) m := by
    -- Remaining PF-fusion debt:
    -- identify `fpDimCandidate` as a common positive eigencharacter and use
    -- the fusion-matrix action to derive the multiplicative/fusion relation.
    sorry
  exact hFusion

theorem fpDimCandidateByFin_pos
    (i : Fin (rank (k := ℂ) (C := C))) :
    0 < fpDimCandidateByFin (C := C) i := by
  simpa [fpDimCandidateByFin, fpDimCandidate, leftFusionSpectralRadiusByFin_eq] using
    (fpDimCandidate_pos (C := C) (idxOfFin (k := ℂ) (C := C) i))

theorem fpDimCandidateByFin_fusion
    (i j : Fin (rank (k := ℂ) (C := C))) :
    fpDimCandidateByFin (C := C) i * fpDimCandidateByFin (C := C) j =
      ∑ m : Idx (k := ℂ) (C := C),
        (fusionCoeff (k := ℂ)
          (idxOfFin (k := ℂ) (C := C) i)
          (idxOfFin (k := ℂ) (C := C) j)
          m : ℝ≥0∞) *
          fpDimCandidate (C := C) m := by
  simpa [fpDimCandidateByFin, fpDimCandidate, leftFusionSpectralRadiusByFin_eq] using
    (fpDimCandidate_fusion (C := C)
      (idxOfFin (k := ℂ) (C := C) i)
      (idxOfFin (k := ℂ) (C := C) j))

end FusionCategory

end StringAlgebra.MTC

/-
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringAlgebra.MTC.ModularTensorCategory

/-!
# The Verlinde Formula

The Verlinde formula expresses the fusion coefficients of a modular tensor
category in terms of the S-matrix:

  N^m_{ij} = ∑_ℓ (S_{iℓ} · S_{jℓ} · S_{m*,ℓ}) / S_{0ℓ}

This remarkable formula shows that all fusion rules are determined by the
S-matrix alone, which itself encodes the mutual braiding statistics.

## Main Results

* `verlinde_formula` - The Verlinde formula relating N^m_{ij} to S_{ij}
* `sMatrix_diagonalizes_fusion` - The S-matrix diagonalizes fusion matrices
* `dimTQFTSpace` - Dimension of TQFT vector space on genus-g surface

## References

* [E. Verlinde, *Fusion rules and modular transformations in 2D conformal
  field theory*]
* [G. Moore, N. Seiberg, *Classical and quantum conformal field theory*]
* [B. Bakalov, A. Kirillov Jr., *Lectures on Tensor Categories and Modular Functors*]
-/

namespace StringAlgebra.MTC

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v₁ u₁

variable {k : Type u₁} [Field k] [IsAlgClosed k]
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
variable [Preadditive C] [Linear k C] [MonoidalPreadditive C]
variable [HasFiniteBiproducts C] [RigidCategory C]
variable [HasKernels C]
variable [ModularTensorCategory k C]

namespace Verlinde

/-- The Verlinde formula: the fusion coefficients are determined by the S-matrix.

    N^m_{ij} = ∑_ℓ S_{iℓ} · S_{jℓ} · S_{m*,ℓ} / S_{0ℓ}

    This is the most important structure theorem for modular tensor categories.
    It shows that the braiding statistics alone (encoded in S) determine the
    entire fusion ring.

    Here m* = dualIdx m is the charge conjugate of m. -/
theorem verlinde_formula
    (i j m : FusionCategory.Idx (k := k) (C := C)) :
    (FusionCategory.fusionCoeff (k := k) i j m : k) =
    ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
      SMatrix.sMatrix (C := C) i ℓ * SMatrix.sMatrix (C := C) j ℓ *
      SMatrix.sMatrix (C := C) (FusionCategory.dualIdx m) ℓ /
      SMatrix.sMatrix (C := C) FusionCategory.unitIdx ℓ := by
  have hVerlindeExpansion :
      (FusionCategory.fusionCoeff (k := k) i j m : k) =
      ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
        SMatrix.sMatrix (C := C) i ℓ * SMatrix.sMatrix (C := C) j ℓ *
        SMatrix.sMatrix (C := C) (FusionCategory.dualIdx m) ℓ /
        SMatrix.sMatrix (C := C) FusionCategory.unitIdx ℓ := by
    -- Remaining Verlinde debt:
    -- combine S-matrix orthogonality, modular inversion, and nonvanishing
    -- vacuum-column denominators to rewrite fusion coefficients explicitly.
    sorry
  exact hVerlindeExpansion

/-- The S-matrix diagonalizes the fusion rules.

    For each simple i, the fusion matrix N_i (with entries (N_i)_{jm} = N^m_{ij})
    is diagonalized by the S-matrix:

    ∑_m S_{jm} · N^m_{ij'} = (S_{ij} / S_{0j}) · S_{jj'}

    This is equivalent to the Verlinde formula. -/
theorem sMatrix_diagonalizes_fusion
    (i j j' : FusionCategory.Idx (k := k) (C := C)) :
    ∑ m : FusionCategory.Idx (k := k) (C := C),
      SMatrix.sMatrix (C := C) j m *
      (FusionCategory.fusionCoeff (k := k) i j' m : k) =
    (SMatrix.sMatrix (C := C) i j /
     SMatrix.sMatrix (C := C) FusionCategory.unitIdx j) *
    SMatrix.sMatrix (C := C) j j' := by
  have hDiagonalization :
      ∑ m : FusionCategory.Idx (k := k) (C := C),
        SMatrix.sMatrix (C := C) j m *
        (FusionCategory.fusionCoeff (k := k) i j' m : k) =
      (SMatrix.sMatrix (C := C) i j /
       SMatrix.sMatrix (C := C) FusionCategory.unitIdx j) *
      SMatrix.sMatrix (C := C) j j' := by
    -- Remaining diagonalization debt:
    -- substitute Verlinde expansion, exchange finite sums, and evaluate by
    -- S-matrix orthogonality to isolate the eigenvalue ratio `S_{ij}/S_{0j}`.
    sorry
  exact hDiagonalization

/-- The dimension of the TQFT vector space associated to a genus-g surface Σ_g:

    dim V(Σ_g) = ∑_i (S_{0i} / S_{00})^{2-2g} = ∑_i d_i^{2-2g}

    For g = 0 (sphere): dim = 1
    For g = 1 (torus): dim = rank (number of simples)
    For g ≥ 2: given by the formula above -/
noncomputable def dimTQFTSpace (g : ℕ) : k :=
  ∑ i : FusionCategory.Idx (k := k) (C := C),
    (SMatrix.quantumDim (C := C) i) ^ (2 - 2 * (g : ℤ))

/-- The TQFT dimension on the torus (g=1) equals the rank. -/
theorem dimTQFTSpace_torus :
    dimTQFTSpace (C := C) 1 =
    (FusionCategory.rank (k := k) (C := C) : k) := by
  unfold dimTQFTSpace FusionCategory.rank
  -- Exponent: 2 - 2 * 1 = 0, so each term is d_i^0 = 1
  simp only [show (2 : ℤ) - 2 * ((1 : ℕ) : ℤ) = 0 from by norm_num, zpow_zero,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

end Verlinde

end StringAlgebra.MTC

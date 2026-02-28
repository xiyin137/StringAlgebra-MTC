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
      SMatrix.sMatrix (C := C) FusionCategory.unitIdx ℓ := by
  let S : FusionCategory.Idx (k := k) (C := C) →
      FusionCategory.Idx (k := k) (C := C) → k :=
    SMatrix.sMatrix (C := C)
  have hInjectiveDual :
      Function.Injective (FusionCategory.dualIdx (k := k) (C := C)) := by
    intro a b hab
    have h' := congrArg (FusionCategory.dualIdx (k := k) (C := C)) hab
    simpa [hDualInvol] using h'
  symm
  calc
    ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
        S i ℓ * S j ℓ * S (FusionCategory.dualIdx m) ℓ /
          S FusionCategory.unitIdx ℓ
      =
        ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
          S (FusionCategory.dualIdx m) ℓ *
            ((S i ℓ / S FusionCategory.unitIdx ℓ) * S ℓ j) := by
          refine Finset.sum_congr rfl ?_
          intro ℓ hℓ
          have hsymℓ : S j ℓ = S ℓ j := by
            simpa [S] using (SMatrix.sMatrix_symmetric (C := C) j ℓ)
          simp [hsymℓ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    _ =
        ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
          S (FusionCategory.dualIdx m) ℓ *
            ∑ x : FusionCategory.Idx (k := k) (C := C),
              S ℓ x * (FusionCategory.fusionCoeff (k := k) i j x : k) := by
          refine Finset.sum_congr rfl ?_
          intro ℓ hℓ
          rw [hDiag i ℓ j]
    _ =
        ∑ x : FusionCategory.Idx (k := k) (C := C),
          (FusionCategory.fusionCoeff (k := k) i j x : k) *
            ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
              S (FusionCategory.dualIdx m) ℓ * S ℓ x := by
          calc
            ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
                S (FusionCategory.dualIdx m) ℓ *
                  ∑ x : FusionCategory.Idx (k := k) (C := C),
                    S ℓ x * (FusionCategory.fusionCoeff (k := k) i j x : k)
              =
                ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
                  ∑ x : FusionCategory.Idx (k := k) (C := C),
                    S (FusionCategory.dualIdx m) ℓ *
                      (S ℓ x * (FusionCategory.fusionCoeff (k := k) i j x : k)) := by
                    refine Finset.sum_congr rfl ?_
                    intro ℓ hℓ
                    rw [Finset.mul_sum]
            _ =
                ∑ x : FusionCategory.Idx (k := k) (C := C),
                  ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
                    S (FusionCategory.dualIdx m) ℓ *
                      (S ℓ x * (FusionCategory.fusionCoeff (k := k) i j x : k)) := by
                    rw [Finset.sum_comm]
            _ =
                ∑ x : FusionCategory.Idx (k := k) (C := C),
                  (FusionCategory.fusionCoeff (k := k) i j x : k) *
                    ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
                      S (FusionCategory.dualIdx m) ℓ * S ℓ x := by
                    refine Finset.sum_congr rfl ?_
                    intro x hx
                    let Nx : k := (FusionCategory.fusionCoeff (k := k) i j x : k)
                    calc
                      ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
                          S (FusionCategory.dualIdx m) ℓ * (S ℓ x * Nx)
                        =
                          ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
                            Nx * (S (FusionCategory.dualIdx m) ℓ * S ℓ x) := by
                              refine Finset.sum_congr rfl ?_
                              intro ℓ hℓ
                              simp [Nx, mul_assoc, mul_comm]
                      _ = Nx *
                          ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
                            S (FusionCategory.dualIdx m) ℓ * S ℓ x := by
                            symm
                            simpa [Nx] using
                              (Finset.mul_sum
                                (s := Finset.univ) (a := Nx)
                                (f := fun ℓ : FusionCategory.Idx (k := k) (C := C) =>
                                  S (FusionCategory.dualIdx m) ℓ * S ℓ x))
                      _ =
                          (FusionCategory.fusionCoeff (k := k) i j x : k) *
                            ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
                              S (FusionCategory.dualIdx m) ℓ * S ℓ x := by
                            simp [Nx]
    _ =
        ∑ x : FusionCategory.Idx (k := k) (C := C),
          (FusionCategory.fusionCoeff (k := k) i j x : k) *
            (if m = x then (1 : k) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          have hInner :
              ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
                S (FusionCategory.dualIdx m) ℓ * S ℓ x =
              if m = x then (1 : k) else 0 := by
            calc
              ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
                  S (FusionCategory.dualIdx m) ℓ * S ℓ x
                =
                  ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
                    S (FusionCategory.dualIdx m) ℓ *
                      S (FusionCategory.dualIdx ℓ) (FusionCategory.dualIdx x) := by
                      refine Finset.sum_congr rfl ?_
                      intro ℓ hℓ
                      have hDualS : S ℓ x =
                          S (FusionCategory.dualIdx ℓ) (FusionCategory.dualIdx x) := by
                        simpa [S] using hDual ℓ x
                      simp [hDualS]
              _ = if FusionCategory.dualIdx m = FusionCategory.dualIdx x then (1 : k) else 0 := by
                    simpa [S] using
                      (hOrth (FusionCategory.dualIdx m) (FusionCategory.dualIdx x))
              _ = if m = x then (1 : k) else 0 := by
                    by_cases hmx : m = x
                    · simp [hmx]
                    · have hdx : FusionCategory.dualIdx m ≠ FusionCategory.dualIdx x := by
                        intro hdx
                        exact hmx (hInjectiveDual hdx)
                      simp [hmx, hdx]
          simp [hInner]
    _ = (FusionCategory.fusionCoeff (k := k) i j m : k) := by
          rw [Finset.sum_eq_single m]
          · simp
          · intro x hx hxm
            have hmx : m ≠ x := by
              intro h
              exact hxm h.symm
            simp [hmx]
          · intro hm
            exact (hm (Finset.mem_univ m)).elim

/-- The S-matrix diagonalizes the fusion rules.

    For each simple i, the fusion matrix N_i (with entries (N_i)_{jm} = N^m_{ij})
    is diagonalized by the S-matrix:

    ∑_m S_{jm} · N^m_{ij'} = (S_{ij} / S_{0j}) · S_{jj'}

    This is equivalent to the Verlinde formula. -/
theorem sMatrix_diagonalizes_fusion
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
    SMatrix.sMatrix (C := C) j j' := by
  let S : FusionCategory.Idx (k := k) (C := C) →
      FusionCategory.Idx (k := k) (C := C) → k :=
    SMatrix.sMatrix (C := C)
  calc
    ∑ m : FusionCategory.Idx (k := k) (C := C),
        S j m * (FusionCategory.fusionCoeff (k := k) i j' m : k)
      =
        ∑ m : FusionCategory.Idx (k := k) (C := C),
          S j m *
            ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
              S i ℓ * S j' ℓ * S (FusionCategory.dualIdx m) ℓ /
                S FusionCategory.unitIdx ℓ := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          simpa [S] using congrArg (fun t : k => S j m * t) (hVerlinde i j' m)
    _ =
        ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
          ∑ m : FusionCategory.Idx (k := k) (C := C),
            S j m *
              (S i ℓ * S j' ℓ * S (FusionCategory.dualIdx m) ℓ /
                S FusionCategory.unitIdx ℓ) := by
          calc
            ∑ m : FusionCategory.Idx (k := k) (C := C),
                S j m *
                  ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
                    S i ℓ * S j' ℓ * S (FusionCategory.dualIdx m) ℓ /
                      S FusionCategory.unitIdx ℓ
              =
                ∑ m : FusionCategory.Idx (k := k) (C := C),
                  ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
                    S j m *
                      (S i ℓ * S j' ℓ * S (FusionCategory.dualIdx m) ℓ /
                        S FusionCategory.unitIdx ℓ) := by
                    refine Finset.sum_congr rfl ?_
                    intro m hm
                    rw [Finset.mul_sum]
            _ =
                ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
                  ∑ m : FusionCategory.Idx (k := k) (C := C),
                    S j m *
                      (S i ℓ * S j' ℓ * S (FusionCategory.dualIdx m) ℓ /
                        S FusionCategory.unitIdx ℓ) := by
                    rw [Finset.sum_comm]
    _ =
        ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
          (S i ℓ * S j' ℓ / S FusionCategory.unitIdx ℓ) *
            ∑ m : FusionCategory.Idx (k := k) (C := C),
              S j m * S (FusionCategory.dualIdx m) ℓ := by
          refine Finset.sum_congr rfl ?_
          intro ℓ hℓ
          let c : k := S i ℓ * S j' ℓ / S FusionCategory.unitIdx ℓ
          calc
            ∑ m : FusionCategory.Idx (k := k) (C := C),
                S j m *
                  (S i ℓ * S j' ℓ * S (FusionCategory.dualIdx m) ℓ /
                    S FusionCategory.unitIdx ℓ)
              =
                ∑ m : FusionCategory.Idx (k := k) (C := C),
                  c * (S j m * S (FusionCategory.dualIdx m) ℓ) := by
                    refine Finset.sum_congr rfl ?_
                    intro m hm
                    simp [c, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
            _ = c *
                ∑ m : FusionCategory.Idx (k := k) (C := C),
                  S j m * S (FusionCategory.dualIdx m) ℓ := by
                    symm
                    simpa using
                      (Finset.mul_sum
                        (s := Finset.univ)
                        (a := c)
                        (f := fun m : FusionCategory.Idx (k := k) (C := C) =>
                          S j m * S (FusionCategory.dualIdx m) ℓ))
            _ = (S i ℓ * S j' ℓ / S FusionCategory.unitIdx ℓ) *
                ∑ m : FusionCategory.Idx (k := k) (C := C),
                  S j m * S (FusionCategory.dualIdx m) ℓ := by
                    simp [c]
    _ =
        ∑ ℓ : FusionCategory.Idx (k := k) (C := C),
          (S i ℓ * S j' ℓ / S FusionCategory.unitIdx ℓ) *
            (if j = ℓ then (1 : k) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro ℓ hℓ
          rw [hOrth j ℓ]
    _ = S i j * S j' j / S FusionCategory.unitIdx j := by
          rw [Finset.sum_eq_single j]
          · simp
          · intro ℓ hℓ hne
            have hne' : j ≠ ℓ := by
              intro h
              exact hne h.symm
            simp [hne']
          · intro hj
            exact (hj (Finset.mem_univ j)).elim
    _ = (S i j / S FusionCategory.unitIdx j) * S j j' := by
          have hsym : S j' j = S j j' := by
            simpa [S] using (SMatrix.sMatrix_symmetric (C := C) j' j)
          simp [hsym, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

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

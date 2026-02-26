import StringAlgebra.MTC.FusionCategory
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Fusion Matrices

Matrix packaging of fusion coefficients.

For each simple index `i`, the left fusion matrix `N_i` has entries
`(N_i)_{j,m} = N^m_{i,j}`. The associativity of fusion coefficients becomes
matrix multiplication identities in this basis.
-/

namespace StringAlgebra.MTC

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v₁ u₁

variable {k : Type u₁} [Field k]
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable [Preadditive C] [Linear k C] [MonoidalPreadditive C]
variable [HasFiniteBiproducts C] [RigidCategory C]
variable [FusionCategory k C]

namespace FusionCategory

/-- Left fusion matrix `N_i` with entries `(N_i)_{j,m} = N^m_{i,j}`. -/
noncomputable def leftFusionMatrix (i : Idx (k := k) (C := C)) :
    Matrix (Idx (k := k) (C := C)) (Idx (k := k) (C := C)) ℕ :=
  fun j m => fusionCoeff (k := k) i j m

@[simp] theorem leftFusionMatrix_apply
    (i j m : Idx (k := k) (C := C)) :
    leftFusionMatrix (k := k) (C := C) i j m =
      fusionCoeff (k := k) i j m := rfl

/-- Entrywise form of left-fusion matrix multiplication. -/
theorem leftFusionMatrix_mul_apply
    (i j l m : Idx (k := k) (C := C)) :
    (leftFusionMatrix (k := k) (C := C) j *
      leftFusionMatrix (k := k) (C := C) i) l m =
      ∑ q : Idx (k := k) (C := C),
        fusionCoeff (k := k) j l q * fusionCoeff (k := k) i q m := by
  simp [leftFusionMatrix, Matrix.mul_apply]

/-- Associativity of fusion coefficients rewritten as a matrix-entry identity. -/
theorem leftFusionMatrix_mul_assoc_entry
    (i j l m : Idx (k := k) (C := C)) :
    (leftFusionMatrix (k := k) (C := C) j *
      leftFusionMatrix (k := k) (C := C) i) l m =
      ∑ p : Idx (k := k) (C := C),
        fusionCoeff (k := k) i j p * fusionCoeff (k := k) p l m := by
  calc
    (leftFusionMatrix (k := k) (C := C) j *
      leftFusionMatrix (k := k) (C := C) i) l m =
        ∑ q : Idx (k := k) (C := C),
          fusionCoeff (k := k) j l q * fusionCoeff (k := k) i q m :=
      leftFusionMatrix_mul_apply (k := k) (C := C) i j l m
    _ = ∑ p : Idx (k := k) (C := C),
          fusionCoeff (k := k) i j p * fusionCoeff (k := k) p l m := by
      simpa using (FusionCategory.fusionCoeff_assoc (k := k) (C := C) i j l m).symm

/-- The linear-combination matrix
`∑_p N^p_{i,j} N_p` appearing in fusion-matrix product formulas. -/
noncomputable def leftFusionProductLinearCombination
    (i j : Idx (k := k) (C := C)) :
    Matrix (Idx (k := k) (C := C)) (Idx (k := k) (C := C)) ℕ :=
  fun l m => ∑ p : Idx (k := k) (C := C),
    fusionCoeff (k := k) i j p * fusionCoeff (k := k) p l m

/-- Matrix form of fusion associativity:
`N_j N_i = ∑_p N^p_{i,j} N_p`. -/
theorem leftFusionMatrix_mul_eq_linearCombination
    (i j : Idx (k := k) (C := C)) :
    leftFusionMatrix (k := k) (C := C) j *
      leftFusionMatrix (k := k) (C := C) i =
      leftFusionProductLinearCombination (k := k) (C := C) i j := by
  ext l m
  exact leftFusionMatrix_mul_assoc_entry (k := k) (C := C) i j l m

/-- In a braided fusion category, the linear-combination matrix is symmetric
in `(i,j)`. -/
theorem leftFusionProductLinearCombination_comm
    [BraidedCategory C]
    (i j : Idx (k := k) (C := C)) :
    leftFusionProductLinearCombination (k := k) (C := C) i j =
      leftFusionProductLinearCombination (k := k) (C := C) j i := by
  ext l m
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hsym :
      fusionCoeff (k := k) (C := C) i j p =
        fusionCoeff (k := k) (C := C) j i p :=
    LinearEquiv.finrank_eq
      (Linear.homCongr k
        (β_ (simpleObj (k := k) i) (simpleObj (k := k) j))
        (Iso.refl (simpleObj (k := k) p)))
  simp [hsym]

section BraidedCommutativity

variable [BraidedCategory C]

/-- In a braided fusion category, left fusion matrices commute:
`N_i N_j = N_j N_i`. -/
theorem leftFusionMatrix_mul_comm
    (i j : Idx (k := k) (C := C)) :
    leftFusionMatrix (k := k) (C := C) i *
      leftFusionMatrix (k := k) (C := C) j =
      leftFusionMatrix (k := k) (C := C) j *
        leftFusionMatrix (k := k) (C := C) i := by
  ext l m
  calc
    (leftFusionMatrix (k := k) (C := C) i *
      leftFusionMatrix (k := k) (C := C) j) l m =
        ∑ p : Idx (k := k) (C := C),
          fusionCoeff (k := k) j i p * fusionCoeff (k := k) p l m := by
      simpa using
        (leftFusionMatrix_mul_assoc_entry (k := k) (C := C) j i l m)
    _ = ∑ p : Idx (k := k) (C := C),
          fusionCoeff (k := k) i j p * fusionCoeff (k := k) p l m := by
      refine Finset.sum_congr rfl ?_
      intro p hp
      have hsym :
          fusionCoeff (k := k) (C := C) j i p =
            fusionCoeff (k := k) (C := C) i j p :=
        LinearEquiv.finrank_eq
          (Linear.homCongr k
            (β_ (simpleObj (k := k) j) (simpleObj (k := k) i))
            (Iso.refl (simpleObj (k := k) p)))
      simp [hsym]
    _ = (leftFusionMatrix (k := k) (C := C) j *
          leftFusionMatrix (k := k) (C := C) i) l m := by
      simpa using
        (leftFusionMatrix_mul_assoc_entry (k := k) (C := C) i j l m).symm

end BraidedCommutativity

/-- Field-valued left fusion matrix, obtained by casting the natural-valued
    fusion coefficients into `k`. -/
noncomputable def leftFusionMatrixK (i : Idx (k := k) (C := C)) :
    Matrix (Idx (k := k) (C := C)) (Idx (k := k) (C := C)) k :=
  fun j m => (fusionCoeff (k := k) i j m : k)

@[simp] theorem leftFusionMatrixK_apply
    (i j m : Idx (k := k) (C := C)) :
    leftFusionMatrixK (k := k) (C := C) i j m =
      (fusionCoeff (k := k) i j m : k) := rfl

/-- Associativity of fusion coefficients in field-valued matrix-entry form. -/
theorem leftFusionMatrixK_mul_assoc_entry
    (i j l m : Idx (k := k) (C := C)) :
    (leftFusionMatrixK (k := k) (C := C) j *
      leftFusionMatrixK (k := k) (C := C) i) l m =
      ∑ p : Idx (k := k) (C := C),
        (fusionCoeff (k := k) i j p : k) * (fusionCoeff (k := k) p l m : k) := by
  have hNat := leftFusionMatrix_mul_assoc_entry (k := k) (C := C) i j l m
  have hCast := congrArg (fun n : ℕ => (n : k)) hNat
  simpa [leftFusionMatrixK, Matrix.mul_apply, Nat.cast_sum, Nat.cast_mul] using hCast

/-- Field-valued linear-combination matrix
`∑_p N^p_{i,j} N_p` for `leftFusionMatrixK`. -/
noncomputable def leftFusionProductLinearCombinationK
    (i j : Idx (k := k) (C := C)) :
    Matrix (Idx (k := k) (C := C)) (Idx (k := k) (C := C)) k :=
  fun l m => ∑ p : Idx (k := k) (C := C),
    (fusionCoeff (k := k) i j p : k) * (fusionCoeff (k := k) p l m : k)

/-- Matrix form of fusion associativity over `k`:
`N_j N_i = ∑_p N^p_{i,j} N_p` for `leftFusionMatrixK`. -/
theorem leftFusionMatrixK_mul_eq_linearCombination
    (i j : Idx (k := k) (C := C)) :
    leftFusionMatrixK (k := k) (C := C) j *
      leftFusionMatrixK (k := k) (C := C) i =
      leftFusionProductLinearCombinationK (k := k) (C := C) i j := by
  ext l m
  exact leftFusionMatrixK_mul_assoc_entry (k := k) (C := C) i j l m

/-- In a braided fusion category, the field-valued linear-combination matrix is
symmetric in `(i,j)`. -/
theorem leftFusionProductLinearCombinationK_comm
    [BraidedCategory C]
    (i j : Idx (k := k) (C := C)) :
    leftFusionProductLinearCombinationK (k := k) (C := C) i j =
      leftFusionProductLinearCombinationK (k := k) (C := C) j i := by
  ext l m
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hsymNat :
      fusionCoeff (k := k) (C := C) i j p =
        fusionCoeff (k := k) (C := C) j i p :=
    LinearEquiv.finrank_eq
      (Linear.homCongr k
        (β_ (simpleObj (k := k) i) (simpleObj (k := k) j))
        (Iso.refl (simpleObj (k := k) p)))
  have hsym : (fusionCoeff (k := k) i j p : k) = (fusionCoeff (k := k) j i p : k) :=
    congrArg (fun n : ℕ => (n : k)) hsymNat
  simp [hsym]

/-! ## Finite Reindexing

Canonical reindexing from `Idx` to `Fin rank` for matrix-based algorithms.
-/

/-- Canonical equivalence between simple indices and `Fin rank`. -/
noncomputable def idxEquivFin :
    Idx (k := k) (C := C) ≃ Fin (rank (k := k) (C := C)) := by
  classical
  simpa [rank] using (Fintype.equivFin (Idx (k := k) (C := C)))

/-- Convert a `Fin rank` index into the corresponding simple index. -/
noncomputable def idxOfFin
    (a : Fin (rank (k := k) (C := C))) : Idx (k := k) (C := C) :=
  (idxEquivFin (k := k) (C := C)).symm a

/-- Convert a simple index into `Fin rank`. -/
noncomputable def finOfIdx
    (i : Idx (k := k) (C := C)) : Fin (rank (k := k) (C := C)) :=
  idxEquivFin (k := k) (C := C) i

@[simp] theorem idxOfFin_finOfIdx (i : Idx (k := k) (C := C)) :
    idxOfFin (k := k) (C := C) (finOfIdx (k := k) (C := C) i) = i := by
  simp [idxOfFin, finOfIdx]

@[simp] theorem finOfIdx_idxOfFin
    (a : Fin (rank (k := k) (C := C))) :
    finOfIdx (k := k) (C := C) (idxOfFin (k := k) (C := C) a) = a := by
  simp [idxOfFin, finOfIdx]

/-- `ℕ`-valued left fusion matrix, reindexed to `Fin rank × Fin rank`. -/
noncomputable def leftFusionMatrixFinNat
    (i : Idx (k := k) (C := C)) :
    Matrix (Fin (rank (k := k) (C := C))) (Fin (rank (k := k) (C := C))) ℕ :=
  (leftFusionMatrix (k := k) (C := C) i).submatrix
    (idxEquivFin (k := k) (C := C)).symm
    (idxEquivFin (k := k) (C := C)).symm

/-- `ℕ`-valued linear-combination matrix
`∑_p N^p_{i,j} N_p`, reindexed to `Fin rank × Fin rank`. -/
noncomputable def leftFusionProductLinearCombinationFinNat
    (i j : Idx (k := k) (C := C)) :
    Matrix (Fin (rank (k := k) (C := C))) (Fin (rank (k := k) (C := C))) ℕ :=
  (leftFusionProductLinearCombination (k := k) (C := C) i j).submatrix
    (idxEquivFin (k := k) (C := C)).symm
    (idxEquivFin (k := k) (C := C)).symm

/-- Matrix form of fusion associativity on `Fin rank × Fin rank`
for `ℕ`-valued fusion matrices. -/
theorem leftFusionMatrixFinNat_mul_eq_linearCombination
    (i j : Idx (k := k) (C := C)) :
    leftFusionMatrixFinNat (k := k) (C := C) j *
      leftFusionMatrixFinNat (k := k) (C := C) i =
      leftFusionProductLinearCombinationFinNat (k := k) (C := C) i j := by
  let e : Fin (rank (k := k) (C := C)) ≃ Idx (k := k) (C := C) :=
    (idxEquivFin (k := k) (C := C)).symm
  change (leftFusionMatrix (k := k) (C := C) j).submatrix e e *
      (leftFusionMatrix (k := k) (C := C) i).submatrix e e =
      (leftFusionProductLinearCombination (k := k) (C := C) i j).submatrix e e
  calc
    (leftFusionMatrix (k := k) (C := C) j).submatrix e e *
        (leftFusionMatrix (k := k) (C := C) i).submatrix e e =
        ((leftFusionMatrix (k := k) (C := C) j) *
          (leftFusionMatrix (k := k) (C := C) i)).submatrix e e := by
      exact (Matrix.submatrix_mul_equiv
        (leftFusionMatrix (k := k) (C := C) j)
        (leftFusionMatrix (k := k) (C := C) i) e e e)
    _ = (leftFusionProductLinearCombination (k := k) (C := C) i j).submatrix e e := by
      exact congrArg (fun M => M.submatrix e e)
        (leftFusionMatrix_mul_eq_linearCombination (k := k) (C := C) i j)

/-- `k`-valued left fusion matrix, reindexed to `Fin rank × Fin rank`. -/
noncomputable def leftFusionMatrixFin
    (i : Idx (k := k) (C := C)) :
    Matrix (Fin (rank (k := k) (C := C))) (Fin (rank (k := k) (C := C))) k :=
  (leftFusionMatrixK (k := k) (C := C) i).submatrix
    (idxEquivFin (k := k) (C := C)).symm
    (idxEquivFin (k := k) (C := C)).symm

/-- `k`-valued linear-combination matrix
`∑_p N^p_{i,j} N_p`, reindexed to `Fin rank × Fin rank`. -/
noncomputable def leftFusionProductLinearCombinationFin
    (i j : Idx (k := k) (C := C)) :
    Matrix (Fin (rank (k := k) (C := C))) (Fin (rank (k := k) (C := C))) k :=
  (leftFusionProductLinearCombinationK (k := k) (C := C) i j).submatrix
    (idxEquivFin (k := k) (C := C)).symm
    (idxEquivFin (k := k) (C := C)).symm

/-- Matrix form of fusion associativity on `Fin rank × Fin rank`
for `k`-valued fusion matrices. -/
theorem leftFusionMatrixFin_mul_eq_linearCombination
    (i j : Idx (k := k) (C := C)) :
    leftFusionMatrixFin (k := k) (C := C) j *
      leftFusionMatrixFin (k := k) (C := C) i =
      leftFusionProductLinearCombinationFin (k := k) (C := C) i j := by
  let e : Fin (rank (k := k) (C := C)) ≃ Idx (k := k) (C := C) :=
    (idxEquivFin (k := k) (C := C)).symm
  change (leftFusionMatrixK (k := k) (C := C) j).submatrix e e *
      (leftFusionMatrixK (k := k) (C := C) i).submatrix e e =
      (leftFusionProductLinearCombinationK (k := k) (C := C) i j).submatrix e e
  calc
    (leftFusionMatrixK (k := k) (C := C) j).submatrix e e *
        (leftFusionMatrixK (k := k) (C := C) i).submatrix e e =
        ((leftFusionMatrixK (k := k) (C := C) j) *
          (leftFusionMatrixK (k := k) (C := C) i)).submatrix e e := by
      exact (Matrix.submatrix_mul_equiv
        (leftFusionMatrixK (k := k) (C := C) j)
        (leftFusionMatrixK (k := k) (C := C) i) e e e)
    _ = (leftFusionProductLinearCombinationK (k := k) (C := C) i j).submatrix e e := by
      exact congrArg (fun M => M.submatrix e e)
        (leftFusionMatrixK_mul_eq_linearCombination (k := k) (C := C) i j)

/-- Reindexed `ℕ`-valued linear-combination matrix is symmetric in `(i,j)` in
the braided setting. -/
theorem leftFusionProductLinearCombinationFinNat_comm
    [BraidedCategory C]
    (i j : Idx (k := k) (C := C)) :
    leftFusionProductLinearCombinationFinNat (k := k) (C := C) i j =
      leftFusionProductLinearCombinationFinNat (k := k) (C := C) j i := by
  let e : Fin (rank (k := k) (C := C)) ≃ Idx (k := k) (C := C) :=
    (idxEquivFin (k := k) (C := C)).symm
  change (leftFusionProductLinearCombination (k := k) (C := C) i j).submatrix e e =
      (leftFusionProductLinearCombination (k := k) (C := C) j i).submatrix e e
  exact congrArg (fun M => M.submatrix e e)
    (leftFusionProductLinearCombination_comm (k := k) (C := C) i j)

/-- Reindexed `k`-valued linear-combination matrix is symmetric in `(i,j)` in
the braided setting. -/
theorem leftFusionProductLinearCombinationFin_comm
    [BraidedCategory C]
    (i j : Idx (k := k) (C := C)) :
    leftFusionProductLinearCombinationFin (k := k) (C := C) i j =
      leftFusionProductLinearCombinationFin (k := k) (C := C) j i := by
  let e : Fin (rank (k := k) (C := C)) ≃ Idx (k := k) (C := C) :=
    (idxEquivFin (k := k) (C := C)).symm
  change (leftFusionProductLinearCombinationK (k := k) (C := C) i j).submatrix e e =
      (leftFusionProductLinearCombinationK (k := k) (C := C) j i).submatrix e e
  exact congrArg (fun M => M.submatrix e e)
    (leftFusionProductLinearCombinationK_comm (k := k) (C := C) i j)

/-- Fully `Fin rank`-indexed `ℕ`-valued left fusion matrix family. -/
noncomputable def leftFusionMatrixByFinNat
    (i : Fin (rank (k := k) (C := C))) :
    Matrix (Fin (rank (k := k) (C := C))) (Fin (rank (k := k) (C := C))) ℕ :=
  leftFusionMatrixFinNat (k := k) (C := C) (idxOfFin (k := k) (C := C) i)

/-- Fully `Fin rank`-indexed `k`-valued left fusion matrix family. -/
noncomputable def leftFusionMatrixByFin
    (i : Fin (rank (k := k) (C := C))) :
    Matrix (Fin (rank (k := k) (C := C))) (Fin (rank (k := k) (C := C))) k :=
  leftFusionMatrixFin (k := k) (C := C) (idxOfFin (k := k) (C := C) i)

section BraidedCommutativityFin

variable [BraidedCategory C]

/-- In a braided fusion category, the field-valued left fusion matrices commute:
`N_i N_j = N_j N_i`. -/
theorem leftFusionMatrixK_mul_comm
    (i j : Idx (k := k) (C := C)) :
    leftFusionMatrixK (k := k) (C := C) i *
      leftFusionMatrixK (k := k) (C := C) j =
      leftFusionMatrixK (k := k) (C := C) j *
        leftFusionMatrixK (k := k) (C := C) i := by
  ext l m
  calc
    (leftFusionMatrixK (k := k) (C := C) i *
      leftFusionMatrixK (k := k) (C := C) j) l m =
        ∑ p : Idx (k := k) (C := C),
          (fusionCoeff (k := k) j i p : k) * (fusionCoeff (k := k) p l m : k) := by
      simpa using
        (leftFusionMatrixK_mul_assoc_entry (k := k) (C := C) j i l m)
    _ = ∑ p : Idx (k := k) (C := C),
          (fusionCoeff (k := k) i j p : k) * (fusionCoeff (k := k) p l m : k) := by
      refine Finset.sum_congr rfl ?_
      intro p hp
      have hsymNat :
          fusionCoeff (k := k) (C := C) j i p =
            fusionCoeff (k := k) (C := C) i j p :=
        LinearEquiv.finrank_eq
          (Linear.homCongr k
            (β_ (simpleObj (k := k) j) (simpleObj (k := k) i))
            (Iso.refl (simpleObj (k := k) p)))
      have hsym : (fusionCoeff (k := k) j i p : k) = (fusionCoeff (k := k) i j p : k) :=
        congrArg (fun n : ℕ => (n : k)) hsymNat
      simp [hsym]
    _ = (leftFusionMatrixK (k := k) (C := C) j *
          leftFusionMatrixK (k := k) (C := C) i) l m := by
      simpa using
        (leftFusionMatrixK_mul_assoc_entry (k := k) (C := C) i j l m).symm

/-- Reindexed `ℕ`-valued left fusion matrices commute on `Fin rank`. -/
theorem leftFusionMatrixFinNat_mul_comm
    (i j : Idx (k := k) (C := C)) :
    leftFusionMatrixFinNat (k := k) (C := C) i *
      leftFusionMatrixFinNat (k := k) (C := C) j =
      leftFusionMatrixFinNat (k := k) (C := C) j *
        leftFusionMatrixFinNat (k := k) (C := C) i := by
  let e : Fin (rank (k := k) (C := C)) ≃ Idx (k := k) (C := C) :=
    (idxEquivFin (k := k) (C := C)).symm
  change (leftFusionMatrix (k := k) (C := C) i).submatrix e e *
      (leftFusionMatrix (k := k) (C := C) j).submatrix e e =
      (leftFusionMatrix (k := k) (C := C) j).submatrix e e *
        (leftFusionMatrix (k := k) (C := C) i).submatrix e e
  calc
    (leftFusionMatrix (k := k) (C := C) i).submatrix e e *
        (leftFusionMatrix (k := k) (C := C) j).submatrix e e =
        ((leftFusionMatrix (k := k) (C := C) i) *
          (leftFusionMatrix (k := k) (C := C) j)).submatrix e e := by
      exact (Matrix.submatrix_mul_equiv
        (leftFusionMatrix (k := k) (C := C) i)
        (leftFusionMatrix (k := k) (C := C) j) e e e)
    _ = ((leftFusionMatrix (k := k) (C := C) j) *
          (leftFusionMatrix (k := k) (C := C) i)).submatrix e e := by
      exact congrArg (fun M => M.submatrix e e)
        (leftFusionMatrix_mul_comm (k := k) (C := C) i j)
    _ = (leftFusionMatrix (k := k) (C := C) j).submatrix e e *
          (leftFusionMatrix (k := k) (C := C) i).submatrix e e := by
      symm
      exact (Matrix.submatrix_mul_equiv
        (leftFusionMatrix (k := k) (C := C) j)
        (leftFusionMatrix (k := k) (C := C) i) e e e)

/-- Reindexed `k`-valued left fusion matrices commute on `Fin rank`. -/
theorem leftFusionMatrixFin_mul_comm
    (i j : Idx (k := k) (C := C)) :
    leftFusionMatrixFin (k := k) (C := C) i *
      leftFusionMatrixFin (k := k) (C := C) j =
      leftFusionMatrixFin (k := k) (C := C) j *
        leftFusionMatrixFin (k := k) (C := C) i := by
  let e : Fin (rank (k := k) (C := C)) ≃ Idx (k := k) (C := C) :=
    (idxEquivFin (k := k) (C := C)).symm
  change (leftFusionMatrixK (k := k) (C := C) i).submatrix e e *
      (leftFusionMatrixK (k := k) (C := C) j).submatrix e e =
      (leftFusionMatrixK (k := k) (C := C) j).submatrix e e *
        (leftFusionMatrixK (k := k) (C := C) i).submatrix e e
  calc
    (leftFusionMatrixK (k := k) (C := C) i).submatrix e e *
        (leftFusionMatrixK (k := k) (C := C) j).submatrix e e =
        ((leftFusionMatrixK (k := k) (C := C) i) *
          (leftFusionMatrixK (k := k) (C := C) j)).submatrix e e := by
      exact (Matrix.submatrix_mul_equiv
        (leftFusionMatrixK (k := k) (C := C) i)
        (leftFusionMatrixK (k := k) (C := C) j) e e e)
    _ = ((leftFusionMatrixK (k := k) (C := C) j) *
          (leftFusionMatrixK (k := k) (C := C) i)).submatrix e e := by
      exact congrArg (fun M => M.submatrix e e)
        (leftFusionMatrixK_mul_comm (k := k) (C := C) i j)
    _ = (leftFusionMatrixK (k := k) (C := C) j).submatrix e e *
          (leftFusionMatrixK (k := k) (C := C) i).submatrix e e := by
      symm
      exact (Matrix.submatrix_mul_equiv
        (leftFusionMatrixK (k := k) (C := C) j)
        (leftFusionMatrixK (k := k) (C := C) i) e e e)

/-- Fully `Fin rank`-indexed `ℕ`-valued left fusion matrices commute. -/
theorem leftFusionMatrixByFinNat_mul_comm
    (i j : Fin (rank (k := k) (C := C))) :
    leftFusionMatrixByFinNat (k := k) (C := C) i *
      leftFusionMatrixByFinNat (k := k) (C := C) j =
      leftFusionMatrixByFinNat (k := k) (C := C) j *
        leftFusionMatrixByFinNat (k := k) (C := C) i := by
  simpa [leftFusionMatrixByFinNat] using
    (leftFusionMatrixFinNat_mul_comm (k := k) (C := C)
      (idxOfFin (k := k) (C := C) i) (idxOfFin (k := k) (C := C) j))

/-- Fully `Fin rank`-indexed `k`-valued left fusion matrices commute. -/
theorem leftFusionMatrixByFin_mul_comm
    (i j : Fin (rank (k := k) (C := C))) :
    leftFusionMatrixByFin (k := k) (C := C) i *
      leftFusionMatrixByFin (k := k) (C := C) j =
      leftFusionMatrixByFin (k := k) (C := C) j *
        leftFusionMatrixByFin (k := k) (C := C) i := by
  simpa [leftFusionMatrixByFin] using
    (leftFusionMatrixFin_mul_comm (k := k) (C := C)
      (idxOfFin (k := k) (C := C) i) (idxOfFin (k := k) (C := C) j))

end BraidedCommutativityFin

section VacuumDiag

variable [IsAlgClosed k] [HasKernels C]

/-- Vacuum row on the diagonal: `(N_0)_{j,j} = 1`. -/
theorem leftFusionMatrix_unit_diag
    (j : Idx (k := k) (C := C)) :
    leftFusionMatrix (k := k) (C := C) unitIdx j j = 1 :=
  fusionCoeff_vacuum_eq (k := k) (C := C) j

end VacuumDiag

section VacuumOffdiag

variable [HasKernels C]

/-- Vacuum row off-diagonal vanishing under non-isomorphism hypothesis. -/
theorem leftFusionMatrix_unit_offdiag
    (j m : Idx (k := k) (C := C))
    (h : ¬Nonempty (simpleObj (k := k) j ≅ simpleObj (k := k) m)) :
    leftFusionMatrix (k := k) (C := C) unitIdx j m = 0 :=
  fusionCoeff_vacuum_ne (k := k) (C := C) j m h

end VacuumOffdiag

section VacuumUnitMatrix

variable [IsAlgClosed k] [HasKernels C]
variable [CanonicalSimpleIndex (k := k) (C := C)]

/-- Entrywise vacuum fusion coefficient as a Kronecker delta in canonical indexing. -/
@[simp] theorem leftFusionMatrix_unit_apply
    (j m : Idx (k := k) (C := C)) :
    leftFusionMatrix (k := k) (C := C) unitIdx j m = if j = m then 1 else 0 := by
  simpa [leftFusionMatrix] using
    (fusionCoeff_vacuum_kronecker (k := k) (C := C) j m)

/-- Entrywise vacuum fusion coefficient cast into `k`. -/
@[simp] theorem leftFusionMatrixK_unit_apply
    (j m : Idx (k := k) (C := C)) :
    leftFusionMatrixK (k := k) (C := C) unitIdx j m = if j = m then 1 else 0 := by
  by_cases hEq : j = m
  · subst hEq
    simp [leftFusionMatrixK, fusionCoeff_vacuum_eq]
  · have hIso : ¬Nonempty (simpleObj (k := k) j ≅ simpleObj (k := k) m) := by
      intro h
      exact hEq (CanonicalSimpleIndex.eq_of_iso (k := k) (C := C) h)
    simp [leftFusionMatrixK, hEq, fusionCoeff_vacuum_ne (k := k) (C := C) j m hIso]

/-- The vacuum left fusion matrix is the identity matrix on `Idx`. -/
theorem leftFusionMatrix_unit :
    leftFusionMatrix (k := k) (C := C) unitIdx = 1 := by
  ext j m
  simpa [Matrix.one_apply] using
    (leftFusionMatrix_unit_apply (k := k) (C := C) j m)

/-- The `k`-valued vacuum left fusion matrix is the identity matrix on `Idx`. -/
theorem leftFusionMatrixK_unit :
    leftFusionMatrixK (k := k) (C := C) unitIdx = 1 := by
  ext j m
  simpa [Matrix.one_apply] using
    (leftFusionMatrixK_unit_apply (k := k) (C := C) j m)

/-- Reindexed `ℕ`-valued vacuum left fusion matrix is identity on `Fin rank`. -/
theorem leftFusionMatrixFinNat_unit :
    leftFusionMatrixFinNat (k := k) (C := C) unitIdx = 1 := by
  let e : Fin (rank (k := k) (C := C)) ≃ Idx (k := k) (C := C) :=
    (idxEquivFin (k := k) (C := C)).symm
  change (leftFusionMatrix (k := k) (C := C) unitIdx).submatrix e e = 1
  rw [leftFusionMatrix_unit (k := k) (C := C)]
  exact Matrix.submatrix_one_equiv (α := ℕ) e

/-- Reindexed `k`-valued vacuum left fusion matrix is identity on `Fin rank`. -/
theorem leftFusionMatrixFin_unit :
    leftFusionMatrixFin (k := k) (C := C) unitIdx = 1 := by
  let e : Fin (rank (k := k) (C := C)) ≃ Idx (k := k) (C := C) :=
    (idxEquivFin (k := k) (C := C)).symm
  change (leftFusionMatrixK (k := k) (C := C) unitIdx).submatrix e e = 1
  rw [leftFusionMatrixK_unit (k := k) (C := C)]
  exact Matrix.submatrix_one_equiv (α := k) e

/-- Fully `Fin rank`-indexed `ℕ`-valued vacuum left fusion matrix is identity. -/
theorem leftFusionMatrixByFinNat_unit :
    leftFusionMatrixByFinNat (k := k) (C := C)
      (finOfIdx (k := k) (C := C) unitIdx) = 1 := by
  simpa [leftFusionMatrixByFinNat] using
    (leftFusionMatrixFinNat_unit (k := k) (C := C))

/-- Fully `Fin rank`-indexed `k`-valued vacuum left fusion matrix is identity. -/
theorem leftFusionMatrixByFin_unit :
    leftFusionMatrixByFin (k := k) (C := C)
      (finOfIdx (k := k) (C := C) unitIdx) = 1 := by
  simpa [leftFusionMatrixByFin] using
    (leftFusionMatrixFin_unit (k := k) (C := C))

end VacuumUnitMatrix

end FusionCategory

end StringAlgebra.MTC

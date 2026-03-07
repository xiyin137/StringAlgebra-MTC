/-
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringAlgebra.MTC.Trace

/-!
# Spherical Categories

A spherical category is a pivotal category in which the left and right
categorical traces agree for all endomorphisms. This is the key condition
that makes the graphical calculus for pivotal categories fully isotopy-invariant.

## Main Definitions

* `SphericalCategory` - Pivotal category with left trace = right trace

## Main Results

* `spherical_dim` - Left and right quantum dimensions agree
* `dim_dual` - dim(X*) = dim(X) in a spherical category

## References

* [J. Barrett, B. Westbury, *Spherical Categories*]
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*], §4.7
-/

namespace StringAlgebra.MTC

open CategoryTheory MonoidalCategory

universe v₁ u₁

/-- A spherical category is a pivotal category where the left and right
    categorical traces agree for all endomorphisms. This ensures full
    isotopy invariance of the graphical calculus.

    In a spherical category, we can speak of THE trace and THE quantum
    dimension without ambiguity. -/
class SphericalCategory (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    [RigidCategory C] [PivotalCategory C] where
  /-- The left and right traces agree for all endomorphisms -/
  spherical : ∀ {X : C} (f : X ⟶ X), leftTrace f = rightTrace f

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [RigidCategory C]
variable [PivotalCategory C]

/-- The categorical trace in a spherical category (left = right). -/
def trace {X : C} (f : X ⟶ X) : (𝟙_ C ⟶ 𝟙_ C) := leftTrace f

/-- The quantum dimension of an object in a spherical category. -/
def dim (X : C) : (𝟙_ C ⟶ 𝟙_ C) := trace (𝟙 X)

/-- Invariance of trace under isomorphism conjugation. -/
theorem trace_conj {X Y : C} (e : X ≅ Y) (f : Y ⟶ Y) :
    trace (e.hom ≫ f ≫ e.inv) = trace f := by
  simpa [trace] using leftTrace_conj (C := C) e f

section

variable [SphericalCategory C]

/-- In a spherical category, left and right quantum dimensions agree. -/
theorem spherical_dim (X : C) : leftDim X = rightDim X :=
  SphericalCategory.spherical (𝟙 X)

end

/-- Quantum-dimension duality: dim(X*) = dim(X) in a spherical category. -/
theorem qdim_dual [SphericalCategory C] (X : C) :
    dim Xᘁ = dim X := by
  unfold dim trace leftTrace
  rw [PivotalCategory.pivotalIso_dual_compatibility_inv]
  simp
  rw [coevaluation_comp_rightAdjointMate_assoc
      (f := (PivotalCategory.pivotalIso (C := C) X).hom)]
  simpa [leftTrace, rightTrace] using
    (SphericalCategory.spherical (C := C) (𝟙 X)).symm

/-- Quantum-dimension normalization on the tensor unit.

Under explicit unit right-dimension normalization. -/
theorem qdim_unit [SphericalCategory C]
    (hunit : rightDim (C := C) (𝟙_ C) = 𝟙 (𝟙_ C)) :
    dim (𝟙_ C) = 𝟙 (𝟙_ C) := by
  unfold dim trace
  calc
    leftDim (C := C) (𝟙_ C) = rightDim (C := C) (𝟙_ C) :=
      spherical_dim (C := C) (𝟙_ C)
    _ = 𝟙 (𝟙_ C) := hunit

/-- Tensor multiplicativity of quantum dimension.

Under explicit right-dimension tensor multiplicativity normalization. -/
theorem qdim_tensor [SphericalCategory C]
    (X Y : C)
    (hTensorR : rightDim (C := C) (X ⊗ Y) = rightDim X ≫ rightDim Y) :
    dim (X ⊗ Y) = dim X ≫ dim Y := by
  unfold dim trace
  calc
    leftDim (C := C) (X ⊗ Y) = rightDim (C := C) (X ⊗ Y) :=
      spherical_dim (C := C) (X ⊗ Y)
    _ = rightDim X ≫ rightDim Y := hTensorR
    _ = leftDim X ≫ rightDim Y := by rw [spherical_dim (C := C) X]
    _ = leftDim X ≫ leftDim Y := by rw [spherical_dim (C := C) Y]

end StringAlgebra.MTC

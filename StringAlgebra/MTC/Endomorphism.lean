/-
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringAlgebra.MTC.FusionCategory
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Scalar Extraction for Endomorphisms of Simple Objects

For a simple object X in a k-linear category over an algebraically closed field k,
Schur's lemma implies that every endomorphism f : X → X is of the form c • id_X
for a unique scalar c ∈ k (since End(X) is 1-dimensional over k).

This module provides the scalar extraction function and its basic properties.

## Main Definitions

* `scalarOfEndo` - Extract the scalar c such that f = c • id_X
* `scalarOfEndUnit` - Specialization to the tensor unit
* `scalarOfEndSimple` - Specialization to fusion category simple objects

## References

* Schur's lemma: `CategoryTheory.endomorphism_simple_eq_smul_id`
* `CategoryTheory.finrank_endomorphism_simple_eq_one`
-/

namespace StringAlgebra.MTC

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v₁ u₁

section ScalarExtraction

variable {k : Type u₁} [Field k]
variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear k C]

/-- The canonical linear map `k → End(X)`, sending `c` to `c • id_X`. -/
noncomputable def smulIdLinearMap {X : C} : k →ₗ[k] (X ⟶ X) where
  toFun c := c • 𝟙 X
  map_add' _ _ := by simp [add_smul]
  map_smul' _ _ := by simp [smul_smul]

/-- The map `c ↦ c • id_X` is injective. -/
theorem smulIdLinearMap_injective {X : C} [Simple X] :
    Function.Injective (smulIdLinearMap (k := k) (X := X)) := by
  intro a b h
  have hab : a • (𝟙 X : X ⟶ X) = b • (𝟙 X : X ⟶ X) := h
  have hsub : ((a - b) : k) • (𝟙 X : X ⟶ X) = 0 := by
    calc
      ((a - b) : k) • (𝟙 X : X ⟶ X) =
          a • (𝟙 X : X ⟶ X) - b • (𝟙 X : X ⟶ X) := by simp [sub_smul]
      _ = 0 := by simp [hab]
  rw [smul_eq_zero] at hsub
  rcases hsub with hzero | hid
  · exact sub_eq_zero.mp hzero
  · exact (id_nonzero X hid).elim

variable [IsAlgClosed k] [HasKernels C]

/-- Finite-dimensional rank equality needed to upgrade `smulIdLinearMap`
    to a linear equivalence when `X` is simple. -/
theorem smulIdLinearMap_finrank_eq {X : C} [Simple X]
    [FiniteDimensional k (X ⟶ X)] :
    Module.finrank k k = Module.finrank k (X ⟶ X) := by
  calc
    Module.finrank k k = 1 := Module.finrank_self k
    _ = Module.finrank k (X ⟶ X) := by
      simpa using (finrank_endomorphism_simple_eq_one k X).symm

/-- Canonical linear equivalence `k ≃ End(X)` for a simple object `X`
    over an algebraically closed field. -/
noncomputable def smulIdLinearEquiv {X : C} [Simple X]
    [FiniteDimensional k (X ⟶ X)] : k ≃ₗ[k] (X ⟶ X) :=
  LinearEquiv.ofInjectiveOfFinrankEq
    (smulIdLinearMap (k := k) (X := X))
    (smulIdLinearMap_injective (k := k) (X := X))
    (smulIdLinearMap_finrank_eq (k := k) (X := X))

@[simp] theorem smulIdLinearEquiv_apply {X : C} [Simple X]
    [FiniteDimensional k (X ⟶ X)] (c : k) :
    smulIdLinearEquiv (k := k) (X := X) c = c • 𝟙 X := by
  have hcoe :
      (smulIdLinearEquiv (k := k) (X := X)).toLinearMap =
      smulIdLinearMap (k := k) (X := X) := by
    change
      (LinearEquiv.ofInjectiveOfFinrankEq
        (smulIdLinearMap (k := k) (X := X))
        (smulIdLinearMap_injective (k := k) (X := X))
        (smulIdLinearMap_finrank_eq (k := k) (X := X))).toLinearMap =
      smulIdLinearMap (k := k) (X := X)
    exact LinearEquiv.coe_ofInjectiveOfFinrankEq
      (f := smulIdLinearMap (k := k) (X := X))
      (hinj := smulIdLinearMap_injective (k := k) (X := X))
      (hrank := smulIdLinearMap_finrank_eq (k := k) (X := X))
  exact LinearMap.congr_fun hcoe c

/-- Extract the unique scalar from an endomorphism of a simple object.

    By Schur's lemma over an algebraically closed field, every endomorphism
    f : X → X of a simple object X equals c • id_X for a unique c ∈ k.
    This function extracts that c. -/
noncomputable def scalarOfEndo {X : C} [Simple X]
    [FiniteDimensional k (X ⟶ X)] (f : X ⟶ X) : k :=
  (smulIdLinearEquiv (k := k) (X := X)).symm f

/-- The scalar extraction satisfies f = (scalarOfEndo f) • id_X. -/
theorem scalarOfEndo_spec {X : C} [Simple X]
    [FiniteDimensional k (X ⟶ X)] (f : X ⟶ X) :
    scalarOfEndo (k := k) f • 𝟙 X = f := by
  rw [← smulIdLinearEquiv_apply (k := k) (X := X) (scalarOfEndo (k := k) f)]
  change (smulIdLinearEquiv (k := k) (X := X))
      ((smulIdLinearEquiv (k := k) (X := X)).symm f) = f
  exact (smulIdLinearEquiv (k := k) (X := X)).apply_symm_apply f

/-- The scalar of the identity is 1. -/
theorem scalarOfEndo_id {X : C} [Simple X]
    [FiniteDimensional k (X ⟶ X)] :
    scalarOfEndo (k := k) (𝟙 X : X ⟶ X) = 1 := by
  have h := scalarOfEndo_spec (k := k) (𝟙 X : X ⟶ X)
  by_contra hne
  have h1 : (scalarOfEndo (k := k) (𝟙 X : X ⟶ X) - 1) • 𝟙 X = (0 : X ⟶ X) := by
    rw [sub_smul, one_smul, h, sub_self]
  rw [smul_eq_zero] at h1
  cases h1 with
  | inl h => exact hne (sub_eq_zero.mp h)
  | inr h => exact id_nonzero X h

end ScalarExtraction

section FusionScalars

variable {k : Type u₁} [Field k] [IsAlgClosed k]
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable [Preadditive C] [Linear k C] [MonoidalPreadditive C]
variable [HasFiniteBiproducts C] [RigidCategory C]
variable [HasKernels C]
variable [FusionCategory k C]

/-- Scalar extraction for endomorphisms of the tensor unit.
    The unit is simple in a fusion category, so Schur's lemma applies. -/
noncomputable def scalarOfEndUnit (f : 𝟙_ C ⟶ 𝟙_ C) : k :=
  letI : Simple (𝟙_ C) := FusionCategory.unit_simple (k := k)
  letI : FiniteDimensional k (𝟙_ C ⟶ 𝟙_ C) :=
    FusionCategory.finiteDimensionalHom (k := k) (𝟙_ C) (𝟙_ C)
  scalarOfEndo f

/-- Scalar extraction for endomorphisms of a fusion category simple object. -/
noncomputable def scalarOfEndSimple
    (i : FusionCategory.Idx (k := k) (C := C))
    (f : FusionCategory.simpleObj i ⟶ FusionCategory.simpleObj i) : k :=
  letI : Simple (FusionCategory.simpleObj i) :=
    FusionCategory.simpleObj_simple (k := k) i
  letI : FiniteDimensional k
      (FusionCategory.simpleObj i ⟶ FusionCategory.simpleObj i) :=
    FusionCategory.finiteDimensionalHom (k := k)
      (FusionCategory.simpleObj i) (FusionCategory.simpleObj i)
  scalarOfEndo f

/-- The scalar extraction for the unit satisfies the expected equation:
    scalarOfEndUnit f • 𝟙 (𝟙_ C) = f -/
theorem scalarOfEndUnit_spec (f : 𝟙_ C ⟶ 𝟙_ C) :
    (scalarOfEndUnit f : k) • 𝟙 (𝟙_ C) = f := by
  letI : Simple (𝟙_ C) := FusionCategory.unit_simple (k := k)
  letI : FiniteDimensional k (𝟙_ C ⟶ 𝟙_ C) :=
    FusionCategory.finiteDimensionalHom (k := k) (𝟙_ C) (𝟙_ C)
  exact scalarOfEndo_spec f

/-- The scalar extraction for simples satisfies the expected equation:
    scalarOfEndSimple i f • 𝟙 (simpleObj i) = f -/
theorem scalarOfEndSimple_spec
    (i : FusionCategory.Idx (k := k) (C := C))
    (f : FusionCategory.simpleObj (k := k) i ⟶ FusionCategory.simpleObj (k := k) i) :
    (scalarOfEndSimple i f : k) • 𝟙 (FusionCategory.simpleObj (k := k) i) = f := by
  letI : Simple (FusionCategory.simpleObj i) :=
    FusionCategory.simpleObj_simple (k := k) i
  letI : FiniteDimensional k
      (FusionCategory.simpleObj i ⟶ FusionCategory.simpleObj i) :=
    FusionCategory.finiteDimensionalHom (k := k)
      (FusionCategory.simpleObj i) (FusionCategory.simpleObj i)
  exact scalarOfEndo_spec f

end FusionScalars

end StringAlgebra.MTC

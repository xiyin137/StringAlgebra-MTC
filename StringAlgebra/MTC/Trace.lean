/-
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringAlgebra.MTC.Pivotal

/-!
# Categorical Traces in Pivotal Categories

In a pivotal category, we define left and right categorical traces for
endomorphisms. These are morphisms `𝟙_ C ⟶ 𝟙_ C` (elements of the
endomorphism ring of the tensor unit).

## Main Definitions

* `leftTrace` - Left categorical trace using right dual coevaluation
* `rightTrace` - Right categorical trace using right dual evaluation
* `leftDim` - Left quantum dimension (left trace of identity)
* `rightDim` - Right quantum dimension (right trace of identity)

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*], §4.7
-/

namespace StringAlgebra.MTC

open CategoryTheory MonoidalCategory

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [RigidCategory C]
variable [PivotalCategory C]

/-- The left categorical trace of an endomorphism f : X ⟶ X in a pivotal category.

    Defined as the composition:
    ```
    𝟙 --η_{Xᘁ}-→ Xᘁ ⊗ (Xᘁ)ᘁ --id ⊗ j⁻¹-→ Xᘁ ⊗ X --id ⊗ f-→ Xᘁ ⊗ X --ε_X-→ 𝟙
    ```
    where j = pivotalIso X : X ≅ (Xᘁ)ᘁ, and η, ε are the coevaluation and
    evaluation maps from the exact pairings. -/
def leftTrace {X : C} (f : X ⟶ X) : (𝟙_ C ⟶ 𝟙_ C) :=
  η_ Xᘁ (Xᘁ)ᘁ ≫ (Xᘁ ◁ (PivotalCategory.pivotalIso X).inv) ≫
    (Xᘁ ◁ f) ≫ ε_ X Xᘁ

/-- The right categorical trace of an endomorphism f : X ⟶ X in a pivotal category.

    Defined as the composition:
    ```
    𝟙 --η_X-→ X ⊗ Xᘁ --f ⊗ id-→ X ⊗ Xᘁ --j ⊗ id-→ (Xᘁ)ᘁ ⊗ Xᘁ --ε_{Xᘁ}-→ 𝟙
    ```
    where j = pivotalIso X : X ≅ (Xᘁ)ᘁ. -/
def rightTrace {X : C} (f : X ⟶ X) : (𝟙_ C ⟶ 𝟙_ C) :=
  η_ X Xᘁ ≫ (f ▷ Xᘁ) ≫ ((PivotalCategory.pivotalIso X).hom ▷ Xᘁ) ≫
    ε_ Xᘁ (Xᘁ)ᘁ

/-- The left quantum dimension of an object X, defined as the left trace of
    the identity morphism. -/
def leftDim (X : C) : (𝟙_ C ⟶ 𝟙_ C) := leftTrace (𝟙 X)

/-- The right quantum dimension of an object X, defined as the right trace of
    the identity morphism. -/
def rightDim (X : C) : (𝟙_ C ⟶ 𝟙_ C) := rightTrace (𝟙 X)

/-- Invariance of left trace under isomorphism conjugation. -/
theorem leftTrace_conj {X Y : C} (e : X ≅ Y) (f : Y ⟶ Y) :
    leftTrace (e.hom ≫ f ≫ e.inv) = leftTrace f := by
  let jX : X ≅ ((Xᘁ)ᘁ : C) := PivotalCategory.pivotalIso X
  let jY : Y ≅ ((Yᘁ)ᘁ : C) := PivotalCategory.pivotalIso Y
  have hnat := PivotalCategory.pivotalIso_naturality (C := C) (f := e.hom)
  have hji : jX.inv ≫ e.hom = e.homᘁᘁ ≫ jY.inv := by
    have hnat' := congrArg (fun t => jX.inv ≫ t ≫ jY.inv) hnat
    simp [jX, jY, Category.assoc] at hnat'
    exact hnat'
  have hdual : e.homᘁ ≫ e.invᘁ = 𝟙 (Yᘁ : C) := by
    calc
      e.homᘁ ≫ e.invᘁ = (e.inv ≫ e.hom)ᘁ := by
        symm
        simpa using (CategoryTheory.comp_rightAdjointMate (f := e.inv) (g := e.hom))
      _ = (𝟙 Y)ᘁ := by simp [e.inv_hom_id]
      _ = 𝟙 (Yᘁ : C) := by simp
  have heval : (Xᘁ ◁ e.inv) ≫ ε_ X (Xᘁ : C) =
      (e.invᘁ ▷ Y) ≫ ε_ Y (Yᘁ : C) := by
    simpa using (rightAdjointMate_comp_evaluation (f := e.inv)).symm
  have hwhiskComp : (e.homᘁ ▷ Y) ≫ (e.invᘁ ▷ Y) =
      ((e.homᘁ ≫ e.invᘁ) ▷ Y) := by
    simp [comp_whiskerRight]
  have hcancelWhisk :
      η_ (Yᘁ : C) ((Yᘁ)ᘁ : C) ≫
          (Yᘁ ◁ jY.inv) ≫ (Yᘁ ◁ f) ≫ (e.homᘁ ▷ Y) ≫ (e.invᘁ ▷ Y) ≫
          ε_ Y (Yᘁ : C) =
        η_ (Yᘁ : C) ((Yᘁ)ᘁ : C) ≫
      (Yᘁ ◁ jY.inv) ≫ (Yᘁ ◁ f) ≫ ((e.homᘁ ≫ e.invᘁ) ▷ Y) ≫
      ε_ Y (Yᘁ : C) := by
    simpa [Category.assoc] using
      congrArg (fun t =>
        η_ (Yᘁ : C) ((Yᘁ)ᘁ : C) ≫
          (Yᘁ ◁ jY.inv) ≫ (Yᘁ ◁ f) ≫ t ≫ ε_ Y (Yᘁ : C)) hwhiskComp
  unfold leftTrace
  calc
    η_ (Xᘁ : C) ((Xᘁ)ᘁ : C) ≫
        (Xᘁ ◁ jX.inv) ≫ (Xᘁ ◁ (e.hom ≫ f ≫ e.inv)) ≫ ε_ X (Xᘁ : C)
      = η_ (Xᘁ : C) ((Xᘁ)ᘁ : C) ≫
          (Xᘁ ◁ jX.inv) ≫ (Xᘁ ◁ e.hom) ≫ (Xᘁ ◁ f) ≫ (Xᘁ ◁ e.inv) ≫
            ε_ X (Xᘁ : C) := by
          simp [Category.assoc, MonoidalCategory.whiskerLeft_comp]
    _ = η_ (Xᘁ : C) ((Xᘁ)ᘁ : C) ≫
          (Xᘁ ◁ (jX.inv ≫ e.hom)) ≫ (Xᘁ ◁ f) ≫ (Xᘁ ◁ e.inv) ≫ ε_ X (Xᘁ : C) := by
          simp [Category.assoc, MonoidalCategory.whiskerLeft_comp]
    _ = η_ (Xᘁ : C) ((Xᘁ)ᘁ : C) ≫
          (Xᘁ ◁ (e.homᘁᘁ ≫ jY.inv)) ≫ (Xᘁ ◁ f) ≫ (Xᘁ ◁ e.inv) ≫ ε_ X (Xᘁ : C) := by
          simp [hji]
    _ = η_ (Xᘁ : C) ((Xᘁ)ᘁ : C) ≫
          (Xᘁ ◁ e.homᘁᘁ) ≫ (Xᘁ ◁ jY.inv) ≫ (Xᘁ ◁ f) ≫ (Xᘁ ◁ e.inv) ≫
            ε_ X (Xᘁ : C) := by
          simp [Category.assoc, MonoidalCategory.whiskerLeft_comp]
    _ = η_ (Yᘁ : C) ((Yᘁ)ᘁ : C) ≫
          (e.homᘁ ▷ ((Yᘁ)ᘁ : C)) ≫ (Xᘁ ◁ jY.inv) ≫ (Xᘁ ◁ f) ≫
            (Xᘁ ◁ e.inv) ≫ ε_ X (Xᘁ : C) := by
          rw [coevaluation_comp_rightAdjointMate_assoc (f := e.homᘁ)]
    _ = η_ (Yᘁ : C) ((Yᘁ)ᘁ : C) ≫
          (Yᘁ ◁ jY.inv) ≫ (e.homᘁ ▷ Y) ≫ (Xᘁ ◁ f) ≫ (Xᘁ ◁ e.inv) ≫
            ε_ X (Xᘁ : C) := by
          rw [← whisker_exchange_assoc]
    _ = η_ (Yᘁ : C) ((Yᘁ)ᘁ : C) ≫
          (Yᘁ ◁ jY.inv) ≫ (Yᘁ ◁ f) ≫ (e.homᘁ ▷ Y) ≫ (Xᘁ ◁ e.inv) ≫
            ε_ X (Xᘁ : C) := by
          rw [← whisker_exchange_assoc]
    _ = η_ (Yᘁ : C) ((Yᘁ)ᘁ : C) ≫
          (Yᘁ ◁ jY.inv) ≫ (Yᘁ ◁ f) ≫ (e.homᘁ ▷ Y) ≫
            (e.invᘁ ▷ Y) ≫ ε_ Y (Yᘁ : C) := by
          simp [heval]
    _ = η_ (Yᘁ : C) ((Yᘁ)ᘁ : C) ≫
          (Yᘁ ◁ jY.inv) ≫ (Yᘁ ◁ f) ≫ ((e.homᘁ ≫ e.invᘁ) ▷ Y) ≫
            ε_ Y (Yᘁ : C) := hcancelWhisk
    _ = η_ (Yᘁ : C) ((Yᘁ)ᘁ : C) ≫
          (Yᘁ ◁ jY.inv) ≫ (Yᘁ ◁ f) ≫ ε_ Y (Yᘁ : C) := by
          simp [hdual]

/-- Rewrite the left trace of an identity through the right-adjoint mate of the
pivotal inverse. This is a useful bridge when comparing left/right trace
normal forms in duality arguments. -/
theorem leftTrace_id_eq_rightAdjointMate_eval (X : C) :
    leftTrace (C := C) (𝟙 X) =
      η_ (Xᘁ : C) ((Xᘁ)ᘁ : C) ≫
        (PivotalCategory.pivotalIso X).invᘁ ▷ ((Xᘁ)ᘁ : C) ≫
        ε_ ((Xᘁ)ᘁ : C) (((Xᘁ)ᘁ)ᘁ : C) := by
  unfold leftTrace
  simp
  have key := (@rightAdjointMate_comp_evaluation C _ _ _ _ _ _
    ((PivotalCategory.pivotalIso X).inv))
  have key' := congrArg (fun t => η_ (Xᘁ : C) ((Xᘁ)ᘁ : C) ≫ t) key.symm
  simpa [Category.assoc] using key'

/-- Transport the pivotal inverse whisker/evaluation composite to the corresponding
right-adjoint-mate normal form. -/
theorem whisker_pivotalInv_comp_evaluation (X : C) :
    (Xᘁ ◁ (PivotalCategory.pivotalIso X).inv) ≫ ε_ X Xᘁ =
      (PivotalCategory.pivotalIso X).invᘁ ▷ ((Xᘁ)ᘁ : C) ≫
        ε_ ((Xᘁ)ᘁ : C) (((Xᘁ)ᘁ)ᘁ : C) := by
  simpa [Category.assoc] using
    (@rightAdjointMate_comp_evaluation C _ _ ((Xᘁ)ᘁ : C) X _ _
      ((PivotalCategory.pivotalIso X).inv)).symm

/-- Transport the pivotal-hom whisker/evaluation composite to the corresponding
right-adjoint-mate normal form. -/
theorem whisker_pivotalHom_comp_evaluation (X : C) :
    (((Xᘁ)ᘁ)ᘁ ◁ (PivotalCategory.pivotalIso X).hom) ≫
      ε_ ((Xᘁ)ᘁ : C) (((Xᘁ)ᘁ)ᘁ : C) =
    (PivotalCategory.pivotalIso X).homᘁ ▷ X ≫ ε_ X Xᘁ := by
  simpa [Category.assoc] using
    (@rightAdjointMate_comp_evaluation C _ _ X ((Xᘁ)ᘁ : C) _ _
      ((PivotalCategory.pivotalIso X).hom)).symm

/-- Rewrite the evaluation map `ε_X` through pivotal inverse/hom data by
precomposing `rightAdjointMate_comp_evaluation` with `(pivotalIso X).invᘁ ▷ X`
and collapsing the inverse/hom mate composition. -/
theorem evaluation_eq_pivotalInvMate_comp_pivotalHom (X : C) :
    ε_ X (Xᘁ : C) =
      ((PivotalCategory.pivotalIso X).invᘁ ▷ X) ≫
        ((((Xᘁ)ᘁ)ᘁ : C) ◁ (PivotalCategory.pivotalIso X).hom) ≫
          ε_ ((Xᘁ)ᘁ : C) (((Xᘁ)ᘁ)ᘁ : C) := by
  let j : X ≅ ((Xᘁ)ᘁ : C) := PivotalCategory.pivotalIso X
  have hcomp : j.invᘁ ≫ j.homᘁ = 𝟙 (Xᘁ : C) := by
    calc
      j.invᘁ ≫ j.homᘁ = (j.hom ≫ j.inv)ᘁ := by
        symm
        simpa using (CategoryTheory.comp_rightAdjointMate (f := j.hom) (g := j.inv))
      _ = (𝟙 X)ᘁ := by simp [j.hom_inv_id]
      _ = 𝟙 (Xᘁ : C) := by simp
  have hhom := (@rightAdjointMate_comp_evaluation C _ _ X ((Xᘁ)ᘁ : C) _ _ j.hom)
  have hpre := congrArg (fun t => (j.invᘁ ▷ X) ≫ t) hhom
  have hpre0 :
      ((j.invᘁ ≫ j.homᘁ) ▷ X) ≫ ε_ X (Xᘁ : C) =
        (j.invᘁ ▷ X) ≫ ((((Xᘁ)ᘁ)ᘁ : C) ◁ j.hom) ≫
          ε_ ((Xᘁ)ᘁ : C) (((Xᘁ)ᘁ)ᘁ : C) := by
    simpa [Category.assoc, comp_whiskerRight] using hpre
  calc
    ε_ X (Xᘁ : C) = ((𝟙 (Xᘁ : C)) ▷ X) ≫ ε_ X (Xᘁ : C) := by simp
    _ = ((j.invᘁ ≫ j.homᘁ) ▷ X) ≫ ε_ X (Xᘁ : C) := by simp [hcomp]
    _ = (j.invᘁ ▷ X) ≫ ((((Xᘁ)ᘁ)ᘁ : C) ◁ j.hom) ≫
          ε_ ((Xᘁ)ᘁ : C) (((Xᘁ)ᘁ)ᘁ : C) := hpre0
    _ = ((PivotalCategory.pivotalIso X).invᘁ ▷ X) ≫
          ((((Xᘁ)ᘁ)ᘁ : C) ◁ (PivotalCategory.pivotalIso X).hom) ≫
            ε_ ((Xᘁ)ᘁ : C) (((Xᘁ)ᘁ)ᘁ : C) := by
          simp [j]

omit [PivotalCategory C] in
/-- The core string-diagram block in the definition of `rightAdjointMate`,
without the outer right-unitor factor. -/
theorem rightAdjointMate_core_eq_rho_hom_comp
    {X Y : C} (f : X ⟶ Y) :
    (Yᘁ : C) ◁ η_ X (Xᘁ : C) ≫
        (Yᘁ : C) ◁ f ▷ (Xᘁ : C) ≫
          (α_ (Yᘁ : C) Y (Xᘁ : C)).inv ≫
            ε_ Y (Yᘁ : C) ▷ (Xᘁ : C) ≫
              (λ_ (Xᘁ : C)).hom =
      (ρ_ (Yᘁ : C)).hom ≫ CategoryTheory.rightAdjointMate f := by
  simp [CategoryTheory.rightAdjointMate]

omit [PivotalCategory C] in
/-- Equivalent right-unitor-cancelled form of `rightAdjointMate`. -/
theorem rightAdjointMate_eq_rho_inv_comp_core
    {X Y : C} (f : X ⟶ Y) :
    CategoryTheory.rightAdjointMate f =
      (ρ_ (Yᘁ : C)).inv ≫
        ((Yᘁ : C) ◁ η_ X (Xᘁ : C) ≫
          (Yᘁ : C) ◁ f ▷ (Xᘁ : C) ≫
            (α_ (Yᘁ : C) Y (Xᘁ : C)).inv ≫
              ε_ Y (Yᘁ : C) ▷ (Xᘁ : C) ≫
                (λ_ (Xᘁ : C)).hom) := by
  simp [CategoryTheory.rightAdjointMate]

end StringAlgebra.MTC

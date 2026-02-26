/-
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Pivotal Categories

A pivotal category is a rigid monoidal category equipped with a monoidal natural
isomorphism from the identity functor to the double right dual functor X ↦ (Xᘁ)ᘁ.

Mathlib provides `RigidCategory` (both left and right duals exist) with the
definitional equality `ᘁ(Xᘁ) = X`. However, the *right-right* double dual `(Xᘁ)ᘁ`
is in general a different object. A pivotal structure provides a coherent
identification `X ≅ (Xᘁ)ᘁ`.

## Main Definitions

* `PivotalCategory` - Rigid monoidal category with pivotal isomorphism X ≅ (Xᘁ)ᘁ
* `leftRightDualIso` - Derived isomorphism ᘁX ≅ Xᘁ in a pivotal category

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*], Definition 2.11.1
* [V. Turaev, *Quantum Invariants of Knots and 3-Manifolds*]
-/

namespace StringAlgebra.MTC

open CategoryTheory MonoidalCategory

universe v₁ u₁

/-- A pivotal category is a rigid monoidal category equipped with a monoidal
    natural isomorphism from the identity functor to the double right dual
    functor X ↦ (Xᘁ)ᘁ.

    The monoidal condition is captured by the left duality zigzag identity:
    the pivotal isomorphism induces a left duality (X ⊗ Xᘁ → 𝟙 and 𝟙 → Xᘁ ⊗ X)
    from the right duality, and the zigzag identity ensures this left duality
    is valid, which is equivalent to the pivotal isomorphism being monoidal.

    Concretely, the induced left evaluation is:
      ε_L(X) : X ⊗ Xᘁ →[j_X ⊗ id] (Xᘁ)ᘁ ⊗ Xᘁ →[ε_{Xᘁ}] 𝟙
    and the induced left coevaluation is:
      η_L(X) : 𝟙 →[η_{Xᘁ}] Xᘁ ⊗ (Xᘁ)ᘁ →[id ⊗ j_X⁻¹] Xᘁ ⊗ X

    ## References

    * [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*],
      Definition 2.11.1
    * [nLab, *pivotal category*]: requires monoidal natural isomorphism -/
class PivotalCategory (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    [RigidCategory C] where
  /-- The pivotal isomorphism from X to its double right dual -/
  pivotalIso : ∀ (X : C), X ≅ (Xᘁ)ᘁ
  /-- Naturality: the pivotal isomorphism commutes with morphisms and their
      double right adjoint mates. For f : X ⟶ Y, the diagram commutes:
      ```
           f
      X ------→ Y
      |          |
    j_X        j_Y
      |          |
      ↓    fᘁᘁ   ↓
      Xᘁᘁ ----→ Yᘁᘁ
      ``` -/
  pivotalIso_naturality : ∀ {X Y : C} (f : X ⟶ Y),
    f ≫ (pivotalIso Y).hom = (pivotalIso X).hom ≫ (rightAdjointMate (rightAdjointMate f))
  /-- The pivotal isomorphism satisfies the left duality zigzag identities.
      These are the monoidal conditions: they ensure that the induced left evaluation
      ε_L(X) = (j_X ▷ Xᘁ) ≫ ε_{Xᘁ,(Xᘁ)ᘁ} and the induced left coevaluation
      η_L(X) = η_{Xᘁ,(Xᘁ)ᘁ} ≫ (Xᘁ ◁ j_X⁻¹) form a valid exact pairing.

      The first zigzag identity (for X) states:
      X →[ρ⁻¹] X ⊗ 𝟙 →[id ⊗ η_L] X ⊗ (Xᘁ ⊗ X) →[α⁻¹] (X ⊗ Xᘁ) ⊗ X
        →[ε_L ⊗ id] 𝟙 ⊗ X →[λ] X = id_X -/
  pivotalIso_leftDuality : ∀ (X : C),
    (ρ_ X).inv ≫ (X ◁ η_ Xᘁ (Xᘁ)ᘁ) ≫ (X ◁ (Xᘁ ◁ (pivotalIso X).inv)) ≫
    (α_ X Xᘁ X).inv ≫ (((pivotalIso X).hom ▷ Xᘁ) ▷ X) ≫
    ((ε_ Xᘁ (Xᘁ)ᘁ) ▷ X) ≫ (λ_ X).hom = 𝟙 X
  /-- The second zigzag identity (for Xᘁ) of the induced left exact pairing.
      Together with `pivotalIso_leftDuality`, this ensures the induced left
      duality is a proper exact pairing (Mathlib's `ExactPairing` requires both
      zigzag identities), which is equivalent to j being monoidal.

      The zigzag identity for Xᘁ states:
      Xᘁ →[λ⁻¹] 𝟙 ⊗ Xᘁ →[η_L ⊗ id] (Xᘁ ⊗ X) ⊗ Xᘁ →[α] Xᘁ ⊗ (X ⊗ Xᘁ)
        →[id ⊗ ε_L] Xᘁ ⊗ 𝟙 →[ρ] Xᘁ = id_{Xᘁ} -/
  pivotalIso_leftDuality_dual : ∀ (X : C),
    (λ_ Xᘁ).inv ≫ (η_ Xᘁ (Xᘁ)ᘁ ▷ Xᘁ) ≫ ((Xᘁ ◁ (pivotalIso X).inv) ▷ Xᘁ) ≫
    (α_ Xᘁ X Xᘁ).hom ≫ (Xᘁ ◁ ((pivotalIso X).hom ▷ Xᘁ)) ≫
    (Xᘁ ◁ ε_ Xᘁ (Xᘁ)ᘁ) ≫ (ρ_ Xᘁ).hom = 𝟙 Xᘁ

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [RigidCategory C]

namespace PivotalCategory

variable [PivotalCategory C]

/-- Shorthand for the pivotal isomorphism -/
abbrev j (X : C) : X ≅ (Xᘁ)ᘁ := pivotalIso X

/-- In a pivotal category, the left and right duals of any object are
    canonically isomorphic.

    We first use the pivotal isomorphism to build an exact pairing
    `ExactPairing Xᘁ X`, then invoke uniqueness of left duals. -/
private def pivotalExactPairing (X : C) : ExactPairing Xᘁ X where
  coevaluation' := η_ Xᘁ (Xᘁ)ᘁ ≫ (Xᘁ ◁ (pivotalIso X).inv)
  evaluation' := ((pivotalIso X).hom ▷ Xᘁ) ≫ ε_ Xᘁ (Xᘁ)ᘁ
  coevaluation_evaluation' := by
    have h := pivotalIso_leftDuality (C := C) X
    have h' :
        (X ◁ η_ Xᘁ (Xᘁ)ᘁ) ≫ (X ◁ (Xᘁ ◁ (pivotalIso X).inv)) ≫
          (α_ X Xᘁ X).inv ≫ (((pivotalIso X).hom ▷ Xᘁ) ▷ X) ≫
          ((ε_ Xᘁ (Xᘁ)ᘁ) ▷ X) = (ρ_ X).hom ≫ (λ_ X).inv := by
      have h1 := congrArg (fun t => (ρ_ X).hom ≫ t ≫ (λ_ X).inv) h
      simpa [Category.assoc] using h1
    simpa [MonoidalCategory.whiskerLeft_comp, comp_whiskerRight, Category.assoc] using h'
  evaluation_coevaluation' := by
    have h := pivotalIso_leftDuality_dual (C := C) X
    have h' :
        (η_ Xᘁ (Xᘁ)ᘁ ▷ Xᘁ) ≫ ((Xᘁ ◁ (pivotalIso X).inv) ▷ Xᘁ) ≫
          (α_ Xᘁ X Xᘁ).hom ≫ (Xᘁ ◁ ((pivotalIso X).hom ▷ Xᘁ)) ≫
          (Xᘁ ◁ ε_ Xᘁ (Xᘁ)ᘁ) = (λ_ Xᘁ).hom ≫ (ρ_ Xᘁ).inv := by
      have h1 := congrArg (fun t => (λ_ Xᘁ).hom ≫ t ≫ (ρ_ Xᘁ).inv) h
      simpa [Category.assoc] using h1
    simpa [comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc] using h'

noncomputable def leftRightDualIso (X : C) : (ᘁX) ≅ (Xᘁ) :=
  leftDualIso
    (inferInstance : ExactPairing (ᘁX) X)
    (pivotalExactPairing (C := C) X)

end PivotalCategory

end StringAlgebra.MTC

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
  /-- Pivotal dual compatibility (EGNO Exercise 4.7.9):
      the pivotal isomorphism on the dual is the adjoint mate of
      the pivotal inverse.

      Mathematically, this states `j_{X*} = (j_X⁻¹)^*` and is a
      consequence of the monoidality of the pivotal structure. In the
      current formulation, monoidality is encoded through the zigzag
      identities above; this field makes the dual-compatibility consequence
      directly available.

      This is the key bridge needed for spherical trace normalization:
      it identifies `(pivotalIso Xᘁ).inv` with `(pivotalIso X).homᘁ`,
      enabling `qdim_dual`, `qdim_unit`, and downstream modular identities.

      TODO: derive from zigzag identities (requires infrastructure to
      bridge between exact pairings at different duality levels). -/
  pivotalIso_dual_compatibility : ∀ (X : C),
    (pivotalIso (Xᘁ : C)).hom = (pivotalIso X).invᘁ

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [RigidCategory C]

namespace PivotalCategory

variable [PivotalCategory C]

/-- Shorthand for the pivotal isomorphism -/
abbrev j (X : C) : X ≅ (Xᘁ)ᘁ := pivotalIso X

/-- The double right-adjoint mate of the pivotal inverse identifies with the
inverse pivotal isomorphism on the double right dual. -/
theorem doubleRightAdjointMate_pivotalInv (X : C) :
    rightAdjointMate (rightAdjointMate ((pivotalIso X).inv)) =
      (pivotalIso ((Xᘁ)ᘁ : C)).inv := by
  let jX : X ≅ ((Xᘁ)ᘁ : C) := pivotalIso X
  let jDD : ((Xᘁ)ᘁ : C) ≅ ((((Xᘁ)ᘁ)ᘁ)ᘁ : C) := pivotalIso ((Xᘁ)ᘁ : C)
  have hnat := (pivotalIso_naturality (C := C) (f := jX.inv))
  have hcomp :
      jDD.hom ≫ rightAdjointMate (rightAdjointMate jX.inv) =
        𝟙 ((Xᘁ)ᘁ : C) := by
    simpa [jX, jDD, jX.inv_hom_id, Category.id_comp] using hnat.symm
  have hcomp' :
      jDD.hom ≫ rightAdjointMate (rightAdjointMate jX.inv) =
        jDD.hom ≫ jDD.inv := by
    calc
      jDD.hom ≫ rightAdjointMate (rightAdjointMate jX.inv) = 𝟙 ((Xᘁ)ᘁ : C) := hcomp
      _ = jDD.hom ≫ jDD.inv := by simp [jDD.hom_inv_id]
  have hcancel := (cancel_epi jDD.hom).1 hcomp'
  simpa [jDD] using hcancel

/-- The double right-adjoint mate of the pivotal hom identifies with the
pivotal hom on the double right dual. -/
theorem doubleRightAdjointMate_pivotalHom (X : C) :
    rightAdjointMate (rightAdjointMate ((pivotalIso X).hom)) =
      (pivotalIso ((Xᘁ)ᘁ : C)).hom := by
  let jX : X ≅ ((Xᘁ)ᘁ : C) := pivotalIso X
  let jDD : ((Xᘁ)ᘁ : C) ≅ ((((Xᘁ)ᘁ)ᘁ)ᘁ : C) := pivotalIso ((Xᘁ)ᘁ : C)
  have hnat := (pivotalIso_naturality (C := C) (f := jX.hom))
  have hcomp :
      jX.hom ≫ jDD.hom =
        jX.hom ≫ rightAdjointMate (rightAdjointMate jX.hom) := by
    simpa [jX, jDD] using hnat
  have hcancel := (cancel_epi jX.hom).1 hcomp
  simpa [jDD] using hcancel.symm

/-- Naturality specialized to the right-adjoint mate of the pivotal inverse.
This is the core compatibility equation underlying the dual-compatibility
normalization attempts for pivotal traces. -/
theorem pivotalIso_invMate_naturality (X : C) :
    (pivotalIso X).invᘁ ≫ (pivotalIso (((Xᘁ)ᘁ)ᘁ : C)).hom =
      (pivotalIso (Xᘁ : C)).hom ≫ (pivotalIso X).invᘁᘁᘁ := by
  simpa using (pivotalIso_naturality (C := C) (f := (pivotalIso X).invᘁ))

/-- The inverse form of dual compatibility: the pivotal inverse on the dual
    equals the right adjoint mate of the pivotal hom. -/
theorem pivotalIso_dual_compatibility_inv (X : C) :
    (pivotalIso (Xᘁ : C)).inv = (pivotalIso X).homᘁ := by
  rw [← cancel_epi (pivotalIso (Xᘁ : C)).hom, Iso.hom_inv_id,
      pivotalIso_dual_compatibility, ← comp_rightAdjointMate,
      Iso.hom_inv_id, rightAdjointMate_id]

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

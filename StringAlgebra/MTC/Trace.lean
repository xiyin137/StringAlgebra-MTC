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

end StringAlgebra.MTC

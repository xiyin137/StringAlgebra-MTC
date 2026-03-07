/-
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringAlgebra.MTC.Spherical
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

-- Disable diamond-causing instances from Rigid.Braided:
-- These create competing RightRigidCategory/LeftRigidCategory instances
-- that conflict with the direct path through RigidCategory.
-- We only need `exactPairing_swap` from that import.
attribute [-instance] CategoryTheory.BraidedCategory.rightRigidCategoryOfLeftRigidCategory
attribute [-instance] CategoryTheory.BraidedCategory.leftRigidCategoryOfRightRigidCategory
attribute [-instance] CategoryTheory.BraidedCategory.rigidCategoryOfRightRigidCategory
attribute [-instance] CategoryTheory.BraidedCategory.rigidCategoryOfLeftRigidCategory

/-!
# Ribbon Categories

A ribbon category (also called a tortile category) is a braided rigid monoidal
category equipped with a twist (or balancing) natural automorphism θ satisfying
compatibility conditions with the braiding and duals.

Every ribbon category has a canonical pivotal structure.

## Main Definitions

* `RibbonCategory` - Braided rigid category with twist
* `RibbonCategory.toPivotalCategory` - Canonical pivotal structure from twist

## References

* [V. Turaev, *Quantum Invariants of Knots and 3-Manifolds*]
* [N. Reshetikhin, V. Turaev, *Ribbon graphs and their invariants*]
* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*]
-/

namespace StringAlgebra.MTC

open CategoryTheory MonoidalCategory BraidedCategory

universe v₁ u₁

/-- A ribbon category is a braided rigid monoidal category equipped with a
    twist (balancing) θ_X : X ≅ X for each object, satisfying:
    1. Naturality: f ≫ θ_Y = θ_X ≫ f
    2. Tensor compatibility: θ_{X⊗Y} = (β_{Y,X} ∘ β_{X,Y}) ∘ (θ_X ⊗ θ_Y)
    3. Dual compatibility: (θ_X)ᘁ = θ_{Xᘁ}

    The twist encodes the topological spin of anyons in the context of
    topological quantum field theory. -/
class RibbonCategory (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    [BraidedCategory C] [RigidCategory C] where
  /-- The twist (or balancing) isomorphism -/
  twist : ∀ (X : C), X ≅ X
  /-- Naturality of the twist -/
  twist_naturality : ∀ {X Y : C} (f : X ⟶ Y),
    f ≫ (twist Y).hom = (twist X).hom ≫ f
  /-- Compatibility with tensor product and braiding:
      θ_{X⊗Y} = β_{Y,X} ∘ β_{X,Y} ∘ (θ_X ⊗ θ_Y) -/
  twist_tensor : ∀ (X Y : C),
    (twist (X ⊗ Y)).hom =
      ((twist X).hom ⊗ₘ (twist Y).hom) ≫
        (β_ X Y).hom ≫ (β_ Y X).hom
  /-- Compatibility with duals: the adjoint mate of the twist on X
      equals the twist on the dual.
      This ensures θ_{X*} = (θ_X)* -/
  twist_dual : ∀ (X : C),
    rightAdjointMate (twist X).hom = (twist Xᘁ).hom

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable [BraidedCategory C] [RigidCategory C] [RibbonCategory C]

namespace RibbonCategory

/-- Shorthand for the twist isomorphism -/
abbrev θ (X : C) : X ≅ X := twist X

/-- The twist on the tensor unit is the identity. -/
theorem twist_unit : (twist (𝟙_ C)).hom = 𝟙 (𝟙_ C) := by
  -- Step 1: β²_{𝟙,𝟙} = id (from braiding coherence with unit)
  have hβ_sq : (β_ (𝟙_ C) (𝟙_ C)).hom ≫ (β_ (𝟙_ C) (𝟙_ C)).hom = 𝟙 _ := by
    rw [← cancel_mono (λ_ (𝟙_ C)).hom, Category.assoc,
        braiding_leftUnitor, braiding_rightUnitor, Category.id_comp]
  -- Step 2: θ_{𝟙⊗𝟙} = θ_𝟙 ⊗ₘ θ_𝟙 (twist_tensor + β² = id)
  have h_tensor := twist_tensor (𝟙_ C) (𝟙_ C)
  rw [hβ_sq, Category.comp_id] at h_tensor
  -- Step 3: λ ≫ θ = (θ ⊗ₘ θ) ≫ λ (twist_naturality applied to λ)
  have h_nat := twist_naturality (λ_ (𝟙_ C)).hom
  rw [h_tensor] at h_nat
  -- Step 4: (θ ⊗ₘ θ) ≫ λ = λ ≫ θ ≫ θ
  -- Decompose via tensorHom_def', use unitor naturality
  have h_comp : ((twist (𝟙_ C)).hom ⊗ₘ (twist (𝟙_ C)).hom) ≫ (λ_ (𝟙_ C)).hom =
      (λ_ (𝟙_ C)).hom ≫ (twist (𝟙_ C)).hom ≫ (twist (𝟙_ C)).hom := by
    rw [tensorHom_def', Category.assoc]
    conv_lhs =>
      rw [unitors_equal, rightUnitor_naturality, ← unitors_equal,
          ← Category.assoc, leftUnitor_naturality, Category.assoc]
  -- Step 5: θ = θ ≫ θ (cancel λ which is epi)
  have h_eq : (twist (𝟙_ C)).hom =
      (twist (𝟙_ C)).hom ≫ (twist (𝟙_ C)).hom := by
    have := h_nat.trans h_comp
    rwa [cancel_epi] at this
  -- Step 6: θ = 𝟙 (idempotent iso is identity)
  have : (twist (𝟙_ C)).hom ≫ (twist (𝟙_ C)).hom =
      (twist (𝟙_ C)).hom ≫ 𝟙 _ := by
    rw [Category.comp_id]; exact h_eq.symm
  rwa [cancel_epi] at this

/-- The Drinfeld isomorphism u_X : X ≅ (Xᘁ)ᘁ constructed from the braiding.

    This is the canonical isomorphism between two right duals of Xᘁ:
    - The standard right dual (Xᘁ)ᘁ (from `HasRightDual Xᘁ`)
    - X itself, which becomes a right dual of Xᘁ via the braiding
      (from `BraidedCategory.exactPairing_swap X Xᘁ : ExactPairing Xᘁ X`)

    Concretely, the forward map u_X : X → (Xᘁ)ᘁ is:
      X →[ρ⁻¹] X ⊗ 𝟙 →[id ⊗ coev] X ⊗ (Xᘁ ⊗ (Xᘁ)ᘁ) →[α⁻¹] (X ⊗ Xᘁ) ⊗ (Xᘁ)ᘁ
        →[β ⊗ id] (Xᘁ ⊗ X) ⊗ (Xᘁ)ᘁ →[ev ⊗ id] 𝟙 ⊗ (Xᘁ)ᘁ →[λ] (Xᘁ)ᘁ

    The isomorphism property (hom_inv_id and inv_hom_id) follows from
    Mathlib's `rightDualIso` applied to the standard and braiding-swapped
    exact pairings for Xᘁ. -/
noncomputable def drinfeldIsoIso (X : C) : X ≅ (Xᘁ)ᘁ :=
  (rightDualIso
    (inferInstance : ExactPairing Xᘁ (Xᘁ)ᘁ)
    (BraidedCategory.exactPairing_swap X Xᘁ)).symm

omit [BraidedCategory C] [RibbonCategory C] in
/-- Injectivity: if two morphisms to (Yᘁ)ᘁ agree after right-whiskering
    with Yᘁ and composing with evaluation, they are equal. This follows
    from the fact that `tensorRightHomEquiv` is an equivalence. -/
private theorem whiskerRight_eval_cancel {Z : C} {Y : C}
    {f g : Z ⟶ (Yᘁ)ᘁ}
    (h : f ▷ Yᘁ ≫ ε_ Yᘁ (Yᘁ)ᘁ = g ▷ Yᘁ ≫ ε_ Yᘁ (Yᘁ)ᘁ) : f = g := by
  have h2 := congr_arg (tensorRightHomEquiv Z Yᘁ (Yᘁ)ᘁ (𝟙_ C)) h
  simp only [tensorRightHomEquiv_whiskerRight_comp_evaluation] at h2
  exact (cancel_mono (λ_ _).inv).mp h2

omit [RibbonCategory C] in
/-- The Drinfeld isomorphism evaluation property:
    u_X ▷ Xᘁ ≫ ε_{Xᘁ,(Xᘁ)ᘁ} = β_{X,Xᘁ} ≫ ε_{X,Xᘁ}

    This key property says that composing the Drinfeld iso with evaluation
    yields the braiding composed with evaluation. It follows from the
    construction of u_X via `rightAdjointMate (𝟙 Xᘁ)` with mixed
    HasRightDual instances (standard and swap). -/
private theorem drinfeldIsoIso_eval (X : C) :
    (drinfeldIsoIso X).hom ▷ Xᘁ ≫ ε_ Xᘁ (Xᘁ)ᘁ = (β_ X Xᘁ).hom ≫ ε_ X Xᘁ := by
  -- drinfeldIsoIso X = (rightDualIso p_std p_swap).symm
  -- so .hom = rightDualIso.inv = @rightAdjointMate ... ⟨(Xᘁ)ᘁ, p_std⟩ ⟨X, p_swap⟩ (𝟙 Xᘁ)
  -- rightAdjointMate_comp_evaluation with these instances gives the result
  letI : ExactPairing Xᘁ X := BraidedCategory.exactPairing_swap X Xᘁ
  have key := @rightAdjointMate_comp_evaluation C _ _ Xᘁ Xᘁ
    inferInstance (⟨X⟩ : HasRightDual Xᘁ) (𝟙 Xᘁ)
  simp only [MonoidalCategory.whiskerLeft_id, Category.id_comp] at key
  exact key

omit [RibbonCategory C] in
/-- The Drinfeld isomorphism coevaluation property:
    η_{Xᘁ,(Xᘁ)ᘁ} ≫ Xᘁ ◁ u_X⁻¹ = η_swap = η_{X,Xᘁ} ≫ (β_{Xᘁ,X})⁻¹

    Dual to `drinfeldIsoIso_eval`. -/
private theorem drinfeldIsoIso_coeval (X : C) :
    η_ Xᘁ (Xᘁ)ᘁ ≫ Xᘁ ◁ (drinfeldIsoIso X).inv =
      η_ X Xᘁ ≫ (β_ Xᘁ X).inv := by
  letI : ExactPairing Xᘁ X := BraidedCategory.exactPairing_swap X Xᘁ
  have key := @coevaluation_comp_rightAdjointMate C _ _ Xᘁ Xᘁ
    (⟨X⟩ : HasRightDual Xᘁ) inferInstance (𝟙 Xᘁ)
  simp only [id_whiskerRight, Category.comp_id] at key
  exact key

omit [RibbonCategory C] in
/-- The Drinfeld isomorphism is natural: f ≫ u_Y = u_X ≫ fᘁᘁ.

    Proof strategy (testing + injectivity):
    Both sides, when right-whiskered with Yᘁ and composed with ε_{Yᘁ,(Yᘁ)ᘁ},
    give (β_{X,Yᘁ}).hom ≫ fᘁ ▷ X ≫ ε_{X,Xᘁ}. By `whiskerRight_eval_cancel`,
    the two sides are equal. -/
private theorem drinfeldIsoIso_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (drinfeldIsoIso Y).hom =
      (drinfeldIsoIso X).hom ≫ rightAdjointMate (rightAdjointMate f) := by
  apply whiskerRight_eval_cancel
  simp only [comp_whiskerRight, Category.assoc]
  -- Both sides reduce to (β_ X Yᘁ).hom ≫ fᘁ ▷ X ≫ ε_ X Xᘁ
  trans (β_ X Yᘁ).hom ≫ (rightAdjointMate f) ▷ X ≫ ε_ X Xᘁ
  · -- LHS: f ▷ Yᘁ ≫ u_Y ▷ Yᘁ ≫ ε_ → ... → (β_ X Yᘁ).hom ≫ fᘁ ▷ X ≫ ε_
    rw [drinfeldIsoIso_eval, braiding_naturality_left_assoc,
        ← rightAdjointMate_comp_evaluation]
  · -- RHS: u_X ▷ Yᘁ ≫ fᘁᘁ ▷ Yᘁ ≫ ε_ → ... → (β_ X Yᘁ).hom ≫ fᘁ ▷ X ≫ ε_
    symm
    rw [rightAdjointMate_comp_evaluation (rightAdjointMate f),
        ← whisker_exchange_assoc, drinfeldIsoIso_eval,
        braiding_naturality_right_assoc]

-- Key derived identity: η ≫ θ² ▷ Xᘁ ≫ β_{X,Xᘁ} ≫ β_{Xᘁ,X} = η
-- This follows from twist_tensor on η + mate_coeval
private theorem coeval_twist_sq_monodromy (X : C) :
    η_ X Xᘁ ≫ ((twist X).hom ≫ (twist X).hom) ▷ Xᘁ ≫
      (β_ X Xᘁ).hom ≫ (β_ Xᘁ X).hom = η_ X Xᘁ := by
  have h_nat : η_ X Xᘁ ≫ (twist (X ⊗ Xᘁ)).hom = η_ X Xᘁ := by
    have := (twist_naturality (η_ X Xᘁ)).symm
    rw [twist_unit, Category.id_comp] at this; exact this.symm
  rw [twist_tensor] at h_nat
  rw [tensorHom_def] at h_nat
  simp only [Category.assoc] at h_nat
  rw [← whisker_exchange_assoc] at h_nat
  have mate_coeval : η_ X Xᘁ ≫ X ◁ (twist Xᘁ).hom =
      η_ X Xᘁ ≫ (twist X).hom ▷ Xᘁ := by
    have h := coevaluation_comp_rightAdjointMate (twist X).hom
    rw [twist_dual] at h; exact h
  rw [← Category.assoc (η_ X Xᘁ), mate_coeval, Category.assoc] at h_nat
  rw [← comp_whiskerRight_assoc] at h_nat
  exact h_nat

-- Key derived identity: (θ_{Xᘁ})² ▷ X ≫ β_{Xᘁ,X} ≫ β_{X,Xᘁ} ≫ ε = ε
-- This follows from twist_tensor on ε + mate_eval
private theorem eval_twist_sq_monodromy (X : C) :
    ((twist Xᘁ).hom ≫ (twist Xᘁ).hom) ▷ X ≫
      (β_ Xᘁ X).hom ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ = ε_ X Xᘁ := by
  have h_nat : (twist (Xᘁ ⊗ X)).hom ≫ ε_ X Xᘁ = ε_ X Xᘁ := by
    have := twist_naturality (ε_ X Xᘁ)
    rw [twist_unit, Category.comp_id] at this; exact this.symm
  rw [twist_tensor] at h_nat
  simp only [Category.assoc] at h_nat
  rw [tensorHom_def] at h_nat
  simp only [Category.assoc] at h_nat
  have mate_eval : (twist Xᘁ).hom ▷ X ≫ ε_ X Xᘁ =
      Xᘁ ◁ (twist X).hom ≫ ε_ X Xᘁ := by
    have h := rightAdjointMate_comp_evaluation (twist X).hom
    rw [twist_dual] at h; exact h
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  rw [braiding_naturality_left_assoc, braiding_naturality_right_assoc]
  rw [mate_eval]
  rw [← braiding_naturality_left_assoc, ← braiding_naturality_right_assoc]
  exact h_nat

/-- The right adjoint mate of the twist inverse equals the dual twist inverse. -/
private theorem rightAdjointMate_twist_inv (X : C) :
    rightAdjointMate (twist X).inv = (twist Xᘁ).inv := by
  have := congr_arg rightAdjointMate (twist X).hom_inv_id
  rw [comp_rightAdjointMate, rightAdjointMate_id, twist_dual] at this
  exact (cancel_mono (twist Xᘁ).hom).mp (by rw [this, Iso.inv_hom_id])

/-- Key identity: θ ▷ X ≫ c² ≫ ε = θ⁻¹ ▷ X ≫ ε.
    Follows from eval_twist_sq_monodromy by pre-composing with θ⁻¹. -/
private theorem eval_twist_monodromy_cancel (X : C) :
    (twist Xᘁ).hom ▷ X ≫ (β_ Xᘁ X).hom ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ =
      (twist Xᘁ).inv ▷ X ≫ ε_ X Xᘁ := by
  have h := eval_twist_sq_monodromy X
  rw [comp_whiskerRight, Category.assoc] at h
  -- h : θ ▷ X ≫ θ ▷ X ≫ c² ≫ ε = ε
  -- Pre-compose with θ⁻¹ ▷ X and cancel θ⁻¹ ≫ θ
  have h' : (twist Xᘁ).inv ▷ X ≫ (twist Xᘁ).hom ▷ X ≫ (twist Xᘁ).hom ▷ X ≫
      (β_ Xᘁ X).hom ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ =
      (twist Xᘁ).inv ▷ X ≫ ε_ X Xᘁ := by rw [h]
  rw [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp] at h'
  exact h'

/-- A ribbon category has a canonical pivotal structure.

    The pivotal isomorphism j_X : X ≅ (Xᘁ)ᘁ is defined as the composition
    of the twist with the Drinfeld isomorphism:
      j_X = u_X ∘ θ_X

    The Drinfeld isomorphism u_X alone is natural but not monoidal. The
    twist correction θ_X is essential: the twist axiom
    θ_{X⊗Y} = c²_{X,Y} ∘ (θ_X ⊗ θ_Y) cancels the monodromy factor in
    u_{X⊗Y}, making j = u ∘ θ monoidal.

    This follows EGNO Proposition 8.10.5 and the nLab: in a braided rigid
    category, there is a canonical bijection between twists and pivotal
    structures, and the pivotal structure corresponding to θ is
    j_X = u_X ∘ θ_X. -/
noncomputable instance toPivotalCategory : PivotalCategory C where
  pivotalIso X := twist X ≪≫ drinfeldIsoIso X
  pivotalIso_naturality {X Y} f := by
    simp only [Iso.trans_hom, Category.assoc]
    conv_lhs => rw [← Category.assoc, twist_naturality, Category.assoc]
    rw [drinfeldIsoIso_naturality]
  pivotalIso_leftDuality X := by
    -- Step 1: Expand j = θ ≫ u, distribute whiskers, right-associate
    simp only [Iso.trans_hom, Iso.trans_inv,
               whiskerLeft_comp, comp_whiskerRight, Category.assoc]
    -- Step 2: Fold η ≫ Xᘁ◁u⁻¹ → η_swap via drinfeldIsoIso_coeval
    rw [← whiskerLeft_comp_assoc, drinfeldIsoIso_coeval]
    -- Step 3: Fold u▷Xᘁ▷X ≫ ε▷X → ε_swap▷X via drinfeldIsoIso_eval
    slice_lhs 6 7 => rw [← comp_whiskerRight, drinfeldIsoIso_eval]
    simp only [comp_whiskerRight, Category.assoc]
    -- Step 4: Move θ⁻¹ to far right via naturality
    rw [associator_inv_naturality_right_assoc]  -- past α⁻¹
    rw [whisker_exchange_assoc]                  -- past θ▷Xᘁ▷X
    rw [whisker_exchange_assoc]                  -- past (β_ X Xᘁ).hom▷X
    rw [whisker_exchange_assoc]                  -- past ε_ X Xᘁ▷X
    rw [leftUnitor_naturality]                   -- past λ
    -- Step 5: Move θ to far left via naturality
    rw [← associator_inv_naturality_left_assoc]  -- past α⁻¹
    rw [whisker_exchange_assoc]                   -- past X◁η_swap
    rw [← rightUnitor_inv_naturality_assoc]       -- past ρ⁻¹
    -- Step 6: Fold ε_swap and apply swap pairing zigzag
    rw [← comp_whiskerRight_assoc]
    have swap_zig : X ◁ (η_ X Xᘁ ≫ (β_ Xᘁ X).inv) ≫ (α_ X Xᘁ X).inv ≫
        ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ) ▷ X = (ρ_ X).hom ≫ (λ_ X).inv :=
      @ExactPairing.coevaluation_evaluation C _ _ Xᘁ X
        (BraidedCategory.exactPairing_swap X Xᘁ)
    slice_lhs 3 5 => rw [swap_zig]
    -- Step 7: Cancel θ ≫ ρ⁻¹ ≫ ρ ≫ λ⁻¹ ≫ λ ≫ θ⁻¹ = 𝟙
    simp
  pivotalIso_leftDuality_dual X := by
    -- Step 1: Expand j = θ ≫ u, distribute whiskers, right-associate
    simp only [Iso.trans_hom, Iso.trans_inv,
               whiskerLeft_comp, comp_whiskerRight, Category.assoc]
    -- Step 2: Fold coeval pair: η▷Xᘁ ≫ (Xᘁ◁u⁻¹)▷Xᘁ → η_swap▷Xᘁ
    rw [← comp_whiskerRight_assoc, drinfeldIsoIso_coeval]
    -- Step 3: Fold eval pair: Xᘁ◁(u▷Xᘁ) ≫ Xᘁ◁ε → Xᘁ◁ε_swap
    slice_lhs 6 7 => rw [← whiskerLeft_comp, drinfeldIsoIso_eval]
    simp only [whiskerLeft_comp, Category.assoc]
    -- Step 4: Move θ⁻¹ past α via associator_naturality_middle
    rw [associator_naturality_middle_assoc]
    -- Step 5: Cancel θ⁻¹ ≫ θ (now adjacent as Xᘁ◁(θ⁻¹▷Xᘁ) ≫ Xᘁ◁(θ▷Xᘁ))
    rw [← whiskerLeft_comp_assoc, ← comp_whiskerRight, Iso.inv_hom_id,
        id_whiskerRight, MonoidalCategory.whiskerLeft_id, Category.id_comp]
    -- Step 6: Fold ε_swap and apply swap zigzag (evaluation_coevaluation)
    rw [← whiskerLeft_comp_assoc]
    have swap_zig : (η_ X Xᘁ ≫ (β_ Xᘁ X).inv) ▷ Xᘁ ≫ (α_ Xᘁ X Xᘁ).hom ≫
        Xᘁ ◁ ((β_ X Xᘁ).hom ≫ ε_ X Xᘁ) = (λ_ Xᘁ).hom ≫ (ρ_ Xᘁ).inv :=
      @ExactPairing.evaluation_coevaluation C _ _ Xᘁ X
        (BraidedCategory.exactPairing_swap X Xᘁ)
    slice_lhs 2 4 => rw [swap_zig]
    -- Step 7: Cancel λ⁻¹ ≫ λ ≫ ρ⁻¹ ≫ ρ = 𝟙
    simp

  pivotalIso_dual_compatibility X := by
    -- Goal: (twist Xᘁ ≪≫ drinfeldIsoIso Xᘁ).hom = (twist X ≪≫ drinfeldIsoIso X).invᘁ
    -- i.e., θ_{Xᘁ} ≫ u_{Xᘁ} = (u_X⁻¹ ≫ θ_X⁻¹)ᘁ = θ_{Xᘁ}⁻¹ ≫ (u_X⁻¹)ᘁ
    -- Strategy: eval-test both sides ▷ (Xᘁ)ᘁ ≫ ε_ (Xᘁ)ᘁ ((Xᘁ)ᘁ)ᘁ
    apply whiskerRight_eval_cancel
    simp only [Iso.trans_hom, Iso.trans_inv, comp_whiskerRight, Category.assoc]
    -- LHS: θ_{Xᘁ} ▷ _ ≫ u_{Xᘁ} ▷ _ ≫ ε → θ_{Xᘁ} ▷ _ ≫ β ≫ ε_dual
    rw [drinfeldIsoIso_eval Xᘁ]
    -- RHS: decompose (u⁻¹ ≫ θ⁻¹)ᘁ = (θ⁻¹)ᘁ ≫ (u⁻¹)ᘁ, expand, simplify
    rw [comp_rightAdjointMate, comp_whiskerRight, Category.assoc,
        rightAdjointMate_comp_evaluation (f := (drinfeldIsoIso X).inv),
        rightAdjointMate_twist_inv]
    -- Goal: θ ▷ _ ≫ β ≫ ε_dual = θ⁻¹ ▷ _ ≫ Xᘁ ◁ u⁻¹ ≫ ε
    -- Rewrite ε_dual via inverse of drinfeldIsoIso_eval
    have hε : ε_ Xᘁ (Xᘁ)ᘁ =
        (drinfeldIsoIso X).inv ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ := by
      rw [← drinfeldIsoIso_eval, ← comp_whiskerRight_assoc,
          Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
    rw [hε]
    -- LHS: θ ▷ _ ≫ β_{Xᘁ,(Xᘁ)ᘁ} ≫ u⁻¹ ▷ Xᘁ ≫ β_{X,Xᘁ} ≫ ε
    -- Use braiding_naturality_right: β ≫ u⁻¹ ▷ = Xᘁ ◁ u⁻¹ ≫ β
    rw [← braiding_naturality_right_assoc]
    -- Use whisker_exchange: θ ▷ _ ≫ Xᘁ ◁ u⁻¹ = Xᘁ ◁ u⁻¹ ≫ θ ▷ X
    rw [← whisker_exchange_assoc]
    -- Apply θ ▷ X ≫ c² ≫ ε = θ⁻¹ ▷ X ≫ ε
    rw [eval_twist_monodromy_cancel]
    -- Both sides: Xᘁ ◁ u⁻¹ ≫ θ⁻¹ ▷ X ≫ ε = θ⁻¹ ▷ _ ≫ Xᘁ ◁ u⁻¹ ≫ ε
    rw [whisker_exchange_assoc]

/-- In a ribbon category, the canonical pivotal structure is spherical:
    the left and right categorical traces agree for all endomorphisms. -/
private theorem leftTrace_eq_rightTrace {X : C} (f : X ⟶ X) :
    leftTrace (C := C) f = rightTrace (C := C) f := by
  letI : PivotalCategory C := RibbonCategory.toPivotalCategory (C := C)
  let jX : X ≅ (Xᘁ)ᘁ := PivotalCategory.pivotalIso X
  have hjX : jX = twist X ≪≫ drinfeldIsoIso X := rfl
  unfold leftTrace rightTrace
  change
    η_ Xᘁ (Xᘁ)ᘁ ≫ (Xᘁ ◁ jX.inv) ≫ (Xᘁ ◁ f) ≫ ε_ X Xᘁ =
      η_ X Xᘁ ≫ (f ▷ Xᘁ) ≫ (jX.hom ▷ Xᘁ) ≫ ε_ Xᘁ (Xᘁ)ᘁ
  rw [hjX]
  rw [Iso.trans_inv, Iso.trans_hom, whiskerLeft_comp, comp_whiskerRight]
  simp only [Category.assoc]
  calc
    η_ Xᘁ (Xᘁ)ᘁ ≫ (Xᘁ ◁ (drinfeldIsoIso X).inv) ≫ (Xᘁ ◁ (twist X).inv) ≫
        (Xᘁ ◁ f) ≫ ε_ X Xᘁ
      = η_ X Xᘁ ≫ (β_ Xᘁ X).inv ≫ (Xᘁ ◁ (twist X).inv) ≫ (Xᘁ ◁ f) ≫ ε_ X Xᘁ := by
          simpa [Category.assoc] using
            congrArg
              (fun t => t ≫ (Xᘁ ◁ (twist X).inv) ≫ (Xᘁ ◁ f) ≫ ε_ X Xᘁ)
              (drinfeldIsoIso_coeval (C := C) X)
    _ = η_ X Xᘁ ≫ ((twist X).hom ≫ (twist X).hom) ▷ Xᘁ ≫
          (β_ X Xᘁ).hom ≫ (β_ Xᘁ X).hom ≫ (β_ Xᘁ X).inv ≫
          (Xᘁ ◁ (twist X).inv) ≫ (Xᘁ ◁ f) ≫ ε_ X Xᘁ := by
          simpa [Category.assoc] using
            congrArg
              (fun t => t ≫ (β_ Xᘁ X).inv ≫ (Xᘁ ◁ (twist X).inv) ≫
                (Xᘁ ◁ f) ≫ ε_ X Xᘁ)
              (coeval_twist_sq_monodromy (C := C) X).symm
    _ = η_ X Xᘁ ≫ ((twist X).hom ≫ (twist X).hom) ▷ Xᘁ ≫
          (β_ X Xᘁ).hom ≫ (Xᘁ ◁ (twist X).inv) ≫ (Xᘁ ◁ f) ≫ ε_ X Xᘁ := by
          simp
    _ = η_ X Xᘁ ≫ (twist X).hom ▷ Xᘁ ≫ (twist X).hom ▷ Xᘁ ≫
          (β_ X Xᘁ).hom ≫ (Xᘁ ◁ (twist X).inv) ≫ (Xᘁ ◁ f) ≫ ε_ X Xᘁ := by
          simp [comp_whiskerRight, Category.assoc]
    _ = η_ X Xᘁ ≫ (twist X).hom ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫
          (Xᘁ ◁ (twist X).hom) ≫ (Xᘁ ◁ (twist X).inv) ≫ (Xᘁ ◁ f) ≫ ε_ X Xᘁ := by
          simpa using
            congrArg
              (fun t => η_ X Xᘁ ≫ (twist X).hom ▷ Xᘁ ≫ t ≫
                (Xᘁ ◁ (twist X).inv) ≫ (Xᘁ ◁ f) ≫ ε_ X Xᘁ)
              (BraidedCategory.braiding_naturality_left
                (f := (twist X).hom) (Y := Xᘁ))
    _ = η_ X Xᘁ ≫ (twist X).hom ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ (Xᘁ ◁ f) ≫ ε_ X Xᘁ := by
          simp
    _ = η_ X Xᘁ ≫ (twist X).hom ▷ Xᘁ ≫ f ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ := by
          simpa using
            congrArg
              (fun t => η_ X Xᘁ ≫ (twist X).hom ▷ Xᘁ ≫ t ≫ ε_ X Xᘁ)
              (BraidedCategory.braiding_naturality_left (f := f) (Y := Xᘁ)).symm
    _ = η_ X Xᘁ ≫ ((twist X).hom ≫ f) ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ := by
          rw [← comp_whiskerRight_assoc]
    _ = η_ X Xᘁ ≫ (f ≫ (twist X).hom) ▷ Xᘁ ≫ (β_ X Xᘁ).hom ≫ ε_ X Xᘁ := by
          rw [twist_naturality]
    _ = η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (twist X).hom ▷ Xᘁ ≫
          (β_ X Xᘁ).hom ≫ ε_ X Xᘁ := by
          rw [comp_whiskerRight, Category.assoc]
    _ = η_ X Xᘁ ≫ f ▷ Xᘁ ≫ (twist X).hom ▷ Xᘁ ≫
          (drinfeldIsoIso X).hom ▷ Xᘁ ≫ ε_ Xᘁ (Xᘁ)ᘁ := by
          rw [drinfeldIsoIso_eval]

noncomputable instance toSphericalCategory : SphericalCategory C where
  spherical f := leftTrace_eq_rightTrace (C := C) f

/-- The monodromy (double braiding) of X with Y:
    c_{Y,X} ∘ c_{X,Y} : X ⊗ Y → X ⊗ Y -/
def monodromy (X Y : C) : X ⊗ Y ⟶ X ⊗ Y :=
  (β_ X Y).hom ≫ (β_ Y X).hom

/-- The twist satisfies θ_{X⊗Y} = monodromy(X,Y) ∘ (θ_X ⊗ θ_Y) -/
theorem twist_tensor' (X Y : C) :
    (twist (X ⊗ Y)).hom = ((twist X).hom ⊗ₘ (twist Y).hom) ≫ monodromy X Y :=
  twist_tensor X Y

end RibbonCategory

end StringAlgebra.MTC

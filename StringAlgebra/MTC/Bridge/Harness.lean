import StringAlgebra.MTC.Bridge.VOAToMTC

/-!
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Bridge Harness

Integration checks for the explicit VOA-to-MTC theorem interfaces.
-/

namespace StringAlgebra.MTC.Bridge

open CategoryTheory MonoidalCategory CategoryTheory.Limits

universe v₁ u₁

section Nondegeneracy

variable {k : Type u₁} [Field k]
variable {RepV : Type u₁} [Category.{v₁} RepV] [MonoidalCategory RepV]
variable [BraidedCategory RepV] [Preadditive RepV] [Linear k RepV]
variable [MonoidalPreadditive RepV] [HasFiniteBiproducts RepV] [RigidCategory RepV]
variable [RibbonFusionCategory k RepV]

theorem nondegeneracy_from_huang
    (i : FusionCategory.Idx (k := k) (C := RepV))
    (h : BraidedFusionCategory.isTransparent (FusionCategory.simpleObj i))
    (hHuang :
      ∀ j : FusionCategory.Idx (k := k) (C := RepV),
        BraidedFusionCategory.isTransparent (FusionCategory.simpleObj j) →
        Nonempty (FusionCategory.simpleObj j ≅ 𝟙_ RepV)) :
    Nonempty (FusionCategory.simpleObj i ≅ 𝟙_ RepV) :=
  huang_nondegeneracy (k := k) (RepV := RepV) i h hHuang

noncomputable def modularity_from_huang
    (hHuang :
      ∀ i : FusionCategory.Idx (k := k) (C := RepV),
        BraidedFusionCategory.isTransparent (FusionCategory.simpleObj i) →
        Nonempty (FusionCategory.simpleObj i ≅ 𝟙_ RepV)) :
    ModularTensorCategory k RepV :=
  modularTensorCategoryOfHuang (k := k) (RepV := RepV) hHuang

end Nondegeneracy

section TwistRoots

variable {k : Type u₁} [Field k] [IsAlgClosed k]
variable {RepV : Type u₁} [Category.{v₁} RepV] [MonoidalCategory RepV]
variable [BraidedCategory RepV] [Preadditive RepV] [Linear k RepV]
variable [MonoidalPreadditive RepV] [HasFiniteBiproducts RepV] [RigidCategory RepV]
variable [RibbonFusionCategory k RepV] [HasKernels RepV]

theorem twist_roots_from_hypothesis
    (i : FusionCategory.Idx (k := k) (C := RepV))
    (hTwistRoots :
      ∀ j : FusionCategory.Idx (k := k) (C := RepV),
        ∃ (n : ℕ) (_ : 0 < n),
          RibbonFusionCategory.twistValue (C := RepV) j ^ n = (1 : k)) :
    ∃ (n : ℕ) (_ : 0 < n),
      RibbonFusionCategory.twistValue (C := RepV) i ^ n = (1 : k) :=
  twist_roots_of_unity (k := k) (RepV := RepV) i hTwistRoots

end TwistRoots

end StringAlgebra.MTC.Bridge

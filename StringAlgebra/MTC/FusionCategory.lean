/-
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringAlgebra.MTC.Semisimple
import StringAlgebra.MTC.Pivotal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Fusion Categories

A fusion category is a k-linear semisimple rigid monoidal category with finitely
many isomorphism classes of simple objects, finite-dimensional Hom spaces, and
simple tensor unit.

## Main Definitions

* `FusionCategory` - The main class combining all axioms
* `FusionCategory.fusionCoeff` - The fusion coefficients N^m_{ij} = dim_k Hom(X_i ⊗ X_j, X_m)

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*], Ch. 4
* [P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*]
-/

namespace StringAlgebra.MTC

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v₁ u₁

/-- A fusion category over a field k is a k-linear, semisimple, rigid monoidal
    category with finitely many simple isoclasses, finite-dimensional Homs,
    and simple tensor unit.

    The data includes:
    - A finite type `Idx` indexing the simple isoclasses
    - Representative simple objects `simpleObj i` for each index
    - A distinguished unit index with an explicit isomorphism to the unit
    - A duality operation on indices with explicit isomorphisms to duals -/
class FusionCategory (k : Type u₁) [Field k]
    (C : Type u₁) [Category.{v₁} C]
    [MonoidalCategory C] [Preadditive C] [Linear k C]
    [MonoidalPreadditive C]
    [HasFiniteBiproducts C] [RigidCategory C]
    extends SemisimpleCategory C where
  /-- The finite type indexing simple isoclasses -/
  Idx : Type
  /-- The indexing type is finite -/
  [idx_fintype : Fintype Idx]
  /-- Decidable equality on the indexing type -/
  [idx_decidableEq : DecidableEq Idx]
  /-- Representative simple object for each index -/
  simpleObj : Idx → C
  /-- Each representative is simple -/
  simpleObj_simple : ∀ (i : Idx), Simple (simpleObj i)
  /-- Every simple is isomorphic to some representative -/
  simpleObj_exhaustive : ∀ (X : C), Simple X → ∃ (i : Idx), Nonempty (X ≅ simpleObj i)
  /-- Hom spaces are finite-dimensional k-vector spaces -/
  finiteDimensionalHom : ∀ (X Y : C), Module.Finite k (X ⟶ Y)
  /-- The tensor unit is a simple object -/
  unit_simple : Simple (𝟙_ C)
  /-- Distinguished index for the unit -/
  unitIdx : Idx
  /-- An isomorphism between the unit representative and the tensor unit -/
  unitIdx_iso : simpleObj unitIdx ≅ 𝟙_ C
  /-- Duality operation on indices -/
  dualIdx : Idx → Idx
  /-- The dual of X_i is isomorphic to X_{dualIdx i} -/
  dualIdx_iso : ∀ (i : Idx), (simpleObj i)ᘁ ≅ simpleObj (dualIdx i)
  /-- Semisimple multiplicity transport for right tensoring by a simple object:
      decompose `Hom(A ⊗ X_l, X_m)` through simple summands of `A`. -/
  tensorRight_finrank_decompose :
    ∀ (A : C) (l m : Idx),
      Module.finrank k (A ⊗ simpleObj l ⟶ simpleObj m) =
        ∑ p : Idx,
          Module.finrank k (A ⟶ simpleObj p) *
            Module.finrank k (simpleObj p ⊗ simpleObj l ⟶ simpleObj m)
  /-- Semisimple multiplicity transport for left tensoring by a simple object:
      decompose `Hom(X_i ⊗ A, X_m)` through simple summands of `A`. -/
  tensorLeft_finrank_decompose :
    ∀ (A : C) (i m : Idx),
      Module.finrank k (simpleObj i ⊗ A ⟶ simpleObj m) =
        ∑ q : Idx,
          Module.finrank k (A ⟶ simpleObj q) *
            Module.finrank k (simpleObj i ⊗ simpleObj q ⟶ simpleObj m)
  /-- Semisimple Hom-dimension symmetry: the multiplicity of a simple
      in the Hom-from and Hom-to directions agree.

      This is a standard consequence of semisimplicity (the non-degenerate
      trace pairing identifies `Hom(S_i, X)` and `Hom(X, S_i)` as vector
      spaces of equal dimension). The current `FusionCategory` axioms do
      not include a full semisimple decomposition for arbitrary objects, so
      this is included as a structural axiom at the class level. -/
  simpleHomSymm :
    ∀ (a : Idx) (X : C),
      Module.finrank k (simpleObj a ⟶ X) =
        Module.finrank k (X ⟶ simpleObj a)

-- Explicit instances to help typeclass resolution
noncomputable instance instFintypeFusionIdx {k : Type u₁} [Field k]
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    [Preadditive C] [Linear k C] [MonoidalPreadditive C]
    [HasFiniteBiproducts C] [RigidCategory C]
    [FusionCategory k C] :
    Fintype (FusionCategory.Idx (k := k) (C := C)) :=
  FusionCategory.idx_fintype

instance instDecidableEqFusionIdx {k : Type u₁} [Field k]
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    [Preadditive C] [Linear k C] [MonoidalPreadditive C]
    [HasFiniteBiproducts C] [RigidCategory C]
    [FusionCategory k C] :
    DecidableEq (FusionCategory.Idx (k := k) (C := C)) :=
  FusionCategory.idx_decidableEq

variable {k : Type u₁} [Field k]
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable [Preadditive C] [Linear k C] [MonoidalPreadditive C]
variable [HasFiniteBiproducts C] [RigidCategory C]
variable [FusionCategory k C]

namespace FusionCategory

/-- The rank of the fusion category (number of simple isoclasses). -/
noncomputable def rank : ℕ := Fintype.card (Idx (k := k) (C := C))

/-- Optional coherence assumption for indexing simples:
isomorphic chosen representatives have equal indices. -/
class CanonicalSimpleIndex : Prop where
  eq_of_iso :
    ∀ {i j : Idx (k := k) (C := C)},
      Nonempty (simpleObj (k := k) i ≅ simpleObj (k := k) j) → i = j

theorem simpleObj_iso_of_eq
    {i j : Idx (k := k) (C := C)} (h : i = j) :
    Nonempty (simpleObj (k := k) i ≅ simpleObj (k := k) j) := by
  subst h
  exact ⟨Iso.refl _⟩

@[simp] theorem simpleObj_iso_iff_eq
    [CanonicalSimpleIndex (k := k) (C := C)]
    (i j : Idx (k := k) (C := C)) :
    Nonempty (simpleObj (k := k) i ≅ simpleObj (k := k) j) ↔ i = j := by
  constructor
  · intro h
    exact CanonicalSimpleIndex.eq_of_iso (k := k) (C := C) h
  · intro h
    exact simpleObj_iso_of_eq (k := k) (C := C) h

section DualIndexCoherence

variable [PivotalCategory C]
variable [CanonicalSimpleIndex (k := k) (C := C)]

/-- In a pivotal setting with canonical indexing, the chosen dual index is
involutive up to equality on indices. -/
noncomputable def dualIdxDoubleIso
    (i : Idx (k := k) (C := C)) :
    simpleObj (k := k) (C := C) i ≅ simpleObj (k := k) (C := C) (dualIdx (dualIdx i)) := by
  let e : (simpleObj (k := k) (C := C) i)ᘁ ≅
      simpleObj (k := k) (C := C) (dualIdx i) :=
    dualIdx_iso (k := k) (C := C) i
  let eDD : ((simpleObj (k := k) (C := C) i)ᘁ)ᘁ ≅
      (simpleObj (k := k) (C := C) (dualIdx i))ᘁ :=
    { hom := e.invᘁ
      inv := e.homᘁ
      hom_inv_id := by
        simpa using (comp_rightAdjointMate (f := e.hom) (g := e.inv)).symm
      inv_hom_id := by
        simpa using (comp_rightAdjointMate (f := e.inv) (g := e.hom)).symm }
  exact
    (PivotalCategory.pivotalIso (C := C) (simpleObj (k := k) (C := C) i)) ≪≫
      eDD ≪≫ (dualIdx_iso (k := k) (C := C) (dualIdx i))

/-- Index-level involutivity of `dualIdx` under pivotal transport and canonical
index coherence. -/
theorem dualIdx_involutive_pivotal
    (i : Idx (k := k) (C := C)) :
    dualIdx (dualIdx i) = i := by
  apply CanonicalSimpleIndex.eq_of_iso (k := k) (C := C)
  exact ⟨(dualIdxDoubleIso (k := k) (C := C) i).symm⟩

end DualIndexCoherence

/-- The fusion coefficients N^m_{ij} = dim_k Hom(X_i ⊗ X_j, X_m).

    This is the dimension of the space of morphisms from the tensor product
    of simple objects X_i and X_j to the simple object X_m. By semisimplicity,
    this equals the multiplicity of X_m in the decomposition of X_i ⊗ X_j. -/
noncomputable def fusionCoeff (i j m : Idx (k := k) (C := C)) : ℕ :=
  Module.finrank k (simpleObj i ⊗ simpleObj j ⟶ simpleObj m)

/-- The dual of a simple object is simple. -/
theorem dual_simple (i : Idx (k := k) (C := C)) : Simple (simpleObj i)ᘁ := by
  haveI := simpleObj_simple (k := k) (C := C) (dualIdx i)
  exact Simple.of_iso (dualIdx_iso i)

/-- Chosen simple representatives are nonzero objects. -/
theorem simpleObj_not_isZero (i : Idx (k := k) (C := C)) :
    ¬ IsZero (simpleObj (k := k) (C := C) i) := by
  haveI := simpleObj_simple (k := k) (C := C) i
  exact Simple.not_isZero (simpleObj (k := k) (C := C) i)

/-- Every nonzero object admits a nonzero morphism to some chosen simple
representative. -/
theorem exists_nonzero_hom_to_simpleObj_of_not_isZero
    (X : C) (hX : ¬ IsZero X) :
    ∃ (i : Idx (k := k) (C := C)) (f : X ⟶ simpleObj (k := k) (C := C) i), f ≠ 0 := by
  obtain ⟨S, hS, f, hf⟩ :=
    SemisimpleCategory.exists_nonzero_to_simple_of_not_isZero (C := C) X hX
  obtain ⟨i, ⟨e⟩⟩ := simpleObj_exhaustive (k := k) (C := C) S hS
  refine ⟨i, f ≫ e.hom, ?_⟩
  intro h
  apply hf
  exact zero_of_comp_mono e.hom h

/-- Every nonzero object receives a nonzero morphism from some chosen simple
representative. -/
theorem exists_nonzero_hom_from_simpleObj_of_not_isZero
    (X : C) (hX : ¬ IsZero X) :
    ∃ (i : Idx (k := k) (C := C)) (f : simpleObj (k := k) (C := C) i ⟶ X), f ≠ 0 := by
  obtain ⟨S, hS, f, hf⟩ :=
    SemisimpleCategory.exists_nonzero_from_simple_of_not_isZero (C := C) X hX
  obtain ⟨i, ⟨e⟩⟩ := simpleObj_exhaustive (k := k) (C := C) S hS
  refine ⟨i, e.inv ≫ f, ?_⟩
  intro h
  apply hf
  exact zero_of_epi_comp e.inv h

/-- Right-adjoint Hom equivalence used in Frobenius-style rewrites:
    `Hom(Xᵢ ⊗ Xⱼ, Xₘ) ≃ Hom(Xᵢ, Xₘ ⊗ Xⱼᘁ)`. -/
noncomputable def homTensorAdjointEquiv
    (i j m : Idx (k := k) (C := C)) :
    (simpleObj i ⊗ simpleObj j ⟶ simpleObj m) ≃
      (simpleObj i ⟶ simpleObj m ⊗ (simpleObj j)ᘁ) :=
  tensorRightHomEquiv (simpleObj i) (simpleObj j) ((simpleObj j)ᘁ) (simpleObj m)

/-- `homTensorAdjointEquiv` rewritten through the chosen dual index representative. -/
noncomputable def homTensorAdjointDualIdxEquiv
    (i j m : Idx (k := k) (C := C)) :
    (simpleObj i ⊗ simpleObj j ⟶ simpleObj m) ≃
      (simpleObj i ⟶ simpleObj m ⊗ simpleObj (dualIdx j)) := by
  let e0 :
      (simpleObj i ⊗ simpleObj j ⟶ simpleObj m) ≃
        (simpleObj i ⟶ simpleObj m ⊗ (simpleObj j)ᘁ) :=
    homTensorAdjointEquiv (k := k) (C := C) i j m
  let e1 : simpleObj m ⊗ (simpleObj j)ᘁ ≅ simpleObj m ⊗ simpleObj (dualIdx j) :=
    whiskerLeftIso (simpleObj m) (dualIdx_iso (k := k) (C := C) j)
  refine
    { toFun := fun f => e0 f ≫ e1.hom
      invFun := fun g => e0.symm (g ≫ e1.inv)
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    simp [e0, e1]
  · intro g
    simp [e0, e1]

section LinearAdjunction

variable [CategoryTheory.MonoidalLinear k C]

/-- Linearization of `homTensorAdjointEquiv` (requires `MonoidalLinear`). -/
noncomputable def homTensorAdjointLinearEquiv
    (i j m : Idx (k := k) (C := C)) :
    (simpleObj i ⊗ simpleObj j ⟶ simpleObj m) ≃ₗ[k]
      (simpleObj i ⟶ simpleObj m ⊗ (simpleObj j)ᘁ) where
  toFun := homTensorAdjointEquiv (k := k) (C := C) i j m
  invFun := (homTensorAdjointEquiv (k := k) (C := C) i j m).symm
  left_inv := by
    intro f
    exact (homTensorAdjointEquiv (k := k) (C := C) i j m).left_inv f
  right_inv := by
    intro f
    exact (homTensorAdjointEquiv (k := k) (C := C) i j m).right_inv f
  map_add' := by
    intro f g
    change (ρ_ _).inv ≫ _ ◁ η_ _ _ ≫ (α_ _ _ _).inv ≫ (f + g) ▷ _ =
      ((ρ_ _).inv ≫ _ ◁ η_ _ _ ≫ (α_ _ _ _).inv ≫ f ▷ _) +
      ((ρ_ _).inv ≫ _ ◁ η_ _ _ ≫ (α_ _ _ _).inv ≫ g ▷ _)
    simp
  map_smul' := by
    intro r f
    change (ρ_ _).inv ≫ _ ◁ η_ _ _ ≫ (α_ _ _ _).inv ≫ (r • f) ▷ _ =
      r • ((ρ_ _).inv ≫ _ ◁ η_ _ _ ≫ (α_ _ _ _).inv ≫ f ▷ _)
    simp

/-- Finrank form of right-adjoint Hom transport:
    `dim Hom(Xᵢ ⊗ Xⱼ, Xₘ) = dim Hom(Xᵢ, Xₘ ⊗ Xⱼᘁ)`. -/
theorem finrank_hom_tensor_eq_finrank_hom_tensor_rightDual
    (i j m : Idx (k := k) (C := C)) :
    Module.finrank k (simpleObj i ⊗ simpleObj j ⟶ simpleObj m) =
      Module.finrank k (simpleObj i ⟶ simpleObj m ⊗ (simpleObj j)ᘁ) := by
  exact LinearEquiv.finrank_eq
    (homTensorAdjointLinearEquiv (k := k) (C := C) i j m)

/-- Finrank form of right-adjoint Hom transport rewritten through `dualIdx`. -/
theorem finrank_hom_tensor_eq_finrank_hom_tensor_dualIdx
    (i j m : Idx (k := k) (C := C)) :
    Module.finrank k (simpleObj i ⊗ simpleObj j ⟶ simpleObj m) =
      Module.finrank k (simpleObj i ⟶ simpleObj m ⊗ simpleObj (dualIdx j)) := by
  calc
    Module.finrank k (simpleObj i ⊗ simpleObj j ⟶ simpleObj m)
        = Module.finrank k (simpleObj i ⟶ simpleObj m ⊗ (simpleObj j)ᘁ) := by
          exact finrank_hom_tensor_eq_finrank_hom_tensor_rightDual
            (k := k) (C := C) i j m
    _ = Module.finrank k (simpleObj i ⟶ simpleObj m ⊗ simpleObj (dualIdx j)) := by
        exact LinearEquiv.finrank_eq
          (Linear.homCongr k (Iso.refl (simpleObj i))
            (whiskerLeftIso (simpleObj m) (dualIdx_iso (k := k) (C := C) j)))

/-- Frobenius-adjunction rewrite of `fusionCoeff` through `dualIdx` on the right
    tensor factor (requires `MonoidalLinear`). -/
theorem fusionCoeff_eq_finrank_hom_tensor_dualIdx
    (i j m : Idx (k := k) (C := C)) :
    fusionCoeff (k := k) i j m =
      Module.finrank k (simpleObj i ⟶ simpleObj m ⊗ simpleObj (dualIdx j)) := by
  unfold fusionCoeff
  exact finrank_hom_tensor_eq_finrank_hom_tensor_dualIdx
    (k := k) (C := C) i j m

/-- Frobenius-adjunction rewrite of `fusionCoeff` through the raw right dual
    object on the right tensor factor (requires `MonoidalLinear`). -/
theorem fusionCoeff_eq_finrank_hom_tensor_rightDual
    (i j m : Idx (k := k) (C := C)) :
    fusionCoeff (k := k) i j m =
      Module.finrank k (simpleObj i ⟶ simpleObj m ⊗ (simpleObj j)ᘁ) := by
  unfold fusionCoeff
  exact finrank_hom_tensor_eq_finrank_hom_tensor_rightDual
    (k := k) (C := C) i j m

/-- Specialized adjunction rewrite for the right-dual-index input:
    `N^i_{m,j*}` as a Hom-into-tensor finrank with `dualIdx (dualIdx j)`. -/
theorem fusionCoeff_dualIdx_right_eq_finrank_hom_tensor_dualDualIdx
    (i j m : Idx (k := k) (C := C)) :
    fusionCoeff (k := k) m (dualIdx j) i =
      Module.finrank k (simpleObj m ⟶ simpleObj i ⊗ simpleObj (dualIdx (dualIdx j))) := by
  exact fusionCoeff_eq_finrank_hom_tensor_dualIdx
    (k := k) (C := C) m (dualIdx j) i

end LinearAdjunction

section FusionVacuum

variable [IsAlgClosed k] [HasKernels C]

/-- Module.Finite instance for Hom spaces in a fusion category. -/
instance instFiniteDimensionalHom (X Y : C) : Module.Finite k (X ⟶ Y) :=
  finiteDimensionalHom X Y

/-- Fusion with the vacuum: N^m_{0,j} = δ_{m,j}.
    More precisely, if X_j ≅ X_m then N^m_{0j} = 1, otherwise 0. -/
theorem fusionCoeff_vacuum_eq (j : Idx (k := k) (C := C)) :
    fusionCoeff (k := k) unitIdx j j = 1 := by
  unfold fusionCoeff
  -- simpleObj unitIdx ⊗ simpleObj j ≅ 𝟙 ⊗ simpleObj j ≅ simpleObj j
  have iso : simpleObj (k := k) unitIdx ⊗ simpleObj j ≅ simpleObj j :=
    (whiskerRightIso unitIdx_iso (simpleObj j)) ≪≫ (λ_ (simpleObj j))
  -- Transfer finrank via linear equiv
  rw [LinearEquiv.finrank_eq (Linear.homCongr k iso (Iso.refl (simpleObj j)))]
  -- Now finrank k (simpleObj j ⟶ simpleObj j) = 1 by Schur
  haveI := simpleObj_simple (k := k) (C := C) j
  exact finrank_endomorphism_simple_eq_one k (simpleObj j)

/-- Right vacuum fusion: `N^i_{i,0} = 1`. -/
theorem fusionCoeff_right_vacuum_eq (i : Idx (k := k) (C := C)) :
    fusionCoeff (k := k) i unitIdx i = 1 := by
  unfold fusionCoeff
  have iso :
      simpleObj (k := k) i ⊗ simpleObj (k := k) (C := C) (unitIdx (k := k) (C := C)) ≅
        simpleObj (k := k) i :=
    (whiskerLeftIso (simpleObj (k := k) i) (unitIdx_iso (k := k) (C := C))) ≪≫
      (ρ_ (simpleObj (k := k) i))
  rw [LinearEquiv.finrank_eq (Linear.homCongr k iso (Iso.refl (simpleObj i)))]
  haveI := simpleObj_simple (k := k) (C := C) i
  exact finrank_endomorphism_simple_eq_one k (simpleObj i)

/-- If `X_j` and `X_m` are isomorphic simples, then `N^m_{0,j} = 1`. -/
theorem fusionCoeff_vacuum_iso
    (j m : Idx (k := k) (C := C))
    (h : Nonempty (simpleObj j ≅ simpleObj m)) :
    fusionCoeff (k := k) unitIdx j m = 1 := by
  unfold fusionCoeff
  have iso : simpleObj (k := k) unitIdx ⊗ simpleObj j ≅ simpleObj j :=
    (whiskerRightIso unitIdx_iso (simpleObj j)) ≪≫ (λ_ (simpleObj j))
  rw [LinearEquiv.finrank_eq (Linear.homCongr k iso (Iso.refl (simpleObj m)))]
  haveI := simpleObj_simple (k := k) (C := C) j
  haveI := simpleObj_simple (k := k) (C := C) m
  exact (finrank_hom_simple_simple_eq_one_iff k (simpleObj j) (simpleObj m)).2 h

/-- If `X_i` and `X_m` are isomorphic simples, then `N^m_{i,0} = 1`. -/
theorem fusionCoeff_right_vacuum_iso
    (i m : Idx (k := k) (C := C))
    (h : Nonempty (simpleObj i ≅ simpleObj m)) :
    fusionCoeff (k := k) i unitIdx m = 1 := by
  unfold fusionCoeff
  have iso :
      simpleObj (k := k) i ⊗ simpleObj (k := k) (C := C) (unitIdx (k := k) (C := C)) ≅
        simpleObj (k := k) i :=
    (whiskerLeftIso (simpleObj (k := k) i) (unitIdx_iso (k := k) (C := C))) ≪≫
      (ρ_ (simpleObj (k := k) i))
  rw [LinearEquiv.finrank_eq (Linear.homCongr k iso (Iso.refl (simpleObj m)))]
  haveI := simpleObj_simple (k := k) (C := C) i
  haveI := simpleObj_simple (k := k) (C := C) m
  exact (finrank_hom_simple_simple_eq_one_iff k (simpleObj i) (simpleObj m)).2 h

omit [IsAlgClosed k] in
theorem fusionCoeff_vacuum_ne (j m : Idx (k := k) (C := C))
    (h : ¬Nonempty (simpleObj j ≅ simpleObj m)) :
    fusionCoeff (k := k) unitIdx j m = 0 := by
  unfold fusionCoeff
  have iso : simpleObj (k := k) unitIdx ⊗ simpleObj j ≅ simpleObj j :=
    (whiskerRightIso unitIdx_iso (simpleObj j)) ≪≫ (λ_ (simpleObj j))
  rw [LinearEquiv.finrank_eq (Linear.homCongr k iso (Iso.refl (simpleObj m)))]
  haveI := simpleObj_simple (k := k) (C := C) j
  haveI := simpleObj_simple (k := k) (C := C) m
  apply finrank_hom_simple_simple_eq_zero_of_not_iso
  intro i; exact h ⟨i⟩

omit [IsAlgClosed k] in
theorem fusionCoeff_right_vacuum_ne (i m : Idx (k := k) (C := C))
    (h : ¬Nonempty (simpleObj i ≅ simpleObj m)) :
    fusionCoeff (k := k) i unitIdx m = 0 := by
  unfold fusionCoeff
  have iso :
      simpleObj (k := k) i ⊗ simpleObj (k := k) (C := C) (unitIdx (k := k) (C := C)) ≅
        simpleObj (k := k) i :=
    (whiskerLeftIso (simpleObj (k := k) i) (unitIdx_iso (k := k) (C := C))) ≪≫
      (ρ_ (simpleObj (k := k) i))
  rw [LinearEquiv.finrank_eq (Linear.homCongr k iso (Iso.refl (simpleObj m)))]
  haveI := simpleObj_simple (k := k) (C := C) i
  haveI := simpleObj_simple (k := k) (C := C) m
  apply finrank_hom_simple_simple_eq_zero_of_not_iso
  intro him
  exact h ⟨him⟩

/-- Vacuum fusion as a Kronecker delta on indices, under canonical indexing. -/
theorem fusionCoeff_vacuum_kronecker
    [CanonicalSimpleIndex (k := k) (C := C)]
    (j m : Idx (k := k) (C := C)) :
    fusionCoeff (k := k) unitIdx j m = if j = m then 1 else 0 := by
  by_cases hEq : j = m
  · subst hEq
    simp [fusionCoeff_vacuum_eq]
  · have hIso : ¬Nonempty (simpleObj j ≅ simpleObj m) := by
      intro h
      exact hEq (CanonicalSimpleIndex.eq_of_iso (k := k) (C := C) h)
    simp [hEq, fusionCoeff_vacuum_ne (k := k) (C := C) j m hIso]

/-- Right vacuum fusion as a Kronecker delta on indices, under canonical indexing. -/
theorem fusionCoeff_right_vacuum_kronecker
    [CanonicalSimpleIndex (k := k) (C := C)]
    (i m : Idx (k := k) (C := C)) :
    fusionCoeff (k := k) i unitIdx m = if i = m then 1 else 0 := by
  by_cases hEq : i = m
  · subst hEq
    simp [fusionCoeff_right_vacuum_eq]
  · have hIso : ¬Nonempty (simpleObj i ≅ simpleObj m) := by
      intro h
      exact hEq (CanonicalSimpleIndex.eq_of_iso (k := k) (C := C) h)
    simp [hEq, fusionCoeff_right_vacuum_ne (k := k) (C := C) i m hIso]

end FusionVacuum

/-- Associativity of fusion coefficients.

Proof path: semisimple multiplicity decomposition on both tensor
parenthesizations, then associator transport of Hom-finrank. -/
theorem fusionCoeff_assoc
    (i j l m : Idx (k := k) (C := C)) :
    ∑ p, fusionCoeff (k := k) i j p * fusionCoeff p l m =
    ∑ q, fusionCoeff (k := k) j l q * fusionCoeff i q m := by
  let Xi : C := simpleObj (k := k) (C := C) i
  let Xj : C := simpleObj (k := k) (C := C) j
  let Xl : C := simpleObj (k := k) (C := C) l
  let Xm : C := simpleObj (k := k) (C := C) m
  calc
    ∑ p : Idx (k := k) (C := C),
        fusionCoeff (k := k) i j p * fusionCoeff (k := k) p l m
      =
        ∑ p : Idx (k := k) (C := C),
          Module.finrank k (Xi ⊗ Xj ⟶ simpleObj (k := k) (C := C) p) *
            Module.finrank k (simpleObj (k := k) (C := C) p ⊗ Xl ⟶ Xm) := by
          simp [fusionCoeff, Xi, Xj, Xl, Xm]
    _ = Module.finrank k ((Xi ⊗ Xj) ⊗ Xl ⟶ Xm) := by
      symm
      simpa [Xi, Xj, Xl, Xm] using
        (tensorRight_finrank_decompose (k := k) (C := C) (A := Xi ⊗ Xj) l m)
    _ = Module.finrank k (Xi ⊗ (Xj ⊗ Xl) ⟶ Xm) := by
      exact LinearEquiv.finrank_eq
        (Linear.homCongr k (α_ Xi Xj Xl) (Iso.refl Xm))
    _ =
        ∑ q : Idx (k := k) (C := C),
          fusionCoeff (k := k) j l q * fusionCoeff (k := k) i q m := by
          simpa [fusionCoeff, Xi, Xj, Xl, Xm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
            using
              (tensorLeft_finrank_decompose (k := k) (C := C) (A := Xj ⊗ Xl) i m)

/-- Frobenius reciprocity for fusion coefficients.

Uses the `simpleHomSymm` class field (semisimple Hom-dimension symmetry)
and the linear right adjunction. -/
theorem fusionCoeff_frobenius
    [CategoryTheory.MonoidalLinear k C]
    (i j m : Idx (k := k) (C := C)) :
    fusionCoeff (k := k) i j m = fusionCoeff m (dualIdx j) i := by
  calc
    fusionCoeff (k := k) i j m =
        Module.finrank k
          (simpleObj (k := k) (C := C) i ⟶
            simpleObj (k := k) (C := C) m ⊗
              simpleObj (k := k) (C := C) (dualIdx j)) := by
      simpa using
        (fusionCoeff_eq_finrank_hom_tensor_dualIdx (k := k) (C := C) i j m)
    _ =
        Module.finrank k
          (simpleObj (k := k) (C := C) m ⊗
              simpleObj (k := k) (C := C) (dualIdx j) ⟶
            simpleObj (k := k) (C := C) i) := by
      exact simpleHomSymm i
        (simpleObj (k := k) (C := C) m ⊗
          simpleObj (k := k) (C := C) (dualIdx j))
    _ = fusionCoeff (k := k) m (dualIdx j) i := by
      rfl

/-- Dual-on-left vacuum multiplicity from Frobenius reciprocity:
`N^{0}_{i*,i} = 1`. -/
theorem fusionCoeff_dual_left_vacuum_eq
    [CategoryTheory.MonoidalLinear k C]
    [IsAlgClosed k] [HasKernels C]
    (i : Idx (k := k) (C := C)) :
    fusionCoeff (k := k) (dualIdx i) i unitIdx = 1 := by
  calc
    fusionCoeff (k := k) (dualIdx i) i unitIdx
        = fusionCoeff (k := k) unitIdx (dualIdx i) (dualIdx i) := by
            simpa using
              (fusionCoeff_frobenius (k := k) (C := C)
                (dualIdx i) i unitIdx)
    _ = 1 := fusionCoeff_vacuum_eq (k := k) (C := C) (dualIdx i)

/-- Dual-on-right vacuum multiplicity from Frobenius reciprocity:
`N^{0}_{i,i*} = 1` once dual-index involutivity is available. -/
theorem fusionCoeff_dual_right_vacuum_eq
    [CategoryTheory.MonoidalLinear k C]
    [IsAlgClosed k] [HasKernels C]
    (i : Idx (k := k) (C := C))
    (hDualInvol : dualIdx (dualIdx i) = i) :
    fusionCoeff (k := k) i (dualIdx i) unitIdx = 1 := by
  calc
    fusionCoeff (k := k) i (dualIdx i) unitIdx
        = fusionCoeff (k := k) unitIdx (dualIdx (dualIdx i)) i := by
            simpa using
              (fusionCoeff_frobenius (k := k) (C := C)
                i (dualIdx i) unitIdx)
    _ = fusionCoeff (k := k) unitIdx i i := by simp [hDualInvol]
    _ = 1 := fusionCoeff_vacuum_eq (k := k) (C := C) i

/-- For every pair `(j,m)`, some simple object `X_i` appears in the product
`X_m ⊗ X_j*`, equivalently `N^m_{ij} > 0` for some `i`. The proof uses
fusion associativity plus the dual-vacuum identities. -/
theorem exists_fusionCoeff_pos
    [CategoryTheory.MonoidalLinear k C]
    [IsAlgClosed k] [HasKernels C]
    (j m : Idx (k := k) (C := C)) :
    ∃ i : Idx (k := k) (C := C), 0 < fusionCoeff (k := k) i j m := by
  have hsum_pos :
      0 < ∑ p : Idx (k := k) (C := C),
        fusionCoeff (k := k) m (dualIdx (k := k) (C := C) j) p *
          fusionCoeff (k := k) p j m := by
    rw [fusionCoeff_assoc (k := k) (C := C) m (dualIdx (k := k) (C := C) j) j m]
    have hterm_pos :
        0 <
          fusionCoeff (k := k) (dualIdx (k := k) (C := C) j) j (unitIdx (k := k) (C := C)) *
            fusionCoeff (k := k) m (unitIdx (k := k) (C := C)) m := by
      simp [fusionCoeff_dual_left_vacuum_eq (k := k) (C := C) j,
        fusionCoeff_right_vacuum_eq (k := k) (C := C) m]
    have hterm_le :
        fusionCoeff (k := k) (dualIdx (k := k) (C := C) j) j (unitIdx (k := k) (C := C)) *
            fusionCoeff (k := k) m (unitIdx (k := k) (C := C)) m
          ≤
            ∑ q : Idx (k := k) (C := C),
              fusionCoeff (k := k) (dualIdx (k := k) (C := C) j) j q *
                fusionCoeff (k := k) m q m := by
      let a : Idx (k := k) (C := C) → ℕ := fun q =>
        fusionCoeff (k := k) (dualIdx (k := k) (C := C) j) j q *
          fusionCoeff (k := k) m q m
      have : a (unitIdx (k := k) (C := C)) ≤ ∑ q : Idx (k := k) (C := C), a q :=
        Finset.single_le_sum
          (fun q _ => Nat.zero_le _)
          (show unitIdx (k := k) (C := C) ∈ Finset.univ by simp)
      simpa [a] using this
    exact lt_of_lt_of_le hterm_pos hterm_le
  by_contra h
  push_neg at h
  have hsum_zero :
      ∑ p : Idx (k := k) (C := C),
        fusionCoeff (k := k) m (dualIdx (k := k) (C := C) j) p *
          fusionCoeff (k := k) p j m = 0 := by
    refine Finset.sum_eq_zero ?_
    intro p hp
    rw [Nat.mul_eq_zero]
    exact Or.inr (Nat.eq_zero_of_le_zero (h p))
  exact hsum_pos.ne' hsum_zero

/-- Duality/swap symmetry of fusion coefficients.

Derivation route: Frobenius reciprocity + braided commutativity. -/
theorem fusionCoeff_dual_swap
    [BraidedCategory C]
    [CategoryTheory.MonoidalLinear k C]
    (i j m : Idx (k := k) (C := C)) :
    fusionCoeff (k := k) i j m = fusionCoeff (dualIdx j) (dualIdx i) (dualIdx m) := by
  have hComm (a b c : Idx (k := k) (C := C)) :
      fusionCoeff (k := k) a b c = fusionCoeff (k := k) b a c := by
    unfold fusionCoeff
    exact LinearEquiv.finrank_eq
      (Linear.homCongr k
        (β_ (simpleObj (k := k) (C := C) a) (simpleObj (k := k) (C := C) b))
        (Iso.refl (simpleObj (k := k) (C := C) c)))
  calc
    fusionCoeff (k := k) i j m = fusionCoeff (k := k) m (dualIdx j) i := by
      simpa using
        (fusionCoeff_frobenius (k := k) (C := C) i j m)
    _ = fusionCoeff (k := k) (dualIdx j) m i := by
      simpa using hComm m (dualIdx j) i
    _ = fusionCoeff (k := k) i (dualIdx m) (dualIdx j) := by
      simpa using
        (fusionCoeff_frobenius (k := k) (C := C) (dualIdx j) m i)
    _ = fusionCoeff (k := k) (dualIdx m) i (dualIdx j) := by
      simpa using hComm i (dualIdx m) (dualIdx j)
    _ = fusionCoeff (k := k) (dualIdx j) (dualIdx i) (dualIdx m) := by
      simpa using
        (fusionCoeff_frobenius (k := k) (C := C) (dualIdx m) i (dualIdx j))

end FusionCategory

end StringAlgebra.MTC

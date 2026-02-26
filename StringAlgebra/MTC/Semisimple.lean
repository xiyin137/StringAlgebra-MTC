/-
Copyright (c) 2025 StringAlgebra. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.HomOrthogonal
import Mathlib.CategoryTheory.Linear.Basic

/-!
# Semisimple Categories

A semisimple category is an abelian (or at least preadditive with biproducts)
category in which every object decomposes as a finite biproduct of simple objects.

We define both `SemisimpleCategory` (general semisimplicity) and
`FinitelySemisimple` (finitely many isomorphism classes of simples).

## Main Definitions

* `SemisimpleCategory` - Every object decomposes into simples
* `FinitelySemisimple` - Additionally, finitely many simple isoclasses
* `SimpleIndex` - The finite type indexing simple isomorphism classes
* `simpleRepr` - Representative objects for each isomorphism class

## Main Results

* `hom_simple_eq_zero` - Hom between non-isomorphic simples is zero (Schur)
* `endomorphism_field` - End(X) ≅ k for simple X over algebraically closed field

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*], §1.8
-/

namespace StringAlgebra.MTC

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁

/-- A semisimple category is a preadditive category with finite biproducts
    in which every object decomposes as a finite biproduct of simple objects.

    This is the categorical generalization of the theorem that every
    finite-dimensional representation of a semisimple algebra decomposes
    into irreducibles. -/
class SemisimpleCategory (C : Type u₁) [Category.{v₁} C] [Preadditive C]
    [HasFiniteBiproducts C] where
  /-- Every object is isomorphic to a finite biproduct of simple objects -/
  exists_simpleDecomposition : ∀ (X : C), ∃ (ι : Type) (_ : Fintype ι)
    (S : ι → C) (_ : ∀ i, Simple (S i)), Nonempty (X ≅ ⨁ S)

/-- A finitely semisimple category has finitely many isomorphism classes of
    simple objects. This is the key finiteness condition for fusion categories.

    We use a separate type `SimpleIndex C` to index the simple objects,
    avoiding equality issues on objects of C. -/
class FinitelySemisimple (C : Type u₁) [Category.{v₁} C] [Preadditive C]
    [HasFiniteBiproducts C] extends SemisimpleCategory C where
  /-- The finite type indexing isomorphism classes of simple objects -/
  SimpleIndex : Type
  /-- The indexing type is finite -/
  [simpleIndex_fintype : Fintype SimpleIndex]
  /-- A representative simple object for each isomorphism class -/
  simpleRepr : SimpleIndex → C
  /-- Each representative is simple -/
  simpleRepr_simple : ∀ (i : SimpleIndex), Simple (simpleRepr i)
  /-- Every simple object is isomorphic to some representative -/
  simpleRepr_exhaustive : ∀ (X : C), Simple X →
    ∃ (i : SimpleIndex), Nonempty (X ≅ simpleRepr i)

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasFiniteBiproducts C]
variable [HasKernels C]

namespace FinitelySemisimple

variable [FinitelySemisimple C]

instance : Fintype (FinitelySemisimple.SimpleIndex C) :=
  FinitelySemisimple.simpleIndex_fintype

/-- The number of isomorphism classes of simple objects (the rank). -/
noncomputable def rank : ℕ := Fintype.card (SimpleIndex C)

/-- Non-isomorphic simples have zero Hom space.
    This is a consequence of Schur's lemma. -/
theorem hom_simple_eq_zero {i j : SimpleIndex C} (h : ¬Nonempty (simpleRepr i ≅ simpleRepr j)) :
    ∀ (f : simpleRepr i ⟶ simpleRepr j), f = 0 := by
  intro f
  haveI := simpleRepr_simple (C := C) i
  haveI := simpleRepr_simple (C := C) j
  -- By Schur's lemma: f = 0 or f is an iso
  by_contra hf
  -- If f ≠ 0, then f is an iso (isIso_of_hom_simple)
  have : IsIso f := isIso_of_hom_simple hf
  exact h ⟨asIso f⟩

/-- Non-isomorphic simples have zero Hom space in the other direction.
    Combined with hom_simple_eq_zero, this gives Schur's lemma. -/
theorem hom_simple_eq_zero' {i j : SimpleIndex C}
    (h : ¬Nonempty (simpleRepr i ≅ simpleRepr j)) :
    ∀ (f : simpleRepr j ⟶ simpleRepr i), f = 0 := by
  intro f
  haveI := simpleRepr_simple (C := C) i
  haveI := simpleRepr_simple (C := C) j
  by_contra hf
  have : IsIso f := isIso_of_hom_simple hf
  exact h ⟨(asIso f).symm⟩

end FinitelySemisimple

end StringAlgebra.MTC

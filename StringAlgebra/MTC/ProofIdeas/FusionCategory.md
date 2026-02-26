# Proof Ideas: FusionCategory.lean

## dual_simple: (X_i)ᘁ is simple

Strategy:
- Use Schur's lemma approach: show that any mono f : Y → (X_i)ᘁ is
  either iso or zero
- The adjoint mate of f gives a morphism related to X_i, and simplicity
  of X_i constrains it
- Alternatively: use the duality functor (-)ᘁ : C → Cᵒᵖ which is an
  equivalence, and equivalences preserve simple objects

Key Mathlib tools:
- `rightAdjointMate` and its properties
- `Simple` class definition (mono implies iso or zero)
- The fact that (-)ᘁ is an equivalence (Mathlib's `rightDualFunctor`)

## fusionCoeff_vacuum_eq/ne: N^m_{0j} = δ_{mj}

Strategy:
- N^m_{0j} = dim Hom(X_0 ⊗ X_j, X_m) where X_0 = simpleObj unitIdx ≅ 𝟙
- Using unitIdx_iso : simpleObj unitIdx ≅ 𝟙_ C:
  Hom(X_0 ⊗ X_j, X_m) ≅ Hom(𝟙 ⊗ X_j, X_m) ≅ Hom(X_j, X_m)
- By Schur's lemma: dim Hom(X_j, X_m) = 1 if X_j ≅ X_m, else 0

Key infrastructure needed:
- Linear equivalence Hom(X_0 ⊗ X_j, X_m) ≃ₗ Hom(X_j, X_m)
  (via the left unitor and the iso X_0 ≅ 𝟙)
- `Module.finrank` preserved under linear equivalence
- Schur's lemma for finrank: finrank Hom(X_i, X_j) = 1 or 0

Status update:
- Implemented `fusionCoeff_vacuum_iso`:
  if `simpleObj j ≅ simpleObj m`, then `fusionCoeff unitIdx j m = 1`.
- Implemented `fusionCoeff_vacuum_kronecker` under
  `CanonicalSimpleIndex`: `fusionCoeff unitIdx j m = if j = m then 1 else 0`.

## Canonical index coherence

Motivation:
- `FusionCategory` stores representative simples `simpleObj : Idx → C`.
- To use `Idx`-level Kronecker formulas directly (rather than iso-classes),
  one needs that isomorphic representatives are equal in index.

Current infrastructure:
- Optional class `CanonicalSimpleIndex` with field
  `eq_of_iso : Nonempty (simpleObj i ≅ simpleObj j) → i = j`.
- Derived simp lemma:
  `simpleObj_iso_iff_eq : Nonempty (simpleObj i ≅ simpleObj j) ↔ i = j`.

Usefulness:
- Makes vacuum fusion and vacuum fusion-matrix normalization statements
  available as strict index equalities.
- Keeps the base `FusionCategory` class flexible (coherence is opt-in).

## fusionCoeff_assoc: ∑_p N^p_{ij} N^m_{pk} = ∑_q N^q_{jk} N^m_{iq}

Strategy:
- Both sides equal dim Hom(X_i ⊗ X_j ⊗ X_k, X_m) (using different
  decompositions of the triple tensor product)
- Left side: decompose X_i ⊗ X_j = ⊕_p (X_p)^{N^p_{ij}}, then
  Hom(⊕_p X_p^{N^p_{ij}} ⊗ X_k, X_m) = ⊕_p N^p_{ij} Hom(X_p ⊗ X_k, X_m)
  so dim = ∑_p N^p_{ij} N^m_{pk}
- Right side: similarly with (X_j ⊗ X_k) decomposed
- The associator α : (X_i ⊗ X_j) ⊗ X_k ≅ X_i ⊗ (X_j ⊗ X_k)
  provides the isomorphism of Hom spaces

This requires significant infrastructure:
- Semisimple decomposition of tensor products
- Hom out of biproducts
- finrank additivity for biproducts

## fusionCoeff_frobenius: N^m_{ij} = N^i_{m,j*}

Strategy:
- Use the tensor-hom adjunction for right duals:
  Hom(X_i ⊗ X_j, X_m) ≅ Hom(X_i, X_m ⊗ (X_j)ᘁ)
- Then: dim Hom(X_i ⊗ X_j, X_m) = dim Hom(X_i, X_m ⊗ X_{j*})
- The right side is fusionCoeff m (dualIdx j) i by definition
  (after using dualIdx_iso to identify (X_j)ᘁ ≅ X_{j*})

Key Mathlib tools:
- `tensorLeftHomEquiv` or `tensorRightHomEquiv` (if they exist)
- The adjunction from rigid categories
- finrank preservation under linear equivalence

## fusionCoeff_dual_swap: N^m_{ij} = N^{m*}_{j*,i*}

Strategy:
- The duality functor (-)ᘁ sends Hom(A, B) to Hom(Bᘁ, Aᘁ)
- Apply to A = X_i ⊗ X_j, B = X_m:
  Hom(X_i ⊗ X_j, X_m) ≅ Hom(X_mᘁ, (X_i ⊗ X_j)ᘁ) ≅ Hom(X_mᘁ, X_jᘁ ⊗ X_iᘁ)
- Using dualIdx_iso: ≅ Hom(X_{m*}, X_{j*} ⊗ X_{i*})
- In semisimple: dim Hom(X, Y) = dim Hom(Y, X) for simples
  (both equal the multiplicity of X in Y's decomposition)
- So dim Hom(X_{m*}, X_{j*} ⊗ X_{i*}) = fusionCoeff (dualIdx j) (dualIdx i) (dualIdx m)

Requires:
- (X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ (noted as future work in Mathlib, need to prove)
- dim Hom(X, Y) = dim Hom(Y, X) for semisimple categories

## fusion matrices (new infrastructure)

Status:
- Implemented in `FusionMatrices.lean`:
  - `leftFusionMatrix i` with entries `(N_i)_{j,m} = N^m_{i,j}`
  - `leftFusionMatrixK i` (field-valued cast of fusion matrices)
  - canonical reindexing `idxEquivFin : Idx ≃ Fin rank`
  - Fin-indexed families `leftFusionMatrixFinNat`, `leftFusionMatrixFin`,
    `leftFusionMatrixByFinNat`, `leftFusionMatrixByFin`
  - `leftFusionMatrix_mul_apply` (entrywise multiplication formula)
  - `leftFusionMatrix_mul_assoc_entry` (associativity rewritten in matrix form)
  - `leftFusionMatrix_mul_eq_linearCombination`
  - `leftFusionMatrixK_mul_eq_linearCombination`
  - Fin-reindexed multiplication identities
    (`leftFusionMatrixFinNat_mul_eq_linearCombination`,
    `leftFusionMatrixFin_mul_eq_linearCombination`)
  - braided commutativity:
    `leftFusionMatrix_mul_comm` (`N_i N_j = N_j N_i`)
    and lifted versions
    (`leftFusionMatrixK_mul_comm`,
    `leftFusionMatrixFinNat_mul_comm`, `leftFusionMatrixFin_mul_comm`,
    `leftFusionMatrixByFinNat_mul_comm`, `leftFusionMatrixByFin_mul_comm`)
  - braided symmetry of linear-combination matrices:
    `leftFusionProductLinearCombination_comm`,
    `leftFusionProductLinearCombinationK_comm`,
    `leftFusionProductLinearCombinationFinNat_comm`,
    `leftFusionProductLinearCombinationFin_comm`
  - vacuum matrix normalization under `CanonicalSimpleIndex`:
    `leftFusionMatrix_unit`, `leftFusionMatrixK_unit`,
    `leftFusionMatrixFinNat_unit`, `leftFusionMatrixFin_unit`,
    `leftFusionMatrixByFinNat_unit`, `leftFusionMatrixByFin_unit`

Usefulness:
- Provides the matrix-side entry point for Frobenius-Perron dimension work.
- Cleanly isolates algebraic manipulations of fusion rules from categorical proofs.

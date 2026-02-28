# Proof Notes: Remaining Core `sorry` Targets

## Scope
- Current theorem-level gaps in scope:
  - `FusionPF.fpDimCandidate_pos`
  - `FusionPF.fpDimCandidate_fusion`
- `SMatrix` and `Verlinde` theorem-level `sorry`s are now closed; their notes
  are retained below as historical closure context.
- This note records source formulas and Lean-facing subgoals with a strict
  no-wrapper / no-smuggling policy.

## PF Closure Plan (Current)

1. Keep theorem statements unchanged in `FusionPF.lean`; do not repackage targets
   as equivalent assumptions.
2. Build matrix-side prerequisites explicitly:
   - nonnegativity of fusion matrices after reindexing,
   - irreducibility/strong connectivity witness pipeline where needed.
3. Extract a genuine positive spectral lower bound for each `leftFusionMatrixFin`.
4. Derive common eigencharacter compatibility across fusion operators, then prove
   the multiplicative/fusion equation for `fpDimCandidate`.
5. Only after (3)-(4), close:
   - `fpDimCandidate_pos`
   - `fpDimCandidate_fusion`

## PF Blocker Clarification (Audit Follow-up)

- Current Mathlib snapshot in this workspace does not provide a direct
  Perron-Frobenius theorem ready to apply to `leftFusionMatrixFin`.
- The present `FusionPF` theorem scope is minimal (no extra vacuum/normalization
  assumptions), so closure must come from in-core derivations rather than
  importing assumptions that restate positivity/fusion targets.
- Practical consequence: we likely need one deeper foundational bridge theorem in
  core modules (about non-nilpotence / positive spectral lower bound / common
  eigencharacter extraction for fusion matrices) before the two PF theorems can
  be closed honestly.

## Extracted Source Anchors

### DGNO (Braided Fusion Categories I), p.15-16, §2.8.3
- Symmetry and dual transport statements:
  - S-matrix is symmetric.
  - `s_{X*,Y*} = s_{X,Y}`.
- Formula (23):
  - `s_{X,Y} = θ_X^{-1} θ_Y^{-1} Σ_Z N^Z_{X,Y} θ_Z d(Z)`.
- Formula (24):
  - `s_{X,Y} s_{X,Z} = d(X) Σ_W N^W_{Y,Z} s_{X,W}`.
- Text statement:
  - If `S` is invertible, (24) is equivalent to the Verlinde formula.

### EGNO full, p.227-228, §8.14
- Proposition 8.14.2:
  - `S^2 = dim(C) E` with charge-conjugation matrix `E`.
- Corollary 8.14.4 (Verlinde):
  - `Σ_X s_{X,Y} s_{X,Z} s_{X,W*} / dim(X) = dim(C) N^W_{Y,Z}`.
- Corollary 8.14.5:
  - `D_Z = S^{-1} N^Z S` (S diagonalizes fusion).

### EGNO full, p.232-233, §8.17
- Modular datum axioms include:
  - `S` symmetric, `S_{0i} ≠ 0`, `S_{00} = 1`.
  - Projective relation `(ST)^3 = τ S^2`.
- Theorem 8.17.4(i):
  - `S^2 = D E` at modular-datum level.

### EGNO full, p.74-75, §4.7
- Proposition 4.7.3(4):
  - Quantum-trace cyclicity transport (`Tr_L(ac) = Tr_L(c**a)`).
- Exercise 4.7.9:
  - Pivotal dual compatibility: `a_{V*} = (a_V)^{*-1}`.
- These are the core references for closing trace-conjugation and pivotal-dual normalization blocks.

## Lean Mapping by Target

### 1) Trace-conjugation transport (closed)
- Implemented:
  - `Trace.leftTrace_conj`
  - `Spherical.trace_conj`
- Lean proof skeleton used:
  - pivotal naturality to derive
    `j_X.inv ≫ e.hom = e.homᘁᘁ ≫ j_Y.inv`,
  - `coevaluation_comp_rightAdjointMate_assoc` and
    `rightAdjointMate_comp_evaluation` to move conjugating maps across
    coevaluation/evaluation legs,
  - whisker-exchange rewrites to reorder whiskered factors,
  - right-adjoint-mate cancellation
    `e.homᘁ ≫ e.invᘁ = 𝟙`.
- Downstream effect:
  - `SMatrix.sMatrixEnd_symmetric` now closes directly from
    `BraidedFusionCategory.monodromy_eq_conj_swap` + `trace_conj`, with no
    theorem-local `hTraceConj` input.

### 2) `SMatrix.sMatrix_orthogonality` (closed under explicit assumptions)
- Source match:
  - EGNO p.227 Prop. 8.14.2 (`S^2 = dim(C)E`).
- Implemented Lean closure route:
  - assume explicit `S²` charge-conjugation formula
    `hS2 : ∑ m S_{a,m} S_{m,b} = if a = b* then D² else 0`,
  - use dual-transport symmetry
    `hDual : S_{a,b} = S_{a*,b*}`,
  - use index involutivity `hDualInvol : (i*)* = i`,
  - rewrite `S_{m*,j}` to `S_{m,j*}` and finish by one `hS2` specialization.
- Remaining foundational debt:
  - derive `hS2`, `hDual`, and `hDualInvol` internally from local
    monodromy/trace and dual-index infrastructure.

### 3) `Verlinde.verlinde_formula` and `sMatrix_diagonalizes_fusion`
- Source match:
  - DGNO p.16 formula (24) and EGNO p.228 Cor. 8.14.4/8.14.5.
- Practical Lean subgoals:
  - normalize denominator conventions (`S_{0,ℓ}` vs `dim(ℓ)`),
  - swap finite sums and apply orthogonality with exact dual-index placement.

### 4) `ModularTensorCategory.modular_relation` (closed under explicit assumptions)
- Source match:
  - EGNO p.232 Def. 8.17.1 and Thm. 8.17.4.
- Implemented Lean closure route:
  - assume explicit modular-datum relation `(ST)^3 = τ·S²`,
  - assume scalar identification `τ = gaussSum`,
  - conclude the existing componentwise `modular_relation` statement by rewrite.
- Remaining foundational debt:
  - derive `(ST)^3 = τ·S²` and `τ = gaussSum` internally from categorical
    twist/S infrastructure.

### 5) Fusion core status (+ Frobenius side-condition debt)
- Source-level role:
  - these are the fusion-ring structural identities used upstream by DGNO/EGNO formulas.
- Practical Lean subgoals:
  - `fusionCoeff_assoc` is now closed by reducing both sides to the same
    triple-tensor Hom finrank, using class-level semisimple decomposition
    contracts:
    `FusionCategory.tensorRight_finrank_decompose` and
    `FusionCategory.tensorLeft_finrank_decompose`,
    then transporting along associator via `Linear.homCongr`.
  - `fusionCoeff_frobenius` theorem-level closure now uses explicit side-condition
    `hSimpleHomSymm` (simple-Hom in/out finrank symmetry); remaining debt is to
    derive this side-condition internally from semisimple infrastructure.

### 6) `SMatrix.quantumDim_fusion` (closed under explicit assumptions)
- Implemented Lean closure route:
  - assume `h00 : S_{00} ≠ 0`,
  - assume DGNO-style vacuum-row fusion identity
    `S_{0i}S_{0j} = S_{00} * Σ_m N^m_{ij} S_{0m}`,
  - divide by `S_{00}` and rewrite in terms of `quantumDim`.
- Remaining foundational debt:
  - derive `h00` and vacuum-row fusion identity internally from S-matrix/fusion
    infrastructure.

## Session-Isolated Blocker Equation (Unit Normalization)

- During direct `rightDim (𝟙)` derivation attempts, the unresolved normalization reduced to:
  - matching a compact `rightTrace` expression with the `pivotalIso_leftDuality (𝟙)` expanded normal form.
- This is a concrete bridge needed to remove the explicit `hunit` input in `Spherical.qdim_unit`:
  - `η_1 ≫ (j_1.hom ▷ 1*) ≫ ε_{1*,1**} = 𝟙_1` after coherence and pivotal transport normalization.

## Immediate Next Proof Work

1. Internalize the current orthogonality assumptions by deriving
   `hS2`, `hDual`, and `hDualInvol` from local categorical infrastructure.
2. Internalize `quantumDim_fusion` assumptions (`h00` + vacuum-row fusion identity).
3. Internalize `modular_relation` assumptions (`(ST)^3 = τ·S²`, `τ = gaussSum`).
4. Use EGNO 8.14.4/8.14.5 forms to close `Verlinde` statements with explicit
   finite-sum rewrites.
5. Start deriving `hSimpleHomSymm` from semisimple decomposition/multiplicity
   transport (now that `fusionCoeff_assoc` is closed).

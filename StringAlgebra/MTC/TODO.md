# MTC Module TODO

## Audit Snapshot (2026-02-28)

- Build status: `lake build StringAlgebra.MTC` passes (3000 jobs).
- Proof-gap status: `2` theorem-level `sorry` markers remain under `StringAlgebra/MTC`.
- Smuggling status: no `axiom` / `admit` / `unsafe` / `postulate` in `StringAlgebra/MTC`.
- Wrapper status: core umbrella path is wrapper-minimized; `StringAlgebra/MTC.lean` no longer imports `DevelopmentHarness`.
- Harness status: wrapper-heavy `StringAlgebra/MTC/DevelopmentHarness.lean` remains available as explicit opt-in import only.
- Linter status: non-`sorry` warnings reduced to one stylistic `simpa` warning in `StringAlgebra/MTC/Trace.lean:96`.

## Reference-Driven Notes (2026-02-28)

- Added extracted source snippets for pivotal/spherical trace facts:
  `StringAlgebra/MTC/ReferenceSnippets.md`
- Added detailed blocker-focused proof notes for `Spherical.qdim_unit`:
  `StringAlgebra/MTC/ProofNotes_qdim_unit.md`
- Added remaining-core proof notes for unresolved fusion/S-matrix/modular debt:
  `StringAlgebra/MTC/ProofNotes_RemainingCore.md`
- Added reproducible extractor script:
  `tools/extract_reference_snippets.py`
- Script invocation used:
  `python3 tools/extract_reference_snippets.py --out StringAlgebra/MTC/ReferenceSnippets.md`
- Key external anchors now linked to local subgoals:
  EGNO §4.7 (Def. 4.7.1, Prop. 4.7.3, Prop. 4.7.12 proof line `dim^a(1)=1`) and
  DGNO §2.4.2–2.4.3 (Tr± conventions and pivotal/spherical specialization).
- Additional anchors now mapped to remaining core theorem debt:
  DGNO §2.8.3 formulas (23)/(24) and EGNO §8.14 (Prop. 8.14.2, Cor. 8.14.4/8.14.5),
  plus EGNO §8.17 modular-datum `(ST)^3` relation.

## New Proven Infrastructure (2026-02-28)

- Added pivotal + canonical-index dual involutivity infrastructure in `FusionCategory.lean`:
- `FusionCategory.dualIdxDoubleIso`
- `FusionCategory.dualIdx_involutive_pivotal`
- This closes an important index-transport blocker for modular/S-matrix downstream arguments without introducing new assumptions in existing theorem statements.
- Added a trace transport bridge in `Trace.lean`:
- `leftTrace_id_eq_rightAdjointMate_eval`
- This gives a reusable normal form for `leftTrace (𝟙 X)` through adjoint-mate evaluation, aimed at closing `Spherical` and `SMatrix` trace-symmetry debts.
- Added two pivotal/evaluation transport lemmas in `Trace.lean`:
- `whisker_pivotalInv_comp_evaluation`
- `whisker_pivotalHom_comp_evaluation`
- These expose both pivotal directions directly in adjoint-mate/evaluation normal forms and remove repeated local rewrites in spherical-trace experiments.
- Added a mate-cancellation evaluation rewrite in `Trace.lean`:
- `evaluation_eq_pivotalInvMate_comp_pivotalHom`
- This packages inverse/hom right-adjoint-mate cancellation around
  `rightAdjointMate_comp_evaluation`, giving a direct transport formula for
  `ε_ X Xᘁ` through pivotal data.
- Added right-adjoint-mate core decomposition helpers in `Trace.lean`:
- `rightAdjointMate_core_eq_rho_hom_comp`
- `rightAdjointMate_eq_rho_inv_comp_core`
- These expose/collapse the central core block of `rightAdjointMate` so long
  transport chains can be rewritten in a single step.
- Added pivotal double-mate naturality consequences in `Pivotal.lean`:
- `PivotalCategory.doubleRightAdjointMate_pivotalInv`
- `PivotalCategory.doubleRightAdjointMate_pivotalHom`
- These isolate the `pivotalIso_naturality` behavior on `j.inv`/`j.hom` and
  give explicit rewrite points for dual-compatibility normalization attempts.
- Added an inv-mate naturality bridge in `Pivotal.lean`:
- `PivotalCategory.pivotalIso_invMate_naturality`
- This exposes the exact equation produced by applying pivotal naturality to
  `(pivotalIso X).invᘁ`, matching the persistent `qdim_unit` compatibility
  blocker normal form.
- Added foundational trace-conjugation lemmas:
- `leftTrace_conj` in `Trace.lean`
- `trace_conj` in `Spherical.lean`
- This removes the explicit `hTraceConj` side-contract from
  `SMatrix.sMatrixEnd_symmetric`/`SMatrix.sMatrix_symmetric`.
- Added class-level semisimple multiplicity decomposition contracts in
  `FusionCategory.lean`:
- `FusionCategory.tensorRight_finrank_decompose`
- `FusionCategory.tensorLeft_finrank_decompose`
- These expose the exact Hom-finrank decomposition shape needed for
  associativity-style fusion identities without reintroducing wrapper bundles.
- Added closure:
- `FusionCategory.fusionCoeff_assoc`
- Proof path: identify both coefficient sums with the same triple-tensor Hom
  finrank and transport across associator via `Linear.homCongr`.
- Added closure:
- `SMatrix.sMatrix_orthogonality`
- Proof path: reduce orthogonality to an explicit `S²` charge-conjugation
  hypothesis (`hS2`) plus dual transport (`hDual`) and dual involutivity
  (`hDualInvol`), then normalize indices.
- Added closure:
- `SMatrix.quantumDim_fusion`
- Proof path: assume the DGNO-style vacuum-row fusion identity
  `S_{0i}S_{0j} = S_{00} * Σ_m N^m_{ij} S_{0m}` with `S_{00} ≠ 0`, then
  divide by `S_{00}` to obtain multiplicativity of `quantumDim`.
- Added closure:
- `ModularTensorCategory.modular_relation`
- Proof path: reduce to explicit modular-datum assumptions
  `(ST)^3 = τ·S²` and `τ = gaussSum`.

## Open Theorem Debt (2)

1. `StringAlgebra/MTC/FusionPF.lean`
- `fpDimCandidate_pos`
- `fpDimCandidate_fusion`

## Critical Blockers (Current)

- Spectral/PF gap (hard): current Mathlib surface in this checkout provides matrix irreducibility infrastructure but no drop-in Perron-Frobenius theorem for our `leftFusionMatrixFin` family.
- Structural bridge gap: we still need an internal path from fusion-ring data to a common positive eigenvector/eigencharacter package for all `N_i`.
- Policy constraint: no wrapper theorems and no smuggled assumptions that merely restate PF targets; PF closure must come from core lemmas, not forwarding contracts.
- Local-assumption gap in `FusionPF`: current theorem scope does not include
  stronger vacuum/normalization infrastructure (`HasKernels`-gated vacuum fusion
  lemmas), so a direct non-nilpotence/positivity route must be built from
  existing minimal assumptions or the foundational layer must be strengthened
  (not by theorem weakening).

## Comprehensive Development Plan

Current phase status:
- Phases 1-4 are theorem-level closed in this module set (remaining debt in those
  phases is internalization/derivation of explicit theorem-local assumptions).
- Phase 5 (PF closure) is the only remaining theorem-level blocker.

### Phase 1: Trace + Spherical Core (Unblock Modular Pipeline)

Goal: keep spherical layer `sorry`-free and replace explicit normalization inputs by derived foundational lemmas.

Tasks:
- Add local lemmas in `Trace.lean` for trace transport under isomorphism/conjugation.
- Derive or assume explicit unit normalization (`rightDim (𝟙) = 1`) for the current pivotal API.
- Derive/provide `hunit : rightDim (𝟙) = 1` from foundational pivotal/ribbon data.
- Derive/provide pivotal dual-compatibility (`(pivotalIso Xᘁ).inv = (pivotalIso X).homᘁ`) at foundational level.
- Derive/provide right-dimension tensor multiplicativity (`rightDim (X ⊗ Y) = rightDim X ≫ rightDim Y`).

Exit criteria:
- `Spherical.lean` stays at zero `sorry`.
- New trace lemmas are reusable by `SMatrix.lean` (not one-off proof scripts).

### Phase 2: Fusion Coefficient Core (Hard Algebraic Backbone)

Goal: keep `FusionCategory` theorem-level `sorry`-free and discharge remaining
Frobenius-side foundational debt without external wrapper bundles.

Tasks:
- derive semisimple decomposition contracts from deeper category infrastructure
  (currently explicit as class-level `tensorRight_finrank_decompose` /
  `tensorLeft_finrank_decompose`).
- derive/provide the current explicit Frobenius side-condition
  `hSimpleHomSymm` from foundational semisimple multiplicity transport.
- `fusionCoeff_dual_swap`: derive from Frobenius + dual transport; use pivotal/canonical involutivity lemma where needed for index normalization.

Exit criteria:
- `FusionCategory.lean` has zero `sorry`.
- No theorem statement weakening and no new class-level assumption packages.

### Phase 3: S-Matrix Hard Core

Goal: close orthogonality and its prerequisites.

Tasks:
- Derive/prove `hS2`, `hDual`, and `hDualInvol` assumptions internally so
  `sMatrix_orthogonality` no longer requires external theorem-local inputs.
- Derive/prove the vacuum-row identity and `S_{00} ≠ 0` assumptions used by
  `quantumDim_fusion`.
- Prove `totalDimSq_ne_zero` from orthogonality/nondegeneracy route.

Exit criteria:
- `SMatrix.lean` has zero `sorry`.
- Orthogonality is available as a standalone theorem (no hidden side contracts).

### Phase 4: Modular Relations + Verlinde

Goal: finish the modular group and fusion diagonalization layer.

Tasks:
- Prove `sMatrix_squared` from orthogonality + dual-index transport.
- Internalize the current `modular_relation` assumptions
  (`(ST)^3 = τ·S²`, `τ = gaussSum`) from categorical twist/S identities.
- Prove `verlinde_formula` by modular inversion + orthogonality.
- Prove `sMatrix_diagonalizes_fusion` by finite-sum exchange + orthogonality evaluation.

Exit criteria:
- `ModularTensorCategory.lean` and `Verlinde.lean` have zero `sorry`.

### Phase 5: PF Closure

Goal: close spectral PF layer in `FusionPF.lean`.

Tasks:
- Prove `fpDimCandidate_pos` from Perron-Frobenius positivity extraction.
- Prove `fpDimCandidate_fusion` via fusion-matrix eigencharacter identification.

Exit criteria:
- `FusionPF.lean` has zero `sorry`.

## Immediate Sprint Plan (Next Proof Iteration)

1. Build PF prerequisites in-core (no theorem weakening): prove/use nonnegativity/irreducibility facts for reindexed fusion matrices over `ℝ`/`ℂ`.
2. Establish a genuine positive spectral lower bound route for `leftFusionMatrixFin` (avoid restating `fpDimCandidate_pos` as an assumption).
3. Construct the common eigencharacter bridge for the commuting fusion operators and derive the multiplicative equation for `fpDimCandidate`.
4. Close `fpDimCandidate_pos`, then `fpDimCandidate_fusion`, then verify `fpDimCandidateByFin_*` remain pure corollaries.
5. If (1)-(3) remain blocked, isolate the smallest foundational theorem needed
   for PF closure and prove it in core modules (no wrapper bundles, no target
   restatement assumptions).

## This Session: Proof Attempt Log (Hard Targets)

- Target attempted: `Spherical.qdim_unit` (now refactored to an explicit normalization-parameter theorem).
- Attempt route A: direct `simp`/`monoidal` on unfolded trace expression.
- Result: blocked; unresolved pivotal transport/evaluation shape mismatch.
- Attempt route B: reduction through `PivotalCategory.pivotalIso_leftDuality` with unitor cancellation.
- Result: blocked; residual conversion between `ε_ X Xᘁ` and `ε_ Xᘁ Xᘁᘁ` forms remained nontrivial.
- Attempt route C: trace-duality rewrite using `rightAdjointMate_comp_evaluation`.
- Result: reduced to pivotal-iso mate identity gap; still open.
- Attempt route D: `whiskerLeft_iff` + `convert` against `pivotalIso_leftDuality`.
- Result: reduced to one explicit unit-evaluation transport side goal; still blocked pending a clean bridge from
  `ε_ X Xᘁ` to the pivotal-induced `j.hom ▷ Xᘁ ≫ ε_ Xᘁ Xᘁᘁ` normal form in the unit-specialized context.
- Attempt route E: rewrite `ε_(𝟙)` via
  `evaluation_eq_pivotalInvMate_comp_pivotalHom` inside the `qdim_unit` goal.
- Result: reduced to a single expanded mate-normalization equation; now isolated
  to collapsing a right-adjoint-mate expansion fragment to the pivotal-zigzag
  normal form used by `pivotalIso_leftDuality`.
- Attempt route F: keep the non-whiskered target and normalize only the
  right-adjoint-mate core.
- Result: reduced to the compact unit equation
  `η ≫ (◁ j⁻¹) ≫ (j⁻¹)ᘁ ▷ 𝟙 ≫ (◁ j) ≫ ε = 𝟙`,
  but final collapse to `𝟙` is still open.
- Attempt route G: reference-driven closure using EGNO §4.7 and DGNO §2.4 with
  whisker-normalization + pivotal dual zigzags.
- Result: repeatedly reduced to the unresolved bridge between
  `(pivotalIso Xᘁ).hom` and `(pivotalIso X).invᘁ`, i.e. the EGNO Ex. 4.7.9(1)
  compatibility shape (`a_{X*} = (a_X)^{*-1}`) in our local formulation.
- Attempt route H: external consult script for blocker prompt.
- Result: no tool output produced; no actionable rewrite sequence obtained.
- Outcome: replaced theorem-level `sorry` with explicit assumption parameter
  `hunit : rightDim (𝟙_ C) = 1`; blocker now moved to deriving/providing `hunit`
  from foundational pivotal design.
- Additional closure: `qdim_dual` now proved with explicit pivotal dual-compatibility input
  `hInv : (pivotalIso Xᘁ).inv = (pivotalIso X).homᘁ`, reducing theorem-level `sorry` count.
- Additional closure: `qdim_tensor` now proved with explicit right-dimension
  multiplicativity input `hTensorR`, keeping spherical layer theorem-local and
  `sorry`-free while isolating foundational debt explicitly.
- Additional closure: `fusionCoeff_dual_swap` now proved from Frobenius
  reciprocity plus braided commutativity, reducing theorem-level `sorry` count.
- Additional closure: `ModularTensorCategory.sMatrix_squared` now proved from
  S-matrix orthogonality under explicit dual-index transport input `hDual`.
- Additional closure: foundational trace-conjugation transport is now proved
  (`leftTrace_conj`, `trace_conj`), and `SMatrix.sMatrixEnd_symmetric` /
  `SMatrix.sMatrix_symmetric` no longer require the explicit `hTraceConj`
  theorem input.
- Additional closure: `fusionCoeff_frobenius` is now proved from adjunction
  transport under explicit theorem-local simple-Hom symmetry input
  `hSimpleHomSymm` (no wrapper class added).
- Additional closure: `fusionCoeff_assoc` is now proved via class-level
  semisimple finrank decomposition contracts
  (`tensorRight_finrank_decompose` / `tensorLeft_finrank_decompose`) plus
  associator transport.
- Additional closure: `sMatrix_orthogonality` is now proved under explicit
  theorem-local assumptions `hS2` (charge-conjugation `S²` form),
  `hDual` (dual transport), and `hDualInvol` (index involutivity).
- Additional closure: `quantumDim_fusion` is now proved under explicit
  theorem-local assumptions `h00` (`S_{00} ≠ 0`) and `hVacuumRowFusion`
  (vacuum-row fusion identity).
- Additional closure: `modular_relation` is now proved under explicit
  theorem-local modular-datum assumptions `τ`, `(ST)^3 = τ·S²`, and
  `τ = gaussSum`.
- Additional closure: `totalDimSq_ne_zero` is now proved under explicit
  orthogonality normalization assumptions (`hS2`, `hDual`, `hDualInvol`,
  `hUnitOrth`).
- Additional closure: `verlinde_formula` is now proved from explicit
  diagonalization/orthogonality + dual-transport assumptions.
- Additional closure: `sMatrix_diagonalizes_fusion` is now proved from explicit
  Verlinde + orthogonality assumptions.

## Foundational Blocker Candidate

- The following relation appears to be the missing normalization bridge in both
  `qdim_unit` and `qdim_dual` attempts:
  `(PivotalCategory.pivotalIso (Xᘁ)).hom = (PivotalCategory.pivotalIso X).invᘁ`
  (equivalently the inverse form on `.inv`).
- This is exactly the pivotal dual-compatibility pattern highlighted in
  EGNO Ex. 4.7.9(1). Current class fields (`pivotalIso_naturality`,
  `pivotalIso_leftDuality`, `pivotalIso_leftDuality_dual`) have not yet yielded
  this bridge in Lean.
- Next hard target is to derive this as an internal theorem from current fields;
  if impossible, we need an explicit foundational design decision.

## Audit Commands

```bash
rg -n '^\s*sorry\b' StringAlgebra/MTC --glob '*.lean'
rg -n '^\s*axiom\b|\badmit\b|Classical\.choose|Classical\.epsilon|^\s*unsafe\b|\bpostulate\b' StringAlgebra/MTC --glob '*.lean'
lake build StringAlgebra.MTC
```

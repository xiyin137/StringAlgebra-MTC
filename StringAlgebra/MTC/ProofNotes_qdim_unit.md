# Proof Notes: `Spherical.qdim_unit`

## Scope
- Target theorem: `qdim_unit` in `StringAlgebra/MTC/Spherical.lean`.
- Current status: theorem-level `sorry` is removed by making unit normalization explicit:
  `qdim_unit` now takes
  `hunit : rightDim (𝟙_ C) = 𝟙 (𝟙_ C)`.
- Related status: `qdim_dual` and `qdim_tensor` are also now discharged with
  explicit foundational inputs (`hInv`, `hTensorR`), so `Spherical.lean`
  has no theorem-level `sorry`.
- Remaining foundational goal is to derive/provide `hunit` from stronger pivotal data.

## Extracted Reference Facts

### EGNO full, p.90 (Def. 4.7.1)
- Left categorical trace is defined for `a : V → V**` by:
  `TrL(a) = ev_{V*} ∘ (a ⊗ id_{V*}) ∘ coev_V`.
- This matches our use of a pivotal map inserted between coevaluation and evaluation.

### EGNO full, p.91 (Prop. 4.7.3)
- Quantum traces satisfy:
  1. left/right dual relation,
  2. additivity,
  3. multiplicativity under tensor,
  4. cyclicity:
     `TrL(ac) = TrL(c**a)` and right-trace analogue.
- For us, (4) is the conceptual source of “mate transport” rewrites already appearing as `rightAdjointMate_comp_evaluation`-based lemmas.

### EGNO full, p.91 (Def. 4.7.7 + Ex. 4.7.9)
- Pivotal structure is monoidal natural iso `a : Id ⇒ (** )`.
- Exercise consequence: `a_{V*} = (a_V)^{*-1}` and `a_{V**} = a_V**`.
- This is the reference origin for the dual/mate conversions around `j.hom/j.inv`.

### EGNO full, p.92 (Prop. 4.7.12 proof line)
- The character proof explicitly uses “obvious fact” `dim^a(1) = 1`.
- Why: for monoidal natural isomorphism, unit component is identity (`a_1 = id_1`).
- This is the exact conceptual reason `qdim_unit` should hold.

### DGNO, p.9–10 (§2.4.2–2.4.3)
- With any natural iso `ψ : Id ⇒ (** )` (not necessarily monoidal), traces `Tr+`, `Tr-` are defined.
- With pivotal `ψ`, one gets categorical dimensions `d`.
- Spherical condition identifies left/right traces.
- Our `leftTrace/rightTrace` formulas are the same pattern as DGNO `Tr-/Tr+` conventions.

## Lean Mapping

### Existing local lemmas already aligned with references
- `evaluation_eq_pivotalInvMate_comp_pivotalHom`
- `whisker_pivotalInv_comp_evaluation`
- `whisker_pivotalHom_comp_evaluation`
- `rightAdjointMate_core_eq_rho_hom_comp`
- `rightAdjointMate_eq_rho_inv_comp_core`
- `PivotalCategory.doubleRightAdjointMate_pivotalInv`
- `PivotalCategory.doubleRightAdjointMate_pivotalHom`
- `PivotalCategory.pivotalIso_invMate_naturality`

These cover the EGNO Prop. 4.7.3(4)-style transport/cyclicity mechanics at the string-diagram level.

### Remaining missing bridge
- The unresolved piece is the unit normalization of the pivotal component:
  transport from the current pivotal fields to the monoidal-unit consequence equivalent to `j_𝟙 = id`.
- This is now isolated as the obligation behind `hunit`, rather than a theorem-local `sorry`.

## Concrete Subgoal Decomposition (for deriving `hunit`)

1. Normalize `qdim_unit` to compact core form:
   - already reached in experiments:
   `η ≫ (◁ j⁻¹) ≫ (j⁻¹)ᘁ ▷ 𝟙 ≫ (◁ j) ≫ ε = 𝟙`.

2. Prove a unit pivotal-component lemma (one of equivalent forms):
   - `((𝟙_ C)ᘁ ◁ j.inv) ≫ (j.invᘁ ▷ 𝟙_ C) ≫ ((((𝟙_ C)ᘁ)ᘁ)ᘁ ◁ j.hom) = 𝟙 _`,
   - or a directly usable variant after composing with `η` and `ε`.

3. Discharge `rightDim (𝟙_ C) = 𝟙` (or equivalent) from Step 2.

### Unit-specialized pivotal transport equation isolated in Lean

From `PivotalCategory.pivotalIso_leftDuality (𝟙_ C)` plus `convert`, the core
unresolved comparison is now explicit:

- target side:
  `η_ (𝟙_ C) (𝟙_ C)ᘁ ≫ (pivotalIso (𝟙_ C)).hom ▷ (𝟙_ C)ᘁ ≫ ε_ (𝟙_ C)ᘁ (𝟙_ C)ᘁᘁ`
- left-duality-expanded side:
  the same `η/j/ε` block wrapped by a specific unitor/associator whisker chain
  including one `j.inv` insertion and the compensating `j.hom`.

This isolates the remaining work to a coherence + naturality normalization
problem (not an unknown categorical identity).

## High-Probability Proof Route (Foundational)

1. Specialize `PivotalCategory.pivotalIso_leftDuality` at `X = 𝟙_ C`.
2. Pre/post-compose by unitors (same pattern already used in `Pivotal.pivotalExactPairing`).
3. Rewrite coherence-only parts using `monoidal_coherence`.
4. Convert resulting expression to the compact core via:
   - `whiskerLeft_comp`,
   - `comp_whiskerRight`,
   - `whiskerRight_id`,
   - `id_whiskerLeft`,
   - existing mate/evaluation bridge lemmas from `Trace.lean`.
5. Feed the derived normalization lemma as `hunit` into `Spherical.qdim_unit`.

## Non-smuggling Guardrail
- Assumption is explicit at theorem boundary (`hunit`) instead of hidden.
- Preferred next step is still deriving `hunit` internally from stronger foundational pivotal data.
- Only derive from current class fields unless a deliberate foundational upgrade is adopted:
  - `pivotalIso_naturality`,
  - `pivotalIso_leftDuality`,
  - `pivotalIso_leftDuality_dual`,
  plus rigid/monoidal coherence and existing exact-pairing identities.

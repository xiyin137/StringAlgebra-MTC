# Codex Agent Guidance for StringAlgebra-MTC

This file is my working guidance for this repository.

## Core rigor rules

1. Never introduce `axiom` or equivalent assumption smuggling in Lean code.
2. Prioritize mathematically correct and sound definitions over shortcuts.
3. Definitions must be proper and rigorous; avoid semantic stubs that only satisfy types.
4. A simplified definition is a wrong definition for this project unless explicitly marked as temporary scaffolding; temporary scaffolding must never be presented as rigorous or final.
5. If a simplified placeholder exists, track it as a blocker and replace it with the mathematically correct definition before claiming rigor/completeness.
6. For unresolved theorem-level obligations, prefer explicit `sorry` in theorem/lemma proofs over burying missing mathematics inside extra witness fields or design-level assumptions.
7. Never use `sorry` in `def`/`structure`/`abbrev` bodies.
8. Do not weaken theorem statements or definitions just to make proofs easy.
9. If a proof stalls, check in this order: statement correctness, definition correctness, then missing infrastructure.
10. Treat type-level issues as high priority; they often indicate flawed definitions or missing bridge lemmas.
11. Prefer reusable infrastructure (helper lemmas/files) over ad-hoc local hacks.
12. Strongly prefer local infrastructure development: when a proof is blocked, first build the missing internal definitions/lemmas/bridges in this repository instead of introducing new external assumption bundles or forwarding contracts.
13. Try-hard requirement: before declaring a theorem blocked, make at least three materially different proof attempts (e.g. statement normalization, helper-lemma route, and API/definition refactor) and record the failed routes plus exact blocker.
14. No-wrapper policy: do not add thin projection/forwarding wrappers, synonym theorems, or alias APIs unless the user explicitly requests them.

## No-wrapper policy (hard rule)

1. Do not introduce theorem wrappers whose proof is only `exact Existing.theorem ...`.
2. Do not introduce structures/classes whose only purpose is to carry assumptions already expressible as theorem arguments.
3. Do not repackage a hard theorem as an equivalent assumption-parameter theorem just to remove a `sorry`.
4. If a wrapper is unavoidable for compatibility, get user approval first and document why direct usage of the canonical theorem is impossible.
5. Prefer editing call sites to use the canonical theorem directly instead of creating a bridge wrapper.
6. Helper lemmas are encouraged when they genuinely simplify repeated proof steps, control recursive unfolding, or isolate a nontrivial normalization pattern.
7. A helper lemma is acceptable only if it contributes new proof structure; if it is only a rename/forwarding alias, do not add it.

## Helper-lemma strategy

1. Add lemmas to remove repeated `calc`/rewrite blocks that appear in multiple proofs.
2. Add lemmas to stabilize proofs against recursive-definition unfolding noise.
3. Prefer domain-meaningful names that describe the mathematical transformation performed.
4. Before adding a lemma, check whether the same effect can be obtained by directly using an existing theorem without duplication.
5. Do not add "bridge" lemmas whose body is just `exact ...` unless required for external API compatibility and explicitly approved.

## Sorry-closing workflow

1. Use `sorry` intentionally to mark real proof gaps at theorem/lemma sites during active work.
2. Do not hide proof gaps by inflating structures with assumption-carrying witness fields.
3. For complex goals, split proofs into helper lemmas with explicit names and purposes.
4. Search Mathlib and local `StringAlgebra/MTC` files before re-proving known results.
5. When proofs are blocked, document attempts/failures in `StringAlgebra/MTC/ProofIdeas/`.
6. Keep TODO tracking in `TODO.md` (root) and `StringAlgebra/MTC/TODO.md`.
7. Re-check nearby definitions whenever a theorem is unexpectedly hard.
8. If still blocked after multiple attempts, leave a precise local TODO with the current goal shape, attempted lemmas/tactics, and the smallest missing ingredient.

## Context management

1. Before editing, read imports and the target region (about +/-50 lines).
2. Do not read entire large files in one pass unless required by a structural change.
3. Orientation order:
   - `TODO.md` (root)
   - `StringAlgebra/MTC/TODO.md`
   - target file module docstring + signatures
   - exact theorem/definition region being changed
4. For dependency-heavy changes, map the import chain first.

## Build and tooling rules

1. Do not run bare `lake build`; use targeted builds only.
2. Primary module build command: `lake build StringAlgebra.MTC`.
3. Single-file check command: `lake env lean StringAlgebra/MTC/<File>.lean`.
4. Never run `lake clean` unless the user explicitly asks.
5. Do not change `lean-toolchain` without explicit user approval (project currently uses an RC).

## Audit protocol

Run after substantial changes:

1. `rg -cn 'sorry' StringAlgebra/MTC --glob '*.lean'`
2. `rg -n '^\s*axiom\s|\badmit\b|Classical\\.choose|Classical\\.epsilon|^\s*unsafe\s|\bpostulate\b' StringAlgebra/MTC --glob '*.lean'`
3. `lake build StringAlgebra.MTC`

## Edit discipline

1. Default to one-file-at-a-time edits unless changes are mechanically coupled.
2. Compile the changed file before touching additional files.
3. Do not rename structures/fields without explicit user approval.
4. Prefer explicit proof scripts over brittle heavy automation.

## Mathlib search techniques

1. Use `exact?`, `apply?`, `rw?`, `simp?` in proof mode.
2. Use `#check` to inspect signatures quickly.
3. For map properties, search `Function.*` and `LinearMap.*` lemmas first.
4. When proof shape is unexpectedly hard, revisit statement/definition before adding helper assumptions.

## Practical proof tactics

1. Write and compile early to inspect real goal states.
2. Keep proof scripts explicit when automation is unstable.
3. Refactor broadly useful lemmas into shared files/subfolders.
4. Validate semantic soundness continuously, not only compilation success.

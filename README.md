# StringAlgebra-MTC

Lean 4 formalization of modular tensor category infrastructure.

## Scope

1. Foundations: `Pivotal`, `Trace`, `Spherical`, `Ribbon`, `Semisimple`
2. Fusion layer: `FusionCategory`, `FusionMatrices`, `FusionSpectral`, `FusionPF`, `BraidedFusion`, `RibbonFusion`, `Endomorphism`
3. Modular layer: `SMatrix`, `ModularTensorCategory`, `Verlinde`, `Bridge/*`

## Build

```bash
lake build StringAlgebra.MTC
```

## Audit

```bash
rg -n '^\s*sorry\b' StringAlgebra/MTC --glob '*.lean'
rg -n '^\s*class\s+.*(Axiom|Axioms|Assumption|Assumptions)' StringAlgebra/MTC --glob '*.lean'
rg -n '^\s*axiom\s|\badmit\b|Classical\.choose|Classical\.epsilon|^\s*unsafe\s' StringAlgebra/MTC --glob '*.lean'
```

## Status (2026-02-28)

1. Build status: `lake build StringAlgebra.MTC` passes.
2. Theorem-level `sorry` count: `2` (both in `StringAlgebra/MTC/FusionPF.lean`).
3. No assumption-bundle wrapper classes.
4. No hidden-choice smuggling patterns (`axiom` / `admit` / `unsafe` / `postulate` scan clean).
5. Umbrella import is wrapper-minimized: `StringAlgebra/MTC.lean` does not import `DevelopmentHarness` (harness remains opt-in).

## Related Repositories

1. Control repo: https://github.com/xiyin137/StringAlgebra
2. MZV: https://github.com/xiyin137/StringAlgebra-MZV
3. VOA: https://github.com/xiyin137/StringAlgebra-VOA
4. Linfinity: https://github.com/xiyin137/StringAlgebra-Linfinity

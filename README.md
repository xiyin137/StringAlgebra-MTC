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

## Status (2026-02-26)

1. Theorem-level `sorry` count: `16` (theorem-level proof debt only)
2. No assumption-bundle wrapper classes.
3. No hidden-choice smuggling patterns.

## Related Repositories

1. Control repo: https://github.com/xiyin137/StringAlgebra
2. MZV: https://github.com/xiyin137/StringAlgebra-MZV
3. VOA: https://github.com/xiyin137/StringAlgebra-VOA
4. Linfinity: https://github.com/xiyin137/StringAlgebra-Linfinity

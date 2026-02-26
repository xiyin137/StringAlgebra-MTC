# StringAlgebra MTC

Standalone extraction of `StringAlgebra.MTC` from the StringAlgebra monorepo.

## Status (2026-02-26)

1. Theorem-level `sorry` count in `StringAlgebra/MTC`: 16
2. Anti-smuggling policy: no `axiom` smuggling, no assumption-bundle wrapper classes.
3. Build target: `lake build StringAlgebra.MTC`

## Quick Audit Commands

```bash
lake build StringAlgebra.MTC
rg -n '^\s*sorry\b' StringAlgebra/MTC --glob '*.lean'
rg -n '^\s*class\s+.*(Axiom|Axioms|Assumption|Assumptions)' StringAlgebra/MTC --glob '*.lean'
rg -n '^\s*axiom\s|\badmit\b|Classical\.choose|Classical\.epsilon|^\s*unsafe\s' StringAlgebra/MTC --glob '*.lean'
```

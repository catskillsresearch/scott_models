# LRSODInCIC (standalone)

Thought exercise: L/R/S/O/D axiom layers embedded in Lean 4's CIC — no Mathlib, no scott1972/1980/1982.

| File | Role |
|---|---|
| `LRSODInCIC.md` | Paper (axioms, CIC, translation) |
| `LRSODInCIC.lean` | Deep embedding |

```bash
cd LRSODInCIC
lake build
```

Open `LRSODInCIC.lean` in Cursor; the Lean server uses **this** package's `lakefile.toml`, not the parent `ScottModels` workspace.

# scott_models

**Part IV** of the Scott domain theory monograph: equivalence theorems relating the
1972 continuous-lattice, 1980 neighborhood-system, and 1982 information-system
presentations.

Depends on sibling packages (Lake path deps by default):

- [`scott1972`](../scott1972) — Part I
- [`scott1980`](../scott1980) — Part II
- [`scott1982`](../scott1982) — Part III

Replace `path = "../…"` in `lakefile.toml` with git URLs when publishing.

## Build

```bash
lake exe cache get
lake build ScottModels
```

Narrative inventory: `arxiv.md`. Session resume: `HANDOFF.md`.

[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/scott_models/build.yml?label=Lean%204)](https://github.com/catskillsresearch/scott_models/actions/workflows/build.yml)
# scott_models

Equivalence theorems relating the 1972 continuous-lattice, 1980 neighborhood-system,
and 1982 information-system presentations of Scott domain theory.

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

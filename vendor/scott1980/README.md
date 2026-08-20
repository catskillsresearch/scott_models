[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/scott1980/build.yml?label=Lean%204)](https://github.com/catskillsresearch/scott1980/actions/workflows/build.yml)
# scott1980

Lean 4 formalization of Dana Scott's **1981** PRG-19 *Lectures on a Mathematical
Theory of Computation* (neighborhood systems / filter domains).

Standalone package — no dependency on the 1972 formalization. Part IV equivalence
theorems live in [`scott_models`](../scott_models).

## Build

```bash
lake exe cache get
lake build Scott1980
```

Pinned: Lean / mathlib **v4.30.0** (`lean-toolchain`).

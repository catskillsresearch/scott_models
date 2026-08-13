# Lean 4 formalization of 2 models and 5 presentations for untyped λ-calculus
Within "models" we have "presentations." Here is the landscape, and below it the precise goals for a Lean formalization. Please correct me if I'm wrong.

**Model: Pω** (set-theoretic λ-model)

- **Presentation 1 — MSFR:** enumeration operators / effective functionals (Myhill–Shepherdson [Myhill–Shepherdson 1955]; Friedberg–Rogers [Friedberg–Rogers 1959]).
- **Presentation 2 — Gr** (my name, to distinguish the model Pω from this presentation): set-theoretic graph construction (Plotkin [Plotkin 1972]; Scott [Scott 1976]). Gr is local notation; the literature usually identifies it with Pω / the graph model rather than treating it as a separate symbol.

**Model: D∞** (domain-theoretic λ-model; reflexive domain with D∞ ≅ [D∞ → D∞], Scott November 1969, published [Scott 1972])

- **Presentation 1 — ScDom:** continuous lattices / order–topology (Scott [Scott 1972]; cf. PRG-7 [Scott 1971]).
- **Presentation 2 — Neigh:** neighbourhood systems, filters as domain elements (Scott [Scott 1981]; Oxford lectures Michaelmas Term 1980).
- **Presentation 3 — InfSys:** information systems, consistent closed token sets (Scott [Scott 1982]).

Order-isomorphism bridges for ScDom / Neigh / InfSys are already in https://github.com/catskillsresearch/scott_models (`PresentationDomains.lean`, etc.). We plan to extend this package.

**Target theorems (Lean 4):**

**(i)** MSFR and Gr determine **isomorphic λ-models** of untyped λ-calculus (same Pω model class up to isomorphism, with application/abstraction agreeing under the bridge).

**(ii)** ScDom, Neigh, and InfSys determine **isomorphic λ-models** of untyped λ-calculus (extending the existing order-isomorphism bridges to transport the λ-structure, not just the carrier posets).

**(iii)** Each presentation in (i) and (ii) yields a **non-trivial, β-sound model** of untyped λ-calculus (terms are interpreted in a structure satisfying β-conversion; the model is not degenerate — e.g. distinct Church numerals).

**(iv)** The Pω model from (i) and the D∞ model from (ii) are **not isomorphic** to each other (two distinct model classes for the same syntactic untyped λ-calculus).

---

**References**

- **[Myhill–Shepherdson 1955]** John Myhill, John C. Shepherdson, "Effective operations on partial recursive functions," *Zeitschrift für Mathematische Logik und Grundlagen der Mathematik* 1 (1955), 310–317.

- **[Friedberg–Rogers 1959]** Richard M. Friedberg, Hartley Rogers Jr., "Reducibility and completeness for sets of integers," *Zeitschrift für Mathematische Logik und Grundlagen der Mathematik* 5 (1959), 117–125. (Abstract: *Journal of Symbolic Logic* 22 (1957), 107.)

- **[Plotkin 1972]** Gordon D. Plotkin, "Set-theoretical and other elementary models of the λ-calculus," *Theoretical Computer Science* 121 (1993), 351–409 (includes the previously unpublished 1972 memorandum).

- **[Scott 1971]** Dana S. Scott, "Continuous Lattices," Technical Monograph PRG-7, Oxford University Programming Research Group, August 1971.

- **[Scott 1972]** Dana S. Scott, "Continuous lattices," in *Toposes, Algebraic Geometry and Logic* (F. W. Lawvere, ed.), *Lecture Notes in Mathematics* 274, Springer, 1972, 97–136.

- **[Scott 1976]** Dana S. Scott, "Data types as lattices: To the Memory of Christopher Strachey, 1916–1975," *SIAM Journal on Computing* 5 (1976), 522–587.

- **[Scott 1981]** Dana S. Scott, *Lectures on a Mathematical Theory of Computation*, Technical Monograph PRG-19, Oxford University Computing Laboratory, May 1981 (Michaelmas Term lectures, 1980).

- **[Scott 1982]** Dana S. Scott, "Domains for denotational semantics," in *Automata, Languages and Programming: 9th ICALP* (M. Nielsen, E. M. Schmidt, eds.), *Lecture Notes in Computer Science* 140, Springer, 1982, 577–613.

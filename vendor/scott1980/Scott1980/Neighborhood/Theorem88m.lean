/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Theorem88l
import Scott1980.Neighborhood.UComputablePresentation

/-!
# Theorem 8.8(c), Part 6 of 6 — final assembly

Following Theorem 8.8(c)'s 6-part plan (`arxiv.md`): Parts 1–5 (`Theorem88h.lean`–`Theorem88l.lean`)
built, relative to an *arbitrary* `qChar`/`cons : ℕ → ℕ` satisfying the two extracted hypotheses
`hqChar`/`hcons`, an enumeration `D_X qChar cons : ℕ → Set α` that is onto `fixedNbhd a`
(`D_X_mem`/`D_X_surj`), has recursively decidable `interEq`/`cons` relations
(`D_X_interEq_computable`/`D_X_cons_computable`), and a primitive-recursive `.inter`
(`D_inter`/`D_inter_primrec`/`D_X_inter_spec`). This file supplies the two missing concrete
witnesses (`qChar` from Part 1's `diagFixed_exists_qChar`, `cons` from `P.cons_computable` itself)
and packages the result into a genuine `ComputablePresentation (fixedNbhd a)`, proving the headline:

> **Theorem 8.8(c).** If `a : U → U` is a computable, finitary projection, then
> `{Y ∈ U ∣ Y a Y} = fixedNbhd a` is effectively given (and, by Theorem 8.5/8.6(a), a subsystem of
> `U`).

## Why the two witnesses cause no `Classical.choice`

Both `qChar` and `cons` are extracted from *propositional* existentials (`diagFixed_exists_qChar`,
`P.cons_computable` — both `RecDecidable`-shaped `∃ f, ...`) via plain `obtain`, which is legitimate
choice-free `Exists`-elimination **because the target of `fixedNbhd_isEffectivelyGiven` is itself a
`Prop`** (`NeighborhoodSystem.IsEffectivelyGiven = Nonempty (ComputablePresentation V)`, and
`Nonempty` is a `Prop`) — eliminating a `Prop`-valued `Exists` into a `Prop`-valued goal never needs
choice, only eliminating into `Type`/`Data` does. This mirrors the discipline already used
throughout Lecture VII/VIII (e.g. `Theorem88a.lean`'s `theorem_8_8_a`, also a bare `Nonempty`
statement). We therefore do **not** state a `def`-level "the" presentation; only the `Prop`-level
existence statement.

## Assembly

`hqChar`/`hqCharp` come straight from `diagFixed_exists_qChar hcomp` (Part 1). `hcons`/`hconsp` come
from unfolding `P.cons_computable : RecDecidable₂ (fun n m => ∃k, Xₖ ⊆ Xₙ∩Xₘ)`, i.e. `∃ f,
Nat.Primrec f ∧ ∀ t, (∃k,…) ↔ f t = 1` — reindexing the `∀t` at `t := Nat.pair n m` and simplifying
`unpair_pair` gives exactly the `hcons` shape every one of Parts 2–5's lemmas expects.

The `masterIdx := 0` field needs `D_X qChar cons 0 = (fixedNbhd a).master = V.master`: unfolding
`D_X`/`myFoldCode_eq` reduces `myFoldCode qChar cons 0` to `myFold qChar cons (decodeList 0) =
myFold qChar cons [] = P.masterIdx` (`decodeList_zero`/`myFold_nil`), and `P.masterIdx_spec` finishes
it.

Everything here is **choice-free** (`⊆ {propext, Quot.sound}`): the only `Exists`-eliminations are
into a `Prop` goal (see above), and every other ingredient (Parts 1–5) was already audited
choice-free. The generic `fixedNbhd_isEffectivelyGiven` audits exactly this way. **The specialization
`theorem_8_8_c` itself audits `⊆ {propext, Classical.choice, Quot.sound}`** — but this is *not* new
taint introduced here: `U` (`Definition87.lean`) already audits with `Classical.choice` for a
documented upstream reason (Mathlib's `Rat` order instance path), and the two other `U`-mentioning
headline theorems, `theorem_8_8_a`/`theorem_8_8_b`, audit identically (confirmed directly). Any proof
term merely *stating* something about `ApproximableMap U U`/`_ ◁ U` inherits `U`'s own footprint.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

/-- **Theorem 8.8(c), Part 6 of 6 — final assembly.** A computable approximable self-map `a` of an
effectively given `V` (via `P`) makes `fixedNbhd a` effectively given: package Parts 1–5's `D_X`/
`D_inter` enumeration, instantiated at concrete witnesses `qChar` (Part 1) and `cons` (`P`'s own
`cons_computable`), into a `ComputablePresentation (fixedNbhd a)`. -/
theorem fixedNbhd_isEffectivelyGiven {P : ComputablePresentation V} {a : ApproximableMap V V}
    (hcomp : IsComputableMap P P a) : (fixedNbhd a).IsEffectivelyGiven := by
  obtain ⟨qChar, hqCharp, hqChar⟩ := diagFixed_exists_qChar hcomp
  obtain ⟨cons, hconsp, hconse⟩ := P.cons_computable
  have hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m := by
    intro n m
    have h := hconse (Nat.pair n m)
    simp only [unpair_pair_fst, unpair_pair_snd] at h
    exact h.symm
  refine ⟨{
    X := D_X P qChar cons
    mem_X := D_X_mem hqChar hcons
    surj := fun hY => D_X_surj hqChar hcons hY
    interEq_computable := D_X_interEq_computable P qChar cons hqCharp hconsp
    cons_computable := D_X_cons_computable P qChar cons hqChar hcons hqCharp hconsp
    inter := D_inter
    inter_primrec := D_inter_primrec
    inter_spec := fun h => D_X_inter_spec hcons h
    masterIdx := 0
    masterIdx_spec := ?_ }⟩
  show D_X P qChar cons 0 = V.master
  show P.X (myFoldCode P qChar cons 0) = V.master
  rw [myFoldCode_eq, decodeList_zero, myFold_nil, P.masterIdx_spec]

/-- **Theorem 8.8(c) (Scott 1981, PRG-19), headline.** If `a : U → U` is a computable, finitary
projection of the universal domain, then `{Y ∈ U ∣ Y a Y}` is effectively given (and, unconditionally
by Theorem 8.5, a subsystem of `U`). As in Theorem 8.6(c)'s converse, `hfin` is carried in the
signature to match Scott's stated hypothesis on `a`, but is **not** actually needed by this
implication — only `hcomp` drives the effectiveness argument; this is called out here rather than
silently dropping the hypothesis. -/
theorem theorem_8_8_c {a : ApproximableMap U U} (_hfin : IsFinitaryProjection a)
    (hcomp : IsComputableMap UComputablePresentation UComputablePresentation a) :
    (fixedNbhd a).IsEffectivelyGiven ∧ fixedNbhd a ◁ U :=
  ⟨fixedNbhd_isEffectivelyGiven hcomp, fixedNbhd_subsystem a⟩

end Scott1980.Neighborhood

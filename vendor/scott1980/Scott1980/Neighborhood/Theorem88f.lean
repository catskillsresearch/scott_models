/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Theorem88e
import Scott1980.Neighborhood.Definition72
import Scott1980.Neighborhood.Proposition612

/-!
# Theorem 8.8(b)(vii)(4) — the projection pair `D'' ⊴ U` is computable

`Theorem88e.lean` (Part 7's third sub-part) assembled `D'' := DprimeUCode P`, `D ≅ᴰ D''`, and
`D'' ◁ U`, with `D''`'s own `ComputablePresentation` (`DprimeUCodePresentation`, master index `0`,
`X n := Yc P n = UX (YseqCode P n)`). This file supplies the actual headline claim of Theorem
8.8(b)(vii): the projection pair `i := (D'' ◁ U).inj`/`j := (D'' ◁ U).proj` (Proposition 6.12) is
**computable** (Definition 7.2, `IsComputableMap`) relative to `DprimeUCodePresentation`/
`UComputablePresentation`.

## Why this is now easy

Both relations unfold (`Subsystem.inj_rel`/`Subsystem.proj_rel`) to a `mem`-clause on each side
*plus* a raw subset test — and every `mem`-clause is automatically true once both sides are read off
their own presentations (`⟨n, rfl⟩` for `D''`, `U_mem_UX` for `U`), so `i`/`j`'s relations reduce to
exactly

* `i`: `Yc P n ⊆ UX m`, i.e. `UX (YseqCode P n) ⊆ UX m`;
* `j`: `UX m ⊆ Yc P n`, i.e. `UX m ⊆ UX (YseqCode P n)`;

both instances of the single **generic** fact `Xₙ ⊆ Xₘ` is recursively decidable for *any*
`ComputablePresentation` (`ComputablePresentation.incl_computable`, Definition 7.1), here applied to
`UComputablePresentation` and reindexed along the `Nat.Primrec` function `YseqCode P`
(`primrec_YseqCode`, Theorem 8.8(b)(vii)(2)) in one argument. No new `Nat.Primrec` machinery, no new
decidability core — the entire content is packaging two reindexings of `incl_computable`, decidable
hence r.e. (`RecDecidable.re`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- **The injection `i : D'' → U` is computable.** `i`'s relation `Yc P n \, i \, UX m` reduces to
the raw code-level subset test `UX (YseqCode P n) ⊆ UX m`, decidable by reindexing
`UComputablePresentation.incl_computable` along `YseqCode P` in the first argument. -/
theorem DprimeUCode_inj_isComputableMap :
    IsComputableMap (DprimeUCodePresentation P) UComputablePresentation
      (DprimeUCode_subsystem P).inj := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair (YseqCode P t.unpair.1) t.unpair.2) :=
    Nat.Primrec.pair ((primrec_YseqCode P).comp Nat.Primrec.left) Nat.Primrec.right
  have hp : RecDecidable (fun t : ℕ => UX (YseqCode P t.unpair.1) ⊆ UX t.unpair.2) := by
    refine RecDecidable.of_iff (fun t => ?_) (UComputablePresentation.incl_computable.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
    rfl
  refine REPred.of_iff (fun t => ?_) hp.re
  show (DprimeUCode_subsystem P).inj.rel (Yc P t.unpair.1) (UX t.unpair.2) ↔ _
  rw [Subsystem.inj_rel]
  exact ⟨fun ⟨_, _, hsub⟩ => hsub,
    fun hsub => ⟨⟨t.unpair.1, rfl⟩, U_mem_UX _, hsub⟩⟩

/-- **The projection `j : U → D''` is computable.** `j`'s relation `UX m \, j \, Yc P n` reduces to
the raw code-level subset test `UX m ⊆ UX (YseqCode P n)`, decidable by reindexing
`UComputablePresentation.incl_computable` along `YseqCode P` in the second argument. -/
theorem DprimeUCode_proj_isComputableMap :
    IsComputableMap UComputablePresentation (DprimeUCodePresentation P)
      (DprimeUCode_subsystem P).proj := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 (YseqCode P t.unpair.2)) :=
    Nat.Primrec.pair Nat.Primrec.left ((primrec_YseqCode P).comp Nat.Primrec.right)
  have hp : RecDecidable (fun t : ℕ => UX t.unpair.1 ⊆ UX (YseqCode P t.unpair.2)) := by
    refine RecDecidable.of_iff (fun t => ?_) (UComputablePresentation.incl_computable.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
    rfl
  refine REPred.of_iff (fun t => ?_) hp.re
  show (DprimeUCode_subsystem P).proj.rel (UX t.unpair.1) (Yc P t.unpair.2) ↔ _
  rw [Subsystem.proj_rel]
  exact ⟨fun ⟨_, _, hsub⟩ => hsub,
    fun hsub => ⟨U_mem_UX _, ⟨t.unpair.2, rfl⟩, hsub⟩⟩

/-- **Theorem 8.8(b)(vii)(4), full statement.** The projection pair witnessing `D'' ◁ U` (Proposition
6.12, applied to `DprimeUCode_subsystem P : DprimeUCode P ◁ U`) is computable in both directions
relative to `D''`'s own presentation (`DprimeUCodePresentation`) and `U`'s presentation
(`UComputablePresentation`) — the headline claim of Theorem 8.8(b)(vii). -/
theorem DprimeUCode_projectionPair_isComputable :
    IsComputableMap (DprimeUCodePresentation P) UComputablePresentation
        (DprimeUCode_subsystem P).inj ∧
      IsComputableMap UComputablePresentation (DprimeUCodePresentation P)
        (DprimeUCode_subsystem P).proj :=
  ⟨DprimeUCode_inj_isComputableMap P, DprimeUCode_proj_isComputableMap P⟩

end Scott1980.Neighborhood

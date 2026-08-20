/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Theorem88b

/-!
# Theorem 8.8(b), Part 6d/6e — `D'` (Theorem 8.8(a)'s own subsystem) is effectively given

`Theorem88b.lean` (Part 6a–6c) reduces `genAtom (idxSet e)`-emptiness to `DAtom`-emptiness, which
Part 5 (`DAtomDecidable.lean`) already decides. The original Part 6d/6e plan tried to go one step
further: build an explicit, *computable* replacement `splitEff` for `splitChoice` (Theorem 8.8(a)'s
classical splitting operation), tracking a `U`-code `atomUCode` alongside the abstract `Set`-level
recursion, so that `Yidx e n` itself could be read off as an explicit `U`-code. That plan hit a
genuine wall (recorded in `HANDOFF.md`'s "design pitfall" entry): `SplitU.lean`'s `splitULeft`/
`splitURight` split against the *specific* code fed in (via `canonCode`'s first pair), not against
the *set* `B` alone, and two different codes for the same set can canonicalize to different first
pairs — so there is no way to make an abstract, `Set`-valued `splitEff` agree, code-for-code, with
an independently-built primitive-recursive tracker without first building a genuine canonical-form
(sort+merge) normalization of `List (ℚ × ℚ)`, a substantial undertaking of its own.

## The resolution: never compute `Yidx e n`'s value as a code at all

**The key realization**: `ComputablePresentation`'s `X : ℕ → Set α` field is *data*, not required to
be "computable" as a function producing explicit codes (`unitPresentation`'s constant `X _ := Set.univ`
is the existing sanity check for this). All that must be *decidable* are the two **index relations**
(`interEq_computable`, `cons_computable`) and the primitive-recursive `inter` index function. So
instead of computing `Yidx e n`'s value, we show its *index relations* reduce directly to facts
already decided by Parts 5–6c, via `Theorem88.lean`'s existing generic transfer lemmas — with **no
new splitting operation, no canonical forms, and no exponential atom-union machinery** needed:

* `Yidx e i ∩ Yidx e j = Yidx e k` transfers (`transfer_inter_eq_iff`) to `idxSet e i ∩ idxSet e j =
  idxSet e k`, which unfolds (`idxSet_inter_eq_iff_DAtom`) to `(e k ⊆ e i) ∧ (e k ⊆ e j) ∧
  (DAtom (P0 P) [i, j] [k] = ∅)` — three small, fixed-size decidable facts (two `incl_computable`
  queries, one `DAtom_recDecidable` query at 2-element/1-element lists).
* `∃ k, Yidx e k ⊆ Yidx e i ∩ Yidx e j` transfers (`embed_subset_iff`, twice) to `∃ k, e k ⊆ e i ∧
  e k ⊆ e j`, which is *literally* `(P0 P).cons_computable`'s own predicate — reused verbatim.
* The intersection index itself is *literally* `(P0 P).inter n m` (Scott's own index, reused): its
  correctness transfers via `idxSet_inter_of_inter_eq` + `transfer_inter_eq_iff`.
* The master index is `0` (`Yidx_zero`, already proved in `Theorem88a.lean`).

This packages into `DprimeUPresentation`, a genuine `ComputablePresentation (DprimeU D (e P) …)` —
i.e. **Theorem 8.8(a)'s own `D'` (no new construction!) is effectively given whenever `D` is**. This
completes Part 6 of Theorem 8.8(b): the recursive `Yₙ`-chain now has a certified effective
witness/verifier (its index relations are decidable), ready for Part 7's `IsComputableMap` work on
the embedding/projection pair `Subsystem.inj`/`Subsystem.proj` (`D' ◁ U`, via `DprimeU_subsystem`).

Everything here is **choice-free at the `Nat.Primrec` core** (the deciders extracted from
`(P0 P).cons_computable`/`incl_computable`/`DAtom_recDecidable` are plain primitive-recursive
functions); the presentation's `X`-field itself (`Yidx e`) is unavoidably classical (built via
`splitChoice`), exactly like `unitPresentation`'s trivial `X` field is "just data".
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-! ## A general `idxSet`/`DAtom` fact: 2-point atom emptiness characterizes `idxSet`-intersection -/

/-- **`idxSet`-intersection, characterized by a single `DAtom` emptiness query.** For *any*
computable presentation `Q`, `idxSet Q.X i ∩ idxSet Q.X j = idxSet Q.X k` iff `Q.X k` refines both
`Q.X i` and `Q.X j` (Scott's own decidable inclusion) *and* the depth-2 atom `DAtom Q [i,j] [k]`
(positive constraints `{i,j}`, negative constraint `{k}`) is empty. The three pieces are each
decidable (`incl_computable` used twice, `DAtom_recDecidable` at a fixed 2-element/1-element list
pair), so this is
the bridge that lets Part 5's `DAtom` apparatus decide `idxSet`-level *equations*, not just
emptiness. -/
theorem idxSet_inter_eq_iff_DAtom {β : Type*} {V : NeighborhoodSystem β}
    (Q : ComputablePresentation V) (i j k : ℕ) :
    idxSet Q.X i ∩ idxSet Q.X j = idxSet Q.X k ↔
      Q.X k ⊆ Q.X i ∧ Q.X k ⊆ Q.X j ∧ DAtom Q [i, j] [k] = ∅ := by
  have hDAtom_iff : DAtom Q [i, j] [k] = ∅ ↔ idxSet Q.X i ∩ idxSet Q.X j ⊆ idxSet Q.X k := by
    have hIPos : IPos Q [i, j] = idxSet Q.X i ∩ idxSet Q.X j := by
      rw [IPos_cons, IPos_cons, IPos_nil, Set.inter_univ]
    have hDAtom_eq : DAtom Q [i, j] [k] = (idxSet Q.X i ∩ idxSet Q.X j) \ idxSet Q.X k := by
      show IPos Q [i, j] ∩ {m | ∀ j' ∈ ([k] : List ℕ), m ∉ idxSet Q.X j'} = _
      rw [hIPos]
      ext m
      simp [Set.mem_diff]
    rw [hDAtom_eq, Set.diff_eq_empty]
  constructor
  · intro heq
    have h1 : idxSet Q.X k ⊆ idxSet Q.X i := by rw [← heq]; exact Set.inter_subset_left
    have h2 : idxSet Q.X k ⊆ idxSet Q.X j := by rw [← heq]; exact Set.inter_subset_right
    exact ⟨(idxSet_subset_iff Q.X k i).mp h1, (idxSet_subset_iff Q.X k j).mp h2,
      hDAtom_iff.mpr heq.subset⟩
  · rintro ⟨hki, hkj, hempty⟩
    exact Set.Subset.antisymm (hDAtom_iff.mp hempty)
      (Set.subset_inter ((idxSet_subset_iff Q.X k i).mpr hki) ((idxSet_subset_iff Q.X k j).mpr hkj))

/-! ## Packaging `DAtom (P0 P) [i, j] [k] = ∅` as a `RecDecidable₃` -/

private def capPosCode (t : ℕ) : ℕ := encodeList [t.unpair.1, t.unpair.2.unpair.1]

private def capNegCode (t : ℕ) : ℕ := encodeList [t.unpair.2.unpair.2]

private theorem capPosCode_eq (a b : ℕ) : encodeList [a, b] = Nat.pair a (Nat.pair b 0 + 1) + 1 :=
  rfl

private theorem capNegCode_eq (a : ℕ) : encodeList [a] = Nat.pair a 0 + 1 := rfl

private theorem primrec_capPosCode : Nat.Primrec capPosCode := by
  have h2 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hinner : Nat.Primrec (fun t : ℕ => Nat.pair (t.unpair.2.unpair.1) 0 + 1) :=
    primrec_add₂ (Nat.Primrec.pair h2 (Nat.Primrec.const 0)) (Nat.Primrec.const 1)
  have houter : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 (Nat.pair t.unpair.2.unpair.1 0 + 1)) :=
    Nat.Primrec.pair Nat.Primrec.left hinner
  refine (primrec_add₂ houter (Nat.Primrec.const 1)).of_eq (fun t => ?_)
  show _ = capPosCode t
  rw [capPosCode, capPosCode_eq]

private theorem primrec_capNegCode : Nat.Primrec capNegCode := by
  have hinner : Nat.Primrec (fun t : ℕ => Nat.pair (t.unpair.2.unpair.2) 0) :=
    Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right) (Nat.Primrec.const 0)
  refine (primrec_add₂ hinner (Nat.Primrec.const 1)).of_eq (fun t => ?_)
  show _ = capNegCode t
  rw [capNegCode, capNegCode_eq]

/-- **`DAtom (P0 P) [i, j] [k] = ∅` is recursively decidable in `(i, j, k)`.** Reindexes
`DAtom_recDecidable (P0 P)` (Part 5) along the codes of the fixed-shape lists `[i,j]`/`[k]`. -/
theorem DAtom_pair_recDecidable :
    RecDecidable₃ (fun i j k => DAtom (P0 P) [i, j] [k] = ∅) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair (capPosCode t) (capNegCode t)) :=
    primrec_capPosCode.pair primrec_capNegCode
  have hp := (DAtom_recDecidable (P0 P)).comp hg
  refine RecDecidable.of_iff (fun t => ?_) hp
  simp only [unpair_pair_fst, unpair_pair_snd, capPosCode, capNegCode, decodeList_encodeList]

/-! ## `Yidx`'s index relations are decidable -/

/-- **`Yidx (e P) i ⊆ Yidx (e P) j`, reindexed.** A thin wrapper packaging two `incl_computable`-style
facts (`(P0 P).X k ⊆ (P0 P).X i`, resp. `j`) as `RecDecidable₃`, ready to combine with the `DAtom`
decider above. -/
private theorem inclK_i_recDecidable :
    RecDecidable₃ (fun i _ k => (P0 P).X k ⊆ (P0 P).X i) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.2.unpair.2 t.unpair.1) :=
    Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right) Nat.Primrec.left
  have hp := (P0 P).incl_computable.comp hg
  refine RecDecidable.of_iff (fun t => ?_) hp
  simp only [unpair_pair_fst, unpair_pair_snd]

private theorem inclK_j_recDecidable :
    RecDecidable₃ (fun _ j k => (P0 P).X k ⊆ (P0 P).X j) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.2.unpair.2 t.unpair.2.unpair.1) :=
    Nat.Primrec.pair (Nat.Primrec.right.comp Nat.Primrec.right)
      (Nat.Primrec.left.comp Nat.Primrec.right)
  have hp := (P0 P).incl_computable.comp hg
  refine RecDecidable.of_iff (fun t => ?_) hp
  simp only [unpair_pair_fst, unpair_pair_snd]

/-- **Part 6's headline decidability result.** `Yidx (e P) i ∩ Yidx (e P) j = Yidx (e P) k` is
recursively decidable in `(i, j, k)`: it transfers (`transfer_inter_eq_iff`) to the `idxSet`-level
equation, which `idxSet_inter_eq_iff_DAtom` reduces to two `incl_computable` queries and one
`DAtom_recDecidable` query — all already decidable. -/
theorem DprimeU_interEq_computable :
    RecDecidable₃ (fun i j k => Yidx (e P) i ∩ Yidx (e P) j = Yidx (e P) k) := by
  have hcomb : RecDecidable₃ (fun i j k =>
      ((P0 P).X k ⊆ (P0 P).X i ∧ (P0 P).X k ⊆ (P0 P).X j) ∧ DAtom (P0 P) [i, j] [k] = ∅) :=
    (inclK_i_recDecidable P |>.and (inclK_j_recDecidable P)).and (DAtom_pair_recDecidable P)
  refine RecDecidable.of_iff (fun t => ?_) hcomb
  dsimp only
  rw [← transfer_inter_eq_iff splitChoice (idxSet (e P)) Set.univ univ_nonempty_nat
      splitChoice_isSplitSpec t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2
      (Set.subset_univ _) (Set.subset_univ _) (Set.subset_univ _),
    idxSet_inter_eq_iff_DAtom (P0 P) t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2]
  tauto

/-- **`∃ k, Yidx (e P) k ⊆ Yidx (e P) i ∩ Yidx (e P) j` is recursively decidable in `(i, j)`.** This
transfers (`embed_subset_iff`, twice) to `∃ k, e P k ⊆ e P i ∧ e P k ⊆ e P j`, which is literally
`(P0 P).cons_computable`'s own predicate — reused with no new `Nat.Primrec` work. -/
theorem DprimeU_cons_computable :
    RecDecidable₂ (fun i j => ∃ k, Yidx (e P) k ⊆ Yidx (e P) i ∩ Yidx (e P) j) := by
  refine RecDecidable.of_iff (fun t => ?_) (P0 P).cons_computable
  simp only [Set.subset_inter_iff]
  exact exists_congr (fun k => by
    rw [← embed_subset_iff (e P) k t.unpair.1, ← embed_subset_iff (e P) k t.unpair.2])

/-- **The intersection index transfers.** `(P0 P).inter n m` — Scott's own primitive-recursive
intersection index for `D` (reused verbatim, no new index function) — also indexes `Yidx (e P) n ∩
Yidx (e P) m` whenever that intersection is consistent. -/
theorem DprimeU_inter_spec {n m : ℕ}
    (h : ∃ k, Yidx (e P) k ⊆ Yidx (e P) n ∩ Yidx (e P) m) :
    Yidx (e P) ((P0 P).inter n m) = Yidx (e P) n ∩ Yidx (e P) m := by
  have h' : ∃ k, (P0 P).X k ⊆ (P0 P).X n ∩ (P0 P).X m := by
    obtain ⟨k, hk⟩ := h
    rw [Set.subset_inter_iff] at hk
    exact ⟨k, Set.subset_inter ((embed_subset_iff (e P) k n).mpr hk.1)
      ((embed_subset_iff (e P) k m).mpr hk.2)⟩
  have heP : (P0 P).X ((P0 P).inter n m) = (P0 P).X n ∩ (P0 P).X m := (P0 P).inter_spec h'
  have hidx : idxSet (e P) n ∩ idxSet (e P) m = idxSet (e P) ((P0 P).inter n m) :=
    idxSet_inter_of_inter_eq (e P) heP.symm
  exact ((transfer_inter_eq_iff splitChoice (idxSet (e P)) Set.univ univ_nonempty_nat
    splitChoice_isSplitSpec n m ((P0 P).inter n m)
    (Set.subset_univ _) (Set.subset_univ _) (Set.subset_univ _)).mp hidx).symm

/-! ## Assembling the `ComputablePresentation` -/

/-- **Part 6's final assembly.** Theorem 8.8(a)'s own subsystem `DprimeU D (e P) (hcover P) (he0 P)`
(no new construction — the *same* classical `D'`, built via `splitChoice`, that already witnesses
`D ≅ᴰ D'` and `D' ◁ U`) is **effectively given**: its enumeration is `Yidx (e P)` (classical, exactly
like `unitPresentation`'s constant `X`), and its two index relations reduce, via the transfer lemmas
above, to facts already decided by `P0 P`'s own deciders and Part 5's `DAtom_recDecidable`. -/
noncomputable def DprimeUPresentation :
    ComputablePresentation (DprimeU D (e P) (hcover P) (he0 P)) where
  X n := Yidx (e P) n
  mem_X n := ⟨n, rfl⟩
  surj := fun hY => hY.imp (fun _ h => h.symm)
  interEq_computable := DprimeU_interEq_computable P
  cons_computable := DprimeU_cons_computable P
  inter n m := (P0 P).inter n m
  inter_primrec := (P0 P).inter_primrec
  inter_spec h := DprimeU_inter_spec P h
  masterIdx := 0
  masterIdx_spec := Yidx_zero D (e P) (hcover P) (he0 P)

/-- **Theorem 8.8(b), Part 6.** If `D` is effectively given, then Theorem 8.8(a)'s own subsystem
`D'` (with `D ≅ᴰ D'` and `D' ◁ U`, from `isomorphic_DprimeU`/`DprimeU_subsystem`) is *also*
effectively given. -/
theorem DprimeU_isEffectivelyGiven :
    (DprimeU D (e P) (hcover P) (he0 P)).IsEffectivelyGiven :=
  ⟨DprimeUPresentation P⟩

end Scott1980.Neighborhood

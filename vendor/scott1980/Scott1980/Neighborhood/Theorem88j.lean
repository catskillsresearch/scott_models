/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Theorem88i

/-!
# Theorem 8.8(c), Part 3 of 6 — the induced enumeration covers `fixedNbhd a`

Following Theorem 8.8(c)'s 6-part plan (`arxiv.md`): Part 2 (`Theorem88i.lean`) built a
`qChar`-gated primitive-recursive fold `myFoldCode` whose output, for *every* list-code `c`, is a
raw index `myFoldCode qChar cons c` satisfying `DiagFixed P a` (Part 1's r.e. diagonal predicate,
`↔ (fixedNbhd a).mem (P.X ·)`). This file packages that enumeration and shows it is exactly onto
`fixedNbhd a`.

`D_X qChar cons c := P.X (myFoldCode qChar cons c)`:

* **`D_X_mem`** — every `D_X qChar cons c` is a `fixedNbhd a`-neighbourhood: immediate from Part 2's
  invariant `diagFixed_myFoldCode` via `diagFixed_iff_fixedNbhd_mem`.
* **`D_X_of_diagFixed`** — the reusable core of the surjectivity argument: for *any* raw `V`-index
  `m` already known to be `DiagFixed` (not necessarily `myFoldCode`'s own output), some `D_X` value
  hits `P.X m` on the nose. Part 1's `hqChar` extracts a witness `i` with `qChar ⟨i, m⟩ = 1`.
  Feeding the **singleton list `[⟨i, m⟩]`** (encoded via `encodeList`) into the fold performs
  exactly one step from `P.masterIdx`: the `qChar`-gate passes by construction, and the
  `V`-consistency gate passes because `P.X m ⊆ V.master = P.X P.masterIdx` (`V.sub_master`) makes
  `P.masterIdx`/`m` trivially consistent via the witness `m` itself (`P.X m ⊆ P.X P.masterIdx ∩
  P.X m`, in fact equality). The fold therefore advances to `P.inter P.masterIdx m`, and
  `P.inter_spec` gives `P.X (P.inter P.masterIdx m) = V.master ∩ P.X m = P.X m`.
* **`D_X_surj`** — every `fixedNbhd a`-neighbourhood `Y` is hit by some `D_X qChar cons c`:
  `P.surj` produces a raw `V`-index `n₀` with `P.X n₀ = Y`, which is `DiagFixed` since `Y` is
  `a`-fixed, so `D_X_of_diagFixed` finishes it. (This reduction is also exactly what Theorem
  8.8(c) Part 4 needs for its `cons_computable` direction `⟸`, applied instead to `m := P.inter
  n₁ n₂` — hence factoring `D_X_of_diagFixed` out here rather than inlining it.)

Everything here is **choice-free** (`⊆ {propext, Quot.sound}`), built purely from `Theorem88h.lean`/
`Theorem88i.lean`'s choice-free apparatus plus `Recursive.lean`'s choice-free `encodeList`/
`decodeList` round-trip.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)

/-- **The enumeration induced by the `qChar`-gated fold**: `D_X c` reads off the `V`-neighbourhood
presented at the fold's output raw index. -/
def D_X (c : ℕ) : Set α := P.X (myFoldCode P qChar cons c)

variable {P qChar cons}

/-- **Theorem 8.8(c), Part 3 of 6, first half.** Every `D_X qChar cons c` is a `fixedNbhd
a`-neighbourhood — Part 2's invariant `diagFixed_myFoldCode`, repackaged via
`diagFixed_iff_fixedNbhd_mem`. -/
theorem D_X_mem {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (c : ℕ) :
    (fixedNbhd a).mem (D_X P qChar cons c) :=
  (diagFixed_iff_fixedNbhd_mem P a _).mp (diagFixed_myFoldCode P qChar cons hqChar hcons c)

/-- **The reusable core of the surjectivity argument.** Any `V`-neighbourhood `P.X m` already
known to be `DiagFixed` (regardless of whether `m` itself is `myFoldCode`'s output) is `D_X qChar
cons c` for some list-code `c`: the singleton-list code witnessing `m` together with Part 1's
`qChar`-witness for it. -/
theorem D_X_of_diagFixed {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m)
    {m : ℕ} (hm : DiagFixed P a m) : ∃ c, D_X P qChar cons c = P.X m := by
  obtain ⟨i, hi⟩ := (hqChar m).mp hm
  refine ⟨encodeList [Nat.pair i m], ?_⟩
  have hstep : myFoldCode P qChar cons (encodeList [Nat.pair i m])
      = myStep P qChar cons P.masterIdx (Nat.pair i m) := by
    rw [myFoldCode_eq, decodeList_encodeList]
    unfold myFold
    rw [List.foldl_cons, List.foldl_nil]
  have hcond : cons (Nat.pair P.masterIdx m) = 1 := by
    apply (hcons P.masterIdx m).mpr
    refine ⟨m, ?_⟩
    have hsub : P.X m ⊆ V.master := V.sub_master (P.mem_X m)
    rw [P.masterIdx_spec]
    exact Set.subset_inter hsub subset_rfl
  have hstepval : myStep P qChar cons P.masterIdx (Nat.pair i m)
      = P.inter P.masterIdx m := by
    unfold myStep
    simp only [unpair_pair_snd]
    rw [(isOne_eq_one_iff _).mpr hi, (isOne_eq_one_iff _).mpr hcond, Nat.one_mul, selectFn_one]
  show D_X P qChar cons (encodeList [Nat.pair i m]) = P.X m
  unfold D_X
  rw [hstep, hstepval]
  have hcons' : (∃ k, P.X k ⊆ P.X P.masterIdx ∩ P.X m) := (hcons P.masterIdx m).mp hcond
  rw [P.inter_spec hcons', P.masterIdx_spec, Set.inter_eq_right.mpr (V.sub_master (P.mem_X m))]

/-- **Theorem 8.8(c), Part 3 of 6, second half.** Every `fixedNbhd a`-neighbourhood `Y` is
`D_X qChar cons c` for some list-code `c`: `P.surj` finds `Y`'s raw `V`-index, which is `DiagFixed`
since `Y` is `a`-fixed, and `D_X_of_diagFixed` finishes it. -/
theorem D_X_surj {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m)
    {Y : Set α} (hY : (fixedNbhd a).mem Y) : ∃ c, D_X P qChar cons c = Y := by
  obtain ⟨hYV, hYa⟩ := hY
  obtain ⟨n₀, hn₀⟩ := P.surj hYV
  have hdiag : DiagFixed P a n₀ := by unfold DiagFixed; rw [hn₀]; exact hYa
  obtain ⟨c, hc⟩ := D_X_of_diagFixed hqChar hcons hdiag
  exact ⟨c, by rw [hc, hn₀]⟩

end Scott1980.Neighborhood

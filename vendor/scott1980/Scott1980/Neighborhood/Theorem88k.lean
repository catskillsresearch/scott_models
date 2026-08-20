/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Theorem88j

/-!
# Theorem 8.8(c), Part 4 of 6 — `D_X`'s `interEq`/`cons` relations are recursively decidable

Following Theorem 8.8(c)'s 6-part plan (`arxiv.md`): Part 3 (`Theorem88j.lean`) built the
enumeration `D_X qChar cons c := P.X (myFoldCode qChar cons c)` and showed it is onto `fixedNbhd
a`. This file proves the two relations Definition 7.1 actually needs are recursively decidable
*on the list-codes* `c` (not on the underlying `V`-indices, which are already handled by `P`).

## `interEq_computable` — free

`D_X c₁ ∩ D_X c₂ = D_X c₃` unfolds *literally* to `P.X n₁ ∩ P.X n₂ = P.X n₃` for `nᵢ := myFoldCode
qChar cons cᵢ`, so this is exactly `P.interEq_computable` reindexed along the (primitive-recursive,
Part 2's `primrec_myFoldCode`) triple `(c₁,c₂,c₃) ↦ (myFoldCode c₁, myFoldCode c₂, myFoldCode c₃)`.
No `a`/`DiagFixed` apparatus is needed at all.

## `cons_computable` — the one genuine lemma

`D_X_cons_iff` is the mathematical content of this part: `D`-consistency of two list-codes,
`∃ k, D_X k ⊆ D_X c₁ ∩ D_X c₂`, is **equivalent** to plain `V`-consistency of the underlying raw
indices, `∃ k', P.X k' ⊆ P.X n₁ ∩ P.X n₂`:

* `⟹` is immediate: any `D`-side witness `D_X k = P.X (myFoldCode qChar cons k)` is *already* a
  `V`-side witness, since `D_X`'s codomain is literally `P.X` of some raw index — no separate
  "is this really `V`-consistent" check is needed.
* `⟸` needs Theorem 8.8(c) Part 3's `D_X_of_diagFixed`: given a `V`-consistency witness `k'`,
  `P.inter_spec` gives `P.X (P.inter n₁ n₂) = P.X n₁ ∩ P.X n₂`; since `n₁`, `n₂` are both
  `DiagFixed` (Part 2's `diagFixed_myFoldCode`, as they are `myFoldCode`-outputs), so is their
  meet (`fixedNbhd_subsystem a`'s `inter_closed`, transported along the equation above), and
  `D_X_of_diagFixed` then produces the `D`-side witness code directly.

Once this equivalence is in hand, `cons_computable` is `P.cons_computable` composed with the same
primitive-recursive `myFoldCode`-pair reindex used for `interEq_computable`.

Everything here is **choice-free** (`⊆ {propext, Quot.sound}`), built purely from `Theorem88h.lean`–
`Theorem88j.lean`'s choice-free apparatus plus `Definition71.lean`'s choice-free `RecDecidable`
closure lemmas (`comp`/`of_iff`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)

variable {P qChar cons}

/-- **The one genuine lemma of Theorem 8.8(c), Part 4 of 6.** `D`-consistency of two list-codes
(`∃ k, D_X k ⊆ D_X c₁ ∩ D_X c₂`) is equivalent to plain `V`-consistency of the underlying raw
`myFoldCode` indices. -/
theorem D_X_cons_iff {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (c₁ c₂ : ℕ) :
    (∃ k, D_X P qChar cons k ⊆ D_X P qChar cons c₁ ∩ D_X P qChar cons c₂) ↔
      (∃ k, P.X k ⊆ P.X (myFoldCode P qChar cons c₁) ∩ P.X (myFoldCode P qChar cons c₂)) := by
  set n₁ := myFoldCode P qChar cons c₁ with hn₁
  set n₂ := myFoldCode P qChar cons c₂ with hn₂
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨myFoldCode P qChar cons k, hk⟩
  · rintro ⟨k, hk⟩
    have hn1 : DiagFixed P a n₁ := diagFixed_myFoldCode P qChar cons hqChar hcons c₁
    have hn2 : DiagFixed P a n₂ := diagFixed_myFoldCode P qChar cons hqChar hcons c₂
    have hVmem : V.mem (P.X n₁ ∩ P.X n₂) := by
      rw [← P.inter_spec ⟨k, hk⟩]; exact P.mem_X _
    have hfix : (fixedNbhd a).mem (P.X n₁ ∩ P.X n₂) :=
      (fixedNbhd_subsystem a).inter_closed ((diagFixed_iff_fixedNbhd_mem P a n₁).mp hn1)
        ((diagFixed_iff_fixedNbhd_mem P a n₂).mp hn2) hVmem
    have hm : DiagFixed P a (P.inter n₁ n₂) := by
      rw [diagFixed_iff_fixedNbhd_mem, P.inter_spec ⟨k, hk⟩]; exact hfix
    obtain ⟨c, hc⟩ := D_X_of_diagFixed hqChar hcons hm
    have heq : D_X P qChar cons c = D_X P qChar cons c₁ ∩ D_X P qChar cons c₂ := by
      rw [hc, P.inter_spec ⟨k, hk⟩]
      unfold D_X
      rw [← hn₁, ← hn₂]
    exact ⟨c, heq ▸ subset_rfl⟩

variable (P qChar cons)

/-- **Theorem 8.8(c), Part 4 of 6, first half (`interEq_computable`, free).** `D_X c₁ ∩ D_X c₂ =
D_X c₃` is exactly `P.interEq_computable` reindexed along the primitive-recursive triple
`myFoldCode`. -/
theorem D_X_interEq_computable (hqCharp : Nat.Primrec qChar) (hconsp : Nat.Primrec cons) :
    RecDecidable₃ (fun c₁ c₂ c₃ =>
      D_X P qChar cons c₁ ∩ D_X P qChar cons c₂ = D_X P qChar cons c₃) := by
  have hmf : Nat.Primrec (myFoldCode P qChar cons) := primrec_myFoldCode P qChar cons hqCharp hconsp
  have hreindex : Nat.Primrec (fun t : ℕ =>
      Nat.pair (myFoldCode P qChar cons t.unpair.1)
        (Nat.pair (myFoldCode P qChar cons t.unpair.2.unpair.1)
          (myFoldCode P qChar cons t.unpair.2.unpair.2))) :=
    (hmf.comp Nat.Primrec.left).pair
      ((hmf.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
        (hmf.comp (Nat.Primrec.right.comp Nat.Primrec.right)))
  refine RecDecidable.of_iff (fun t => ?_) (P.interEq_computable.comp hreindex)
  unfold D_X
  simp only [unpair_pair_fst, unpair_pair_snd]

/-- **Theorem 8.8(c), Part 4 of 6, second half (`cons_computable`).** `D_X`-consistency is
`P.cons_computable` composed with the same primitive-recursive `myFoldCode`-pair reindex, via the
equivalence `D_X_cons_iff`. -/
theorem D_X_cons_computable {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m)
    (hqCharp : Nat.Primrec qChar) (hconsp : Nat.Primrec cons) :
    RecDecidable₂ (fun c₁ c₂ =>
      ∃ k, D_X P qChar cons k ⊆ D_X P qChar cons c₁ ∩ D_X P qChar cons c₂) := by
  have hmf : Nat.Primrec (myFoldCode P qChar cons) := primrec_myFoldCode P qChar cons hqCharp hconsp
  have hreindex : Nat.Primrec (fun t : ℕ =>
      Nat.pair (myFoldCode P qChar cons t.unpair.1) (myFoldCode P qChar cons t.unpair.2)) :=
    (hmf.comp Nat.Primrec.left).pair (hmf.comp Nat.Primrec.right)
  refine RecDecidable.of_iff (fun t => ?_) (P.cons_computable.comp hreindex)
  simp only [unpair_pair_fst, unpair_pair_snd]
  exact D_X_cons_iff hqChar hcons t.unpair.1 t.unpair.2

end Scott1980.Neighborhood

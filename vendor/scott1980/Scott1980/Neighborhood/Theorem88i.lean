/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Theorem88h

/-!
# Theorem 8.8(c), Part 2 of 6 — a `qChar`-gated primitive-recursive fold landing back in `DiagFixed`

Following Theorem 8.8(c)'s 6-part plan (`arxiv.md`): Part 1 (`Theorem88h.lean`) produced, from a
computable map `a`, a `{0,1}`-valued primitive-recursive `qChar` with `DiagFixed P a n ↔ ∃i,
qChar⟨i,n⟩ = 1`. This file builds the **fold** that will let Part 3 enumerate `fixedNbhd a`: a
primitive-recursive list-fold whose accumulator is *always* a raw index already satisfying
`DiagFixed`, no matter what list it is fed — so no unbounded search is ever needed once `qChar` (an
r.e., not decidable, fact) has been supplied per list entry as a *checked* witness pair.

## Design (mirroring `DAtomDecidable.lean`'s `meetStep`/`meetFold`/`meetFoldCode`, simplified)

Each list entry `e` codes a pair `⟨i, n⟩ = Nat.pair i n`: `n` is a candidate raw index and `i` is a
*claimed* `qChar`-witness for it. One step of the fold (`myStep`), given the current accumulator `r`
(already known — by the invariant — to satisfy `DiagFixed`) and the next entry `e`:

* checks `qChar e = 1` (this literally checks `qChar (Nat.pair i n) = 1`, so — reading `hqChar`
  backwards — witnesses `DiagFixed P a n` for `n := e.unpair.2`, no unbounded search needed since the
  witness `i` was *given*, not searched for);
* checks the `V`-consistency decider `cons (Nat.pair r n) = 1` (i.e. `∃k, X k ⊆ Xᵣ ∩ Xₙ`);
* if **both** succeed, advances the accumulator to `P.inter r n` (which lands back in `DiagFixed` by
  `fixedNbhd_subsystem`'s `inter_closed`, since `Xᵣ ∩ Xₙ` is then both a genuine `V`-neighbourhood
  *and* an intersection of two `fixedNbhd a`-neighbourhoods);
* otherwise **no-ops**, leaving the accumulator at `r` unchanged (unlike `meetStep`'s permanent
  "not ok" freeze — here an invalid or inconsistent entry is simply *skipped*, since we are not
  trying to prove anything about the *particular* list fed in, only that whatever comes out the other
  end is still `DiagFixed`).

The base case is `P.masterIdx`, always `DiagFixed` since `a.master_rel : a.rel V.master V.master`
transported along `P.masterIdx_spec`. No `(ok, idx)` pair is needed in the accumulator (unlike
`meetStep`) precisely because a bad entry is dropped rather than remembered.

`myStepCode`/`myFoldCode` package `myStep`/`myFold` at the `Nat.Primrec` level via the existing
`foldCode` combinator (`Recursive.lean`); `Nat.Primrec` is immediate from `primrec_foldCode` given
`qChar`, `cons`, and `P.inter` are all primitive recursive. The headline result,
`diagFixed_myFoldCode`, is the invariant "`DiagFixed P a (myFoldCode qChar cons c)` for every list-code
`c`" — Part 3 will show this enumeration is *onto* `fixedNbhd a`.

Everything here is **choice-free** (`⊆ {propext, Quot.sound}`), built purely from `Recursive.lean`'s
choice-free `foldCode`/`selectFn`/`isOne` machinery and `Theorem85.lean`'s choice-free
`fixedNbhd_subsystem`.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α} (P : ComputablePresentation V)
  (qChar cons : ℕ → ℕ)

/-! ### The fold, at the `Set`/`List` level -/

/-- **One step of the `qChar`-gated fold.** The accumulator `r` is a raw index (no `(ok,idx)` pair
needed); `e` codes the next list entry `⟨i, n⟩ = Nat.pair i n`. If `qChar e = 1` (a checked
`qChar`-witness for `n := e.unpair.2`) *and* `cons (Nat.pair r n) = 1` (`r`, `n` are `V`-consistent),
advance to `P.inter r n`; otherwise no-op (skip this entry). -/
def myStep (r e : ℕ) : ℕ :=
  selectFn (isOne (qChar e) * isOne (cons (Nat.pair r e.unpair.2)))
    (P.inter r e.unpair.2) r

/-- **The `qChar`-gated fold**, starting from `P.masterIdx`. -/
def myFold (l : List ℕ) : ℕ := l.foldl (myStep P qChar cons) P.masterIdx

@[simp] theorem myFold_nil : myFold P qChar cons [] = P.masterIdx := rfl

theorem myFold_cons (e : ℕ) (rest : List ℕ) :
    myFold P qChar cons (e :: rest) = rest.foldl (myStep P qChar cons) (myStep P qChar cons P.masterIdx e) := by
  unfold myFold; rw [List.foldl_cons]

variable {P qChar cons}

/-- **The base case: `P.masterIdx` is always `DiagFixed`.** `P.X P.masterIdx = V.master`
(`masterIdx_spec`), and `a.rel V.master V.master` holds for every approximable map (`master_rel`). -/
theorem diagFixed_masterIdx (a : ApproximableMap V V) : DiagFixed P a P.masterIdx := by
  show a.rel (P.X P.masterIdx) (P.X P.masterIdx)
  rw [P.masterIdx_spec]
  exact a.master_rel

/-- **One-step preservation of `DiagFixed`.** If the accumulator `r` is already `DiagFixed` and
`e`'s gate succeeds (`qChar e = 1` giving `DiagFixed` of the raw index `e.unpair.2` via `hqChar`, and
`cons (Nat.pair r e.unpair.2) = 1` giving a `V`-consistency witness), then `myStep P qChar cons r e`
is `DiagFixed` too — via `fixedNbhd_subsystem a`'s `inter_closed` plus `P.inter_spec`. If the gate
fails, the step no-ops and the invariant is preserved trivially. -/
theorem myStep_diagFixed_of_diagFixed {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m)
    {r : ℕ} (hr : DiagFixed P a r) (e : ℕ) :
    DiagFixed P a (myStep P qChar cons r e) := by
  unfold myStep
  rcases Nat.decEq (qChar e) 1 with hq | hq
  · rw [isOne_of_ne_one hq, Nat.zero_mul, selectFn_zero]
    exact hr
  · rw [(isOne_eq_one_iff _).mpr hq, Nat.one_mul]
    rcases Nat.decEq (cons (Nat.pair r e.unpair.2)) 1 with hc | hc
    · rw [isOne_of_ne_one hc, selectFn_zero]
      exact hr
    · rw [(isOne_eq_one_iff _).mpr hc, selectFn_one]
      have hn : DiagFixed P a e.unpair.2 :=
        (hqChar e.unpair.2).mpr ⟨e.unpair.1, by rw [pair_unpair]; exact hq⟩
      obtain ⟨k, hk⟩ := (hcons r e.unpair.2).mp hc
      have hVinter : V.mem (P.X r ∩ P.X e.unpair.2) := by
        rw [← P.inter_spec ⟨k, hk⟩]; exact P.mem_X _
      have hfix : (fixedNbhd a).mem (P.X r ∩ P.X e.unpair.2) :=
        (fixedNbhd_subsystem a).inter_closed ((diagFixed_iff_fixedNbhd_mem P a r).mp hr)
          ((diagFixed_iff_fixedNbhd_mem P a e.unpair.2).mp hn) hVinter
      rw [diagFixed_iff_fixedNbhd_mem, P.inter_spec ⟨k, hk⟩]
      exact hfix

/-- **The fold invariant, over an arbitrary starting accumulator.** -/
theorem myFold_diagFixed_of_diagFixed {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (l : List ℕ) :
    ∀ {r : ℕ}, DiagFixed P a r → DiagFixed P a (l.foldl (myStep P qChar cons) r) := by
  induction l with
  | nil => intro r hr; simpa using hr
  | cons e rest ih =>
    intro r hr
    rw [List.foldl_cons]
    exact ih (myStep_diagFixed_of_diagFixed hqChar hcons hr e)

/-- **Correctness of the `qChar`-gated fold, instantiated at the real starting point
`P.masterIdx`.** -/
theorem myFold_diagFixed {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (l : List ℕ) :
    DiagFixed P a (myFold P qChar cons l) :=
  myFold_diagFixed_of_diagFixed hqChar hcons l (diagFixed_masterIdx a)

variable (P qChar cons)

/-! ### Code-level `myFold`, and its primitive recursivity -/

/-- `foldCode`-shaped step matching `myStep`: state `w = pair e (pair r params)` (`params`
unused). -/
def myStepCode (w : ℕ) : ℕ := myStep P qChar cons w.unpair.2.unpair.1 w.unpair.1

/-- The code-level `qChar`-gated fold. -/
def myFoldCode (c : ℕ) : ℕ := foldCode (myStepCode P qChar cons) 0 P.masterIdx c

theorem myFoldCode_eq (c : ℕ) : myFoldCode P qChar cons c = myFold P qChar cons (decodeList c) := by
  have hfun : (fun (acc x : ℕ) => myStepCode P qChar cons (Nat.pair x (Nat.pair acc 0)))
      = myStep P qChar cons := by
    funext acc x
    unfold myStepCode
    simp only [unpair_pair_fst, unpair_pair_snd]
  unfold myFoldCode myFold
  rw [foldCode_eq', hfun]

theorem primrec_myStepCode (hqCharp : Nat.Primrec qChar) (hconsp : Nat.Primrec cons) :
    Nat.Primrec (myStepCode P qChar cons) := by
  have he : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hr : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have he2 : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.2) := Nat.Primrec.right.comp he
  have hargs : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.2.unpair.1 w.unpair.1.unpair.2) :=
    hr.pair he2
  have hqchar_e : Nat.Primrec (fun w : ℕ => qChar w.unpair.1) := hqCharp.comp he
  have hcons_val : Nat.Primrec
      (fun w : ℕ => cons (Nat.pair w.unpair.2.unpair.1 w.unpair.1.unpair.2)) :=
    hconsp.comp hargs
  have hcond : Nat.Primrec (fun w : ℕ =>
      isOne (qChar w.unpair.1) * isOne (cons (Nat.pair w.unpair.2.unpair.1 w.unpair.1.unpair.2))) :=
    primrec_mul₂ (primrec_isOne.comp hqchar_e) (primrec_isOne.comp hcons_val)
  have hinter : Nat.Primrec
      (fun w : ℕ => P.inter w.unpair.2.unpair.1 w.unpair.1.unpair.2) :=
    (P.inter_primrec.comp hargs).of_eq fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_selectFn hcond hinter hr).of_eq fun _ => rfl

/-- **`myFoldCode` is primitive recursive** (Part 2's headline `Nat.Primrec` claim). -/
theorem primrec_myFoldCode (hqCharp : Nat.Primrec qChar) (hconsp : Nat.Primrec cons) :
    Nat.Primrec (myFoldCode P qChar cons) :=
  (primrec_foldCode (primrec_myStepCode P qChar cons hqCharp hconsp)
    (Nat.Primrec.const 0) (Nat.Primrec.const P.masterIdx) primrec_id).of_eq
    fun _ => rfl

/-- **Theorem 8.8(c), Part 2 of 6, headline invariant.** `myFoldCode qChar cons c` is `DiagFixed`
for *every* list-code `c` — no matter what garbage `c` decodes to, the fold only ever advances past
checked (`qChar`-witnessed, `V`-consistent) steps, so the output always lands back inside
`fixedNbhd a`. -/
theorem diagFixed_myFoldCode {a : ApproximableMap V V}
    (hqChar : ∀ n, DiagFixed P a n ↔ ∃ i, qChar (Nat.pair i n) = 1)
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m) (c : ℕ) :
    DiagFixed P a (myFoldCode P qChar cons c) := by
  rw [myFoldCode_eq]
  exact myFold_diagFixed hqChar hcons (decodeList c)

end Scott1980.Neighborhood

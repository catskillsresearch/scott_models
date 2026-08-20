/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Recursive

/-!
# A choice-free primitive-recursive "cross-combine" of two coded lists

`Definition87.lean`'s `combineIntervals L1 L2 := L1.flatMap (fun p => L2.map (fun q => bop p q))`
needs a code-level analogue: given two `List ℕ` codes `c1, c2` (`Recursive.lean`'s `encodeList`
convention) and a primitive-recursive binary operation `bop`, produce the code of the list of all
`bop x y` for `x` ranging over `c1`'s list and `y` over `c2`'s list.

This extends `Recursive.lean`'s existing two-combinator toolkit (`mapPairCode`, itself built from
`foldCode`) with a genuine **nested** fold: an outer fold over `c1` whose accumulator at each step
is extended by an *inner* fold over `c2` (via `appendCode`, list concatenation on codes). Since the
downstream use (`combineIntervals`, realizing set unions) never cares about list order or
duplicates, correctness is stated at the level of list **membership**, not exact list equality —
this sidesteps tracking the reversals `foldCode`'s left-to-right consing introduces.

Everything here is `⊆ {propext, Quot.sound}`.
-/

namespace Domain.Recursive

/-! ### `appendCode`: concatenation of two coded lists (up to order) -/

/-- `foldCode`'s step for consing the popped element `x` onto the accumulator (ignoring the
threaded parameter). -/
def consStep2 (w : ℕ) : ℕ := Nat.pair w.unpair.1 w.unpair.2.unpair.1 + 1

theorem primrec_consStep2 : Nat.Primrec consStep2 := by
  have h1 : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have h21 : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  exact (Nat.Primrec.succ.comp (h1.pair h21)).of_eq fun _ => rfl

/-- `appendCode c1 c2` codes a list with the same **elements** as `decodeList c1 ++ decodeList c2`
(reversed on the `c1` side, since `foldCode` conses left-to-right; irrelevant for set-level uses). -/
def appendCode (c1 c2 : ℕ) : ℕ := foldCode consStep2 0 c2 c1

theorem primrec_appendCode : Nat.Primrec (fun t => appendCode t.unpair.1 t.unpair.2) :=
  (primrec_foldCode primrec_consStep2 (Nat.Primrec.const 0) Nat.Primrec.right
    Nat.Primrec.left).of_eq fun _ => rfl

theorem consStep2_eq (x acc params : ℕ) :
    consStep2 (Nat.pair x (Nat.pair acc params)) = Nat.pair x acc + 1 := by
  unfold consStep2; simp only [unpair_pair_fst, unpair_pair_snd]

private theorem mem_decodeList_appendCode_aux :
    ∀ (l : List ℕ) (acc z : ℕ),
      z ∈ decodeList (List.foldl (fun acc x => consStep2 (Nat.pair x (Nat.pair acc 0))) acc l)
        ↔ z ∈ l ∨ z ∈ decodeList acc
  | [], acc, z => by simp
  | a :: l, acc, z => by
    rw [List.foldl_cons, consStep2_eq, mem_decodeList_appendCode_aux l (Nat.pair a acc + 1) z,
      decodeList_succ, unpair_pair_fst, unpair_pair_snd]
    simp only [List.mem_cons]
    constructor
    · rintro (hl | (rfl | hacc))
      · exact Or.inl (Or.inr hl)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr hacc
    · rintro ((rfl | hl) | hacc)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl hl
      · exact Or.inr (Or.inr hacc)

theorem mem_decodeList_appendCode (c1 c2 z : ℕ) :
    z ∈ decodeList (appendCode c1 c2) ↔ z ∈ decodeList c1 ∨ z ∈ decodeList c2 := by
  unfold appendCode
  rw [foldCode_eq', mem_decodeList_appendCode_aux (decodeList c1) c2 z]

/-! ### `crossInner`: `bop x` mapped over a coded list -/

/-- `foldCode`'s step for the inner loop: pops `y` from `c2`, applies `bop (pair x y)` (`x` threaded
as the fixed parameter), conses onto the accumulator. -/
def crossInnerStep (bop : ℕ → ℕ) (w : ℕ) : ℕ :=
  Nat.pair (bop (Nat.pair w.unpair.2.unpair.2 w.unpair.1)) w.unpair.2.unpair.1 + 1

theorem primrec_crossInnerStep {bop : ℕ → ℕ} (hbop : Nat.Primrec bop) :
    Nat.Primrec (crossInnerStep bop) := by
  have hy : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact (Nat.Primrec.succ.comp ((hbop.comp (hx.pair hy)).pair hacc)).of_eq fun _ => rfl

/-- `crossInner bop x c2` codes `[bop (x, y) ∣ y ∈ decodeList c2]` (up to order). -/
def crossInner (bop : ℕ → ℕ) (x c2 : ℕ) : ℕ := foldCode (crossInnerStep bop) x 0 c2

theorem primrec_crossInner {bop : ℕ → ℕ} (hbop : Nat.Primrec bop) :
    Nat.Primrec (fun t => crossInner bop t.unpair.1 t.unpair.2) :=
  (primrec_foldCode (primrec_crossInnerStep hbop) Nat.Primrec.left (Nat.Primrec.const 0)
    Nat.Primrec.right).of_eq fun _ => rfl

theorem crossInnerStep_eq (bop : ℕ → ℕ) (y acc x : ℕ) :
    crossInnerStep bop (Nat.pair y (Nat.pair acc x)) = Nat.pair (bop (Nat.pair x y)) acc + 1 := by
  unfold crossInnerStep; simp only [unpair_pair_fst, unpair_pair_snd]

private theorem mem_decodeList_crossInner_aux (bop : ℕ → ℕ) (x : ℕ) :
    ∀ (l : List ℕ) (acc z : ℕ),
      z ∈ decodeList
          (List.foldl (fun acc y => crossInnerStep bop (Nat.pair y (Nat.pair acc x))) acc l)
        ↔ (∃ y ∈ l, z = bop (Nat.pair x y)) ∨ z ∈ decodeList acc
  | [], acc, z => by simp
  | a :: l, acc, z => by
    rw [List.foldl_cons, crossInnerStep_eq,
      mem_decodeList_crossInner_aux bop x l (Nat.pair (bop (Nat.pair x a)) acc + 1) z,
      decodeList_succ, unpair_pair_fst, unpair_pair_snd]
    simp only [List.mem_cons]
    constructor
    · rintro (⟨y, hy, heq⟩ | (rfl | hacc))
      · exact Or.inl ⟨y, Or.inr hy, heq⟩
      · exact Or.inl ⟨a, Or.inl rfl, rfl⟩
      · exact Or.inr hacc
    · rintro (⟨y, (rfl | hy), heq⟩ | hacc)
      · exact Or.inr (Or.inl heq)
      · exact Or.inl ⟨y, hy, heq⟩
      · exact Or.inr (Or.inr hacc)

theorem mem_decodeList_crossInner {bop : ℕ → ℕ} (x c2 z : ℕ) :
    z ∈ decodeList (crossInner bop x c2) ↔ ∃ y ∈ decodeList c2, z = bop (Nat.pair x y) := by
  unfold crossInner
  rw [foldCode_eq', mem_decodeList_crossInner_aux bop x (decodeList c2) 0 z]
  simp only [decodeList_zero, List.not_mem_nil, or_false]

/-! ### `crossCombine`: the full nested fold -/

/-- `foldCode`'s outer step: pops `x` from `c1`, appends `crossInner bop x c2` onto the
accumulator (`c2` threaded as the fixed parameter). -/
def crossOuterStep (bop : ℕ → ℕ) (w : ℕ) : ℕ :=
  appendCode (crossInner bop w.unpair.1 w.unpair.2.unpair.2) w.unpair.2.unpair.1

theorem primrec_crossOuterStep {bop : ℕ → ℕ} (hbop : Nat.Primrec bop) :
    Nat.Primrec (crossOuterStep bop) := by
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hc2 : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hinner : Nat.Primrec (fun w : ℕ => crossInner bop w.unpair.1 w.unpair.2.unpair.2) :=
    ((primrec_crossInner hbop).comp (hx.pair hc2)).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_appendCode.comp (hinner.pair hacc)).of_eq fun w => by
    unfold crossOuterStep
    simp only [unpair_pair_fst, unpair_pair_snd]

/-- **`crossCombine bop c1 c2`** codes `[bop (x, y) ∣ x ∈ decodeList c1, y ∈ decodeList c2]`
(up to order/duplicates), i.e. the code-level analogue of `L1.flatMap (fun x => L2.map (bop x ·))`.
This is the workhorse behind `Definition87.lean`'s `combineIntervals` at the code level. -/
def crossCombine (bop : ℕ → ℕ) (c1 c2 : ℕ) : ℕ := foldCode (crossOuterStep bop) c2 0 c1

theorem primrec_crossCombine {bop : ℕ → ℕ} (hbop : Nat.Primrec bop) :
    Nat.Primrec (fun t => crossCombine bop t.unpair.1 t.unpair.2) :=
  (primrec_foldCode (primrec_crossOuterStep hbop) Nat.Primrec.right (Nat.Primrec.const 0)
    Nat.Primrec.left).of_eq fun _ => rfl

theorem crossOuterStep_eq (bop : ℕ → ℕ) (x acc c2 : ℕ) :
    crossOuterStep bop (Nat.pair x (Nat.pair acc c2)) = appendCode (crossInner bop x c2) acc := by
  unfold crossOuterStep; simp only [unpair_pair_fst, unpair_pair_snd]

private theorem mem_decodeList_crossCombine_aux (bop : ℕ → ℕ) (c2 : ℕ) :
    ∀ (l : List ℕ) (acc z : ℕ),
      z ∈ decodeList (List.foldl (fun acc x => crossOuterStep bop (Nat.pair x (Nat.pair acc c2)))
          acc l)
        ↔ (∃ x ∈ l, ∃ y ∈ decodeList c2, z = bop (Nat.pair x y)) ∨ z ∈ decodeList acc
  | [], acc, z => by simp
  | a :: l, acc, z => by
    rw [List.foldl_cons, crossOuterStep_eq,
      mem_decodeList_crossCombine_aux bop c2 l (appendCode (crossInner bop a c2) acc) z,
      mem_decodeList_appendCode, mem_decodeList_crossInner]
    simp only [List.mem_cons]
    constructor
    · rintro (⟨x, hx, y, hy, heq⟩ | (⟨y, hy, heq⟩ | hacc))
      · exact Or.inl ⟨x, Or.inr hx, y, hy, heq⟩
      · exact Or.inl ⟨a, Or.inl rfl, y, hy, heq⟩
      · exact Or.inr hacc
    · rintro (⟨x, (rfl | hx), y, hy, heq⟩ | hacc)
      · exact Or.inr (Or.inl ⟨y, hy, heq⟩)
      · exact Or.inl ⟨x, hx, y, hy, heq⟩
      · exact Or.inr (Or.inr hacc)

theorem mem_decodeList_crossCombine {bop : ℕ → ℕ} (c1 c2 z : ℕ) :
    z ∈ decodeList (crossCombine bop c1 c2) ↔
      ∃ x ∈ decodeList c1, ∃ y ∈ decodeList c2, z = bop (Nat.pair x y) := by
  unfold crossCombine
  rw [foldCode_eq', mem_decodeList_crossCombine_aux bop c2 (decodeList c1) 0 z]
  simp only [decodeList_zero, List.not_mem_nil, or_false]

/-! ### `flatMapCode`: `f x` (list-valued) flat-mapped over a coded list

Like `crossInner`, but the per-element operation `f` returns the *code of a list* to be
**appended** (`appendCode`) onto the accumulator, rather than a single value to be *consed* — the
code-level analogue of `l.flatMap (fun y => decodeList (f x y))`. This is the piece
`Theorem88b`'s interval-*difference* needs: subtracting a whole interval-list from a single
interval can produce `0`, `1`, or `2` result-pieces per step, so the per-element result is itself
list-valued. -/

/-- `foldCode`'s step for `flatMapCode`: pops `y` from the folded list, appends `f (pair x y)`
(`x` threaded as the fixed parameter) onto the accumulator. -/
def flatMapStep (f : ℕ → ℕ) (w : ℕ) : ℕ :=
  appendCode (f (Nat.pair w.unpair.2.unpair.2 w.unpair.1)) w.unpair.2.unpair.1

theorem primrec_flatMapStep {f : ℕ → ℕ} (hf : Nat.Primrec f) : Nat.Primrec (flatMapStep f) := by
  have hy : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact (primrec_appendCode.comp ((hf.comp (hx.pair hy)).pair hacc)).of_eq fun w => by
    unfold flatMapStep; simp only [unpair_pair_fst, unpair_pair_snd]

/-- **`flatMapCode f x c`** codes `(decodeList c).flatMap (fun y => decodeList (f (pair x y)))`
(up to order/duplicates). -/
def flatMapCode (f : ℕ → ℕ) (x c : ℕ) : ℕ := foldCode (flatMapStep f) x 0 c

theorem primrec_flatMapCode {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    Nat.Primrec (fun t => flatMapCode f t.unpair.1 t.unpair.2) :=
  (primrec_foldCode (primrec_flatMapStep hf) Nat.Primrec.left (Nat.Primrec.const 0)
    Nat.Primrec.right).of_eq fun _ => rfl

theorem flatMapStep_eq (f : ℕ → ℕ) (y acc x : ℕ) :
    flatMapStep f (Nat.pair y (Nat.pair acc x)) = appendCode (f (Nat.pair x y)) acc := by
  unfold flatMapStep; simp only [unpair_pair_fst, unpair_pair_snd]

private theorem mem_decodeList_flatMapCode_aux (f : ℕ → ℕ) (x : ℕ) :
    ∀ (l : List ℕ) (acc z : ℕ),
      z ∈ decodeList (List.foldl (fun acc y => flatMapStep f (Nat.pair y (Nat.pair acc x))) acc l)
        ↔ (∃ y ∈ l, z ∈ decodeList (f (Nat.pair x y))) ∨ z ∈ decodeList acc
  | [], acc, z => by simp
  | a :: l, acc, z => by
    rw [List.foldl_cons, flatMapStep_eq,
      mem_decodeList_flatMapCode_aux f x l (appendCode (f (Nat.pair x a)) acc) z,
      mem_decodeList_appendCode]
    simp only [List.mem_cons]
    constructor
    · rintro (⟨y, hy, hz⟩ | (hfa | hacc))
      · exact Or.inl ⟨y, Or.inr hy, hz⟩
      · exact Or.inl ⟨a, Or.inl rfl, hfa⟩
      · exact Or.inr hacc
    · rintro (⟨y, (rfl | hy), hz⟩ | hacc)
      · exact Or.inr (Or.inl hz)
      · exact Or.inl ⟨y, hy, hz⟩
      · exact Or.inr (Or.inr hacc)

theorem mem_decodeList_flatMapCode {f : ℕ → ℕ} (x c z : ℕ) :
    z ∈ decodeList (flatMapCode f x c) ↔ ∃ y ∈ decodeList c, z ∈ decodeList (f (Nat.pair x y)) := by
  unfold flatMapCode
  rw [foldCode_eq', mem_decodeList_flatMapCode_aux f x (decodeList c) 0 z]
  simp only [decodeList_zero, List.not_mem_nil, or_false]

end Domain.Recursive

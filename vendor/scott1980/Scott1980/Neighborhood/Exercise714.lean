/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Definition72

/-!
# Exercise 7.14 (Scott 1981, PRG-19, §7) — the r.e. facts after Definition 7.2

> **Exercise 7.14.** (For recursive-function theorists.) Prove the statements after definition 7.2
> about the existence of primitive recursive functions for showing things recursively enumerable.
> (Recall that a non-empty set is r.e. iff it is the range of a primitive recursive function.) Show
> also that every computable element `y ∈ |ℰ|` can be written
> `y = ⋃ {↑Y_{t(i)} ∣ i ∈ ℕ}`, where `t : ℕ → ℕ` is primitive recursive and where we may assume
> `Y_{t(i+1)} ⊆ Y_{t(i)}` for all `i ∈ ℕ`.

This exercise has two halves.

## Half 1 — "a non-empty set is r.e. iff it is the range of a primitive recursive function"

Scott's prose after Definition 7.2 reads: *"What it means to be recursively enumerable is that there
is a primitive recursive function (hence, a total function) `r : ℕ → ℕ` such that
`y = {Y_{r(i)} ∣ i ∈ ℕ}`"* and, for a computable map, *"`f = {(X_{s(i)}, Y_{r(i)}) ∣ i ∈ ℕ}` for a
suitable pair of primitive recursive functions `s` and `r`."* This is exactly the classical
characterization **non-empty r.e. set = range of a primitive recursive function**. Our choice-free
model of r.e. is `Domain.Recursive.REPred p := ∃ q, RecDecidable q ∧ ∀ n, p n ↔ ∃ i, q ⟨i,n⟩`
(projection of a recursively decidable relation), so we prove both directions against it:

* `repred_range_primrec` — the **range** of a primitive recursive `r` is r.e. (the relation
  `r i = n` is recursively decidable by `RecDecidable.natEq`, and `∃ i, r i = n` is its projection);
* `repred_exists_primrec_range` — every **non-empty** r.e. set is the range of a primitive recursive
  function. From a witness `a ∈ p` and the decider `qc` of the underlying relation, the function
  `r w := selectFn (isOne (qc w)) w.2 a` enumerates `p`: on a witnessing code `w = ⟨i,n⟩` (where
  `qc w = 1`) it returns `n`, and it falls back to the fixed `a ∈ p` otherwise, so its range is
  exactly `p`. (The fall-back `a` is precisely why *non-emptiness* is needed.)
* `repred₂_exists_primrec_enum` — the map form: a non-empty r.e. *relation* `p n m` is enumerated by
  a pair of primitive recursive functions `s, r` with `p n m ↔ ∃ i, s i = n ∧ r i = m` (split the
  range function of the `Nat.pair`-coded relation into its two projections). This is Scott's
  `f = {(X_{s(i)}, Y_{r(i)})}`.

## Half 2 — every computable element is a decreasing union of finite (principal) elements

`computableElement_eq_decreasing_iUnion_principal`: for a computable element `y` of an effectively
given `W` (`IsComputableElement Q y`, i.e. the index set `{m ∣ Yₘ ∈ y}` is r.e.), there is a
**primitive recursive** `t : ℕ → ℕ` with

* (decreasing)   `Q.X (t (i+1)) ⊆ Q.X (t i)` for all `i`;
* (union)        `y.mem Z ↔ ∃ i, (↑Y_{t(i)}).mem Z`, i.e. `y = ⋃ᵢ ↑Y_{t(i)}` (Factoid 1.7b form).

The index set is non-empty (it contains the master `Δ`, since every filter contains `Δ`), so Half 1
gives a primitive recursive enumeration `r₀` of all of `y`'s indices. To force the approximations to
*decrease*, we take running intersections: `t 0 = r₀ 0`, `t (i+1) = inter (t i) (r₀ (i+1))`, using
the presentation's primitive-recursive intersection function `Q.inter`. Each `Yₜ₍ᵢ₎` is the meet of
the first `i+1` members of `y`, hence still in `y` (filters are ∩-closed) and `⊆ Yᵣ₀₍ᵢ₎`, which is
what makes the union still equal to `y` while being a decreasing chain.

**Choice discipline.** Half 1 is built only on the choice-free `Recursive.lean` layer and audits
`⊆ {propext, Quot.sound}`. Half 2's *data* (the function `t` and its primitive recursiveness) is also
choice-free; the `Prop`-level union/membership reasoning over `Set β` may pull `Classical.choice`
(the usual `Set`-equality pattern of Lecture VII), flagged in the checkpoint.
-/

namespace Scott1980.Neighborhood.Exercise714

open NeighborhoodSystem Domain.Recursive Scott1980.Neighborhood

/-! ## Half 1 — non-empty r.e. ⇔ range of a primitive recursive function -/

/-- **The range of a primitive recursive function is recursively enumerable.** The relation
`r i = n` is recursively decidable (`RecDecidable.natEq`), and `∃ i, r i = n` is its projection, so
it is r.e. by definition of `REPred`. -/
theorem repred_range_primrec {r : ℕ → ℕ} (hr : Nat.Primrec r) :
    REPred (fun n => ∃ i, r i = n) := by
  refine ⟨fun t => r t.unpair.1 = t.unpair.2,
    RecDecidable.natEq (hr.comp Nat.Primrec.left) Nat.Primrec.right, fun n => ?_⟩
  refine exists_congr (fun i => ?_)
  simp only [unpair_pair_fst, unpair_pair_snd]

/-- **A non-empty recursively enumerable set is the range of a primitive recursive function.** This
is the precise content of Scott's prose after Definition 7.2 (*"there is a primitive recursive `r`
with `y = {Y_{r(i)}}`"*). Given a witness `a ∈ p` and the `{0,1}` decider `qc` of the relation `q`
underlying `p` (`p n ↔ ∃ i, q ⟨i,n⟩`), the function `r w := selectFn (isOne (qc w)) w.2 a` enumerates
`p`: on a code `w = ⟨i,n⟩` with `q ⟨i,n⟩` it returns `n`, otherwise it returns the fixed `a`. Its
range is exactly `p` (the fall-back `a` covers the codes that do not witness anything — this is where
non-emptiness is used). -/
theorem repred_exists_primrec_range {p : ℕ → Prop} (hp : REPred p) {a : ℕ} (ha : p a) :
    ∃ r : ℕ → ℕ, Nat.Primrec r ∧ ∀ n, p n ↔ ∃ i, r i = n := by
  obtain ⟨q, ⟨qc, hqcp, hqcs⟩, hqe⟩ := hp
  refine ⟨fun w => selectFn (isOne (qc w)) w.unpair.2 a,
    primrec_selectFn (primrec_isOne.comp hqcp) Nat.Primrec.right (Nat.Primrec.const a), ?_⟩
  -- Every value of the enumerator lies in `p`.
  have hrw_mem : ∀ w, p (selectFn (isOne (qc w)) w.unpair.2 a) := by
    intro w
    rcases (show isOne (qc w) = 0 ∨ isOne (qc w) = 1 by
        have := isOne_le_one (qc w); omega) with h0 | h1
    · rw [h0, selectFn_zero]; exact ha
    · rw [h1, selectFn_one]
      have hqw : q w := (hqcs w).mpr ((isOne_eq_one_iff (qc w)).mp h1)
      rw [hqe w.unpair.2]
      exact ⟨w.unpair.1, by rw [pair_unpair]; exact hqw⟩
  intro n
  constructor
  · intro hpn
    rw [hqe n] at hpn
    obtain ⟨i, hi⟩ := hpn
    refine ⟨Nat.pair i n, ?_⟩
    show selectFn (isOne (qc (Nat.pair i n))) (Nat.pair i n).unpair.2 a = n
    have hqc1 : isOne (qc (Nat.pair i n)) = 1 := (isOne_eq_one_iff _).mpr ((hqcs _).mp hi)
    rw [hqc1, selectFn_one, unpair_pair_snd]
  · rintro ⟨w, rfl⟩
    exact hrw_mem w

/-- **A non-empty recursively enumerable relation is enumerated by a pair of primitive recursive
functions** (Scott's `f = {(X_{s(i)}, Y_{r(i)}) ∣ i ∈ ℕ}`). Apply `repred_exists_primrec_range` to
the `Nat.pair`-coded relation and split the resulting range function into its two coordinates. -/
theorem repred₂_exists_primrec_enum {p : ℕ → ℕ → Prop} (hp : REPred₂ p) {a b : ℕ}
    (hab : p a b) :
    ∃ s r : ℕ → ℕ, Nat.Primrec s ∧ Nat.Primrec r ∧
      ∀ n m, p n m ↔ ∃ i, s i = n ∧ r i = m := by
  have hp' : REPred (fun t => p t.unpair.1 t.unpair.2) := hp
  have hwit : (fun t => p t.unpair.1 t.unpair.2) (Nat.pair a b) := by
    simp only [unpair_pair_fst, unpair_pair_snd]; exact hab
  obtain ⟨pf, hpf, hspec⟩ := repred_exists_primrec_range hp' hwit
  refine ⟨fun i => (pf i).unpair.1, fun i => (pf i).unpair.2,
    Nat.Primrec.left.comp hpf, Nat.Primrec.right.comp hpf, fun n m => ?_⟩
  have h := hspec (Nat.pair n m)
  simp only [unpair_pair_fst, unpair_pair_snd] at h
  rw [h]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_, ?_⟩
    · show (pf i).unpair.1 = n; rw [hi, unpair_pair_fst]
    · show (pf i).unpair.2 = m; rw [hi, unpair_pair_snd]
  · rintro ⟨i, hs, hr⟩
    refine ⟨i, ?_⟩
    change (pf i).unpair.1 = n at hs
    change (pf i).unpair.2 = m at hr
    rw [← hs, ← hr]; exact (pair_unpair _).symm

/-! ## Half 2 — every computable element is a decreasing union of finite elements -/

variable {β : Type*}

/-- The **running-intersection enumeration** of a computable element: `tFun Q r 0 = r 0` and
`tFun Q r (i+1) = Q.inter (tFun Q r i) (r (i+1))`. As `i` grows it lists the meet of the first `i+1`
members `Y_{r 0}, …, Y_{r i}` of the element, giving a *decreasing* chain of neighbourhoods. -/
private def tFun {W : NeighborhoodSystem β} (Q : ComputablePresentation W) (r : ℕ → ℕ) (n : ℕ) :
    ℕ :=
  Nat.rec (motive := fun _ => ℕ) (r 0) (fun y IH => Q.inter IH (r (y + 1))) n

private theorem tFun_zero {W : NeighborhoodSystem β} (Q : ComputablePresentation W) (r : ℕ → ℕ) :
    tFun Q r 0 = r 0 := rfl

private theorem tFun_succ {W : NeighborhoodSystem β} (Q : ComputablePresentation W) (r : ℕ → ℕ)
    (i : ℕ) : tFun Q r (i + 1) = Q.inter (tFun Q r i) (r (i + 1)) := rfl

/-- The running-intersection enumeration is primitive recursive whenever `r` is (genuine primitive
recursion with a counter-dependent step, via `Nat.Primrec.prec`). -/
private theorem primrec_tFun {W : NeighborhoodSystem β} (Q : ComputablePresentation W) {r : ℕ → ℕ}
    (hr : Nat.Primrec r) : Nat.Primrec (tFun Q r) := by
  have hg : Nat.Primrec (fun w => Q.inter w.unpair.2.unpair.2 (r (w.unpair.2.unpair.1 + 1))) := by
    have hIH : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
      Nat.Primrec.right.comp Nat.Primrec.right
    have hy1 : Nat.Primrec (fun w : ℕ => r (w.unpair.2.unpair.1 + 1)) :=
      hr.comp (Nat.Primrec.succ.comp (Nat.Primrec.left.comp Nat.Primrec.right))
    exact (Q.inter_primrec.comp (hIH.pair hy1)).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  refine ((Nat.Primrec.prec (Nat.Primrec.const (r 0)) hg).comp
    ((Nat.Primrec.const 0).pair primrec_id)).of_eq (fun n => ?_)
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]
  rfl

/-- **Exercise 7.14, Half 2 (Scott 1981, PRG-19).** Every computable element `y ∈ |ℰ|` can be
written `y = ⋃ {↑Y_{t(i)} ∣ i ∈ ℕ}` with `t : ℕ → ℕ` primitive recursive and the approximations
*decreasing*, `Y_{t(i+1)} ⊆ Y_{t(i)}`.

The index set `{m ∣ Yₘ ∈ y}` is r.e. (`IsComputableElement`) and non-empty (it contains the master
`Δ`, by `y.master_mem`), so Half 1's `repred_exists_primrec_range` lists it as the range of a
primitive recursive `r₀`. Running intersections (`tFun Q r₀`) turn this into a decreasing chain whose
members are still in `y` (a filter is closed under `∩`) and still cofinal in `y` (each
`Y_{t(i)} ⊆ Y_{r₀(i)}`), so the principal-filter union is unchanged. -/
theorem computableElement_eq_decreasing_iUnion_principal {W : NeighborhoodSystem β}
    (Q : ComputablePresentation W) {y : W.Element} (hy : IsComputableElement Q y) :
    ∃ t : ℕ → ℕ, Nat.Primrec t ∧
      (∀ i, Q.X (t (i + 1)) ⊆ Q.X (t i)) ∧
      (∀ Z, y.mem Z ↔ ∃ i, (W.principal (Q.mem_X (t i))).mem Z) := by
  have hy' : REPred (fun m => y.mem (Q.X m)) := hy
  -- The index set is non-empty: it contains the master neighbourhood `Δ`.
  obtain ⟨m₀, hm₀⟩ := Q.surj W.master_mem
  have hwit : y.mem (Q.X m₀) := by rw [hm₀]; exact y.master_mem
  obtain ⟨r₀, hr₀, hr0_spec⟩ := repred_exists_primrec_range hy' hwit
  -- Each enumerated index gives a member of `y`.
  have hr0_mem : ∀ i, y.mem (Q.X (r₀ i)) := fun i => (hr0_spec (r₀ i)).mpr ⟨i, rfl⟩
  -- Consistency of a pair of members (witnessed by their meet, itself in `y`).
  have hcons : ∀ a c : ℕ, y.mem (Q.X a) → y.mem (Q.X c) →
      ∃ k, Q.X k ⊆ Q.X a ∩ Q.X c := by
    intro a c ha hc
    obtain ⟨k, hk⟩ := Q.surj (y.sub (y.inter_mem ha hc))
    exact ⟨k, hk.subset⟩
  -- Every `tFun` value is a member of `y`.
  have ht_mem : ∀ i, y.mem (Q.X (tFun Q r₀ i)) := by
    intro i
    induction i with
    | zero => rw [tFun_zero]; exact hr0_mem 0
    | succ k ih =>
      have heq : Q.X (tFun Q r₀ (k + 1)) = Q.X (tFun Q r₀ k) ∩ Q.X (r₀ (k + 1)) :=
        Q.inter_spec (hcons (tFun Q r₀ k) (r₀ (k + 1)) ih (hr0_mem (k + 1)))
      rw [heq]; exact y.inter_mem ih (hr0_mem (k + 1))
  -- The defining intersection equation for `tFun`.
  have ht_eq : ∀ i, Q.X (tFun Q r₀ (i + 1)) = Q.X (tFun Q r₀ i) ∩ Q.X (r₀ (i + 1)) := fun i =>
    Q.inter_spec (hcons (tFun Q r₀ i) (r₀ (i + 1)) (ht_mem i) (hr0_mem (i + 1)))
  -- Decreasing: the next approximation is contained in the current one.
  have ht_dec : ∀ i, Q.X (tFun Q r₀ (i + 1)) ⊆ Q.X (tFun Q r₀ i) := by
    intro i; rw [ht_eq i]; exact Set.inter_subset_left
  -- Each approximation is contained in the corresponding enumerated member.
  have ht_sub_r : ∀ i, Q.X (tFun Q r₀ i) ⊆ Q.X (r₀ i) := by
    intro i
    cases i with
    | zero => rw [tFun_zero]
    | succ k => rw [ht_eq k]; exact Set.inter_subset_right
  refine ⟨tFun Q r₀, primrec_tFun Q hr₀, ht_dec, fun Z => ?_⟩
  constructor
  · intro hZ
    obtain ⟨m, hm⟩ := Q.surj (y.sub hZ)
    have hym : y.mem (Q.X m) := by rw [hm]; exact hZ
    obtain ⟨i, hi⟩ := (hr0_spec m).mp hym
    have hZeq : Q.X (r₀ i) = Z := by rw [hi]; exact hm
    exact ⟨i, y.sub hZ, by rw [← hZeq]; exact ht_sub_r i⟩
  · rintro ⟨i, hWZ, hsub⟩
    exact y.up_mem (ht_mem i) hWZ hsub

end Scott1980.Neighborhood.Exercise714

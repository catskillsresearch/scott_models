/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Definition71
import Scott1980.Neighborhood.ExampleB
import Scott1980.Neighborhood.Example23
import Scott1980.Neighborhood.Theorem75

/-!
# Exercise 7.24 (Scott 1981, PRG-19, §7) — the LUCID system `L`

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VII.

> **Exercise 7.24.** (Suggested by the LUCID language of Ashcroft and Wadge: *SIAM Jour. Comp.*
> vol. 5 (1976).) Define a set `Γ` by
>
> `Γ = ⋃ᵢ ({i} × Γ) ∪ {*}`.
>
> Define a system `L = {Γ} ∪ {{i} × X ∣ i ∈ ℕ and X ∈ L}`. Show that `L` is effectively given.
> Show that the elements of `|L|` can be identified with the finite and infinite sequences of
> natural numbers. What is the connection between `B` and `L`? Show that the combinators of LUCID
> can be construed as computable mappings of type `(L→T) → (L→T)` or of type
> `(L→T) × (L→T) → (L→T)`. Conclude that programs in LUCID define computable maps.

## What this file proves

Scott's `Γ` satisfies a *coinductive* set equation `Γ ≅ 1 + (ℕ × Γ)`: an element is either the
basepoint `*` or a pair `(i, γ)` with `γ ∈ Γ` again. Taking the **final** (as opposed to initial)
solution — so that the recursion may run forever — identifies `Γ` with the finite-or-infinite
sequences of naturals directly:

* **`Gamma := List ℕ ⊕ (ℕ → ℕ)`** — a finite sequence (`inl`, terminating at `*`) or an infinite
  one (`inr`, a stream that never reaches `*`). **`star`**/**`cons`** realize `*`/`(i, γ)`;
  **`Gamma_cases`** is the defining equation read as a theorem (every `γ` is `star` or a unique
  `cons i γ'`), and **`cons_injective`** is the "unique" half.
* **`consSet i X = {i} × X`** and **`nbhd l`** (`nbhd [] = Γ`, `nbhd (i :: l) = {i} × nbhd l`) —
  exactly Scott's neighbourhoods, indexed by the finite list of naturals `l` that names them
  (mirroring `ExampleB.cone`/`Example62.embBit`, generalized from `Bool` to `ℕ`-ary branching).
  **`nbhd_subset_iff`** (`nbhd l ⊆ nbhd l' ↔ l' <+: l`) is the master reduction, giving
  **`Lmem`**'s nested-or-disjointness (`L_nestedOrDisjoint`) and hence the system **`L`**.
-/

namespace Scott1980.Neighborhood.Exercise724

open NeighborhoodSystem Domain.Recursive

/-! ## `Γ`: finite and infinite sequences of naturals -/

/-- Scott's set `Γ`, the *terminal* solution of `Γ = (⋃ᵢ {i} × Γ) ∪ {*}`: a finite sequence,
terminating at `*` (`Sum.inl`), or an infinite one that never terminates (`Sum.inr`). -/
abbrev Gamma : Type := List ℕ ⊕ (ℕ → ℕ)

instance : Nonempty Gamma := ⟨Sum.inl []⟩

/-- Scott's basepoint `*`: the empty (already-terminated) sequence. -/
def star : Gamma := Sum.inl []

/-- Prepend `i` to an infinite stream (`Stream'.cons`, spelled out by hand). -/
def streamCons (i : ℕ) (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => i
  | n + 1 => s n

@[simp] theorem streamCons_zero (i : ℕ) (s : ℕ → ℕ) : streamCons i s 0 = i := rfl

@[simp] theorem streamCons_succ (i : ℕ) (s : ℕ → ℕ) (n : ℕ) : streamCons i s (n + 1) = s n := rfl

/-- Scott's `(i, γ)`: prepend the natural `i` to a finite-or-infinite sequence `γ`. -/
def cons (i : ℕ) : Gamma → Gamma
  | .inl l => .inl (i :: l)
  | .inr s => .inr (streamCons i s)

@[simp] theorem cons_inl (i : ℕ) (l : List ℕ) : cons i (.inl l) = .inl (i :: l) := rfl

@[simp] theorem cons_inr (i : ℕ) (s : ℕ → ℕ) : cons i (.inr s) = .inr (streamCons i s) := rfl

/-- `*` is never of the shape `(i, γ)`. -/
theorem star_ne_cons (i : ℕ) (γ : Gamma) : star ≠ cons i γ := by
  cases γ <;> simp [star, cons]

/-- **`cons` is injective** (jointly in both arguments): `(i, γ) = (j, δ) ⟹ i = j ∧ γ = δ`. -/
theorem cons_injective {i j : ℕ} {γ δ : Gamma} (h : cons i γ = cons j δ) : i = j ∧ γ = δ := by
  cases γ with
  | inl l =>
    cases δ with
    | inl l' =>
      simp only [cons, Sum.inl.injEq, List.cons.injEq] at h
      exact ⟨h.1, by rw [h.2]⟩
    | inr s' => simp [cons] at h
  | inr s =>
    cases δ with
    | inl l' => simp [cons] at h
    | inr s' =>
      have heq : streamCons i s = streamCons j s' := by simpa [cons] using h
      have hi : i = j := by simpa using congrFun heq 0
      refine ⟨hi, ?_⟩
      have hs : s = s' := funext fun n => by simpa using congrFun heq (n + 1)
      rw [hs]

/-- **The defining equation of `Γ`, read as a theorem.** Every `γ ∈ Γ` is either `*` or `(i, γ')`
for some `i, γ'`: `Γ = (⋃ᵢ {i} × Γ) ∪ {*}`. -/
theorem Gamma_cases (γ : Gamma) : γ = star ∨ ∃ i γ', γ = cons i γ' := by
  cases γ with
  | inl l =>
    cases l with
    | nil => exact Or.inl rfl
    | cons i l' => exact Or.inr ⟨i, .inl l', rfl⟩
  | inr s =>
    refine Or.inr ⟨s 0, .inr (fun n => s (n + 1)), ?_⟩
    simp only [cons]
    congr 1
    funext n
    cases n <;> rfl

/-! ## The neighbourhood system `L` -/

/-- Scott's `{i} × X`: the `i`-prefixed copy of a neighbourhood `X`. -/
def consSet (i : ℕ) (X : Set Gamma) : Set Gamma := {z | ∃ γ ∈ X, z = cons i γ}

@[simp] theorem mem_consSet {i : ℕ} {X : Set Gamma} {z : Gamma} :
    z ∈ consSet i X ↔ ∃ γ ∈ X, z = cons i γ := Iff.rfl

theorem consSet_subset_of_subset {i : ℕ} {X X' : Set Gamma} (h : X ⊆ X') :
    consSet i X ⊆ consSet i X' := by
  rintro z ⟨γ, hγ, rfl⟩; exact ⟨γ, h hγ, rfl⟩

/-- **`{i} × X ⊆ {i} × X' ↔ X ⊆ X'`.** -/
theorem consSet_subset {i : ℕ} {X X' : Set Gamma} :
    consSet i X ⊆ consSet i X' ↔ X ⊆ X' := by
  refine ⟨fun h γ hγ => ?_, consSet_subset_of_subset⟩
  obtain ⟨γ', hγ', heq⟩ := h ⟨γ, hγ, rfl⟩
  rwa [(cons_injective heq.symm).2] at hγ'

theorem consSet_inter (i : ℕ) (X X' : Set Gamma) :
    consSet i X ∩ consSet i X' = consSet i (X ∩ X') := by
  ext z
  simp only [Set.mem_inter_iff, mem_consSet]
  constructor
  · rintro ⟨⟨γ, hγ, rfl⟩, γ', hγ', heq⟩
    obtain ⟨-, hγγ'⟩ := cons_injective heq
    exact ⟨γ, ⟨hγ, hγγ' ▸ hγ'⟩, rfl⟩
  · rintro ⟨γ, ⟨hγ, hγ'⟩, rfl⟩
    exact ⟨⟨γ, hγ, rfl⟩, ⟨γ, hγ', rfl⟩⟩

theorem consSet_inter_ne {i j : ℕ} (h : i ≠ j) (X Y : Set Gamma) :
    consSet i X ∩ consSet j Y = ∅ := by
  ext z
  simp only [Set.mem_inter_iff, mem_consSet, Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨γ, -, rfl⟩ ⟨γ', -, heq⟩
  exact h (cons_injective heq).1

@[simp] theorem consSet_empty (i : ℕ) : consSet i (∅ : Set Gamma) = ∅ := by
  ext z; simp [mem_consSet]

theorem consSet_nonempty {i : ℕ} {X : Set Gamma} (h : X.Nonempty) : (consSet i X).Nonempty := by
  obtain ⟨γ, hγ⟩ := h; exact ⟨cons i γ, γ, hγ, rfl⟩

theorem star_not_mem_consSet (i : ℕ) (X : Set Gamma) : star ∉ consSet i X := by
  rintro ⟨γ, -, heq⟩; exact star_ne_cons i γ heq

/-- **The neighbourhood coded by a finite list.** `nbhd [] = Γ` (Scott's master `Γ`);
`nbhd (i :: l) = {i} × nbhd l`. Every `Lmem`-neighbourhood is `nbhd l` for a *unique* `l`
(`nbhd_injective`), mirroring `ExampleB.cone`/`Example62.embBit` generalized to `ℕ`-ary
branching. -/
def nbhd : List ℕ → Set Gamma
  | [] => Set.univ
  | i :: l => consSet i (nbhd l)

@[simp] theorem nbhd_nil : nbhd [] = (Set.univ : Set Gamma) := rfl

@[simp] theorem nbhd_cons (i : ℕ) (l : List ℕ) : nbhd (i :: l) = consSet i (nbhd l) := rfl

theorem nbhd_nonempty : ∀ l : List ℕ, (nbhd l).Nonempty
  | [] => ⟨star, trivial⟩
  | _ :: l => consSet_nonempty (nbhd_nonempty l)

/-- **The master reduction (mirrors `ExampleB.cone_subset_cone`).** `nbhd l ⊆ nbhd l' ↔ l' <+: l`:
cones reverse the prefix order. Proved by induction on `l`, peeling off matching heads. -/
theorem nbhd_subset_iff : ∀ (l l' : List ℕ), nbhd l ⊆ nbhd l' ↔ l' <+: l := by
  intro l
  induction l with
  | nil =>
    intro l'
    cases l' with
    | nil => simp
    | cons j t =>
      constructor
      · intro h
        exact absurd (h (Set.mem_univ star)) (by rw [nbhd_cons]; exact star_not_mem_consSet j (nbhd t))
      · rintro ⟨u, hu⟩
        simp at hu
  | cons i s ih =>
    intro l'
    cases l' with
    | nil => simp [nbhd_cons]
    | cons j t =>
      by_cases hij : i = j
      · subst hij
        rw [nbhd_cons, nbhd_cons, consSet_subset, ih t, List.cons_prefix_cons]
        simp
      · constructor
        · intro h
          exfalso
          obtain ⟨γ, hγ⟩ := nbhd_nonempty s
          have hmem : cons i γ ∈ consSet j (nbhd t) := h ⟨γ, hγ, rfl⟩
          obtain ⟨γ', -, heq⟩ := hmem
          exact hij (cons_injective heq).1
        · intro h
          rw [List.cons_prefix_cons] at h
          exact absurd h.1.symm hij

/-- **`nbhd` is injective.** Antisymmetry of `nbhd_subset_iff`: `l' <+: l` and `l <+: l'` force
`l.length = l'.length`, and a prefix of equal length is the whole list. -/
theorem nbhd_injective {l l' : List ℕ} (h : nbhd l = nbhd l') : l = l' := by
  have h1 : l' <+: l := (nbhd_subset_iff l l').mp h.subset
  have h2 : l <+: l' := (nbhd_subset_iff l' l).mp h.symm.subset
  exact (h1.eq_of_length (h1.length_le.antisymm h2.length_le)).symm

/-- Membership in Scott's system `L = {Γ} ∪ {{i} × X ∣ i ∈ ℕ, X ∈ L}`: `X ∈ L` iff `X = nbhd l`
for some finite list `l` (the "address" of the neighbourhood). -/
def Lmem (X : Set Gamma) : Prop := ∃ l, X = nbhd l

@[simp] theorem mem_nbhd (l : List ℕ) : Lmem (nbhd l) := ⟨l, rfl⟩

/-- **`L` is nested-or-disjoint** (Scott's "very special circumstance", generalizing
`ExampleB.cone_trichotomy`/`Example62`'s pairwise structure from `Bool` to `ℕ`-ary branching). -/
theorem L_nestedOrDisjoint : NestedOrDisjoint Lmem := by
  rintro X Y ⟨l, rfl⟩ ⟨l', rfl⟩
  induction l generalizing l' with
  | nil => exact Or.inr (Or.inl (by simp))
  | cons i s ih =>
    cases l' with
    | nil => exact Or.inl (by simp)
    | cons j t =>
      by_cases hij : i = j
      · subst hij
        rcases ih t with h1 | h2 | h3
        · exact Or.inl (by rw [nbhd_cons, nbhd_cons]; exact consSet_subset_of_subset h1)
        · exact Or.inr (Or.inl (by rw [nbhd_cons, nbhd_cons]; exact consSet_subset_of_subset h2))
        · exact Or.inr (Or.inr (by rw [nbhd_cons, nbhd_cons, consSet_inter, h3, consSet_empty]))
      · exact Or.inr (Or.inr (by rw [nbhd_cons, nbhd_cons]; exact consSet_inter_ne hij _ _))

/-- **Exercise 7.24 — `L` is a neighbourhood system** on tokens `Γ`, master `Γ = nbhd []`. -/
def L : NeighborhoodSystem Gamma :=
  NeighborhoodSystem.ofNestedOrDisjoint Lmem Set.univ (mem_nbhd []) L_nestedOrDisjoint
    (fun {X} _ => Set.subset_univ X)

@[simp] theorem L_mem {X : Set Gamma} : L.mem X ↔ Lmem X := Iff.rfl

@[simp] theorem L_master : L.master = Set.univ := rfl

/-! ## `L` is effectively given -/

/-- **The `{0,1}` prefix test.** `isPrefixChar m n = 1 ↔ decodeList m <+: decodeList n`, built from
`Recursive.lean`'s `listLenChar`/`takeCode`/`listEqChar` (already primitive recursive): `l₁ <+: l₂`
iff `l₂.take l₁.length = l₁` (`List.prefix_iff_eq_take`), unconditionally (`List.take` auto-caps at
the available length, so no separate length guard is needed). -/
def isPrefixChar (m n : ℕ) : ℕ := listEqChar (takeCode (listLenChar m) n) m

theorem isPrefixChar_eq_one_iff (m n : ℕ) :
    isPrefixChar m n = 1 ↔ decodeList m <+: decodeList n := by
  unfold isPrefixChar
  rw [listEqChar_eq_one_iff, takeCode_eq, listLenChar_eq, List.prefix_iff_eq_take]
  exact eq_comm

theorem isPrefixChar_le_one (m n : ℕ) : isPrefixChar m n ≤ 1 := listEqChar_le_one _ _

theorem primrec_isPrefixChar : Nat.Primrec (fun t => isPrefixChar t.unpair.1 t.unpair.2) := by
  have hlen : Nat.Primrec (fun t : ℕ => listLenChar t.unpair.1) := primrec_listLenChar.comp Nat.Primrec.left
  have htake : Nat.Primrec (fun t : ℕ => takeCode (listLenChar t.unpair.1) t.unpair.2) :=
    (primrec_takeCode.comp (Nat.Primrec.pair hlen Nat.Primrec.right)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_listEqChar.comp (Nat.Primrec.pair htake Nat.Primrec.left)).of_eq fun t => by
    simp only [isPrefixChar, unpair_pair_fst, unpair_pair_snd]

/-- The enumeration `Lenum n := nbhd (decodeList n)`: every code `n` names the neighbourhood
addressed by its decoded list, and (via `encodeList`/`decodeList` round-tripping) this hits every
`Lmem` set. -/
def Lenum (n : ℕ) : Set Gamma := nbhd (decodeList n)

@[simp] theorem Lenum_mem (n : ℕ) : Lmem (Lenum n) := mem_nbhd (decodeList n)

theorem Lenum_surj {Y : Set Gamma} (hY : Lmem Y) : ∃ n, Lenum n = Y := by
  obtain ⟨l, rfl⟩ := hY
  exact ⟨encodeList l, by unfold Lenum; rw [decodeList_encodeList]⟩

/-- **`Xₙ ⊆ Xₘ` on the `Lenum` coding, decided by `isPrefixChar`.** -/
theorem Lenum_subset_iff (n m : ℕ) : Lenum n ⊆ Lenum m ↔ isPrefixChar m n = 1 := by
  unfold Lenum; rw [nbhd_subset_iff, isPrefixChar_eq_one_iff]

/-- **`Xₙ ∩ Xₘ = X_k` on the `Lenum` coding.** The intersection of two `nbhd`s is the more specific
of the two whenever they are nested, and no `Lmem` set at all otherwise (`nbhd` is always
nonempty, so `∅` never equals an `Lenum k`). -/
theorem Lenum_interEq_iff (n m k : ℕ) :
    Lenum n ∩ Lenum m = Lenum k ↔
      (isPrefixChar m n = 1 ∧ decodeList k = decodeList n) ∨
      (isPrefixChar n m = 1 ∧ decodeList k = decodeList m) := by
  unfold Lenum
  rcases L_nestedOrDisjoint (mem_nbhd (decodeList n)) (mem_nbhd (decodeList m)) with h | h | h
  · have hp : isPrefixChar m n = 1 := (isPrefixChar_eq_one_iff m n).mpr ((nbhd_subset_iff _ _).mp h)
    rw [Set.inter_eq_left.mpr h]
    constructor
    · intro heq; exact Or.inl ⟨hp, (nbhd_injective heq).symm⟩
    · rintro (⟨-, heq⟩ | ⟨hp', heq⟩)
      · rw [heq]
      · rw [isPrefixChar_eq_one_iff] at hp'
        rw [heq]
        exact Set.Subset.antisymm h ((nbhd_subset_iff (decodeList m) (decodeList n)).mpr hp')
  · have hp : isPrefixChar n m = 1 := (isPrefixChar_eq_one_iff n m).mpr ((nbhd_subset_iff _ _).mp h)
    rw [Set.inter_eq_right.mpr h]
    constructor
    · intro heq; exact Or.inr ⟨hp, (nbhd_injective heq).symm⟩
    · rintro (⟨hp', heq⟩ | ⟨-, heq⟩)
      · rw [isPrefixChar_eq_one_iff] at hp'
        rw [heq]
        exact Set.Subset.antisymm h ((nbhd_subset_iff (decodeList n) (decodeList m)).mpr hp')
      · rw [heq]
  · rw [h]
    have h1 : isPrefixChar m n ≠ 1 := by
      intro hp; rw [isPrefixChar_eq_one_iff] at hp
      obtain ⟨t, ht⟩ := (nbhd_nonempty (decodeList n))
      exact Set.notMem_empty t (h ▸ Set.mem_inter ht ((nbhd_subset_iff _ _).mpr hp ht))
    have h2 : isPrefixChar n m ≠ 1 := by
      intro hp; rw [isPrefixChar_eq_one_iff] at hp
      obtain ⟨t, ht⟩ := (nbhd_nonempty (decodeList m))
      exact Set.notMem_empty t (h ▸ Set.mem_inter ((nbhd_subset_iff _ _).mpr hp ht) ht)
    constructor
    · intro heq; exact absurd heq.symm (nbhd_nonempty (decodeList k)).ne_empty
    · rintro (⟨hp, -⟩ | ⟨hp, -⟩)
      · exact absurd hp h1
      · exact absurd hp h2

/-- **7.1(ii) — consistency is recursively decidable.** `∃ k, Lenum k ⊆ Lenum n ∩ Lenum m` holds
iff `n, m` are nested (`isPrefixChar m n = 1 ∨ isPrefixChar n m = 1`): if nested, the more specific
of `n, m` itself witnesses it; conversely a common lower bound forces nestedness by
`L_nestedOrDisjoint` (a properly disjoint pair has no nonempty common lower bound, and every
`Lmem` set is nonempty). -/
theorem Lenum_cons_iff (n m : ℕ) :
    (∃ k, Lenum k ⊆ Lenum n ∩ Lenum m) ↔ isPrefixChar m n = 1 ∨ isPrefixChar n m = 1 := by
  constructor
  · rintro ⟨k, hk⟩
    rcases L_nestedOrDisjoint (mem_nbhd (decodeList n)) (mem_nbhd (decodeList m)) with h | h | h
    · exact Or.inl ((isPrefixChar_eq_one_iff m n).mpr ((nbhd_subset_iff _ _).mp h))
    · exact Or.inr ((isPrefixChar_eq_one_iff n m).mpr ((nbhd_subset_iff _ _).mp h))
    · exfalso
      unfold Lenum at hk
      obtain ⟨t, ht⟩ := nbhd_nonempty (decodeList k)
      exact Set.notMem_empty t (h ▸ hk ht)
  · rintro (hp | hp)
    · exact ⟨n, Set.subset_inter subset_rfl ((Lenum_subset_iff n m).mpr hp)⟩
    · exact ⟨m, Set.subset_inter ((Lenum_subset_iff m n).mpr hp) subset_rfl⟩

/-- `isPrefixChar` composed with the swap of `unpair`, built via `.of_eq` (rather than relying
on elaborator defeq-unification against `Nat.pair`/`Nat.unpair`, which is expensive and can blow
the `whnf` budget). -/
private theorem primrec_isPrefixChar_swap :
    Nat.Primrec (fun t => isPrefixChar t.unpair.2 t.unpair.1) :=
  (primrec_isPrefixChar.comp (Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left)).of_eq
    fun t => by simp only [unpair_pair_fst, unpair_pair_snd]

/-- **`Xₙ ⊆ Xₘ` `{0,1}` characteristic**, packaged as a single *named* unary function (rather than
an anonymous `t.unpair`-lambda passed positionally to `RecDecidable₂.of_paired_zero_one_char`):
naming it lets the `hfe` obligation be stated and proved as a standalone lemma whose conclusion is
syntactically `LenumSubsetChar (Nat.pair n m) = 1`, so the final application only needs to match
this name against itself — no elaborator-side defeq unfolding of `Nat.pair`/`Nat.unpair` (which is
expensive and blows the `whnf` budget; see the project's course-of-values discipline). -/
def LenumSubsetChar (t : ℕ) : ℕ := isPrefixChar t.unpair.2 t.unpair.1

theorem primrec_LenumSubsetChar : Nat.Primrec LenumSubsetChar :=
  primrec_isPrefixChar_swap.of_eq fun t => by simp only [LenumSubsetChar]

theorem LenumSubsetChar_le_one (t : ℕ) : LenumSubsetChar t ≤ 1 :=
  isPrefixChar_le_one _ _

theorem Lenum_subset_char_eq_one_iff (n m : ℕ) :
    Lenum n ⊆ Lenum m ↔ LenumSubsetChar (Nat.pair n m) = 1 := by
  unfold LenumSubsetChar
  rw [unpair_pair_fst, unpair_pair_snd, Lenum_subset_iff]

/-- `isPrefixChar` gives a `RecDecidable₂` decider for `Lenum n ⊆ Lenum m`. -/
theorem Lenum_subset_recDecidable : RecDecidable₂ (fun n m => Lenum n ⊆ Lenum m) :=
  RecDecidable₂.of_paired_zero_one_char primrec_LenumSubsetChar
    (fun t => by have := LenumSubsetChar_le_one t; omega)
    Lenum_subset_char_eq_one_iff

/-- **The `{0,1}` consistency characteristic** — a flat `orBit` of the two `isPrefixChar`
directions (kept as a single hand-rolled arithmetic combinator rather than composing
`RecDecidable.or`/`.and`, per the project's course-of-values discipline: nesting the generic
`RecDecidable` combinators here elaborates a deeply-repeated composition and blows the `whnf`
budget). -/
def LenumConsChar (n m : ℕ) : ℕ :=
  isPrefixChar m n + isPrefixChar n m - isPrefixChar m n * isPrefixChar n m

private theorem isPrefixChar_eq_zero_or_one (m n : ℕ) :
    isPrefixChar m n = 0 ∨ isPrefixChar m n = 1 := by
  have := isPrefixChar_le_one m n; omega

theorem LenumConsChar_eq_one_iff (n m : ℕ) :
    LenumConsChar n m = 1 ↔ isPrefixChar m n = 1 ∨ isPrefixChar n m = 1 := by
  unfold LenumConsChar
  rcases isPrefixChar_eq_zero_or_one m n with ha | ha <;>
    rcases isPrefixChar_eq_zero_or_one n m with hb | hb <;> simp [ha, hb]

theorem LenumConsChar_le_one (n m : ℕ) : LenumConsChar n m ≤ 1 := by
  unfold LenumConsChar
  rcases isPrefixChar_eq_zero_or_one m n with ha | ha <;>
    rcases isPrefixChar_eq_zero_or_one n m with hb | hb <;> simp [ha, hb]

theorem primrec_LenumConsChar :
    Nat.Primrec (fun t => LenumConsChar t.unpair.1 t.unpair.2) := by
  have ha : Nat.Primrec (fun t : ℕ => isPrefixChar t.unpair.2 t.unpair.1) :=
    primrec_isPrefixChar_swap
  have hb : Nat.Primrec (fun t : ℕ => isPrefixChar t.unpair.1 t.unpair.2) := primrec_isPrefixChar
  exact (primrec_sub₂ (primrec_add₂ ha hb) (primrec_mul₂ ha hb)).of_eq fun t => by
    simp only [LenumConsChar]

/-- Named-function packaging of `LenumConsChar` on `Nat.pair`-coded pairs (same rationale as
`LenumSubsetChar` above: avoids elaborator defeq-unification against `Nat.pair`/`Nat.unpair`). -/
def LenumConsCharP (t : ℕ) : ℕ := LenumConsChar t.unpair.1 t.unpair.2

theorem primrec_LenumConsCharP : Nat.Primrec LenumConsCharP :=
  primrec_LenumConsChar.of_eq fun t => by simp only [LenumConsCharP]

theorem LenumConsCharP_le_one (t : ℕ) : LenumConsCharP t ≤ 1 :=
  LenumConsChar_le_one _ _

theorem Lenum_cons_charP_eq_one_iff (n m : ℕ) :
    (∃ k, Lenum k ⊆ Lenum n ∩ Lenum m) ↔ LenumConsCharP (Nat.pair n m) = 1 := by
  unfold LenumConsCharP
  rw [unpair_pair_fst, unpair_pair_snd, LenumConsChar_eq_one_iff]
  exact Lenum_cons_iff n m

/-- **7.1(ii) — consistency is recursively decidable.** -/
theorem Lenum_cons_computable : RecDecidable₂ (fun n m => ∃ k, Lenum k ⊆ Lenum n ∩ Lenum m) :=
  RecDecidable₂.of_paired_zero_one_char primrec_LenumConsCharP
    (fun t => by have := LenumConsCharP_le_one t; omega)
    Lenum_cons_charP_eq_one_iff

/-- **The `{0,1}` intersection-equality characteristic** — same flat-`orBit` discipline as
`LenumConsChar`. -/
def LenumInterEqChar (n m k : ℕ) : ℕ :=
  mulBit (isPrefixChar m n) (listEqChar k n) + mulBit (isPrefixChar n m) (listEqChar k m)
    - mulBit (isPrefixChar m n) (listEqChar k n) * mulBit (isPrefixChar n m) (listEqChar k m)

private theorem mulBit_eq_zero_or_one {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) :
    mulBit a b = 0 ∨ mulBit a b = 1 := by
  have := mulBit_le_one ha hb; omega

theorem LenumInterEqChar_eq_one_iff (n m k : ℕ) :
    LenumInterEqChar n m k = 1 ↔
      (isPrefixChar m n = 1 ∧ decodeList k = decodeList n) ∨
      (isPrefixChar n m = 1 ∧ decodeList k = decodeList m) := by
  have hstep : LenumInterEqChar n m k = 1 ↔
      mulBit (isPrefixChar m n) (listEqChar k n) = 1 ∨
      mulBit (isPrefixChar n m) (listEqChar k m) = 1 := by
    unfold LenumInterEqChar
    rcases mulBit_eq_zero_or_one (isPrefixChar_le_one m n) (listEqChar_le_one k n) with ha | ha <;>
      rcases mulBit_eq_zero_or_one (isPrefixChar_le_one n m) (listEqChar_le_one k m) with hb | hb <;>
        simp [ha, hb]
  rw [hstep, mulBit_eq_one_iff, mulBit_eq_one_iff, listEqChar_eq_one_iff, listEqChar_eq_one_iff]

theorem LenumInterEqChar_le_one (n m k : ℕ) : LenumInterEqChar n m k ≤ 1 := by
  unfold LenumInterEqChar
  rcases mulBit_eq_zero_or_one (isPrefixChar_le_one m n) (listEqChar_le_one k n) with ha | ha <;>
    rcases mulBit_eq_zero_or_one (isPrefixChar_le_one n m) (listEqChar_le_one k m) with hb | hb <;>
      simp [ha, hb]

theorem primrec_LenumInterEqChar :
    Nat.Primrec (fun t => LenumInterEqChar t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2) := by
  have hn : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have hk : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) := Nat.Primrec.right.comp Nat.Primrec.right
  have hpmn : Nat.Primrec (fun t : ℕ => isPrefixChar t.unpair.2.unpair.1 t.unpair.1) :=
    (primrec_isPrefixChar.comp (Nat.Primrec.pair hm hn)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hpnm : Nat.Primrec (fun t : ℕ => isPrefixChar t.unpair.1 t.unpair.2.unpair.1) :=
    (primrec_isPrefixChar.comp (Nat.Primrec.pair hn hm)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hekn : Nat.Primrec (fun t : ℕ => listEqChar t.unpair.2.unpair.2 t.unpair.1) :=
    (primrec_listEqChar.comp (Nat.Primrec.pair hk hn)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hekm : Nat.Primrec (fun t : ℕ => listEqChar t.unpair.2.unpair.2 t.unpair.2.unpair.1) :=
    (primrec_listEqChar.comp (Nat.Primrec.pair hk hm)).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have ha : Nat.Primrec (fun t : ℕ => mulBit (isPrefixChar t.unpair.2.unpair.1 t.unpair.1)
      (listEqChar t.unpair.2.unpair.2 t.unpair.1)) :=
    (primrec_mulBit.comp (Nat.Primrec.pair hpmn hekn)).of_eq fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hb : Nat.Primrec (fun t : ℕ => mulBit (isPrefixChar t.unpair.1 t.unpair.2.unpair.1)
      (listEqChar t.unpair.2.unpair.2 t.unpair.2.unpair.1)) :=
    (primrec_mulBit.comp (Nat.Primrec.pair hpnm hekm)).of_eq fun t => by simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_sub₂ (primrec_add₂ ha hb) (primrec_mul₂ ha hb)).of_eq fun t => by
    simp only [LenumInterEqChar]

/-- Named-function packaging of `LenumInterEqChar` on `Nat.pair (Nat.pair)`-coded triples (same
rationale as `LenumSubsetChar`/`LenumConsCharP` above). -/
def LenumInterEqCharP (t : ℕ) : ℕ :=
  LenumInterEqChar t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2

theorem primrec_LenumInterEqCharP : Nat.Primrec LenumInterEqCharP :=
  primrec_LenumInterEqChar.of_eq fun t => by simp only [LenumInterEqCharP]

theorem LenumInterEqCharP_le_one (t : ℕ) : LenumInterEqCharP t ≤ 1 :=
  LenumInterEqChar_le_one _ _ _

theorem Lenum_interEq_charP_eq_one_iff (n m k : ℕ) :
    Lenum n ∩ Lenum m = Lenum k ↔ LenumInterEqCharP (Nat.pair n (Nat.pair m k)) = 1 := by
  unfold LenumInterEqCharP
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [LenumInterEqChar_eq_one_iff]
  exact Lenum_interEq_iff n m k

/-- **7.1(i) — `Xₙ ∩ Xₘ = X_k` is recursively decidable.** -/
theorem Lenum_interEq_computable : RecDecidable₃ (fun n m k => Lenum n ∩ Lenum m = Lenum k) :=
  RecDecidable₃.of_triple_zero_one_char primrec_LenumInterEqCharP
    (fun t => by have := LenumInterEqCharP_le_one t; omega)
    Lenum_interEq_charP_eq_one_iff

/-- The master neighbourhood is coded by `0` (`decodeList 0 = []`). -/
theorem Lenum_zero : Lenum 0 = Set.univ := by unfold Lenum; rw [decodeList_zero]; rfl

/-! ### The primitive-recursive intersection function

Whenever `Lenum n, Lenum m` are consistent (one is nested inside the other), their intersection
is simply the more specific of the two: `Lenum n` if `Lenum n ⊆ Lenum m` (i.e. `isPrefixChar m n =
1`), else `Lenum m`. `selectFn` (from `Recursive.lean`) packages this `{0,1}`-driven choice as a
primitive-recursive arithmetic combinator. -/
def LenumInter (n m : ℕ) : ℕ := selectFn (isPrefixChar m n) n m

theorem primrec_LenumInter : Nat.Primrec (fun t => LenumInter t.unpair.1 t.unpair.2) :=
  (primrec_selectFn primrec_isPrefixChar_swap Nat.Primrec.left Nat.Primrec.right).of_eq
    fun t => by simp only [LenumInter]

theorem LenumInter_spec {n m : ℕ} (h : ∃ k, Lenum k ⊆ Lenum n ∩ Lenum m) :
    Lenum (LenumInter n m) = Lenum n ∩ Lenum m := by
  unfold LenumInter
  rcases isPrefixChar_eq_zero_or_one m n with h0 | h1
  · rw [h0, selectFn_zero]
    have hp : isPrefixChar n m = 1 := by
      rcases (Lenum_cons_iff n m).mp h with hp | hp
      · rw [h0] at hp; exact absurd hp (by decide)
      · exact hp
    exact (Set.inter_eq_right.mpr ((Lenum_subset_iff m n).mpr hp)).symm
  · rw [h1, selectFn_one]
    exact (Set.inter_eq_left.mpr ((Lenum_subset_iff n m).mpr h1)).symm

/-! ### `L` is effectively given -/

/-- **Exercise 7.24, first claim — `L` is effectively given.** The enumeration `Lenum` (indices
via `encodeList`/`decodeList`), Scott's two relations (`Lenum_interEq_computable`,
`Lenum_cons_computable`), the primitive-recursive intersection (`LenumInter`), and the master
index `0` (`Lenum_zero`) assemble into a `ComputablePresentation L`. -/
def Lpres : ComputablePresentation L where
  X := Lenum
  mem_X n := Lenum_mem n
  surj hY := Lenum_surj hY
  interEq_computable := Lenum_interEq_computable
  cons_computable := Lenum_cons_computable
  inter := LenumInter
  inter_primrec := primrec_LenumInter
  inter_spec h := LenumInter_spec h
  masterIdx := 0
  masterIdx_spec := Lenum_zero

/-- **Exercise 7.24 (i) — `L` is effectively given.** -/
theorem L_isEffectivelyGiven : L.IsEffectivelyGiven := ⟨Lpres⟩

/-! ## Exercise 7.24, second claim — `|L|` is the finite-or-infinite sequences

`toElement : Gamma → L.Element` sends a finite list `l` to the *principal* filter `↑(nbhd l)`
(Scott's finite elements), and an infinite stream `f` to the *limit* filter of its finite
prefixes (`streamElement`, an instance of Scott's `limitFamily`, Definition 1.6's prose).
`toElement_bijective` shows this identification is exact: injectivity is choice-free (finite vs.
finite is `nbhd_injective`; finite vs. infinite is separated by `HasMin`, "having a smallest
neighbourhood", which the finite elements have and the infinite ones provably don't;
infinite vs. infinite recovers `f` pointwise from its prefixes). Surjectivity genuinely needs
choice (build the infinite witness sequence one coordinate at a time; flagged below), matching
Scott's "**can be identified with**" (an existence claim, not a computable retraction). -/

/-- The length-`n` prefix of an infinite stream `f`: `finPrefix f n = [f 0, …, f (n - 1)]`. -/
def finPrefix (f : ℕ → ℕ) (n : ℕ) : List ℕ := (List.range n).map f

@[simp] theorem finPrefix_zero (f : ℕ → ℕ) : finPrefix f 0 = [] := rfl

theorem finPrefix_succ (f : ℕ → ℕ) (n : ℕ) :
    finPrefix f (n + 1) = finPrefix f n ++ [f n] := by
  unfold finPrefix; rw [List.range_succ, List.map_append, List.map_singleton]

theorem finPrefix_length (f : ℕ → ℕ) (n : ℕ) : (finPrefix f n).length = n := by
  unfold finPrefix; rw [List.length_map, List.length_range]

theorem finPrefix_take (f : ℕ → ℕ) {n m : ℕ} (h : n ≤ m) :
    (finPrefix f m).take n = finPrefix f n := by
  unfold finPrefix; rw [← List.map_take, List.take_range, min_eq_left h]

theorem finPrefix_prefix_succ (f : ℕ → ℕ) (n : ℕ) : finPrefix f n <+: finPrefix f (n + 1) := by
  rw [finPrefix_succ]; exact List.prefix_append _ _

theorem finPrefix_prefix_of_le (f : ℕ → ℕ) {n m : ℕ} (h : n ≤ m) :
    finPrefix f n <+: finPrefix f m := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (finPrefix_prefix_succ f _)

/-- Longer prefixes give smaller (more specific) neighbourhoods. -/
theorem nbhd_finPrefix_antitone (f : ℕ → ℕ) {n m : ℕ} (h : n ≤ m) :
    nbhd (finPrefix f m) ⊆ nbhd (finPrefix f n) :=
  (nbhd_subset_iff _ _).mpr (finPrefix_prefix_of_le f h)

/-- **The element of `|L|` determined by an infinite sequence `f`**: the filter of neighbourhoods
containing some finite prefix of `f` — Scott's `limitFamily` (Definition 1.6's motivating prose),
specialized to `L`'s prefix chain `nbhd (finPrefix f ·)`. -/
def streamElement (f : ℕ → ℕ) : L.Element where
  mem Z := L.mem Z ∧ ∃ n, nbhd (finPrefix f n) ⊆ Z
  sub h := h.1
  master_mem := ⟨mem_nbhd [], 0, subset_rfl⟩
  inter_mem := by
    rintro X Y ⟨hXmem, n, hXsub⟩ ⟨hYmem, m, hYsub⟩
    have hn : nbhd (finPrefix f (max n m)) ⊆ X :=
      (nbhd_finPrefix_antitone f (le_max_left n m)).trans hXsub
    have hm : nbhd (finPrefix f (max n m)) ⊆ Y :=
      (nbhd_finPrefix_antitone f (le_max_right n m)).trans hYsub
    exact ⟨L.inter_mem hXmem hYmem (mem_nbhd _) (Set.subset_inter hn hm),
      max n m, Set.subset_inter hn hm⟩
  up_mem := by
    rintro X Y ⟨-, n, hn⟩ hYmem hXY
    exact ⟨hYmem, n, hn.trans hXY⟩

/-- **`toElement`: `Γ → |L|`**, realizing Scott's identification. -/
def toElement : Gamma → L.Element
  | .inl l => L.principal (mem_nbhd l)
  | .inr f => streamElement f

/-- A filter `x` **has a minimum neighbourhood** — the hallmark of Scott's *finite* elements. -/
def HasMin (x : L.Element) : Prop := ∃ X, x.mem X ∧ ∀ Y, x.mem Y → X ⊆ Y

theorem principal_hasMin (l : List ℕ) : HasMin (L.principal (mem_nbhd l)) :=
  ⟨nbhd l, ⟨mem_nbhd l, subset_rfl⟩, fun _ hY => hY.2⟩

/-- **The infinite elements have no minimum neighbourhood.** Given any witness `X ⊇ nbhd
(finPrefix f n)` in the filter, the *next* prefix neighbourhood is strictly smaller yet still in
the filter, so `X` cannot be the minimum. -/
theorem streamElement_not_hasMin (f : ℕ → ℕ) : ¬ HasMin (streamElement f) := by
  rintro ⟨X, ⟨-, n, hXsub⟩, hmin⟩
  have hmemsucc : (streamElement f).mem (nbhd (finPrefix f (n + 1))) := ⟨mem_nbhd _, n + 1, subset_rfl⟩
  have hle : X ⊆ nbhd (finPrefix f (n + 1)) := hmin _ hmemsucc
  have heq : nbhd (finPrefix f n) = nbhd (finPrefix f (n + 1)) :=
    Set.Subset.antisymm (hXsub.trans hle) (nbhd_finPrefix_antitone f (Nat.le_succ n))
  have hlen := congrArg List.length (nbhd_injective heq)
  rw [finPrefix_length, finPrefix_length] at hlen
  omega

/-- **Prefixes match on the nose whenever the stream elements agree.** -/
theorem finPrefix_eq_of_streamElement_eq {f₁ f₂ : ℕ → ℕ} (heq : streamElement f₁ = streamElement f₂) :
    ∀ n, finPrefix f₁ n = finPrefix f₂ n := by
  intro n
  have hmem1 : (streamElement f₁).mem (nbhd (finPrefix f₁ n)) := ⟨mem_nbhd _, n, subset_rfl⟩
  rw [heq] at hmem1
  obtain ⟨-, m, hm⟩ := hmem1
  have hpre : finPrefix f₁ n <+: finPrefix f₂ m := (nbhd_subset_iff _ _).mp hm
  have hlen : n ≤ m := by
    have hl := hpre.length_le; rwa [finPrefix_length, finPrefix_length] at hl
  have hpre' : finPrefix f₁ n = (finPrefix f₂ m).take (finPrefix f₁ n).length :=
    List.prefix_iff_eq_take.mp hpre
  rw [finPrefix_length] at hpre'
  rw [hpre', finPrefix_take f₂ hlen]

/-- **`streamElement` is injective**: two streams agreeing on every finite prefix agree
everywhere. -/
theorem streamElement_injective : Function.Injective streamElement := by
  intro f₁ f₂ heq
  have hpre := finPrefix_eq_of_streamElement_eq heq
  funext n
  have h1 := hpre (n + 1)
  rw [finPrefix_succ, finPrefix_succ, hpre n] at h1
  simpa using List.append_cancel_left h1

/-- **`toElement` is injective** (Exercise 7.24, second claim, uniqueness half). Finite vs. finite
is `nbhd_injective`; the two mixed cases are separated by `HasMin`; infinite vs. infinite is
`streamElement_injective`. -/
theorem toElement_injective : Function.Injective toElement := by
  rintro (l₁ | f₁) (l₂ | f₂) heq
  · exact congrArg Sum.inl
      (nbhd_injective (principal_injective (V := L) (mem_nbhd l₁) (mem_nbhd l₂) heq))
  · have heq' : L.principal (mem_nbhd l₁) = streamElement f₂ := heq
    exact absurd (heq' ▸ principal_hasMin l₁) (streamElement_not_hasMin f₂)
  · have heq' : streamElement f₁ = L.principal (mem_nbhd l₂) := heq
    exact absurd (principal_hasMin l₂) (heq' ▸ streamElement_not_hasMin f₁)
  · exact congrArg Sum.inr (streamElement_injective heq)

/-! ### Surjectivity (uses choice to build the witness stream, coordinate by coordinate) -/

/-- If `l ++ [i] <+: l'` fails for every `i`, then... (helper): a list strictly longer than a
prefix of it extends by *some* single element first. -/
theorem exists_cons_prefix_of_prefix_of_length_lt {l l' : List ℕ} (h : l <+: l')
    (hlt : l.length < l'.length) : ∃ i, l ++ [i] <+: l' := by
  obtain ⟨r, hr⟩ := h
  cases r with
  | nil => simp [← hr] at hlt
  | cons i r' => exact ⟨i, r', by rw [← hr]; simp⟩

/-- **One-step extension exists whenever `x` has no minimum.** If `x.mem (nbhd l)` and `x` has no
smallest neighbourhood, some length-`(l.length + 1)` extension `l ++ [i]` is also in `x`: pick any
`Y ∈ x.mem` witnessing that `nbhd l` is not the minimum (`hx`), which — being nested with `nbhd l`
(disjointness is impossible, `x.inter_mem` would force `L.mem ∅`) and *not* containing it — is a
strictly smaller neighbourhood `nbhd l' ⊊ nbhd l`; the first new list entry of `l'` past `l` is the
witness `i`. -/
theorem exists_extend_of_not_hasMin {x : L.Element} (hx : ¬ HasMin x) {l : List ℕ}
    (hl : x.mem (nbhd l)) : ∃ i, x.mem (nbhd (l ++ [i])) := by
  have hex : ∃ Y, x.mem Y ∧ ¬ nbhd l ⊆ Y := by
    by_contra hc; push Not at hc; exact hx ⟨nbhd l, hl, hc⟩
  obtain ⟨Y, hYmem, hnsub⟩ := hex
  obtain ⟨l', rfl⟩ := x.sub hYmem
  rcases L_nestedOrDisjoint (mem_nbhd l) (mem_nbhd l') with hsub | hsub | hdisj
  · exact absurd hsub hnsub
  · have hpre : l <+: l' := (nbhd_subset_iff l' l).mp hsub
    have hne : l ≠ l' := by rintro rfl; exact hnsub subset_rfl
    have hlt : l.length < l'.length :=
      lt_of_le_of_ne hpre.length_le (fun heqlen => hne (hpre.eq_of_length heqlen))
    obtain ⟨i, hi⟩ := exists_cons_prefix_of_prefix_of_length_lt hpre hlt
    exact ⟨i, x.up_mem hYmem (mem_nbhd _) ((nbhd_subset_iff l' (l ++ [i])).mpr hi)⟩
  · exfalso
    have hxmem : x.mem (nbhd l ∩ nbhd l') := x.inter_mem hl hYmem
    rw [hdisj] at hxmem
    obtain ⟨l'', hl''⟩ := x.sub hxmem
    exact (nbhd_nonempty l'').ne_empty hl''.symm

/-- **Choice-built data**: the length-`n` list `x.mem`s, together with the invariant, by iterating
`exists_extend_of_not_hasMin`. This is the one genuinely non-constructive step (`Classical.choose`
picking a witness coordinate at every stage), unavoidable for a *general* filter `x` (no
computability is assumed of `x` at this point in the exercise). -/
noncomputable def buildData (x : L.Element) (hx : ¬ HasMin x) :
    ∀ n : ℕ, {l : List ℕ // x.mem (nbhd l) ∧ l.length = n} :=
  fun n =>
    Nat.rec (⟨[], x.master_mem, rfl⟩ : {l : List ℕ // x.mem (nbhd l) ∧ l.length = 0})
      (fun n prev =>
        ⟨prev.1 ++ [Classical.choose (exists_extend_of_not_hasMin hx prev.2.1)],
          Classical.choose_spec (exists_extend_of_not_hasMin hx prev.2.1),
          by rw [List.length_append, List.length_singleton, prev.2.2]⟩)
      n

/-- **`toStream x hx`: the witness infinite sequence for a min-free filter `x`.** -/
noncomputable def toStream (x : L.Element) (hx : ¬ HasMin x) (n : ℕ) : ℕ :=
  Classical.choose (exists_extend_of_not_hasMin hx (buildData x hx n).2.1)

theorem buildData_succ (x : L.Element) (hx : ¬ HasMin x) (n : ℕ) :
    (buildData x hx (n + 1)).1 = (buildData x hx n).1 ++ [toStream x hx n] := rfl

theorem buildData_eq_finPrefix (x : L.Element) (hx : ¬ HasMin x) :
    ∀ n, (buildData x hx n).1 = finPrefix (toStream x hx) n
  | 0 => rfl
  | n + 1 => by rw [buildData_succ, finPrefix_succ, buildData_eq_finPrefix x hx n]

theorem mem_nbhd_finPrefix_toStream (x : L.Element) (hx : ¬ HasMin x) (n : ℕ) :
    x.mem (nbhd (finPrefix (toStream x hx) n)) :=
  buildData_eq_finPrefix x hx n ▸ (buildData x hx n).2.1

/-- **Every neighbourhood `Z ∈ x` contains some sufficiently deep prefix.** `Z = nbhd l` for some
`l` (`x.sub`), and comparing `nbhd l` against the (unboundedly long) chain
`nbhd (finPrefix (toStream x hx) n)` — nested, not disjoint, by the same
`x.inter_mem`/`L_nestedOrDisjoint` argument as `exists_extend_of_not_hasMin` — forces `l` itself to
be a prefix of the chain once `n > l.length` (the chain entry is then too long to be *the* shorter
side). Together with `mem_nbhd_finPrefix_toStream` this gives `streamElement (toStream x hx) = x`
(used directly in `toElement_surjective`). -/
theorem exists_finPrefix_subset_of_mem (x : L.Element) (hx : ¬ HasMin x) {Z : Set Gamma}
    (hZ : x.mem Z) : ∃ n, nbhd (finPrefix (toStream x hx) n) ⊆ Z := by
  obtain ⟨l, rfl⟩ := x.sub hZ
  refine ⟨l.length + 1, ?_⟩
  set n := l.length + 1
  have hn : x.mem (nbhd (finPrefix (toStream x hx) n)) := mem_nbhd_finPrefix_toStream x hx n
  have hinter := x.inter_mem hZ hn
  rcases L_nestedOrDisjoint (mem_nbhd l) (mem_nbhd (finPrefix (toStream x hx) n)) with
    hsub | hsub | hdisj
  · -- nbhd l ⊆ nbhd (finPrefix _ n): impossible by length once n = l.length + 1
    have hpre : finPrefix (toStream x hx) n <+: l := (nbhd_subset_iff l _).mp hsub
    have := hpre.length_le
    rw [finPrefix_length] at this
    omega
  · exact hsub
  · exfalso
    rw [hdisj] at hinter
    obtain ⟨l', hl'⟩ := x.sub hinter
    exact (nbhd_nonempty l').ne_empty hl'.symm

/-- **`toElement` is surjective** (Exercise 7.24, second claim, existence half; uses
`Classical.choice` via `buildData`/`toStream` for the infinite case — see `buildData`'s docstring).
-/
theorem toElement_surjective : Function.Surjective toElement := by
  intro x
  by_cases hx : HasMin x
  · obtain ⟨X, hXmem, hXmin⟩ := hx
    obtain ⟨l, rfl⟩ := x.sub hXmem
    exact ⟨Sum.inl l, (eq_principal_of_isMin (V := L) x hXmem hXmin).symm⟩
  · exact ⟨Sum.inr (toStream x hx), by
      apply Element.ext
      intro Z
      constructor
      · rintro ⟨hZmem, n, hn⟩
        exact x.up_mem (mem_nbhd_finPrefix_toStream x hx n) hZmem hn
      · intro hZ
        exact ⟨x.sub hZ, exists_finPrefix_subset_of_mem x hx hZ⟩⟩

/-- **Exercise 7.24, second claim.** `|L|` (the domain elements `L.Element`) is exactly the type of
finite-or-infinite sequences of naturals `Γ`, via `toElement`. -/
theorem toElement_bijective : Function.Bijective toElement :=
  ⟨toElement_injective, toElement_surjective⟩

/-- **`Γ ≃ |L|`**, the promised identification (noncomputable: surjectivity used choice). -/
noncomputable def gammaEquivElement : Gamma ≃ L.Element :=
  Equiv.ofBijective toElement toElement_bijective

/-! ## Exercise 7.24, third claim — the connection between `B` and `L`

Scott's binary system `B` (`ExampleB.lean`) branches over `Bool = {0,1}` at each node
(`Σ* = ⋃_b {b} × Σ* ∪ {Λ}`); `L` branches over all of `ℕ` (`Γ = ⋃ᵢ {i} × Γ ∪ {*}`). **`L` is `B`
generalized from `2`-ary to `ℕ`-ary branching** — concretely, digit-wise embedding the bits `0, 1`
as the naturals `0, 1` identifies `B` with the sub-system of `L` consisting of addresses built from
only the two digits `{0, 1}`. `embStr_prefix_iff`/`cone_subset_cone_iff_nbhd_embStr` make this
precise: the embedding `embStr : Σ* → List ℕ` is an order-embedding of the *prefix* posets, hence
(via `nbhd_subset_iff`/`cone_subset_cone`) of the neighbourhood-inclusion posets, hence (via
`principal_le_iff`) of `|B|`'s finite elements into `|L|`'s (`sigmaBot_le_iff_toElement_inl_embStr`).
The same digit-wise embedding on infinite streams (`ℕ → Bool ↪ ℕ → ℕ`) identifies Scott's *infinite*
binary sequences with the `ℕ → ℕ`-branch of `Γ` whose values happen to lie in `{0, 1}`, by the same
argument as `toElement`'s `Sum.inr` case — `B`'s domain `|B|` sits inside `|L|` as the sub-domain of
"binary-valued" LUCID sequences. -/

/-- The digit-wise embedding of a bit into `ℕ`: `false ↦ 0`, `true ↦ 1`. -/
def bitToNat (b : Bool) : ℕ := if b then 1 else 0

@[simp] theorem bitToNat_false : bitToNat false = 0 := rfl
@[simp] theorem bitToNat_true : bitToNat true = 1 := rfl

theorem bitToNat_injective : Function.Injective bitToNat := by
  intro a b h; cases a <;> cases b <;> simp_all [bitToNat]

/-- Embed a finite bit-string `Σ*` into a finite `ℕ`-list `Γ`'s finite part, digit by digit. -/
def embStr (σ : ExampleB.Str) : List ℕ := σ.map bitToNat

@[simp] theorem embStr_nil : embStr [] = [] := rfl

theorem embStr_cons (b : Bool) (s : ExampleB.Str) : embStr (b :: s) = bitToNat b :: embStr s := rfl

/-- **`embStr` is an order-embedding of the prefix posets** (`Σ*`'s into `List ℕ`'s): it respects
and reflects the initial-segment relation, since `bitToNat` is injective. -/
theorem embStr_prefix_iff : ∀ σ τ : ExampleB.Str, embStr σ <+: embStr τ ↔ σ <+: τ := by
  intro σ
  induction σ with
  | nil => intro τ; simp
  | cons b s ih =>
    intro τ
    cases τ with
    | nil => simp [embStr_cons]
    | cons c t =>
      rw [embStr_cons, embStr_cons, List.cons_prefix_cons, List.cons_prefix_cons,
        bitToNat_injective.eq_iff, ih t]

/-- `embStr` is injective. -/
theorem embStr_injective : Function.Injective embStr :=
  List.map_injective_iff.mpr bitToNat_injective

/-- **The connection between `B` and `L` (Exercise 7.24, third claim), at the neighbourhood
level.** `B`'s cone-inclusion order embeds into `L`'s nbhd-inclusion order via `embStr`: `σ`'s cone
sits inside `τ`'s cone in `B` iff `embStr σ`'s neighbourhood sits inside `embStr τ`'s in `L`. -/
theorem cone_subset_cone_iff_nbhd_embStr (σ τ : ExampleB.Str) :
    ExampleB.cone σ ⊆ ExampleB.cone τ ↔ nbhd (embStr σ) ⊆ nbhd (embStr τ) := by
  rw [ExampleB.cone_subset_cone, nbhd_subset_iff, embStr_prefix_iff]

/-- **The connection between `B` and `L`, at the level of finite elements.** `σ⊥ ⊑ τ⊥` in `|B|`
iff the corresponding `L`-elements (`toElement` applied to the embedded addresses) are `⊑`-related
in `|L|` — `B`'s finite elements embed order-isomorphically into `L`'s. -/
theorem sigmaBot_le_iff_toElement_inl_embStr (σ τ : ExampleB.Str) :
    ExampleB.sigmaBot σ ≤ ExampleB.sigmaBot τ ↔
      toElement (Sum.inl (embStr σ)) ≤ toElement (Sum.inl (embStr τ)) := by
  show ExampleB.sigmaBot σ ≤ ExampleB.sigmaBot τ ↔
      L.principal (mem_nbhd (embStr σ)) ≤ L.principal (mem_nbhd (embStr τ))
  rw [ExampleB.sigmaBot_le_iff, L.principal_le_iff, nbhd_subset_iff, embStr_prefix_iff]

/-! ## Exercise 7.24, fourth claim — LUCID combinators as computable maps

> Show that the combinators of LUCID can be construed as computable mappings of type
> `(L→T) → (L→T)` or of type `(L→T) × (L→T) → (L→T)`. Conclude that programs in LUCID define
> computable maps.

`T` is Example 1.2's three-point truth-value domain (`Example23.T`). We give it a computable
presentation `Tpres` (three neighbourhoods, enumerated by hand — the tiniest instance of Definition
7.1), then show two representative LUCID-style combinators are computable: pointwise **negation**
`notT : T → T` and pointwise **conjunction** `andT : T × T → T`. The general engine is the pair of
*lifting* theorems `postcompose`/`pointwiseBin`: any computable `h : V₁ → V₂` lifts to a computable
map `(L→V₁) → (L→V₂)` via `curry (h ∘ eval)` (Scott's `postcompose`), and any computable
`h : V₀ × V₁ → V₂` lifts to a computable `(L→V₀) × (L→V₁) → (L→V₂)` by evaluating both factors at
the same argument and applying `h`. Since `comp_isComputable`/`paired_isComputable` close
computability under composition and pairing (Proposition 7.3, Theorem 7.4), **every** LUCID program
built from such combinators — however deeply composed — again defines a computable map. This is the
choice-free core of the claim; assembling one concrete presentation of `(L → T)` to state it against
uses `Classical.choice` exactly once (to extract concrete characteristic functions from the existential
deciders of `Lpres`/`Tpres`), matching the classical bridge already used for `toElement_surjective`.
-/

open Scott1980.Neighborhood.Example12 (Token zero one)

/-! ### A computable presentation of `T` (Example 1.2's three-point domain) -/

/-- **`T`'s enumeration.** `0 ↦ Δ`, `1 ↦ {0}`, `2 ↦ {1}`, and every `n ≥ 2` collapses to `{1}` — we
only need *some* enumeration onto the three neighbourhoods, not a bijection. -/
def Tenum (n : ℕ) : Set Token :=
  match n with
  | 0 => Example12.master
  | 1 => zero
  | _ => one

@[simp] theorem Tenum_zero : Tenum 0 = Example12.master := rfl
@[simp] theorem Tenum_one : Tenum 1 = zero := rfl
@[simp] theorem Tenum_two : Tenum 2 = one := rfl

/-- `Tenum` only depends on `n` through `min n 2`. -/
theorem Tenum_eq_canon (n : ℕ) : Tenum n = Tenum (min n 2) := by
  rcases n with _ | _ | n
  · rfl
  · rfl
  · show one = Tenum (min (n + 2) 2)
    rw [show min (n + 2) 2 = 2 from by omega]
    rfl

theorem Tenum_mem (n : ℕ) : Example23.T.mem (Tenum n) := by
  rcases n with _ | _ | n
  · exact Example12.mem_master
  · exact Example12.mem_zero
  · exact Example12.mem_one

theorem Tenum_surj {Y : Set Token} (hY : Example23.T.mem Y) : ∃ n, Tenum n = Y := by
  rcases (Example12.mem_iff Y).mp hY with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

/-- `Tenum` never hits `∅` (it always lands on a genuine `T`-neighbourhood, and `∅` is not one). -/
theorem Tenum_ne_empty (n : ℕ) : Tenum n ≠ (∅ : Set Token) := by
  intro h
  exact Example12.not_mem_empty (h ▸ Tenum_mem n)

private theorem master_ne_zero_T : Example12.master ≠ zero := by
  intro h
  have h1 : (1 : Token) ∈ Example12.master := by simp [Example12.master]
  rw [h] at h1; simp [zero] at h1

private theorem master_ne_one_T : Example12.master ≠ one := by
  intro h
  have h1 : (0 : Token) ∈ Example12.master := by simp [Example12.master]
  rw [h] at h1; simp [one] at h1

private theorem zero_ne_one_T : zero ≠ one := by
  intro h
  have h1 : (0 : Token) ∈ zero := by simp [zero]
  rw [h] at h1; simp [one] at h1

/-- `Tenum` is injective on its "canonical" range `{0, 1, 2}`. -/
theorem Tenum_injOn {a b : ℕ} (ha : a ≤ 2) (hb : b ≤ 2) (h : Tenum a = Tenum b) : a = b := by
  interval_cases a <;> interval_cases b <;>
    simp only [Tenum_zero, Tenum_one, Tenum_two] at h <;>
    first
      | rfl
      | exact absurd h master_ne_zero_T
      | exact absurd h.symm master_ne_zero_T
      | exact absurd h master_ne_one_T
      | exact absurd h.symm master_ne_one_T
      | exact absurd h zero_ne_one_T
      | exact absurd h.symm zero_ne_one_T

private theorem zero_inter_one_T : zero ∩ one = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [zero, one]

private theorem one_inter_zero_T : one ∩ zero = (∅ : Set Token) := by
  ext t; fin_cases t <;> simp [zero, one]

/-- **The intersection code.** `TinterCode a b` names the intersection `Tenum a ∩ Tenum b` when it
is a `T`-neighbourhood (`a = 0`, `b = 0`, or `a = b`), and is the junk value `3` (never `≤ 2`, hence
never named by `Tenum`'s canonical range) exactly when the intersection is inconsistent
(`{0} ∩ {1} = ∅`). -/
def TinterCode (a b : ℕ) : ℕ := if a = 0 then b else if b = 0 then a else if a = b then a else 3

theorem Tenum_inter_eq {a b : ℕ} (ha : a ≤ 2) (hb : b ≤ 2) :
    Tenum a ∩ Tenum b = if a = 0 then Tenum b else if b = 0 then Tenum a
      else if a = b then Tenum a else (∅ : Set Token) := by
  interval_cases a <;> interval_cases b <;>
    simp [Tenum, Example12.master, Set.univ_inter, Set.inter_univ, Set.inter_self,
      zero_inter_one_T, one_inter_zero_T]

theorem Tenum_interEq_iff {a b c : ℕ} (ha : a ≤ 2) (hb : b ≤ 2) (hc : c ≤ 2) :
    Tenum a ∩ Tenum b = Tenum c ↔ TinterCode a b = c := by
  rw [Tenum_inter_eq ha hb]
  unfold TinterCode
  split_ifs with h1 h2 h3
  · exact ⟨fun h => (Tenum_injOn hb hc h).symm ▸ rfl, fun h => h ▸ rfl⟩
  · exact ⟨fun h => (Tenum_injOn ha hc h).symm ▸ rfl, fun h => h ▸ rfl⟩
  · exact ⟨fun h => (Tenum_injOn ha hc h).symm ▸ rfl, fun h => h ▸ rfl⟩
  · exact ⟨fun h => absurd h.symm (Tenum_ne_empty c), fun h => absurd h.symm (by omega)⟩

/-- Same characterization, restated for arbitrary `n, m, k` via the `min · 2` canonicalization. -/
theorem Tenum_interEq_iff' (n m k : ℕ) :
    Tenum n ∩ Tenum m = Tenum k ↔ TinterCode (min n 2) (min m 2) = min k 2 := by
  rw [Tenum_eq_canon n, Tenum_eq_canon m, Tenum_eq_canon k,
    Tenum_interEq_iff (Nat.min_le_right n 2) (Nat.min_le_right m 2) (Nat.min_le_right k 2)]

/-- `TeqChar a b = 1` decides `a = b` (truncated-subtraction trick, primitive recursive). -/
def TeqChar (a b : ℕ) : ℕ := isZero ((a - b) + (b - a))

theorem TeqChar_eq_one_iff (a b : ℕ) : TeqChar a b = 1 ↔ a = b := by
  unfold TeqChar isZero; omega

theorem primrec_TeqChar {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => TeqChar (f n) (g n)) :=
  (primrec_isZero.comp (primrec_add₂ (primrec_sub₂ hf hg) (primrec_sub₂ hg hf))).of_eq
    fun _ => rfl

theorem primrec_TinterCode {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => TinterCode (f n) (g n)) := by
  have heq : Nat.Primrec (fun n => TeqChar (f n) (g n)) := primrec_TeqChar hf hg
  have hz1 := primrec_selectFn heq hf (Nat.Primrec.const 3)
  have hz2 := primrec_selectFn (primrec_isZero.comp hg) hf hz1
  refine (primrec_selectFn (primrec_isZero.comp hf) hg hz2).of_eq fun n => ?_
  unfold TinterCode TeqChar
  by_cases h0 : f n = 0
  · rw [if_pos h0, h0, isZero]; simp
  · rw [if_neg h0]
    have hz0 : isZero (f n) = 0 := by unfold isZero; omega
    rw [hz0, selectFn_zero]
    by_cases h1 : g n = 0
    · rw [if_pos h1, h1, isZero]; simp
    · rw [if_neg h1]
      have hz0' : isZero (g n) = 0 := by unfold isZero; omega
      rw [hz0', selectFn_zero]
      by_cases h2 : f n = g n
      · have : isZero ((f n - g n) + (g n - f n)) = 1 := by unfold isZero; omega
        rw [if_pos h2, this, selectFn_one]
      · have : isZero ((f n - g n) + (g n - f n)) = 0 := by unfold isZero; omega
        rw [if_neg h2, this, selectFn_zero]

/-- **The `{0,1}` intersection-equality characteristic for `T`** (Scott's relation (i)). -/
theorem Tpres_interEq_computable : RecDecidable₃ (fun n m k => Tenum n ∩ Tenum m = Tenum k) := by
  have ha : Nat.Primrec (fun t : ℕ => TinterCode (min t.unpair.1 2) (min t.unpair.2.unpair.1 2)) :=
    primrec_TinterCode (primrec_min Nat.Primrec.left (Nat.Primrec.const 2))
      (primrec_min (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 2))
  have hb : Nat.Primrec (fun t : ℕ => min t.unpair.2.unpair.2 2) :=
    primrec_min (Nat.Primrec.right.comp Nat.Primrec.right) (Nat.Primrec.const 2)
  exact RecDecidable.of_iff
    (fun t => Tenum_interEq_iff' t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2)
    (RecDecidable.natEq ha hb)

/-- `Tenum n ∩ Tenum m` is `Tenum (TinterCode ·)` when consistent, and `∅` exactly when
`TinterCode` hits the junk value `3`. -/
theorem Tenum_inter_eq_TinterCode' {a b : ℕ} (ha : a ≤ 2) (hb : b ≤ 2) :
    Tenum a ∩ Tenum b = if TinterCode a b = 3 then (∅ : Set Token) else Tenum (TinterCode a b) := by
  interval_cases a <;> interval_cases b <;>
    simp [Tenum, TinterCode, Example12.master, Set.univ_inter, Set.inter_univ, Set.inter_self,
      zero_inter_one_T, one_inter_zero_T]

theorem Tenum_inter_eq_TinterCode (n m : ℕ) :
    Tenum n ∩ Tenum m = if TinterCode (min n 2) (min m 2) = 3 then (∅ : Set Token)
      else Tenum (TinterCode (min n 2) (min m 2)) := by
  rw [Tenum_eq_canon n, Tenum_eq_canon m]
  exact Tenum_inter_eq_TinterCode' (Nat.min_le_right n 2) (Nat.min_le_right m 2)

theorem Tpres_cons_iff (n m : ℕ) :
    (∃ k, Tenum k ⊆ Tenum n ∩ Tenum m) ↔ TinterCode (min n 2) (min m 2) ≠ 3 := by
  rw [Tenum_inter_eq_TinterCode n m]
  constructor
  · rintro ⟨k, hk⟩ hcontra
    rw [if_pos hcontra] at hk
    exact Tenum_ne_empty k (Set.subset_empty_iff.mp hk)
  · intro hne
    rw [if_neg hne]
    exact ⟨TinterCode (min n 2) (min m 2), subset_rfl⟩

/-- **The `{0,1}` consistency characteristic for `T`** (Scott's relation (ii)): `∃ k, Xₖ ⊆ Xₙ ∩ Xₘ`
holds iff `Xₙ ∩ Xₘ` is itself a `T`-neighbourhood, i.e. `TinterCode` did not hit the junk value `3`. -/
theorem Tpres_cons_computable : RecDecidable₂ (fun n m => ∃ k, Tenum k ⊆ Tenum n ∩ Tenum m) := by
  have ha : Nat.Primrec (fun t : ℕ => TinterCode (min t.unpair.1 2) (min t.unpair.2 2)) :=
    primrec_TinterCode (primrec_min Nat.Primrec.left (Nat.Primrec.const 2))
      (primrec_min Nat.Primrec.right (Nat.Primrec.const 2))
  have hne : RecDecidable (fun t : ℕ => TinterCode (min t.unpair.1 2) (min t.unpair.2 2) ≠ 3) :=
    (RecDecidable.natEq ha (Nat.Primrec.const 3)).not
  exact RecDecidable.of_iff (fun t => Tpres_cons_iff t.unpair.1 t.unpair.2) hne

/-- **`T` is effectively given**, via the hand-built enumeration `Tenum`. The presentation's
`inter`/`masterIdx` fields reuse `TinterCode`/`0` (both concrete, no search required, since `T`'s
finiteness makes the intersection function immediate from the case analysis above). -/
def Tpres : ComputablePresentation Example23.T where
  X := Tenum
  mem_X := Tenum_mem
  surj := Tenum_surj
  interEq_computable := Tpres_interEq_computable
  cons_computable := Tpres_cons_computable
  inter n m := TinterCode (min n 2) (min m 2)
  inter_primrec :=
    (primrec_TinterCode (primrec_min Nat.Primrec.left (Nat.Primrec.const 2))
      (primrec_min Nat.Primrec.right (Nat.Primrec.const 2))).of_eq fun _ => rfl
  inter_spec {n m} h := by
    rw [Tenum_inter_eq_TinterCode n m, if_neg ((Tpres_cons_iff n m).mp h)]
  masterIdx := 0
  masterIdx_spec := rfl

theorem T_isEffectivelyGiven : Example23.T.IsEffectivelyGiven := ⟨Tpres⟩

/-! ### `notT` — pointwise negation on `T`, as a computable map -/

private theorem eq_master_of_master_subset {Y : Set Token} (h : Example12.master ⊆ Y) :
    Y = Example12.master := (Set.univ_subset_iff.mp h : Y = Set.univ)

/-- **Among `T`'s three neighbourhoods, `X' ⊆ X` forces `X' = X` or `X = Δ`.** (`Δ` is the only
non-trivial containee since `{0}`, `{1}` are incomparable singletons.) -/
theorem subset_iff_eq_or_eq_master {X' X : Set Token} (hX' : Example23.T.mem X')
    (hX : Example23.T.mem X) (h : X' ⊆ X) : X' = X ∨ X = Example12.master := by
  rcases (Example12.mem_iff X).mp hX with rfl | rfl | rfl
  · exact Or.inr rfl
  · refine Or.inl ?_
    rcases (Example12.mem_iff X').mp hX' with rfl | rfl | rfl
    · exact absurd (show (1 : Token) ∈ zero from h (by simp [Example12.master])) (by simp [zero])
    · rfl
    · exact absurd (show (1 : Token) ∈ zero from h (by simp [one])) (by simp [zero])
  · refine Or.inl ?_
    rcases (Example12.mem_iff X').mp hX' with rfl | rfl | rfl
    · exact absurd (show (0 : Token) ∈ one from h (by simp [Example12.master])) (by simp [one])
    · exact absurd (show (0 : Token) ∈ one from h (by simp [zero])) (by simp [one])
    · rfl

/-- The pointwise negation function on `T`'s three neighbourhoods: swaps `{0}`/`{1}`, fixes `Δ`. -/
noncomputable def notFn (X : Set Token) : Set Token :=
  if X = zero then one else if X = one then zero else Example12.master

theorem notFn_master : notFn Example12.master = Example12.master := by
  unfold notFn; rw [if_neg master_ne_zero_T, if_neg master_ne_one_T]

theorem notFn_zero : notFn zero = one := by unfold notFn; rw [if_pos rfl]

theorem notFn_one : notFn one = zero := by
  unfold notFn; rw [if_neg (Ne.symm zero_ne_one_T), if_pos rfl]

theorem notFn_mem {X : Set Token} (hX : Example23.T.mem X) : Example23.T.mem (notFn X) := by
  rcases (Example12.mem_iff X).mp hX with rfl | rfl | rfl
  · rw [notFn_master]; exact Example12.mem_master
  · rw [notFn_zero]; exact Example12.mem_one
  · rw [notFn_one]; exact Example12.mem_zero

/-- **Pointwise negation on `T`**, as an approximable map: `X f Y ↔ mem X ∧ mem Y ∧ notFn X ⊆ Y`
(Scott's "step" pattern, turning the pointwise function `notFn` into a neighbourhood relation). -/
noncomputable def notT : ApproximableMap Example23.T Example23.T where
  rel X Y := Example23.T.mem X ∧ Example23.T.mem Y ∧ notFn X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨Example12.mem_master, Example12.mem_master, by
    show notFn Example12.master ⊆ Example12.master; rw [notFn_master]⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hsub⟩ ⟨_, hY', hsub'⟩
    exact ⟨hX, Example23.T.inter_mem hY hY' (notFn_mem hX) (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' Y Y' ⟨hX, hY, hsub⟩ hX'X hYY' hX' hY'
    refine ⟨hX', hY', ?_⟩
    rcases subset_iff_eq_or_eq_master hX' hX hX'X with heq | heq
    · rw [heq]; exact hsub.trans hYY'
    · rw [heq, notFn_master] at hsub
      have hY'master : Y' = Example12.master := eq_master_of_master_subset (hsub.trans hYY')
      rw [hY'master, Example12.master]; exact Set.subset_univ _

/-- `notCode c` names `notFn (Tenum c)` when `c ≤ 2`: `0 ↦ 0`, `1 ↦ 2`, `2 ↦ 1`. -/
def notCode (c : ℕ) : ℕ := if c = 1 then 2 else if c = 2 then 1 else 0

theorem primrec_notCode {f : ℕ → ℕ} (hf : Nat.Primrec f) : Nat.Primrec (fun n => notCode (f n)) := by
  refine (primrec_selectFn (primrec_TeqChar hf (Nat.Primrec.const 1)) (Nat.Primrec.const 2)
    (primrec_selectFn (primrec_TeqChar hf (Nat.Primrec.const 2)) (Nat.Primrec.const 1)
      (Nat.Primrec.const 0))).of_eq fun n => ?_
  unfold notCode
  by_cases h1 : f n = 1
  · have h1' : TeqChar (f n) 1 = 1 := by unfold TeqChar isZero; omega
    rw [if_pos h1, h1', selectFn_one]
  · have h1' : TeqChar (f n) 1 = 0 := by unfold TeqChar isZero; omega
    rw [if_neg h1, h1', selectFn_zero]
    by_cases h2 : f n = 2
    · have h2' : TeqChar (f n) 2 = 1 := by unfold TeqChar isZero; omega
      rw [if_pos h2, h2', selectFn_one]
    · have h2' : TeqChar (f n) 2 = 0 := by unfold TeqChar isZero; omega
      rw [if_neg h2, h2', selectFn_zero]

theorem notFn_Tenum (n : ℕ) : notFn (Tenum n) = Tenum (notCode (min n 2)) := by
  rw [Tenum_eq_canon n]
  have hc2 : min n 2 ≤ 2 := Nat.min_le_right n 2
  interval_cases (min n 2) <;> simp [Tenum, notCode, notFn_master, notFn_zero, notFn_one]

/-- **`notT` is a computable map** (relative to `Tpres` on both sides): its neighbourhood relation
`notFn (Xₙ) ⊆ Xₘ` reduces, via `notFn_Tenum`, to the *decidable* `Tpres`-inclusion relation
`X_{notCode (min n 2)} ⊆ Xₘ`, hence is recursively decidable — a fortiori r.e. -/
theorem notT_isComputable : IsComputableMap Tpres Tpres notT := by
  have hcomp : Nat.Primrec (fun t : ℕ => Nat.pair (notCode (min t.unpair.1 2)) t.unpair.2) :=
    (primrec_notCode (primrec_min Nat.Primrec.left (Nat.Primrec.const 2))).pair Nat.Primrec.right
  have hdec : RecDecidable₂ (fun n m => Tenum (notCode (min n 2)) ⊆ Tenum m) :=
    RecDecidable.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd]; rfl)
      (Tpres.incl_computable.comp hcomp)
  have hiff : ∀ n m, notT.rel (Tenum n) (Tenum m) ↔ Tenum (notCode (min n 2)) ⊆ Tenum m := by
    intro n m
    show (Example23.T.mem (Tenum n) ∧ Example23.T.mem (Tenum m) ∧ notFn (Tenum n) ⊆ Tenum m) ↔ _
    rw [notFn_Tenum]
    exact ⟨fun h => h.2.2, fun h => ⟨Tenum_mem n, Tenum_mem m, h⟩⟩
  have key : RecDecidable₂ (fun n m => notT.rel (Tenum n) (Tenum m)) :=
    RecDecidable.of_iff (fun t => hiff t.unpair.1 t.unpair.2) hdec
  exact key.re

/-! ### `andT` — pointwise (sequential/left-strict) conjunction on `T`, as a computable map -/

/-- **Sequential conjunction** on `T`'s neighbourhoods: `andFn X Y` is `Y` when `X` names `true`
(`zero`), the constant `false` (`one`) when `X` names `false` — regardless of `Y` — and `Δ` (no
information yet) otherwise. This is the standard *left-strict* `and`, matching `zero`/`one` naming
`true`/`false` (`Example23.trueElt = elemZero`, `Example23.falseElt = elemOne`). -/
noncomputable def andFn (X Y : Set Token) : Set Token :=
  if X = zero then Y else if X = one then one else Example12.master

theorem andFn_master (Y : Set Token) : andFn Example12.master Y = Example12.master := by
  unfold andFn; rw [if_neg master_ne_zero_T, if_neg master_ne_one_T]

theorem andFn_zero (Y : Set Token) : andFn zero Y = Y := by unfold andFn; rw [if_pos rfl]

theorem andFn_one (Y : Set Token) : andFn one Y = one := by
  unfold andFn; rw [if_neg (Ne.symm zero_ne_one_T), if_pos rfl]

theorem andFn_mem {X Y : Set Token} (hX : Example23.T.mem X) (hY : Example23.T.mem Y) :
    Example23.T.mem (andFn X Y) := by
  rcases (Example12.mem_iff X).mp hX with rfl | rfl | rfl
  · rw [andFn_master]; exact Example12.mem_master
  · rw [andFn_zero]; exact hY
  · rw [andFn_one]; exact Example12.mem_one

/-- **Pointwise (sequential) conjunction on `T`**, as a two-variable approximable mapping:
`X, Y f Z ↔ mem X ∧ mem Y ∧ mem Z ∧ andFn X Y ⊆ Z` (Scott's "step" pattern again). -/
noncomputable def andMap2 : ApproximableMap₂ Example23.T Example23.T Example23.T where
  rel X Y Z := Example23.T.mem X ∧ Example23.T.mem Y ∧ Example23.T.mem Z ∧ andFn X Y ⊆ Z
  rel_dom₀ h := h.1
  rel_dom₁ h := h.2.1
  rel_cod h := h.2.2.1
  master_rel := ⟨Example12.mem_master, Example12.mem_master, Example12.mem_master, by
    show andFn Example12.master Example12.master ⊆ Example12.master
    rw [andFn_master]⟩
  inter_right := by
    rintro X Y Z Z' ⟨hX, hY, hZ, hsub⟩ ⟨_, _, hZ', hsub'⟩
    exact ⟨hX, hY, Example23.T.inter_mem hZ hZ' (andFn_mem hX hY) (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' Y Y' Z Z' ⟨hX, hY, hZ, hsub⟩ hX'X hY'Y hZZ' hX' hY' hZ'
    refine ⟨hX', hY', hZ', ?_⟩
    rcases (Example12.mem_iff X).mp hX with rfl | rfl | rfl
    · rw [andFn_master] at hsub
      have hZ'master : Z' = Example12.master := eq_master_of_master_subset (hsub.trans hZZ')
      rw [hZ'master, Example12.master]; exact Set.subset_univ _
    · rw [andFn_zero] at hsub
      have hX'eq : X' = zero :=
        (subset_iff_eq_or_eq_master hX' Example12.mem_zero hX'X).resolve_right
          master_ne_zero_T.symm
      rw [hX'eq, andFn_zero]
      exact (hY'Y.trans hsub).trans hZZ'
    · rw [andFn_one] at hsub
      have hX'eq : X' = one :=
        (subset_iff_eq_or_eq_master hX' Example12.mem_one hX'X).resolve_right
          master_ne_one_T.symm
      rw [hX'eq, andFn_one]
      exact hsub.trans hZZ'

/-- **`andT`**, the joint approximable mapping `T × T → T` corresponding to `andMap2`
(Theorem 3.5's `ofMap₂`). -/
noncomputable def andT : ApproximableMap (prod Example23.T Example23.T) Example23.T :=
  ofMap₂ andMap2

/-- `andCode a b` names `andFn (Tenum a) (Tenum b)` when `a, b ≤ 2`: `andCode 0 b = 0`,
`andCode 1 b = b`, `andCode 2 b = 2`. -/
def andCode (a b : ℕ) : ℕ := if a = 1 then b else if a = 2 then 2 else 0

theorem primrec_andCode {f g : ℕ → ℕ} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (fun n => andCode (f n) (g n)) := by
  refine (primrec_selectFn (primrec_TeqChar hf (Nat.Primrec.const 1)) hg
    (primrec_selectFn (primrec_TeqChar hf (Nat.Primrec.const 2)) (Nat.Primrec.const 2)
      (Nat.Primrec.const 0))).of_eq fun n => ?_
  unfold andCode
  by_cases h1 : f n = 1
  · have h1' : TeqChar (f n) 1 = 1 := by unfold TeqChar isZero; omega
    rw [if_pos h1, h1', selectFn_one]
  · have h1' : TeqChar (f n) 1 = 0 := by unfold TeqChar isZero; omega
    rw [if_neg h1, h1', selectFn_zero]
    by_cases h2 : f n = 2
    · have h2' : TeqChar (f n) 2 = 1 := by unfold TeqChar isZero; omega
      rw [if_pos h2, h2', selectFn_one]
    · have h2' : TeqChar (f n) 2 = 0 := by unfold TeqChar isZero; omega
      rw [if_neg h2, h2', selectFn_zero]

theorem andFn_Tenum (n m : ℕ) :
    andFn (Tenum n) (Tenum m) = Tenum (andCode (min n 2) (min m 2)) := by
  rw [Tenum_eq_canon n, Tenum_eq_canon m]
  have hn2 : min n 2 ≤ 2 := Nat.min_le_right n 2
  have hm2 : min m 2 ≤ 2 := Nat.min_le_right m 2
  interval_cases (min n 2) <;> interval_cases (min m 2) <;>
    simp [Tenum, andCode, andFn_master, andFn_zero, andFn_one]

/-- **`andT` is a computable map** (relative to `prodPresentation Tpres Tpres` on the input side and
`Tpres` on the output side): its neighbourhood relation reduces, via `ofMap₂`'s unfolding and
`andFn_Tenum`, to the *decidable* `Tpres`-inclusion relation `X_{andCode (min n 2) (min m 2)} ⊆ Xₖ`,
hence is recursively decidable — a fortiori r.e. -/
theorem andT_isComputable : IsComputableMap (prodPresentation Tpres Tpres) Tpres andT := by
  have hcomp : Nat.Primrec (fun s : ℕ => Nat.pair
      (andCode (min s.unpair.1.unpair.1 2) (min s.unpair.1.unpair.2 2)) s.unpair.2) :=
    (primrec_andCode (primrec_min (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 2))
      (primrec_min (Nat.Primrec.right.comp Nat.Primrec.left) (Nat.Primrec.const 2))).pair
      Nat.Primrec.right
  have hdec : RecDecidable₂
      (fun t k => Tenum (andCode (min t.unpair.1 2) (min t.unpair.2 2)) ⊆ Tenum k) :=
    RecDecidable.of_iff (fun s => by simp only [unpair_pair_fst, unpair_pair_snd]; rfl)
      (Tpres.incl_computable.comp hcomp)
  have hiff : ∀ n m k, andT.rel (prodNbhd (Tenum n) (Tenum m)) (Tenum k) ↔
      Tenum (andCode (min n 2) (min m 2)) ⊆ Tenum k := by
    intro n m k
    have hstep : andT.rel (prodNbhd (Tenum n) (Tenum m)) (Tenum k) ↔
        andMap2.rel (Tenum n) (Tenum m) (Tenum k) := by
      show ((prod Example23.T Example23.T).mem (prodNbhd (Tenum n) (Tenum m)) ∧
        andMap2.rel (Sum.inl ⁻¹' prodNbhd (Tenum n) (Tenum m))
          (Sum.inr ⁻¹' prodNbhd (Tenum n) (Tenum m)) (Tenum k)) ↔ _
      rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
      exact and_iff_right (prod_mem_prodNbhd (Tenum_mem n) (Tenum_mem m))
    rw [hstep]
    show (Example23.T.mem (Tenum n) ∧ Example23.T.mem (Tenum m) ∧ Example23.T.mem (Tenum k) ∧
      andFn (Tenum n) (Tenum m) ⊆ Tenum k) ↔ _
    rw [andFn_Tenum n m]
    exact ⟨fun h => h.2.2.2, fun h => ⟨Tenum_mem n, Tenum_mem m, Tenum_mem k, h⟩⟩
  have key : RecDecidable₂
      (fun t k => andT.rel ((prodPresentation Tpres Tpres).X t) (Tpres.X k)) :=
    RecDecidable.of_iff (fun s => by
      show andT.rel ((prodPresentation Tpres Tpres).X s.unpair.1) (Tpres.X s.unpair.2) ↔ _
      rw [prodPresentation_X]
      exact hiff s.unpair.1.unpair.1 s.unpair.1.unpair.2 s.unpair.2) hdec
  exact key.re

/-! ### The general lifting engine: `postcompose` and `pointwiseBin`

Any computable `h : V₁ → V₂` lifts to a computable `(L → V₁) → (L → V₂)` (Scott's `postcompose`,
`curry (h ∘ eval)`), and any computable `h : V₀ × V₁ → V₂` lifts to a computable
`(L → V₀) × (L → V₁) → (L → V₂)` (`pointwiseBin`, evaluating both factors at the same argument and
applying `h`). Stating either against a *concrete* presentation of the relevant function space(s)
needs a bundle of characteristic functions for `funPresentation Lpres P`; `LFunData` packages
exactly that bundle, and `LFunData.ofPresentation` extracts one from an arbitrary
`P : ComputablePresentation V`, using `Classical.choice` exactly once per component presentation (to
pull concrete deciders out of `P.incl_computable`/`P.cons_computable`/`P.eq_computable`'s existentials
— the same classical bridge already used for `funSpace_isEffectivelyGiven`, just packaged so it can be
*named* and reused as data rather than immediately discharged into a `Prop` goal). -/

variable {β γ δ : Type*}

/-- The characteristic-function bundle needed to write down `funPresentation Lpres P` concretely:
`gN` for function-space consistency, `incl0`/`incl1` for `L`/`V`-inclusion, `eq1` for `V`-equality. -/
structure LFunData {V : NeighborhoodSystem β} (P : ComputablePresentation V) where
  gN : ℕ → ℕ
  incl0 : ℕ → ℕ
  incl1 : ℕ → ℕ
  eq1 : ℕ → ℕ
  hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf Lpres P (decodeList c))
    : Set (ApproximableMap L V)).Nonempty
  hgNp : Nat.Primrec gN
  hincl0 : ∀ s, incl0 s = 1 ↔ Lpres.X s.unpair.1 ⊆ Lpres.X s.unpair.2
  hincl0p : Nat.Primrec incl0
  hincl1 : ∀ s, incl1 s = 1 ↔ P.X s.unpair.1 ⊆ P.X s.unpair.2
  hincl1p : Nat.Primrec incl1
  heq1 : ∀ s, eq1 s = 1 ↔ P.X s.unpair.1 = P.X s.unpair.2
  heq1p : Nat.Primrec eq1

/-- The concrete `ComputablePresentation (L → V)` assembled from an `LFunData` bundle. -/
def LFunData.pres {V : NeighborhoodSystem β} {P : ComputablePresentation V} (d : LFunData P) :
    ComputablePresentation (funSpace L V) :=
  funPresentation Lpres P d.gN d.incl0 d.incl1 d.eq1 d.hgN d.hgNp d.hincl0 d.hincl0p
    d.hincl1 d.hincl1p d.heq1 d.heq1p

/-- **The one use of `Classical.choice` in this section.** Every `ComputablePresentation P` of a
`V` yields *some* `LFunData P`, by choosing concrete deciders out of `Lpres`'s and `P`'s existential
`incl_computable`/`cons_computable`/`eq_computable` witnesses. -/
noncomputable def LFunData.ofPresentation {V : NeighborhoodSystem β} (P : ComputablePresentation V) :
    LFunData P where
  gN := funConsChar Lpres P Lpres.cons_computable.choose P.cons_computable.choose
  incl0 := Lpres.incl_computable.choose
  incl1 := P.incl_computable.choose
  eq1 := P.eq_computable.choose
  hgN := funConsChar_spec Lpres P Lpres.cons_computable.choose P.cons_computable.choose
    (fun s => (Lpres.cons_computable.choose_spec.2 s).symm)
    (fun s => (P.cons_computable.choose_spec.2 s).symm)
  hgNp := primrec_funConsChar Lpres P Lpres.cons_computable.choose P.cons_computable.choose
    Lpres.cons_computable.choose_spec.1 P.cons_computable.choose_spec.1
  hincl0 := fun s => (Lpres.incl_computable.choose_spec.2 s).symm
  hincl0p := Lpres.incl_computable.choose_spec.1
  hincl1 := fun s => (P.incl_computable.choose_spec.2 s).symm
  hincl1p := P.incl_computable.choose_spec.1
  heq1 := fun s => (P.eq_computable.choose_spec.2 s).symm
  heq1p := P.eq_computable.choose_spec.1

/-- **`postcompose h`**: post-composing every `L`-indexed sequence `f : L → V₁` with `h`, i.e.
`f ↦ h ∘ f`. Built as `curry (h ∘ eval)`, following Scott. -/
def postcompose {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
    (h : ApproximableMap V₁ V₂) : ApproximableMap (funSpace L V₁) (funSpace L V₂) :=
  curry (h.comp (evalMap L V₁))

/-- **`postcompose` preserves computability.** If `h : V₁ → V₂` is computable, then so is
`postcompose h : (L → V₁) → (L → V₂)`, relative to any concrete function-space presentations built
from `LFunData` bundles: `eval` is computable (Theorem 7.5), composing with `h` stays computable
(Proposition 7.3), and `curry`-ing the result stays computable (Theorem 7.5 again). -/
theorem postcompose_isComputable {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
    {P₁ : ComputablePresentation V₁} {P₂ : ComputablePresentation V₂}
    (d₁ : LFunData P₁) (d₂ : LFunData P₂) {h : ApproximableMap V₁ V₂}
    (hh : IsComputableMap P₁ P₂ h) :
    IsComputableMap d₁.pres d₂.pres (postcompose h) := by
  have heval : IsComputableMap (prodPresentation d₁.pres Lpres) P₁ (evalMap L V₁) :=
    evalMap_isComputable Lpres P₁ d₁.gN d₁.incl0 d₁.incl1 d₁.eq1
      d₁.hgN d₁.hgNp d₁.hincl0 d₁.hincl0p d₁.hincl1 d₁.hincl1p d₁.heq1 d₁.heq1p
  exact curry_isComputable d₁.pres Lpres P₂ d₂.gN d₂.incl0 d₂.incl1 d₂.eq1
    d₂.hgN d₂.hgNp d₂.hincl0 d₂.hincl0p d₂.hincl1 d₂.hincl1p d₂.heq1 d₂.heq1p
    (comp_isComputable heval hh)

/-- The "extract `f`" projection out of the pointwise-binary domain `(L→V₀) × (L→V₁) × L`. -/
private def pwFst (V₀ : NeighborhoodSystem β) (V₁ : NeighborhoodSystem γ) :
    ApproximableMap (prod (prod (funSpace L V₀) (funSpace L V₁)) L) (funSpace L V₀) :=
  (proj₀ (funSpace L V₀) (funSpace L V₁)).comp (proj₀ (prod (funSpace L V₀) (funSpace L V₁)) L)

/-- The "extract `g`" projection out of the pointwise-binary domain. -/
private def pwSnd (V₀ : NeighborhoodSystem β) (V₁ : NeighborhoodSystem γ) :
    ApproximableMap (prod (prod (funSpace L V₀) (funSpace L V₁)) L) (funSpace L V₁) :=
  (proj₁ (funSpace L V₀) (funSpace L V₁)).comp (proj₀ (prod (funSpace L V₀) (funSpace L V₁)) L)

/-- The "extract the shared argument `x`" projection out of the pointwise-binary domain. -/
private def pwArg (V₀ : NeighborhoodSystem β) (V₁ : NeighborhoodSystem γ) :
    ApproximableMap (prod (prod (funSpace L V₀) (funSpace L V₁)) L) L :=
  proj₁ (prod (funSpace L V₀) (funSpace L V₁)) L

/-- **`pointwiseBin h`**: given `f : L → V₀`, `g : L → V₁`, produce the `L`-sequence
`x ↦ h(f x, g x)`. Built by evaluating both factors at the shared argument and applying `h`, then
`curry`-ing. -/
def pointwiseBin {V₀ : NeighborhoodSystem β} {V₁ : NeighborhoodSystem γ} {V₂ : NeighborhoodSystem δ}
    (h : ApproximableMap (prod V₀ V₁) V₂) :
    ApproximableMap (prod (funSpace L V₀) (funSpace L V₁)) (funSpace L V₂) :=
  curry (h.comp (paired
    ((evalMap L V₀).comp (paired (pwFst V₀ V₁) (pwArg V₀ V₁)))
    ((evalMap L V₁).comp (paired (pwSnd V₀ V₁) (pwArg V₀ V₁)))))

/-- **`pointwiseBin` preserves computability.** If `h : V₀ × V₁ → V₂` is computable, then so is
`pointwiseBin h : (L → V₀) × (L → V₁) → (L → V₂)`, by the same composition-closure argument as
`postcompose` (projections, pairing, `eval`, and `curry` are all computable). -/
theorem pointwiseBin_isComputable {V₀ : NeighborhoodSystem β} {V₁ : NeighborhoodSystem γ}
    {V₂ : NeighborhoodSystem δ} {P₀ : ComputablePresentation V₀} {P₁ : ComputablePresentation V₁}
    {P₂ : ComputablePresentation V₂} (d₀ : LFunData P₀) (d₁ : LFunData P₁) (d₂ : LFunData P₂)
    {h : ApproximableMap (prod V₀ V₁) V₂} (hh : IsComputableMap (prodPresentation P₀ P₁) P₂ h) :
    IsComputableMap (prodPresentation d₀.pres d₁.pres) d₂.pres (pointwiseBin h) := by
  have hπAB : IsComputableMap (prodPresentation (prodPresentation d₀.pres d₁.pres) Lpres)
      (prodPresentation d₀.pres d₁.pres) (proj₀ (prod (funSpace L V₀) (funSpace L V₁)) L) :=
    proj₀_isComputable (prodPresentation d₀.pres d₁.pres) Lpres
  have hπL : IsComputableMap (prodPresentation (prodPresentation d₀.pres d₁.pres) Lpres) Lpres
      (proj₁ (prod (funSpace L V₀) (funSpace L V₁)) L) :=
    proj₁_isComputable (prodPresentation d₀.pres d₁.pres) Lpres
  have hp0 : IsComputableMap (prodPresentation (prodPresentation d₀.pres d₁.pres) Lpres) d₀.pres
      (pwFst V₀ V₁) := comp_isComputable hπAB (proj₀_isComputable d₀.pres d₁.pres)
  have hp1 : IsComputableMap (prodPresentation (prodPresentation d₀.pres d₁.pres) Lpres) d₁.pres
      (pwSnd V₀ V₁) := comp_isComputable hπAB (proj₁_isComputable d₀.pres d₁.pres)
  have heval0 : IsComputableMap (prodPresentation (prodPresentation d₀.pres d₁.pres) Lpres) P₀
      ((evalMap L V₀).comp (paired (pwFst V₀ V₁) (pwArg V₀ V₁))) :=
    comp_isComputable (paired_isComputable hp0 hπL)
      (evalMap_isComputable Lpres P₀ d₀.gN d₀.incl0 d₀.incl1 d₀.eq1
        d₀.hgN d₀.hgNp d₀.hincl0 d₀.hincl0p d₀.hincl1 d₀.hincl1p d₀.heq1 d₀.heq1p)
  have heval1 : IsComputableMap (prodPresentation (prodPresentation d₀.pres d₁.pres) Lpres) P₁
      ((evalMap L V₁).comp (paired (pwSnd V₀ V₁) (pwArg V₀ V₁))) :=
    comp_isComputable (paired_isComputable hp1 hπL)
      (evalMap_isComputable Lpres P₁ d₁.gN d₁.incl0 d₁.incl1 d₁.eq1
        d₁.hgN d₁.hgNp d₁.hincl0 d₁.hincl0p d₁.hincl1 d₁.hincl1p d₁.heq1 d₁.heq1p)
  exact curry_isComputable (prodPresentation d₀.pres d₁.pres) Lpres P₂ d₂.gN d₂.incl0 d₂.incl1
    d₂.eq1 d₂.hgN d₂.hgNp d₂.hincl0 d₂.hincl0p d₂.hincl1 d₂.hincl1p d₂.heq1 d₂.heq1p
    (comp_isComputable (paired_isComputable heval0 heval1) hh)

/-! ### Conclusion: the LUCID combinators `notT`/`andT` lift to computable `(L → T)` maps

One concrete choice of `LFunData Tpres` (`LTdata`, via `Classical.choice`) presents `(L → T)`
(`LTpres`); `notT`/`andT`'s computability (already established, choice-free) transports through
`postcompose`/`pointwiseBin` to give computable maps of exactly Scott's two stated types,
`(L→T) → (L→T)` and `(L→T) × (L→T) → (L→T)`. Since `comp_isComputable`/`paired_isComputable` close
computability under composition and pairing, **any** LUCID program built from these (and their kin,
built the same way from any other computable `T`-combinator) — however deeply composed — again
defines a computable map on `(L→T)`; `deMorganT_isComputable` below composes both lifted combinators
together (`¬(¬f ∧ ¬g)`, De Morgan's law for the sequential `and`) as a concrete witness of this
closure. -/

/-- The one concrete presentation of `(L → T)` used to state the LUCID combinators' computability. -/
noncomputable def LTdata : LFunData Tpres := LFunData.ofPresentation Tpres

/-- **The computable presentation of `(L → T)`.** -/
noncomputable def LTpres : ComputablePresentation (funSpace L Example23.T) := LTdata.pres

/-- **Exercise 7.24, fourth claim, `notT` case.** LUCID's pointwise negation lifts to a computable
map of type `(L→T) → (L→T)`. -/
theorem notT_lifted_isComputable : IsComputableMap LTpres LTpres (postcompose notT) :=
  postcompose_isComputable LTdata LTdata notT_isComputable

/-- **Exercise 7.24, fourth claim, `andT` case.** LUCID's pointwise (sequential) conjunction lifts to
a computable map of type `(L→T) × (L→T) → (L→T)`. -/
theorem andT_lifted_isComputable :
    IsComputableMap (prodPresentation LTpres LTpres) LTpres (pointwiseBin andT) :=
  pointwiseBin_isComputable LTdata LTdata LTdata andT_isComputable

/-- **A deeper LUCID program is still computable.** `deMorganT f g := ¬(¬f ∧ ¬g)` on `(L→T)`,
built by composing/pairing the two lifted combinators above (De Morgan's law for the sequential
`and`); it is computable purely by the closure lemmas `comp_isComputable`/`paired_isComputable`,
**with no fresh recursion-theoretic argument needed** — exactly Scott's "conclude that programs in
LUCID define computable maps." -/
theorem deMorganT_isComputable :
    IsComputableMap (prodPresentation LTpres LTpres) LTpres
      ((postcompose notT).comp (pointwiseBin andT)
        |>.comp (paired
          (postcompose notT |>.comp (proj₀ (funSpace L Example23.T) (funSpace L Example23.T)))
          (postcompose notT |>.comp (proj₁ (funSpace L Example23.T) (funSpace L Example23.T))))) :=
  comp_isComputable
    (paired_isComputable
      (comp_isComputable (proj₀_isComputable LTpres LTpres) notT_lifted_isComputable)
      (comp_isComputable (proj₁_isComputable LTpres LTpres) notT_lifted_isComputable))
    (comp_isComputable andT_lifted_isComputable notT_lifted_isComputable)

end Scott1980.Neighborhood.Exercise724

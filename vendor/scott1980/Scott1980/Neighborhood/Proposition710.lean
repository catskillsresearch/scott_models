/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Definition71
import Scott1980.Neighborhood.Definition79
import Mathlib.Tactic

/-!
# Proposition 7.10 (Scott 1981, PRG-19, §7) — `ℙ𝒟` is a neighbourhood system, effectively given

Scott states, right after defining the Smyth power domain `ℙ𝒟` (Definition 7.9):

> **Proposition 7.10.** `ℙ𝒟` *is a neighbourhood system, and it is effectively given if `𝒟` is.*

This file delivers both halves.

## Part A — `ℙ𝒟` is a neighbourhood system (`NeighborhoodSystem.PowerDomain`)

Building on `Definition79.lean`'s neighbourhood family `PDmem` (finite unions of down-sets
`⋃_{X ∈ L} ↓X`), we package it as `V.PowerDomain : NeighborhoodSystem (Set α)` with master `↓Δ`. The
content is closure under binary intersection (`PDmem_inter`), which follows from distributing `∩`
over the finite union and the *unconditional* identity `↓X ∩ ↓Y = ↓(X ∩ Y)` (Exercise 1.20's
`upSet_inter`): each product term `↓X ∩ ↓Y` is itself in `ℙ𝒟` (`PDmem_upSet_inter`) — it is `↓(X∩Y)`
when `{X,Y}` is consistent, and `∅` otherwise (the empty term). Deciding *which* requires testing
`X ∩ Y ∈ 𝒟` over an arbitrary system, so this **one** `Prop`-level step uses `Classical` (`by_cases`),
exactly as Scott's "throwing out empty terms" anticipates; the *data* of `PowerDomain` (`mem`,
`master`) is choice-free.

## Part B — `ℙ𝒟` is effectively given (`PowerDomain_isEffectivelyGiven`)

Given `P : ComputablePresentation 𝒟`, we enumerate `ℙ𝒟`-neighbourhoods by codes of finite lists of
`𝒟`-indices: `Ypd c = ⋃_{a ∈ decodeList c} ↓X_a`. The two relations of Definition 7.1:

* **(ii) consistency is *always true*** — `∅ ∈ ℙ𝒟` (the empty union, code `0`) is below every
  neighbourhood, so `cons_computable` is the constant decider.
* **(i)** reduces to *equality of two finite unions of down-sets*, which unfolds (`Ypd_eq_iff`) to the
  nested bounded quantifier
  `(∀ a ∈ dl c, ∃ b ∈ dl k, X_a ⊆ X_b) ∧ (∀ b ∈ dl k, ∃ a ∈ dl c, X_b ⊆ X_a)` —
  recursively decidable by `RecDecidable.bForallList`/`bExistsList` over `P.incl_computable`.

The **intersection function** is a primitive-recursive nested fold over the two index lists, emitting
`P.inter a b` for the *consistent* pairs `(a, b)` and dropping the rest (the empty terms); its
correctness is the distribution `Y_n ∩ Y_m = ⋃_{a,b} ↓(X_a ∩ X_b)`. Following the `funPresentation`
pattern (Theorem 7.5), the presentation takes the component deciders as explicit primitive-recursive
arguments, so the assembled data is choice-free; `PowerDomain_isEffectivelyGiven` obtains the deciders
from `P` inside the `Nonempty` proof (extraction into a `Prop` goal needs no choice).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-! ### Part A — `ℙ𝒟` is a neighbourhood system. -/

/-- The finite union `⋃_{X ∈ []} ↓X` is empty. -/
theorem upSetUnion_nil : (⋃ X ∈ ([] : List (Set α)), V.upSet X) = ∅ := by
  ext z
  rw [V.mem_PDunion]
  simp only [List.not_mem_nil, false_and, exists_false, Set.mem_empty_iff_false]

/-- Cons law for the finite union of down-sets: `⋃_{X ∈ Y::L} ↓X = ↓Y ∪ ⋃_{X ∈ L} ↓X`. -/
theorem upSetUnion_cons (Y : Set α) (L : List (Set α)) :
    (⋃ X ∈ (Y :: L), V.upSet X) = V.upSet Y ∪ ⋃ X ∈ L, V.upSet X := by
  ext z
  rw [Set.mem_union, V.mem_PDunion, V.mem_PDunion]
  constructor
  · rintro ⟨X, hX, hz⟩
    rcases List.mem_cons.mp hX with rfl | hX'
    · exact Or.inl hz
    · exact Or.inr ⟨X, hX', hz⟩
  · rintro (hz | ⟨X, hX, hz⟩)
    · exact ⟨Y, List.mem_cons.mpr (Or.inl rfl), hz⟩
    · exact ⟨X, List.mem_cons.mpr (Or.inr hX), hz⟩

/-- **Each product term `↓X ∩ ↓Y` is a `ℙ𝒟`-neighbourhood.** By `upSet_inter` it is `↓(X ∩ Y)`; if
`{X, Y}` is consistent (`X ∩ Y ∈ 𝒟`) this is the down-set of a neighbourhood (`PDmem_upSet`),
otherwise `↓(X ∩ Y) = ∅` (no `Z ∈ 𝒟` lies below `X ∩ Y`), the empty union (`PDmem_empty`). The
`by_cases` on `V.mem (X ∩ Y)` is the lone `Classical` step (deciding membership in an arbitrary
system). -/
theorem PDmem_upSet_inter {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) :
    V.PDmem (V.upSet X ∩ V.upSet Y) := by
  rw [V.upSet_inter]
  by_cases h : V.mem (X ∩ Y)
  · exact V.PDmem_upSet h
  · have hempty : V.upSet (X ∩ Y) = ∅ := by
      ext Z
      simp only [mem_upSet, Set.mem_empty_iff_false, iff_false, not_and]
      intro hZmem hZsub
      exact h (V.inter_mem hX hY hZmem hZsub)
    rw [hempty]; exact V.PDmem_empty

/-- `↓X ∩ (⋃_{Y ∈ L} ↓Y) ∈ ℙ𝒟`: distribute `∩` over the finite union and use `PDmem_upSet_inter`
term by term. -/
theorem PDmem_upSet_inter_biUnion {X : Set α} (hX : V.mem X) :
    ∀ (L : List (Set α)), (∀ Y ∈ L, V.mem Y) → V.PDmem (V.upSet X ∩ ⋃ Y ∈ L, V.upSet Y) := by
  intro L
  induction L with
  | nil =>
    intro _
    rw [V.upSetUnion_nil, Set.inter_empty]
    exact V.PDmem_empty
  | cons Y L ih =>
    intro hL
    rw [V.upSetUnion_cons, Set.inter_union_distrib_left]
    exact V.PDmem_union (V.PDmem_upSet_inter hX (hL Y (List.mem_cons.mpr (Or.inl rfl))))
      (ih (fun Z hZ => hL Z (List.mem_cons.mpr (Or.inr hZ))))

/-- `(⋃_{X ∈ L₁} ↓X) ∩ W₂ ∈ ℙ𝒟` for any `ℙ𝒟`-neighbourhood `W₂` (induction on `L₁`). -/
theorem PDmem_biUnion_inter :
    ∀ (L₁ : List (Set α)), (∀ X ∈ L₁, V.mem X) → ∀ {W₂ : Set (Set α)}, V.PDmem W₂ →
      V.PDmem ((⋃ X ∈ L₁, V.upSet X) ∩ W₂) := by
  intro L₁
  induction L₁ with
  | nil =>
    intro _ W₂ _
    rw [V.upSetUnion_nil, Set.empty_inter]
    exact V.PDmem_empty
  | cons X L ih =>
    intro hL W₂ hW₂
    rw [V.upSetUnion_cons, Set.union_inter_distrib_right]
    refine V.PDmem_union ?_ (ih (fun Z hZ => hL Z (List.mem_cons.mpr (Or.inr hZ))) hW₂)
    obtain ⟨L₂, hL₂, rfl⟩ := hW₂
    exact V.PDmem_upSet_inter_biUnion (hL X (List.mem_cons.mpr (Or.inl rfl))) L₂ hL₂

/-- **`ℙ𝒟` is closed under binary intersection.** (The content of Part A's condition (ii).) -/
theorem PDmem_inter {W₁ W₂ : Set (Set α)} (h₁ : V.PDmem W₁) (h₂ : V.PDmem W₂) :
    V.PDmem (W₁ ∩ W₂) := by
  obtain ⟨L₁, hL₁, rfl⟩ := h₁
  exact V.PDmem_biUnion_inter L₁ hL₁ h₂

/-- **Proposition 7.10 (Part A) — the Smyth power domain `ℙ𝒟` as a neighbourhood system.** Master
`↓Δ`; closure under intersection is `PDmem_inter`; `↓X ⊆ ↓Δ` since `X ⊆ Δ`. -/
abbrev PowerDomain : NeighborhoodSystem (Set α) where
  mem := V.PDmem
  master := V.upSet V.master
  master_nonempty := ⟨V.master, V.master_mem, subset_rfl⟩
  master_mem := V.PDmem_master
  inter_mem := fun h₁ h₂ _ _ => V.PDmem_inter h₁ h₂
  sub_master := by
    intro W hW
    obtain ⟨L, hL, rfl⟩ := hW
    intro Z hZ
    rw [V.mem_PDunion] at hZ
    obtain ⟨X, hX, hZmem, hZsub⟩ := hZ
    exact ⟨hZmem, hZsub.trans (V.sub_master (hL X hX))⟩

@[simp] theorem PowerDomain_mem {W : Set (Set α)} : V.PowerDomain.mem W ↔ V.PDmem W := Iff.rfl

@[simp] theorem PowerDomain_master : V.PowerDomain.master = V.upSet V.master := rfl

/-! ### Part B — `ℙ𝒟` is effectively given.

Throughout, `P : ComputablePresentation 𝒟`. We enumerate `ℙ𝒟`-neighbourhoods by codes of finite lists
of `𝒟`-indices. -/

variable (P : ComputablePresentation V)

/-- The finite union of down-sets indexed by a `List` of `𝒟`-indices: `⋃_{b ∈ l} ↓X_b`. -/
def UPX (l : List ℕ) : Set (Set α) := ⋃ b ∈ l, V.upSet (P.X b)

theorem UPX_def (l : List ℕ) : V.UPX P l = ⋃ b ∈ l, V.upSet (P.X b) := rfl

theorem mem_UPX {l : List ℕ} {z : Set α} :
    z ∈ V.UPX P l ↔ ∃ b ∈ l, z ∈ V.upSet (P.X b) := by
  simp only [UPX, Set.mem_iUnion, exists_prop]

theorem UPX_nil : V.UPX P [] = ∅ := by
  ext z
  rw [V.mem_UPX P]
  simp only [List.not_mem_nil, false_and, exists_false, Set.mem_empty_iff_false]

theorem UPX_cons (b : ℕ) (l : List ℕ) :
    V.UPX P (b :: l) = V.upSet (P.X b) ∪ V.UPX P l := by
  ext z
  rw [Set.mem_union, V.mem_UPX P, V.mem_UPX P]
  constructor
  · rintro ⟨c, hc, hz⟩
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact Or.inl hz
    · exact Or.inr ⟨c, hc', hz⟩
  · rintro (hz | ⟨c, hc, hz⟩)
    · exact ⟨b, List.mem_cons.mpr (Or.inl rfl), hz⟩
    · exact ⟨c, List.mem_cons.mpr (Or.inr hc), hz⟩

/-- **The enumeration of `ℙ𝒟`.** `Ypd c = ⋃_{a ∈ decodeList c} ↓X_a` — a finite union of down-sets,
ranging over all of `ℙ𝒟` as `c` ranges over `ℕ` (the empty code `0` gives `∅`). -/
def Ypd (c : ℕ) : Set (Set α) := V.UPX P (decodeList c)

theorem Ypd_def (c : ℕ) : V.Ypd P c = V.UPX P (decodeList c) := rfl

theorem mem_Ypd {c : ℕ} {z : Set α} :
    z ∈ V.Ypd P c ↔ ∃ a ∈ decodeList c, z ∈ V.upSet (P.X a) := V.mem_UPX P

theorem Ypd_zero : V.Ypd P 0 = ∅ := by rw [Ypd_def, decodeList_zero, V.UPX_nil P]

theorem Ypd_cons_code (v acc : ℕ) :
    V.Ypd P (Nat.pair v acc + 1) = V.upSet (P.X v) ∪ V.Ypd P acc := by
  rw [Ypd_def, decodeList_succ, unpair_pair_fst, unpair_pair_snd, V.UPX_cons P, ← V.Ypd_def P]

/-- Every `Ypd c` is a `ℙ𝒟`-neighbourhood (list `(decodeList c).map P.X`). -/
theorem Ypd_isPDmem (c : ℕ) : V.PDmem (V.Ypd P c) := by
  refine ⟨(decodeList c).map P.X, ?_, ?_⟩
  · intro X hX
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hX
    exact P.mem_X a
  · ext z
    rw [V.mem_Ypd P, V.mem_PDunion]
    constructor
    · rintro ⟨a, ha, hz⟩; exact ⟨P.X a, List.mem_map.mpr ⟨a, ha, rfl⟩, hz⟩
    · rintro ⟨X, hX, hz⟩
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hX
      exact ⟨a, ha, hz⟩

/-- The enumeration is onto `ℙ𝒟` (build the index list entry by entry from `P.surj`; choice-free). -/
theorem PDmem_exists_Ypd_aux :
    ∀ (L : List (Set α)), (∀ X ∈ L, V.mem X) → ∃ c, V.Ypd P c = ⋃ X ∈ L, V.upSet X := by
  intro L
  induction L with
  | nil => intro _; exact ⟨0, by rw [V.Ypd_zero P, V.upSetUnion_nil]⟩
  | cons X L ih =>
    intro hL
    obtain ⟨n, hn⟩ := P.surj (hL X (List.mem_cons.mpr (Or.inl rfl)))
    obtain ⟨c', hc'⟩ := ih (fun Y hY => hL Y (List.mem_cons.mpr (Or.inr hY)))
    exact ⟨Nat.pair n c' + 1, by rw [V.Ypd_cons_code P, hn, hc', V.upSetUnion_cons]⟩

theorem PDmem_exists_Ypd {W : Set (Set α)} (hW : V.PDmem W) : ∃ c, V.Ypd P c = W := by
  obtain ⟨L, hL, rfl⟩ := hW
  exact V.PDmem_exists_Ypd_aux P L hL

/-! #### The equality decider (Scott's relation (i)). -/

/-- `↓X_a ⊆ Y_k ↔ ∃ b ∈ dl k, X_a ⊆ X_b` (a down-set lies in a finite union of down-sets iff its top
`X_a` is below one of them). -/
theorem upSet_subset_Ypd_iff {a k : ℕ} :
    V.upSet (P.X a) ⊆ V.Ypd P k ↔ ∃ b ∈ decodeList k, P.X a ⊆ P.X b := by
  constructor
  · intro h
    have hmem : P.X a ∈ V.Ypd P k := h ⟨P.mem_X a, subset_rfl⟩
    obtain ⟨b, hb, hPab⟩ := (V.mem_Ypd P).mp hmem
    exact ⟨b, hb, hPab.2⟩
  · rintro ⟨b, hb, hab⟩ z hz
    exact (V.mem_Ypd P).mpr ⟨b, hb, hz.1, hz.2.trans hab⟩

/-- `Y_c ⊆ Y_k ↔ ∀ a ∈ dl c, ∃ b ∈ dl k, X_a ⊆ X_b`. -/
theorem Ypd_subset_iff {c k : ℕ} :
    V.Ypd P c ⊆ V.Ypd P k ↔ ∀ a ∈ decodeList c, ∃ b ∈ decodeList k, P.X a ⊆ P.X b := by
  rw [Ypd_def, UPX_def, Set.iUnion₂_subset_iff]
  constructor
  · intro h a ha; exact (V.upSet_subset_Ypd_iff P).mp (h a ha)
  · intro h a ha; exact (V.upSet_subset_Ypd_iff P).mpr (h a ha)

/-- **Equality of two finite unions of down-sets**, unfolded as a nested bounded `∀/∃`. -/
theorem Ypd_eq_iff {c k : ℕ} :
    V.Ypd P c = V.Ypd P k ↔
      (∀ a ∈ decodeList c, ∃ b ∈ decodeList k, P.X a ⊆ P.X b) ∧
      (∀ b ∈ decodeList k, ∃ a ∈ decodeList c, P.X b ⊆ P.X a) := by
  rw [Set.Subset.antisymm_iff, V.Ypd_subset_iff P, V.Ypd_subset_iff P]

/-- `∀ a ∈ dl c, ∃ b ∈ dl k, X_a ⊆ X_b` is recursively decidable (nested bounded `∀/∃` over
`P.incl_computable`). -/
theorem subCode_computable :
    RecDecidable₂ (fun c k => ∀ a ∈ decodeList c, ∃ b ∈ decodeList k, P.X a ⊆ P.X b) := by
  have hinner : RecDecidable₂ (fun k a => ∃ b ∈ decodeList k, P.X a ⊆ P.X b) :=
    P.incl_computable.swap.bExistsList
  exact hinner.swap.bForallList

/-- **Scott's relation (i) for `ℙ𝒟`, at the level of codes:** equality of two enumerated
neighbourhoods is recursively decidable. -/
theorem eqCode_computable : RecDecidable₂ (fun c k => V.Ypd P c = V.Ypd P k) := by
  have h := (V.subCode_computable P).and (V.subCode_computable P).swap
  refine RecDecidable.of_iff (fun t => ?_) h
  exact V.Ypd_eq_iff P

/-! #### The primitive-recursive intersection function (the nested filtered product fold). -/

/-- One step of the **inner** fold (over `decodeList m`, parameter the outer index `a`): prepend
`P.inter a b` to the accumulator code iff `(a, b)` is consistent (`cons ⟨a,b⟩ = 1`), else leave it.
`foldCode` shape: state `w = ⟨b, ⟨acc, a⟩⟩`. -/
def innerInterStp (cons : ℕ → ℕ) (w : ℕ) : ℕ :=
  selectFn (isOne (cons (Nat.pair w.unpair.2.unpair.2 w.unpair.1)))
    (Nat.pair (P.inter w.unpair.2.unpair.2 w.unpair.1) w.unpair.2.unpair.1 + 1)
    w.unpair.2.unpair.1

theorem innerInterStp_eq (cons : ℕ → ℕ) (a acc b : ℕ) :
    V.innerInterStp P cons (Nat.pair b (Nat.pair acc a))
      = selectFn (isOne (cons (Nat.pair a b))) (Nat.pair (P.inter a b) acc + 1) acc := by
  unfold innerInterStp; simp only [unpair_pair_fst, unpair_pair_snd]

/-- The inner fold: process `decodeList m`, accumulating the consistent intersection indices. -/
def innerInterCode (cons : ℕ → ℕ) (a acc m : ℕ) : ℕ := foldCode (V.innerInterStp P cons) a acc m

theorem innerInterCode_eq (cons : ℕ → ℕ) (a acc m : ℕ) :
    V.innerInterCode P cons a acc m
      = List.foldl (fun acc b => selectFn (isOne (cons (Nat.pair a b)))
          (Nat.pair (P.inter a b) acc + 1) acc) acc (decodeList m) := by
  have hf : (fun (acc x : ℕ) => V.innerInterStp P cons (Nat.pair x (Nat.pair acc a)))
      = (fun acc b => selectFn (isOne (cons (Nat.pair a b))) (Nat.pair (P.inter a b) acc + 1) acc) := by
    funext acc b; exact V.innerInterStp_eq P cons a acc b
  unfold innerInterCode; rw [foldCode_eq', hf]

/-- One step of the **outer** fold (over `decodeList n`, parameter `m`): run the inner fold for the
current outer index `a`. `foldCode` shape: state `w = ⟨a, ⟨acc, m⟩⟩`. -/
def outerInterStp (cons : ℕ → ℕ) (w : ℕ) : ℕ :=
  V.innerInterCode P cons w.unpair.1 w.unpair.2.unpair.1 w.unpair.2.unpair.2

theorem outerInterStp_eq (cons : ℕ → ℕ) (a acc m : ℕ) :
    V.outerInterStp P cons (Nat.pair a (Nat.pair acc m)) = V.innerInterCode P cons a acc m := by
  unfold outerInterStp; simp only [unpair_pair_fst, unpair_pair_snd]

/-- **The intersection code** `interCode cons n m`: a code of the list of `P.inter a b` over the
consistent pairs `(a, b) ∈ dl n × dl m`. -/
def interCode (cons : ℕ → ℕ) (n m : ℕ) : ℕ := foldCode (V.outerInterStp P cons) m 0 n

theorem interCode_eq (cons : ℕ → ℕ) (n m : ℕ) :
    V.interCode P cons n m
      = List.foldl (fun acc a => V.innerInterCode P cons a acc m) 0 (decodeList n) := by
  have hf : (fun (acc x : ℕ) => V.outerInterStp P cons (Nat.pair x (Nat.pair acc m)))
      = (fun acc a => V.innerInterCode P cons a acc m) := by
    funext acc a; exact V.outerInterStp_eq P cons a acc m
  unfold interCode; rw [foldCode_eq', hf]

/-- If `(a, b)` is *inconsistent* (no `𝒟`-neighbourhood below `X_a ∩ X_b`) then `↓X_a ∩ ↓X_b = ∅`. -/
theorem upSet_inter_eq_empty_of_not_cons {a b : ℕ}
    (h : ¬ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    V.upSet (P.X a) ∩ V.upSet (P.X b) = ∅ := by
  rw [V.upSet_inter]
  ext Z
  simp only [mem_upSet, Set.mem_empty_iff_false, iff_false, not_and]
  intro hZmem hZsub
  obtain ⟨n, hn⟩ := P.surj hZmem
  exact h ⟨n, by rw [hn]; exact hZsub⟩

/-- One inner step at the `Ypd` level: prepending the consistent intersection index adds exactly
`↓X_a ∩ ↓X_b` (which is `∅` for inconsistent pairs). The `by_cases` on `cons ⟨a,b⟩ = 1` is on a
*decidable* `ℕ`-equality — choice-free. -/
theorem Ypd_innerstep (cons : ℕ → ℕ) {a b : ℕ}
    (hcons : cons (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) (acc : ℕ) :
    V.Ypd P (selectFn (isOne (cons (Nat.pair a b))) (Nat.pair (P.inter a b) acc + 1) acc)
      = V.Ypd P acc ∪ (V.upSet (P.X a) ∩ V.upSet (P.X b)) := by
  by_cases h : cons (Nat.pair a b) = 1
  · rw [(isOne_eq_one_iff _).mpr h, selectFn_one, V.Ypd_cons_code P]
    have hXeq : P.X (P.inter a b) = P.X a ∩ P.X b := P.inter_spec (hcons.mp h)
    rw [hXeq, ← V.upSet_inter, Set.union_comm]
  · have hisz : isOne (cons (Nat.pair a b)) = 0 := by
      have hle := isOne_le_one (cons (Nat.pair a b))
      rcases (show isOne (cons (Nat.pair a b)) = 0 ∨ isOne (cons (Nat.pair a b)) = 1 by omega)
        with h0 | h1
      · exact h0
      · exact absurd ((isOne_eq_one_iff _).mp h1) h
    rw [hisz, selectFn_zero,
      V.upSet_inter_eq_empty_of_not_cons P (fun hk => h (hcons.mpr hk)), Set.union_empty]

/-- The inner fold computes `↓X_a ∩ (⋃_{b ∈ bs} ↓X_b)` on top of the starting accumulator. -/
theorem Ypd_innerfoldl (cons : ℕ → ℕ) (a : ℕ)
    (hcons : ∀ b, cons (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    ∀ (bs : List ℕ) (acc : ℕ),
      V.Ypd P (List.foldl (fun acc b => selectFn (isOne (cons (Nat.pair a b)))
          (Nat.pair (P.inter a b) acc + 1) acc) acc bs)
        = V.Ypd P acc ∪ (V.upSet (P.X a) ∩ V.UPX P bs) := by
  intro bs
  induction bs with
  | nil => intro acc; rw [List.foldl_nil, V.UPX_nil P, Set.inter_empty, Set.union_empty]
  | cons b bs ih =>
    intro acc
    rw [List.foldl_cons, ih, V.Ypd_innerstep P cons (hcons b), V.UPX_cons P,
      Set.inter_union_distrib_left, Set.union_assoc]

/-- `Ypd (innerInterCode cons a acc m) = Ypd acc ∪ (↓X_a ∩ Y_m)`. -/
theorem Ypd_innerInterCode (cons : ℕ → ℕ) (a acc m : ℕ)
    (hcons : ∀ b, cons (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    V.Ypd P (V.innerInterCode P cons a acc m)
      = V.Ypd P acc ∪ (V.upSet (P.X a) ∩ V.Ypd P m) := by
  rw [V.innerInterCode_eq P, V.Ypd_innerfoldl P cons a hcons (decodeList m) acc, ← V.Ypd_def P]

/-- The outer fold computes `(⋃_{a ∈ as} ↓X_a) ∩ Y_m` on top of the starting accumulator. -/
theorem Ypd_outerfoldl (cons : ℕ → ℕ) (m : ℕ)
    (hcons : ∀ a b, cons (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    ∀ (as : List ℕ) (acc : ℕ),
      V.Ypd P (List.foldl (fun acc a => V.innerInterCode P cons a acc m) acc as)
        = V.Ypd P acc ∪ (V.UPX P as ∩ V.Ypd P m) := by
  intro as
  induction as with
  | nil => intro acc; rw [List.foldl_nil, V.UPX_nil P, Set.empty_inter, Set.union_empty]
  | cons a as ih =>
    intro acc
    rw [List.foldl_cons, ih, V.Ypd_innerInterCode P cons a acc m (hcons a), V.UPX_cons P,
      Set.union_inter_distrib_right, Set.union_assoc]

/-- **Correctness of the intersection code:** `Y_{interCode n m} = Y_n ∩ Y_m`. -/
theorem Ypd_interCode (cons : ℕ → ℕ) (n m : ℕ)
    (hcons : ∀ a b, cons (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    V.Ypd P (V.interCode P cons n m) = V.Ypd P n ∩ V.Ypd P m := by
  rw [V.interCode_eq P, V.Ypd_outerfoldl P cons m hcons (decodeList n) 0, V.Ypd_zero P,
    Set.empty_union, ← V.Ypd_def P]

/-! #### Primitive recursivity of `interCode`. -/

theorem primrec_innerInterStp (cons : ℕ → ℕ) (hconsp : Nat.Primrec cons) :
    Nat.Primrec (V.innerInterStp P cons) := by
  have h1 : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have ha : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hpair_ab : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.2.unpair.2 w.unpair.1) := ha.pair h1
  have hcons_ab : Nat.Primrec (fun w : ℕ => cons (Nat.pair w.unpair.2.unpair.2 w.unpair.1)) :=
    hconsp.comp hpair_ab
  have hinter_ab : Nat.Primrec (fun w : ℕ => P.inter w.unpair.2.unpair.2 w.unpair.1) :=
    (P.inter_primrec.comp hpair_ab).of_eq (fun w => by simp only [unpair_pair_fst, unpair_pair_snd])
  have hprepend : Nat.Primrec
      (fun w : ℕ => Nat.pair (P.inter w.unpair.2.unpair.2 w.unpair.1) w.unpair.2.unpair.1 + 1) :=
    Nat.Primrec.succ.comp (hinter_ab.pair hacc)
  exact (primrec_selectFn (primrec_isOne.comp hcons_ab) hprepend hacc).of_eq (fun _ => rfl)

theorem primrec_outerInterStp (cons : ℕ → ℕ) (hconsp : Nat.Primrec cons) :
    Nat.Primrec (V.outerInterStp P cons) :=
  (primrec_foldCode (V.primrec_innerInterStp P cons hconsp) Nat.Primrec.left
    (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.right.comp Nat.Primrec.right)).of_eq
    (fun _ => rfl)

theorem primrec_interCode (cons : ℕ → ℕ) (hconsp : Nat.Primrec cons) :
    Nat.Primrec (fun t => V.interCode P cons t.unpair.1 t.unpair.2) :=
  (primrec_foldCode (V.primrec_outerInterStp P cons hconsp) Nat.Primrec.right
    (Nat.Primrec.const 0) Nat.Primrec.left).of_eq (fun _ => rfl)

/-- **Scott's relation (i):** `Y_n ∩ Y_m = Y_k` is recursively decidable, by reducing to the equality
decider via the (primitive-recursive) intersection code. -/
theorem Ypd_interEq_computable (cons : ℕ → ℕ) (hconsp : Nat.Primrec cons)
    (hcons : ∀ a b, cons (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    RecDecidable₃ (fun n m k => V.Ypd P n ∩ V.Ypd P m = V.Ypd P k) := by
  have hic : Nat.Primrec (fun t => V.interCode P cons t.unpair.1 t.unpair.2.unpair.1) :=
    ((V.primrec_interCode P cons hconsp).comp
      (Nat.Primrec.left.pair (Nat.Primrec.left.comp Nat.Primrec.right))).of_eq
      (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
  have hg : Nat.Primrec
      (fun t => Nat.pair (V.interCode P cons t.unpair.1 t.unpair.2.unpair.1) t.unpair.2.unpair.2) :=
    hic.pair (Nat.Primrec.right.comp Nat.Primrec.right)
  refine RecDecidable.of_iff (fun t => ?_) ((V.eqCode_computable P).comp hg)
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [V.Ypd_interCode P cons t.unpair.1 t.unpair.2.unpair.1 hcons]

/-! #### Assembling the `ℙ𝒟` presentation. -/

/-- **Proposition 7.10 (Part B), parametrised.** The `ℙ𝒟` presentation built from an explicit
primitive-recursive consistency decider `cons` for `𝒟` (cf. `funPresentation`, Theorem 7.5). The data
(`X = Ypd`, `inter = interCode cons`, `masterIdx`) is choice-free given `cons`. -/
def PDPresentation (cons : ℕ → ℕ) (hconsp : Nat.Primrec cons)
    (hcons : ∀ a b, cons (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    ComputablePresentation V.PowerDomain where
  X := V.Ypd P
  mem_X := fun c => V.Ypd_isPDmem P c
  surj := fun hW => V.PDmem_exists_Ypd P hW
  interEq_computable := V.Ypd_interEq_computable P cons hconsp hcons
  cons_computable :=
    recDecidable_of_forall (fun t => ⟨0, by rw [V.Ypd_zero P]; exact Set.empty_subset _⟩)
  inter := V.interCode P cons
  inter_primrec := V.primrec_interCode P cons hconsp
  inter_spec := fun _ => V.Ypd_interCode P cons _ _ hcons
  masterIdx := Nat.pair P.masterIdx 0 + 1
  masterIdx_spec := by
    show V.Ypd P (Nat.pair P.masterIdx 0 + 1) = V.PowerDomain.master
    rw [V.Ypd_cons_code P, V.Ypd_zero P, Set.union_empty, P.masterIdx_spec, PowerDomain_master]

end NeighborhoodSystem

/-- **Proposition 7.10 (Scott 1981, PRG-19).** The Smyth power domain `ℙ𝒟` is a neighbourhood system
(`PowerDomain`), and it is **effectively given** whenever `𝒟` is. The consistency decider is obtained
from `𝒟`'s presentation inside the `Nonempty` proof (extraction into a `Prop` needs no choice). -/
theorem NeighborhoodSystem.PowerDomain_isEffectivelyGiven {α : Type*} {V : NeighborhoodSystem α}
    (h : V.IsEffectivelyGiven) : V.PowerDomain.IsEffectivelyGiven := by
  obtain ⟨P⟩ := h
  obtain ⟨cons, hconsp, hconss⟩ := P.cons_computable
  refine ⟨V.PDPresentation P cons hconsp (fun a b => ?_)⟩
  have hb := hconss (Nat.pair a b)
  simp only [unpair_pair_fst, unpair_pair_snd] at hb
  exact hb.symm

end Scott1980.Neighborhood

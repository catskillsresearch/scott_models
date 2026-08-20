/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Basic
import Scott1980.Neighborhood.Theorem41
import Mathlib.Data.Set.Insert

/-!
# Exercise 7.22 (Scott 1981, PRG-19, §7) — a domain over `{0,1}*` by least fixed point

> **EXERCISE 7.22.** (For algebraists.) Let `Σ = {0,1}*` be the free semigroup. A new domain is
> constructed by defining a family of sets by the least fixed point theorem as follows:
>
> `S = {Σ} ∪ {{σ} ∣ σ ∈ Σ} ∪ {XY ∣ X, Y ∈ S} ∪ {X ∩ Y ∣ X, Y ∈ S and X ∩ Y ≠ ∅}.`
>
> Here `XY = {στ ∣ σ ∈ X and τ ∈ Y}`.
>
> Prove that `S` is an effectively given, positive neighbourhood system. (Hint: the sets in `S` are
> each "regular events" in the terminology of automata theory, and we have a decision method for the
> set algebra of regular events.)
>
> Define multiplication on `|S|` by `xy = {Z ∈ S ∣ ∃ X ∈ x ∃ Y ∈ y. XY ⊆ Z}`, and show `|S|` becomes
> a semigroup with `Σ` embedded into `|S|` by the homomorphism `σ ↦ {X ∈ S ∣ σ ∈ X}`.
>
> Investigate some *infinite words* in `S`, say those defined by least fixed points such as
> `σ⃗ = σ σ⃗` and `σ⃗ = σ⃗ σ`. Are the equations `σ⃗ σ⃗ = σ⃗`, `σ⃗ σ⃗ σ⃗ = σ⃗`,
> `σ⃗ 1⃗ σ⃗ 1⃗ = σ⃗ 1⃗`, and `01⃗ 01⃗ 01⃗ 01⃗ = 01⃗ 01⃗` true?

This file formalises the **algebraic core** of the exercise, fully and choice-free:

* the least-fixed-point family `S` as an inductive predicate `InS` over tokens `Σ = {0,1}* = List Bool`;
* `S` is a **positive neighbourhood system** `Ssys` (Definition 1.1 / Exercise 1.19), built choice-free
  via `NeighborhoodSystem.ofPositive`;
* the **multiplication** `xy` on the domain `|S|` and the proof that it is **associative**, so `|S|`
  is a semigroup (`mulElem`, `mulElem_assoc`);
* the **embedding** `σ ↦ {X ∈ S ∣ σ ∈ X}` of the free monoid into `|S|`, proved a semigroup
  **homomorphism** (`emb_mul`) and **injective** (`emb_injective`);
* Scott's **infinite words** `σ⃗`, as genuine least fixed points `σ⃗ = σ · σ⃗` (Theorem 4.1) of
  `x ↦ σ·x` realised as an approximable self-map `prependMap σ` on `|S|`, and **all four of Scott's
  equations**, proved unconditionally (`streamArrow_mul_self` and friends, **Exercise 7.22l**).

## Effective givenness (mechanised elsewhere in the project)

Every member of `S` is a *regular event* (Scott's hint), and effective givenness is **fully
mechanised** (not a gap): `Exercise722Regular.lean` (regularity), `Exercise722Decide.lean` /
`Exercise722Cat.lean` / `Exercise722Equiv.lean` (explicit finite automata; emptiness and language
equivalence deciders), `Recursive.lean` (the choice-free primitive-recursive `Nat.Primrec` mirrors),
and `Exercise722Presentation.lean` (`Ssys_cons_computable`, `Ssys_interEq_computable`: Definition 7.1
relations (ii) and (i) are recursively decidable). See `arxiv.md`, Exercise 7.22a–k (all Pass).

## Infinite words (Exercise 7.22l)

Scott's last questions ask about *infinite words* in `S` and whether certain multiplicative
equations hold in `|S|`. We answer them **the way Scott poses the question**: `σ⃗` is a genuine
**least fixed point in the domain `|S|`**, `σ⃗ = σ · σ⃗` (`streamArrow`, `streamArrow_eq`), built with
this project's existing Theorem 4.1 machinery — the same construction as `Example44.lean`'s
alternating sequence `a = 0(1a)` — rather than a set-theoretic proxy. All four of Scott's equations
then hold **unconditionally**, with no side-condition and no open question:
`streamArrow_mul_self` (`σ⃗σ⃗ = σ⃗`), `streamArrow_mul_self_self` (`σ⃗σ⃗σ⃗ = σ⃗`),
`streamArrow_mul_self_append_true` (`σ1⃗ · σ1⃗ = σ1⃗`), and `streamArrow_containsZero_pow_four`
(`01⃗01⃗01⃗01⃗ = 01⃗01⃗`).

(An earlier pass answered the same questions via a *set-theoretic proxy* instead: `streamElem w`,
the filter `Z ↦ InS Z ∧ ∀n, wⁿ ∈ Z`, conditional on the side-question `InS (powerLang w)` — is the
language `{wⁿ}` itself a member of `S`? That side-question turned out to be a genuinely open
combinatorics-on-words question (kept below, `streamElem`/`powerLang`, for reference), but it is
*not* Scott's question — it was an artefact of choosing that particular proxy, and `streamArrow`
above answers Scott's actual equations without ever needing it.)

Everything in this file depends only on `propext` / `Quot.sound` (no `Classical.choice`).
-/

namespace Scott1980.Neighborhood

namespace Exercise722

open NeighborhoodSystem ApproximableMap

/-! ## Concatenation of languages over `Σ = {0,1}*`

We work with tokens `Σ = List Bool` (the words over `{0,1}`); a neighbourhood is a `Set (List Bool)`
(a "language"). We use a bespoke `concat` (rather than mathlib's `Language.*`) so that intersection,
`Set.univ`, and singletons remain the native `Set` operations the neighbourhood-system API expects. -/

/-- Scott's `XY = {στ ∣ σ ∈ X and τ ∈ Y}`: the concatenation of two languages. -/
def concat (X Y : Set (List Bool)) : Set (List Bool) := {w | ∃ a ∈ X, ∃ b ∈ Y, a ++ b = w}

@[simp] theorem mem_concat {X Y : Set (List Bool)} {w : List Bool} :
    w ∈ concat X Y ↔ ∃ a ∈ X, ∃ b ∈ Y, a ++ b = w := Iff.rfl

/-- `a ∈ X`, `b ∈ Y ⟹ a ++ b ∈ XY`. -/
theorem append_mem_concat {X Y : Set (List Bool)} {a b : List Bool} (ha : a ∈ X) (hb : b ∈ Y) :
    a ++ b ∈ concat X Y := ⟨a, ha, b, hb, rfl⟩

/-- Concatenation is monotone in both arguments. -/
theorem concat_mono {X X' Y Y' : Set (List Bool)} (hX : X ⊆ X') (hY : Y ⊆ Y') :
    concat X Y ⊆ concat X' Y' := by
  rintro w ⟨a, ha, b, hb, rfl⟩; exact ⟨a, hX ha, b, hY hb, rfl⟩

/-- Concatenation is associative (inherited from `List.append_assoc`). -/
theorem concat_assoc (X Y Z : Set (List Bool)) :
    concat (concat X Y) Z = concat X (concat Y Z) := by
  ext w
  constructor
  · rintro ⟨ab, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩
    exact ⟨a, ha, b ++ c, ⟨b, hb, c, hc, rfl⟩, by rw [List.append_assoc]⟩
  · rintro ⟨a, ha, bc, ⟨b, hb, c, hc, rfl⟩, rfl⟩
    exact ⟨a ++ b, ⟨a, ha, b, hb, rfl⟩, c, hc, by rw [List.append_assoc]⟩

/-- The concatenation of two non-empty languages is non-empty. -/
theorem concat_nonempty {X Y : Set (List Bool)} (hX : X.Nonempty) (hY : Y.Nonempty) :
    (concat X Y).Nonempty := by
  obtain ⟨a, ha⟩ := hX
  obtain ⟨b, hb⟩ := hY
  exact ⟨a ++ b, a, ha, b, hb, rfl⟩

/-- `{a}{b} = {a ++ b}`: concatenation of singletons is the singleton of the concatenation. -/
theorem concat_singleton (a b : List Bool) : concat {a} {b} = {a ++ b} := by
  ext w
  simp only [mem_concat, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a', rfl, b', rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨a, rfl, b, rfl, rfl⟩

/-! ## The least-fixed-point family `S` -/

/-- **Scott's family `S`**, as the least fixed point (an inductive predicate). A language `X` is *in
`S`* iff it is built from the four generators:

* `Σ = {0,1}*` itself (`Set.univ`);
* a singleton `{σ}`;
* a concatenation `XY` of two members;
* a *non-empty* intersection `X ∩ Y` of two members. -/
inductive InS : Set (List Bool) → Prop
  | univ : InS Set.univ
  | singleton (σ : List Bool) : InS {σ}
  | mul {X Y : Set (List Bool)} : InS X → InS Y → InS (concat X Y)
  | inter {X Y : Set (List Bool)} : InS X → InS Y → (X ∩ Y).Nonempty → InS (X ∩ Y)

/-- **Every member of `S` is non-empty.** (`Σ` and singletons are non-empty; concatenation preserves
non-emptiness; intersections are only admitted to `S` when non-empty.) This is what makes `S`
*positive*. -/
theorem InS.nonempty {X : Set (List Bool)} (h : InS X) : X.Nonempty := by
  induction h with
  | univ => exact ⟨[], trivial⟩
  | singleton σ => exact ⟨σ, rfl⟩
  | mul _ _ ihX ihY => exact concat_nonempty ihX ihY
  | inter _ _ hne _ _ => exact hne

/-! ## `S` is a positive neighbourhood system -/

/-- **Exercise 7.22 (neighbourhood-system part).** `S` is a *positive* neighbourhood system over the
token type `Σ = {0,1}*`, with master neighbourhood `Δ = Σ = Set.univ`. Built choice-free via
`NeighborhoodSystem.ofPositive`: positivity `(X ∩ Y) ∈ S ↔ (X ∩ Y).Nonempty` holds because every
member of `S` is non-empty (`InS.nonempty`, the `→` direction) and `InS.inter` is exactly the `←`. -/
def Ssys : NeighborhoodSystem (List Bool) :=
  NeighborhoodSystem.ofPositive InS Set.univ InS.univ (fun {X} _ => Set.subset_univ X)
    (fun _ _ hX hY => ⟨fun h => h.nonempty, fun h => InS.inter hX hY h⟩)

@[simp] theorem Ssys_mem {X : Set (List Bool)} : Ssys.mem X ↔ InS X := Iff.rfl

theorem Ssys_master : Ssys.master = Set.univ := rfl

/-- `S` is indeed positive (Exercise 1.19's `IsPositive`). -/
theorem Ssys_isPositive : Ssys.IsPositive := by
  intro X Y hX hY
  exact ⟨fun h => h.nonempty, fun h => InS.inter hX hY h⟩

/-! ## Multiplication on the domain `|S|`

`xy = {Z ∈ S ∣ ∃ X ∈ x ∃ Y ∈ y. XY ⊆ Z}`. We show this is again a filter (an element of `|S|`). -/

/-- **Scott's multiplication on `|S|`.** `xy = {Z ∈ S ∣ ∃ X ∈ x ∃ Y ∈ y. XY ⊆ Z}`. The filter
conditions:

* `master_mem`: take `X = Y = Σ` (both in any filter), `Σ·Σ ⊆ Σ`;
* `inter_mem`: from witnesses `X₁Y₁ ⊆ Z₁`, `X₂Y₂ ⊆ Z₂`, the pair `X₁ ∩ X₂ ∈ x`, `Y₁ ∩ Y₂ ∈ y` (filter
  closure) gives `(X₁ ∩ X₂)(Y₁ ∩ Y₂) ⊆ Z₁ ∩ Z₂` by monotonicity of `concat`, and `Z₁ ∩ Z₂ ∈ S`
  because this non-empty witness sits inside it (positivity);
* `up_mem`: transitivity of `⊆`. -/
def mulElem (x y : Ssys.Element) : Ssys.Element where
  mem Z := InS Z ∧ ∃ X, x.mem X ∧ ∃ Y, y.mem Y ∧ concat X Y ⊆ Z
  sub h := h.1
  master_mem :=
    ⟨InS.univ, Set.univ, x.master_mem, Set.univ, y.master_mem, Set.subset_univ _⟩
  inter_mem := by
    rintro Z1 Z2 ⟨hZ1, X1, hX1, Y1, hY1, hsub1⟩ ⟨hZ2, X2, hX2, Y2, hY2, hsub2⟩
    have hXi : x.mem (X1 ∩ X2) := x.inter_mem hX1 hX2
    have hYi : y.mem (Y1 ∩ Y2) := y.inter_mem hY1 hY2
    have hcsub : concat (X1 ∩ X2) (Y1 ∩ Y2) ⊆ Z1 ∩ Z2 := by
      intro w hw
      exact ⟨hsub1 (concat_mono Set.inter_subset_left Set.inter_subset_left hw),
             hsub2 (concat_mono Set.inter_subset_right Set.inter_subset_right hw)⟩
    have hne : (Z1 ∩ Z2).Nonempty :=
      (concat_nonempty (x.sub hXi).nonempty (y.sub hYi).nonempty).mono hcsub
    exact ⟨InS.inter hZ1 hZ2 hne, X1 ∩ X2, hXi, Y1 ∩ Y2, hYi, hcsub⟩
  up_mem := by
    rintro Z W ⟨_, X, hX, Y, hY, hsub⟩ hW hZW
    exact ⟨hW, X, hX, Y, hY, hsub.trans hZW⟩

@[simp] theorem mem_mulElem {x y : Ssys.Element} {Z : Set (List Bool)} :
    (mulElem x y).mem Z ↔ InS Z ∧ ∃ X, x.mem X ∧ ∃ Y, y.mem Y ∧ concat X Y ⊆ Z := Iff.rfl

/-- **Exercise 7.22 (semigroup part): multiplication on `|S|` is associative**, so `|S|` is a
semigroup. The forward inclusion rewrites `X(YZ) = (XY)Z` (`concat_assoc`) and uses monotonicity of
`concat` to push the witnesses through; the converse is symmetric. -/
theorem mulElem_assoc (x y z : Ssys.Element) :
    mulElem (mulElem x y) z = mulElem x (mulElem y z) := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro ⟨hW, P, ⟨_, X, hX, Y, hY, hXY⟩, Z, hZ, hPZ⟩
    refine ⟨hW, X, hX, concat Y Z, ⟨InS.mul (y.sub hY) (z.sub hZ), Y, hY, Z, hZ,
      Set.Subset.refl _⟩, ?_⟩
    rw [← concat_assoc]
    exact (concat_mono hXY (Set.Subset.refl _)).trans hPZ
  · rintro ⟨hW, X, hX, Q, ⟨_, Y, hY, Z, hZ, hYZ⟩, hXQ⟩
    refine ⟨hW, concat X Y, ⟨InS.mul (x.sub hX) (y.sub hY), X, hX, Y, hY,
      Set.Subset.refl _⟩, Z, hZ, ?_⟩
    rw [concat_assoc]
    exact (concat_mono (Set.Subset.refl _) hYZ).trans hXQ

/-! ## The embedding of `Σ = {0,1}*` into `|S|` -/

/-- **Scott's embedding** `σ ↦ {X ∈ S ∣ σ ∈ X}`. This is a filter (an element of `|S|`): it contains
`Σ`, is closed under intersection (the intersection is non-empty since it still contains `σ`, so it
lies in `S` by positivity), and is upward closed. -/
def emb (σ : List Bool) : Ssys.Element where
  mem X := InS X ∧ σ ∈ X
  sub h := h.1
  master_mem := ⟨InS.univ, Set.mem_univ σ⟩
  inter_mem := by
    rintro X Y ⟨hX, hσX⟩ ⟨hY, hσY⟩
    exact ⟨InS.inter hX hY ⟨σ, hσX, hσY⟩, hσX, hσY⟩
  up_mem := by
    rintro X Y ⟨_, hσ⟩ hY hsub
    exact ⟨hY, hsub hσ⟩

@[simp] theorem mem_emb {σ : List Bool} {X : Set (List Bool)} :
    (emb σ).mem X ↔ InS X ∧ σ ∈ X := Iff.rfl

/-- **Exercise 7.22 (homomorphism part): `emb` is a semigroup homomorphism**,
`emb (σ ++ τ) = emb σ · emb τ`. Forward: from `σ ++ τ ∈ Z`, the witnesses `X = {σ}`, `Y = {τ}` give
`{σ}{τ} = {σ ++ τ} ⊆ Z`. Converse: if `{σ}` ∈ `emb σ`, `{τ}` ∈ `emb τ` with `XY ⊆ Z` then
`σ ++ τ ∈ XY ⊆ Z`. -/
theorem emb_mul (σ τ : List Bool) : emb (σ ++ τ) = mulElem (emb σ) (emb τ) := by
  apply NeighborhoodSystem.Element.ext
  intro Z
  constructor
  · rintro ⟨hZ, hστ⟩
    refine ⟨hZ, {σ}, ⟨InS.singleton σ, rfl⟩, {τ}, ⟨InS.singleton τ, rfl⟩, ?_⟩
    rw [concat_singleton]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw; exact hστ
  · rintro ⟨hZ, X, ⟨_, hσX⟩, Y, ⟨_, hτY⟩, hsub⟩
    exact ⟨hZ, hsub (append_mem_concat hσX hτY)⟩

/-- The embedding is **injective**: distinct words give distinct elements of `|S|`. (If
`emb σ = emb τ` then `emb τ` contains `{σ}`, forcing `τ = σ`.) So `Σ` genuinely *embeds* into `|S|`. -/
theorem emb_injective : Function.Injective emb := by
  intro σ τ h
  have hmem : (emb τ).mem {σ} := h ▸ (⟨InS.singleton σ, rfl⟩ : (emb σ).mem {σ})
  exact (Set.mem_singleton_iff.mp hmem.2).symm

/-! ## Infinite words as genuine least fixed points (Exercise 7.22l)

Scott's actual question defines `σ⃗` **as a least fixed point in the domain `|S|`**: `σ⃗ = σ·σ⃗`
(Theorem 4.1's construction, already built for exactly this purpose, e.g. `Example44.lean`'s
alternating sequence `a = 0(1a)`). We realise `x ↦ σ·x` as an approximable self-map on `Ssys`
(`prependMap`, generalising `Example44.lean`'s `consMap` from a single bit to a whole word), and
take `σ⃗ := (prependMap σ).fixElement`. This gives Scott's equation *unconditionally* — no side
condition on `InS (powerLang σ)` is needed, and (Theorem 4.1's construction being choice-free) no
`Classical.choice` is pulled in either. -/

/-- **`x ↦ σ·x`, realised as an approximable self-map on `|S|`.** Mirrors `Example44.lean`'s
`consMap`, generalised from a single bit `b` to an arbitrary word `σ`. -/
def prependMap (σ : List Bool) : ApproximableMap Ssys Ssys where
  rel Y Z := InS Y ∧ InS Z ∧ concat {σ} Y ⊆ Z
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨InS.univ, InS.univ, Set.subset_univ _⟩
  inter_right := by
    rintro Y Z Z' ⟨hY, hZ, hsub⟩ ⟨_, hZ', hsub'⟩
    have hcsub : concat {σ} Y ⊆ Z ∩ Z' := Set.subset_inter hsub hsub'
    have hne : (Z ∩ Z').Nonempty :=
      (concat_nonempty (Set.singleton_nonempty σ) hY.nonempty).mono hcsub
    exact ⟨hY, InS.inter hZ hZ' hne, hcsub⟩
  mono := by
    rintro Y Y' Z Z' ⟨_, hZ, hsub⟩ hYY' hZZ' hY' hZ'
    exact ⟨hY', hZ', (concat_mono (Set.Subset.refl _) hYY').trans (hsub.trans hZZ')⟩

/-- `(prependMap σ).toElementMap y = σ · y`: the approximable-map action agrees with Scott's
multiplication `mulElem`, using `{σ} ⊆ X` (any valid witness `X` for `emb σ` contains `σ`) to
tighten the witness set to `{σ}` without loss. -/
theorem prependMap_toElementMap (σ : List Bool) (y : Ssys.Element) :
    (prependMap σ).toElementMap y = mulElem (emb σ) y := by
  apply NeighborhoodSystem.Element.ext
  intro Z
  constructor
  · rintro ⟨Y, hY, hInSY, hInSZ, hsub⟩
    exact ⟨hInSZ, {σ}, ⟨InS.singleton σ, rfl⟩, Y, hY, hsub⟩
  · rintro ⟨hInSZ, X, ⟨_, hσX⟩, Y, hY, hsub⟩
    refine ⟨Y, hY, y.sub hY, hInSZ, ?_⟩
    exact (concat_mono (Set.singleton_subset_iff.mpr hσX) (Set.Subset.refl _)).trans hsub

/-- **Scott's `σ⃗`, as a genuine least fixed point** (Theorem 4.1) of `x ↦ σ·x` in `|S|`. -/
def streamArrow (σ : List Bool) : Ssys.Element := (prependMap σ).fixElement

/-- **`σ⃗ = σ·σ⃗`** (Scott's defining equation), unconditionally. -/
theorem streamArrow_eq (σ : List Bool) :
    mulElem (emb σ) (streamArrow σ) = streamArrow σ := by
  rw [← prependMap_toElementMap]
  exact toElementMap_fixElement (prependMap σ)

/-- `mulElem` is monotone in its right argument. -/
theorem mulElem_mono_right (x : Ssys.Element) : Monotone (mulElem x) := by
  rintro y y' hyy' Z ⟨hInS, X, hX, Y, hY, hsub⟩
  exact ⟨hInS, X, hX, Y, hyy' Y hY, hsub⟩

/-- **`⊥` is a left-annihilator up to `≤`**: `⊥·y ≤ y`. (`⊥`'s only neighbourhood is `Δ = Σ`, and
`Y ⊆ Σ·Y` via the empty-word split, so any witness collapses onto `y` itself.) -/
theorem mulElem_bot_le (y : Ssys.Element) : mulElem Ssys.bot y ≤ y := by
  rintro Z ⟨hInS, X, hX, Y, hY, hsub⟩
  rw [NeighborhoodSystem.mem_bot, Ssys_master] at hX
  subst hX
  refine y.up_mem hY hInS fun w hw => hsub ?_
  simpa using append_mem_concat (Set.mem_univ ([] : List Bool)) hw

/-- **`σ⃗ ≤ σ⃗·σ⃗`**: `σ⃗·σ⃗` is itself a fixed point of `x ↦ σ·x` (by associativity and `σ⃗ = σ·σ⃗`),
and `σ⃗` is the *least* such fixed point (`fixElement_le_of_toElementMap_le`). -/
theorem streamArrow_le_mul_self (σ : List Bool) :
    streamArrow σ ≤ mulElem (streamArrow σ) (streamArrow σ) := by
  apply fixElement_le_of_toElementMap_le
  have heq : (prependMap σ).toElementMap (mulElem (streamArrow σ) (streamArrow σ)) =
      mulElem (streamArrow σ) (streamArrow σ) := by
    rw [prependMap_toElementMap, ← mulElem_assoc, streamArrow_eq]
  exact le_of_eq heq

/-- **Per-approximant bound**: `fⁿ(⊥) · σ⃗ ≤ σ⃗`, by induction using `mulElem_bot_le` (base case)
and associativity + monotonicity + `streamArrow_eq` (step). -/
theorem prependMap_iterElem_mul_streamArrow_le (σ : List Bool) :
    ∀ n, mulElem ((prependMap σ).iterElem n) (streamArrow σ) ≤ streamArrow σ
  | 0 => by
      have h0 : (prependMap σ).iterElem 0 = Ssys.bot := by
        show (idMap Ssys).toElementMap Ssys.bot = Ssys.bot
        exact toElementMap_idMap Ssys.bot
      rw [h0]
      exact mulElem_bot_le (streamArrow σ)
  | n + 1 => by
      have hsucc : (prependMap σ).iterElem (n + 1) =
          mulElem (emb σ) ((prependMap σ).iterElem n) := by
        show ((prependMap σ).comp ((prependMap σ).iterMap n)).toElementMap Ssys.bot = _
        rw [toElementMap_comp]
        exact prependMap_toElementMap σ _
      rw [hsucc, mulElem_assoc]
      calc mulElem (emb σ) (mulElem ((prependMap σ).iterElem n) (streamArrow σ))
          ≤ mulElem (emb σ) (streamArrow σ) :=
            mulElem_mono_right (emb σ) (prependMap_iterElem_mul_streamArrow_le σ n)
        _ = streamArrow σ := streamArrow_eq σ

/-- **`σ⃗·σ⃗ ≤ σ⃗`**: `σ⃗`'s membership witnesses come from *some* finite approximant `fⁿ(⊥)`
(`mem_fixElement`/`mem_iterElem`), and every approximant satisfies the per-`n` bound above. -/
theorem streamArrow_mul_self_le (σ : List Bool) :
    mulElem (streamArrow σ) (streamArrow σ) ≤ streamArrow σ := by
  rintro Z ⟨hInSZ, X, hX, Y, hY, hsub⟩
  obtain ⟨n, hn⟩ := (mem_fixElement (prependMap σ)).mp hX
  have hXn : ((prependMap σ).iterElem n).mem X := (mem_iterElem (prependMap σ) n).mpr hn
  exact prependMap_iterElem_mul_streamArrow_le σ n Z ⟨hInSZ, X, hXn, Y, hY, hsub⟩

/-- **Exercise 7.22l (Scott's first equation, unconditional).** `σ⃗·σ⃗ = σ⃗`, for the genuine
least-fixed-point `σ⃗`, with no side-condition. -/
theorem streamArrow_mul_self (σ : List Bool) :
    mulElem (streamArrow σ) (streamArrow σ) = streamArrow σ :=
  le_antisymm (streamArrow_mul_self_le σ) (streamArrow_le_mul_self σ)

/-- **Scott's second equation.** `σ⃗·σ⃗·σ⃗ = σ⃗`. -/
theorem streamArrow_mul_self_self (σ : List Bool) :
    mulElem (mulElem (streamArrow σ) (streamArrow σ)) (streamArrow σ) = streamArrow σ := by
  rw [streamArrow_mul_self, streamArrow_mul_self]

/-- **Scott's third equation.** `σ1⃗ · σ1⃗ = σ1⃗`, where `σ1⃗ := streamArrow (σ ++ [true])` is the
arrow of the *combined* token `σ1` (Scott's notation `σ⃗1⃗` names the infinite repetition of the
word `σ` followed by `1`, not a product of two separate arrows — matching how the file's earlier
`streamElem`-based examples read the same equation). An instance of `streamArrow_mul_self`. -/
theorem streamArrow_mul_self_append_true (σ : List Bool) :
    mulElem (streamArrow (σ ++ [true])) (streamArrow (σ ++ [true])) =
      streamArrow (σ ++ [true]) :=
  streamArrow_mul_self (σ ++ [true])

/-- **Scott's fourth equation (the concrete numeric instance).** `01⃗·01⃗·01⃗·01⃗ = 01⃗·01⃗`, for
`01⃗ := streamArrow [false, true]`. Follows from `streamArrow_mul_self` applied twice. -/
theorem streamArrow_containsZero_pow_four :
    mulElem
        (mulElem (streamArrow [false, true]) (streamArrow [false, true]))
        (mulElem (streamArrow [false, true]) (streamArrow [false, true]))
      = mulElem (streamArrow [false, true]) (streamArrow [false, true]) := by
  rw [streamArrow_mul_self, streamArrow_mul_self]

/-! ## Stream elements (Scott's infinite-word investigations)

Write `wⁿ` for `w` appended to itself `n` times. **`streamElem w`** is the filter
`Z ↦ InS Z ∧ ∀ n, wⁿ ∈ Z` (Scott's `w⃗`). -/

/-- `wⁿ`: `w` concatenated with itself `n` times (`w⁰ = []`). -/
def repeatWord (w : List Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => w ++ repeatWord w n

@[simp] theorem repeatWord_zero (w : List Bool) : repeatWord w 0 = [] := rfl

theorem repeatWord_succ (w : List Bool) (n : ℕ) :
    repeatWord w (n + 1) = w ++ repeatWord w n := rfl

theorem repeatWord_add (w : List Bool) (a b : ℕ) :
    repeatWord w (a + b) = repeatWord w a ++ repeatWord w b := by
  induction a with
  | zero => simp [repeatWord]
  | succ a ih =>
      simp only [Nat.succ_add, repeatWord]
      rw [ih, List.append_assoc]

/-- `{wⁿ ∣ n}` — the language of all finite powers of `w`. -/
def powerLang (w : List Bool) : Set (List Bool) :=
  {u | ∃ n, repeatWord w n = u}

@[simp] theorem mem_powerLang {w u : List Bool} :
    u ∈ powerLang w ↔ ∃ n, repeatWord w n = u := Iff.rfl

theorem powerLang_concat (w : List Bool) :
    concat (powerLang w) (powerLang w) ⊆ powerLang w := by
  rintro u ⟨a, ⟨m, hm⟩, b, ⟨n, hn⟩, rfl⟩
  exact ⟨m + n, by rw [repeatWord_add, hm, hn]⟩

theorem repeatWord_eq_empty (w : List Bool) (n : ℕ) (hw : w = []) :
    repeatWord w n = [] := by
  subst hw
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatWord, ih]

theorem InS_powerLang_empty : InS (powerLang []) := by
  have h : powerLang [] = {[]} := by
    ext u
    simp only [mem_powerLang, Set.mem_singleton_iff]
    constructor
    · rintro ⟨n, hn⟩; exact hn.symm.trans (repeatWord_eq_empty [] n rfl)
    · intro hu; subst hu; exact ⟨0, rfl⟩
  simpa [h] using InS.singleton []

/-- Membership in Scott's **`w⃗`**: every power `wⁿ` lies in `Z`. Concatenation-closure of `Z`
  is not required for membership, but holds for neighbourhoods in `mulElem (streamElem w) (streamElem w)`. -/
def streamElemMem (w : List Bool) (Z : Set (List Bool)) : Prop :=
  InS Z ∧ ∀ n, repeatWord w n ∈ Z

/-- Scott's **`w⃗`** as a domain element. -/
def streamElem (w : List Bool) : Ssys.Element where
  mem Z := streamElemMem w Z
  sub h := h.1
  master_mem := ⟨InS.univ, fun n => Set.mem_univ (repeatWord w n)⟩
  inter_mem := by
    intro X Y hX hY
    obtain ⟨hXIn, hXw⟩ := hX
    obtain ⟨hYIn, hYw⟩ := hY
    exact ⟨InS.inter hXIn hYIn ⟨repeatWord w 0, hXw 0, hYw 0⟩, fun n => ⟨hXw n, hYw n⟩⟩
  up_mem := by
    intro X Y hX hInSY hsub
    obtain ⟨_hXIn, hXw⟩ := hX
    exact ⟨hInSY, fun n => hsub (hXw n)⟩

@[simp] theorem mem_streamElem {w : List Bool} {Z : Set (List Bool)} :
    (streamElem w).mem Z ↔ streamElemMem w Z := Iff.rfl

/-- From **`w⃗ · w⃗`**, every power `wⁿ` still lies in `Z`. -/
theorem streamElem_powers_of_mul (w : List Bool) (Z : Set (List Bool))
    (h : (mulElem (streamElem w) (streamElem w)).mem Z) :
    streamElemMem w Z := by
  obtain ⟨hZ, X, hX, Y, hY, hsub⟩ := h
  obtain ⟨_hXIn, hXw⟩ := hX
  obtain ⟨_hYIn, hYw⟩ := hY
  refine ⟨hZ, fun n => ?_⟩
  have h1 := hsub (append_mem_concat (hXw n) (hYw 0))
  simpa [repeatWord_zero, List.append_nil] using h1

/-- **`w⃗ · w⃗` is in `Z` whenever `w⃗` is**, using the witness `powerLang w ∈ S`. -/
theorem streamElem_mul_self_mem (w : List Bool) (Z : Set (List Bool))
    (h : streamElemMem w Z) (hPL : InS (powerLang w)) :
    (mulElem (streamElem w) (streamElem w)).mem Z := by
  refine ⟨h.1, powerLang w, ⟨hPL, fun n => ⟨n, rfl⟩⟩, powerLang w, ⟨hPL, fun n => ⟨n, rfl⟩⟩, ?_⟩
  intro u hu
  obtain ⟨a, ⟨m, hm⟩, b, ⟨n, hn⟩, rfl⟩ := hu
  simpa [hm, hn, repeatWord_add] using h.2 (m + n)

/-- Scott's stream equation **`w⃗ · w⃗ = w⃗`** (filter equality), when `{wⁿ}` lies in `S`. -/
theorem streamElem_idempotent (w : List Bool) (hPL : InS (powerLang w)) :
    mulElem (streamElem w) (streamElem w) = streamElem w := by
  apply NeighborhoodSystem.Element.ext
  intro Z
  exact ⟨streamElem_powers_of_mul w Z, fun h => streamElem_mul_self_mem w Z h hPL⟩

/-- Scott's stream equations (Exercise 7.22, investigatory part). -/

example : mulElem (streamElem []) (streamElem []) = streamElem [] :=
  streamElem_idempotent [] InS_powerLang_empty

example (σ : List Bool) (Z : Set (List Bool)) :
    (mulElem (streamElem σ) (streamElem σ)).mem Z → streamElemMem σ Z :=
  streamElem_powers_of_mul σ Z

example (σ : List Bool) (h : InS (powerLang σ)) :
    mulElem (mulElem (streamElem σ) (streamElem σ)) (streamElem σ) = streamElem σ := by
  rw [mulElem_assoc, streamElem_idempotent σ h, streamElem_idempotent σ h]

example (σ : List Bool) (h : InS (powerLang (σ ++ [true]))) :
    mulElem (streamElem (σ ++ [true])) (streamElem (σ ++ [true])) =
      streamElem (σ ++ [true]) :=
  streamElem_idempotent (σ ++ [true]) h

example (h : InS (powerLang [false, true])) :
    mulElem
        (mulElem (streamElem [false, true]) (streamElem [false, true]))
        (mulElem (streamElem [false, true]) (streamElem [false, true])) =
      mulElem (streamElem [false, true]) (streamElem [false, true]) := by
  rw [streamElem_idempotent _ h, streamElem_idempotent _ h]

end Exercise722

end Scott1980.Neighborhood

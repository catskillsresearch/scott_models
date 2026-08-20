/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Basic
import Scott1980.Neighborhood.Exercise120
import Mathlib.Tactic

/-!
# Definition 7.9 (Scott 1981, PRG-19, §7) — the Smyth power domain `ℙ𝒟`

Scott closes Lecture VII with "an example of another kind of domain construct", the
*Smyth Power Domain*. For any neighbourhood system `𝒟` it builds a new system `ℙ𝒟` whose
elements behave like *sets of elements* of `𝒟`.

**Definition 7.9.** For a neighbourhood system `𝒟`,

`ℙ𝒟 = { ⋃_{i<n} (↓Xᵢ) ∣ ∀ i<n. Xᵢ ∈ 𝒟 }`,

where the **down-set** of `X ∈ 𝒟` is `↓X = {Y ∈ 𝒟 ∣ Y ⊆ X}`. The finite unions can be
*empty* (`n = 0`), giving the neighbourhood `∅`.

Two surrounding remarks Scott records as part of the definition:

* The construct is made *isomorphism-invariant* by first **preparing** `𝒟`: replace it by the
  isomorphic positive system `𝒟† = {↓X ∣ X ∈ 𝒟}` (Exercise 1.20). Then `ℙ𝒟` is the closure of
  `𝒟†` under finite unions.
* `↓X ∩ ↓Y ≠ ∅` iff `{X, Y}` is consistent in `𝒟`, and in that case `↓X ∩ ↓Y = ↓(X ∩ Y)`.

## What this file formalizes

Scott's `↓X` of §7 is *exactly* the set `Exercise 1.20` already named `upSet`
(`{Y ∈ 𝒟 ∣ Y ⊆ X}`), and the preparation `𝒟†` is exactly Exercise 1.20's `powerSystem`
(here aliased `dagger`, with the iso `dagger_isomorphic : 𝒟 ≅ᴰ 𝒟†` reusing
`isomorphic_powerSystem`). On top of those we add:

* `PDmem` — the neighbourhood family of `ℙ𝒟` (finite unions of down-sets, indexed by a
  `List` of `𝒟`-neighbourhoods; the empty list realizes the empty union `n = 0`);
* `mem_PDunion` / `PDmem_empty` / `PDmem_upSet` / `PDmem_master` / `PDmem_union` — the basic
  membership facts that pin the family down (it contains `∅`, every down-set `↓X`, the
  master `↓Δ`, and is closed under binary — hence finite — union);
* `PDmem_iff_fin` — the same family written with Scott's `⋃_{i<n}` (a `Fin n → Set 𝒟`);
* the two displayed remarks: `upSet_inter_nonempty_iff` (`↓X ∩ ↓Y ≠ ∅ ↔ {X,Y}` consistent)
  and, in the consistent case, `dagger_upSet_inter` (`↓X ∩ ↓Y = ↓(X∩Y) ∈ 𝒟†`); the
  unconditional set identity `↓X ∩ ↓Y = ↓(X∩Y)` is Exercise 1.20's `upSet_inter`.

This is everything Scott states as part of Definition 7.9 itself; that `ℙ𝒟` is *itself a
neighbourhood system*, effectively given when `𝒟` is, is the separate **Proposition 7.10**
(`Proposition710.lean`). Everything here is choice-free (`⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Definition 7.9 — the preparation `𝒟†`.** Scott prepares `𝒟` for the power-domain
construct by replacing it with the isomorphic system `𝒟† = {↓X ∣ X ∈ 𝒟}`, which is exactly
Exercise 1.20's `powerSystem` (over the token type `Δ† = 𝒟`, i.e. `Set α`). It is a *positive*
neighbourhood system (`powerSystem_isPositive`). -/
abbrev dagger : NeighborhoodSystem (Set α) := V.powerSystem

/-- **Definition 7.9 — `𝒟 ≅ 𝒟†` (Exercise 1.20).** The preparation does not change the domain:
`𝒟` and `𝒟†` are isomorphic. (This is what makes `ℙ𝒟` isomorphism-invariant.) -/
theorem dagger_isomorphic : V ≅ᴰ V.dagger := V.isomorphic_powerSystem

/-- **Definition 7.9 — the Smyth power domain `ℙ𝒟`.** A set `W : Set (Set α)` is a
neighbourhood of `ℙ𝒟` iff it is a *finite union of down-sets* `⋃_{X ∈ L} ↓X` for some finite
list `L` of `𝒟`-neighbourhoods. The empty list `L = []` realizes Scott's `n = 0` (the empty
union `∅`). -/
def PDmem (W : Set (Set α)) : Prop :=
  ∃ L : List (Set α), (∀ X ∈ L, V.mem X) ∧ W = ⋃ X ∈ L, V.upSet X

/-- Membership in a finite union of down-sets: `z ∈ ⋃_{X∈L} ↓X ↔ ∃ X ∈ L, z ∈ ↓X`. -/
theorem mem_PDunion {L : List (Set α)} {z : Set α} :
    z ∈ (⋃ X ∈ L, V.upSet X) ↔ ∃ X ∈ L, z ∈ V.upSet X := by
  simp only [Set.mem_iUnion, exists_prop]

/-- **Definition 7.9 — the empty union.** "The finite unions in `ℙ𝒟` can be empty (i.e. if
`n = 0`)." The empty neighbourhood `∅` is a neighbourhood of `ℙ𝒟` (witnessed by `L = []`). -/
theorem PDmem_empty : V.PDmem ∅ := by
  refine ⟨[], ?_, ?_⟩
  · intro X hX; cases hX
  · ext z
    rw [mem_PDunion]
    constructor
    · intro h; exact absurd h (Set.notMem_empty z)
    · rintro ⟨X, hX, _⟩; cases hX

/-- **Definition 7.9 — singletons.** Every down-set `↓X` (`X ∈ 𝒟`) is a neighbourhood of `ℙ𝒟`
(the case `n = 1`); these are exactly the neighbourhoods of the prepared system `𝒟†`. -/
theorem PDmem_upSet {X : Set α} (hX : V.mem X) : V.PDmem (V.upSet X) := by
  refine ⟨[X], ?_, ?_⟩
  · intro Y hY; rw [List.mem_singleton] at hY; subst hY; exact hX
  · ext z
    rw [mem_PDunion]
    constructor
    · intro hz; exact ⟨X, List.mem_singleton.mpr rfl, hz⟩
    · rintro ⟨Y, hY, hz⟩; rw [List.mem_singleton] at hY; subst hY; exact hz

/-- **Definition 7.9 — the master neighbourhood `↓Δ`.** The largest neighbourhood of `ℙ𝒟` is
`↓Δ = 𝒟` (all `𝒟`-neighbourhoods), itself a finite union (the case `X₀ = Δ`). -/
theorem PDmem_master : V.PDmem (V.upSet V.master) := V.PDmem_upSet V.master_mem

/-- **Definition 7.9 — closure under finite unions.** `ℙ𝒟` is closed under binary union
(concatenate the index lists); with `PDmem_empty` this gives closure under all finite unions,
which is exactly how Scott defines the family. -/
theorem PDmem_union {W₁ W₂ : Set (Set α)} (h₁ : V.PDmem W₁) (h₂ : V.PDmem W₂) :
    V.PDmem (W₁ ∪ W₂) := by
  obtain ⟨L₁, hL₁, rfl⟩ := h₁
  obtain ⟨L₂, hL₂, rfl⟩ := h₂
  refine ⟨L₁ ++ L₂, ?_, ?_⟩
  · intro X hX
    rcases List.mem_append.mp hX with h | h
    · exact hL₁ X h
    · exact hL₂ X h
  · ext z
    simp only [Set.mem_union, Set.mem_iUnion, exists_prop, List.mem_append]
    constructor
    · rintro (⟨X, hX, hz⟩ | ⟨X, hX, hz⟩)
      · exact ⟨X, Or.inl hX, hz⟩
      · exact ⟨X, Or.inr hX, hz⟩
    · rintro ⟨X, hX | hX, hz⟩
      · exact Or.inl ⟨X, hX, hz⟩
      · exact Or.inr ⟨X, hX, hz⟩

/-- **Definition 7.9 — Scott's `⋃_{i<n}` form.** The neighbourhood family of `ℙ𝒟`, written with
a finite sequence `X : Fin n → 𝒟` exactly as Scott displays it: `W = ⋃_{i<n} ↓Xᵢ` with each
`Xᵢ ∈ 𝒟`. Equivalent to the `List` form via `List.ofFn` / `List.get`. -/
theorem PDmem_iff_fin {W : Set (Set α)} :
    V.PDmem W ↔ ∃ (n : ℕ) (X : Fin n → Set α),
      (∀ i, V.mem (X i)) ∧ W = ⋃ i, V.upSet (X i) := by
  constructor
  · rintro ⟨L, hL, rfl⟩
    refine ⟨L.length, L.get, fun i => hL _ (L.get_mem i), ?_⟩
    ext z
    rw [mem_PDunion, Set.mem_iUnion]
    constructor
    · rintro ⟨X, hX, hz⟩
      obtain ⟨i, rfl⟩ := List.get_of_mem hX
      exact ⟨i, hz⟩
    · rintro ⟨i, hz⟩
      exact ⟨L.get i, L.get_mem i, hz⟩
  · rintro ⟨n, X, hX, rfl⟩
    refine ⟨List.ofFn X, ?_, ?_⟩
    · intro Y hY
      obtain ⟨i, rfl⟩ := Set.mem_range.mp (List.mem_ofFn.mp hY)
      exact hX i
    · ext z
      rw [Set.mem_iUnion, mem_PDunion]
      constructor
      · rintro ⟨i, hz⟩
        exact ⟨X i, List.mem_ofFn.mpr (Set.mem_range.mpr ⟨i, rfl⟩), hz⟩
      · rintro ⟨Y, hY, hz⟩
        obtain ⟨i, rfl⟩ := Set.mem_range.mp (List.mem_ofFn.mp hY)
        exact ⟨i, hz⟩

/-! ### Definition 7.9 — the two displayed intersection remarks -/

/-- **Definition 7.9 (remark 1).** "`↓X ∩ ↓Y ≠ ∅` iff `{X, Y}` is consistent in `𝒟`." The
down-sets `↓X`, `↓Y` meet exactly when `X, Y` have a common lower neighbourhood `Z ⊆ X ∩ Y`. -/
theorem upSet_inter_nonempty_iff {X Y : Set α} :
    (V.upSet X ∩ V.upSet Y).Nonempty ↔ ∃ Z, V.mem Z ∧ Z ⊆ X ∩ Y := by
  rw [V.upSet_inter]
  constructor
  · rintro ⟨Z, hZmem, hZsub⟩; exact ⟨Z, hZmem, hZsub⟩
  · rintro ⟨Z, hZmem, hZsub⟩; exact ⟨Z, hZmem, hZsub⟩

/-- **Definition 7.9 (remark 2).** "In that case `↓X ∩ ↓Y = ↓(X ∩ Y)`." When `{X, Y}` is
consistent (witness `Z ⊆ X ∩ Y`, `Z ∈ 𝒟`), the intersection `X ∩ Y` is again a neighbourhood,
so `↓X ∩ ↓Y = ↓(X ∩ Y)` is a neighbourhood of the prepared system `𝒟†`. (The unconditional set
identity `↓X ∩ ↓Y = ↓(X ∩ Y)` is Exercise 1.20's `upSet_inter`; the content here is membership
in `𝒟†`.) -/
theorem dagger_upSet_inter {X Y Z : Set α} (hX : V.mem X) (hY : V.mem Y) (hZ : V.mem Z)
    (hsub : Z ⊆ X ∩ Y) : V.dagger.mem (V.upSet X ∩ V.upSet Y) := by
  rw [V.upSet_inter]
  exact ⟨X ∩ Y, V.inter_mem hX hY hZ hsub, rfl⟩

end NeighborhoodSystem

end Scott1980.Neighborhood

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Approximable
import Scott1980.Neighborhood.ExampleB
import Scott1980.Neighborhood.Example23

/-!
# Exercise 2.16 (Scott 1981, PRG-19, §2) — the prefixing map `x ↦ σx` is approximable

In Lecture I (Example 1.B) Scott defined, for each finite string `σ ∈ Σ*`, the elementwise operation
`x ↦ σx` on `|B|` (`ExampleB.sigmaElt`). Exercise 2.16 asks whether this mapping is *approximable*.
It is: the witnessing neighbourhood relation is

`X f Y ↔ X, Y ∈ B ∧ σX ⊆ Y`,

i.e. "the prefixed input cone `σX` is at least as sharp as `Y`." We package it as
`sigmaMap σ : ApproximableMap B B` and show its elementwise action is exactly `sigmaElt σ`
(`toElementMap_sigmaMap`).

**Second half.** Scott also asks to show that the parity map `f : B → T` of Example 2.3
(`Example23.parityMap`) is *uniquely* determined among approximable mappings by the three
equations `f(1x)=true`, `f(01x)=false`, `f(00x)=f(x)` (`SatisfiesParityEquations`). We check
`parityMap` itself satisfies them (`Example23.parityMap_toElementMap_sigmaElt`, so the statement
is non-vacuous) and then prove uniqueness (`eq_parityMap_of_satisfies`): the recursive core
(`key`) pins down any such `g` on every principal element `σ⊥`, peeling two tokens of `σ` at a
time (mirroring `scan`'s own recursion); the base case `σ = []` and the leftover singleton
`σ = [false]` are the two places genuine order theory (flatness of `𝒯`, `Example23.eq_botElt_of_le`)
enters, everything else being pure substitution into the equations.

Constructive except for the `by_cases` in `ApproximableMap.ext`'s use of `Classical.em`
(`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`). -/

namespace Scott1980.Neighborhood.Exercise216

open Scott1980.Neighborhood NeighborhoodSystem ExampleB

/-- **Exercise 2.16 — `x ↦ σx` is approximable.** The neighbourhood relation `X f Y ↔ σX ⊆ Y`
(confined to `B × B`). Definition 2.1: (i) `σΔ ⊆ Δ`; (ii) the prefixed cone `σX` is a common lower
bound of `Y, Y'`, witnessing `Y ∩ Y' ∈ B`; (iii) `prepend_mono` shrinks `σX'` as `X' ⊆ X`. -/
def sigmaMap (σ : Str) : ApproximableMap B B where
  rel X Y := B.mem X ∧ B.mem Y ∧ prepend σ X ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨B.master_mem, B.master_mem, Set.subset_univ _⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hsub⟩ ⟨_, hY', hsub'⟩
    have hpre : B.mem (prepend σ X) := memB_prepend σ hX
    have hsubInter : prepend σ X ⊆ Y ∩ Y' := Set.subset_inter hsub hsub'
    exact ⟨hX, B.inter_mem hY hY' hpre hsubInter, hsubInter⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hsub⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', ((prepend_mono σ hX'X).trans hsub).trans hYY'⟩

/-- **Exercise 2.16.** The elementwise action of `sigmaMap σ` is Scott's `σx`: `(sigmaMap σ)(x) =
σx` for every `x ∈ |B|`. -/
theorem toElementMap_sigmaMap (σ : Str) (x : B.Element) :
    (sigmaMap σ).toElementMap x = sigmaElt σ x := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hxX, _, hY, hsub⟩
    exact ⟨hY, X, hxX, hsub⟩
  · rintro ⟨hY, X, hxX, hsub⟩
    exact ⟨X, hxX, x.sub hxX, hY, hsub⟩

/-! ## Exercise 2.16, second half — the parity map is *uniquely* determined by its equations -/

/-- **The three equations of Exercise 2.16.** `f(1x) = true`, `f(01x) = false`, `f(00x) = f(x)`,
for *every* `x : |B|`. -/
structure SatisfiesParityEquations (g : ApproximableMap B Example23.T) : Prop where
  one : ∀ x : B.Element, g.toElementMap (sigmaElt [true] x) = Example23.trueElt
  zeroOne : ∀ x : B.Element, g.toElementMap (sigmaElt [false, true] x) = Example23.falseElt
  zeroZero : ∀ x : B.Element, g.toElementMap (sigmaElt [false, false] x) = g.toElementMap x

/-- **`parityMap` satisfies its own defining equations.** Each is a direct instance of the
"shift formula" `Example23.parityMap_toElementMap_sigmaElt`, using that a leading `1` (resp. `01`,
`00`) fixes the scan of the concatenation `σ ++ τ` regardless of the tail `τ`
(`scan_append_true`/`scan_append_falseTrue`/`scan_append_falseFalse`). -/
theorem parityMap_satisfies : SatisfiesParityEquations Example23.parityMap where
  one x := by
    apply Element.ext
    intro Y
    rw [Example23.parityMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, _, hval⟩
      rwa [Example23.scan_append_true] at hval
    · intro hval
      exact ⟨[], by rw [cone_nil]; exact x.master_mem, by rwa [Example23.scan_append_true]⟩
  zeroOne x := by
    apply Element.ext
    intro Y
    rw [Example23.parityMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, _, hval⟩
      rwa [Example23.scan_append_falseTrue] at hval
    · intro hval
      exact ⟨[], by rw [cone_nil]; exact x.master_mem, by rwa [Example23.scan_append_falseTrue]⟩
  zeroZero x := by
    apply Element.ext
    intro Y
    rw [Example23.parityMap_toElementMap_sigmaElt, Example23.parityMap_toElementMap_mem]
    constructor
    · rintro ⟨τ, hτ, hval⟩
      exact ⟨τ, hτ, by rwa [Example23.scan_append_falseFalse] at hval⟩
    · rintro ⟨τ, hτ, hval⟩
      exact ⟨τ, hτ, by rwa [Example23.scan_append_falseFalse]⟩

/-- **The recursive core of uniqueness.** Any `g` satisfying the three equations agrees with
`parityMap` on every principal (finite) element `σ⊥`. Recursion peels *two* tokens at a time
(mirroring `scan`'s own recursion `scan(00τ)=scanτ`): `1τ` and `01τ` are pinned directly by
`hg.one`/`hg.zeroOne` for *any* tail (no recursion needed there); `00τ` reduces to `τ` by
`hg.zeroZero`, decreasing structurally. The base case `σ = []` and the leftover singleton
`σ = [false]` (an odd trailing zero, never reached by the two-at-a-time step) are the two places
genuine order theory enters: `⊥ ≤ 1⊥` and `⊥ ≤ 01⊥` force `g(⊥) ≤ true` and `g(⊥) ≤ false`, and
`⊥` is the *only* element below both (`eq_botElt_of_le`, `𝒯`'s flatness); the singleton then
follows by squeezing `g(0⊥)` between `⊥` and `g(00⊥) = g(⊥)` via monotonicity. -/
theorem key (g : ApproximableMap B Example23.T) (hg : SatisfiesParityEquations g) :
    ∀ σ : Str, g.toElementMap (sigmaElt σ B.bot) = Example23.valElt (Example23.scan σ)
  | [] => by
      rw [sigmaElt_nil]
      have h1 : g.toElementMap B.bot ≤ Example23.trueElt := by
        have hm := g.toElementMap_mono (B.bot_le (sigmaElt [true] B.bot))
        rwa [hg.one] at hm
      have h2 : g.toElementMap B.bot ≤ Example23.falseElt := by
        have hm := g.toElementMap_mono (B.bot_le (sigmaElt [false, true] B.bot))
        rwa [hg.zeroOne] at hm
      exact Example23.eq_botElt_of_le h1 h2
  | [false] => by
      have hbase : g.toElementMap B.bot = Example23.botElt := by
        have h0 := key g hg []
        rwa [sigmaElt_nil] at h0
      have hb : sigmaElt [false] B.bot ≤ sigmaElt [false, false] B.bot := by
        rw [sigmaElt_bot, sigmaElt_bot]
        exact (sigmaBot_le_iff _ _).mpr ⟨[false], rfl⟩
      have hm : g.toElementMap (sigmaElt [false] B.bot) ≤ Example23.botElt := by
        have := g.toElementMap_mono hb
        rwa [hg.zeroZero, hbase] at this
      have hm2 : Example23.botElt ≤ g.toElementMap (sigmaElt [false] B.bot) :=
        Example23.botElt_le _
      exact (le_antisymm hm hm2).trans rfl
  | (true :: t) => by
      rw [show (true :: t : Str) = [true] ++ t from rfl, sigmaElt_append, hg.one,
        Example23.scan_append_true]
      rfl
  | (false :: true :: t) => by
      rw [show (false :: true :: t : Str) = [false, true] ++ t from rfl, sigmaElt_append,
        hg.zeroOne, Example23.scan_append_falseTrue]
      rfl
  | (false :: false :: t) => by
      rw [show (false :: false :: t : Str) = [false, false] ++ t from rfl, sigmaElt_append,
        hg.zeroZero, key g hg t, Example23.scan_append_falseFalse]

/-- **Exercise 2.16, second half.** `parityMap` is the *unique* approximable map `B → T`
satisfying `f(1x)=true`, `f(01x)=false`, `f(00x)=f(x)`. Every neighbourhood of `B` is a cone
(`memB_cone`), so `ApproximableMap.ext` reduces `g = parityMap` to matching relations on cones,
which is exactly `key` read through `rel_iff_mem_principal`/`parityMap_rel_cone`. -/
theorem eq_parityMap_of_satisfies {g : ApproximableMap B Example23.T}
    (hg : SatisfiesParityEquations g) : g = Example23.parityMap := by
  apply ApproximableMap.ext
  intro X Y
  by_cases hX : B.mem X
  · obtain ⟨σ, rfl⟩ := hX
    rw [g.rel_iff_mem_principal (memB_cone σ)]
    show (g.toElementMap (sigmaBot σ)).mem Y ↔ Example23.parityMap.rel (cone σ) Y
    rw [← sigmaElt_bot, key g hg σ, Example23.parityMap_rel_cone]
  · exact ⟨fun hr => absurd (g.rel_dom hr) hX,
      fun hr => absurd (Example23.parityMap.rel_dom hr) hX⟩

end Scott1980.Neighborhood.Exercise216

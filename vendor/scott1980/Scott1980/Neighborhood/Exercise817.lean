/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Theorem88a
import Scott1980.Neighborhood.Lemma615
import Scott1980.Neighborhood.Proposition612
import Scott1980.Neighborhood.Theorem69
import Scott1980.Neighborhood.Definition89
import Scott1980.Neighborhood.Exercise812g4

/-!
# Exercise 8.17 (Scott 1981, PRG-19)

> **Exercise 8.17.** Find explicitly (if possible) the projection pairs for `𝒰+𝒰`, `𝒰×𝒰`, and
> `𝒰→𝒰` needed for 8.9. Are any of these domains isomorphic with `𝒰`? (The author does not know a
> really good construction for `𝒰→𝒰`.) Find a universal domain `V ≠ 𝒰`.

## What is formalized here

**Part 1** (projection pairs for 8.9) is already fully answered by `Definition89.lean`: `iPlus/jPlus`,
`iTimes/jTimes`, `iArrow/jArrow` are exactly computable projection pairs `𝒰+𝒰 ⇄ 𝒰`, `𝒰×𝒰 ⇄ 𝒰`,
`𝒰→𝒰 ⇄ 𝒰` (via `theorem_8_8_b_strong`), so this file only *restates* them under §8.17's name, and
adds the free bonus corollary `sumUU_trianglelefteq_U`/`prodUU_trianglelefteq_U`/
`funSpaceUU_trianglelefteq_U : (·) ⊴ 𝒰` (Lemma 6.15 applied to those exact pairs).

**Part 3** (a universal domain `V ≠ 𝒰`) is answered in full: Exercise 8.12's `V` (a *different*
`NeighborhoodSystem`, over `ℕ` rather than `𝒰`'s `ℚ`, built from `2^kℕ+ℓ`) is effectively isomorphic
to `𝒰` (`effectiveIso812_UV`), hence — since universality (`𝒰`'s defining property, Theorem 8.8(a))
transports along isomorphism — `V` is *also* universal (`V_isUniversal`). This needed one genuinely
new general-purpose tool, **`⊴` is transitive** (`trianglelefteq_trans`), built by composing
`ProjectionPair`s (a new `ProjectionPair.comp`, plus `ProjectionPair.ofIso` turning any `DomainIso`
into a projection pair via Theorem 2.7's `ofIso`) — surprisingly, `⊴`'s transitivity was not yet in
the codebase despite being an obviously expected structural fact.

**Part 2** (are `𝒰+𝒰`/`𝒰×𝒰`/`𝒰→𝒰` isomorphic to `𝒰`?) is **deliberately left open/deferred** here,
documented rather than guessed at: what we get for free is only the *one-directional* embeddings
`𝒰+𝒰, 𝒰×𝒰, 𝒰→𝒰 ⊴ 𝒰` (bonus corollaries above). Establishing genuine *isomorphism* `𝒰+𝒰 ≅ 𝒰` (or
`×`) would need a **converse embedding plus a back-and-forth argument** of the same scale as Exercise
8.12's 7-part, ~2000-line development (`arxiv.md`'s Exercise 8.12 row: "order isos preserve
compactness... so `U≅V` is not just tedious to build, it needs a genuinely different technique").
Scott's own parenthetical — "the author does not know a really good construction for `𝒰→𝒰`" — flags
that even *he* did not resolve the `→` case; we do not attempt to go further than Scott here. This is
therefore recorded as a clearly-scoped deferral, not a `sorry`.

Everything proved in this file is **choice-free** (`⊆ {propext, Quot.sound}`) except where it merely
*mentions* `U`/`V` (which inherit `Classical.choice` from `Definition87.lean`'s `Rat`-order-instance
provenance, the same footprint as every other `U`-mentioning headline theorem in this project).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap Subsystem

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-! ## A general tool: `⊴` is transitive (not yet in the codebase)

`Subsystem.ProjectionPair` (`Proposition612.lean`) is deliberately single-token-type (`D E :
NeighborhoodSystem α`), since it is built for the *homogeneous* `D ◁ E` case. `⊴`'s projection pairs
are heterogeneous (`i : ApproximableMap D E`, `j : ApproximableMap E D`, possibly different token
types), so we bundle a small local heterogeneous analogue, `ProjPair`, purely as scaffolding for
`trianglelefteq_trans` below. -/

/-- **A heterogeneous projection pair** — the raw data `Lemma615.trianglelefteq_of_projectionPair`
consumes, bundled for easy composition. -/
structure ProjPair (D : NeighborhoodSystem α) (E : NeighborhoodSystem β) where
  /-- The injection `i : D → E`. -/
  inj : ApproximableMap D E
  /-- The projection `j : E → D`. -/
  proj : ApproximableMap E D
  /-- `j ∘ i = I_D`. -/
  proj_comp_inj : proj.comp inj = idMap D
  /-- `i ∘ j ⊆ I_E`. -/
  inj_comp_proj_le : inj.comp proj ≤ idMap E

/-- **A subsystem relation `D ◁ E` gives a `ProjPair`** (Proposition 6.12, rebundled). -/
def ProjPair.ofSubsystem {D E : NeighborhoodSystem α} (h : D ◁ E) : ProjPair D E where
  inj := h.inj
  proj := h.proj
  proj_comp_inj := h.proj_comp_inj
  inj_comp_proj_le := h.inj_comp_proj_le

/-- **A `DomainIso` gives a `ProjPair`, via Theorem 2.7's `ofIso`.** Both round trips are genuine
*equalities* (not just `≤`), since `e` is a full isomorphism, not merely a retraction. Uses
`le_iff_toElementMap_le` (choice-free) rather than the classical `ext_of_toElementMap` — matching
`Theorem86.lean`'s `isRetraction_subApprox`, which flags the same discipline. -/
def ProjPair.ofIso {D : NeighborhoodSystem α} {E : NeighborhoodSystem β} (e : DomainIso D E) :
    ProjPair D E where
  inj := ApproximableMap.ofIso e
  proj := ApproximableMap.ofIso e.symm
  proj_comp_inj := by
    have heq : ∀ x, ((ApproximableMap.ofIso e.symm).comp (ApproximableMap.ofIso e)).toElementMap x
        = (idMap D).toElementMap x := by
      intro x
      rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, OrderIso.symm_apply_apply,
        toElementMap_idMap]
    exact le_antisymm (le_iff_toElementMap_le.mpr fun x => (heq x).le)
      (le_iff_toElementMap_le.mpr fun x => (heq x).ge)
  inj_comp_proj_le := by
    have heq : ∀ y, ((ApproximableMap.ofIso e).comp (ApproximableMap.ofIso e.symm)).toElementMap y
        = (idMap E).toElementMap y := by
      intro y
      rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, OrderIso.apply_symm_apply,
        toElementMap_idMap]
    exact le_iff_toElementMap_le.mpr fun y => (heq y).le

/-- **`ProjPair`s compose.** If `D ⇄ E` and `E ⇄ F` are projection pairs, so is `D ⇄ F`
(`inj := p2.inj ∘ p1.inj`, `proj := p1.proj ∘ p2.proj`). The first law composes as an equality
chain; the second only needs `≤`, transported through `comp_mono_gen`. -/
def ProjPair.comp {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
    {F : NeighborhoodSystem γ} (p1 : ProjPair D E) (p2 : ProjPair E F) :
    ProjPair D F where
  inj := p2.inj.comp p1.inj
  proj := p1.proj.comp p2.proj
  proj_comp_inj := by
    show (p1.proj.comp p2.proj).comp (p2.inj.comp p1.inj) = idMap D
    rw [comp_assoc, ← comp_assoc p2.proj p2.inj p1.inj, p2.proj_comp_inj, idMap_comp,
      p1.proj_comp_inj]
  inj_comp_proj_le := by
    show (p2.inj.comp p1.inj).comp (p1.proj.comp p2.proj) ≤ idMap F
    rw [comp_assoc, ← comp_assoc p1.inj p1.proj p2.proj]
    calc p2.inj.comp ((p1.inj.comp p1.proj).comp p2.proj)
        ≤ p2.inj.comp ((idMap E).comp p2.proj) :=
          comp_mono_gen le_rfl (comp_mono_gen p1.inj_comp_proj_le le_rfl)
      _ = p2.inj.comp p2.proj := by rw [idMap_comp]
      _ ≤ idMap F := p2.inj_comp_proj_le

/-- **`D ⊴ E` composed with an isomorphism `D ≅ᴰ D'` on the left is still `D ⊴ E`** — immediate
from unfolding `⊴` and composing the two `DomainIso`s (`OrderIso.trans`). -/
theorem trianglelefteq_of_isomorphic_left {D : NeighborhoodSystem α} {D' : NeighborhoodSystem β}
    {E : NeighborhoodSystem γ} (hDD' : D ≅ᴰ D') (hD'E : D' ⊴ E) : D ⊴ E := by
  obtain ⟨F, hFE, ⟨eD'F⟩⟩ := hD'E
  obtain ⟨eDD'⟩ := hDD'
  exact ⟨F, hFE, ⟨eDD'.trans eD'F⟩⟩

/-- **`⊴` is transitive.** `D ⊴ E` and `E ⊴ F` give `D ⊴ F`: unfold both to a subsystem `D' ◁ E`
(`D ≅ᴰ D'`) and `E' ◁ F` (`E ≅ᴰ E'`); `ProjPair.ofSubsystem` turns `D' ◁ E`/`E' ◁ F` into projection
pairs, `ProjPair.ofIso` turns `E ≅ᴰ E'` into one too, and composing all three (`ProjPair.comp`) gives
a projection pair `D' ⇄ F`, hence `D' ⊴ F` (Lemma 6.15). Gluing back `D ≅ᴰ D'` on the left
(`trianglelefteq_of_isomorphic_left`) finishes. -/
theorem trianglelefteq_trans {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
    {F : NeighborhoodSystem γ} (h1 : D ⊴ E) (h2 : E ⊴ F) : D ⊴ F := by
  obtain ⟨D', hD'E, ⟨eDD'⟩⟩ := h1
  obtain ⟨E', hE'F, ⟨eEE'⟩⟩ := h2
  have pD'F : ProjPair D' F :=
    ((ProjPair.ofSubsystem hD'E).comp (ProjPair.ofIso eEE')).comp (ProjPair.ofSubsystem hE'F)
  have hD'F : D' ⊴ F :=
    trianglelefteq_of_projectionPair pD'F.inj pD'F.proj pD'F.proj_comp_inj pD'F.inj_comp_proj_le
  exact trianglelefteq_of_isomorphic_left ⟨eDD'⟩ hD'F

/-! ## Part 1 — the projection pairs for `𝒰+𝒰`, `𝒰×𝒰`, `𝒰→𝒰` needed for 8.9 -/

/-- **Exercise 8.17, Part 1 (`+`).** `iPlus/jPlus` (`Definition89.lean`) already *are* the computable
projection pair `𝒰+𝒰 ⇄ 𝒰` needed for 8.9. Bonus: Lemma 6.15 upgrades it to `𝒰+𝒰 ⊴ 𝒰`. -/
theorem sumUU_trianglelefteq_U : sum U U U_mem_nonempty U_mem_nonempty ⊴ U :=
  trianglelefteq_of_projectionPair iPlus jPlus jPlus_comp_iPlus iPlus_comp_jPlus_le

/-- **Exercise 8.17, Part 1 (`×`).** `iTimes/jTimes` already are the pair `𝒰×𝒰 ⇄ 𝒰`; bonus `⊴`. -/
theorem prodUU_trianglelefteq_U : prod U U ⊴ U :=
  trianglelefteq_of_projectionPair iTimes jTimes jTimes_comp_iTimes iTimes_comp_jTimes_le

/-- **Exercise 8.17, Part 1 (`→`).** `iArrow/jArrow` already are the pair `𝒰→𝒰 ⇄ 𝒰`; bonus `⊴`. -/
theorem funSpaceUU_trianglelefteq_U : funSpace U U ⊴ U :=
  trianglelefteq_of_projectionPair iArrow jArrow jArrow_comp_iArrow iArrow_comp_jArrow_le

/-! ## Part 3 — a universal domain `V ≠ 𝒰` -/

/-- **Universality, as an abstract predicate**: every countable neighbourhood system embeds
(up to isomorphism) as a subsystem of `W` — Theorem 8.8(a)'s property, extracted from the specific
domain `𝒰` to an arbitrary `W`. -/
def IsUniversal {δ : Type w} (W : NeighborhoodSystem δ) : Prop :=
  ∀ {α : Type u} (D : NeighborhoodSystem α) [Countable {S : Set α // D.mem S}], D ⊴ W

/-- **`𝒰` is universal** (restating Theorem 8.8(a) in `⊴`-shape). -/
theorem U_isUniversal : IsUniversal.{u} U := by
  intro α D _
  obtain ⟨D', hiso, hsub⟩ := theorem_8_8_a D
  exact ⟨D', hsub, hiso⟩

/-- **Universality transports along isomorphism.** If `W` is universal and `W ≅ᴰ W'`, then `W'` is
universal too: every countable `D` embeds in `W` (`D ⊴ W`), and `W ⊴ W'` (take `D' := W'` in `⊴`'s
definition, using `Subsystem.refl` and the given isomorphism), so `trianglelefteq_trans` finishes. -/
theorem isUniversal_of_isomorphic {W : NeighborhoodSystem β} {W' : NeighborhoodSystem γ}
    (hW : IsUniversal.{u} W) (hWW' : W ≅ᴰ W') : IsUniversal.{u} W' := by
  have hWW'_tri : W ⊴ W' := hWW'.elim fun e => ⟨W', Subsystem.refl W', ⟨e⟩⟩
  intro α D _
  exact trianglelefteq_trans (hW D) hWW'_tri

/-- **Exercise 8.17, Part 3.** Exercise 8.12's `V` (a `NeighborhoodSystem ℕ`, built from `2^kℕ+ℓ` —
literally a *different* neighbourhood system from `U : NeighborhoodSystem ℚ`, not merely a
relabelling) is a universal domain, since it is effectively isomorphic to `𝒰` (`effectiveIso812_UV`,
Exercise 8.12's headline) and universality transports along isomorphism. -/
theorem V_isUniversal : IsUniversal.{u} V :=
  isUniversal_of_isomorphic U_isUniversal ⟨effectiveIso812_UV.toDomainIso⟩

end Scott1980.Neighborhood

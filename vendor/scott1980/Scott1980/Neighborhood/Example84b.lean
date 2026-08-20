/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Example84
import Scott1980.Neighborhood.Definition83
import Scott1980.Neighborhood.Exercise510

/-!
# Lecture VIII — Example 8.4(b) (Scott 1981, PRG-19): `smash` and `strict` as projections

The remainder of Scott's **EXAMPLES 8.4**, building on Example 8.4(a)'s `check`/`fade` combinators
(`Scott1980/Neighborhood/Example84.lean`):

* **`smash : D × E → D × E`**, `smash(x, y) = fade(check(x), fade(check(y), ⟨x, y⟩))`, is a
  *projection* on `D × E` whose range is isomorphic to the smash product `D ⊗ E` (Exercise 5.10).
* **`strict : (D → E) → (D → E)`**, `strict(f) = λx. fade(check(x), f(x))`, is a *projection* on
  the function space `(D → E)` whose range is isomorphic to the strict function space `D →⊥ E`
  (Exercise 5.10).

## Formalization strategy

Both combinators reuse `check`/`fade` **verbatim** (they are already generic over the ambient
codomain of `fade` and the ambient domain of `check`), reinstantiated at a second neighbourhood
system: `fade (D := prod D E)`/`fade (D := E)` and `check (D := D)`/`check (D := E)`. No new
`ApproximableMap`-level combinator is built from scratch; the whole file is `comp`/`paired`/`proj`
bookkeeping plus the accompanying closed-form calculations, exactly as in 8.4(a).

**`smash`.** The key move is *reduction to Proposition 8.2*: `Exercise510.smash D E`
(the smash-product neighbourhood system) is a genuine *subsystem* of `prod D E`
(`smash_subsystem_prod`) — every smash neighbourhood is a product neighbourhood, and a proper
smash neighbourhood stays proper (hence still a smash neighbourhood) after any intersection that
lands back inside `prod D E` (`Exercise510.inter_ne_master_left/right` do the heavy lifting,
exactly as in `Exercise510.smash`'s own closure proof). Scott's literal combinator is built first
and its closed form derived directly (`smashRetraction_mem_iff` — literally "leave `z` alone if
neither coordinate is `⊥`, else collapse to `⊥`"); it is then identified with
`Subsystem.retractionOfSubsystem smash_subsystem_prod` (`smashRetraction_eq_retractionOfSubsystem`,
the one genuinely new argument — a "compactness" calculation packing a witness neighbourhood of the
smash out of any pair of non-`⊥` witnesses via `z.fst`/`z.snd` filter algebra), after which
`IsProjection`/`IsFinitary`/the isomorphism to `Exercise510.smash D E` are *all* inherited for free
from Definition 8.3's `Subsystem` corollaries.

**`strict`.** Built directly as `curry (fade.comp (paired (check.comp proj₁) evalMap))` using
Theorem 3.12's `curry`/`evalMap` (no new function-space machinery needed — `curry` already exists).
Its closed form (`toApproxMap_strictRetraction_apply`) says exactly "`strict(f)(y) = ⊥_E` if
`y = ⊥_D`, else `f(y)`", from which: (a) `f` is a fixed point of `strict` iff `f(⊥) = ⊥`, i.e. iff
`IsStrict f` (`strictRetraction_fixed_iff`); (b) restricting `funSpaceEquiv` along this
correspondence gives `Fix(strict) ≃o {f ∣ IsStrict f} = StrictMap D E` (`strictRetractionFixIso`),
which composed with `Exercise510.strictFunEquiv.symm` gives the isomorphism to
`Exercise510.strictFun D E` announced by Scott.

Everything is **choice-free** in the *data* (`smashRetraction`, `strictRetraction`); the packaged
`OrderIso`s and the `IsRetraction`/`IsProjection` *proofs* pick up `Classical.choice` only through
`by_contra`/`by_cases` case splits, exactly mirroring 8.4(a)'s discipline.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-! ## A shared closed form for `fade` at a general codomain. -/

/-- The closed form of `fade`'s elementwise action, generalized (via `mem_toElementMap₂_fade`) from
Example 8.4(a)'s ambient `D` to an arbitrary neighbourhood system `G`. -/
theorem mem_toElementMap_fade {γ : Type*} {G : NeighborhoodSystem γ} (t : O.Element) (w : G.Element)
    {Z : Set γ} :
    ((fade (D := G)).toElementMap (pair t w)).mem Z ↔
      G.mem Z ∧ (Z = G.master ∨ (t.mem ({0} : Set (Fin 2)) ∧ w.mem Z)) := by
  rw [show (fade (D := G)) = ofMap₂ (fade₂ (D := G)) from rfl, toElementMap_ofMap₂_pair,
    mem_toElementMap₂_fade]

/-- `check(x) ∋ {0} ↔ x ≠ ⊥`: the clean, non-set-theoretic form of `mem_toElementMap_check`. -/
theorem check_toElementMap_mem_zero_iff {x : D.Element} :
    (check.toElementMap x).mem ({0} : Set (Fin 2)) ↔ x ≠ D.bot := by
  rw [mem_toElementMap_check]
  constructor
  · rintro ⟨-, h | h⟩
    · exact absurd h fin2_zero_ne_zero_one
    · exact h
  · intro h; exact ⟨O_mem_zero, Or.inr h⟩

/-! ## `smash : D × E → D × E`. -/

section Smash

/-- `(prod D E).bot = ⟨⊥_D, ⊥_E⟩`. -/
theorem pair_bot_bot : pair (D.bot) (E.bot) = (prod D E).bot := by
  apply Element.ext
  intro W
  rw [mem_pair, mem_bot]
  constructor
  · rintro ⟨X, Y, hX, hY, rfl⟩
    rw [mem_bot] at hX hY
    rw [hX, hY, prod_master]
  · intro hW
    refine ⟨D.master, E.master, ?_, ?_, ?_⟩
    · rw [mem_bot]
    · rw [mem_bot]
    · rw [hW, prod_master]

@[simp] theorem prod_bot_fst : ((prod D E).bot).fst = D.bot := by rw [← pair_bot_bot, fst_pair]

@[simp] theorem prod_bot_snd : ((prod D E).bot).snd = E.bot := by rw [← pair_bot_bot, snd_pair]

/-- The inner application `fade(check(y), z)` of Scott's `smash(x, y) = fade(check(x),
fade(check(y), ⟨x, y⟩))`: here `z = ⟨x, y⟩` is passed through `idMap` (Scott's `⟨x,y⟩` *is* the
ambient input). -/
def smashFadeInner : ApproximableMap (prod D E) (prod D E) :=
  (fade (D := prod D E)).comp
    (paired ((check (D := E)).comp (proj₁ D E)) (idMap (prod D E)))

/-- **Example 8.4(b)(ii)'s `smash` combinator.** `smash(x, y) = fade(check(x), fade(check(y),
⟨x, y⟩))`. -/
def smashRetraction : ApproximableMap (prod D E) (prod D E) :=
  (fade (D := prod D E)).comp
    (paired ((check (D := D)).comp (proj₀ D E)) (smashFadeInner (D := D) (E := E)))

theorem smashFadeInner_mem {z : (prod D E).Element} {Z : Set (α ⊕ β)} :
    (smashFadeInner.toElementMap z).mem Z ↔
      (prod D E).mem Z ∧ (Z = (prod D E).master ∨ (z.snd ≠ E.bot ∧ z.mem Z)) := by
  show (((fade (D := prod D E)).comp
    (paired ((check (D := E)).comp (proj₁ D E)) (idMap (prod D E)))).toElementMap z).mem Z ↔ _
  rw [toElementMap_comp, toElementMap_paired, toElementMap_comp, toElementMap_proj₁,
    toElementMap_idMap, mem_toElementMap_fade, check_toElementMap_mem_zero_iff]

theorem smashRetraction_mem {z : (prod D E).Element} {Z : Set (α ⊕ β)} :
    (smashRetraction.toElementMap z).mem Z ↔
      (prod D E).mem Z ∧
        (Z = (prod D E).master ∨ (z.fst ≠ D.bot ∧ (smashFadeInner.toElementMap z).mem Z)) := by
  show (((fade (D := prod D E)).comp
    (paired ((check (D := D)).comp (proj₀ D E)) smashFadeInner)).toElementMap z).mem Z ↔ _
  rw [toElementMap_comp, toElementMap_paired, toElementMap_comp, toElementMap_proj₀,
    mem_toElementMap_fade, check_toElementMap_mem_zero_iff]

/-- **`smashRetraction`'s closed form.** `smash(z) = z` if neither coordinate is `⊥`; otherwise
`smash(z) = ⊥`. -/
theorem smashRetraction_mem_iff {z : (prod D E).Element} {Z : Set (α ⊕ β)} :
    (smashRetraction.toElementMap z).mem Z ↔
      (prod D E).mem Z ∧
        (Z = (prod D E).master ∨ (z.fst ≠ D.bot ∧ z.snd ≠ E.bot ∧ z.mem Z)) := by
  rw [smashRetraction_mem, smashFadeInner_mem]
  constructor
  · rintro ⟨hPZ, hZeq | ⟨hx, hPZ', hZeq' | ⟨hy, hzZ⟩⟩⟩
    · exact ⟨hPZ, Or.inl hZeq⟩
    · exact ⟨hPZ, Or.inl hZeq'⟩
    · exact ⟨hPZ, Or.inr ⟨hx, hy, hzZ⟩⟩
  · rintro ⟨hPZ, hZeq | ⟨hx, hy, hzZ⟩⟩
    · exact ⟨hPZ, Or.inl hZeq⟩
    · exact ⟨hPZ, Or.inr ⟨hx, hPZ, Or.inr ⟨hy, hzZ⟩⟩⟩

theorem smashRetraction_of_ne_bot {z : (prod D E).Element} (hx : z.fst ≠ D.bot)
    (hy : z.snd ≠ E.bot) : smashRetraction.toElementMap z = z := by
  apply Element.ext
  intro Z
  rw [smashRetraction_mem_iff]
  constructor
  · rintro ⟨hPZ, hZeq | ⟨-, -, hzZ⟩⟩
    · rw [hZeq]; exact z.master_mem
    · exact hzZ
  · intro hzZ
    exact ⟨z.sub hzZ, Or.inr ⟨hx, hy, hzZ⟩⟩

theorem smashRetraction_of_eq_bot {z : (prod D E).Element} (hz : z.fst = D.bot ∨ z.snd = E.bot) :
    smashRetraction.toElementMap z = (prod D E).bot := by
  apply Element.ext
  intro Z
  rw [smashRetraction_mem_iff, mem_bot]
  constructor
  · rintro ⟨-, rfl | ⟨hx, hy, -⟩⟩
    · rfl
    · exact absurd hz (by simp [hx, hy])
  · rintro rfl
    exact ⟨(prod D E).master_mem, Or.inl rfl⟩

theorem isRetraction_smashRetraction : IsRetraction (smashRetraction (D := D) (E := E)) := by
  apply ext_of_toElementMap
  intro z
  rw [toElementMap_comp]
  by_cases hx : z.fst = D.bot
  · rw [smashRetraction_of_eq_bot (Or.inl hx),
      smashRetraction_of_eq_bot (Or.inl prod_bot_fst)]
  · by_cases hy : z.snd = E.bot
    · rw [smashRetraction_of_eq_bot (Or.inr hy),
        smashRetraction_of_eq_bot (Or.inr prod_bot_snd)]
    · rw [smashRetraction_of_ne_bot hx hy, smashRetraction_of_ne_bot hx hy]

theorem smashRetraction_le_idMap : smashRetraction (D := D) (E := E) ≤ idMap (prod D E) := by
  rw [le_iff_toElementMap_le]
  intro z
  rw [toElementMap_idMap]
  intro Z hZ
  rw [smashRetraction_mem_iff] at hZ
  rcases hZ with ⟨hPZ, rfl | ⟨-, -, hzZ⟩⟩
  · exact z.master_mem
  · exact hzZ

/-- **The subsystem relation `Exercise510.smash D E ◁ prod D E`.** Every smash neighbourhood is a
product neighbourhood; a proper smash neighbourhood stays proper (hence smash-membership, not just
product-membership) after any consistent intersection, by `Exercise510.inter_ne_master_left/right`
exactly as in `Exercise510.smash`'s own closure proof. -/
theorem smash_subsystem_prod : Exercise510.smash D E ◁ prod D E where
  master_eq := by rw [Exercise510.smash_master, prod_master]
  sub := by
    rintro W (rfl | ⟨X, Y, hX, -, hY, -, rfl⟩)
    · exact prod_mem_prodNbhd D.master_mem E.master_mem
    · exact prod_mem_prodNbhd hX hY
  inter_closed := by
    rintro W W' (rfl | ⟨X, Y, hX, hXne, hY, hYne, rfl⟩) hW' hPint
    · -- `W = smash master = prod master`.
      rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · left; rw [Set.inter_self]
      · right
        refine ⟨X', Y', hX', hX'ne, hY', hY'ne, ?_⟩
        rw [prodNbhd_inter, Set.inter_eq_right.mpr (D.sub_master hX'),
          Set.inter_eq_right.mpr (E.sub_master hY')]
    · -- `W = prodNbhd X Y` proper.
      rcases hW' with rfl | ⟨X', Y', hX', hX'ne, hY', hY'ne, rfl⟩
      · right
        refine ⟨X, Y, hX, hXne, hY, hYne, ?_⟩
        rw [prodNbhd_inter, Set.inter_eq_left.mpr (D.sub_master hX),
          Set.inter_eq_left.mpr (E.sub_master hY)]
      · -- both proper: `hPint` supplies the membership of the intersection in `prod D E`.
        rw [prodNbhd_inter] at hPint ⊢
        obtain ⟨hXX'mem, hYY'mem⟩ := prod_mem_prodNbhd_iff.mp hPint
        exact Or.inr ⟨X ∩ X', Y ∩ Y', hXX'mem, Exercise510.inter_ne_master_left hX hXne, hYY'mem,
          Exercise510.inter_ne_master_right hY hYne, rfl⟩

/-- The closed form of `Subsystem.retractionOfSubsystem`'s elementwise action, specialized to
`smash_subsystem_prod`, simplified using that `z` is already up-closed: the existential witness
`X ⊆ Y ⊆ Z` of Proposition 8.2's formula collapses to `z.mem Y` directly. -/
theorem mem_toElementMap_retractionOfSubsystem_smash {z : (prod D E).Element}
    {Z : Set (α ⊕ β)} :
    ((Subsystem.retractionOfSubsystem (smash_subsystem_prod (D := D) (E := E))).toElementMap z).mem
        Z ↔
      (prod D E).mem Z ∧ ∃ Y, (Exercise510.smash D E).mem Y ∧ z.mem Y ∧ Y ⊆ Z := by
  rw [mem_toElementMap]
  constructor
  · rintro ⟨X, hzX, hrel⟩
    obtain ⟨hPX, hPZ, Y, hSY, hXY, hYZ⟩ := (Subsystem.retractionOfSubsystem_rel _).mp hrel
    exact ⟨hPZ, Y, hSY, z.up_mem hzX (smash_subsystem_prod.sub hSY) hXY, hYZ⟩
  · rintro ⟨hPZ, Y, hSY, hzY, hYZ⟩
    exact ⟨Y, hzY, (Subsystem.retractionOfSubsystem_rel _).mpr
      ⟨z.sub hzY, hPZ, Y, hSY, subset_rfl, hYZ⟩⟩

/-- **The compactness lemma.** If neither coordinate of `z` is `⊥`, some *proper* smash
neighbourhood witnesses `z.mem Y ⊆ Z` for any `Z ∈ z` — built from `exists_mem_ne_master_of_ne_bot`
witnesses on each coordinate, intersected against `Z`'s own decomposition via the *filter*
`inter_mem` of `z.fst`/`z.snd` (no `NeighborhoodSystem`-level consistency witness needed). -/
theorem exists_smash_witness {z : (prod D E).Element} (hx : z.fst ≠ D.bot) (hy : z.snd ≠ E.bot)
    {Z : Set (α ⊕ β)} (hzZ : z.mem Z) :
    ∃ Y, (Exercise510.smash D E).mem Y ∧ z.mem Y ∧ Y ⊆ Z := by
  obtain ⟨X0, hX0, hX0ne⟩ := exists_mem_ne_master_of_ne_bot hx
  obtain ⟨Y0, hY0, hY0ne⟩ := exists_mem_ne_master_of_ne_bot hy
  set A := Sum.inl ⁻¹' Z with hA
  set B := Sum.inr ⁻¹' Z with hB
  have hZeq : Z = prodNbhd A B := prodNbhd_preimage (z.sub hzZ)
  have hAmem : D.mem A := prod_mem_inl (z.sub hzZ)
  have hBmem : E.mem B := prod_mem_inr (z.sub hzZ)
  rw [hZeq] at hzZ
  have hzfA : z.fst.mem A := mem_fst.mpr ⟨hAmem, ((prod_mem_split hAmem hBmem).mp hzZ).1⟩
  have hzsB : z.snd.mem B := mem_snd.mpr ⟨hBmem, ((prod_mem_split hAmem hBmem).mp hzZ).2⟩
  have hzfX0' : z.fst.mem (X0 ∩ A) := z.fst.inter_mem hX0 hzfA
  have hzsY0' : z.snd.mem (Y0 ∩ B) := z.snd.inter_mem hY0 hzsB
  have hX0'mem : D.mem (X0 ∩ A) := z.fst.sub hzfX0'
  have hY0'mem : E.mem (Y0 ∩ B) := z.snd.sub hzsY0'
  have hX0'ne : X0 ∩ A ≠ D.master := Exercise510.inter_ne_master_left (z.fst.sub hX0) hX0ne
  have hY0'ne : Y0 ∩ B ≠ E.master := Exercise510.inter_ne_master_right (z.snd.sub hY0) hY0ne
  refine ⟨prodNbhd (X0 ∩ A) (Y0 ∩ B),
    Exercise510.smash_mem_proper hX0'mem hX0'ne hY0'mem hY0'ne, ?_, ?_⟩
  · exact (prod_mem_split hX0'mem hY0'mem).mpr
      ⟨(mem_fst.mp hzfX0').2, (mem_snd.mp hzsY0').2⟩
  · rw [hZeq]
    exact prodNbhd_subset_iff.mpr ⟨Set.inter_subset_right, Set.inter_subset_right⟩

/-- **Scott's `smash` combinator equals Proposition 8.2's canonical subsystem retraction.** Both
sides agree with `smashRetraction_mem_iff`'s closed form: the `Z = master` branch matches (both
sides always admit the master witness `Y = (smash D E).master`), and the "genuine pair" branch
matches by `exists_smash_witness` (`←`) and a direct case split on `(smash D E).mem Y` (`→`, using
that `Y ⊆ (prod D E).master` sandwiches `Z = master` when `Y` is itself the master, and that
`z.fst.mem`/`z.snd.mem` of a proper `Y`'s factors forces both coordinates non-`⊥`, `mem_bot`). -/
theorem smashRetraction_eq_retractionOfSubsystem :
    smashRetraction (D := D) (E := E) = Subsystem.retractionOfSubsystem smash_subsystem_prod := by
  apply ext_of_toElementMap
  intro z
  apply Element.ext
  intro Z
  rw [smashRetraction_mem_iff, mem_toElementMap_retractionOfSubsystem_smash]
  constructor
  · rintro ⟨hPZ, rfl | ⟨hx, hy, hzZ⟩⟩
    · exact ⟨hPZ, (prod D E).master, Exercise510.smash_mem_iff.mpr (Or.inl rfl), z.master_mem,
        subset_rfl⟩
    · exact ⟨hPZ, exists_smash_witness hx hy hzZ⟩
  · rintro ⟨hPZ, Y, hSY, hzY, hYZ⟩
    rcases Exercise510.smash_mem_iff.mp hSY with rfl | ⟨YA, YB, hYA, hYAne, hYB, hYBne, rfl⟩
    · exact ⟨hPZ, Or.inl (Set.Subset.antisymm ((prod D E).sub_master hPZ) hYZ)⟩
    · have hzfYA : z.fst.mem YA := mem_fst.mpr ⟨hYA, ((prod_mem_split hYA hYB).mp hzY).1⟩
      have hzsYB : z.snd.mem YB := mem_snd.mpr ⟨hYB, ((prod_mem_split hYA hYB).mp hzY).2⟩
      refine ⟨hPZ, Or.inr ⟨?_, ?_, z.up_mem hzY hPZ hYZ⟩⟩
      · intro hxbot; rw [hxbot, mem_bot] at hzfYA; exact hYAne hzfYA
      · intro hybot; rw [hybot, mem_bot] at hzsYB; exact hYBne hzsYB

/-- **Example 8.4(b)(ii) (Scott 1981, PRG-19).** `smashRetraction` is a projection on `D × E`
whose fixed-point set is isomorphic to the smash product `Exercise510.smash D E`. -/
theorem example84b_smash :
    IsProjection (smashRetraction (D := D) (E := E)) ∧
      Nonempty ((Exercise510.smash D E).Element ≃o
        {z : (prod D E).Element // smashRetraction.toElementMap z = z}) := by
  rw [smashRetraction_eq_retractionOfSubsystem]
  exact ⟨Subsystem.isProjection_retractionOfSubsystem smash_subsystem_prod,
    ⟨Subsystem.elementIso smash_subsystem_prod⟩⟩

end Smash

/-! ## `strict : (D → E) → (D → E)`. -/

section Strict

/-- Two tiny reproofs of `funSpaceEquiv`'s own round-trips, stated standalone so the closed-form
calculations below don't have to fight `OrderIso` field-access notation. -/
theorem toFilter_toApproxMap (φ : (funSpace D E).Element) : toFilter (toApproxMap φ) = φ :=
  (funSpaceEquiv D E).left_inv φ

theorem toApproxMap_toFilter (f : ApproximableMap D E) : toApproxMap (toFilter f) = f :=
  (funSpaceEquiv D E).right_inv f

theorem toApproxMap_injective {a b : (funSpace D E).Element} (h : toApproxMap a = toApproxMap b) :
    a = b := by
  rw [← toFilter_toApproxMap a, ← toFilter_toApproxMap b, h]

/-- `g(f, y) = fade(check(y), f(y))`, as a joint approximable map `(D → E) × D → E`. -/
def strictEvalFade : ApproximableMap (prod (funSpace D E) D) E :=
  (fade (D := E)).comp
    (paired ((check (D := D)).comp (proj₁ (funSpace D E) D)) (evalMap D E))

/-- **Example 8.4(b)(i)'s `strict` combinator.** `strict(f) = λy. fade(check(y), f(y))`, built via
Theorem 3.12's `curry`. -/
def strictRetraction : ApproximableMap (funSpace D E) (funSpace D E) := curry strictEvalFade

/-- The closed form of `strict`'s elementwise action: `strict(f)(y) = ⊥_E` if `y = ⊥_D`, else
`f(y)`. -/
theorem toApproxMap_strictRetraction_mem {φ : (funSpace D E).Element} {y : D.Element}
    {Z : Set β} :
    ((toApproxMap (strictRetraction.toElementMap φ)).toElementMap y).mem Z ↔
      E.mem Z ∧ (Z = E.master ∨ (y ≠ D.bot ∧ ((toApproxMap φ).toElementMap y).mem Z)) := by
  show ((toApproxMap ((curry strictEvalFade).toElementMap φ)).toElementMap y).mem Z ↔ _
  rw [toElementMap_curry_apply]
  show (((fade (D := E)).comp
    (paired ((check (D := D)).comp (proj₁ (funSpace D E) D)) (evalMap D E))).toElementMap
      (pair φ y)).mem Z ↔ _
  rw [toElementMap_comp, toElementMap_paired, toElementMap_comp, toElementMap_proj₁, snd_pair,
    evalMap_apply, mem_toElementMap_fade, check_toElementMap_mem_zero_iff]

theorem strictRetraction_apply_bot (φ : (funSpace D E).Element) :
    (toApproxMap (strictRetraction.toElementMap φ)).toElementMap D.bot = E.bot := by
  apply Element.ext
  intro Z
  rw [toApproxMap_strictRetraction_mem, mem_bot]
  constructor
  · rintro ⟨-, rfl | ⟨hne, -⟩⟩
    · rfl
    · exact absurd rfl hne
  · rintro rfl
    exact ⟨E.master_mem, Or.inl rfl⟩

theorem strictRetraction_apply_of_ne_bot {y : D.Element} (hy : y ≠ D.bot)
    (φ : (funSpace D E).Element) :
    (toApproxMap (strictRetraction.toElementMap φ)).toElementMap y
      = (toApproxMap φ).toElementMap y := by
  apply Element.ext
  intro Z
  rw [toApproxMap_strictRetraction_mem]
  constructor
  · rintro ⟨-, rfl | ⟨-, hZ⟩⟩
    · exact ((toApproxMap φ).toElementMap y).master_mem
    · exact hZ
  · intro hZ
    exact ⟨((toApproxMap φ).toElementMap y).sub hZ, Or.inr ⟨hy, hZ⟩⟩

theorem isRetraction_strictRetraction : IsRetraction (strictRetraction (D := D) (E := E)) := by
  apply ext_of_toElementMap
  intro φ
  rw [toElementMap_comp]
  apply toApproxMap_injective
  apply ext_of_toElementMap
  intro y
  by_cases hy : y = D.bot
  · rw [hy, strictRetraction_apply_bot, strictRetraction_apply_bot]
  · rw [strictRetraction_apply_of_ne_bot hy, strictRetraction_apply_of_ne_bot hy]

theorem strictRetraction_le_idMap : strictRetraction (D := D) (E := E) ≤ idMap (funSpace D E) := by
  rw [le_iff_toElementMap_le]
  intro φ
  rw [toElementMap_idMap]
  have hmap : toApproxMap (strictRetraction.toElementMap φ) ≤ toApproxMap φ := by
    rw [le_iff_toElementMap_le]
    intro y
    by_cases hy : y = D.bot
    · rw [hy, strictRetraction_apply_bot]
      intro Z hZ
      rw [mem_bot] at hZ
      rw [hZ]
      exact ((toApproxMap φ).toElementMap D.bot).master_mem
    · rw [strictRetraction_apply_of_ne_bot hy]
  exact (funSpaceEquiv D E).map_rel_iff.mp hmap

/-- **`f` is a fixed point of `strict` iff `f` is strict.** -/
theorem isStrict_toApproxMap_of_fixed {φ : (funSpace D E).Element}
    (hφ : strictRetraction.toElementMap φ = φ) : Exercise510.IsStrict (toApproxMap φ) := by
  rw [Exercise510.isStrict_iff_apply_bot]
  have h := strictRetraction_apply_bot φ
  rwa [hφ] at h

theorem strictRetraction_fixed_of_isStrict {f : ApproximableMap D E} (hf : Exercise510.IsStrict f) :
    strictRetraction.toElementMap (toFilter f) = toFilter f := by
  have hbot : f.toElementMap D.bot = E.bot := Exercise510.isStrict_iff_apply_bot.mp hf
  have key : toApproxMap (strictRetraction.toElementMap (toFilter f)) = f := by
    apply ext_of_toElementMap
    intro y
    by_cases hy : y = D.bot
    · rw [hy, strictRetraction_apply_bot, hbot]
    · rw [strictRetraction_apply_of_ne_bot hy, toApproxMap_toFilter]
  rw [← toFilter_toApproxMap (strictRetraction.toElementMap (toFilter f)), key]

/-- **Example 8.4(b)(i), the fixed-point representation.** Restricting `funSpaceEquiv` along
`isStrict_toApproxMap_of_fixed`/`strictRetraction_fixed_of_isStrict` identifies `Fix(strict)` with
the strict approximable maps `Exercise510.StrictMap D E`. -/
def strictRetractionFixIso :
    {φ : (funSpace D E).Element // strictRetraction.toElementMap φ = φ} ≃o
      Exercise510.StrictMap D E where
  toFun φ := ⟨toApproxMap φ.1, isStrict_toApproxMap_of_fixed φ.2⟩
  invFun f := ⟨toFilter f.1, strictRetraction_fixed_of_isStrict f.2⟩
  left_inv φ := Subtype.ext (toFilter_toApproxMap φ.1)
  right_inv f := Subtype.ext (toApproxMap_toFilter f.1)
  map_rel_iff' := by
    intro φ φ'
    show toApproxMap φ.1 ≤ toApproxMap φ'.1 ↔ φ.1 ≤ φ'.1
    exact (funSpaceEquiv D E).map_rel_iff

/-- **Example 8.4(b)(i) (Scott 1981, PRG-19).** `strictRetraction` is a projection on `D → E`
whose fixed-point set is isomorphic to the strict function space `Exercise510.strictFun D E`. -/
theorem example84b_strict :
    IsProjection (strictRetraction (D := D) (E := E)) ∧
      Nonempty ((Exercise510.strictFun D E).Element ≃o
        {φ : (funSpace D E).Element // strictRetraction.toElementMap φ = φ}) :=
  ⟨⟨isRetraction_strictRetraction, strictRetraction_le_idMap⟩,
    ⟨strictRetractionFixIso.trans (Exercise510.strictFunEquiv D E).symm |>.symm⟩⟩

end Strict

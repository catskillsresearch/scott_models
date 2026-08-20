/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Proposition810
import Scott1980.Neighborhood.Theorem86

/-!
# Proposition 8.10 (Scott 1981, PRG-19), second half — finitary-closure

**Proposition 8.10(b).** If `a, b : 𝒰 → 𝒰` are finitary (projections), then so are `a+b`, `a×b`,
`a→b`, and moreover `D_{a+b} ≅ D_a + D_b`, `D_{a×b} ≅ D_a × D_b`, `D_{a→b} ≅ (D_a → D_b)`, where
`D_a`, `D_b` are the (witnessing) domains of `a`, `b`.

## Strategy

For a finitary projection `a : 𝒰 → 𝒰`, Theorem 8.6's `sub_eq_self_of_isFinitaryProjection` gives
`a = retractionOfSubsystem (fixedNbhd_subsystem a)`, i.e. `a = i_a ∘ j_a` for the canonical
injection/projection pair `i_a : D_a → 𝒰`, `j_a : 𝒰 → D_a` of Proposition 6.12, where
`D_a := fixedNbhd a` is a genuine subsystem of `𝒰` (Theorem 8.5). This is Scott's "`D_a`" made
concrete and computed with directly (rather than via the abstract `IsFinitary` witness).

The key generic tool (`elementIsoOfProjectionPair` below) is Proposition 8.2's `elementIso`,
generalized away from requiring a literal `D ◁ E` subset relation to an *arbitrary* approximable
projection pair `i : D → E`, `j : E → D` with `j ∘ i = I_D` (no requirement `i ∘ j ≤ I_E`, and no
requirement that `D`, `E` share a token type) — exactly what `theorem_8_8_b_strong`'s fixed maps
`i₊/j₊`, `i_×/j_×`, `i_→/j_→` (Definition 8.9) are. Given such a pair and `g = i.comp j`, it
produces `D.Element ≃o Fix(g)` directly.

For each combinator `* ∈ {+, ×, →}` we build a *new* projection pair `I : D_a * D_b → 𝒰`,
`J : 𝒰 → D_a * D_b` (composing Definition 8.9's fixed maps with the functorial action of `*` on
`i_a, j_a, i_b, j_b`) and show algebraically (via the functor laws of `×`/`+`/`→` on maps, plus
`i_a.comp j_a = a`, `i_b.comp j_b = b`) that `J.comp I = idMap (D_a * D_b)` and
`I.comp J = a * b`. `elementIsoOfProjectionPair` then hands us
`(D_a * D_b).Element ≃o Fix(a * b)` directly, both witnessing `IsFinitary (a * b)` and Scott's
"moreover" isomorphism claim in one shot.

* **`×`** uses Exercise 3.19/3.20's `prodMap` and its functor laws `prodMap_id`/`prodMap_comp`
  directly — no new infrastructure needed.
* **`+`** needs a modest amount of new infrastructure for `sumMap` (Exercise 3.19's sum functor):
  its own elementwise case-split formulas (mirroring `Proposition810.lean`'s `sumComb` formulas)
  and its functor laws `sumMap_id`/`sumMap_comp`, built here.
* **`→`** needs a generalization of `lamComb`'s construction (`expMap`, the Hom-functor's action
  `f ↦ k ∘ f ∘ h`) away from self-maps of `𝒰` to a genuine bifunctor `funSpace V₀ V₁ →
  funSpace V₀' V₁'` for `h : V₀' → V₀`, `k : V₁ → V₁'`, together with its functor laws.

Axiom footprint: everything here mentions `U`, so it inherits `U`'s own `Classical.choice`
footprint, `⊆ {propext, Classical.choice, Quot.sound}`, confirmed not new (same as
`Proposition810.lean`/`Definition89.lean`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u v

/-! ## A generic projection-pair `elementIso`, without requiring a literal `◁` subset relation -/

variable {α β : Type u} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **Generalized Proposition 8.2 `elementIso`.** Given an approximable projection pair
`i : D → E`, `j : E → D` with `j ∘ i = I_D` (no requirement `i ∘ j ≤ I_E`, and `D`, `E` need not
share a token type — unlike `Subsystem.elementIso`, which requires a literal `D ◁ E`), and
`g : E → E` with `g = i ∘ j`, then `D.Element ≃o Fix(g)`. The proof is verbatim
`Subsystem.elementIso`'s, generalized. -/
def elementIsoOfProjectionPair (i : ApproximableMap D E) (j : ApproximableMap E D)
    (hji : j.comp i = idMap D) {g : ApproximableMap E E} (hg : g = i.comp j) :
    D.Element ≃o {y : E.Element // g.toElementMap y = y} where
  toFun x := ⟨i.toElementMap x, by
    have h1 : j.toElementMap (i.toElementMap x) = (j.comp i).toElementMap x :=
      (toElementMap_comp j i x).symm
    rw [hg, toElementMap_comp, h1, hji, toElementMap_idMap]⟩
  invFun y := j.toElementMap y.1
  left_inv x := by
    have h1 : j.toElementMap (i.toElementMap x) = (j.comp i).toElementMap x :=
      (toElementMap_comp j i x).symm
    show j.toElementMap (i.toElementMap x) = x
    rw [h1, hji, toElementMap_idMap]
  right_inv y := by
    apply Subtype.ext
    have hfix : g.toElementMap y.1 = y.1 := y.2
    show i.toElementMap (j.toElementMap y.1) = y.1
    rw [← toElementMap_comp, ← hg]
    exact hfix
  map_rel_iff' := by
    intro x x'
    show i.toElementMap x ≤ i.toElementMap x' ↔ x ≤ x'
    constructor
    · intro hle
      have hmono := j.toElementMap_mono hle
      have h1 : j.toElementMap (i.toElementMap x) = (j.comp i).toElementMap x :=
        (toElementMap_comp j i x).symm
      have h2 : j.toElementMap (i.toElementMap x') = (j.comp i).toElementMap x' :=
        (toElementMap_comp j i x').symm
      rw [h1, h2, hji, toElementMap_idMap, toElementMap_idMap] at hmono
      exact hmono
    · intro hle
      exact i.toElementMap_mono hle

/-- **`IsFinitary` from a concrete projection-pair witness.** -/
theorem isFinitary_of_projectionPair (i : ApproximableMap D E) (j : ApproximableMap E D)
    (hji : j.comp i = idMap D) {g : ApproximableMap E E} (hg : g = i.comp j) :
    IsFinitary g :=
  ⟨α, D, ⟨(elementIsoOfProjectionPair i j hji hg).symm⟩⟩

/-- If `i ∘ j ≤ I_E`, then `i` sends `D`'s bottom to `E`'s bottom: `i(⊥_D) ≤ i(j(⊥_E)) ≤ ⊥_E`
(the first step by monotonicity, since `⊥_D ≤ j(⊥_E)`; the second is `toElementMap_le_of_comp_le_idMap`
at `x := ⊥_E`), and `⊥_E ≤ i(⊥_D)` always. -/
theorem toElementMap_bot_eq_bot_of_comp_le_idMap {i : ApproximableMap D E} {j : ApproximableMap E D}
    (hij : i.comp j ≤ idMap E) : i.toElementMap D.bot = E.bot := by
  apply le_antisymm
  · calc i.toElementMap D.bot ≤ i.toElementMap (j.toElementMap E.bot) :=
          i.toElementMap_mono (D.bot_le _)
      _ ≤ E.bot := toElementMap_le_of_comp_le_idMap hij E.bot
  · exact E.bot_le _

/-! ## Setup: `D_a := fixedNbhd a`, the concrete witnessing domain of a finitary projection `a` -/

variable {a b : ApproximableMap U U}

/-- Every neighbourhood of `D_a := fixedNbhd a` is non-empty (inherited from `𝒰`). -/
theorem fixedNbhd_mem_nonempty (a : ApproximableMap U U) :
    ∀ X, (fixedNbhd a).mem X → X.Nonempty :=
  fun X hX => U_mem_nonempty X ((fixedNbhd_subsystem a).sub hX)

/-- **`i_a ∘ j_a = a`, for a finitary projection `a`.** Theorem 8.6's `sub_eq_self_of_isFinitaryProjection`,
restated via `retractionOfSubsystem`'s definition. -/
theorem inj_comp_proj_eq_self (ha : IsFinitaryProjection a) :
    (fixedNbhd_subsystem a).inj.comp (fixedNbhd_subsystem a).proj = a :=
  sub_eq_self_of_isFinitaryProjection ha

/-! ## The `×` case -/

section ProdCase

variable (a b : ApproximableMap U U)

/-- **`I_× : D_a × D_b → 𝒰`**, built by transporting `i_×` (Definition 8.9) through the functorial
action of `×` (Exercise 3.19's `prodMap`) on the injections `i_a : D_a → 𝒰`, `i_b : D_b → 𝒰`. -/
noncomputable def IProdComb : ApproximableMap (prod (fixedNbhd a) (fixedNbhd b)) U :=
  iTimes.comp (prodMap (fixedNbhd_subsystem a).inj (fixedNbhd_subsystem b).inj)

/-- **`J_× : 𝒰 → D_a × D_b`**, symmetric to `IProdComb`, via the projections `j_a`, `j_b`. -/
noncomputable def JProdComb : ApproximableMap U (prod (fixedNbhd a) (fixedNbhd b)) :=
  (prodMap (fixedNbhd_subsystem a).proj (fixedNbhd_subsystem b).proj).comp jTimes

theorem JProdComb_comp_IProdComb :
    (JProdComb a b).comp (IProdComb a b) = idMap (prod (fixedNbhd a) (fixedNbhd b)) := by
  unfold JProdComb IProdComb
  rw [comp_assoc, ← comp_assoc jTimes iTimes (prodMap _ _), jTimes_comp_iTimes, idMap_comp,
    ← prodMap_comp, (fixedNbhd_subsystem a).proj_comp_inj, (fixedNbhd_subsystem b).proj_comp_inj,
    prodMap_id]

theorem IProdComb_comp_JProdComb (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    (IProdComb a b).comp (JProdComb a b) = prodComb a b := by
  unfold IProdComb JProdComb
  rw [comp_assoc, ← comp_assoc (prodMap _ _) (prodMap _ _) jTimes, ← prodMap_comp,
    inj_comp_proj_eq_self ha, inj_comp_proj_eq_self hb, ← comp_assoc, prodComb_eq, comp_assoc]

/-- **Proposition 8.10(b), `×`-case.** `a, b` finitary projections `⟹` `a × b` is finitary, with
witnessing domain `D_a × D_b`. -/
theorem finitary_prodComb (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    IsFinitary (prodComb a b) :=
  isFinitary_of_projectionPair (IProdComb a b) (JProdComb a b) (JProdComb_comp_IProdComb a b)
    (IProdComb_comp_JProdComb a b ha hb).symm

/-- **Proposition 8.10(b), `×`-case, the isomorphism `D_{a×b} ≅ D_a × D_b`.** -/
noncomputable def prodComb_elementIso (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    (prod (fixedNbhd a) (fixedNbhd b)).Element ≃o
      {y : U.Element // (prodComb a b).toElementMap y = y} :=
  elementIsoOfProjectionPair (IProdComb a b) (JProdComb a b) (JProdComb_comp_IProdComb a b)
    (IProdComb_comp_JProdComb a b ha hb).symm

/-- **Proposition 8.10(b), `×`-case, in full.** `a, b` finitary projections `⟹` `a × b` is a
finitary projection, and its fixed-point set is order-isomorphic to `D_a × D_b`. -/
theorem finitaryProjection_prodComb (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    IsFinitaryProjection (prodComb a b) :=
  ⟨isProjection_prodComb ha.1 hb.1, finitary_prodComb a b ha hb⟩

end ProdCase

/-! ## `sumMap` infrastructure: elementwise formulas and functoriality

Exercise 3.19's sum functor `sumMap` is not literally built from `cond`/`which` (unlike
`prodMap`), so its elementwise behaviour and functor laws (`sumMap_id`/`sumMap_comp`) are
established here directly, mirroring `Proposition810.lean`'s treatment of `sumComb` itself. -/

section SumMapLemmas

variable {γ δ γ' δ' γ'' δ'' : Type u}
variable {V0 : NeighborhoodSystem γ} {V1 : NeighborhoodSystem δ}
variable {V0' : NeighborhoodSystem γ'} {V1' : NeighborhoodSystem δ'}
variable {V0'' : NeighborhoodSystem γ''} {V1'' : NeighborhoodSystem δ''}
variable {h0 : ∀ X, V0.mem X → X.Nonempty} {h1 : ∀ Y, V1.mem Y → Y.Nonempty}
variable {h0' : ∀ X, V0'.mem X → X.Nonempty} {h1' : ∀ Y, V1'.mem Y → Y.Nonempty}
variable {h0'' : ∀ X, V0''.mem X → X.Nonempty} {h1'' : ∀ Y, V1''.mem Y → Y.Nonempty}

/-- A sum-element reaches "neither" copy iff it is the bottom element. -/
theorem reaches_neither_iff_eq_bot {y : (sum V0 V1 h0 h1).Element} :
    (∀ W, y.mem W → W = (sum V0 V1 h0 h1).master) ↔ y = (sum V0 V1 h0 h1).bot := by
  constructor
  · intro hN
    apply Element.ext
    intro W
    rw [mem_bot]
    exact ⟨hN W, fun h => h ▸ y.master_mem⟩
  · rintro rfl W hW
    rw [mem_bot] at hW
    exact hW

/-- `sumMap` sends the bottom element to the bottom element. -/
theorem sumMap_bot (f : ApproximableMap V0 V0') (g : ApproximableMap V1 V1') :
    (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
        (sum V0 V1 h0 h1).bot = (sum V0' V1' h0' h1').bot := by
  apply Element.ext
  intro Z
  rw [mem_bot]
  constructor
  · rintro ⟨W, hW, _, hZmem, hd⟩
    rw [mem_bot] at hW
    subst hW
    rcases hd with rfl | ⟨X, Y', hWX, -, -⟩ | ⟨Y, Y', hWY, -, -⟩
    · rfl
    · have hWX' : sumMaster V0 V1 = inj₀ X := hWX
      exact absurd (hWX' ▸ none_mem_sumMaster) none_mem_inj₀
    · have hWY' : sumMaster V0 V1 = inj₁ Y := hWY
      exact absurd (hWY' ▸ none_mem_sumMaster) none_mem_inj₁
  · rintro rfl
    exact ⟨sumMaster V0 V1, (sum V0 V1 h0 h1).mem_bot.mpr rfl, (sum V0 V1 h0 h1).master_mem,
      (sum V0' V1' h0' h1').master_mem, Or.inl rfl⟩

/-- If `y` reaches the left copy, `(sumMap f g)(y)` also reaches the left copy. -/
theorem sumMap_reaches_left {f : ApproximableMap V0 V0'} {g : ApproximableMap V1 V1'}
    {y : (sum V0 V1 h0 h1).Element} (hL : ∃ X, V0.mem X ∧ y.mem (inj₀ X)) :
    ∃ X', V0'.mem X' ∧ ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
      y).mem (inj₀ X') := by
  obtain ⟨X, hX, hXy⟩ := hL
  have hf : f.rel X V0'.master :=
    f.mono f.master_rel (V0.sub_master hX) subset_rfl hX V0'.master_mem
  exact ⟨V0'.master, V0'.master_mem, inj₀ X, hXy,
    Or.inr (Or.inl ⟨X, hX, rfl⟩), Or.inr (Or.inl ⟨V0'.master, V0'.master_mem, rfl⟩),
    Or.inr (Or.inl ⟨X, V0'.master, rfl, rfl, hf⟩)⟩

/-- If `y` reaches the right copy, `(sumMap f g)(y)` also reaches the right copy. -/
theorem sumMap_reaches_right {f : ApproximableMap V0 V0'} {g : ApproximableMap V1 V1'}
    {y : (sum V0 V1 h0 h1).Element} (hR : ∃ Y, V1.mem Y ∧ y.mem (inj₁ Y)) :
    ∃ Y', V1'.mem Y' ∧ ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
      y).mem (inj₁ Y') := by
  obtain ⟨Y, hY, hYy⟩ := hR
  have hg : g.rel Y V1'.master :=
    g.mono g.master_rel (V1.sub_master hY) subset_rfl hY V1'.master_mem
  exact ⟨V1'.master, V1'.master_mem, inj₁ Y, hYy,
    Or.inr (Or.inr ⟨Y, hY, rfl⟩), Or.inr (Or.inr ⟨V1'.master, V1'.master_mem, rfl⟩),
    Or.inr (Or.inr ⟨Y, V1'.master, rfl, rfl, hg⟩)⟩

theorem toElementMap_sumMap_inMap₀ (f : ApproximableMap V0 V0') (g : ApproximableMap V1 V1')
    (v : V0.Element) :
    (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
        ((inMap₀ (h₀ := h0) (h₁ := h1)).toElementMap v) =
      (inMap₀ (h₀ := h0') (h₁ := h1')).toElementMap (f.toElementMap v) := by
  set z := (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
    ((inMap₀ (h₀ := h0) (h₁ := h1)).toElementMap v) with hz
  have hLz : ∃ X', V0'.mem X' ∧ z.mem (inj₀ X') :=
    sumMap_reaches_left (inMap₀_toElementMap_reaches_left v)
  rw [← inMap₀_outMap₀_eq_of_left hLz]
  congr 1
  have heq : (outMap₀ (h₀ := h0') (h₁ := h1')).comp
      ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).comp
        (inMap₀ (h₀ := h0) (h₁ := h1))) = f :=
    outMap₀_comp_sumMap_comp_inMap₀ f g
  calc (outMap₀ (h₀ := h0') (h₁ := h1')).toElementMap z
      = ((outMap₀ (h₀ := h0') (h₁ := h1')).comp
          ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).comp
            (inMap₀ (h₀ := h0) (h₁ := h1)))).toElementMap v := by
        rw [toElementMap_comp, toElementMap_comp, ← hz]
    _ = f.toElementMap v := by rw [heq]

theorem toElementMap_sumMap_inMap₁ (f : ApproximableMap V0 V0') (g : ApproximableMap V1 V1')
    (w : V1.Element) :
    (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
        ((inMap₁ (h₀ := h0) (h₁ := h1)).toElementMap w) =
      (inMap₁ (h₀ := h0') (h₁ := h1')).toElementMap (g.toElementMap w) := by
  set z := (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap
    ((inMap₁ (h₀ := h0) (h₁ := h1)).toElementMap w) with hz
  have hRz : ∃ Y', V1'.mem Y' ∧ z.mem (inj₁ Y') :=
    sumMap_reaches_right (inMap₁_toElementMap_reaches_right w)
  rw [← inMap₁_outMap₁_eq_of_right hRz]
  congr 1
  have heq : (outMap₁ (h₀ := h0') (h₁ := h1')).comp
      ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).comp
        (inMap₁ (h₀ := h0) (h₁ := h1))) = g :=
    outMap₁_comp_sumMap_comp_inMap₁ f g
  calc (outMap₁ (h₀ := h0') (h₁ := h1')).toElementMap z
      = ((outMap₁ (h₀ := h0') (h₁ := h1')).comp
          ((sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).comp
            (inMap₁ (h₀ := h0) (h₁ := h1)))).toElementMap w := by
        rw [toElementMap_comp, toElementMap_comp, ← hz]
    _ = g.toElementMap w := by rw [heq]

theorem toElementMap_sumMap_of_left {f : ApproximableMap V0 V0'} {g : ApproximableMap V1 V1'}
    {y : (sum V0 V1 h0 h1).Element} (hL : ∃ X, V0.mem X ∧ y.mem (inj₀ X)) :
    (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap y =
      (inMap₀ (h₀ := h0') (h₁ := h1')).toElementMap
        (f.toElementMap ((outMap₀ (h₀ := h0) (h₁ := h1)).toElementMap y)) := by
  conv_lhs => rw [← inMap₀_outMap₀_eq_of_left hL]
  exact toElementMap_sumMap_inMap₀ f g _

theorem toElementMap_sumMap_of_right {f : ApproximableMap V0 V0'} {g : ApproximableMap V1 V1'}
    {y : (sum V0 V1 h0 h1).Element} (hR : ∃ Y, V1.mem Y ∧ y.mem (inj₁ Y)) :
    (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g).toElementMap y =
      (inMap₁ (h₀ := h0') (h₁ := h1')).toElementMap
        (g.toElementMap ((outMap₁ (h₀ := h0) (h₁ := h1)).toElementMap y)) := by
  conv_lhs => rw [← inMap₁_outMap₁_eq_of_right hR]
  exact toElementMap_sumMap_inMap₁ f g _

/-- **`sumMap` preserves identities: `id + id = id`.** -/
theorem sumMap_id : sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0) (h₁' := h1)
    (idMap V0) (idMap V1) = idMap (sum V0 V1 h0 h1) := by
  apply ext_of_toElementMap
  intro y
  rw [toElementMap_idMap]
  rcases sum_element_trichotomy y with hL | hR | hN
  · rw [toElementMap_sumMap_of_left hL, toElementMap_idMap, inMap₀_outMap₀_eq_of_left hL]
  · rw [toElementMap_sumMap_of_right hR, toElementMap_idMap, inMap₁_outMap₁_eq_of_right hR]
  · rw [reaches_neither_iff_eq_bot] at hN
    rw [hN, sumMap_bot]

/-- **`sumMap` preserves composition: `(f'∘f) + (g'∘g) = (f'+g') ∘ (f+g)`.** -/
theorem sumMap_comp (f' : ApproximableMap V0' V0'') (f : ApproximableMap V0 V0')
    (g' : ApproximableMap V1' V1'') (g : ApproximableMap V1 V1') :
    sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0'') (h₁' := h1'') (f'.comp f) (g'.comp g) =
      (sumMap (h₀ := h0') (h₁ := h1') (h₀' := h0'') (h₁' := h1'') f' g').comp
        (sumMap (h₀ := h0) (h₁ := h1) (h₀' := h0') (h₁' := h1') f g) := by
  apply ext_of_toElementMap
  intro y
  rw [toElementMap_comp]
  rcases sum_element_trichotomy y with hL | hR | hN
  · rw [toElementMap_sumMap_of_left hL, toElementMap_comp, toElementMap_sumMap_of_left hL,
      toElementMap_sumMap_of_left (inMap₀_toElementMap_reaches_left _),
      toElementMap_of_comp_eq_idMap outMap₀_comp_inMap₀]
  · rw [toElementMap_sumMap_of_right hR, toElementMap_comp, toElementMap_sumMap_of_right hR,
      toElementMap_sumMap_of_right (inMap₁_toElementMap_reaches_right _),
      toElementMap_of_comp_eq_idMap outMap₁_comp_inMap₁]
  · rw [reaches_neither_iff_eq_bot] at hN
    rw [hN, sumMap_bot, sumMap_bot, sumMap_bot]

end SumMapLemmas

/-! ## The `+` case

Unlike the `×` case, `sumComb` is *not* literally `iPlus.comp ((sumMap a b).comp jPlus)` by
`rfl` (Definition 8.9 builds it from `cond`/`whichMap` instead) — but it *is* that map
elementwise (`sumComb_eq_iPlus_sumMap_jPlus` below), by the exact same case-split already used
for `isRetraction_sumComb`/`le_idMap_sumComb` in `Proposition810.lean`. Given that bridge, the
rest is verbatim the `×` case's algebra, now powered by `sumMap_id`/`sumMap_comp`. -/

section SumCase

variable (a b : ApproximableMap U U)

/-- **`sumComb a b = i₊ ∘ (a+b) ∘ j₊`, at the level of approximable maps**, where `a+b` on the
right is Exercise 3.19's `sumMap`. Proved by case-splitting on `sum_element_trichotomy` of
`jPlus.toElementMap x`, matching `sumMap`'s elementwise formulas
(`toElementMap_sumMap_of_left/right`, `sumMap_bot`) against `sumComb`'s own
(`toElementMap_sumComb_of_left/right/neither`, `Proposition810.lean`). The bottom case additionally
needs `iPlus.toElementMap (sum U U ..).bot = U.bot`, from `iPlus_comp_jPlus_le`. -/
theorem sumComb_eq_iPlus_sumMap_jPlus :
    sumComb a b = iPlus.comp
      ((sumMap (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty) (h₀' := U_mem_nonempty)
          (h₁' := U_mem_nonempty) a b).comp jPlus) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_comp]
  rcases sum_element_trichotomy (jPlus.toElementMap x) with hL | hR | hN
  · rw [toElementMap_sumComb_of_left hL, toElementMap_sumMap_of_left hL]
  · rw [toElementMap_sumComb_of_right hR, toElementMap_sumMap_of_right hR]
  · rw [toElementMap_sumComb_of_neither hN, reaches_neither_iff_eq_bot.mp hN, sumMap_bot,
      toElementMap_bot_eq_bot_of_comp_le_idMap iPlus_comp_jPlus_le]

/-- **`I_+ : D_a + D_b → 𝒰`**, built by transporting `i₊` (Definition 8.9) through the functorial
action of `+` (Exercise 3.19's `sumMap`) on the injections `i_a : D_a → 𝒰`, `i_b : D_b → 𝒰`. -/
noncomputable def ISumComb : ApproximableMap (sum (fixedNbhd a) (fixedNbhd b)
    (fixedNbhd_mem_nonempty a) (fixedNbhd_mem_nonempty b)) U :=
  iPlus.comp (sumMap (h₀' := U_mem_nonempty) (h₁' := U_mem_nonempty)
    (fixedNbhd_subsystem a).inj (fixedNbhd_subsystem b).inj)

/-- **`J_+ : 𝒰 → D_a + D_b`**, symmetric to `ISumComb`, via the projections `j_a`, `j_b`. -/
noncomputable def JSumComb : ApproximableMap U (sum (fixedNbhd a) (fixedNbhd b)
    (fixedNbhd_mem_nonempty a) (fixedNbhd_mem_nonempty b)) :=
  (sumMap (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)
    (fixedNbhd_subsystem a).proj (fixedNbhd_subsystem b).proj).comp jPlus

theorem JSumComb_comp_ISumComb :
    (JSumComb a b).comp (ISumComb a b) =
      idMap (sum (fixedNbhd a) (fixedNbhd b) (fixedNbhd_mem_nonempty a)
        (fixedNbhd_mem_nonempty b)) := by
  unfold JSumComb ISumComb
  rw [comp_assoc, ← comp_assoc jPlus iPlus (sumMap _ _), jPlus_comp_iPlus, idMap_comp,
    ← sumMap_comp, (fixedNbhd_subsystem a).proj_comp_inj, (fixedNbhd_subsystem b).proj_comp_inj,
    sumMap_id]

theorem ISumComb_comp_JSumComb (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    (ISumComb a b).comp (JSumComb a b) = sumComb a b := by
  unfold ISumComb JSumComb
  rw [comp_assoc, ← comp_assoc (sumMap _ _) (sumMap _ _) jPlus, ← sumMap_comp,
    inj_comp_proj_eq_self ha, inj_comp_proj_eq_self hb, ← comp_assoc,
    sumComb_eq_iPlus_sumMap_jPlus, comp_assoc]

/-- **Proposition 8.10(b), `+`-case.** `a, b` finitary projections `⟹` `a + b` is finitary, with
witnessing domain `D_a + D_b`. -/
theorem finitary_sumComb (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    IsFinitary (sumComb a b) :=
  isFinitary_of_projectionPair (ISumComb a b) (JSumComb a b) (JSumComb_comp_ISumComb a b)
    (ISumComb_comp_JSumComb a b ha hb).symm

/-- **Proposition 8.10(b), `+`-case, the isomorphism `D_{a+b} ≅ D_a + D_b`.** -/
noncomputable def sumComb_elementIso (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    (sum (fixedNbhd a) (fixedNbhd b) (fixedNbhd_mem_nonempty a) (fixedNbhd_mem_nonempty b)).Element
      ≃o {y : U.Element // (sumComb a b).toElementMap y = y} :=
  elementIsoOfProjectionPair (ISumComb a b) (JSumComb a b) (JSumComb_comp_ISumComb a b)
    (ISumComb_comp_JSumComb a b ha hb).symm

/-- **Proposition 8.10(b), `+`-case, in full.** `a, b` finitary projections `⟹` `a + b` is a
finitary projection, and its fixed-point set is order-isomorphic to `D_a + D_b`. -/
theorem finitaryProjection_sumComb (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    IsFinitaryProjection (sumComb a b) :=
  ⟨isProjection_sumComb ha.1 hb.1, finitary_sumComb a b ha hb⟩

end SumCase

/-! ## `expMap`: the Hom-bifunctor `(𝒟₀→𝒟₁) → (𝒟₀'→𝒟₁')`, for `h : 𝒟₀'→𝒟₀`, `k : 𝒟₁→𝒟₁'`

Generalizes `lamComb`'s construction (`Definition89.lean`) — the Hom-functor's action on maps,
`f ↦ k∘f∘h` — away from self-maps of `𝒰` (`lamComb a b = expMap a b`, `expMap_eq_lamComb` below)
to a genuine bifunctor on approximable maps between arbitrary neighbourhood systems, contravariant
in `h` and covariant in `k`. -/

section ExpMap

variable {γ δ γ' δ' γ'' δ'' : Type*}
variable {V0 : NeighborhoodSystem γ} {V1 : NeighborhoodSystem δ}
variable {V0' : NeighborhoodSystem γ'} {V1' : NeighborhoodSystem δ'}
variable {V0'' : NeighborhoodSystem γ''} {V1'' : NeighborhoodSystem δ''}

/-- **The Hom-functor's action on maps**, `f ↦ k∘f∘h`, transported to the function-space
neighbourhood systems via `curry`/`evalMap`/`prodMap`, exactly as `lamComb` (`Definition89.lean`)
does for the self-map case. -/
noncomputable def expMap (h : ApproximableMap V0' V0) (k : ApproximableMap V1 V1') :
    ApproximableMap (funSpace V0 V1) (funSpace V0' V1') :=
  curry (k.comp ((evalMap V0 V1).comp (prodMap (idMap (funSpace V0 V1)) h)))

theorem expMap_eq (h : ApproximableMap V0' V0) (k : ApproximableMap V1 V1') :
    expMap h k = curry (k.comp ((evalMap V0 V1).comp (prodMap (idMap (funSpace V0 V1)) h))) := rfl

/-- `expMap` specializes to `lamComb` on self-maps of `𝒰`. -/
theorem expMap_eq_lamComb (a b : ApproximableMap U U) : expMap a b = lamComb a b := rfl

/-- **`expMap h k`, transported through `funSpaceEquiv`, is exactly `f ↦ k∘f∘h`.** Verbatim
`toApproxMap_toElementMap_lamComb`'s proof (`Proposition810.lean`), generalized away from
self-maps. -/
theorem toApproxMap_toElementMap_expMap (h : ApproximableMap V0' V0) (k : ApproximableMap V1 V1')
    (φ : (funSpace V0 V1).Element) :
    toApproxMap ((expMap h k).toElementMap φ) = k.comp ((toApproxMap φ).comp h) := by
  apply ext_of_toElementMap
  intro z
  rw [expMap_eq, toElementMap_curry_apply, toElementMap_comp, toElementMap_comp,
    toElementMap_prodMap_pair, toElementMap_idMap, evalMap_apply, toElementMap_comp,
    toElementMap_comp]

/-- **`expMap` preserves identities: `expMap I I = I`.** -/
theorem expMap_id : expMap (idMap V0) (idMap V1) = idMap (funSpace V0 V1) := by
  apply ext_of_toElementMap
  intro φ
  apply (funSpaceEquiv V0 V1).injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, toElementMap_idMap,
    toApproxMap_toElementMap_expMap, comp_idMap, idMap_comp]

/-- **`expMap` preserves composition, contravariantly in `h`:
`expMap (h∘h') (k'∘k) = expMap h' k' ∘ expMap h k`.** -/
theorem expMap_comp (h : ApproximableMap V0' V0) (k : ApproximableMap V1 V1')
    (h' : ApproximableMap V0'' V0') (k' : ApproximableMap V1' V1'') :
    expMap (h.comp h') (k'.comp k) = (expMap h' k').comp (expMap h k) := by
  apply ext_of_toElementMap
  intro φ
  apply (funSpaceEquiv V0'' V1'').injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, toApproxMap_toElementMap_expMap, toElementMap_comp,
    toApproxMap_toElementMap_expMap, toApproxMap_toElementMap_expMap]
  simp only [comp_assoc]

end ExpMap

/-! ## The `→` case -/

section ArrowCase

variable (a b : ApproximableMap U U)

/-- **`I_→ : (D_a → D_b) → 𝒰`**, built by transporting `i_→` (Definition 8.9) through the
functorial action of `→` (`expMap`) on `j_a : 𝒰 → D_a` (contravariant slot) and
`i_b : D_b → 𝒰` (covariant slot). -/
noncomputable def IArrowComb : ApproximableMap (funSpace (fixedNbhd a) (fixedNbhd b)) U :=
  iArrow.comp (expMap (fixedNbhd_subsystem a).proj (fixedNbhd_subsystem b).inj)

/-- **`J_→ : 𝒰 → (D_a → D_b)`**, symmetric to `IArrowComb`, via `i_a` (contravariant) and
`j_b` (covariant). -/
noncomputable def JArrowComb : ApproximableMap U (funSpace (fixedNbhd a) (fixedNbhd b)) :=
  (expMap (fixedNbhd_subsystem a).inj (fixedNbhd_subsystem b).proj).comp jArrow

theorem JArrowComb_comp_IArrowComb :
    (JArrowComb a b).comp (IArrowComb a b) =
      idMap (funSpace (fixedNbhd a) (fixedNbhd b)) := by
  unfold JArrowComb IArrowComb
  rw [comp_assoc, ← comp_assoc jArrow iArrow (expMap _ _), jArrow_comp_iArrow, idMap_comp,
    ← expMap_comp, (fixedNbhd_subsystem a).proj_comp_inj, (fixedNbhd_subsystem b).proj_comp_inj,
    expMap_id]

theorem IArrowComb_comp_JArrowComb (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    (IArrowComb a b).comp (JArrowComb a b) = arrowComb a b := by
  unfold IArrowComb JArrowComb
  rw [comp_assoc, ← comp_assoc (expMap _ _) (expMap _ _) jArrow, ← expMap_comp,
    inj_comp_proj_eq_self ha, inj_comp_proj_eq_self hb, expMap_eq_lamComb, ← comp_assoc,
    arrowComb_eq, comp_assoc]

/-- **Proposition 8.10(b), `→`-case.** `a, b` finitary projections `⟹` `a → b` is finitary, with
witnessing domain `D_a → D_b`. -/
theorem finitary_arrowComb (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    IsFinitary (arrowComb a b) :=
  isFinitary_of_projectionPair (IArrowComb a b) (JArrowComb a b) (JArrowComb_comp_IArrowComb a b)
    (IArrowComb_comp_JArrowComb a b ha hb).symm

/-- **Proposition 8.10(b), `→`-case, the isomorphism `D_{a→b} ≅ (D_a → D_b)`.** -/
noncomputable def arrowComb_elementIso (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    (funSpace (fixedNbhd a) (fixedNbhd b)).Element ≃o
      {y : U.Element // (arrowComb a b).toElementMap y = y} :=
  elementIsoOfProjectionPair (IArrowComb a b) (JArrowComb a b) (JArrowComb_comp_IArrowComb a b)
    (IArrowComb_comp_JArrowComb a b ha hb).symm

/-- **Proposition 8.10(b), `→`-case, in full.** `a, b` finitary projections `⟹` `a → b` is a
finitary projection, and its fixed-point set is order-isomorphic to `D_a → D_b`. -/
theorem finitaryProjection_arrowComb (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    IsFinitaryProjection (arrowComb a b) :=
  ⟨isProjection_arrowComb ha.1 hb.1, finitary_arrowComb a b ha hb⟩

end ArrowCase

/-! ## Proposition 8.10(b) — assembled -/

/-- **Proposition 8.10(b) (Scott 1981, PRG-19), in full.** If `a, b : 𝒰 → 𝒰` are finitary
projections, then so are `a+b`, `a×b`, `a→b`, with `D_{a+b} ≅ D_a+D_b`, `D_{a×b} ≅ D_a×D_b`,
`D_{a→b} ≅ (D_a→D_b)`. -/
theorem finitaryProjection_combinators {a b : ApproximableMap U U}
    (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b) :
    IsFinitaryProjection (sumComb a b) ∧ IsFinitaryProjection (prodComb a b) ∧
      IsFinitaryProjection (arrowComb a b) :=
  ⟨finitaryProjection_sumComb a b ha hb, finitaryProjection_prodComb a b ha hb,
    finitaryProjection_arrowComb a b ha hb⟩

end Scott1980.Neighborhood

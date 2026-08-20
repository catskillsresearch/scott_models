/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Definition89
import Scott1980.Neighborhood.Definition83
import Scott1980.Neighborhood.Theorem69

/-!
# Proposition 8.10 (Scott 1981, PRG-19) — the combinators preserve projections

**Proposition 8.10 (first half).** If `a, b : 𝒰 → 𝒰` are projections, then so are `a+b`, `a×b`,
and `a→b`.

*Scott's proof.* `a, b ⊑ I` gives `a+b ⊑ I+I = i₊∘j₊ ⊑ I` (similarly for `×`, `→`);
`a = a∘a, b = b∘b` gives `(a×b)∘(a×b) = i_×∘⟨a∘a∘proj₀, b∘b∘proj₁⟩∘j_× = a×b` (similarly for `+`,
`→`).

## What is formalized in this file

Both halves of Proposition 8.10 — **`IsRetraction`- and `≤ idMap U`-closure** — for all three
combinators, i.e. `IsProjection a → IsProjection b → IsProjection (a*b)` for `* ∈ {+,×,→}`.

* **`×` (cleanest).** `prodComb a b` is *literally* `iTimes.comp ((prodMap a b).comp jTimes)`
  (`prodMap a b = ⟨a∘proj₀, b∘proj₁⟩` is exactly Exercise 3.19's product-functor combinator,
  unfolding `prodComb`'s definition, `rfl`). Both closure facts reduce, at the element level, to
  `pair_le_pair_iff`/`toElementMap_prodMap`/`toElementMap_mono` plus the two generic
  projection-pair identities below.

* **`→` (via `funSpaceEquiv`).** `lamComb a b`'s action, *transported through* `funSpaceEquiv`
  (Theorem 3.10, `(funSpace U U).Element ≃o ApproximableMap U U`), is exactly Scott's map-level
  formula `f ↦ b∘f∘a` (`toApproxMap_toElementMap_lamComb`, chaining `toElementMap_curry_apply`,
  `toElementMap_prodMap_pair`, `evalMap_apply`). Both closure facts then reduce to the same
  algebra as `×`, transported back through the order-embedding `toApproxMap`.

* **`+` (direct, no bridge to `sumMap`).** `sumMap`'s raw relation (`Exercise319Sum.lean`) is
  *not* literally built from `cond`/`which`, so there is no equally cheap `sumComb = i₊∘sumMap∘j₊`
  bridge; instead both facts are proved directly from Scott's literal formula via the elementwise
  characterizations `cond_toElementMap_mem` (Exercise 3.26), `which_mem_zero/one`, and the
  round-trip identities `inMap₀_outMap₀_eq_of_left`/`inMap₁_outMap₁_eq_of_right`, case-splitting
  on `sum_element_trichotomy`. Idempotence's bottom case additionally needs `jPlus_bot_eq_bot`
  (an instance of the general `toElementMap_bot_eq_bot_of_comp_eq_idMap`): if `j∘i = I_D`, then
  `j(E.bot)` is a lower bound of *all* of `|D|` (`D.bot ≤ i(v)`, monotone through `j`, landing on
  `j(i(v)) = v` — take `v := D.bot` — via `j∘i=I_D`), so `j(E.bot) ≤ D.bot`, whence `= D.bot` by
  antisymmetry with `bot_le`; no disjointness needed. The "reaches left"/"reaches right" case
  formulas' own idempotence step *does* need the disjointness fact `not_sum_reaches_both`
  (`inj₀_inter_inj₁`/`not_sum_mem_empty`) to rule out the other injection's guard in `which`, and
  `inMap₀_toElementMap_reaches_left`/`inMap₁_toElementMap_reaches_right` (witnessed by the master
  neighbourhood) to re-enter the same case after one more application of `a`/`b`.

**Not attempted here: the second half of Proposition 8.10** (finitary-closure, i.e.
`D_a * D_b ≅ D_{a*b}`) — this needs substantially more infrastructure (a general "conjugate
fixed-point-sets across a projection pair" lemma, plus `prodEquiv`/`funSpaceEquiv`/a
coproduct-element characterization for `sum`) and is left as a documented follow-up; see
`HANDOFF.md`.

Axiom footprint: everything here mentions `U`, so (as with `Definition89.lean`) it inherits `U`'s
own `Classical.choice` footprint — `⊆ {propext, Classical.choice, Quot.sound}`, confirmed not new.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

/-! ## Two generic projection-pair identities, at the element level -/

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- If `j ∘ i = I_D`, then `j(i(v)) = v` for every `v ∈ |D|`. -/
theorem toElementMap_of_comp_eq_idMap {i : ApproximableMap D E} {j : ApproximableMap E D}
    (hji : j.comp i = idMap D) (v : D.Element) : j.toElementMap (i.toElementMap v) = v := by
  rw [← toElementMap_comp, hji, toElementMap_idMap]

/-- If `i ∘ j ≤ I_E`, then `i(j(x)) ≤ x` for every `x ∈ |E|`. -/
theorem toElementMap_le_of_comp_le_idMap {i : ApproximableMap D E} {j : ApproximableMap E D}
    (hij : i.comp j ≤ idMap E) (x : E.Element) : i.toElementMap (j.toElementMap x) ≤ x := by
  have h := (le_iff_toElementMap_le.mp hij) x
  rwa [toElementMap_comp, toElementMap_idMap] at h

/-- `a ≤ idMap E` unwound at the element level: `a(x) ≤ x` for every `x`. -/
theorem toElementMap_le_self_of_le_idMap {a : ApproximableMap E E} (ha : a ≤ idMap E)
    (x : E.Element) : a.toElementMap x ≤ x := by
  have h := (le_iff_toElementMap_le.mp ha) x
  rwa [toElementMap_idMap] at h

/-- `a ∘ a = a` unwound at the element level: `a(a(x)) = a(x)` for every `x`. -/
theorem toElementMap_idem_of_isRetraction {a : ApproximableMap E E} (ha : IsRetraction a)
    (x : E.Element) : a.toElementMap (a.toElementMap x) = a.toElementMap x := by
  rw [← toElementMap_comp, ha]

/-! ## `×` (Definition 8.9's `prodComb`) -/

theorem prodComb_eq (a b : ApproximableMap U U) :
    prodComb a b = iTimes.comp ((prodMap a b).comp jTimes) := rfl

theorem toElementMap_prodComb (a b : ApproximableMap U U) (x : U.Element) :
    (prodComb a b).toElementMap x =
      iTimes.toElementMap (pair (a.toElementMap (jTimes.toElementMap x).fst)
        (b.toElementMap (jTimes.toElementMap x).snd)) := by
  rw [prodComb_eq]
  simp only [toElementMap_comp, toElementMap_prodMap]

/-- **Proposition 8.10, `×`-case, retraction half.** -/
theorem isRetraction_prodComb {a b : ApproximableMap U U} (ha : IsRetraction a)
    (hb : IsRetraction b) : IsRetraction (prodComb a b) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_prodComb a b ((prodComb a b).toElementMap x),
    toElementMap_prodComb a b x, toElementMap_of_comp_eq_idMap jTimes_comp_iTimes, fst_pair,
    snd_pair, toElementMap_idem_of_isRetraction ha, toElementMap_idem_of_isRetraction hb]

/-- **Proposition 8.10, `×`-case, projection half.** -/
theorem le_idMap_prodComb {a b : ApproximableMap U U} (ha : a ≤ idMap U) (hb : b ≤ idMap U) :
    prodComb a b ≤ idMap U := by
  rw [le_iff_toElementMap_le]
  intro x
  rw [toElementMap_prodComb, toElementMap_idMap]
  have hpair : pair (a.toElementMap (jTimes.toElementMap x).fst)
      (b.toElementMap (jTimes.toElementMap x).snd)
      ≤ pair (jTimes.toElementMap x).fst (jTimes.toElementMap x).snd :=
    pair_le_pair_iff.mpr
      ⟨toElementMap_le_self_of_le_idMap ha _, toElementMap_le_self_of_le_idMap hb _⟩
  rw [pair_fst_snd] at hpair
  calc iTimes.toElementMap (pair (a.toElementMap (jTimes.toElementMap x).fst)
        (b.toElementMap (jTimes.toElementMap x).snd))
      ≤ iTimes.toElementMap (jTimes.toElementMap x) := iTimes.toElementMap_mono hpair
    _ ≤ x := toElementMap_le_of_comp_le_idMap iTimes_comp_jTimes_le x

/-- **Proposition 8.10 (Scott 1981, PRG-19), `×`-case.** `a, b` projections `⟹` `a × b` a
projection. -/
theorem isProjection_prodComb {a b : ApproximableMap U U}
    (ha : IsProjection a) (hb : IsProjection b) : IsProjection (prodComb a b) :=
  ⟨isRetraction_prodComb ha.1 hb.1, le_idMap_prodComb ha.2 hb.2⟩

/-! ## `→` (Definition 8.9's `arrowComb`), via `funSpaceEquiv` -/

theorem lamComb_eq (a b : ApproximableMap U U) :
    lamComb a b = curry (b.comp ((evalMap U U).comp (prodMap (idMap (funSpace U U)) a))) := rfl

/-- **`lamComb a b`, transported through `funSpaceEquiv`, is exactly `λf. b∘f∘a`.** Chains
`toElementMap_curry_apply` (Theorem 3.12(i)), `toElementMap_prodMap_pair`/`toElementMap_idMap`,
and `evalMap_apply` (Theorem 3.11(i)). -/
theorem toApproxMap_toElementMap_lamComb (a b : ApproximableMap U U)
    (φ : (funSpace U U).Element) :
    toApproxMap ((lamComb a b).toElementMap φ) = b.comp ((toApproxMap φ).comp a) := by
  apply ext_of_toElementMap
  intro z
  rw [lamComb_eq, toElementMap_curry_apply, toElementMap_comp, toElementMap_comp,
    toElementMap_prodMap_pair, toElementMap_idMap, evalMap_apply, toElementMap_comp,
    toElementMap_comp]

/-- **Proposition 8.10, `→`-case (the `lamComb` half), retraction.** -/
theorem isRetraction_lamComb {a b : ApproximableMap U U} (ha : IsRetraction a)
    (hb : IsRetraction b) : IsRetraction (lamComb a b) := by
  apply ext_of_toElementMap
  intro φ
  apply (funSpaceEquiv U U).injective
  rw [funSpaceEquiv_apply, funSpaceEquiv_apply, toElementMap_comp,
    toApproxMap_toElementMap_lamComb a b ((lamComb a b).toElementMap φ),
    toApproxMap_toElementMap_lamComb a b φ,
    comp_assoc b ((toApproxMap φ).comp a) a,
    ← comp_assoc b b (((toApproxMap φ).comp a).comp a), hb,
    comp_assoc (toApproxMap φ) a a, ha]

/-- **Proposition 8.10, `→`-case (the `lamComb` half), projection.** -/
theorem le_idMap_lamComb {a b : ApproximableMap U U} (ha : a ≤ idMap U) (hb : b ≤ idMap U) :
    lamComb a b ≤ idMap (funSpace U U) := by
  rw [le_iff_toElementMap_le]
  intro φ
  rw [toElementMap_idMap, ← (funSpaceEquiv U U).le_iff_le, funSpaceEquiv_apply,
    funSpaceEquiv_apply, toApproxMap_toElementMap_lamComb]
  calc b.comp ((toApproxMap φ).comp a) ≤ (idMap U).comp ((toApproxMap φ).comp (idMap U)) :=
        comp_mono_gen hb (comp_mono_gen le_rfl ha)
    _ = toApproxMap φ := by rw [comp_idMap, idMap_comp]

theorem arrowComb_eq (a b : ApproximableMap U U) :
    arrowComb a b = iArrow.comp ((lamComb a b).comp jArrow) := rfl

theorem toElementMap_arrowComb (a b : ApproximableMap U U) (x : U.Element) :
    (arrowComb a b).toElementMap x =
      iArrow.toElementMap ((lamComb a b).toElementMap (jArrow.toElementMap x)) := by
  rw [arrowComb_eq]
  simp only [toElementMap_comp]

/-- **Proposition 8.10, `→`-case, retraction half.** -/
theorem isRetraction_arrowComb {a b : ApproximableMap U U} (ha : IsRetraction a)
    (hb : IsRetraction b) : IsRetraction (arrowComb a b) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_arrowComb a b ((arrowComb a b).toElementMap x),
    toElementMap_arrowComb a b x, toElementMap_of_comp_eq_idMap jArrow_comp_iArrow,
    toElementMap_idem_of_isRetraction (isRetraction_lamComb ha hb)]

/-- **Proposition 8.10, `→`-case, projection half.** -/
theorem le_idMap_arrowComb {a b : ApproximableMap U U} (ha : a ≤ idMap U) (hb : b ≤ idMap U) :
    arrowComb a b ≤ idMap U := by
  rw [le_iff_toElementMap_le]
  intro x
  rw [toElementMap_arrowComb, toElementMap_idMap]
  calc iArrow.toElementMap ((lamComb a b).toElementMap (jArrow.toElementMap x))
      ≤ iArrow.toElementMap (jArrow.toElementMap x) :=
        iArrow.toElementMap_mono
          (toElementMap_le_self_of_le_idMap (le_idMap_lamComb ha hb) _)
    _ ≤ x := toElementMap_le_of_comp_le_idMap iArrow_comp_jArrow_le x

/-- **Proposition 8.10 (Scott 1981, PRG-19), `→`-case.** `a, b` projections `⟹` `a → b` a
projection. -/
theorem isProjection_arrowComb {a b : ApproximableMap U U}
    (ha : IsProjection a) (hb : IsProjection b) : IsProjection (arrowComb a b) :=
  ⟨isRetraction_arrowComb ha.1 hb.1, le_idMap_arrowComb ha.2 hb.2⟩

/-! ## `+` (Definition 8.9's `sumComb`), by direct case analysis on `sum_element_trichotomy` -/

/-- No element of `𝒟₀+𝒟₁` reaches into both the left and the right copy (Exercise 3.18's
disjointness `inj₀_inter_inj₁`, plus `not_sum_mem_empty`). -/
theorem not_sum_reaches_both {γ δ} {V₀ : NeighborhoodSystem γ} {V₁ : NeighborhoodSystem δ}
    {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
    {w : (sum V₀ V₁ h₀ h₁).Element} (hL : ∃ X, V₀.mem X ∧ w.mem (inj₀ X))
    (hR : ∃ Y, V₁.mem Y ∧ w.mem (inj₁ Y)) : False := by
  obtain ⟨X, _, hX⟩ := hL
  obtain ⟨Y, _, hY⟩ := hR
  have h := w.inter_mem hX hY
  rw [inj₀_inter_inj₁] at h
  exact not_sum_mem_empty (w.sub h)

/-- The image of `in₀` always reaches the left copy (witnessed by `V₀.master`, since `v.master_mem`
always holds and `in₀`'s relation only needs `inj₀ X ⊆ inj₀ V₀.master`). -/
theorem inMap₀_toElementMap_reaches_left {γ δ} {V₀ : NeighborhoodSystem γ} {V₁ : NeighborhoodSystem δ}
    {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} (v : V₀.Element) :
    ∃ X, V₀.mem X ∧ ((inMap₀ (h₀ := h₀) (h₁ := h₁)).toElementMap v).mem (inj₀ X) := by
  refine ⟨V₀.master, V₀.master_mem, V₀.master, v.master_mem, V₀.master_mem, ?_, subset_rfl⟩
  exact Or.inr (Or.inl ⟨V₀.master, V₀.master_mem, rfl⟩)

/-- The image of `in₁` always reaches the right copy. -/
theorem inMap₁_toElementMap_reaches_right {γ δ} {V₀ : NeighborhoodSystem γ} {V₁ : NeighborhoodSystem δ}
    {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} (v : V₁.Element) :
    ∃ Y, V₁.mem Y ∧ ((inMap₁ (h₀ := h₀) (h₁ := h₁)).toElementMap v).mem (inj₁ Y) := by
  refine ⟨V₁.master, V₁.master_mem, V₁.master, v.master_mem, V₁.master_mem, ?_, subset_rfl⟩
  exact Or.inr (Or.inr ⟨V₁.master, V₁.master_mem, rfl⟩)

/-- **`j₊` sends `𝒰`'s bottom to `𝒰+𝒰`'s bottom.** General fact: if `j ∘ i = I_D`, then `j(E.bot)`
is a global lower bound of `|D|` (via `D.bot ≤ i(v)` monotone through `j`, landing on
`j(i(D.bot)) = D.bot` for `v := D.bot`), hence equals `D.bot` by antisymmetry with `bot_le`. -/
theorem toElementMap_bot_eq_bot_of_comp_eq_idMap {i : ApproximableMap D E} {j : ApproximableMap E D}
    (hji : j.comp i = idMap D) : j.toElementMap E.bot = D.bot := by
  apply le_antisymm
  · have h2 := j.toElementMap_mono (E.bot_le (i.toElementMap D.bot))
    rwa [toElementMap_of_comp_eq_idMap hji] at h2
  · exact D.bot_le _

theorem jPlus_bot_eq_bot :
    jPlus.toElementMap U.bot = (sum U U U_mem_nonempty U_mem_nonempty).bot :=
  toElementMap_bot_eq_bot_of_comp_eq_idMap jPlus_comp_iPlus

theorem sumComb_eq (a b : ApproximableMap U U) :
    sumComb a b = (cond U).comp
      ((paired (whichMap U U U_mem_nonempty U_mem_nonempty)
          (paired (iPlus.comp ((inMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).comp
                    (a.comp (outMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)))))
                  (iPlus.comp ((inMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).comp
                    (b.comp (outMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty))))))).comp
        jPlus) := rfl

/-- **Elementwise unfolding of `sumComb`.** Chains `sumComb_eq`, `toElementMap_comp`, and
`toElementMap_paired`, landing exactly on `cond_toElementMap_mem`'s pattern. -/
theorem toElementMap_sumComb_mem (a b : ApproximableMap U U) (x : U.Element) {Z : Set ℚ} :
    ((sumComb a b).toElementMap x).mem Z ↔
      (((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap (jPlus.toElementMap x)).mem
          Example12.zero ∧
        (iPlus.toElementMap ((inMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
          (a.toElementMap ((outMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
            (jPlus.toElementMap x))))).mem Z) ∨
      (((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap (jPlus.toElementMap x)).mem
          Example12.one ∧
        (iPlus.toElementMap ((inMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
          (b.toElementMap ((outMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
            (jPlus.toElementMap x))))).mem Z) ∨
      Z = U.master := by
  rw [sumComb_eq]
  simp only [toElementMap_comp, toElementMap_paired]
  rw [cond_toElementMap_mem]

/-- **On a "left" point** (`jPlus x` reaches the left copy), `sumComb a b` evaluates to Scott's
literal `i₊∘in₀∘a∘out₀` formula. -/
theorem toElementMap_sumComb_of_left {a b : ApproximableMap U U} {x : U.Element}
    (hL : ∃ X, U.mem X ∧ (jPlus.toElementMap x).mem (inj₀ X)) :
    (sumComb a b).toElementMap x =
      iPlus.toElementMap ((inMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
        (a.toElementMap ((outMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
          (jPlus.toElementMap x)))) := by
  have hz : ((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap
      (jPlus.toElementMap x)).mem Example12.zero := which_mem_zero.mpr hL
  have hno : ¬ ((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap
      (jPlus.toElementMap x)).mem Example12.one :=
    fun h => not_sum_reaches_both hL (which_mem_one.mp h)
  apply Element.ext
  intro Z
  rw [toElementMap_sumComb_mem]
  constructor
  · rintro (⟨_, h⟩ | ⟨h1, _⟩ | rfl)
    · exact h
    · exact absurd h1 hno
    · exact Element.master_mem _
  · intro h
    exact Or.inl ⟨hz, h⟩

/-- **On a "right" point**, symmetric to `toElementMap_sumComb_of_left`. -/
theorem toElementMap_sumComb_of_right {a b : ApproximableMap U U} {x : U.Element}
    (hR : ∃ Y, U.mem Y ∧ (jPlus.toElementMap x).mem (inj₁ Y)) :
    (sumComb a b).toElementMap x =
      iPlus.toElementMap ((inMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
        (b.toElementMap ((outMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
          (jPlus.toElementMap x)))) := by
  have ho : ((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap
      (jPlus.toElementMap x)).mem Example12.one := which_mem_one.mpr hR
  have hnz : ¬ ((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap
      (jPlus.toElementMap x)).mem Example12.zero :=
    fun h => not_sum_reaches_both (which_mem_zero.mp h) hR
  apply Element.ext
  intro Z
  rw [toElementMap_sumComb_mem]
  constructor
  · rintro (⟨h1, _⟩ | ⟨_, h⟩ | rfl)
    · exact absurd h1 hnz
    · exact h
    · exact Element.master_mem _
  · intro h
    exact Or.inr (Or.inl ⟨ho, h⟩)

/-- **On a point reaching neither copy** (in particular, `𝒰`'s own `⊥`, via `jPlus_bot_eq_bot`),
`sumComb a b` sends it to `𝒰`'s `⊥`. -/
theorem toElementMap_sumComb_of_neither {a b : ApproximableMap U U} {x : U.Element}
    (hN : ∀ W, (jPlus.toElementMap x).mem W → W = (sum U U U_mem_nonempty U_mem_nonempty).master) :
    (sumComb a b).toElementMap x = U.bot := by
  have hnz : ¬ ((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap
      (jPlus.toElementMap x)).mem Example12.zero := by
    rw [which_mem_zero]
    rintro ⟨X, _, hX⟩
    exact inj₀_ne_sumMaster (hN _ hX)
  have hno : ¬ ((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap
      (jPlus.toElementMap x)).mem Example12.one := by
    rw [which_mem_one]
    rintro ⟨Y, _, hY⟩
    exact inj₁_ne_sumMaster (hN _ hY)
  apply Element.ext
  intro Z
  rw [toElementMap_sumComb_mem, mem_bot]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | h)
    · exact absurd h hnz
    · exact absurd h hno
    · exact h
  · intro h
    exact Or.inr (Or.inr h)

/-- **Proposition 8.10, `+`-case, retraction half.** -/
theorem isRetraction_sumComb {a b : ApproximableMap U U} (ha : IsRetraction a)
    (hb : IsRetraction b) : IsRetraction (sumComb a b) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp]
  rcases sum_element_trichotomy (jPlus.toElementMap x) with hL | hR | hN
  · rw [toElementMap_sumComb_of_left hL]
    set v := a.toElementMap (outMap₀.toElementMap (jPlus.toElementMap x)) with hv
    have hjy : jPlus.toElementMap (iPlus.toElementMap (inMap₀.toElementMap v))
        = inMap₀.toElementMap v := toElementMap_of_comp_eq_idMap jPlus_comp_iPlus _
    have hLy : ∃ X, U.mem X ∧
        (jPlus.toElementMap (iPlus.toElementMap (inMap₀.toElementMap v))).mem (inj₀ X) := by
      rw [hjy]; exact inMap₀_toElementMap_reaches_left v
    rw [toElementMap_sumComb_of_left hLy, hjy,
      toElementMap_of_comp_eq_idMap outMap₀_comp_inMap₀ v, toElementMap_idem_of_isRetraction ha]
  · rw [toElementMap_sumComb_of_right hR]
    set v := b.toElementMap (outMap₁.toElementMap (jPlus.toElementMap x)) with hv
    have hjy : jPlus.toElementMap (iPlus.toElementMap (inMap₁.toElementMap v))
        = inMap₁.toElementMap v := toElementMap_of_comp_eq_idMap jPlus_comp_iPlus _
    have hRy : ∃ Y, U.mem Y ∧
        (jPlus.toElementMap (iPlus.toElementMap (inMap₁.toElementMap v))).mem (inj₁ Y) := by
      rw [hjy]; exact inMap₁_toElementMap_reaches_right v
    rw [toElementMap_sumComb_of_right hRy, hjy,
      toElementMap_of_comp_eq_idMap outMap₁_comp_inMap₁ v, toElementMap_idem_of_isRetraction hb]
  · rw [toElementMap_sumComb_of_neither hN]
    apply toElementMap_sumComb_of_neither
    intro W hW
    rw [jPlus_bot_eq_bot, mem_bot] at hW
    exact hW

/-- **Proposition 8.10, `+`-case, projection half.** -/
theorem le_idMap_sumComb {a b : ApproximableMap U U} (ha : a ≤ idMap U) (hb : b ≤ idMap U) :
    sumComb a b ≤ idMap U := by
  rw [le_iff_toElementMap_le]
  intro x
  rw [toElementMap_idMap]
  rcases sum_element_trichotomy (jPlus.toElementMap x) with hL | hR | hN
  · calc (sumComb a b).toElementMap x
        = iPlus.toElementMap ((inMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
            (a.toElementMap ((outMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
              (jPlus.toElementMap x)))) := toElementMap_sumComb_of_left hL
      _ ≤ iPlus.toElementMap ((inMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
            ((outMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
              (jPlus.toElementMap x))) :=
          iPlus.toElementMap_mono (inMap₀.toElementMap_mono (toElementMap_le_self_of_le_idMap ha _))
      _ = iPlus.toElementMap (jPlus.toElementMap x) := by rw [inMap₀_outMap₀_eq_of_left hL]
      _ ≤ x := toElementMap_le_of_comp_le_idMap iPlus_comp_jPlus_le x
  · calc (sumComb a b).toElementMap x
        = iPlus.toElementMap ((inMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
            (b.toElementMap ((outMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
              (jPlus.toElementMap x)))) := toElementMap_sumComb_of_right hR
      _ ≤ iPlus.toElementMap ((inMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
            ((outMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
              (jPlus.toElementMap x))) :=
          iPlus.toElementMap_mono (inMap₁.toElementMap_mono (toElementMap_le_self_of_le_idMap hb _))
      _ = iPlus.toElementMap (jPlus.toElementMap x) := by rw [inMap₁_outMap₁_eq_of_right hR]
      _ ≤ x := toElementMap_le_of_comp_le_idMap iPlus_comp_jPlus_le x
  · rw [toElementMap_sumComb_of_neither hN]
    exact U.bot_le x

/-- **Proposition 8.10 (Scott 1981, PRG-19), `+`-case.** `a, b` projections `⟹` `a + b` a
projection. -/
theorem isProjection_sumComb {a b : ApproximableMap U U}
    (ha : IsProjection a) (hb : IsProjection b) : IsProjection (sumComb a b) :=
  ⟨isRetraction_sumComb ha.1 hb.1, le_idMap_sumComb ha.2 hb.2⟩

/-! ## Proposition 8.10, first half — assembled -/

/-- **Proposition 8.10 (Scott 1981, PRG-19), first half.** If `a, b : 𝒰 → 𝒰` are projections,
then so are `a+b`, `a×b`, and `a→b`. -/
theorem isProjection_combinators {a b : ApproximableMap U U}
    (ha : IsProjection a) (hb : IsProjection b) :
    IsProjection (sumComb a b) ∧ IsProjection (prodComb a b) ∧ IsProjection (arrowComb a b) :=
  ⟨isProjection_sumComb ha hb, isProjection_prodComb ha hb, isProjection_arrowComb ha hb⟩

end Scott1980.Neighborhood

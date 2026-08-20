/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Proposition77

/-!
# Proposition 7.7 — Milestone 4: the Example 6.1 combinators are computable

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VII.

> **Proposition 7.7.** For any effectively given domain `D`, the domain `D^§` is also effectively
> given, and all the combinators of Example 6.1 prove to be computable.

The "`D^§` is effectively given" half is `Proposition77.dsharp_isEffectivelyGiven`. Here we treat,
as Scott does, *a selection* of the Example 6.1 combinators and exhibit them as
`ApproximableMap`s that are `IsComputableMap` with respect to the canonical presentation
`dsharpPresentation P hD`:

* **`inSharpMap`** — Scott's injection `λx. x^§ : D → D^§` (Example 6.1's `inSharp`). Its
  neighbourhood relation is `X (λx.x^§) W ↔ 0·X ⊆ W`, i.e. `V_{2n+1} ⊆ V_k`, a recursive slice of
  the inclusion decider, hence r.e. (`inSharp_isComputable`). `inSharpMap_toElementMap` checks the
  approximable map really computes `inSharp`.
* **`proj0Map`** — the first projection `D^§ → D^§` of the pair part (so `proj0(⟨x,y⟩^§) = x`,
  `proj0_toElementMap_pairSharp`). Its relation is `W proj₀ Z ↔ Z = Γ ∨ ∃ P Q, W = 1·P ∪ 2·Q ∧
  P ⊆ Z`, i.e. on indices `V_m proj₀ V_k ↔ k = 0 ∨ (m even, m ≠ 0, V_{p(m/2-1)} ⊆ V_k)`. Both
  disjuncts are recursively decidable, hence r.e. (`proj0_isComputable`).

Each combinator's relation is *recursively decidable* (no unbounded search), so computability is
`RecDecidable.re` of a Boolean combination of the inclusion/equality/parity deciders — exactly the
style of Theorem 7.4's `proj₀`/`in₀`. The `ApproximableMap` data is choice-free; only the `Prop`
correctness proofs route through `Classical` (set equality over an arbitrary carrier).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)

/-- `(dsharpPresentation P hD).X = Vsharp D P` definitionally; a `simp` handle for the deciders. -/
@[simp] theorem dsharpPresentation_X (P : ComputablePresentation D) (n : ℕ) :
    (dsharpPresentation P hD).X n = Vsharp D P n := rfl

/-! ### `λx. x^§ : D → D^§` (Example 6.1's `inSharp`). -/

/-- **Example 6.1's injection `λx. x^§` as an approximable map.** Scott's neighbourhood relation
`X (λx.x^§) W ↔ 0·X ⊆ W` (`embZero X ⊆ W`). The filter laws are immediate: `inter_right` uses
`memS_inter` (with witness `0·X`), and `mono` uses monotonicity of `embZero`. -/
def inSharpMap : ApproximableMap D (Dsharp D hD) where
  rel X W := D.mem X ∧ MemS D W ∧ embZero X ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨D.master_mem, MemS.gamma, embZero_subset_Gamma D.master_mem⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hsub⟩ ⟨-, hW', hsub'⟩
    exact ⟨hX, memS_inter hD hW hW' (MemS.zero hX) (Set.subset_inter hsub hsub'),
      Set.subset_inter hsub hsub'⟩
  mono := by
    rintro X X' W W' ⟨hX, hW, hsub⟩ hX'X hWW' hX'mem hW'mem
    exact ⟨hX'mem, hW'mem, (embZero_subset.mpr hX'X).trans (hsub.trans hWW')⟩

@[simp] theorem inSharpMap_rel {X : Set α} {W : Set (List Bool × α)} :
    (inSharpMap hD).rel X W ↔ D.mem X ∧ MemS D W ∧ embZero X ⊆ W := Iff.rfl

/-- **`inSharpMap` really computes `inSharp`.** Its elementwise action is Scott's `λx. x^§`. -/
theorem inSharpMap_toElementMap (x : D.Element) :
    (inSharpMap hD).toElementMap x = inSharp D hD x := by
  apply Element.ext
  intro W
  simp only [ApproximableMap.mem_toElementMap, inSharpMap_rel]
  constructor
  · rintro ⟨X, hXx, hX, hW, hsub⟩
    cases hW with
    | gamma => exact Or.inl rfl
    | @zero Y hY => exact Or.inr ⟨Y, x.up_mem hXx hY (embZero_subset.mp hsub), rfl⟩
    | @pair Pp Qq hP hQ =>
      exfalso
      obtain ⟨a, ha⟩ := hD X hX
      rcases hsub (show (([], a) : List Bool × α) ∈ embZero X from ⟨rfl, ha⟩) with
        ⟨p', hp', -⟩ | ⟨q', hq', -⟩
      · simp at hp'
      · simp at hq'
  · rintro (rfl | ⟨Y, hYx, rfl⟩)
    · exact ⟨D.master, x.master_mem, D.master_mem, MemS.gamma, embZero_subset_Gamma D.master_mem⟩
    · exact ⟨Y, hYx, x.sub hYx, MemS.zero (x.sub hYx), subset_rfl⟩

/-- **Proposition 7.7 (Scott 1981, PRG-19) — `λx. x^§` is computable.**
`Xₙ (λx.x^§) V_k ↔ V_{2n+1} ⊆ V_k` (`embZero Xₙ ⊆ V_k`), a recursive slice of the inclusion
decider for `D^§`, hence r.e. -/
theorem inSharp_isComputable (P : ComputablePresentation D) :
    IsComputableMap P (dsharpPresentation P hD) (inSharpMap hD) := by
  show REPred (fun s => (inSharpMap hD).rel (P.X s.unpair.1) (Vsharp D P s.unpair.2))
  have hincl : RecDecidable (fun s => Vsharp D P s.unpair.1 ⊆ Vsharp D P s.unpair.2) :=
    (dsharpPresentation P hD).incl_computable
  have hr : Nat.Primrec (fun t => Nat.pair (2 * t.unpair.1 + 1) t.unpair.2) :=
    (primrec_add₂ (primrec_mul₂ (Nat.Primrec.const 2) Nat.Primrec.left)
      (Nat.Primrec.const 1)).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  simp only [inSharpMap_rel, unpair_pair_fst, unpair_pair_snd, Vsharp_odd]
  exact ⟨fun h => h.2.2, fun h => ⟨P.mem_X _, Vsharp_mem P _, h⟩⟩

/-! ### `proj₀ : D^§ → D^§` (first projection of the pair part). -/

/-- **The first projection of the pair part of `D^§`, as an approximable map.** On the pair summand
`1·P ∪ 2·Q` it returns `P`; everywhere else it returns `⊥ = {Γ}`. The neighbourhood relation is
`W proj₀ Z ↔ Z = Γ ∨ ∃ P Q, W = 1·P ∪ 2·Q ∧ P ⊆ Z`. -/
def proj0Map : ApproximableMap (Dsharp D hD) (Dsharp D hD) where
  rel W Z := MemS D W ∧ MemS D Z ∧ (Z = Gamma D ∨ ∃ Pp Qq, W = embPair Pp Qq ∧ Pp ⊆ Z)
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨MemS.gamma, MemS.gamma, Or.inl rfl⟩
  inter_right := by
    rintro W Z Z' ⟨hW, hZ, hd⟩ ⟨-, hZ', hd'⟩
    have hgZ : Z ⊆ Gamma D := memS_subset_gamma hZ
    have hgZ' : Z' ⊆ Gamma D := memS_subset_gamma hZ'
    rcases hd with rfl | ⟨Pp, Qq, hWeq, hPZ⟩
    · rw [Set.inter_eq_right.mpr hgZ']; exact ⟨hW, hZ', hd'⟩
    · rcases hd' with rfl | ⟨Pp', Qq', hWeq', hPZ'⟩
      · rw [Set.inter_eq_left.mpr hgZ]; exact ⟨hW, hZ, Or.inr ⟨Pp, Qq, hWeq, hPZ⟩⟩
      · have hPP : Pp = Pp' := (embPair_injective (hWeq.symm.trans hWeq')).1
        have hPsub : Pp ⊆ Z ∩ Z' := Set.subset_inter hPZ (by rw [hPP]; exact hPZ')
        have hMemP : MemS D Pp := (memS_embPair_inv hD (hWeq ▸ hW)).1
        exact ⟨hW, memS_inter hD hZ hZ' hMemP hPsub, Or.inr ⟨Pp, Qq, hWeq, hPsub⟩⟩
  mono := by
    rintro W W' Z Z' ⟨hW, hZ, hd⟩ hW'W hZZ' hW'mem hZ'mem
    refine ⟨hW'mem, hZ'mem, ?_⟩
    rcases hd with rfl | ⟨Pp, Qq, hWeq, hPZ⟩
    · exact Or.inl (Set.Subset.antisymm (memS_subset_gamma hZ'mem) hZZ')
    · subst hWeq
      cases hW'mem with
      | gamma =>
        exact absurd (Set.Subset.antisymm (memS_subset_gamma hW) hW'W)
          (embPair_ne_Gamma D hD Pp Qq)
      | @zero X hX =>
        exfalso
        obtain ⟨a, ha⟩ := hD X hX
        rcases hW'W (show (([], a) : List Bool × α) ∈ embZero X from ⟨rfl, ha⟩) with
          ⟨p', hp', -⟩ | ⟨q', hq', -⟩
        · simp at hp'
        · simp at hq'
      | @pair Pp' Qq' hP' hQ' =>
        obtain ⟨hP'P, -⟩ := embPair_subset.mp hW'W
        exact Or.inr ⟨Pp', Qq', rfl, fun z hz => hZZ' (hPZ (hP'P hz))⟩

@[simp] theorem proj0Map_rel {W Z : Set (List Bool × α)} :
    (proj0Map hD).rel W Z ↔
      MemS D W ∧ MemS D Z ∧ (Z = Gamma D ∨ ∃ Pp Qq, W = embPair Pp Qq ∧ Pp ⊆ Z) := Iff.rfl

/-- **`proj0Map` really is the first projection of the pair part:** `proj₀(⟨x, y⟩^§) = x`. -/
theorem proj0_toElementMap_pairSharp (x y : (Dsharp D hD).Element) :
    (proj0Map hD).toElementMap (pairSharp D hD x y) = x := by
  apply Element.ext
  intro Z
  simp only [ApproximableMap.mem_toElementMap, proj0Map_rel]
  constructor
  · rintro ⟨W, hWmem, hMW, hMZ, hdisj⟩
    rcases hWmem with rfl | ⟨Pp, Qq, hxP, hyQ, rfl⟩
    · rcases hdisj with rfl | ⟨Pp', Qq', hPe, -⟩
      · exact x.master_mem
      · exact absurd hPe.symm (embPair_ne_Gamma D hD Pp' Qq')
    · rcases hdisj with rfl | ⟨Pp', Qq', hPe, hP'Z⟩
      · exact x.master_mem
      · obtain ⟨hPP, -⟩ := embPair_injective hPe
        exact x.up_mem hxP hMZ (by rw [hPP]; exact hP'Z)
  · intro hxZ
    exact ⟨embPair Z (Gamma D), Or.inr ⟨Z, Gamma D, hxZ, y.master_mem, rfl⟩,
      MemS.pair (x.sub hxZ) MemS.gamma, x.sub hxZ, Or.inr ⟨Z, Gamma D, rfl, subset_rfl⟩⟩

/-- The index characterization of `proj0Map` against the `Vsharp` enumeration. `V_m proj₀ V_k` iff
`k = 0` (`V_k = Γ`) or `m` is an even node index `2a+2` with `V_{p a} ⊆ V_k` (the left child). -/
theorem proj0_rel_Vsharp_iff (P : ComputablePresentation D) (m k : ℕ) :
    (proj0Map hD).rel (Vsharp D P m) (Vsharp D P k) ↔
      k = 0 ∨ (m % 2 = 0 ∧ m ≠ 0 ∧ Vsharp D P (m / 2 - 1).unpair.1 ⊆ Vsharp D P k) := by
  rw [proj0Map_rel, and_iff_right (Vsharp_mem P m), and_iff_right (Vsharp_mem P k)]
  refine or_congr (Vsharp_eq_Gamma_iff P hD k) ?_
  rcases nat_shape m with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [Vsharp_zero]
    constructor
    · rintro ⟨Pp, Qq, heq, -⟩; exact absurd heq.symm (embPair_ne_Gamma D hD Pp Qq)
    · rintro ⟨-, hne, -⟩; exact absurd rfl hne
  · rw [Vsharp_odd]
    constructor
    · rintro ⟨Pp, Qq, heq, -⟩; exact absurd heq (embZero_ne_embPair D hD (P.mem_X a) Pp Qq)
    · rintro ⟨hmod, -, -⟩; exact absurd hmod (by omega)
  · rw [Vsharp_even, show (2 * a + 2) / 2 - 1 = a from by omega]
    constructor
    · rintro ⟨Pp, Qq, heq, hPk⟩
      obtain ⟨hP, -⟩ := embPair_injective heq
      exact ⟨by omega, by omega, by rw [hP]; exact hPk⟩
    · rintro ⟨-, -, hsub⟩
      exact ⟨Vsharp D P a.unpair.1, Vsharp D P a.unpair.2, rfl, hsub⟩

/-- **Proposition 7.7 (Scott 1981, PRG-19) — `proj₀` is computable.**
`V_m proj₀ V_k ↔ k = 0 ∨ (m even, m ≠ 0, V_{p(m/2-1)} ⊆ V_k)`: a disjunction of the equality and
inclusion deciders with primitive-recursive parity/child reindexings, hence r.e. -/
theorem proj0_isComputable (P : ComputablePresentation D) :
    IsComputableMap (dsharpPresentation P hD) (dsharpPresentation P hD) (proj0Map hD) := by
  show REPred (fun s => (proj0Map hD).rel (Vsharp D P s.unpair.1) (Vsharp D P s.unpair.2))
  have hk0 : RecDecidable (fun s => s.unpair.2 = 0) :=
    RecDecidable.natEq Nat.Primrec.right (Nat.Primrec.const 0)
  have hmod : RecDecidable (fun s => s.unpair.1 % 2 = 0) :=
    RecDecidable.natEq (primrec_mod2.comp Nat.Primrec.left) (Nat.Primrec.const 0)
  have hne : RecDecidable (fun s => s.unpair.1 ≠ 0) :=
    (RecDecidable.natEq Nat.Primrec.left (Nat.Primrec.const 0)).not
  have hg : Nat.Primrec (fun s => Nat.pair (s.unpair.1 / 2 - 1).unpair.1 s.unpair.2) :=
    (Nat.Primrec.left.comp (primrec_sub₂ (primrec_div2.comp Nat.Primrec.left)
      (Nat.Primrec.const 1))).pair Nat.Primrec.right
  have hincl : RecDecidable (fun s => Vsharp D P (s.unpair.1 / 2 - 1).unpair.1 ⊆
      Vsharp D P s.unpair.2) := by
    refine RecDecidable.of_iff (fun s => ?_) ((dsharpPresentation P hD).incl_computable.comp hg)
    simp only [dsharpPresentation_X, unpair_pair_fst, unpair_pair_snd]
  exact (RecDecidable.of_iff (fun s => proj0_rel_Vsharp_iff hD P s.unpair.1 s.unpair.2)
    (hk0.or (hmod.and (hne.and hincl)))).re

end Proposition77

end Scott1980.Neighborhood

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Theorem75
import Scott1980.Neighborhood.Table55

/-!
# Exercise 7.16 (Scott 1981, PRG-19, §7) — `curry` as a neighbourhood relation

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VII.

> **Exercise 7.16.** Let `D₀ = {Xₙ}`, `D₁ = {Yₘ}` and `D₂ = {Zₖ}` be three effectively given domains.
> Complete the proof of 7.5 by writing out `curry` as a relation between neighbourhoods. Is it a
> recursive set or only a recursively enumerable set?

Theorem 7.5 (`Theorem75.lean`) states that `eval` and `curry` are *computable* combinators. Scott
writes out `eval` explicitly and shows its neighbourhood relation is a **recursive** (decidable) set;
he leaves `curry` "to the exercises". This file completes that: it writes out the `curry`
**combinator**

  `curry : (𝒟₀ × 𝒟₁ → 𝒟₂) → (𝒟₀ → (𝒟₁ → 𝒟₂))`

as an approximable mapping between the two function-space domains, gives its neighbourhood relation,
and shows that relation is **recursive** (a recursively *decidable* set), not merely r.e. — exactly as
for `eval`.

## The combinator and its neighbourhood relation

`curry` (Theorem 3.12, `FunctionSpace.curry`) is the function on *maps* `g ↦ curry g`. As Scott's
Theorem 3.12 shows, it is an order-isomorphism `|𝒟₀×𝒟₁→𝒟₂| ≃ |𝒟₀→(𝒟₁→𝒟₂)|`, so by Theorem 2.7
(`ofIso`) it itself comes from an approximable mapping between the function-space domains — already
built as `curryC V₀ V₁ V₂` in `Table55.lean` (with faithfulness `curryC_toApproxMap`). We reuse it
and **write out** its neighbourhood relation (`curryComb_rel`):

  `G curryC H  ⟺  G, H neighbourhoods and ∀ g ∈ G, curry g ∈ H`,

which, unfolded to the explicit step-entries of the two presentations, reads:

  `G curryC H  ⟺  for every entry `[Xₗ, Wₗ]` of `H` and every step `[Yₗᵢ, Zₗᵢ]` of `Wₗ`,
                       G ⊆ [⟨Xₗ, Yₗᵢ⟩, Zₗᵢ]`.

Each `G ⊆ [⟨Xₗ,Yₗᵢ⟩,Zₗᵢ]` is **function-space inclusion** in `(𝒟₀×𝒟₁→𝒟₂)`, which is recursively
*decidable* (`ComputablePresentation.incl_computable`), and the surrounding quantifier is a *bounded*
`∀` over the coded entry-lists. Hence the relation is **recursive** — the answer to Scott's question.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-! ### The `curry` combinator as an approximable mapping (Theorem 2.7 / Theorem 3.12).

The combinator `curry : (𝒟₀×𝒟₁→𝒟₂) → (𝒟₀→(𝒟₁→𝒟₂))` is already built in `Table55.lean` as
`curryC V₀ V₁ V₂ = ofIso (curryIso V₀ V₁ V₂)` (Theorem 2.7 applied to Theorem 3.12's order-iso
`curryIso`), with faithfulness `curryC_toApproxMap`. We reuse it and write out its neighbourhood
relation. -/

/-- `curryIso V₀ V₁ V₂` sends a filter `x` to the filter of the curried least map (by definition). -/
theorem curryIso_apply (x : (funSpace (prod V₀ V₁) V₂).Element) :
    curryIso V₀ V₁ V₂ x = toFilter (curry (toApproxMap x)) := rfl

/-! ### Writing out `curry` as a relation between neighbourhoods. -/

/-- The least map of a function-space neighbourhood `G` — `toApproxMap ↑G` — belongs to `G`. -/
theorem toApproxMap_principal_mem {G : Set (ApproximableMap V₀ V₁)}
    (hG : (funSpace V₀ V₁).mem G) : toApproxMap ((funSpace V₀ V₁).principal hG) ∈ G := by
  obtain ⟨L, hL, rfl⟩ := hG.1
  intro p hp
  show (toApproxMap ((funSpace V₀ V₁).principal hG)).rel p.1 p.2
  rw [toApproxMap_rel, mem_principal]
  exact ⟨step_mem (hL p hp).1 (hL p hp).2, fun f hf => hf p hp⟩

/-- **Exercise 7.16 — `curry` written out as a relation between neighbourhoods.** The combinator
relates a neighbourhood `G` of `(𝒟₀×𝒟₁→𝒟₂)` to a neighbourhood `H` of `(𝒟₀→(𝒟₁→𝒟₂))` exactly when
`curry g ∈ H` for every `g ∈ G`. -/
theorem curryComb_rel {G : Set (ApproximableMap (prod V₀ V₁) V₂)}
    {H : Set (ApproximableMap V₀ (funSpace V₁ V₂))} :
    (curryC V₀ V₁ V₂).rel G H ↔ (funSpace (prod V₀ V₁) V₂).mem G ∧
      (funSpace V₀ (funSpace V₁ V₂)).mem H ∧ ∀ g ∈ G, curry g ∈ H := by
  constructor
  · rintro ⟨hG, hH⟩
    rw [curryIso_apply, mem_toFilter] at hH
    obtain ⟨hHmem, hcurry⟩ := hH
    refine ⟨hG, hHmem, fun g hg => ?_⟩
    have hle : toApproxMap ((funSpace (prod V₀ V₁) V₂).principal hG) ≤ g := by
      rw [ApproximableMap.le_iff]
      intro X Y hrel
      rw [toApproxMap_rel, mem_principal] at hrel
      exact hrel.2 hg
    have hcle : curry (toApproxMap ((funSpace (prod V₀ V₁) V₂).principal hG)) ≤ curry g :=
      (curryEquiv V₀ V₁ V₂).monotone hle
    exact funSpace_mem_up_closed hHmem hcurry hcle
  · rintro ⟨hG, hH, hall⟩
    refine ⟨hG, ?_⟩
    rw [curryIso_apply, mem_toFilter]
    exact ⟨hH, hall _ (toApproxMap_principal_mem hG)⟩

/-! ### Recursive (not merely r.e.): the combinator's neighbourhood relation is decidable.

Following the structure of `eval` (Milestone 7 of `Theorem75.lean`, where Scott observes `eval` is a
*recursive* set), we show that `curry` — read off the explicit step-entries of the two presentations —
is a **recursively decidable** relation between codes. The crux: each clause `G ⊆ [⟨Xₗ,Yₗᵢ⟩,Zₗᵢ]` is
function-space inclusion in `(𝒟₀×𝒟₁→𝒟₂)`, recursively *decidable* via `incl_computable`; the step
`[⟨Xₗ,Yₗᵢ⟩,Zₗᵢ]` is a one-entry function-space neighbourhood (`Xenum_singleton`); the surrounding
quantifiers are *bounded* `∀`s over the coded entry-lists (`RecDecidable₂.bForallList`). -/

/-- The code of the one-entry function-space neighbourhood `[⟨X_{e.1}, X_{e'.1}⟩, X_{e'.2}]` of
`(𝒟₀×𝒟₁→𝒟₂)` (a `Xenum`-singleton over the product presentation). -/
def curryStepCode (a e' : ℕ) : ℕ :=
  Nat.pair (Nat.pair (Nat.pair a e'.unpair.1) e'.unpair.2) 0 + 1

theorem primrec_curryStepCode {a e : ℕ → ℕ} (ha : Nat.Primrec a) (he : Nat.Primrec e) :
    Nat.Primrec (fun w => curryStepCode (a w) (e w)) := by
  have h1 : Nat.Primrec (fun w => (e w).unpair.1) := Nat.Primrec.left.comp he
  have h2 : Nat.Primrec (fun w => (e w).unpair.2) := Nat.Primrec.right.comp he
  refine (Nat.Primrec.succ.comp (((ha.pair h1).pair h2).pair (Nat.Primrec.const 0))).of_eq
    (fun w => ?_)
  rfl

/-- **Exercise 7.16 — `curry` is a *recursive* set.** Relative to the function-space presentations
`PA` of `(𝒟₀×𝒟₁→𝒟₂)` and `PB` of `(𝒟₀→(𝒟₁→𝒟₂))` (and the inner one `Pc` of `(𝒟₁→𝒟₂)`) built by
Theorem 7.5, the `curry` combinator's neighbourhood relation is **recursively decidable**:

  `Xenum_PA n curryComb Xenum_PB m  ⟺  gNb m = 1 → ∀ e ∈ ⟦m⟧, gNc e₂ = 1 →
                                          ∀ e' ∈ ⟦e₂⟧, X_PA n ⊆ X_PA (curryStepCode e₁ e')`,

a bounded double-`∀` over the coded entry-lists of the recursively *decidable* function-space
inclusion. So `curry` is a recursive set — exactly as for `eval`. -/
theorem curryComb_rel_recDecidable
    (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)
    (P₂ : ComputablePresentation V₂) (gNa gNb gNc : ℕ → ℕ)
    (PA : ComputablePresentation (funSpace (prod V₀ V₁) V₂))
    (PB : ComputablePresentation (funSpace V₀ (funSpace V₁ V₂)))
    (Pc : ComputablePresentation (funSpace V₁ V₂))
    (hPAX : PA.X = Xenum (prodPresentation P₀ P₁) P₂ gNa)
    (hPBX : PB.X = Xenum P₀ Pc gNb)
    (hPcX : Pc.X = Xenum P₁ P₂ gNc)
    (hgNa : ∀ c, gNa c = 1 ↔
      (stepFun (funListOf (prodPresentation P₀ P₁) P₂ (decodeList c))
        : Set (ApproximableMap (prod V₀ V₁) V₂)).Nonempty)
    (hgNc : ∀ c, gNc c = 1 ↔
      (stepFun (funListOf P₁ P₂ (decodeList c)) : Set (ApproximableMap V₁ V₂)).Nonempty)
    (hgNbp : Nat.Primrec gNb) (hgNcp : Nat.Primrec gNc) :
    RecDecidable₂ (fun n m => (curryC V₀ V₁ V₂).rel (PA.X n) (PB.X m)) := by
  -- The explicit neighbourhood relation, written out over the coded entries.
  have hcomb : ∀ n m, (curryC V₀ V₁ V₂).rel (PA.X n) (PB.X m) ↔
      (gNb m = 1 → ∀ e ∈ decodeList m, gNc e.unpair.2 = 1 →
        ∀ e' ∈ decodeList e.unpair.2, PA.X n ⊆ PA.X (curryStepCode e.unpair.1 e')) := by
    intro n m
    have hstep1 : (curryC V₀ V₁ V₂).rel (PA.X n) (PB.X m) ↔
        curry (toApproxMap ((funSpace (prod V₀ V₁) V₂).principal (PA.mem_X n))) ∈ PB.X m := by
      constructor
      · rintro ⟨hG, hH⟩
        rw [curryIso_apply, mem_toFilter] at hH
        exact hH.2
      · intro h
        exact ⟨PA.mem_X n, by rw [curryIso_apply, mem_toFilter]; exact ⟨PB.mem_X m, h⟩⟩
    rw [hstep1, hPBX, mem_Xenum_iff_map P₀ Pc gNb
      (curry (toApproxMap ((funSpace (prod V₀ V₁) V₂).principal (PA.mem_X n)))) m]
    apply imp_congr_right; intro _
    apply forall_congr'; intro e
    apply imp_congr_right; intro _
    rw [hPcX, curry_rel_Xenum_iff P₀ P₁ P₂ gNc hgNc
      (toApproxMap ((funSpace (prod V₀ V₁) V₂).principal (PA.mem_X n))) e.unpair.1 e.unpair.2]
    apply imp_congr_right; intro _
    apply forall_congr'; intro e'
    apply imp_congr_right; intro _
    have hstepeq : step (prodNbhd (P₀.X e.unpair.1) (P₁.X e'.unpair.1)) (P₂.X e'.unpair.2)
        = PA.X (curryStepCode e.unpair.1 e') := by
      have hs := Xenum_singleton (prodPresentation P₀ P₁) P₂ gNa hgNa
        (Nat.pair e.unpair.1 e'.unpair.1) e'.unpair.2
      rw [prodPresentation_X, unpair_pair_fst, unpair_pair_snd] at hs
      rw [hPAX]; exact hs.symm
    rw [toApproxMap_rel, mem_principal, hstepeq]
    exact ⟨fun h => h.2, fun h => ⟨PA.mem_X _, h⟩⟩
  -- The right-hand side is recursively decidable.
  have q1_dec : RecDecidable₂ (fun e' p =>
      PA.X p.unpair.1 ⊆ PA.X (curryStepCode p.unpair.2 e')) := by
    have hr : Nat.Primrec (fun w => Nat.pair w.unpair.2.unpair.1
        (curryStepCode w.unpair.2.unpair.2 w.unpair.1)) :=
      (Nat.Primrec.left.comp Nat.Primrec.right).pair
        (primrec_curryStepCode (Nat.Primrec.right.comp Nat.Primrec.right) Nat.Primrec.left)
    refine RecDecidable.of_iff (fun w => ?_) (RecDecidable.comp PA.incl_computable hr)
    simp only [unpair_pair_fst, unpair_pair_snd]
  have dInner := q1_dec.bForallList
  have dMid : RecDecidable₂ (fun e n =>
      gNc e.unpair.2 = 1 → ∀ e' ∈ decodeList e.unpair.2,
        PA.X n ⊆ PA.X (curryStepCode e.unpair.1 e')) := by
    have hg_mid : Nat.Primrec (fun s => Nat.pair s.unpair.1.unpair.2
        (Nat.pair s.unpair.2 s.unpair.1.unpair.1)) :=
      (Nat.Primrec.right.comp Nat.Primrec.left).pair
        (Nat.Primrec.right.pair (Nat.Primrec.left.comp Nat.Primrec.left))
    have B1 : RecDecidable (fun s => ∀ e' ∈ decodeList s.unpair.1.unpair.2,
        PA.X s.unpair.2 ⊆ PA.X (curryStepCode s.unpair.1.unpair.1 e')) := by
      refine RecDecidable.of_iff (fun s => ?_) (RecDecidable.comp dInner hg_mid)
      simp only [unpair_pair_fst, unpair_pair_snd]
    have guard1 : RecDecidable (fun s => gNc s.unpair.1.unpair.2 = 1) :=
      RecDecidable.natEq (hgNcp.comp (Nat.Primrec.right.comp Nat.Primrec.left))
        (Nat.Primrec.const 1)
    refine RecDecidable.of_iff (fun s => ?_) (guard1.not.or B1)
    exact Decidable.imp_iff_not_or
  have dOuter := dMid.bForallList
  refine RecDecidable.of_iff (fun t => hcomb t.unpair.1 t.unpair.2) ?_
  have hswap2 : Nat.Primrec (fun t => Nat.pair t.unpair.2 t.unpair.1) :=
    Nat.Primrec.right.pair Nat.Primrec.left
  have B2 : RecDecidable (fun t => ∀ e ∈ decodeList t.unpair.2, gNc e.unpair.2 = 1 →
      ∀ e' ∈ decodeList e.unpair.2, PA.X t.unpair.1 ⊆ PA.X (curryStepCode e.unpair.1 e')) := by
    refine RecDecidable.of_iff (fun t => ?_) (RecDecidable.comp dOuter hswap2)
    simp only [unpair_pair_fst, unpair_pair_snd]
  have guard2 : RecDecidable (fun t => gNb t.unpair.2 = 1) :=
    RecDecidable.natEq (hgNbp.comp Nat.Primrec.right) (Nat.Primrec.const 1)
  refine RecDecidable.of_iff (fun t => ?_) (guard2.not.or B2)
  exact Decidable.imp_iff_not_or

/-- **Exercise 7.16 — `curry` is computable, and in fact a recursive set.** If `𝒟₀, 𝒟₁, 𝒟₂` are
effectively given, then there are computable presentations of `(𝒟₀×𝒟₁→𝒟₂)` and `(𝒟₀→(𝒟₁→𝒟₂))`
relative to which the `curry` combinator's neighbourhood relation is **recursively decidable**
(`RecDecidable₂`) — hence `curry` is a computable map (`IsComputableMap`, the r.e. condition of
Definition 7.2). The answer to Scott's question: `curry` is a *recursive* set, not merely r.e. -/
theorem curryComb_isComputable
    (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)
    (P₂ : ComputablePresentation V₂) :
    ∃ (PA : ComputablePresentation (funSpace (prod V₀ V₁) V₂))
      (PB : ComputablePresentation (funSpace V₀ (funSpace V₁ V₂))),
      RecDecidable₂ (fun n m => (curryC V₀ V₁ V₂).rel (PA.X n) (PB.X m)) ∧
        IsComputableMap PA PB (curryC V₀ V₁ V₂) := by
  obtain ⟨incl0, hincl0p, hincl0s⟩ := P₀.incl_computable
  obtain ⟨fc0, hfc0p, hfc0s⟩ := P₀.cons_computable
  obtain ⟨incl1, hincl1p, hincl1s⟩ := P₁.incl_computable
  obtain ⟨fc1, hfc1p, hfc1s⟩ := P₁.cons_computable
  obtain ⟨incl2, hincl2p, hincl2s⟩ := P₂.incl_computable
  obtain ⟨eq2, heq2p, heq2s⟩ := P₂.eq_computable
  obtain ⟨fc2, hfc2p, hfc2s⟩ := P₂.cons_computable
  obtain ⟨inclpr, hinclprp, hinclprs⟩ := (prodPresentation P₀ P₁).incl_computable
  obtain ⟨fcpr, hfcprp, hfcprs⟩ := (prodPresentation P₀ P₁).cons_computable
  -- inner function space `Pc = (𝒟₁ → 𝒟₂)`
  let Pc : ComputablePresentation (funSpace V₁ V₂) :=
    funPresentation P₁ P₂ (funConsChar P₁ P₂ fc1 fc2) incl1 incl2 eq2
      (funConsChar_spec P₁ P₂ fc1 fc2 (fun s => (hfc1s s).symm) (fun s => (hfc2s s).symm))
      (primrec_funConsChar P₁ P₂ fc1 fc2 hfc1p hfc2p)
      (fun s => (hincl1s s).symm) hincl1p (fun s => (hincl2s s).symm) hincl2p
      (fun s => (heq2s s).symm) heq2p
  obtain ⟨inclc, hinclcp, hinclcs⟩ := Pc.incl_computable
  obtain ⟨eqc, heqcp, heqcs⟩ := Pc.eq_computable
  obtain ⟨fcc, hfccp, hfccs⟩ := Pc.cons_computable
  -- domain function space `PA = (𝒟₀×𝒟₁ → 𝒟₂)`
  let PA : ComputablePresentation (funSpace (prod V₀ V₁) V₂) :=
    funPresentation (prodPresentation P₀ P₁) P₂
      (funConsChar (prodPresentation P₀ P₁) P₂ fcpr fc2) inclpr incl2 eq2
      (funConsChar_spec (prodPresentation P₀ P₁) P₂ fcpr fc2
        (fun s => (hfcprs s).symm) (fun s => (hfc2s s).symm))
      (primrec_funConsChar (prodPresentation P₀ P₁) P₂ fcpr fc2 hfcprp hfc2p)
      (fun s => (hinclprs s).symm) hinclprp (fun s => (hincl2s s).symm) hincl2p
      (fun s => (heq2s s).symm) heq2p
  -- codomain function space `PB = (𝒟₀ → (𝒟₁ → 𝒟₂))`
  let PB : ComputablePresentation (funSpace V₀ (funSpace V₁ V₂)) :=
    funPresentation P₀ Pc (funConsChar P₀ Pc fc0 fcc) incl0 inclc eqc
      (funConsChar_spec P₀ Pc fc0 fcc (fun s => (hfc0s s).symm) (fun s => (hfccs s).symm))
      (primrec_funConsChar P₀ Pc fc0 fcc hfc0p hfccp)
      (fun s => (hincl0s s).symm) hincl0p (fun s => (hinclcs s).symm) hinclcp
      (fun s => (heqcs s).symm) heqcp
  have hRec : RecDecidable₂ (fun n m => (curryC V₀ V₁ V₂).rel (PA.X n) (PB.X m)) :=
    curryComb_rel_recDecidable P₀ P₁ P₂
      (funConsChar (prodPresentation P₀ P₁) P₂ fcpr fc2) (funConsChar P₀ Pc fc0 fcc)
      (funConsChar P₁ P₂ fc1 fc2) PA PB Pc rfl rfl rfl
      (funConsChar_spec (prodPresentation P₀ P₁) P₂ fcpr fc2
        (fun s => (hfcprs s).symm) (fun s => (hfc2s s).symm))
      (funConsChar_spec P₁ P₂ fc1 fc2 (fun s => (hfc1s s).symm) (fun s => (hfc2s s).symm))
      (primrec_funConsChar P₀ Pc fc0 fcc hfc0p hfccp)
      (primrec_funConsChar P₁ P₂ fc1 fc2 hfc1p hfc2p)
  exact ⟨PA, PB, hRec, hRec.re⟩

end Scott1980.Neighborhood

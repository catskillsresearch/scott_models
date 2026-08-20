/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Exercise719
import Scott1980.Neighborhood.FunctionSpace

/-!
# Exercise 7.21 (Scott 1981, PRG-19, §7) — combinators on the power domain

> **EXERCISE 7.21.** Is there a non-trivial combinator of type `ℙ(D → E) → (ℙD → ℙE)`?
> Are there in general any isomorphisms between the systems `(D → ℙE)`, `ℙ(D × E)`, `ℙD × ℙE`?
> Is there a non-trivial combinator of type `ℙ(D × E) × ℙ(E × F) → ℙ(D × F)`?
> Is there any connection between `ℙN` and `PN`?

This file answers the **first (headline) question with a full construction** and discusses the rest.

## The headline combinator `papply : ℙ(D → E) → (ℙD → ℙE)`

A `ℙ(D→E)`-neighbourhood `Φ` is a finite union of down-sets of *function-space* neighbourhoods; a
`ℙD`-neighbourhood `A` is a finite union of down-sets of `D`-neighbourhoods. The natural — and
non-trivial — combinator "applies a set of functions to a set of arguments" by collecting all the
applications. It is exactly the **Smyth power-domain lift of evaluation** (Theorem 3.11's
`eval : (D→E) × D → E`):

`papplyEval.rel Φ A B  :=  Φ ∈ ℙ(D→E) ∧ A ∈ ℙD ∧ B ∈ ℙE ∧ ∀ G ∈ Φ, ∀ X ∈ A, ∃ Y ∈ B, G, X eval Y`,

the two-variable analogue of Exercise 7.19's `ℙf` (one level: `∀ X ∈ A, ∃ Y ∈ B, X f Y`) and of
Exercise 7.20's `union` (the nested `∀ ∀ ∃`). Packaged as the two-variable map `papplyEval`, made a
map out of the product `papplyB = ofMap₂ papplyEval : ℙ(D→E) × ℙD → ℙE`, and finally **curried**
(Theorem 3.12) to the *exact* type Scott asks for:

`papply = curry papplyB : ℙ(D→E) → (ℙD → ℙE)`.

It is **non-trivial**: `papplyEval_step_witness` exhibits, for any neighbourhoods `X₀ ∈ D`, `Y₀ ∈ E`,
the relation `↓[X₀,Y₀]  papply  ↓X₀ ↦ ↓Y₀` — the set of functions sending (at least) `X₀` to `Y₀`,
applied to (at least) `X₀`, yields (at least) `Y₀`. (Compare Exercise 7.19's image action
`ℙf({x,y}) = {f x, f x'}` — here the function is itself drawn from a power domain.)

## Computability (the implicit "if `D`, `E` effectively given" half)

*Yes, `papply` is computable whenever `eval` is.* Over the canonical presentations of Proposition
7.10 (`ℙ𝒟`-codes = finite lists of indices), the relation reduces (`papplyEval_rel_Ypd_iff`) to the
triply-nested bounded quantifier

`∀ g ∈ dl Φc, ∀ x ∈ dl Ac, ∃ y ∈ dl Bc, eval (Pf.X g) (P.X x) (Q.X y)`,

recursively enumerable (`papplyEval_isComputable`) because each layer preserves r.e.-ness: bounded
`∃` (`bExists_decodeList_re`, Ex 7.19) and parameterised bounded `∀`
(`REPred.forall_mem_decodeList₂`), assembled by the helper `re_forallG_forallX_existsY`. The base
predicate "`eval` is r.e. on codes" is precisely Theorem 7.5's `evalMap_isComputable` (transported to
the ternary relation through the function-space presentation `funPresentation`), so we take it as the
hypothesis `heval` — exactly as Exercise 7.19/7.20 take the component presentations as inputs.

## The other three questions (discussion)

* **Isomorphisms among `(D → ℙE)`, `ℙ(D × E)`, `ℙD × ℙE`?** *Not in general.* There are always
  canonical *maps* — e.g. `⟨ℙp₀, ℙp₁⟩ : ℙ(D×E) → ℙD × ℙE` (the Ex-7.19 functorial action of the two
  projections, paired) and a "graph/strength" map `D → ℙE` ↦ `ℙ(D×E)`-style — but none is an
  isomorphism for non-degenerate `D, E`. The Smyth power domain does **not** distribute over the
  product: `ℙ(D×E)` records *correlated* sets of pairs `{(d,e)}`, whereas `ℙD × ℙE` only records the
  two *marginals*; the map `ℙ(D×E) → ℙD × ℙE` forgets the correlation and is not injective on
  elements (e.g. `{(d₁,e₁),(d₂,e₂)}` and `{(d₁,e₂),(d₂,e₁)}` have the same marginals). Likewise
  `(D → ℙE)` (one set of outputs *per input*) carries strictly more information than a single
  `ℙ(D×E)`. So these are related by combinators, not isomorphisms, in general.
* **A combinator `ℙ(D × E) × ℙ(E × F) → ℙ(D × F)`?** *Yes* — **relational composition**, the Smyth
  lift of "compose the underlying relations": send sets `R ⊆ D×E`, `S ⊆ E×F` to
  `R ; S = {(d,f) ∣ ∃ e, (d,e) ∈ R ∧ (e,f) ∈ S}`. On neighbourhoods, `prodNbhd X Y ∈ R̄`,
  `prodNbhd Y' Z ∈ S̄` with `Y, Y'` consistent produce `prodNbhd X Z`; the middle witness `Y ∩ Y'`
  is gathered exactly as Exercise 7.19's choice-free `comp_witness`. It is the same recipe as
  `papply` (a binary Smyth lift), so "yes, and computable", and is not pursued in code here.
* **Connection between `ℙN` and `PN`?** Here `N` is the flat domain of naturals (Lecture VII's `𝒟 = N`)
  and `PN` is the powerset domain `𝒫(ℕ)` of Example 7.8. The Smyth power domain `ℙN` consists of the
  *finitely generated Smyth predicates* on `N`; its finite elements are finite sets of naturals
  (plus `⊥`), and the embedding "finite set ↦ its set of members" realises `ℙN` as the sub-domain of
  `PN` of finitely generated elements — `ℙN ⊴ PN` (Proposition 7.12's singleton/union machinery),
  with `PN` the ideal completion. They are *not* isomorphic (`PN` has uncountable elements, `ℙN`'s
  elements are the r.e./finite ones), but `ℙN` sits inside `PN` as its computable/finitary core.

## Axiom audit

As in Exercises 7.19/7.20, every declaration carries `Classical.choice`, but only at the `Prop` level
and only *inherited* from the power domain itself (Proposition 7.10's `PDmem_upSet_inter` `by_cases`,
used to build `PowerDomain`). The new content here — `papplyEval`, the displayed reduction, the r.e.
helper, and the curried combinator — adds **no further** use of choice; the recursion layer of
`Recursive.lean` is choice-free.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

/-! ### The combinator `papply` as the Smyth power-domain lift of `eval`. -/

/-- **Exercise 7.21 — the two-variable combinator `papplyEval : ℙ(D→E) × ℙD → ℙE`.** The Smyth
power-domain lift of evaluation (Theorem 3.11): a `ℙ(D→E)`-neighbourhood `Φ` applied to a
`ℙD`-neighbourhood `A` covers a `ℙE`-neighbourhood `B` iff every function-neighbourhood `G ∈ Φ`
applied to every argument-neighbourhood `X ∈ A` lands in some `Y ∈ B` (via `eval`, i.e. every
`f ∈ G` sends `X` into `Y`). This is the two-variable analogue of Exercise 7.19's `ℙf`. -/
def papplyEval (V : NeighborhoodSystem α) (W : NeighborhoodSystem β) :
    ApproximableMap₂ (funSpace V W).PowerDomain V.PowerDomain W.PowerDomain where
  rel Φ A B := (funSpace V W).PDmem Φ ∧ V.PDmem A ∧ W.PDmem B ∧
    ∀ G ∈ Φ, ∀ X ∈ A, ∃ Y ∈ B, (eval V W).rel G X Y
  rel_dom₀ h := h.1
  rel_dom₁ h := h.2.1
  rel_cod h := h.2.2.1
  master_rel := by
    refine ⟨(funSpace V W).PDmem_master, V.PDmem_master, W.PDmem_master, ?_⟩
    intro G hG X hX
    simp only [PowerDomain_master, mem_upSet] at hG hX
    refine ⟨W.master, ⟨W.master_mem, subset_rfl⟩, ?_⟩
    exact ⟨hG.1, hX.1, W.master_mem,
      fun f hf => f.mono f.master_rel (V.sub_master hX.1) subset_rfl hX.1 W.master_mem⟩
  inter_right := by
    rintro Φ A B B' ⟨hΦ, hA, hB, hbody⟩ ⟨-, -, hB', hbody'⟩
    refine ⟨hΦ, hA, W.PDmem_inter hB hB', ?_⟩
    intro G hG X hX
    obtain ⟨Y, hYB, hrel⟩ := hbody G hG X hX
    obtain ⟨Y', hY'B', hrel'⟩ := hbody' G hG X hX
    have hinmem : W.mem (Y ∩ Y') := (eval V W).rel_cod ((eval V W).inter_right hrel hrel')
    exact ⟨Y ∩ Y', Set.mem_inter
      (W.PDmem_down hB hYB Set.inter_subset_left hinmem)
      (W.PDmem_down hB' hY'B' Set.inter_subset_right hinmem),
      (eval V W).inter_right hrel hrel'⟩
  mono := by
    rintro Φ Φ' A A' B B' ⟨_, _, _, hbody⟩ hΦ'Φ hA'A hBB' hΦ' hA' hB'
    refine ⟨hΦ', hA', hB', ?_⟩
    intro G hG X hX
    obtain ⟨Y, hYB, hrel⟩ := hbody G (hΦ'Φ hG) X (hA'A hX)
    exact ⟨Y, hBB' hYB, hrel⟩

@[simp] theorem papplyEval_rel {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    {Φ : Set (Set (ApproximableMap V W))} {A : Set (Set α)} {B : Set (Set β)} :
    (papplyEval V W).rel Φ A B ↔ (funSpace V W).PDmem Φ ∧ V.PDmem A ∧ W.PDmem B ∧
      ∀ G ∈ Φ, ∀ X ∈ A, ∃ Y ∈ B, (eval V W).rel G X Y := Iff.rfl

/-- **Exercise 7.21 — the combinator as a map out of the product `ℙ(D→E) × ℙD → ℙE`.** -/
def papplyB (V : NeighborhoodSystem α) (W : NeighborhoodSystem β) :
    ApproximableMap (prod (funSpace V W).PowerDomain V.PowerDomain) W.PowerDomain :=
  ofMap₂ (papplyEval V W)

/-- **Exercise 7.21 — the headline combinator `papply : ℙ(D→E) → (ℙD → ℙE)`.** Currying `papplyB`
(Theorem 3.12) gives the combinator of *exactly* the type Scott asks for. -/
def papply (V : NeighborhoodSystem α) (W : NeighborhoodSystem β) :
    ApproximableMap (funSpace V W).PowerDomain (funSpace V.PowerDomain W.PowerDomain) :=
  curry (papplyB V W)

/-- **Exercise 7.21 — non-triviality.** For any neighbourhoods `X₀ ∈ D`, `Y₀ ∈ E`, the set of
functions sending `X₀` into `Y₀` (the principal `ℙ(D→E)`-element `↓[X₀,Y₀]`), applied to the
argument-set `↓X₀`, covers `↓Y₀`. So `papply` does genuine work (it is not the constant map). -/
theorem papplyEval_step_witness {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    {X₀ : Set α} {Y₀ : Set β} (hX₀ : V.mem X₀) (hY₀ : W.mem Y₀) :
    (papplyEval V W).rel ((funSpace V W).upSet (step X₀ Y₀)) (V.upSet X₀) (W.upSet Y₀) := by
  refine ⟨(funSpace V W).PDmem_upSet (step_mem hX₀ hY₀), V.PDmem_upSet hX₀,
    W.PDmem_upSet hY₀, ?_⟩
  intro G hG X hX
  obtain ⟨hGmem, hGsub⟩ := hG
  obtain ⟨hXmem, hXsub⟩ := hX
  refine ⟨Y₀, ⟨hY₀, subset_rfl⟩, hGmem, hXmem, hY₀, ?_⟩
  intro f hf
  have hfstep : f.rel X₀ Y₀ := mem_step.mp (hGsub hf)
  exact f.mono hfstep hXsub subset_rfl hXmem hY₀

/-! ### Computability: `papply` is computable whenever `eval` is.

The base predicate "`eval` is recursively enumerable on codes" is Theorem 7.5's `evalMap_isComputable`
transported to the ternary `eval` relation; we take it as the hypothesis `heval`. -/

/-- **Three nested bounded quantifiers preserve recursive enumerability.** If `R` is r.e. (in the
paired form `R g x y`) then so is `∀ g ∈ dl w.1, ∀ x ∈ dl w.2.1, ∃ y ∈ dl w.2.2, R g x y`. Built from
the bounded-`∃` lemma `bExists_decodeList_re` (Exercise 7.19) and the parameterised bounded-`∀` lemma
`REPred.forall_mem_decodeList₂`, layered with primitive-recursive re-indexings. -/
theorem re_forallG_forallX_existsY {R : ℕ → ℕ → ℕ → Prop}
    (hR : REPred (fun s => R s.unpair.1 s.unpair.2.unpair.1 s.unpair.2.unpair.2)) :
    REPred (fun w => ∀ g ∈ decodeList w.unpair.1, ∀ x ∈ decodeList w.unpair.2.unpair.1,
      ∃ y ∈ decodeList w.unpair.2.unpair.2, R g x y) := by
  -- reindex `⟨g,x,y⟩ = ⟨s.1.1, s.1.2, s.2⟩` ↦ `⟨g,⟨x,y⟩⟩`
  have hm1 : Nat.Primrec (fun s : ℕ => Nat.pair s.unpair.1.unpair.1
      (Nat.pair s.unpair.1.unpair.2 s.unpair.2)) :=
    (Nat.Primrec.left.comp Nat.Primrec.left).pair
      ((Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right)
  have hR2 : REPred₂ (fun gx y => R gx.unpair.1 gx.unpair.2 y) := by
    show REPred (fun t => R t.unpair.1.unpair.1 t.unpair.1.unpair.2 t.unpair.2)
    refine REPred.of_iff (fun s => ?_) (hR.comp hm1)
    simp only [unpair_pair_fst, unpair_pair_snd]
  -- bounded `∃ y`
  have hE : REPred (fun u => ∃ b ∈ decodeList u.unpair.1,
      R u.unpair.2.unpair.1 u.unpair.2.unpair.2 b) := bExists_decodeList_re hR2
  -- bounded `∀ x` (parameters `⟨Bc, g⟩`)
  have hm2 : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1.unpair.1
      (Nat.pair t.unpair.1.unpair.2 t.unpair.2)) := hm1
  have hF : REPred₂ (fun param x => ∃ y ∈ decodeList param.unpair.1,
      R param.unpair.2 x y) := by
    show REPred (fun t => ∃ y ∈ decodeList t.unpair.1.unpair.1,
      R t.unpair.1.unpair.2 t.unpair.2 y)
    refine REPred.of_iff (fun t => ?_) (hE.comp hm2)
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hFfull : REPred (fun t => ∀ x ∈ decodeList t.unpair.2,
      ∃ y ∈ decodeList t.unpair.1.unpair.1, R t.unpair.1.unpair.2 x y) :=
    REPred.forall_mem_decodeList₂ hF
  -- bounded `∀ g` (parameters `⟨Bc, Ac⟩`)
  have hm3 : Nat.Primrec (fun t : ℕ => Nat.pair
      (Nat.pair t.unpair.1.unpair.1 t.unpair.2) t.unpair.1.unpair.2) :=
    ((Nat.Primrec.left.comp Nat.Primrec.left).pair Nat.Primrec.right).pair
      (Nat.Primrec.right.comp Nat.Primrec.left)
  have hG : REPred₂ (fun param g => ∀ x ∈ decodeList param.unpair.2,
      ∃ y ∈ decodeList param.unpair.1, R g x y) := by
    show REPred (fun t => ∀ x ∈ decodeList t.unpair.1.unpair.2,
      ∃ y ∈ decodeList t.unpair.1.unpair.1, R t.unpair.2 x y)
    refine REPred.of_iff (fun t => ?_) (hFfull.comp hm3)
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hGfull : REPred (fun t => ∀ g ∈ decodeList t.unpair.2,
      ∀ x ∈ decodeList t.unpair.1.unpair.2,
        ∃ y ∈ decodeList t.unpair.1.unpair.1, R g x y) :=
    REPred.forall_mem_decodeList₂ hG
  -- final reindex to `w = ⟨Φc, ⟨Ac, Bc⟩⟩`
  have hm4 : Nat.Primrec (fun w : ℕ => Nat.pair
      (Nat.pair w.unpair.2.unpair.2 w.unpair.2.unpair.1) w.unpair.1) :=
    ((Nat.Primrec.right.comp Nat.Primrec.right).pair
      (Nat.Primrec.left.comp Nat.Primrec.right)).pair Nat.Primrec.left
  refine REPred.of_iff (fun w => ?_) (hGfull.comp hm4)
  simp only [unpair_pair_fst, unpair_pair_snd]

/-- **Exercise 7.21 — `papply`'s relation at the level of `ℙ𝒟`-codes.** Over the canonical
presentations of Proposition 7.10 (function-space presentation `Pf`, domain `P`, codomain `Q`):
`papplyEval.rel (Y_Φc) (Y_Ac) (Y_Bc) ↔ ∀ g ∈ dl Φc, ∀ x ∈ dl Ac, ∃ y ∈ dl Bc, eval (Pf.X g)(P.X x)(Q.X y)`. -/
theorem papplyEval_rel_Ypd_iff {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (Pf : ComputablePresentation (funSpace V W)) (P : ComputablePresentation V)
    (Q : ComputablePresentation W) {Φc Ac Bc : ℕ} :
    (papplyEval V W).rel ((funSpace V W).Ypd Pf Φc) (V.Ypd P Ac) (W.Ypd Q Bc)
      ↔ ∀ g ∈ decodeList Φc, ∀ x ∈ decodeList Ac, ∃ y ∈ decodeList Bc,
          (eval V W).rel (Pf.X g) (P.X x) (Q.X y) := by
  constructor
  · rintro ⟨-, -, -, hbody⟩ g hg x hx
    have hGin : Pf.X g ∈ (funSpace V W).Ypd Pf Φc :=
      ((funSpace V W).mem_Ypd Pf).mpr ⟨g, hg, Pf.mem_X g, subset_rfl⟩
    have hXin : P.X x ∈ V.Ypd P Ac := (V.mem_Ypd P).mpr ⟨x, hx, P.mem_X x, subset_rfl⟩
    obtain ⟨Y, hYin, hrel⟩ := hbody (Pf.X g) hGin (P.X x) hXin
    obtain ⟨b, hb, hYmem, hYsub⟩ := (W.mem_Ypd Q).mp hYin
    exact ⟨b, hb, (eval V W).mono hrel subset_rfl subset_rfl hYsub
      ((eval V W).rel_dom₀ hrel) ((eval V W).rel_dom₁ hrel) (Q.mem_X b)⟩
  · intro hgen
    refine ⟨(funSpace V W).Ypd_isPDmem Pf Φc, V.Ypd_isPDmem P Ac, W.Ypd_isPDmem Q Bc, ?_⟩
    intro G hGin X hXin
    obtain ⟨g, hg, hGmem, hGsub⟩ := ((funSpace V W).mem_Ypd Pf).mp hGin
    obtain ⟨x, hx, hXmem, hXsub⟩ := (V.mem_Ypd P).mp hXin
    obtain ⟨y, hy, hrel⟩ := hgen g hg x hx
    exact ⟨Q.X y, (W.mem_Ypd Q).mpr ⟨y, hy, Q.mem_X y, subset_rfl⟩,
      (eval V W).mono hrel hGsub hXsub subset_rfl hGmem hXmem (Q.mem_X y)⟩

/-- **Exercise 7.21 (the computability half) — `papply` is computable when `eval` is.** Stated at the
level of the `ℙ𝒟`-codes of Proposition 7.10: given that `eval` is recursively enumerable on codes
(`heval` — this is Theorem 7.5's `evalMap_isComputable` transported through `funPresentation`), the
relation `papplyEval.rel (Y_Φc)(Y_Ac)(Y_Bc)` is recursively enumerable in `⟨Φc, Ac, Bc⟩`. -/
theorem papplyEval_isComputable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (Pf : ComputablePresentation (funSpace V W)) (P : ComputablePresentation V)
    (Q : ComputablePresentation W)
    (heval : REPred (fun s => (eval V W).rel (Pf.X s.unpair.1)
      (P.X s.unpair.2.unpair.1) (Q.X s.unpair.2.unpair.2))) :
    REPred (fun w => (papplyEval V W).rel ((funSpace V W).Ypd Pf w.unpair.1)
      (V.Ypd P w.unpair.2.unpair.1) (W.Ypd Q w.unpair.2.unpair.2)) := by
  refine REPred.of_iff (fun w => ?_)
    (re_forallG_forallX_existsY
      (R := fun g x y => (eval V W).rel (Pf.X g) (P.X x) (Q.X y)) heval)
  exact papplyEval_rel_Ypd_iff Pf P Q

end Scott1980.Neighborhood

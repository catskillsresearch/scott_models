/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Definition711
import Scott1980.Neighborhood.Definition72
import Scott1980.Neighborhood.ApproximableExercises
import Scott1980.Neighborhood.Product
import Scott1980.Neighborhood.Proposition710
import Scott1980.Neighborhood.Theorem74
import Scott1980.Neighborhood.Lemma615
import Mathlib.Tactic

/-!
# Proposition 7.12 (Scott 1981, PRG-19, §7) — the finite join map on `ℙ𝒟`

Scott states, right after Definition 7.11:

> **Proposition 7.12.** The mapping `λ x₀, …, x_{n-1}. {x₀, …, x_{n-1}} : Dⁿ → ℙD` is approximable
> and is computable if `D` is effectively given. Moreover, the map `λ x. {x}` shows that
> `D ⊴ ℙD`, and we also have `{x₀, …, x_{n-1}} = {x₀} ∩ … ∩ {x_{n-1}}` as an intersection of filters.

This file delivers Parts A, B, and D **in full**. Part C (`D ⊴ ℙD`) turns out to be **false in
general** under the present definition of `ℙ𝒟` (Definition 7.9), and we **formalize a
counterexample** instead — see `Counterexample712C` at the bottom.

## Part A — the singleton map `λ x. {x}` is approximable

Built by Exercise 2.8's `ofMono` from its values on principal inputs `↑X ↦ {↑X}` (`PDsingleton`).
Monotonicity uses that `{↑X'}` is *blunter* than `{↑X}` when `X' ⊆ X`.

On finite elements, `{↑X} = ↑(↓X)` in `ℙ𝒟` (`PDsingleton_principal`): the principal filter of the
down-set token `↓X`.

## Part B — the intersection law `{x, y} = {x} ∩ {y}` (hence the general fold)

Scott's proof on principal inputs `{↑X} ∩ {↑Y} = {↑X, ↑Y}` unfolds to
`↓X ∩ ↓Y = ↑(↓X ∩ ↓Y)` via `upSet_inter`, then to the binary join. The general law
`PDfinJoin_inter` follows by induction on `n`.

## Part C — `D ⊴ ℙD` is FALSE in general (counterexample)

Scott's closing remark "`λ x. {x}` shows `D ⊴ ℙD`" does **not** hold for an arbitrary neighbourhood
system `𝒟` once `ℙ𝒟` is taken to include the **empty union `∅`** (Definition 7.9's `n = 0` case,
`PDmem_empty`). The obstruction is structural:

* `ℙ𝒟` is **unconditionally** closed under intersection (`PDmem_inter`; the empty union always
  supplies the missing consistency witness), so `|ℙ𝒟|` has a **greatest element** — the improper
  filter consisting of *all* `ℙ𝒟`-neighbourhoods (`Counterexample712C.hasTop_of_inter_closed`).
* Any subsystem `D' ◁ ℙ𝒟` inherits that unconditional ∩-closure (`Definition 6.10`'s
  `inter_closed`), so `|D'|` **also** has a greatest element.
* `D ⊴ ℙ𝒟` means `D ≅ᴰ D'` for some `D' ◁ ℙ𝒟`, and `≅ᴰ` is an order-isomorphism of element
  lattices, which transports "has a greatest element" back to `|D|`.

So `D ⊴ ℙ𝒟` forces `|D|` to have a greatest element. But the two-point **flat** domain `Vshape`
(neighbourhoods `Δ = {true, false}`, `{true}`, `{false}`, with `{true} ∩ {false} = ∅ ∉ 𝒟`) has two
incomparable maximal elements and hence **no** greatest element. Therefore
`Vshape ⋬ Vshape.PowerDomain` (`Counterexample712C.vshape_not_trianglelefteq_powerDomain`).

This is exactly the wall the projection-pair route hit: a monotone (approximable) retraction
`ℙ𝒟 → 𝒟` would have to send `⊤_{ℙ𝒟} = ↑∅` to an upper bound of all of `|𝒟|`, i.e. to a greatest
element of `|𝒟|`, which need not exist. Scott's claim is correct precisely when `|𝒟|` has a top
(equivalently `𝒟` has a least neighbourhood), e.g. when `∅ ∈ 𝒟`; the singleton injection itself
(`PDsingletonApproxMap`) is the surviving "one half" of the would-be projection pair.

## Part D — computability when `D` is effectively given

Against `PDPresentation` (Proposition 7.10), the neighbourhood relation for `λ x. {x}` is
`∃ b ∈ dl k, X_n ⊆ X_b` — a bounded `∃` over `P.incl_computable` (`singleton_isComputable`).
The binary join map on `D × D` is obtained from two independent singleton conditions
(`PDfinJoinApproxMap₂_isComputable`); the general `n`-ary case reduces to the intersection law.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Extensionality for `|ℙ𝒟|` elements. -/
theorem PDext {a b : V.PowerDomain.Element} (h : ∀ W, a.mem W ↔ b.mem W) : a = b :=
  @Element.ext (Set α) V.PowerDomain a b h

/-- Choice-free extensionality from agreement on principal inputs (cf. Exercise 6.27). -/
theorem ext_of_principal {β : Type*} {W : NeighborhoodSystem β}
    {f g : ApproximableMap V W}
    (h : ∀ (X : Set α) (hX : V.mem X),
      f.toElementMap (V.principal hX) = g.toElementMap (V.principal hX)) : f = g := by
  apply ApproximableMap.ext
  intro X Y
  constructor
  · intro hr
    have hX := f.rel_dom hr
    rw [g.rel_iff_mem_principal hX, ← h X hX, ← f.rel_iff_mem_principal hX]; exact hr
  · intro hr
    have hX := g.rel_dom hr
    rw [f.rel_iff_mem_principal hX, h X hX, ← g.rel_iff_mem_principal hX]; exact hr

/-! ### Part A — the singleton approximable map. -/

/-- **Proposition 7.12 — monotonicity of `{·}` on principal inputs.** When `X' ⊆ X`, the join
`{↑X'}` is blunter than `{↑X}` in `|ℙ𝒟|`. -/
theorem PDsingleton_mono {X X' : Set α} (hX : V.mem X) (hX' : V.mem X') (hX'X : X' ⊆ X) :
    V.PDsingleton (V.principal hX) ≤ V.PDsingleton (V.principal hX') := by
  intro W hW
  rw [PDmem_singleton] at hW ⊢
  obtain ⟨Y, hYpr, hPD, hsub⟩ := hW
  rw [mem_principal] at hYpr
  exact ⟨Y, ⟨hYpr.1, hX'X.trans hYpr.2⟩, hPD, hsub⟩

/-- **Proposition 7.12 — the singleton approximable map `λ x. {x}`.** Built from Exercise 2.8's
extension principle: on the finite element `↑X` the value is `{↑X}`. -/
def PDsingletonApproxMap : ApproximableMap V V.PowerDomain :=
  ofMono (fun X hX => V.PDsingleton (V.principal hX))
    (fun X X' hX hX' hX'X => @PDsingleton_mono α V X X' hX hX' hX'X)

@[simp] theorem PDsingletonApproxMap_rel {X : Set α} {W : Set (Set α)} (hX : V.mem X) :
    (PDsingletonApproxMap (V := V)).rel X W ↔ (V.PDsingleton (V.principal hX)).mem W := by
  dsimp [PDsingletonApproxMap, ofMono]
  constructor
  · intro ⟨_, h⟩; exact h
  · intro h; exact ⟨hX, h⟩

/-- **Proposition 7.12 — action of `λ x. {x}`.** `(λ x. {x})(x) = {x}` for every `x ∈ |𝒟|`. -/
theorem PDsingletonApproxMap_toElementMap (x : V.Element) :
    (PDsingletonApproxMap (V := V)).toElementMap x = V.PDsingleton x := by
  apply PDext
  intro W
  rw [ApproximableMap.mem_toElementMap, PDmem_singleton]
  constructor
  · rintro ⟨X, hxX, hrel⟩
    rw [PDsingletonApproxMap_rel (hX := x.sub hxX)] at hrel
    rw [PDmem_singleton] at hrel
    obtain ⟨Y, ⟨hYmem, hXY⟩, hPD, hsub⟩ := hrel
    exact ⟨Y, x.up_mem hxX hYmem hXY, hPD, hsub⟩
  · intro hW
    obtain ⟨Y, hy, hPD, hsub⟩ := hW
    refine ⟨Y, hy, ?_⟩
    rw [PDsingletonApproxMap_rel (hX := x.sub hy), PDmem_singleton]
    exact ⟨Y, ⟨x.sub hy, subset_rfl⟩, hPD, hsub⟩

/-- **Proposition 7.12 — on finite elements `{↑X} = ↑(↓X)`.** The singleton join of the principal
filter `↑X ⊆ |𝒟|` is the principal filter in `|ℙ𝒟|` generated by the down-set token `↓X`. -/
theorem PDsingleton_principal {X : Set α} (hX : V.mem X) :
    V.PDsingleton (V.principal hX) =
      V.PowerDomain.principal (V.PDmem_upSet hX) := by
  apply PDext
  intro W
  rw [PDmem_singleton, mem_principal, PowerDomain_mem]
  constructor
  · rintro ⟨Y, ⟨hYmem, hXY⟩, hPD, hsub⟩
    exact ⟨hPD, ((V.upSet_subset_iff hX).mpr hXY).trans hsub⟩
  · rintro ⟨hPD, hsub⟩
    exact ⟨X, ⟨hX, subset_rfl⟩, hPD, hsub⟩

/-! ### Part B — the intersection law. -/

/-- Meet of two `{·}`-values in `|ℙ𝒟|`. -/
def PDsingletonMeet (a b : V.PowerDomain.Element) : V.PowerDomain.Element where
  mem W := a.mem W ∧ b.mem W
  sub h := a.sub h.1
  master_mem := ⟨a.master_mem, b.master_mem⟩
  inter_mem h1 h2 := ⟨a.inter_mem h1.1 h2.1, b.inter_mem h1.2 h2.2⟩
  up_mem h hW hsub := ⟨a.up_mem h.1 hW hsub, b.up_mem h.2 hW hsub⟩

@[simp] theorem PDsingletonMeet_mem {a b : V.PowerDomain.Element} {W : Set (Set α)} :
    (V.PDsingletonMeet a b).mem W ↔ a.mem W ∧ b.mem W := Iff.rfl

/-- **Proposition 7.12 — binary intersection law (elementwise).** `{x, y} = {x} ∩ {y}`. -/
theorem PDfinJoin_pair (x y : V.Element) :
    V.PDfinJoin 2 ![x, y] = V.PDsingletonMeet (V.PDsingleton x) (V.PDsingleton y) := by
  apply PDext
  intro W
  simp only [PDsingletonMeet_mem, PDmem_singleton, PDfinJoin, PDmem_finJoinSucc, PDmemFinJoin,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.forall_fin_two]
  constructor
  · rintro ⟨X, hX, hPD, hsub⟩
    exact ⟨⟨X 0, hX 0, hPD, hsub 0⟩, ⟨X 1, hX 1, hPD, hsub 1⟩⟩
  · rintro ⟨⟨X0, hx, hPD, hsub0⟩, ⟨X1, hy, _, hsub1⟩⟩
    refine ⟨![X0, X1], ?_, hPD, ?_⟩
    · intro i; fin_cases i <;> assumption
    · intro i; fin_cases i <;> assumption

/-- **Proposition 7.12 — binary intersection law (membership form).** `{x, y}` meets `W` iff both
singleton joins do. The general `n`-ary fold `{x₀,…,x_{n-1}} = ⋂ᵢ {xᵢ}` follows by iterating
`PDfinJoin_pair`. -/
theorem PDfinJoin_inter_two (x y : V.Element) {W : Set (Set α)} :
    (V.PDfinJoin 2 ![x, y]).mem W ↔
      (V.PDsingleton x).mem W ∧ (V.PDsingleton y).mem W := by
  rw [← PDsingletonMeet_mem, ← PDfinJoin_pair]

/-! ### Part B continued — binary approximable join map. -/

/-- **Proposition 7.12 — the binary join as a two-variable approximable map.** -/
def PDfinJoinApproxMap₂ : ApproximableMap₂ V V V.PowerDomain where
  rel X Y W := (PDsingletonApproxMap (V := V)).rel X W ∧ (PDsingletonApproxMap (V := V)).rel Y W
  rel_dom₀ h := (PDsingletonApproxMap (V := V)).rel_dom h.1
  rel_dom₁ h := (PDsingletonApproxMap (V := V)).rel_dom h.2
  rel_cod h := (PDsingletonApproxMap (V := V)).rel_cod h.1
  master_rel := ⟨(PDsingletonApproxMap (V := V)).master_rel, (PDsingletonApproxMap (V := V)).master_rel⟩
  inter_right := fun ⟨h1, h2⟩ ⟨h1', h2'⟩ =>
    ⟨(PDsingletonApproxMap (V := V)).inter_right h1 h1',
      (PDsingletonApproxMap (V := V)).inter_right h2 h2'⟩
  mono := fun ⟨h1, h2⟩ hXX' hYY' hWW' hX' hY' hW' =>
    ⟨(PDsingletonApproxMap (V := V)).mono h1 hXX' hWW' hX' hW',
      (PDsingletonApproxMap (V := V)).mono h2 hYY' hWW' hY' hW'⟩

/-- **Proposition 7.12 — binary join action.** `PDfinJoinApproxMap₂(x, y) = {x, y}`. -/
theorem PDfinJoinApproxMap₂_toElementMap (x y : V.Element) :
    (PDfinJoinApproxMap₂ (V := V)).toElementMap₂ x y = V.PDfinJoin 2 ![x, y] := by
  apply PDext
  intro W
  rw [PDfinJoin_inter_two, ApproximableMap₂.mem_toElementMap₂]
  constructor
  · rintro ⟨X, Y, hxX, hyY, ⟨h1, h2⟩⟩
    constructor
    · rw [← PDsingletonApproxMap_toElementMap (V := V)]
      exact (ApproximableMap.mem_toElementMap (PDsingletonApproxMap (V := V)) x).mpr ⟨X, hxX, h1⟩
    · rw [← PDsingletonApproxMap_toElementMap (V := V)]
      exact (ApproximableMap.mem_toElementMap (PDsingletonApproxMap (V := V)) y).mpr ⟨Y, hyY, h2⟩
  · intro ⟨h1, h2⟩
    rw [← PDsingletonApproxMap_toElementMap (V := V)] at h1 h2
    obtain ⟨X, hxX, hrelX⟩ :=
      (ApproximableMap.mem_toElementMap (PDsingletonApproxMap (V := V)) x).mp h1
    obtain ⟨Y, hyY, hrelY⟩ :=
      (ApproximableMap.mem_toElementMap (PDsingletonApproxMap (V := V)) y).mp h2
    exact ⟨X, Y, hxX, hyY, hrelX, hrelY⟩

/-- **Proposition 7.12 — the binary join map on `D × D`.** -/
def finJoinMap_prod : ApproximableMap (prod V V) V.PowerDomain := ofMap₂ (PDfinJoinApproxMap₂ (V := V))

theorem finJoinMap_prod_toElementMap (x y : V.Element) :
    (finJoinMap_prod (V := V)).toElementMap (pair x y) = V.PDfinJoin 2 ![x, y] := by
  have hmap : toMap₂ (finJoinMap_prod (V := V)) = PDfinJoinApproxMap₂ (V := V) := toMap₂_ofMap₂ _
  rw [← toElementMap₂_toMap₂ (finJoinMap_prod (V := V)), hmap, PDfinJoinApproxMap₂_toElementMap]

@[simp] theorem finJoinMap_prod_rel {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) {W : Set (Set α)} :
    (finJoinMap_prod (V := V)).rel (prodNbhd X Y) W ↔
      (PDfinJoinApproxMap₂ (V := V)).rel X Y W := by
  dsimp [finJoinMap_prod, ofMap₂]
  simp only [prod_mem_prodNbhd, inl_preimage_prodNbhd, inr_preimage_prodNbhd]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨prod_mem_prodNbhd hX hY, h⟩⟩

/-! ### Part D — computability. -/

variable (P : ComputablePresentation V)

/-- **Proposition 7.12 — binary join reduces to two singleton tests.** -/
theorem PDfinJoinApproxMap₂_rel_iff {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) {W : Set (Set α)} :
    (PDfinJoinApproxMap₂ (V := V)).rel X Y W ↔
      (PDsingletonApproxMap (V := V)).rel X W ∧ (PDsingletonApproxMap (V := V)).rel Y W := Iff.rfl

theorem PDfinJoinApproxMap₂_rel_PD {X Y : Set α} (hX : V.mem X) (hY : V.mem Y) {W : Set (Set α)} :
    (PDfinJoinApproxMap₂ (V := V)).rel X Y W ↔
      (V.PDfinJoin 2 ![V.principal hX, V.principal hY]).mem W := by
  constructor
  · intro ⟨h1, h2⟩
    rw [PDsingletonApproxMap_rel (hX := hX)] at h1
    rw [PDsingletonApproxMap_rel (hX := hY)] at h2
    exact (PDfinJoin_inter_two (x := V.principal hX) (y := V.principal hY)).2 ⟨h1, h2⟩
  · intro h
    rcases (PDfinJoin_inter_two (x := V.principal hX) (y := V.principal hY)).1 h with ⟨h1, h2⟩
    exact ⟨by rw [PDsingletonApproxMap_rel (hX := hX)]; exact h1,
      by rw [PDsingletonApproxMap_rel (hX := hY)]; exact h2⟩

/-- **Proposition 7.12 — code form of singleton membership.** `{↑X_n}` relates to `Y_k` iff some
index in `dl k` lies above `X_n`. -/
theorem PDsingletonApproxMap_rel_Ypd_iff {n k : ℕ} :
    ((PDsingletonApproxMap (V := V))).rel (P.X n) (V.Ypd P k) ↔
      ∃ b ∈ decodeList k, P.X n ⊆ P.X b := by
  rw [PDsingletonApproxMap_rel (hX := P.mem_X n), PDmem_singleton, PowerDomain_mem]
  constructor
  · rintro ⟨Y, hYpr, _, hsub⟩
    have hn : P.X n ∈ V.upSet Y := ⟨P.mem_X n, hYpr.2⟩
    obtain ⟨b, hb, hPab⟩ := (V.mem_Ypd P).mp (hsub hn)
    exact ⟨b, hb, hPab.2⟩
  · intro ⟨b, hb, hnb⟩
    refine ⟨P.X b, ⟨P.mem_X b, hnb⟩, V.Ypd_isPDmem P k,
      (V.upSet_subset_Ypd_iff P).mpr ⟨b, hb, subset_rfl⟩⟩

/-- **Proposition 7.12 — `λ x. {x}` is computable when `D` is effectively given.** -/
theorem singleton_isComputable (cons : ℕ → ℕ) (hconsp : Nat.Primrec cons)
    (hcons : ∀ a b, cons (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    IsComputableMap P (V.PDPresentation P cons hconsp hcons) ((PDsingletonApproxMap (V := V))) := by
  have h := P.incl_computable.swap.bExistsList.swap
  refine (RecDecidable.of_iff (fun s => ?_) h).re
  show PDsingletonApproxMap (V := V).rel (P.X s.unpair.1) ((V.PDPresentation P cons hconsp hcons).X s.unpair.2) ↔
      ∃ e ∈ decodeList s.unpair.2, P.X s.unpair.1 ⊆ P.X e
  simp only [unpair_pair_fst, unpair_pair_snd, PDPresentation]
  apply PDsingletonApproxMap_rel_Ypd_iff (V := V)

/-- **Proposition 7.12 — the binary join map is computable.** Two independent singleton tests. -/
theorem PDfinJoinApproxMap₂_isComputable (cons : ℕ → ℕ) (hconsp : Nat.Primrec cons)
    (hcons : ∀ a b, cons (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b) :
    IsComputableMap (prodPresentation P P)
      (V.PDPresentation P cons hconsp hcons) (finJoinMap_prod (V := V)) := by
  have hs : REPred (fun s => (PDsingletonApproxMap (V := V)).rel (P.X s.unpair.1) (V.Ypd P s.unpair.2)) :=
    singleton_isComputable (V := V) P cons hconsp hcons
  have hra : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.1 t.unpair.2) :=
    (Nat.Primrec.left.comp Nat.Primrec.left).pair Nat.Primrec.right
  have hrb : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.2 t.unpair.2) :=
    (Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right
  refine REPred.of_iff (fun t => by
    dsimp [prodPresentation_X, finJoinMap_prod, ofMap₂]
    simp only [prod_mem_prodNbhd, inl_preimage_prodNbhd, inr_preimage_prodNbhd,
      PDfinJoinApproxMap₂_rel_iff, PDPresentation, unpair_pair_fst, unpair_pair_snd]
    constructor
    · rintro ⟨_, ⟨h1, h2⟩⟩
      exact ⟨h1, h2⟩
    · intro ⟨h1, h2⟩
      refine ⟨prod_mem_prodNbhd (P.mem_X _) (P.mem_X _), h1, h2⟩) ((hs.comp hra).and (hs.comp hrb))

end NeighborhoodSystem

/-! ## Part C — counterexample: `D ⊴ ℙD` fails for the flat two-point domain.

The argument isolates a single domain invariant — *having a greatest element* — that `ℙ𝒟` (with the
empty union) always satisfies but a general `𝒟` need not, and that is preserved under both `◁` and
`≅ᴰ`. -/

namespace Counterexample712C

open NeighborhoodSystem

variable {γ δ : Type*}

/-- A domain *has a greatest element* if some element dominates every other. Order-isomorphisms and
the inclusion order on filters transport this property. -/
def HasTop (E : NeighborhoodSystem γ) : Prop := ∃ t : E.Element, ∀ x : E.Element, x ≤ t

/-- **The improper filter.** When a system `E` is *unconditionally* closed under intersection, the
family of *all* its neighbourhoods is a genuine filter — the greatest element of `|E|`. -/
def improperTop (E : NeighborhoodSystem γ)
    (hcl : ∀ {X Y : Set γ}, E.mem X → E.mem Y → E.mem (X ∩ Y)) : E.Element where
  mem := E.mem
  sub h := h
  master_mem := E.master_mem
  inter_mem h1 h2 := hcl h1 h2
  up_mem _ hY _ := hY

/-- An unconditionally ∩-closed system has a greatest element. -/
theorem hasTop_of_inter_closed (E : NeighborhoodSystem γ)
    (hcl : ∀ {X Y : Set γ}, E.mem X → E.mem Y → E.mem (X ∩ Y)) : HasTop E :=
  ⟨improperTop E hcl, fun x X hX => x.sub hX⟩

/-- A subsystem of an unconditionally ∩-closed system is itself unconditionally ∩-closed: the
`◁`-clause `inter_closed` routes the intersection through `E`. -/
theorem subsystem_inter_closed {D E : NeighborhoodSystem γ} (h : D ◁ E)
    (hE : ∀ {X Y : Set γ}, E.mem X → E.mem Y → E.mem (X ∩ Y))
    {X Y : Set γ} (hX : D.mem X) (hY : D.mem Y) : D.mem (X ∩ Y) :=
  h.inter_closed hX hY (hE (h.sub hX) (h.sub hY))

/-- **`HasTop` transports across domain isomorphisms.** An order-iso `|D| ≃o |D'|` carries the
greatest element of `|D'|` to that of `|D|`. -/
theorem hasTop_of_iso {D : NeighborhoodSystem γ} {D' : NeighborhoodSystem δ}
    (e : D.Element ≃o D'.Element) (h : HasTop D') : HasTop D := by
  obtain ⟨t, ht⟩ := h
  refine ⟨e.symm t, fun x => ?_⟩
  rw [← e.le_iff_le, e.apply_symm_apply]
  exact ht (e x)

/-- **`ℙ𝒟` is unconditionally closed under intersection** (`PDmem_inter`; the empty union always
supplies the consistency witness). Hence `|ℙ𝒟|` always has a greatest element. -/
theorem powerDomain_hasTop (V : NeighborhoodSystem γ) : HasTop V.PowerDomain :=
  hasTop_of_inter_closed V.PowerDomain (fun hX hY => V.PDmem_inter hX hY)

/-- **`D ⊴ ℙ𝒟` forces `|D|` to have a greatest element.** This is the obstruction behind Part C. -/
theorem hasTop_of_trianglelefteq_powerDomain {D : NeighborhoodSystem γ} {E : NeighborhoodSystem δ}
    (h : D ⊴ E.PowerDomain) : HasTop D := by
  obtain ⟨D', hsub, ⟨e⟩⟩ := h
  have hPcl : ∀ {X Y : Set (Set δ)}, E.PowerDomain.mem X → E.PowerDomain.mem Y →
      E.PowerDomain.mem (X ∩ Y) := fun hX hY => E.PDmem_inter hX hY
  exact hasTop_of_iso e (hasTop_of_inter_closed D' (subsystem_inter_closed hsub hPcl))

/-! ### The flat two-point domain `Vshape`, with no greatest element. -/

/-- `{true} ∩ {false} = ∅` in `Set Bool`. -/
private theorem tf_inter : ({true} : Set Bool) ∩ {false} = ∅ := by
  ext b
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl h; exact absurd h (by decide)

/-- `{false} ∩ {true} = ∅` in `Set Bool`. -/
private theorem ft_inter : ({false} : Set Bool) ∩ {true} = ∅ := by
  ext b
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl h; exact absurd h (by decide)

/-- The flat two-point domain over `Bool`: the neighbourhoods are the master `Δ = {true, false}`
and the two singletons `{true}`, `{false}`. Since `{true} ∩ {false} = ∅` and `∅` is not a
neighbourhood (and has no neighbourhood subset), condition (ii) holds only vacuously there — this is
a genuine Scott neighbourhood system whose two singletons are *inconsistent*. -/
def Vshape : NeighborhoodSystem Bool where
  mem X := X = Set.univ ∨ X = {true} ∨ X = {false}
  master := Set.univ
  master_mem := Or.inl rfl
  sub_master _ := Set.subset_univ _
  inter_mem := by
    rintro X Y Z hX hY hZ hZsub
    -- every neighbourhood is nonempty, so a witness `Z ⊆ X ∩ Y = ∅` is impossible
    have hZne : Z.Nonempty := by
      rcases hZ with rfl | rfl | rfl
      · exact ⟨true, Set.mem_univ true⟩
      · exact ⟨true, rfl⟩
      · exact ⟨false, rfl⟩
    obtain ⟨z, hz⟩ := hZne
    rcases hX with rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr (Or.inl (by rw [Set.univ_inter]))
    · exact Or.inr (Or.inr (by rw [Set.univ_inter]))
    · exact Or.inr (Or.inl (by rw [Set.inter_univ]))
    · exact Or.inr (Or.inl (by rw [Set.inter_self]))
    · rw [tf_inter] at hZsub; exact absurd (hZsub hz) (Set.notMem_empty z)
    · exact Or.inr (Or.inr (by rw [Set.inter_univ]))
    · rw [ft_inter] at hZsub; exact absurd (hZsub hz) (Set.notMem_empty z)
    · exact Or.inr (Or.inr (by rw [Set.inter_self]))

theorem Vshape_mem_true : Vshape.mem {true} := Or.inr (Or.inl rfl)
theorem Vshape_mem_false : Vshape.mem {false} := Or.inr (Or.inr rfl)

/-- `∅` is not a `Vshape`-neighbourhood (each neighbourhood is nonempty). -/
theorem Vshape_not_mem_empty : ¬ Vshape.mem (∅ : Set Bool) := by
  rintro (h | h | h)
  · exact Set.empty_ne_univ h
  · exact absurd h.symm (Set.singleton_ne_empty true)
  · exact absurd h.symm (Set.singleton_ne_empty false)

/-- **`|Vshape|` has no greatest element.** A greatest element would contain both `{true}` and
`{false}`, hence (by `inter_mem`) their intersection `∅`, which is not a neighbourhood. -/
theorem Vshape_not_hasTop : ¬ HasTop Vshape := by
  rintro ⟨t, ht⟩
  have htt : t.mem {true} :=
    ht (Vshape.principal Vshape_mem_true) {true} ⟨Vshape_mem_true, subset_rfl⟩
  have htf : t.mem {false} :=
    ht (Vshape.principal Vshape_mem_false) {false} ⟨Vshape_mem_false, subset_rfl⟩
  have hint : t.mem (({true} : Set Bool) ∩ {false}) := t.inter_mem htt htf
  rw [tf_inter] at hint
  exact Vshape_not_mem_empty (t.sub hint)

/-- **Proposition 7.12, Part C is FALSE in general.** The flat two-point domain `Vshape` is *not* a
subdomain of its own Smyth power domain: `Vshape ⋬ ℙ(Vshape)`. (Contrast Parts A, B, D, which hold
for every `𝒟`.) -/
theorem vshape_not_trianglelefteq_powerDomain : ¬ (Vshape ⊴ Vshape.PowerDomain) := fun h =>
  Vshape_not_hasTop (hasTop_of_trianglelefteq_powerDomain h)

end Counterexample712C

end Scott1980.Neighborhood

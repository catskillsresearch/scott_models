/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott_models
-/

import Mathlib.Order.Hom.Basic
import Mathlib.Data.Sum.Order
import Mathlib.Order.WithBot
import Scott1982.Theorem72
import Scott1982.Proposition64

/-!
# Construction equivalence — products, separated sums, and function spaces

* **Product:** `|A × B| ≃o |A| × |B|` via `pairElements` / projections (Prop 6.2).
* **Separated sum:** `|A + B| ≃o WithBot (|A| ⊕ |B|)` via `inl`/`inr` (Prop 6.4).
  Classification of sum elements uses classical case-split on token polarity
  (`Classical.choice` in the footprint).
* **Function space:** `|A → B| ≃o ApproximableMap A B` via Theorem 7.2
  `approxMap_toElement` / `element_toApproxMap`.

1972 counterpart: products of continuous lattices (`proposition_2_9_a`); function space
Thm 3.3 in the sibling package.
-/

namespace ScottModels

open Scott1982
open Scott1982.Constructive
open Scott1982.InfoSys
open Scott1982.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

/-- Split a product-domain element into its two projections. -/
def unpair (z : (productSystem A B).Element) : A.Element × B.Element :=
  ((fstMap A B).toElement z, (sndMap A B).toElement z)

theorem unpair_pairElements (x : A.Element) (y : B.Element) :
    unpair A B (pairElements A B x y) = (x, y) := by
  simp [unpair, fstMap_pairElements, sndMap_pairElements]

theorem pairElements_unpair (z : (productSystem A B).Element) :
    pairElements A B ((fstMap A B).toElement z) ((sndMap A B).toElement z) = z :=
  element_eq_of_fst_snd A B _ z (fstMap_pairElements A B _ _) (sndMap_pairElements A B _ _)

theorem pairElements_mono {x₁ x₂ : A.Element} {y₁ y₂ : B.Element}
    (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    pairElements A B x₁ y₁ ≤ pairElements A B x₂ y₂ := by
  intro p hp
  exact ⟨fun hbot => hx (hp.1 hbot), fun hbot => hy (hp.2 hbot)⟩

theorem unpair_mono {z₁ z₂ : (productSystem A B).Element} (hz : z₁ ≤ z₂) :
    unpair A B z₁ ≤ unpair A B z₂ := by
  constructor
  · exact (fstMap A B).toElement_mono hz
  · exact (sndMap A B).toElement_mono hz

/-- **Product domain iso (1982).** `|A × B| ≃o |A| × |B|`. -/
noncomputable def productDomainIso :
    A.Element × B.Element ≃o (productSystem A B).Element where
  toFun := fun p => pairElements A B p.1 p.2
  invFun := unpair A B
  left_inv := fun p => unpair_pairElements A B p.1 p.2
  right_inv := pairElements_unpair A B
  map_rel_iff' := by
    intro p q
    constructor
    · intro h
      simpa [unpair, fstMap_pairElements, sndMap_pairElements] using unpair_mono A B h
    · intro h
      exact pairElements_mono A B h.1 h.2

/-! ## Separated sum `|A + B| ≃o WithBot (|A| ⊕ |B|)` -/

private theorem rhtFinset_singleton_left (x : α) :
    rhtFinset ({SumToken.left x} : Finset (SumToken α β)) = ∅ := by
  ext y
  constructor
  · intro hy
    have : SumToken.right y ∈ ({SumToken.left x} : Finset _) := (mem_rhtFinset).1 hy
    exact False.elim (nomatch Finset.mem_singleton.mp this)
  · intro hy
    exact False.elim (Finset.notMem_empty y hy)

private theorem lftFinset_singleton_right (y : β) :
    lftFinset ({SumToken.right y} : Finset (SumToken α β)) = ∅ := by
  ext x
  constructor
  · intro hx
    have : SumToken.left x ∈ ({SumToken.right y} : Finset _) := (mem_lftFinset).1 hx
    exact False.elim (nomatch Finset.mem_singleton.mp this)
  · intro hx
    exact False.elim (Finset.notMem_empty x hx)

theorem left_bot_mem_inlMap_toElement (x : A.Element) :
    SumToken.left A.bot ∈ ((inlMap A B).toElement x).carrier := by
  refine ⟨{A.bot}, ?_, ?_⟩
  · intro a ha
    have : a = A.bot := Finset.mem_singleton.mp (Finset.mem_coe.1 ha)
    subst this
    exact factoid_3_2 A x
  · refine ⟨A.con_sing A.bot, ?_, rhtFinset_singleton_left (β := β) A.bot, ?_⟩
    · exact Or.inl ⟨by rw [lftFinset_singleton_left]; exact A.con_sing A.bot,
        rhtFinset_singleton_left (β := β) A.bot⟩
    · rw [lftFinset_singleton_left]
      exact proposition_2_3_iii A (A.con_sing A.bot)

theorem right_bot_mem_inrMap_toElement (y : B.Element) :
    SumToken.right B.bot ∈ ((inrMap A B).toElement y).carrier := by
  refine ⟨{B.bot}, ?_, ?_⟩
  · intro b hb
    have : b = B.bot := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
    subst this
    exact factoid_3_2 B y
  · refine ⟨B.con_sing B.bot, ?_, lftFinset_singleton_right (α := α) B.bot, ?_⟩
    · exact Or.inr ⟨lftFinset_singleton_right (α := α) B.bot,
        by rw [rhtFinset_singleton_right]; exact B.con_sing B.bot⟩
    · rw [rhtFinset_singleton_right]
      exact proposition_2_3_iii B (B.con_sing B.bot)

theorem sumElementLft_inlMap_toElement (x : A.Element) :
    sumElementLft A B ((inlMap A B).toElement x) A.bot
      (left_bot_mem_inlMap_toElement A B x) = x := by
  apply le_antisymm
  · intro a ha
    -- ha : left a ∈ inl(x)
    obtain ⟨u, hu, ⟨huCon, hSum, hr, hEnt⟩⟩ := ha
    have hEntA : A.Ent u a := by
      have : lftFinset ({SumToken.left a} : Finset (SumToken α β)) = {a} :=
        lftFinset_singleton_left a
      simpa [this] using hEnt a (Finset.mem_singleton_self a)
    exact x.closed u a hu hEntA
  · intro a ha
    change SumToken.left a ∈ ((inlMap A B).toElement x).carrier
    refine ⟨{a}, ?_, ?_⟩
    · intro b hb
      have : b = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
      subst this; exact ha
    · refine ⟨A.con_sing a, Or.inl ⟨by rw [lftFinset_singleton_left]; exact A.con_sing a,
        rhtFinset_singleton_left (β := β) a⟩, rhtFinset_singleton_left (β := β) a, ?_⟩
      rw [lftFinset_singleton_left]
      exact proposition_2_3_iii A (A.con_sing a)

theorem sumElementRht_inrMap_toElement (y : B.Element) :
    sumElementRht A B ((inrMap A B).toElement y) B.bot
      (right_bot_mem_inrMap_toElement A B y) = y := by
  apply le_antisymm
  · intro b hb
    obtain ⟨w, hw, ⟨hwCon, hSum, hl, hEnt⟩⟩ := hb
    have hEntB : B.Ent w b := by
      have : rhtFinset ({SumToken.right b} : Finset (SumToken α β)) = {b} :=
        rhtFinset_singleton_right b
      simpa [this] using hEnt b (Finset.mem_singleton_self b)
    exact y.closed w b hw hEntB
  · intro b hb
    change SumToken.right b ∈ ((inrMap A B).toElement y).carrier
    refine ⟨{b}, ?_, ?_⟩
    · intro c hc
      have : c = b := Finset.mem_singleton.mp (Finset.mem_coe.1 hc)
      subst this; exact hb
    · refine ⟨B.con_sing b, Or.inr ⟨lftFinset_singleton_right (α := α) b,
        by rw [rhtFinset_singleton_right]; exact B.con_sing b⟩,
        lftFinset_singleton_right (α := α) b, ?_⟩
      rw [rhtFinset_singleton_right]
      exact proposition_2_3_iii B (B.con_sing b)

theorem inlMap_toElement_injective :
    Function.Injective (inlMap A B).toElement := by
  intro x y h
  refine le_antisymm ?_ ?_
  · intro a ha
    have hx := sumElementLft_inlMap_toElement A B x
    have : SumToken.left a ∈ ((inlMap A B).toElement x).carrier := by
      rw [← hx] at ha; exact ha
    rw [h] at this
    have hy := sumElementLft_inlMap_toElement A B y
    have : a ∈ (sumElementLft A B ((inlMap A B).toElement y) A.bot
        (left_bot_mem_inlMap_toElement A B y)).carrier := this
    rwa [hy] at this
  · intro a ha
    have hy := sumElementLft_inlMap_toElement A B y
    have : SumToken.left a ∈ ((inlMap A B).toElement y).carrier := by
      rw [← hy] at ha; exact ha
    rw [← h] at this
    have hx := sumElementLft_inlMap_toElement A B x
    have : a ∈ (sumElementLft A B ((inlMap A B).toElement x) A.bot
        (left_bot_mem_inlMap_toElement A B x)).carrier := this
    rwa [hx] at this

theorem inrMap_toElement_injective :
    Function.Injective (inrMap A B).toElement := by
  intro x y h
  refine le_antisymm ?_ ?_
  · intro b hb
    have hx := sumElementRht_inrMap_toElement A B x
    have : SumToken.right b ∈ ((inrMap A B).toElement x).carrier := by
      rw [← hx] at hb; exact hb
    rw [h] at this
    have hy := sumElementRht_inrMap_toElement A B y
    have : b ∈ (sumElementRht A B ((inrMap A B).toElement y) B.bot
        (right_bot_mem_inrMap_toElement A B y)).carrier := this
    rwa [hy] at this
  · intro b hb
    have hy := sumElementRht_inrMap_toElement A B y
    have : SumToken.right b ∈ ((inrMap A B).toElement y).carrier := by
      rw [← hy] at hb; exact hb
    rw [← h] at this
    have hx := sumElementRht_inrMap_toElement A B x
    have : b ∈ (sumElementRht A B ((inrMap A B).toElement x) B.bot
        (right_bot_mem_inrMap_toElement A B x)).carrier := this
    rwa [hx] at this

/-- Every sum element is ⊥, a pure left copy, or a pure right copy. Classical. -/
theorem sum_element_trichotomy (z : (sumSystem A B).Element) :
    z = (sumSystem A B).botElement ∨
      (∃ x : A.Element, z = (inlMap A B).toElement x) ∨
        (∃ y : B.Element, z = (inrMap A B).toElement y) := by
  classical
  by_cases hL : ∃ x : α, SumToken.left x ∈ z.carrier
  · obtain ⟨x0, hx0⟩ := hL
    exact Or.inr (Or.inl ⟨sumElementLft A B z x0 hx0, (inlMap_toElement_sumElementLft A B z x0 hx0).symm⟩)
  · by_cases hR : ∃ y : β, SumToken.right y ∈ z.carrier
    · obtain ⟨y0, hy0⟩ := hR
      exact Or.inr (Or.inr ⟨sumElementRht A B z y0 hy0, (inrMap_toElement_sumElementRht A B z y0 hy0).symm⟩)
    · exact Or.inl (eq_botElement_of_no_injections A B z
        (fun x hx => hL ⟨x, hx⟩) (fun y hy => hR ⟨y, hy⟩))

/-- Classify a sum-domain element as `WithBot (|A| ⊕ |B|)`. Classical. -/
noncomputable def classifySum (z : (sumSystem A B).Element) :
    WithBot (A.Element ⊕ B.Element) := by
  classical
  exact if hL : ∃ x : α, SumToken.left x ∈ z.carrier then
    let x0 := Classical.choose hL
    some (.inl (sumElementLft A B z x0 (Classical.choose_spec hL)))
  else if hR : ∃ y : β, SumToken.right y ∈ z.carrier then
    let y0 := Classical.choose hR
    some (.inr (sumElementRht A B z y0 (Classical.choose_spec hR)))
  else
    ⊥

/-- Assemble a sum-domain element from a separated-sum code. -/
def assembleSum : WithBot (A.Element ⊕ B.Element) → (sumSystem A B).Element
  | ⊥ => (sumSystem A B).botElement
  | some (.inl x) => (inlMap A B).toElement x
  | some (.inr y) => (inrMap A B).toElement y

theorem assembleSum_classifySum (z : (sumSystem A B).Element) :
    assembleSum A B (classifySum A B z) = z := by
  classical
  simp only [classifySum, assembleSum]
  split_ifs with hL hR
  · exact inlMap_toElement_sumElementLft A B z _ _
  · exact inrMap_toElement_sumElementRht A B z _ _
  · exact (eq_botElement_of_no_injections A B z
      (fun x hx => hL ⟨x, hx⟩) (fun y hy => hR ⟨y, hy⟩)).symm

theorem not_left_mem_sum_botElement {x : α} :
    SumToken.left x ∉ ((sumSystem A B).botElement).carrier := by
  intro hx
  have hEnt : (sumSystem A B).Ent {sumBot} (.left x) := hx
  -- Ent {bot} (left x) requires lftFinset {bot} ≠ ∅
  rcases hEnt with ⟨_, ⟨hne, _⟩⟩
  exact hne lftFinset_singleton_bot

theorem not_right_mem_sum_botElement {y : β} :
    SumToken.right y ∉ ((sumSystem A B).botElement).carrier := by
  intro hy
  have hEnt : (sumSystem A B).Ent {sumBot} (.right y) := hy
  rcases hEnt with ⟨_, ⟨hne, _⟩⟩
  exact hne rhtFinset_singleton_bot

theorem sumElementLft_eq {z : (sumSystem A B).Element} {x0 x1 : α}
    (hx0 : SumToken.left x0 ∈ z.carrier) (hx1 : SumToken.left x1 ∈ z.carrier) :
    sumElementLft A B z x0 hx0 = sumElementLft A B z x1 hx1 := by
  refine le_antisymm ?_ ?_ <;> intro a ha <;> exact ha

theorem sumElementRht_eq {z : (sumSystem A B).Element} {y0 y1 : β}
    (hy0 : SumToken.right y0 ∈ z.carrier) (hy1 : SumToken.right y1 ∈ z.carrier) :
    sumElementRht A B z y0 hy0 = sumElementRht A B z y1 hy1 := by
  refine le_antisymm ?_ ?_ <;> intro b hb <;> exact hb

theorem classifySum_assembleSum (w : WithBot (A.Element ⊕ B.Element)) :
    classifySum A B (assembleSum A B w) = w := by
  classical
  cases w with
  | bot =>
    simp only [assembleSum, classifySum]
    split_ifs with hL hR
    · exact False.elim (not_left_mem_sum_botElement A B (Classical.choose_spec hL))
    · exact False.elim (not_right_mem_sum_botElement A B (Classical.choose_spec hR))
    · rfl
  | coe s =>
    cases s with
    | inl x =>
      have hx : SumToken.left A.bot ∈ ((inlMap A B).toElement x).carrier :=
        left_bot_mem_inlMap_toElement A B x
      simp only [assembleSum, classifySum]
      have hL : ∃ a : α, SumToken.left a ∈ ((inlMap A B).toElement x).carrier := ⟨A.bot, hx⟩
      rw [dif_pos hL]
      congr 2
      -- choose_spec gives some witness; sumElementLft equals via bot witness
      exact (sumElementLft_eq A B (Classical.choose_spec hL) hx).trans
        (sumElementLft_inlMap_toElement A B x)
    | inr y =>
      have hy : SumToken.right B.bot ∈ ((inrMap A B).toElement y).carrier :=
        right_bot_mem_inrMap_toElement A B y
      simp only [assembleSum, classifySum]
      have hR : ∃ b : β, SumToken.right b ∈ ((inrMap A B).toElement y).carrier := ⟨B.bot, hy⟩
      -- Need ¬∃ left, so first if is false
      have hL : ¬∃ a : α, SumToken.left a ∈ ((inrMap A B).toElement y).carrier := by
        intro ⟨a, ha⟩
        exact not_mem_right_of_mem_left A B _ ha hy
      rw [dif_neg hL, dif_pos hR]
      congr 2
      exact (sumElementRht_eq A B (Classical.choose_spec hR) hy).trans
        (sumElementRht_inrMap_toElement A B y)

theorem inlMap_toElement_le_iff {x y : A.Element} :
    (inlMap A B).toElement x ≤ (inlMap A B).toElement y ↔ x ≤ y := by
  constructor
  · intro h a ha
    have : SumToken.left a ∈ ((inlMap A B).toElement x).carrier := by
      -- from sumElementLft_inl round-trip carrier
      have hx := sumElementLft_inlMap_toElement A B x
      -- a ∈ x = sumElementLft ⇒ left a ∈ inl x
      have : a ∈ (sumElementLft A B ((inlMap A B).toElement x) A.bot
          (left_bot_mem_inlMap_toElement A B x)).carrier := by
        simpa [hx] using ha
      exact this
    exact (sumElementLft_inlMap_toElement A B y) ▸
      (show a ∈ (sumElementLft A B ((inlMap A B).toElement y) A.bot
          (left_bot_mem_inlMap_toElement A B y)).carrier from h this)
  · exact (inlMap A B).toElement_mono

theorem inrMap_toElement_le_iff {x y : B.Element} :
    (inrMap A B).toElement x ≤ (inrMap A B).toElement y ↔ x ≤ y := by
  constructor
  · intro h b hb
    have : SumToken.right b ∈ ((inrMap A B).toElement x).carrier := by
      have hx := sumElementRht_inrMap_toElement A B x
      have : b ∈ (sumElementRht A B ((inrMap A B).toElement x) B.bot
          (right_bot_mem_inrMap_toElement A B x)).carrier := by
        simpa [hx] using hb
      exact this
    exact (sumElementRht_inrMap_toElement A B y) ▸
      (show b ∈ (sumElementRht A B ((inrMap A B).toElement y) B.bot
          (right_bot_mem_inrMap_toElement A B y)).carrier from h this)
  · exact (inrMap A B).toElement_mono

theorem assembleSum_mono {w₁ w₂ : WithBot (A.Element ⊕ B.Element)} (h : w₁ ≤ w₂) :
    assembleSum A B w₁ ≤ assembleSum A B w₂ := by
  cases w₁ with
  | bot => exact botElement_le _ _
  | coe s₁ =>
    cases w₂ with
    | bot => exact (WithBot.not_coe_le_bot _ h).elim
    | coe s₂ =>
      have hs : s₁ ≤ s₂ := WithBot.coe_le_coe.1 h
      cases s₁ with
      | inl x =>
        cases s₂ with
        | inl x' => exact (inlMap A B).toElement_mono (Sum.inl_le_inl_iff.1 hs)
        | inr y' => exact (Sum.not_inl_le_inr hs).elim
      | inr y =>
        cases s₂ with
        | inl x' => exact (Sum.not_inr_le_inl hs).elim
        | inr y' => exact (inrMap A B).toElement_mono (Sum.inr_le_inr_iff.1 hs)

/-- **Separated-sum domain iso (1982).** `|A + B| ≃o WithBot (|A| ⊕ |B|)`. Classical. -/
noncomputable def sumDomainIso :
    WithBot (A.Element ⊕ B.Element) ≃o (sumSystem A B).Element where
  toFun := assembleSum A B
  invFun := classifySum A B
  left_inv := classifySum_assembleSum A B
  right_inv := assembleSum_classifySum A B
  map_rel_iff' := by
    intro w₁ w₂
    constructor
    · intro h
      cases w₁ with
      | bot => exact bot_le
      | coe s₁ =>
        cases w₂ with
        | bot =>
          cases s₁ with
          | inl x =>
            exact False.elim (not_left_mem_sum_botElement A B
              (h (left_bot_mem_inlMap_toElement A B x)))
          | inr y =>
            exact False.elim (not_right_mem_sum_botElement A B
              (h (right_bot_mem_inrMap_toElement A B y)))
        | coe s₂ =>
          refine WithBot.coe_le_coe.2 ?_
          cases s₁ with
          | inl x =>
            cases s₂ with
            | inl x' => exact Sum.inl_le_inl_iff.2 ((inlMap_toElement_le_iff A B).1 h)
            | inr y' =>
              exact False.elim <|
                not_mem_right_of_mem_left A B ((inrMap A B).toElement y')
                  (h (left_bot_mem_inlMap_toElement A B x))
                  (right_bot_mem_inrMap_toElement A B y')
          | inr y =>
            cases s₂ with
            | inl x' =>
              exact False.elim <|
                not_mem_right_of_mem_left A B ((inlMap A B).toElement x')
                  (left_bot_mem_inlMap_toElement A B x')
                  (h (right_bot_mem_inrMap_toElement A B y))
            | inr y' => exact Sum.inr_le_inr_iff.2 ((inrMap_toElement_le_iff A B).1 h)
    · exact assembleSum_mono A B

/-! ## Function space `|A → B| ≃o ApproximableMap A B` -/

/-- Pointwise relation order on approximable maps (Prop 5.3 `Le`). -/
instance instPartialOrderApproximableMap : PartialOrder (ApproximableMap A B) where
  le := @Le _ _ _ _ A B
  le_refl _ _ _ h := h
  le_trans _ _ _ hfg hgh _ _ hf := hgh (hfg hf)
  le_antisymm _ _ hfg hgf := ApproximableMap.ext fun _ _ => ⟨fun h => hfg h, fun h => hgf h⟩

theorem approxMap_toElement_le_iff {f g : ApproximableMap A B} :
    approxMap_toElement A B f ≤ approxMap_toElement A B g ↔ f ≤ g := by
  constructor
  · intro h u v hrel
    have hp : mkFunToken A B u v (f.rel_dom hrel) (f.rel_cod hrel) ∈
        (approxMap_toElement A B f).carrier :=
      (mem_approxMap_toElement A B f).2 hrel
    exact (mem_approxMap_toElement A B g).1 (h hp)
  · intro hfg p hp
    exact (mem_approxMap_toElement A B g).2 (hfg ((mem_approxMap_toElement A B f).1 hp))

/-- **Function-space domain iso (1982, Thm 7.2).** `|A → B| ≃o ApproximableMap A B`. -/
noncomputable def functionSpaceDomainIso :
    ApproximableMap A B ≃o (functionSystem A B).Element where
  toFun := approxMap_toElement A B
  invFun := element_toApproxMap A B
  left_inv := element_toApproxMap_approxMap_toElement A B
  right_inv := approxMap_toElement_element_toApproxMap A B
  map_rel_iff' := by
    intro f g
    exact approxMap_toElement_le_iff A B

end InfoSysConstructions

/-- Blueprint-facing name for the 1982 product domain isomorphism. -/
noncomputable abbrev infoSys_product_domain_equiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) :
    A.Element × B.Element ≃o (productSystem A B).Element :=
  InfoSysConstructions.productDomainIso A B

/-- Blueprint-facing name for the 1982 separated-sum domain isomorphism (classical). -/
noncomputable abbrev infoSys_sum_domain_equiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) :
    WithBot (A.Element ⊕ B.Element) ≃o (sumSystem A B).Element :=
  InfoSysConstructions.sumDomainIso A B

/-- Blueprint-facing name for the 1982 function-space domain isomorphism. -/
noncomputable abbrev infoSys_function_space_domain_equiv {α β : Type*}
    [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β) :
    ApproximableMap A B ≃o (functionSystem A B).Element :=
  InfoSysConstructions.functionSpaceDomainIso A B

end ScottModels

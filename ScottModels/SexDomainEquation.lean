/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott_models
-/

import Mathlib.Order.Hom.Basic
import Scott1982.Factoid81

/-!
# Domain equation `|T| ≃o |A + (T × T)|` via unfolding

Factoid 8.1 presents `T` as an inductive token system whose official
right-hand side is `sumSystem A (productSystem T T)`. The token map
`treeUnfold` is a retraction, identifying only Scott’s two encodings of
the product bottom (`pairL Δ` and `pairR Δ`). After the matching
`ent_bot` clauses, closed elements are saturated for that kernel, so
image and preimage of `treeUnfold` are inverse order isomorphisms of
domains.
-/

namespace ScottModels

open Scott1982
open Scott1982.Constructive
open Scott1982.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

/-- Official product of the tree system with itself. -/
abbrev TreeProd : InfoSys (ProdToken (treeSystem A) (treeSystem A)) :=
  productSystem (treeSystem A) (treeSystem A)

/-- Canonical section of `treeUnfold`. Product bottom folds to `pairL bot`. -/
def treeFold :
    SumToken α (ProdToken (treeSystem A) (treeSystem A)) → TreeToken α
  | .bot => .bot
  | .left x => .atom x
  | .right p =>
      if p.val.2 = treeBot then .pairL p.val.1 else .pairR p.val.2

theorem treeUnfold_treeFold (s : SumToken α (ProdToken (treeSystem A) (treeSystem A))) :
    treeUnfold A (treeFold A s) = s := by
  cases s with
  | bot => rfl
  | left x => rfl
  | right p =>
    dsimp [treeFold, treeUnfold]
    split_ifs with hb
    · apply congrArg SumToken.right
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact hb.symm
    · have ha : p.val.1 = treeBot := by
        rcases p.property with h1 | h2
        · exact h1
        · exact False.elim (hb h2)
      apply congrArg SumToken.right
      apply Subtype.ext
      apply Prod.ext
      · exact ha.symm
      · rfl

theorem treeFold_eq_or_pairBots (t : TreeToken α) :
    treeFold A (treeUnfold A t) = t ∨
      t = .pairR .bot ∧ treeFold A (treeUnfold A t) = .pairL .bot := by
  cases t with
  | bot => exact Or.inl rfl
  | atom x => exact Or.inl rfl
  | pairL t =>
    refine Or.inl ?_
    simp [treeFold, treeUnfold, treeBot]
  | pairR t =>
    simp only [treeFold, treeUnfold, treeBot]
    split_ifs with hb
    · cases t with
      | bot => exact Or.inr ⟨rfl, rfl⟩
      | atom _ | pairL _ | pairR _ => exact False.elim (nomatch hb)
    · exact Or.inl rfl

private def unfoldInsert (t : TreeToken α) :
    Finset (SumToken α (ProdToken (treeSystem A) (treeSystem A))) →
      Finset (SumToken α (ProdToken (treeSystem A) (treeSystem A))) :=
  insert (treeUnfold A t)

private instance : LeftCommutative (unfoldInsert (A := A)) :=
  ⟨fun p q s => insert_comm' (treeUnfold A p) (treeUnfold A q) s⟩

/-- Choice-free image of a tree finset under `treeUnfold`. -/
def unfoldFinset (u : Finset (TreeToken α)) :
    Finset (SumToken α (ProdToken (treeSystem A) (treeSystem A))) :=
  Multiset.foldr (unfoldInsert A) ∅ u.1

private theorem mem_foldr_unfold (m : Multiset (TreeToken α))
    (s : SumToken α (ProdToken (treeSystem A) (treeSystem A))) :
    s ∈ Multiset.foldr (unfoldInsert A) ∅ m ↔
      ∃ t ∈ m, treeUnfold A t = s := by
  refine Multiset.induction_on m ?_ ?_
  · constructor
    · intro hs; exact False.elim (Finset.notMem_empty s hs)
    · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
  · intro t rest ih
    simp only [Multiset.foldr_cons, unfoldInsert, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (h | ⟨q, hq, hq'⟩)
      · exact ⟨t, Or.inl rfl, h.symm⟩
      · exact ⟨q, Or.inr hq, hq'⟩
    · rintro ⟨q, hq, hq'⟩
      rcases hq with rfl | hq
      · exact Or.inl hq'.symm
      · exact Or.inr ⟨q, hq, hq'⟩

theorem mem_unfoldFinset {u : Finset (TreeToken α)}
    {s : SumToken α (ProdToken (treeSystem A) (treeSystem A))} :
    s ∈ unfoldFinset A u ↔ ∃ t ∈ u, treeUnfold A t = s := by
  unfold unfoldFinset
  rw [mem_foldr_unfold]
  simp only [Finset.mem_def]

private def foldInsert (s : SumToken α (ProdToken (treeSystem A) (treeSystem A))) :
    Finset (TreeToken α) → Finset (TreeToken α) :=
  insert (treeFold A s)

private instance : LeftCommutative (foldInsert (A := A)) :=
  ⟨fun p q t => insert_comm' (treeFold A p) (treeFold A q) t⟩

/-- Choice-free image of an RHS finset under `treeFold`. -/
def foldFinset (Y : Finset (SumToken α (ProdToken (treeSystem A) (treeSystem A)))) :
    Finset (TreeToken α) :=
  Multiset.foldr (foldInsert A) ∅ Y.1

private theorem mem_foldr_fold
    (m : Multiset (SumToken α (ProdToken (treeSystem A) (treeSystem A))))
    (t : TreeToken α) :
    t ∈ Multiset.foldr (foldInsert A) ∅ m ↔
      ∃ s ∈ m, treeFold A s = t := by
  refine Multiset.induction_on m ?_ ?_
  · constructor
    · intro ht; exact False.elim (Finset.notMem_empty t ht)
    · rintro ⟨_, hp, _⟩; exact False.elim (by cases hp)
  · intro s rest ih
    simp only [Multiset.foldr_cons, foldInsert, Finset.mem_insert, ih, Multiset.mem_cons]
    constructor
    · rintro (h | ⟨q, hq, hq'⟩)
      · exact ⟨s, Or.inl rfl, h.symm⟩
      · exact ⟨q, Or.inr hq, hq'⟩
    · rintro ⟨q, hq, hq'⟩
      rcases hq with rfl | hq
      · exact Or.inl hq'.symm
      · exact Or.inr ⟨q, hq, hq'⟩

theorem mem_foldFinset
    {Y : Finset (SumToken α (ProdToken (treeSystem A) (treeSystem A)))}
    {t : TreeToken α} :
    t ∈ foldFinset A Y ↔ ∃ s ∈ Y, treeFold A s = t := by
  unfold foldFinset
  rw [mem_foldr_fold]
  simp only [Finset.mem_def]

theorem unfoldFinset_foldFinset
    (Y : Finset (SumToken α (ProdToken (treeSystem A) (treeSystem A)))) :
    unfoldFinset A (foldFinset A Y) = Y := by
  ext s
  constructor
  · intro hs
    rcases (mem_unfoldFinset A).1 hs with ⟨t, ht, hU⟩
    rcases (mem_foldFinset A).1 ht with ⟨s', hs', rfl⟩
    rw [treeUnfold_treeFold] at hU
    rwa [← hU]
  · intro hs
    exact (mem_unfoldFinset A).2 ⟨treeFold A s,
      (mem_foldFinset A).2 ⟨s, hs, rfl⟩, treeUnfold_treeFold A s⟩

theorem lftFinset_image_unfold (u : Finset (TreeToken α)) :
    lftFinset (unfoldFinset A u) = atomFinset u := by
  ext x
  constructor
  · intro hx
    have : SumToken.left x ∈ unfoldFinset A u := (mem_lftFinset).1 hx
    rcases (mem_unfoldFinset A).1 this with ⟨t, ht, hU⟩
    cases t with
    | atom y =>
      have : y = x := SumToken.left.inj hU
      subst this
      exact mem_atomFinset.2 ht
    | bot | pairL _ | pairR _ => exact nomatch hU
  · intro hx
    exact (mem_lftFinset).2
      ((mem_unfoldFinset A).2 ⟨.atom x, mem_atomFinset.1 hx, rfl⟩)

theorem rhtFinset_image_unfold_mem (u : Finset (TreeToken α))
    (y : ProdToken (treeSystem A) (treeSystem A)) :
    y ∈ rhtFinset (unfoldFinset A u) ↔
      (∃ t, .pairL t ∈ u ∧ y = ⟨(t, treeBot), Or.inr rfl⟩) ∨
        (∃ t, .pairR t ∈ u ∧ y = ⟨(treeBot, t), Or.inl rfl⟩) := by
  constructor
  · intro hy
    have : SumToken.right y ∈ unfoldFinset A u := (mem_rhtFinset).1 hy
    rcases (mem_unfoldFinset A).1 this with ⟨t, ht, hU⟩
    cases t with
    | pairL s =>
      refine Or.inl ⟨s, ht, ?_⟩
      exact SumToken.right.inj hU.symm
    | pairR s =>
      refine Or.inr ⟨s, ht, ?_⟩
      exact SumToken.right.inj hU.symm
    | bot | atom _ => exact nomatch hU
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact (mem_rhtFinset).2 ((mem_unfoldFinset A).2 ⟨.pairL t, ht, rfl⟩)
    · exact (mem_rhtFinset).2 ((mem_unfoldFinset A).2 ⟨.pairR t, ht, rfl⟩)

theorem TreeCon_image_sumCon {u : Finset (TreeToken α)} (hu : TreeCon A u) :
    SumCon A (TreeProd A) (unfoldFinset A u) := by
  cases hu with
  | left _ hA hL hR =>
    refine Or.inl ⟨?_, ?_⟩
    · rw [lftFinset_image_unfold]; exact hA
    · ext y
      constructor
      · intro hy
        rcases (rhtFinset_image_unfold_mem A u y).1 hy with ⟨t, ht, _⟩ | ⟨t, ht, _⟩
        · exact False.elim (Finset.notMem_empty t (hL ▸ mem_pairLFinset.2 ht))
        · exact False.elim (Finset.notMem_empty t (hR ▸ mem_pairRFinset.2 ht))
      · intro hy
        exact False.elim (Finset.notMem_empty y hy)
  | right _ hA hL hR =>
    refine Or.inr ⟨?_, ?_⟩
    · rw [lftFinset_image_unfold]; exact hA
    · refine ⟨?_, ?_⟩
      · -- fst of the product tokens is a TreeCon set (pairL, plus bot if needed)
        have hsub :
            fstFinset (treeSystem A) (treeSystem A)
                (rhtFinset (unfoldFinset A u)) ⊆
              insert .bot (pairLFinset u) := by
          intro t ht
          rcases (mem_fstFinset (treeSystem A) (treeSystem A)).1 ht with ⟨p, hp, hb, rfl⟩
          rcases (rhtFinset_image_unfold_mem A u p).1 hp with ⟨s, hs, hp'⟩ | ⟨s, hs, hp'⟩
          · subst hp'
            exact Finset.mem_insert_of_mem (mem_pairLFinset.2 hs)
          · subst hp'
            exact Finset.mem_insert_self _ _
        exact (treeSystem A).con_subset (TreeCon_insert_bot A hL) hsub
      · have hsub :
            sndFinset (treeSystem A) (treeSystem A)
                (rhtFinset (unfoldFinset A u)) ⊆
              insert .bot (pairRFinset u) := by
          intro t ht
          rcases (mem_sndFinset (treeSystem A) (treeSystem A)).1 ht with ⟨p, hp, ha, rfl⟩
          rcases (rhtFinset_image_unfold_mem A u p).1 hp with ⟨s, hs, hp'⟩ | ⟨s, hs, hp'⟩
          · subst hp'
            exact Finset.mem_insert_self _ _
          · subst hp'
            exact Finset.mem_insert_of_mem (mem_pairRFinset.2 hs)
        exact (treeSystem A).con_subset (TreeCon_insert_bot A hR) hsub

theorem SumCon_image_treeCon {u : Finset (TreeToken α)}
    (hu : SumCon A (TreeProd A) (unfoldFinset A u)) : TreeCon A u := by
  rcases hu with ⟨hL, hr⟩ | ⟨hl, hR⟩
  · refine TreeCon.left _ (by rwa [lftFinset_image_unfold] at hL) ?_ ?_
    · ext t
      constructor
      · intro ht
        have : (⟨(t, treeBot), Or.inr rfl⟩ : ProdToken (treeSystem A) (treeSystem A)) ∈
            rhtFinset (unfoldFinset A u) :=
          (rhtFinset_image_unfold_mem A u _).2 (Or.inl ⟨t, mem_pairLFinset.1 ht, rfl⟩)
        rw [hr] at this
        exact False.elim (Finset.notMem_empty _ this)
      · intro ht
        exact False.elim (Finset.notMem_empty t ht)
    · ext t
      constructor
      · intro ht
        have : (⟨(treeBot, t), Or.inl rfl⟩ : ProdToken (treeSystem A) (treeSystem A)) ∈
            rhtFinset (unfoldFinset A u) :=
          (rhtFinset_image_unfold_mem A u _).2 (Or.inr ⟨t, mem_pairRFinset.1 ht, rfl⟩)
        rw [hr] at this
        exact False.elim (Finset.notMem_empty _ this)
      · intro ht
        exact False.elim (Finset.notMem_empty t ht)
  · refine TreeCon.right _ (by rwa [lftFinset_image_unfold] at hl) ?_ ?_
    · have hsub : pairLFinset u ⊆
          fstFinset (treeSystem A) (treeSystem A)
            (rhtFinset (unfoldFinset A u)) := by
        intro t ht
        exact (mem_fstFinset (treeSystem A) (treeSystem A)).2
          ⟨⟨(t, treeBot), Or.inr rfl⟩,
            (rhtFinset_image_unfold_mem A u _).2 (Or.inl ⟨t, mem_pairLFinset.1 ht, rfl⟩),
            rfl, rfl⟩
      exact (treeSystem A).con_subset hR.1 hsub
    · have hsub : pairRFinset u ⊆
          sndFinset (treeSystem A) (treeSystem A)
            (rhtFinset (unfoldFinset A u)) := by
        intro t ht
        exact (mem_sndFinset (treeSystem A) (treeSystem A)).2
          ⟨⟨(treeBot, t), Or.inl rfl⟩,
            (rhtFinset_image_unfold_mem A u _).2 (Or.inr ⟨t, mem_pairRFinset.1 ht, rfl⟩),
            rfl, rfl⟩
      exact (treeSystem A).con_subset hR.2 hsub

theorem TreeEnt_sumEnt {u : Finset (TreeToken α)} {p : TreeToken α}
    (h : TreeEnt A u p) :
    SumEnt A (TreeProd A) (unfoldFinset A u) (treeUnfold A p) := by
  have hCon : SumCon A (TreeProd A) (unfoldFinset A u) :=
    TreeCon_image_sumCon A h.1
  refine ⟨hCon, ?_⟩
  cases p with
  | bot => exact trivial
  | atom x =>
    refine ⟨?_, ?_⟩
    · rw [lftFinset_image_unfold]; exact h.2.1
    · rw [lftFinset_image_unfold]; exact h.2.2
  | pairL t =>
    have hr : rhtFinset (unfoldFinset A u) ≠ ∅ := by
      rcases h.2.2.2.2 with ⟨hne, _⟩ | ⟨_, hR⟩
      · obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hne
        exact Finset.ne_empty_of_mem
          ((rhtFinset_image_unfold_mem A u _).2
            (Or.inl ⟨s, mem_pairLFinset.1 hs, rfl⟩))
      · obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hR
        exact Finset.ne_empty_of_mem
          ((rhtFinset_image_unfold_mem A u _).2
            (Or.inr ⟨s, mem_pairRFinset.1 hs, rfl⟩))
    refine ⟨hr, ?_⟩
    refine ⟨hCon.elim (fun hL => False.elim (hr hL.2)) (fun hR => hR.2), ?_, ?_⟩
    · intro
      -- T.Ent fst t
      have hsub : pairLFinset u ⊆
          fstFinset (treeSystem A) (treeSystem A)
            (rhtFinset (unfoldFinset A u)) := by
        intro s hs
        exact (mem_fstFinset (treeSystem A) (treeSystem A)).2
          ⟨⟨(s, treeBot), Or.inr rfl⟩,
            (rhtFinset_image_unfold_mem A u _).2 (Or.inl ⟨s, mem_pairLFinset.1 hs, rfl⟩),
            rfl, rfl⟩
      have hFstCon : fstFinset (treeSystem A) (treeSystem A)
          (rhtFinset (unfoldFinset A u)) ∈ (treeSystem A).Con :=
        hCon.elim (fun hL => False.elim (hr hL.2)) (fun hR => hR.2.1)
      rcases h.2.2.2.2 with ⟨hne, hPay⟩ | ⟨rfl, _⟩
      · exact (treeSystem A).ent_trans hFstCon h.2.2.1
          (fun y hy => (treeSystem A).ent_refl hFstCon (hsub hy)) ⟨h.2.2.1, hPay⟩
      · exact (treeSystem A).ent_bot hFstCon
    · intro ht
      have hSndCon : sndFinset (treeSystem A) (treeSystem A)
          (rhtFinset (unfoldFinset A u)) ∈ (treeSystem A).Con :=
        hCon.elim (fun hL => False.elim (hr hL.2)) (fun hR => hR.2.2)
      exact (treeSystem A).ent_bot hSndCon

  | pairR t =>
    have hr : rhtFinset (unfoldFinset A u) ≠ ∅ := by
      rcases h.2.2.2.2 with ⟨hne, _⟩ | ⟨_, hL⟩
      · obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hne
        exact Finset.ne_empty_of_mem
          ((rhtFinset_image_unfold_mem A u _).2
            (Or.inr ⟨s, mem_pairRFinset.1 hs, rfl⟩))
      · obtain ⟨s, hs⟩ := Finset.nonempty_of_ne_empty hL
        exact Finset.ne_empty_of_mem
          ((rhtFinset_image_unfold_mem A u _).2
            (Or.inl ⟨s, mem_pairLFinset.1 hs, rfl⟩))
    refine ⟨hr, ?_⟩
    refine ⟨hCon.elim (fun hL => False.elim (hr hL.2)) (fun hR => hR.2), ?_, ?_⟩
    · intro
      have hFstCon : fstFinset (treeSystem A) (treeSystem A)
          (rhtFinset (unfoldFinset A u)) ∈ (treeSystem A).Con :=
        hCon.elim (fun hL => False.elim (hr hL.2)) (fun hR => hR.2.1)
      exact (treeSystem A).ent_bot hFstCon
    · intro
      have hsub : pairRFinset u ⊆
          sndFinset (treeSystem A) (treeSystem A)
            (rhtFinset (unfoldFinset A u)) := by
        intro s hs
        exact (mem_sndFinset (treeSystem A) (treeSystem A)).2
          ⟨⟨(treeBot, s), Or.inl rfl⟩,
            (rhtFinset_image_unfold_mem A u _).2 (Or.inr ⟨s, mem_pairRFinset.1 hs, rfl⟩),
            rfl, rfl⟩
      have hSndCon : sndFinset (treeSystem A) (treeSystem A)
          (rhtFinset (unfoldFinset A u)) ∈ (treeSystem A).Con :=
        hCon.elim (fun hL => False.elim (hr hL.2)) (fun hR => hR.2.2)
      rcases h.2.2.2.2 with ⟨hne, hPay⟩ | ⟨rfl, _⟩
      · exact (treeSystem A).ent_trans hSndCon h.2.2.1
          (fun y hy => (treeSystem A).ent_refl hSndCon (hsub hy)) ⟨h.2.2.1, hPay⟩
      · exact (treeSystem A).ent_bot hSndCon

theorem SumEnt_treeFold {u : Finset (TreeToken α)}
    {s : SumToken α (ProdToken (treeSystem A) (treeSystem A))}
    (h : SumEnt A (TreeProd A) (unfoldFinset A u) s) :
    TreeEnt A u (treeFold A s) := by
  have hu : TreeCon A u := SumCon_image_treeCon A h.1
  refine ⟨hu, ?_⟩
  cases s with
  | bot => exact trivial
  | left x =>
    dsimp [treeFold]
    refine ⟨?_, ?_⟩
    · rw [← lftFinset_image_unfold A u]; exact h.2.1
    · rw [← lftFinset_image_unfold A u]; exact h.2.2
  | right p =>
    dsimp [treeFold]
    have hAt : atomFinset u = ∅ := by
      have hl := (lftFinset_image_unfold A u)
      have : lftFinset (unfoldFinset A u) = ∅ :=
        SumCon_lft_empty_of_rht_nonempty A (TreeProd A) h.1 h.2.1
      rwa [hl] at this
    split_ifs with hb
    · refine ⟨hAt, TreeCon_pairL_of_right A hu hAt, TreeCon_pairR_of_right A hu hAt, ?_⟩
      have hEnt := h.2.2
      -- ProdEnt: Ent fst p.1 (since p.2 = bot)
      have hFst : (treeSystem A).Ent
          (fstFinset (treeSystem A) (treeSystem A)
            (rhtFinset (unfoldFinset A u))) p.val.1 :=
        hEnt.2.1 hb
      have hsub :
          fstFinset (treeSystem A) (treeSystem A)
              (rhtFinset (unfoldFinset A u)) ⊆
            insert .bot (pairLFinset u) := by
        intro t ht
        rcases (mem_fstFinset (treeSystem A) (treeSystem A)).1 ht with ⟨q, hq, _, rfl⟩
        rcases (rhtFinset_image_unfold_mem A u q).1 hq with ⟨w, hw, hq'⟩ | ⟨w, hw, hq'⟩
        · subst hq'; exact Finset.mem_insert_of_mem (mem_pairLFinset.2 hw)
        · subst hq'; exact Finset.mem_insert_self _ _
      -- Transfer Ent along the subset into pairL ∪ {bot}
      have hIns : TreeCon A (insert .bot (pairLFinset u)) :=
        TreeCon_insert_bot A (TreeCon_pairL_of_right A hu hAt)
      have hPay : TreeEntPayload A (insert .bot (pairLFinset u)) p.val.1 :=
        ((treeSystem A).ent_trans hIns
          (SumCon_rht_con_of_rht_nonempty A (TreeProd A) h.1 h.2.1).1
          (fun y hy => (treeSystem A).ent_refl hIns (hsub hy)) hFst).2
      obtain ⟨y, hy⟩ := Finset.nonempty_of_ne_empty h.2.1
      rcases (rhtFinset_image_unfold_mem A u y).1 hy with ⟨w, hwL, _⟩ | ⟨w, hwR, _⟩
      · refine Or.inl ⟨Finset.ne_empty_of_mem (mem_pairLFinset.2 hwL), ?_⟩
        exact ((treeSystem A).ent_trans (TreeCon_pairL_of_right A hu hAt) hIns
          (fun z hz => by
            rw [Finset.mem_insert] at hz
            rcases hz with rfl | hz
            · exact (treeSystem A).ent_bot (TreeCon_pairL_of_right A hu hAt)
            · exact (treeSystem A).ent_refl (TreeCon_pairL_of_right A hu hAt) hz)
          ⟨hIns, hPay⟩).2
      · if ht : p.val.1 = .bot then
          exact Or.inr ⟨ht, Finset.ne_empty_of_mem (mem_pairRFinset.2 hwR)⟩
        else
          refine Or.inl ⟨?_, ?_⟩
          · intro hempty
            have hEq : insert (.bot : TreeToken α) (pairLFinset u) = {.bot} := by
              rw [hempty]; rfl
            exact ht (TreeEntPayload_of_no_atoms_no_pairs A
              atomFinset_singleton_bot pairLFinset_singleton_bot
              pairRFinset_singleton_bot (hEq ▸ hPay))
          · exact ((treeSystem A).ent_trans (TreeCon_pairL_of_right A hu hAt) hIns
              (fun z hz => by
                rw [Finset.mem_insert] at hz
                rcases hz with rfl | hz
                · exact (treeSystem A).ent_bot (TreeCon_pairL_of_right A hu hAt)
                · exact (treeSystem A).ent_refl (TreeCon_pairL_of_right A hu hAt) hz)
              ⟨hIns, hPay⟩).2
    · -- pairR p.2
      refine ⟨hAt, TreeCon_pairR_of_right A hu hAt, TreeCon_pairL_of_right A hu hAt, ?_⟩
      have ha : p.val.1 = treeBot := by
        rcases p.property with h1 | h2
        · exact h1
        · exact False.elim (hb h2)
      have hEnt := h.2.2
      have hSnd : (treeSystem A).Ent
          (sndFinset (treeSystem A) (treeSystem A)
            (rhtFinset (unfoldFinset A u))) p.val.2 :=
        hEnt.2.2 ha
      have hIns : TreeCon A (insert .bot (pairRFinset u)) :=
        TreeCon_insert_bot A (TreeCon_pairR_of_right A hu hAt)
      have hsub :
          sndFinset (treeSystem A) (treeSystem A)
              (rhtFinset (unfoldFinset A u)) ⊆
            insert .bot (pairRFinset u) := by
        intro t ht
        rcases (mem_sndFinset (treeSystem A) (treeSystem A)).1 ht with ⟨q, hq, _, rfl⟩
        rcases (rhtFinset_image_unfold_mem A u q).1 hq with ⟨w, hw, hq'⟩ | ⟨w, hw, hq'⟩
        · subst hq'; exact Finset.mem_insert_self _ _
        · subst hq'; exact Finset.mem_insert_of_mem (mem_pairRFinset.2 hw)
      have hPay : TreeEntPayload A (insert .bot (pairRFinset u)) p.val.2 :=
        ((treeSystem A).ent_trans hIns
          (SumCon_rht_con_of_rht_nonempty A (TreeProd A) h.1 h.2.1).2
          (fun y hy => (treeSystem A).ent_refl hIns (hsub hy)) hSnd).2
      refine Or.inl ⟨?_, ?_⟩
      · intro hempty
        have hEq : insert (.bot : TreeToken α) (pairRFinset u) = {.bot} := by
          rw [hempty]; rfl
        have ht : p.val.2 = .bot :=
          TreeEntPayload_of_no_atoms_no_pairs A
            atomFinset_singleton_bot pairLFinset_singleton_bot
            pairRFinset_singleton_bot (hEq ▸ hPay)
        exact hb (ht ▸ rfl)
      · exact ((treeSystem A).ent_trans (TreeCon_pairR_of_right A hu hAt) hIns
          (fun z hz => by
            rw [Finset.mem_insert] at hz
            rcases hz with rfl | hz
            · exact (treeSystem A).ent_bot (TreeCon_pairR_of_right A hu hAt)
            · exact (treeSystem A).ent_refl (TreeCon_pairR_of_right A hu hAt) hz)
          ⟨hIns, hPay⟩).2

theorem TreeEnt_pairL_bot_of_pairs {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (h : pairLFinset u ≠ ∅ ∨ pairRFinset u ≠ ∅) :
    TreeEnt A u (.pairL .bot) :=
  ⟨hu, TreeCon_atoms_empty_of_right A hu h,
    TreeCon_pairL_of_right A hu (TreeCon_atoms_empty_of_right A hu h),
    TreeCon_pairR_of_right A hu (TreeCon_atoms_empty_of_right A hu h),
    h.elim (fun hL => Or.inl ⟨hL, trivial⟩) (fun hR => Or.inr ⟨rfl, hR⟩)⟩

theorem TreeEnt_pairR_bot_of_pairs {u : Finset (TreeToken α)}
    (hu : TreeCon A u) (h : pairLFinset u ≠ ∅ ∨ pairRFinset u ≠ ∅) :
    TreeEnt A u (.pairR .bot) :=
  ⟨hu, TreeCon_atoms_empty_of_right A hu h,
    TreeCon_pairR_of_right A hu (TreeCon_atoms_empty_of_right A hu h),
    TreeCon_pairL_of_right A hu (TreeCon_atoms_empty_of_right A hu h),
    h.elim (fun hL => Or.inr ⟨rfl, hL⟩) (fun hR => Or.inl ⟨hR, trivial⟩)⟩

theorem mem_closed_pair_bots (x : (treeSystem A).Element) :
    .pairL .bot ∈ x.carrier ↔ .pairR .bot ∈ x.carrier := by
  constructor
  · intro h
    have hsub : (({TreeToken.pairL treeBot} : Finset (TreeToken α)) : Set _) ⊆
        x.carrier := by
      intro a ha
      have : a = .pairL treeBot := Finset.mem_singleton.mp (Finset.mem_coe.1 ha)
      subst this; exact h
    exact x.closed {TreeToken.pairL treeBot} (.pairR treeBot) hsub
      (TreeEnt_pairR_bot_of_pairs A (x.consistent _ hsub)
        (Or.inl (Finset.ne_empty_of_mem (by
          rw [pairLFinset_singleton_pairL]; exact Finset.mem_singleton_self _))))
  · intro h
    have hsub : (({TreeToken.pairR treeBot} : Finset (TreeToken α)) : Set _) ⊆
        x.carrier := by
      intro a ha
      have : a = .pairR treeBot := Finset.mem_singleton.mp (Finset.mem_coe.1 ha)
      subst this; exact h
    exact x.closed {TreeToken.pairR treeBot} (.pairL treeBot) hsub
      (TreeEnt_pairL_bot_of_pairs A (x.consistent _ hsub)
        (Or.inr (Finset.ne_empty_of_mem (by
          rw [pairRFinset_singleton_pairR]; exact Finset.mem_singleton_self _))))

theorem saturated_of_closed (x : (treeSystem A).Element) {t : TreeToken α}
    (ht : t ∈ x.carrier) : treeFold A (treeUnfold A t) ∈ x.carrier := by
  rcases treeFold_eq_or_pairBots A t with h | ⟨rfl, hf⟩
  · rwa [h]
  · rw [hf]
    exact (mem_closed_pair_bots A x).2 ht

/-- Image of a tree element under `treeUnfold` is an official RHS element. -/
def unfoldElement (x : (treeSystem A).Element) : (treeRhs A).Element where
  carrier := treeUnfold A '' x.carrier
  consistent := by
    intro Y hY
    have hFold : ↑(foldFinset A Y) ⊆ x.carrier := by
      intro t ht
      rcases (mem_foldFinset A).1 (Finset.mem_coe.1 ht) with ⟨s, hs, rfl⟩
      have hs' : s ∈ treeUnfold A '' x.carrier := hY (Finset.mem_coe.2 hs)
      rcases hs' with ⟨t', ht', hU⟩
      have : treeFold A (treeUnfold A t') ∈ x.carrier := saturated_of_closed A x ht'
      rwa [hU] at this
    have hCon : TreeCon A (foldFinset A Y) := x.consistent _ hFold
    have : SumCon A (TreeProd A) (unfoldFinset A (foldFinset A Y)) :=
      TreeCon_image_sumCon A hCon
    rwa [unfoldFinset_foldFinset] at this
  closed := by
    intro Y s hY hEnt
    have hFold : ↑(foldFinset A Y) ⊆ x.carrier := by
      intro t ht
      rcases (mem_foldFinset A).1 (Finset.mem_coe.1 ht) with ⟨s', hs', rfl⟩
      have hs'' : s' ∈ treeUnfold A '' x.carrier := hY (Finset.mem_coe.2 hs')
      rcases hs'' with ⟨t', ht', hU⟩
      have : treeFold A (treeUnfold A t') ∈ x.carrier := saturated_of_closed A x ht'
      rwa [hU] at this
    have hEnt' : SumEnt A (TreeProd A)
        (unfoldFinset A (foldFinset A Y)) s := by
      rwa [unfoldFinset_foldFinset]
    have hT : TreeEnt A (foldFinset A Y) (treeFold A s) :=
      SumEnt_treeFold A hEnt'
    have ht : treeFold A s ∈ x.carrier :=
      x.closed _ _ hFold hT
    refine ⟨treeFold A s, ht, treeUnfold_treeFold A s⟩

/-- Preimage of an official RHS element under `treeUnfold` is a tree element. -/
def foldElement (y : (treeRhs A).Element) : (treeSystem A).Element where
  carrier := treeUnfold A ⁻¹' y.carrier
  consistent := by
    intro Y hY
    have him : ↑(unfoldFinset A Y) ⊆ y.carrier := by
      intro s hs
      rcases (mem_unfoldFinset A).1 (Finset.mem_coe.1 hs) with ⟨t, ht, rfl⟩
      exact hY (Finset.mem_coe.2 ht)
    have : SumCon A (TreeProd A) (unfoldFinset A Y) := y.consistent _ him
    exact SumCon_image_treeCon A this
  closed := by
    intro Y p hY hEnt
    have him : ↑(unfoldFinset A Y) ⊆ y.carrier := by
      intro s hs
      rcases (mem_unfoldFinset A).1 (Finset.mem_coe.1 hs) with ⟨t, ht, rfl⟩
      exact hY (Finset.mem_coe.2 ht)
    have hS : SumEnt A (TreeProd A) (unfoldFinset A Y) (treeUnfold A p) :=
      TreeEnt_sumEnt A hEnt
    exact y.closed _ _ him hS

theorem unfoldElement_foldElement (y : (treeRhs A).Element) :
    unfoldElement A (foldElement A y) = y := by
  refine le_antisymm ?_ ?_
  · intro s hs
    rcases hs with ⟨t, ht, rfl⟩
    exact ht
  · intro s hs
    refine ⟨treeFold A s, ?_, treeUnfold_treeFold A s⟩
    change treeUnfold A (treeFold A s) ∈ y.carrier
    rwa [treeUnfold_treeFold]

theorem foldElement_unfoldElement (x : (treeSystem A).Element) :
    foldElement A (unfoldElement A x) = x := by
  refine le_antisymm ?_ ?_
  · intro t ht
    rcases ht with ⟨t', ht', hU⟩
    have : treeFold A (treeUnfold A t') ∈ x.carrier := saturated_of_closed A x ht'
    have hft : treeFold A (treeUnfold A t) ∈ x.carrier := by
      rwa [hU] at this
    rcases treeFold_eq_or_pairBots A t with h | ⟨rfl, hf⟩
    · rwa [h] at hft
    · exact (mem_closed_pair_bots A x).1 (by rwa [hf] at hft)
  · intro t ht
    exact ⟨t, ht, rfl⟩

/-- **Factoid 8.1 at domain level.** `|T| ≃o |A + (T × T)|` via `treeUnfold`. -/
def treeDomainIso : (treeSystem A).Element ≃o (treeRhs A).Element where
  toFun := unfoldElement A
  invFun := foldElement A
  left_inv := foldElement_unfoldElement A
  right_inv := unfoldElement_foldElement A
  map_rel_iff' := by
    intro x₁ x₂
    constructor
    · intro h t ht
      have : treeUnfold A t ∈ (unfoldElement A x₁).carrier := ⟨t, ht, rfl⟩
      have : treeUnfold A t ∈ (unfoldElement A x₂).carrier := h this
      have : t ∈ (foldElement A (unfoldElement A x₂)).carrier := this
      rwa [foldElement_unfoldElement] at this
    · intro h s hs
      rcases hs with ⟨t, ht, rfl⟩
      exact ⟨t, h ht, rfl⟩

end ScottModels

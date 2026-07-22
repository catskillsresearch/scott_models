/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott_models
-/

import Mathlib.Order.Hom.Basic
import Scott1980.Neighborhood.Basic
import Scott1982.Factoid35
import Scott1982.Factoid46
import Scott1982.Proposition23

/-!
# Information systems → neighbourhood systems (1982 → 1980)

Scott (1982, §4): for `u ∈ Con`, the basic open
`[u] = { x ∈ |A| | u ⊆ x }` yields a neighbourhood system on the domain `|A|`
whose filters recover the original elements. This is the converse direction to
`NeighborhoodToInfoSys`.
-/

namespace ScottModels

open Scott1980.Neighborhood
open Scott1982
open Scott1982.Constructive
open Scott1982.InfoSys

namespace InfoSysToNeighborhood

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem basicOpen_empty : A.basicOpen (∅ : Finset α) = (Set.univ : Set A.Element) := by
  ext x
  constructor
  · intro; trivial
  · intro _ a ha
    exact False.elim (Finset.notMem_empty a (Finset.mem_coe.1 ha))

theorem mem_basicOpen_singleton {a : α} {x : A.Element} :
    x ∈ A.basicOpen ({a} : Finset α) ↔ a ∈ x.carrier := by
  constructor
  · intro h
    exact h (Finset.mem_coe.2 (Finset.mem_singleton_self a))
  · intro ha b hb
    have hb' : b = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
    exact hb' ▸ ha

theorem funion_singleton_eq_insert (a : α) (s : Finset α) :
    ({a} : Finset α) ∪' s = insert a s := by
  ext x
  constructor
  · intro hx
    rcases mem_funion.mp hx with h | h
    · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp h))
    · exact Finset.mem_insert_of_mem h
  · intro hx
    rcases Finset.mem_insert.mp hx with h | h
    · exact mem_funion.mpr (Or.inl (h ▸ Finset.mem_singleton_self a))
    · exact mem_funion.mpr (Or.inr h)

theorem basicOpen_singleton_inter (a : α) (s : Finset α) :
    A.basicOpen ({a} : Finset α) ∩ A.basicOpen s = A.basicOpen (insert a s) := by
  rw [basicOpen_inter A, funion_singleton_eq_insert]

theorem ent_of_basicOpen_subset {u w : Finset α} (hw : w ∈ A.Con)
    (hsub : A.basicOpen w ⊆ A.basicOpen u) {a : α} (ha : a ∈ u) : A.Ent w a := by
  have : A.closure w hw ∈ A.basicOpen w := subset_closure A hw
  have hU : A.closure w hw ∈ A.basicOpen u := hsub this
  exact hU (Finset.mem_coe.2 ha)

theorem con_of_basicOpen_subset {u w : Finset α} (hw : w ∈ A.Con)
    (hsub : A.basicOpen w ⊆ A.basicOpen u) : u ∈ A.Con := by
  have hEnt : A.EntSet w u := fun a ha => ent_of_basicOpen_subset A hw hsub ha
  exact A.con_subset (proposition_2_3_ii A hw hEnt) (subset_funion_right _ _)

/-- **`infoSys_to_neighborhoodSystem`.** -/
def toNeighborhoodSystem : NeighborhoodSystem A.Element where
  mem X := ∃ u, u ∈ A.Con ∧ X = A.basicOpen u
  master := Set.univ
  master_mem := ⟨∅, A.con_empty, (basicOpen_empty A).symm⟩
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    obtain ⟨u, hu, rfl⟩ := hX
    obtain ⟨v, hv, rfl⟩ := hY
    obtain ⟨w, hw, rfl⟩ := hZ
    have hsub : A.basicOpen w ⊆ A.basicOpen (u ∪' v) := by
      intro x hx
      have hx' : x ∈ A.basicOpen u ∩ A.basicOpen v := hZsub hx
      rwa [basicOpen_inter A] at hx'
    have huv : u ∪' v ∈ A.Con := con_of_basicOpen_subset A hw hsub
    exact ⟨u ∪' v, huv, basicOpen_inter A u v⟩
  sub_master := fun {_} _ => Set.subset_univ _

theorem mem_basicOpen_of_singletons (f : (toNeighborhoodSystem A).Element) {Y : Finset α}
    (hY : ∀ a ∈ Y, f.mem (A.basicOpen ({a} : Finset α))) :
    f.mem (A.basicOpen Y) := by
  induction Y using Finset.induction with
  | empty =>
    simpa [basicOpen_empty] using f.master_mem
  | insert a s _ha ih =>
    have hA := hY a (Finset.mem_insert_self a s)
    have hSm := ih fun i hi => hY i (Finset.mem_insert_of_mem hi)
    simpa [basicOpen_singleton_inter A a s] using f.inter_mem hA hSm

def toFilter (x : A.Element) : (toNeighborhoodSystem A).Element where
  mem U := ∃ u, u ∈ A.Con ∧ U = A.basicOpen u ∧ ↑u ⊆ x.carrier
  sub := by
    intro U h
    obtain ⟨u, hu, rfl, _⟩ := h
    exact ⟨u, hu, rfl⟩
  master_mem := ⟨∅, A.con_empty, (basicOpen_empty A).symm, by
    intro a ha
    exact False.elim (Finset.notMem_empty a (Finset.mem_coe.1 ha))⟩
  inter_mem := by
    intro U V hU hV
    obtain ⟨u, hu, rfl, huX⟩ := hU
    obtain ⟨v, hv, rfl, hvX⟩ := hV
    refine ⟨u ∪' v, ?_, basicOpen_inter A u v, ?_⟩
    · have hsub : ↑(u ∪' v) ⊆ x.carrier := by
        intro a ha
        rcases mem_funion.mp (Finset.mem_coe.1 ha) with h | h
        · exact huX (Finset.mem_coe.2 h)
        · exact hvX (Finset.mem_coe.2 h)
      exact x.consistent (u ∪' v) hsub
    · intro a ha
      rcases mem_funion.mp (Finset.mem_coe.1 ha) with h | h
      · exact huX (Finset.mem_coe.2 h)
      · exact hvX (Finset.mem_coe.2 h)
  up_mem := by
    intro U V hU hV hUV
    obtain ⟨u, hu, rfl, huX⟩ := hU
    obtain ⟨v, hv, rfl⟩ := hV
    refine ⟨v, hv, rfl, ?_⟩
    intro a ha
    exact x.closed u a huX (ent_of_basicOpen_subset A hu hUV ha)

def ofFilter (f : (toNeighborhoodSystem A).Element) : A.Element where
  carrier := {a | f.mem (A.basicOpen ({a} : Finset α))}
  consistent := by
    intro Y hY
    have hmem : f.mem (A.basicOpen Y) :=
      mem_basicOpen_of_singletons A f fun a ha => hY (Finset.mem_coe.2 ha)
    obtain ⟨u, hu, heq⟩ := f.sub hmem
    have hsub : A.basicOpen u ⊆ A.basicOpen Y := by
      intro x hx; exact heq ▸ hx
    exact con_of_basicOpen_subset A hu hsub
  closed := by
    intro Y b hY hEnt
    have hmemY : f.mem (A.basicOpen Y) :=
      mem_basicOpen_of_singletons A f fun c hc => hY (Finset.mem_coe.2 hc)
    have hsub : A.basicOpen Y ⊆ A.basicOpen ({b} : Finset α) := by
      intro x hx c hc
      have eqcb : c = b := Finset.mem_singleton.mp (Finset.mem_coe.1 hc)
      rw [eqcb]
      exact x.closed Y b hx hEnt
    exact f.up_mem hmemY ⟨({b} : Finset α), A.con_sing b, rfl⟩ hsub

theorem mem_basicOpen_iff (f : (toNeighborhoodSystem A).Element) {u : Finset α}
    (_hu : u ∈ A.Con) :
    f.mem (A.basicOpen u) ↔ ↑u ⊆ (ofFilter A f).carrier := by
  constructor
  · intro h a ha
    have hsub : A.basicOpen u ⊆ A.basicOpen ({a} : Finset α) := by
      intro x hx c hc
      have hc' : c = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hc)
      subst hc'
      exact hx (Finset.mem_coe.2 ha)
    exact f.up_mem h ⟨({a} : Finset α), A.con_sing a, rfl⟩ hsub
  · intro hsub
    exact mem_basicOpen_of_singletons A f fun a ha => hsub (Finset.mem_coe.2 ha)

theorem toFilter_ofFilter (f : (toNeighborhoodSystem A).Element) :
    toFilter A (ofFilter A f) = f := by
  refine NeighborhoodSystem.Element.ext (V := toNeighborhoodSystem A) fun U => ?_
  constructor
  · intro h
    obtain ⟨u, hu, hU, hsub⟩ := h
    subst hU
    exact (mem_basicOpen_iff A f hu).mpr hsub
  · intro hU
    obtain ⟨u, hu, heq⟩ := f.sub hU
    subst heq
    exact ⟨u, hu, rfl, (mem_basicOpen_iff A f hu).mp hU⟩

theorem ofFilter_toFilter (x : A.Element) : ofFilter A (toFilter A x) = x := by
  have hc : (ofFilter A (toFilter A x)).carrier = x.carrier := by
    ext a
    constructor
    · intro ha
      obtain ⟨u, hu, heq, hsub⟩ := ha
      have huA : A.closure u hu ∈ A.basicOpen u := subset_closure A hu
      have hsing : A.closure u hu ∈ A.basicOpen ({a} : Finset α) := by
        rw [heq]; exact huA
      have ha' : a ∈ (A.closure u hu).carrier := (mem_basicOpen_singleton A).1 hsing
      exact x.closed u a hsub ha'
    · intro ha
      refine ⟨({a} : Finset α), A.con_sing a, rfl, ?_⟩
      intro c hc
      have hc' : c = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hc)
      exact hc' ▸ ha
  rcases x with ⟨c, cons, clo⟩
  rcases hte : ofFilter A (toFilter A ⟨c, cons, clo⟩) with ⟨c', cons', clo'⟩
  have hc' : c' = c := by simpa [hte] using hc
  subst hc'
  rfl

def domainOrderIso : A.Element ≃o (toNeighborhoodSystem A).Element where
  toFun := toFilter A
  invFun := ofFilter A
  left_inv := ofFilter_toFilter A
  right_inv := toFilter_ofFilter A
  map_rel_iff' := by
    intro x y
    constructor
    · intro h a ha
      have hx : (toFilter A x).mem (A.basicOpen ({a} : Finset α)) :=
        ⟨({a} : Finset α), A.con_sing a, rfl, by
          intro c hc
          have hc' : c = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hc)
          exact hc' ▸ ha⟩
      have hy : (toFilter A y).mem (A.basicOpen ({a} : Finset α)) := h _ hx
      obtain ⟨u, hu, heq, hsub⟩ := hy
      have huA : A.closure u hu ∈ A.basicOpen u := subset_closure A hu
      have hsing : A.closure u hu ∈ A.basicOpen ({a} : Finset α) := by
        rw [heq]; exact huA
      have ha' : a ∈ (A.closure u hu).carrier := (mem_basicOpen_singleton A).1 hsing
      exact y.closed u a hsub ha'
    · intro h U hU
      obtain ⟨u, hu, hUeq, huX⟩ := hU
      subst hUeq
      exact ⟨u, hu, rfl, fun a ha => h (huX ha)⟩

end InfoSysToNeighborhood

/-- Blueprint-facing name for the 1982 → 1980 basic-open neighbourhood system. -/
abbrev infoSys_to_neighborhoodSystem {α : Type*} [DecidableEq α] (A : InfoSys α) :
    NeighborhoodSystem A.Element :=
  InfoSysToNeighborhood.toNeighborhoodSystem A

end ScottModels

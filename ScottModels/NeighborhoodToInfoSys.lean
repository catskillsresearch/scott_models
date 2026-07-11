import Mathlib.Data.Finset.Fold
import Mathlib.Order.Hom.Basic
import Scott1980.Neighborhood.Basic
import Scott1982.InfoSys
import Scott1982.Proposition23

/-!
# Neighbourhood systems → information systems (1980 → 1982)

Scott (1982) notes that neighbourhood systems and information systems are equivalent
in a precise sense. This module realises one direction: given a neighbourhood system
presented with a **decidable index of its neighbourhoods** (a constructive coding of
`𝒟`), build an information system on those indices whose domain is order-isomorphic
to the original filter domain.

Tokens of the information system are indices of neighbourhoods; consistency is
membership of the finite intersection in `𝒟` (Scott’s empty intersection = `Δ`);
entailment is “the intersection is a neighbourhood and is contained in the target.”
-/

namespace ScottModels

open Scott1980.Neighborhood
open Scott1982

/-- A neighbourhood system with a decidable exhaustive index of its neighbourhoods.
`DecidableEq ι` is required so the induced information system can use choice-free
`Finset` operations (`InfoSys` tokens). -/
structure NbhdBasis (ι α : Type*) [DecidableEq ι] where
  system : NeighborhoodSystem α
  nbhd : ι → Set α
  nbhd_mem : ∀ i, system.mem (nbhd i)
  exhaustive : ∀ {X : Set α}, system.mem X → ∃ i, nbhd i = X
  botIdx : ι
  botIdx_eq : nbhd botIdx = system.master

namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)

/-- Finite intersection of coded neighbourhoods, with Scott’s convention `⋂∅ = Δ`. -/
def interOf (u : Finset ι) : Set α :=
  u.fold (· ∩ ·) B.system.master B.nbhd

@[simp] theorem interOf_empty : B.interOf (∅ : Finset ι) = B.system.master := rfl

theorem interOf_insert {a : ι} {s : Finset ι} (ha : a ∉ s) :
    B.interOf (insert a s) = B.nbhd a ∩ B.interOf s :=
  Finset.fold_insert (op := (· ∩ ·)) ha

theorem nbhd_subset_master (i : ι) : B.nbhd i ⊆ B.system.master :=
  B.system.sub_master (B.nbhd_mem i)

theorem interOf_singleton (a : ι) : B.interOf ({a} : Finset ι) = B.nbhd a := by
  simp [interOf, Finset.fold_singleton, Set.inter_eq_left.mpr (B.nbhd_subset_master a)]

/-- Membership in the folded intersection. -/
theorem mem_interOf {u : Finset ι} {x : α} :
    x ∈ B.interOf u ↔ x ∈ B.system.master ∧ ∀ i ∈ u, x ∈ B.nbhd i := by
  induction u using Finset.induction with
  | empty =>
    simp [interOf_empty]
  | insert a s ha ih =>
    rw [B.interOf_insert ha, Set.mem_inter_iff, ih]
    constructor
    · rintro ⟨ha', hm, hs⟩
      refine ⟨hm, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ha'
      · exact hs i hi
    · rintro ⟨hm, hall⟩
      exact ⟨hall a (Finset.mem_insert_self a s), hm,
        fun i hi => hall i (Finset.mem_insert_of_mem hi)⟩

theorem interOf_subset_nbhd {u : Finset ι} {i : ι} (hi : i ∈ u) :
    B.interOf u ⊆ B.nbhd i := fun _ hx => (B.mem_interOf.mp hx).2 i hi

theorem interOf_subset_master (u : Finset ι) : B.interOf u ⊆ B.system.master :=
  fun _ hx => (B.mem_interOf.mp hx).1

/-- Larger index sets give smaller intersections. -/
theorem interOf_anti {u v : Finset ι} (h : u ⊆ v) : B.interOf v ⊆ B.interOf u := by
  intro x hx
  exact B.mem_interOf.mpr ⟨(B.mem_interOf.mp hx).1, fun i hi => (B.mem_interOf.mp hx).2 i (h hi)⟩

/-- If a neighbourhood sits below `interOf u`, then `interOf u ∈ 𝒟`. -/
theorem interOf_mem_of_lower_bound {u : Finset ι} {Z : Set α}
    (hZ : B.system.mem Z) (hsub : Z ⊆ B.interOf u) : B.system.mem (B.interOf u) := by
  induction u using Finset.induction with
  | empty =>
    simpa [interOf_empty] using B.system.master_mem
  | insert a s ha ih =>
    rw [B.interOf_insert ha] at hsub ⊢
    have hs : B.system.mem (B.interOf s) := ih (hsub.trans Set.inter_subset_right)
    exact B.system.inter_mem (B.nbhd_mem a) hs hZ hsub

/-- A filter containing every `nbhd i` for `i ∈ u` contains `interOf u`. -/
theorem filter_mem_interOf (x : B.system.Element) {u : Finset ι}
    (hu : ∀ i ∈ u, x.mem (B.nbhd i)) : x.mem (B.interOf u) := by
  induction u using Finset.induction with
  | empty =>
    simpa [interOf_empty] using x.master_mem
  | insert a s ha ih =>
    rw [B.interOf_insert ha]
    exact x.inter_mem (hu a (Finset.mem_insert_self a s))
      (ih fun i hi => hu i (Finset.mem_insert_of_mem hi))

/-- **`neighborhoodSystem_to_infoSys`.** -/
def toInfoSys : InfoSys ι where
  bot := B.botIdx
  Con := {u | B.system.mem (B.interOf u)}
  Ent := fun u a => B.system.mem (B.interOf u) ∧ B.interOf u ⊆ B.nbhd a
  con_subset := by
    intro u v hu hv
    exact B.interOf_mem_of_lower_bound hu (B.interOf_anti hv)
  con_sing := by
    intro a
    simpa [Set.mem_setOf_eq, B.interOf_singleton] using B.nbhd_mem a
  ent_con := by
    intro u a ⟨hu, hsub⟩
    have h₁ : B.interOf (insert a u) ⊆ B.interOf u :=
      B.interOf_anti (Finset.subset_insert a u)
    have h₂ : B.interOf u ⊆ B.interOf (insert a u) := by
      intro x hx
      refine B.mem_interOf.mpr ⟨(B.mem_interOf.mp hx).1, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hsub hx
      · exact (B.mem_interOf.mp hx).2 i hi
    have heq : B.interOf (insert a u) = B.interOf u := Set.Subset.antisymm h₁ h₂
    simpa [Set.mem_setOf_eq, heq] using hu
  ent_bot := by
    intro u hu
    refine ⟨hu, ?_⟩
    intro x hx
    rw [B.botIdx_eq]
    exact B.interOf_subset_master u hx
  ent_refl := by
    intro u a hu ha
    exact ⟨hu, B.interOf_subset_nbhd ha⟩
  ent_trans := by
    intro u v c hv _hu hall ⟨_, hsub⟩
    refine ⟨hv, ?_⟩
    intro x hx
    have hxu : x ∈ B.interOf u :=
      B.mem_interOf.mpr ⟨B.interOf_subset_master v hx, fun i hi => (hall i hi).2 hx⟩
    exact hsub hxu

/-! ## Domain isomorphism -/

/-- Filter → InfoSys element. -/
def toElement (x : B.system.Element) : B.toInfoSys.Element where
  carrier := {i | x.mem (B.nbhd i)}
  consistent := fun Y hY => x.sub (B.filter_mem_interOf x hY)
  closed := by
    intro Y a hY ⟨_, hsub⟩
    exact x.up_mem (B.filter_mem_interOf x hY) (B.nbhd_mem a) hsub

/-- InfoSys element → filter (upward closure of its coded neighbourhoods). -/
def ofElement (e : B.toInfoSys.Element) : B.system.Element where
  mem X := B.system.mem X ∧ ∃ i ∈ e.carrier, B.nbhd i ⊆ X
  sub h := h.1
  master_mem := by
    refine ⟨B.system.master_mem, B.botIdx, ?_, by rw [B.botIdx_eq]⟩
    have hEnt : B.toInfoSys.Ent ∅ B.botIdx := B.toInfoSys.ent_bot (InfoSys.con_empty _)
    exact e.closed ∅ B.botIdx (fun _ h => False.elim (Finset.notMem_empty _ h)) hEnt
  inter_mem := by
    intro X Y ⟨hX, i, hi, hix⟩ ⟨hY, j, hj, hjy⟩
    have hCon : ({i, j} : Finset ι) ∈ B.toInfoSys.Con :=
      e.consistent {i, j} (by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hi
        · have : x = j := Finset.mem_singleton.mp hx
          exact this ▸ hj)
    have hInterMem : B.system.mem (B.interOf ({i, j} : Finset ι)) := hCon
    have hInterSub : B.interOf ({i, j} : Finset ι) ⊆ X ∩ Y := by
      intro x hx
      refine ⟨hix (B.interOf_subset_nbhd (by simp) hx),
        hjy (B.interOf_subset_nbhd (by simp) hx)⟩
    refine ⟨B.system.inter_mem hX hY hInterMem hInterSub, ?_⟩
    obtain ⟨k, hk⟩ := B.exhaustive hInterMem
    refine ⟨k, ?_, ?_⟩
    · have hEnt : B.toInfoSys.Ent {i, j} k := ⟨hInterMem, fun x hx => hk ▸ hx⟩
      exact e.closed {i, j} k (by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hi
        · exact Finset.mem_singleton.mp hx ▸ hj) hEnt
    · intro x hx
      exact hInterSub (hk ▸ hx)
  up_mem := by
    intro X Y ⟨hX, i, hi, hix⟩ hY hXY
    exact ⟨hY, i, hi, hix.trans hXY⟩

theorem toElement_carrier (x : B.system.Element) :
    (B.toElement x).carrier = {i | x.mem (B.nbhd i)} := rfl

theorem ofElement_mem (e : B.toInfoSys.Element) (X : Set α) :
    (B.ofElement e).mem X ↔ B.system.mem X ∧ ∃ i ∈ e.carrier, B.nbhd i ⊆ X :=
  Iff.rfl

theorem toElement_ofElement (e : B.toInfoSys.Element) :
    B.toElement (B.ofElement e) = e := by
  have hc : (B.toElement (B.ofElement e)).carrier = e.carrier := by
    ext i
    constructor
    · intro hi
      rcases (B.ofElement_mem e (B.nbhd i)).mp hi with ⟨_, j, hj, hsub⟩
      have hEnt : B.toInfoSys.Ent {j} i := by
        refine ⟨by simpa [B.interOf_singleton] using B.nbhd_mem j, ?_⟩
        simpa [B.interOf_singleton] using hsub
      exact e.closed {j} i (by
        intro x hx
        have : x = j := Finset.mem_singleton.mp hx
        exact this ▸ hj) hEnt
    · intro hi
      exact ⟨B.nbhd_mem i, i, hi, subset_rfl⟩
  rcases e with ⟨c, cons, clo⟩
  rcases hte : B.toElement (B.ofElement ⟨c, cons, clo⟩) with ⟨c', cons', clo'⟩
  have hc' : c' = c := by
    simpa [hte, toElement_carrier] using hc
  subst hc'
  rfl

theorem ofElement_toElement (x : B.system.Element) :
    B.ofElement (B.toElement x) = x := by
  refine NeighborhoodSystem.Element.ext (V := B.system) fun X => ?_
  constructor
  · intro ⟨hX, i, hi, hsub⟩
    exact x.up_mem hi hX hsub
  · intro hX
    obtain ⟨i, rfl⟩ := B.exhaustive (x.sub hX)
    exact ⟨x.sub hX, i, hX, subset_rfl⟩

/-- Order isomorphism between the neighbourhood-system domain and the induced
information-system domain. -/
def domainOrderIso : B.system.Element ≃o B.toInfoSys.Element where
  toFun := B.toElement
  invFun := B.ofElement
  left_inv := B.ofElement_toElement
  right_inv := B.toElement_ofElement
  map_rel_iff' := by
    intro x y
    constructor
    · intro h X hX
      obtain ⟨i, rfl⟩ := B.exhaustive (x.sub hX)
      have hi : i ∈ (B.toElement x).carrier := hX
      have hi' : i ∈ (B.toElement y).carrier := h hi
      exact y.up_mem hi' (x.sub hX) subset_rfl
    · intro h i hi
      exact h (B.nbhd i) hi

end NbhdBasis

/-- Blueprint name: neighbourhood system (with decidable basis) → information system. -/
abbrev neighborhoodSystem_to_infoSys {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α) :
    InfoSys ι :=
  B.toInfoSys

end ScottModels

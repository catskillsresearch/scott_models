/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott_models
-/

import Mathlib.Order.Hom.Basic
import Mathlib.Order.Ideal
import Scott1982.Factoid45

/-!
# Information systems → ideal completion (1982 → algebraic dcpo)

The domain `|A|` of an information system is the **ideal completion** of its
poset of finite elements `ū` (closures of consistent finite token sets):
`A.Element ≃o Order.Ideal (FiniteElement A)`.

Packaging of Factoids 4.4–4.5 (`directedSup`, algebraicity, `compact_closure`).
-/

namespace ScottModels

open Scott1982
open Scott1982.Constructive
open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

/-- Finite (compact) elements: closures of consistent finite token sets. -/
abbrev FiniteElement : Type _ :=
  { x : A.Element // ∃ (u : Finset α) (hu : u ∈ A.Con), x = A.closure u hu }

theorem isFinite_bot :
    ∃ (u : Finset α) (hu : u ∈ A.Con), A.botElement = A.closure u hu :=
  ⟨∅, A.con_empty, A.botElement_eq_closure_empty⟩

/-- Bottom, as a finite element. -/
def botFinite : FiniteElement A := ⟨A.botElement, isFinite_bot A⟩

/-- Finite approximants of `x`, as `FiniteElement`s. -/
def finiteApproximants (x : A.Element) : Set (FiniteElement A) :=
  { y | (y : A.Element) ∈ A.finiteApproximants x }

theorem mem_finiteApproximants_of_le {x : A.Element} {y : FiniteElement A}
    (hle : (y : A.Element) ≤ x) : y ∈ finiteApproximants A x := by
  rcases y with ⟨yval, ⟨u, hu, rfl⟩⟩
  refine ⟨u, hu, ?_, rfl⟩
  intro a ha
  exact hle (A.subset_closure hu ha)

theorem le_of_mem_finiteApproximants {x : A.Element} {y : FiniteElement A}
    (hy : y ∈ finiteApproximants A x) : (y : A.Element) ≤ x := by
  obtain ⟨u, hu, huX, hyeq⟩ := hy
  exact hyeq ▸ A.closure_le_element x hu huX

theorem mem_finiteApproximants_iff {x : A.Element} {y : FiniteElement A} :
    y ∈ finiteApproximants A x ↔ (y : A.Element) ≤ x :=
  ⟨le_of_mem_finiteApproximants A, mem_finiteApproximants_of_le A⟩

theorem nonempty_finiteApproximants (x : A.Element) :
    (finiteApproximants A x).Nonempty :=
  ⟨botFinite A, mem_finiteApproximants_of_le A (A.botElement_le x)⟩

theorem directed_finiteApproximants (x : A.Element) :
    DirectedOn (· ≤ ·) (finiteApproximants A x) := by
  intro y₁ hy₁ y₂ hy₂
  obtain ⟨u, hu, huX, hy₁eq⟩ := hy₁
  obtain ⟨v, hv, hvX, hy₂eq⟩ := hy₂
  obtain ⟨w, hw, hwX, huw, hvw⟩ := A.closures_directed x hu hv huX hvX
  refine ⟨⟨A.closure w hw, ⟨w, hw, rfl⟩⟩, ⟨w, hw, hwX, rfl⟩, ?_, ?_⟩
  · -- y₁ ≤ closure w
    change (y₁ : A.Element) ≤ A.closure w hw
    exact hy₁eq ▸ huw
  · change (y₂ : A.Element) ≤ A.closure w hw
    exact hy₂eq ▸ hvw

theorem isLowerSet_finiteApproximants (x : A.Element) :
    IsLowerSet (finiteApproximants A x) := by
  intro y₁ y₂ hle hy₂
  exact mem_finiteApproximants_of_le A (le_trans hle (le_of_mem_finiteApproximants A hy₂))

/-- Ideal of finite approximants of `x`. -/
def toIdeal (x : A.Element) : Ideal (FiniteElement A) where
  carrier := finiteApproximants A x
  lower' := isLowerSet_finiteApproximants A x
  nonempty' := nonempty_finiteApproximants A x
  directed' := directed_finiteApproximants A x

theorem mem_toIdeal_iff {x : A.Element} {y : FiniteElement A} :
    y ∈ toIdeal A x ↔ (y : A.Element) ≤ x :=
  mem_finiteApproximants_iff A

/-- Underlying set of elements of an ideal of finite elements. -/
def idealCarrier (I : Ideal (FiniteElement A)) : Set A.Element :=
  Subtype.val '' (I : Set (FiniteElement A))

theorem nonempty_idealCarrier (I : Ideal (FiniteElement A)) :
    (idealCarrier A I).Nonempty := by
  obtain ⟨y, hy⟩ := I.nonempty
  exact ⟨y, y, hy, rfl⟩

theorem directed_idealCarrier (I : Ideal (FiniteElement A)) :
    A.IsDirected (idealCarrier A I) := by
  intro x y hx hy
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  obtain ⟨z', hz', hxz, hyz⟩ := I.directed x' hx' y' hy'
  exact ⟨z', ⟨z', hz', rfl⟩, hxz, hyz⟩

/-- Retraction: directed supremum of the finite elements in the ideal. -/
noncomputable def ofIdeal (I : Ideal (FiniteElement A)) : A.Element :=
  A.directedSup (idealCarrier A I) (nonempty_idealCarrier A I) (directed_idealCarrier A I)

theorem le_ofIdeal_of_mem {I : Ideal (FiniteElement A)} {y : FiniteElement A}
    (hy : y ∈ I) : (y : A.Element) ≤ ofIdeal A I :=
  A.le_directedSup _ _ _ ⟨y, hy, rfl⟩

theorem ofIdeal_toIdeal (x : A.Element) : ofIdeal A (toIdeal A x) = x := by
  -- idealCarrier (toIdeal x) = finiteApproximants as Elements = A.finiteApproximants x
  have hset : idealCarrier A (toIdeal A x) = A.finiteApproximants x := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact hy
    · intro hz
      refine ⟨⟨z, ?_⟩, hz, rfl⟩
      obtain ⟨u, hu, _, rfl⟩ := hz
      exact ⟨u, hu, rfl⟩
  -- directedSup of that set is x
  change A.directedSup (idealCarrier A (toIdeal A x)) _ _ = x
  simp_rw [hset]
  exact (A.eq_directedSup_finiteApproximants x).symm

theorem toIdeal_ofIdeal (I : Ideal (FiniteElement A)) : toIdeal A (ofIdeal A I) = I := by
  refine Ideal.ext ?_
  ext y
  constructor
  · intro hy
    have hle : (y : A.Element) ≤ ofIdeal A I := le_of_mem_finiteApproximants A hy
    rcases y with ⟨yval, ⟨u, hu, rfl⟩⟩
    obtain ⟨z, hz, hcle⟩ :=
      A.compact_closure (idealCarrier A I) (nonempty_idealCarrier A I)
        (directed_idealCarrier A I) hu hle
    obtain ⟨z', hz', rfl⟩ := hz
    exact I.lower hcle hz'
  · intro hy
    exact mem_finiteApproximants_of_le A (le_ofIdeal_of_mem A hy)

theorem toIdeal_mono {x y : A.Element} (hxy : x ≤ y) : toIdeal A x ≤ toIdeal A y := by
  intro z hz
  exact mem_finiteApproximants_of_le A
    (le_trans (le_of_mem_finiteApproximants A hz) hxy)

/-- Order isomorphism: domain elements ↔ ideals of finite elements. -/
noncomputable def domainOrderIso : A.Element ≃o Ideal (FiniteElement A) where
  toFun := toIdeal A
  invFun := ofIdeal A
  left_inv := ofIdeal_toIdeal A
  right_inv := toIdeal_ofIdeal A
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      -- x ≤ y from toIdeal x ≤ toIdeal y via algebraicity
      rw [← ofIdeal_toIdeal A x, ← ofIdeal_toIdeal A y]
      refine A.directedSup_le _ _ _ ?_
      intro z hz
      obtain ⟨z', hz', rfl⟩ := hz
      exact le_ofIdeal_of_mem A (h hz')
    · exact toIdeal_mono A

end InfoSysToIdealCompletion

/-- Blueprint name: `|A|` as the ideal completion of its finite elements. -/
noncomputable abbrev infoSys_to_idealCompletion {α : Type*} [DecidableEq α] (A : InfoSys α) :
    A.Element ≃o Ideal (InfoSysToIdealCompletion.FiniteElement A) :=
  InfoSysToIdealCompletion.domainOrderIso A

end ScottModels

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Directed
import Mathlib.Order.Hom.Basic
import Mathlib.Order.UpperLower.Basic

/-!
# Presentation-bridge isos (Palomar statement of record)

This module states the compared family: the 1980 ↔ 1982 coding of a neighbourhood
system as an information system, the converse basic-open neighbourhood system
with `|A| ≃o` its filters, and the round three-presentation iso
`D ≃o RoundInfoSysElement` under `IsContinuousLattice`.

It imports only Mathlib. The sorry-free proofs live in `ScottModels/` and are
exposed to Comparator through `Solution.lean`. Challenge is allowed `sorry`;
the compared declarations are `def`s (`OrderIso` is data), so they appear in
`comparator.json` as `definition_names`.

The type surface below uses the same fully-qualified names as the sibling
packages and `ScottModels`, so Comparator can identify the constants used in
the statements. It is not a copy of the `ScottModels/*.lean` proof modules.

## Informal claim

Dana Scott gave three presentations of the same class of domains. This package
does not re-prove the internal theorems of those papers. It records the
machine-checked **bridges** (`view.pdf` / `arxiv.md`):

1. A neighbourhood system with a decidable exhaustive coding `NbhdBasis ι α`
   induces an `InfoSys` on the codes (`neighborhoodSystem_to_infoSys`).
2. An information system `A` induces a neighbourhood system of basic opens
   `[u] = {x ∈ |A| | ↑u ⊆ x}` (`infoSys_to_neighborhoodSystem`), and the
   domains are order-isomorphic
   (`InfoSysToNeighborhood.domainOrderIso : |A| ≃o` those filters).
3. For a continuous lattice `D` with `DecidableEq D`,
   `presentation_domains_equiv : D ≃o RoundInfoSysElement` — equivalently
   `D ≃o RoundFilter ≃o RoundInfoSysElement` via the `↟`-coding
   `wayBelowNbhdBasis`. Raw `|𝒟|` and the full InfoSys domain are larger;
   the identification is the **round** corner.

The 1980 ↔ 1982 maps and the round continuous-lattice corner audit to
`{propext, Quot.sound}`. `Classical.choice` is permitted (1972 topological
`≪` / classical frontier elsewhere in the library) and is not required by
these three compared declarations.
-/

/-! ## 1980 neighbourhood systems (`Scott1980.Neighborhood`) -/

namespace Scott1980.Neighborhood

structure NeighborhoodSystem (α : Type*) where
  mem : Set α → Prop
  master : Set α
  master_mem : mem master
  inter_mem : ∀ {X Y Z : Set α}, mem X → mem Y → mem Z → Z ⊆ X ∩ Y → mem (X ∩ Y)
  sub_master : ∀ {X : Set α}, mem X → X ⊆ master

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

structure Element where
  mem : Set α → Prop
  sub : ∀ {X}, mem X → V.mem X
  master_mem : mem V.master
  inter_mem : ∀ {X Y}, mem X → mem Y → mem (X ∩ Y)
  up_mem : ∀ {X Y}, mem X → V.mem Y → X ⊆ Y → mem Y

theorem Element.ext {x y : V.Element} (h : ∀ X, x.mem X ↔ y.mem X) : x = y := by
  rcases x with ⟨xmem, _, _, _, _⟩
  rcases y with ⟨ymem, _, _, _, _⟩
  have hmem : xmem = ymem := funext fun X => propext (h X)
  subst hmem
  rfl

instance : PartialOrder V.Element where
  le x y := ∀ X, x.mem X → y.mem X
  le_refl x X h := h
  le_trans x y z h1 h2 X h := h2 X (h1 X h)
  le_antisymm x y h1 h2 :=
    @Element.ext α V x y fun X => ⟨h1 X, h2 X⟩

end NeighborhoodSystem

end Scott1980.Neighborhood

/-! ## 1982 information systems (`Scott1982`) -/

namespace Scott1982

structure InfoSys (α : Type*) [DecidableEq α] where
  bot : α
  Con : Set (Finset α)
  Ent : Finset α → α → Prop
  con_subset : ∀ {u v : Finset α}, u ∈ Con → v ⊆ u → v ∈ Con
  con_sing : ∀ a : α, {a} ∈ Con
  ent_con : ∀ {u : Finset α} {a : α}, Ent u a → insert a u ∈ Con
  ent_bot : ∀ {u : Finset α}, u ∈ Con → Ent u bot
  ent_refl : ∀ {u : Finset α} {a : α}, u ∈ Con → a ∈ u → Ent u a
  ent_trans : ∀ {u v : Finset α} {c : α},
    v ∈ Con → u ∈ Con → (∀ y ∈ u, Ent v y) → Ent u c → Ent v c

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

structure Element where
  carrier : Set α
  consistent : ∀ Y : Finset α, (Y : Set α) ⊆ carrier → Y ∈ sys.Con
  closed : ∀ (Y : Finset α) (a : α), (Y : Set α) ⊆ carrier → sys.Ent Y a → a ∈ carrier

instance : PartialOrder sys.Element where
  le x y := x.carrier ⊆ y.carrier
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ h1 h2 := Set.Subset.trans h1 h2
  le_antisymm x y h1 h2 := by
    have hc : x.carrier = y.carrier := Set.Subset.antisymm h1 h2
    cases x
    cases y
    subst hc
    rfl

end InfoSys

end Scott1982

/-! ## 1972 continuous lattices (`Scott1972.ContinuousLattice`) -/

namespace Scott1972.ContinuousLattice

variable {D : Type*} [CompleteLattice D]

def ScottOpen (U : Set D) : Prop :=
  IsUpperSet U ∧
    ∀ ⦃S : Set D⦄, S.Nonempty → DirectedOn (· ≤ ·) S → sSup S ∈ U → (S ∩ U).Nonempty

/-- `x ≪ y`: `y` lies in a Scott-open neighbourhood contained in `Ici x`. -/
def WayBelow (x y : D) : Prop :=
  ∃ U : Set D, ScottOpen U ∧ y ∈ U ∧ U ⊆ Set.Ici x

@[inherit_doc] scoped infix:50 " ≪ " => WayBelow

def IsContinuousLattice (D : Type*) [CompleteLattice D] : Prop :=
  ∀ y : D, IsLUB {x | x ≪ y} y

end Scott1972.ContinuousLattice

/-! ## Bridges (`ScottModels`) -/

namespace ScottModels

open Scott1980.Neighborhood
open Scott1982
open Scott1972.ContinuousLattice
open scoped Scott1972.ContinuousLattice

structure NbhdBasis (ι α : Type*) [DecidableEq ι] where
  system : NeighborhoodSystem α
  nbhd : ι → Set α
  nbhd_mem : ∀ i, system.mem (nbhd i)
  exhaustive : ∀ {X : Set α}, system.mem X → ∃ i, nbhd i = X
  botIdx : ι
  botIdx_eq : nbhd botIdx = system.master

namespace NbhdBasis

variable {ι α : Type*} [DecidableEq ι] (B : NbhdBasis ι α)
include B

/-- InfoSys on neighbourhood codes. Compared; proved in `NeighborhoodToInfoSys.lean`. -/
noncomputable def toInfoSys : InfoSys ι :=
  let _ := B
  sorry

/-- Filters of `B.system` ≃o elements of `B.toInfoSys`. Supporting hole. -/
noncomputable def domainOrderIso : B.system.Element ≃o B.toInfoSys.Element :=
  sorry

end NbhdBasis

/-- **1980 → 1982.** Neighbourhood system (decidable basis) → information system. -/
noncomputable def neighborhoodSystem_to_infoSys {ι α : Type*} [DecidableEq ι]
    (B : NbhdBasis ι α) : InfoSys ι :=
  let _ := B
  sorry

namespace InfoSysToNeighborhood

variable {α : Type*} [DecidableEq α] (A : InfoSys α)
include A

/-- Basic-open neighbourhood system on `|A|`. Supporting hole. -/
noncomputable def toNeighborhoodSystem : NeighborhoodSystem A.Element :=
  sorry

/-- **1982 → 1980.** `|A| ≃o` filters of the basic-open neighbourhood system. -/
noncomputable def domainOrderIso : A.Element ≃o (toNeighborhoodSystem A).Element :=
  sorry

end InfoSysToNeighborhood

/-- **1982 → 1980.** Blueprint name for the basic-open neighbourhood system. -/
noncomputable def infoSys_to_neighborhoodSystem {α : Type*} [DecidableEq α]
    (A : InfoSys α) : NeighborhoodSystem A.Element :=
  let _ := A
  sorry

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

def wayBelowUp (a : D) : Set D := {z | a ≪ z}

/-- `↟`-neighbourhood system on a complete lattice. Supporting hole. -/
noncomputable def toNeighborhoodSystem : NeighborhoodSystem D :=
  let _ := (⊥ : D)
  sorry

abbrev Filter : Type _ :=
  (toNeighborhoodSystem : NeighborhoodSystem D).Element

def IsRound (f : Filter (D := D)) : Prop :=
  ∀ {a : D}, f.mem (wayBelowUp a) → ∃ b : D, a ≪ b ∧ f.mem (wayBelowUp b)

abbrev RoundFilter : Type _ :=
  { f : Filter (D := D) // IsRound f }

end ContinuousLatticeToNeighborhood

open ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D] [DecidableEq D]

/-- Tokens = elements of `D`; neighbourhoods = `↟a`. Supporting hole. -/
noncomputable def wayBelowNbhdBasis : NbhdBasis D D :=
  let _ := (⊥ : D)
  sorry

/-- Roundness of the `↟`-filter corresponding to an InfoSys element of the
`↟`-basis. Compared as a supporting hole; the Solution transports `IsRound`
along `NbhdBasis.domainOrderIso`. -/
noncomputable def IsRoundInfoSysElement
    (e : (wayBelowNbhdBasis (D := D)).toInfoSys.Element) : Prop :=
  let _ := e
  sorry

abbrev RoundInfoSysElement : Type _ :=
  { e : (wayBelowNbhdBasis (D := D)).toInfoSys.Element // IsRoundInfoSysElement (D := D) e }

variable (hD : IsContinuousLattice D)
include hD

/-- **Three-presentation iso.** `D ≃o RoundFilter ≃o RoundInfoSysElement`. -/
noncomputable def presentation_domains_equiv :
    D ≃o RoundInfoSysElement (D := D) :=
  let _ := hD
  sorry

end ScottModels

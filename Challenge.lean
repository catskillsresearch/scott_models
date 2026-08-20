/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sum.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Directed
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Hom.WithTopBot
import Mathlib.Order.Ideal
import Mathlib.Order.UpperLower.Basic

/-!
# Presentation-bridge isos (Palomar statement of record)

This module states the compared family: the 1980 ↔ 1982 coding of a neighbourhood
system as an information system, the converse basic-open neighbourhood system
with `|A| ≃o` its filters, the round three-presentation iso
`D ≃o RoundInfoSysElement` under `IsContinuousLattice`, and Scott’s
S-expression instance `T ≅ A + (T × T)` (`sexNeighborhoodIso`,
`sexIdealIso`, `sexDomainEquationIso`).

It imports only Mathlib. The sorry-free proofs live in `ScottModels/` and are
exposed to Comparator through `Solution.lean`. Challenge is allowed `sorry`;
the compared isomorphisms are `def`s (`OrderIso` is data) and appear in
`comparator.json` as `definition_names`. The corresponding `Nonempty`
existence claims are `theorem`s in `theorem_names`.

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
4. On Scott’s S-expression domain `T ≅ A + (T × T)` (Factoid 8.1 over the
   ℕ lower-bound atoms), the same carrier is an InfoSys, a neighbourhood
   filter domain, and an ideal completion (`sexNeighborhoodIso`,
   `sexIdealIso`), and the equation holds as an order isomorphism of
   domains (`sexDomainEquationIso`).

The 1980 ↔ 1982 maps, the round continuous-lattice corner, and the
S-expression carrier isos audit to `{propext, Quot.sound}`.
`sexDomainEquationIso` uses `Classical.choice` via the 1982 sum
trichotomy. `Classical.choice` is also permitted for the 1972
topological `≪` frontier elsewhere in the library.
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

set_option linter.unusedSectionVars false

section Element
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

/-- Entailment closure of a consistent set (Factoid 3.5). Supporting hole. -/
noncomputable def closure (u : Finset α) (hu : u ∈ sys.Con) : sys.Element :=
  let _ := u
  let _ := hu
  sorry

end Element

/-- Tokens of the tree / S-expression system (Scott 1982, Factoid 8.1). -/
inductive TreeToken (α : Type*) where
  | bot : TreeToken α
  | atom : α → TreeToken α
  | pairL : TreeToken α → TreeToken α
  | pairR : TreeToken α → TreeToken α
  deriving DecidableEq

section
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Token type of the separated sum `A + B` (Scott 6.3). -/
inductive SumToken (α β : Type*) where
  | left : α → SumToken α β
  | right : β → SumToken α β
  | bot : SumToken α β

instance : DecidableEq (SumToken α β)
  | .left a, .left b =>
      if h : a = b then isTrue (h ▸ rfl)
      else isFalse fun h' => h (SumToken.left.inj h')
  | .right a, .right b =>
      if h : a = b then isTrue (h ▸ rfl)
      else isFalse fun h' => h (SumToken.right.inj h')
  | .bot, .bot => isTrue rfl
  | .left _, .right _ => isFalse fun h => nomatch h
  | .left _, .bot => isFalse fun h => nomatch h
  | .right _, .left _ => isFalse fun h => nomatch h
  | .right _, .bot => isFalse fun h => nomatch h
  | .bot, .left _ => isFalse fun h => nomatch h
  | .bot, .right _ => isFalse fun h => nomatch h

/-- Scott 6.1(i): a product token is `(X, Δ_B)` or `(Δ_A, Y)`. -/
def IsProdToken (A : InfoSys α) (B : InfoSys β) (p : α × β) : Prop :=
  p.1 = A.bot ∨ p.2 = B.bot

instance (A : InfoSys α) (B : InfoSys β) (p : α × β) : Decidable (IsProdToken A B p) :=
  if h1 : p.1 = A.bot then isTrue (Or.inl h1)
  else if h2 : p.2 = B.bot then isTrue (Or.inr h2)
  else isFalse fun h => h.elim h1 h2

/-- Token type of the product system `A × B`. -/
def ProdToken (A : InfoSys α) (B : InfoSys β) : Type _ :=
  {p : α × β // IsProdToken A B p}

instance (A : InfoSys α) (B : InfoSys β) : DecidableEq (ProdToken A B) :=
  Subtype.instDecidableEq

end

section
variable {α : Type*} [DecidableEq α] (A : InfoSys α)

/-- Factoid 8.1 tree system. Supporting hole. -/
noncomputable def treeSystem : InfoSys (TreeToken α) :=
  let _ := A
  sorry

/-- Official RHS `A + (T × T)`. Supporting hole. -/
noncomputable def treeRhs :
    InfoSys (SumToken α (ProdToken (treeSystem A) (treeSystem A))) :=
  let _ := A
  sorry

end

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
open Scott1982.InfoSys
open Order

section Continuous
universe u
variable {D : Type u} [CompleteLattice D] [DecidableEq D]

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

/-- The three presentations determine the same domain (round corner). -/
theorem exists_presentation_domains_equiv :
    Nonempty (D ≃o RoundInfoSysElement (D := D)) :=
  let _ := hD
  sorry

end Continuous

/-! ## Worked example: S-expressions (`T ≅ A + (T × T)`) -/

/-- ℕ lower-bound atom system (Factoid 2.4). Supporting hole. -/
noncomputable def lowerBoundSystem : InfoSys ℕ :=
  sorry

/-- Tree / S-expression information system over lower-bound atoms. -/
noncomputable abbrev SexSys : InfoSys (TreeToken ℕ) :=
  treeSystem lowerBoundSystem

/-- Official right-hand side `A + (T × T)`. -/
noncomputable abbrev SexRhs : InfoSys (SumToken ℕ (ProdToken SexSys SexSys)) :=
  treeRhs lowerBoundSystem

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

/-- Finite (compact) elements: closures of consistent finite token sets. -/
abbrev FiniteElement : Type _ :=
  { x : A.Element // ∃ (u : Finset α) (hu : u ∈ A.Con), x = A.closure u hu }

end InfoSysToIdealCompletion

/-- **1982 ≃o 1980** on this instance: `|T| ≃o` filters of `[u]`. -/
noncomputable def sexNeighborhoodIso :
    SexSys.Element ≃o (InfoSysToNeighborhood.toNeighborhoodSystem SexSys).Element :=
  sorry

/-- **1982 ≃o ideal completion** on this instance: `|T| ≃o Ideal (K(T))`. -/
noncomputable def sexIdealIso :
    SexSys.Element ≃o Ideal (InfoSysToIdealCompletion.FiniteElement SexSys) :=
  sorry

/-- **Domain equation** at domain level:
`WithBot (|A| ⊕ (|T| × |T|)) ≃o |A + (T × T)|`. -/
noncomputable def sexDomainEquationIso :
    WithBot (lowerBoundSystem.Element ⊕ (SexSys.Element × SexSys.Element)) ≃o
      SexRhs.Element :=
  sorry

theorem exists_sexNeighborhoodIso :
    Nonempty (SexSys.Element ≃o
      (InfoSysToNeighborhood.toNeighborhoodSystem SexSys).Element) :=
  sorry

theorem exists_sexIdealIso :
    Nonempty (SexSys.Element ≃o
      Ideal (InfoSysToIdealCompletion.FiniteElement SexSys)) :=
  sorry

theorem exists_sexDomainEquationIso :
    Nonempty
      (WithBot (lowerBoundSystem.Element ⊕ (SexSys.Element × SexSys.Element)) ≃o
        SexRhs.Element) :=
  sorry

end ScottModels

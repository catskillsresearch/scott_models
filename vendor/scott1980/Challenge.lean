/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Basic
import Mathlib.Data.Countable.Defs
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Fin.Basic

/-!
# Scott 1981: D ⊴ U — first sentence of Theorem 8.8

Ground truth for the wording is `sources/PRG19.md`. Theorem 8.8 there is:

> The system \(\mathcal{U}\) is universal in the sense that, for every countable
> neighbourhood system \(\mathcal{D}\), we have
> \(\mathcal{D} \trianglelefteq \mathcal{U}\).

`𝒰` is Definition 8.7's neighbourhood system over `[0,1) ⊆ ℚ`: the non-empty
finite unions of rational intervals `[r,s)`. Scott's `⊴` (the prose before
Lemma 6.15) means *embeds as a subdomain*: `D ⊴ U` iff there is a `D'` with
`D ≅ D'` and `D' ◁ U`. The principal sourced theorem compared here is
**only that first sentence** of Theorem 8.8; the effective projection-pair sentence and the
finitary-projection correspondence are `theorem_8_8_b` / `theorem_8_8_c` in
the library and are not Comparator targets. The library proves the compared
claim as `theorem_8_8` by assembling `theorem_8_8_a`.

This file imports only Mathlib. The proofs live in
`Scott1980/Neighborhood/*` and are compared against this file by Comparator
via `Solution.lean`.

Comparator also selects two new formal corollaries that instantiate the principal theorem:
Example 1.5 (all nonempty subsets of `{0,1,2,3}`) and Exercise 7.22's
least-fixed-point family `S` over `{0,1}*`. The embeddings
`P4_embeds` and `Ssys_embeds` are compared; their proofs are
`theorem_8_8` applied to those systems. Scott defines both systems but
does not separately state these two embeddings.

## How to read this file

The definitions below are the vocabulary of the claim. A reader who wants to
check *what* has been proved should read this file and need not read the proof
development. `Solution.lean` imports the sorry-free library.
-/

namespace Scott1980.Neighborhood

/-- **Definition 1.1 (Scott 1981, PRG-19).** A *neighbourhood system* over a
token type `α`. The field `master_nonempty` records Scott's standing assumption, immediately
before the numbered definition, that the master token set `Δ` is non-empty. -/
structure NeighborhoodSystem (α : Type*) where
  mem : Set α → Prop
  master : Set α
  /-- Scott's standing assumption `Δ ≠ ∅`. -/
  master_nonempty : master.Nonempty
  master_mem : mem master
  inter_mem : ∀ {X Y Z : Set α}, mem X → mem Y → mem Z → Z ⊆ X ∩ Y → mem (X ∩ Y)
  sub_master : ∀ {X : Set α}, mem X → X ⊆ master

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Definition 1.6.** An (ideal) *element*: a filter of neighbourhoods. -/
structure Element where
  mem : Set α → Prop
  sub : ∀ {X}, mem X → V.mem X
  master_mem : mem V.master
  inter_mem : ∀ {X Y}, mem X → mem Y → mem (X ∩ Y)
  up_mem : ∀ {X Y}, mem X → V.mem Y → X ⊆ Y → mem Y

/-- Extensional equality of elements. -/
theorem Element.ext {x y : V.Element} (h : ∀ X, x.mem X ↔ y.mem X) : x = y := by
  sorry

/-- Filter-inclusion order on elements (Definition 1.8). -/
def element_le (x y : V.Element) : Prop :=
  ∀ X, x.mem X → y.mem X

/-- Reflexivity of the filter-inclusion order. -/
theorem element_le_refl (x : V.Element) : ∀ X, x.mem X → x.mem X := by
  sorry

/-- Transitivity of the filter-inclusion order. -/
theorem element_le_trans (x y z : V.Element)
    (hxy : ∀ X, x.mem X → y.mem X) (hyz : ∀ X, y.mem X → z.mem X) :
    ∀ X, x.mem X → z.mem X := by
  sorry

/-- Antisymmetry of the filter-inclusion order. -/
theorem element_le_antisymm (x y : V.Element)
    (hxy : ∀ X, x.mem X → y.mem X) (hyx : ∀ X, y.mem X → x.mem X) :
    x = y := by
  sorry

/-- Elements are ordered by inclusion of their membership predicates
(Definition 1.8). -/
instance : PartialOrder V.Element where
  le := element_le V
  le_refl := element_le_refl V
  le_trans := element_le_trans V
  le_antisymm := element_le_antisymm V

end NeighborhoodSystem

/-- **Definition 1.9.** An order-isomorphism of the element domains. -/
abbrev DomainIso {α β : Type*} (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : Type _ :=
  V₀.Element ≃o V₁.Element

/-- Scott's `𝒟₀ ≅ 𝒟₁`. -/
def Isomorphic {α β : Type*} (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : Prop :=
  Nonempty (DomainIso V₀ V₁)

@[inherit_doc] infix:25 " ≅ᴰ " => Isomorphic

/-- **Definition 6.10.** The subsystem (subdomain) relation `D ◁ E`. -/
structure Subsystem {α : Type*} (D E : NeighborhoodSystem α) : Prop where
  master_eq : D.master = E.master
  sub : ∀ {X : Set α}, D.mem X → E.mem X
  inter_closed : ∀ {X Y : Set α}, D.mem X → D.mem Y → E.mem (X ∩ Y) → D.mem (X ∩ Y)

@[inherit_doc] infix:50 " ◁ " => Subsystem

/-- **Scott's `⊴` (prose before Lemma 6.15).** `D` embeds as a subdomain of `E`. -/
def Trianglelefteq {α β : Type*} (D : NeighborhoodSystem α) (E : NeighborhoodSystem β) : Prop :=
  ∃ D' : NeighborhoodSystem β, D' ◁ E ∧ (D ≅ᴰ D')

@[inherit_doc] infix:50 " ⊴ " => Trianglelefteq

/-- The set presented by a list of interval endpoint-pairs. -/
def presentedIntervals (L : List (ℚ × ℚ)) : Set ℚ := ⋃ p ∈ L, Set.Ico p.1 p.2

/-- Membership in Scott's universal family. This is the list presentation
used by the library: a nonempty `X ⊆ [0,1)` equal to `presentedIntervals L`
for some `L`. Scott's Definition 8.7 writes the same family with a
per-interval side-condition `0 ≤ r < s ≤ 1`; `U_mem_iff_scott` in
`Definition87.lean` proves the two predicates coincide. -/
def UMem (X : Set ℚ) : Prop :=
  (∃ L : List (ℚ × ℚ), X = presentedIntervals L) ∧ X.Nonempty ∧ X ⊆ Set.Ico (0 : ℚ) 1

/-- Scott's master neighbourhood `Δ = [0,1)` for `𝒰`. -/
abbrev UMaster : Set ℚ := Set.Ico (0 : ℚ) 1

/-- `[0,1)` is a neighbourhood of `𝒰`. -/
theorem U_master_mem : UMem UMaster := by
  sorry

/-- Scott's token set `[0,1)` is non-empty. -/
theorem UMaster_nonempty : UMaster.Nonempty := by
  exact ⟨0, by simp [UMaster]⟩

/-- Intersection of two presentable sets is presentable. -/
theorem U_inter_mem {X Y Z : Set ℚ} (hX : UMem X) (hY : UMem Y) (hZ : UMem Z)
    (hZsub : Z ⊆ X ∩ Y) : UMem (X ∩ Y) := by
  sorry

/-- Every `UMem` set is contained in `[0,1)`. -/
theorem U_sub_master {X : Set ℚ} (hX : UMem X) : X ⊆ UMaster := by
  sorry

/-- **Definition 8.7.** The universal neighbourhood system `𝒰` over `[0,1) ⊆ ℚ`. -/
def U : NeighborhoodSystem ℚ where
  mem := UMem
  master := UMaster
  master_nonempty := UMaster_nonempty
  master_mem := U_master_mem
  inter_mem := U_inter_mem
  sub_master := U_sub_master

/-- **First sentence of Theorem 8.8 (Scott 1981, PRG-19)** (`sources/PRG19.md`):
*The system \(\mathcal{U}\) is universal in the sense that, for every countable
neighbourhood system \(\mathcal{D}\), we have \(\mathcal{D} \trianglelefteq \mathcal{U}\).* -/
theorem theorem_8_8.{u} {α : Type u} (D : NeighborhoodSystem α)
    [Countable {S : Set α // D.mem S}] : D ⊴ U := by
  sorry

/-! ### Concrete countable domains that instantiate the compared theorem -/

namespace Example15

abbrev Token := Fin 4
def master : Set Token := Set.univ
def P4Mem (X : Set Token) : Prop := X.Nonempty
theorem P4_master_mem : P4Mem master := by sorry
theorem P4_master_nonempty : master.Nonempty := by
  exact ⟨0, Set.mem_univ 0⟩
theorem P4_inter_mem {X Y Z : Set Token} (_hX : P4Mem X) (_hY : P4Mem Y)
    (hZ : P4Mem Z) (hZsub : Z ⊆ X ∩ Y) : P4Mem (X ∩ Y) := by sorry
theorem P4_sub_master {X : Set Token} (_h : P4Mem X) : X ⊆ master := by sorry
/-- **Example 1.5.** All non-empty subsets of `{0,1,2,3}`. -/
def neighborhoodSystem : NeighborhoodSystem Token where
  mem := P4Mem
  master := master
  master_nonempty := P4_master_nonempty
  master_mem := P4_master_mem
  inter_mem := P4_inter_mem
  sub_master := P4_sub_master
instance P4_countable : Countable {S : Set Token // neighborhoodSystem.mem S} := by
  sorry
theorem P4_embeds : neighborhoodSystem ⊴ U := by sorry

end Example15

namespace Exercise722

/-- Scott's concatenation `XY = {στ ∣ σ ∈ X, τ ∈ Y}`. -/
def concat (X Y : Set (List Bool)) : Set (List Bool) := {w | ∃ a ∈ X, ∃ b ∈ Y, a ++ b = w}

/-- **Exercise 7.22 syntax** of `S`-terms (regular-event fragment). -/
inductive SExpr : Type
  | sigma : SExpr
  | single : List Bool → SExpr
  | cat : SExpr → SExpr → SExpr
  | cap : SExpr → SExpr → SExpr
  deriving DecidableEq

/-- Scott's least-fixed-point family `S`. -/
inductive InS : Set (List Bool) → Prop
  | univ : InS Set.univ
  | singleton (σ : List Bool) : InS {σ}
  | mul {X Y : Set (List Bool)} : InS X → InS Y → InS (concat X Y)
  | inter {X Y : Set (List Bool)} : InS X → InS Y → (X ∩ Y).Nonempty → InS (X ∩ Y)

theorem Ssys_master_mem : InS Set.univ := by sorry
theorem Ssys_master_nonempty : (Set.univ : Set (List Bool)).Nonempty := by
  exact ⟨[], Set.mem_univ []⟩
theorem Ssys_sub_master {X : Set (List Bool)} (_h : InS X) : X ⊆ Set.univ := by
  sorry
theorem Ssys_inter_mem {X Y Z : Set (List Bool)}
    (hX : InS X) (hY : InS Y) (hZ : InS Z) (hZsub : Z ⊆ X ∩ Y) : InS (X ∩ Y) := by
  sorry
/-- **Exercise 7.22.** The positive system `S` over `{0,1}*`. -/
def Ssys : NeighborhoodSystem (List Bool) where
  mem := InS
  master := Set.univ
  master_nonempty := Ssys_master_nonempty
  master_mem := Ssys_master_mem
  inter_mem := Ssys_inter_mem
  sub_master := Ssys_sub_master
instance Ssys_countable : Countable {S : Set (List Bool) // Ssys.mem S} := by
  sorry
theorem Ssys_embeds : Ssys ⊴ U := by sorry

end Exercise722

end Scott1980.Neighborhood

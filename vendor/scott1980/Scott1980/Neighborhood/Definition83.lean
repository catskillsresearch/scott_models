/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Proposition82

/-!
# Lecture VIII — Definition 8.3 (Scott 1981, PRG-19): projections and finitary retractions

**Definition 8.3.** A retraction `a : E → E` is called a *projection* provided `a ⊑ 1_E`; it is
*finitary* iff its fixed-point set is isomorphic to a domain.

Scott's remark right before the definition already shows every retraction of Proposition 8.2's
form is a projection: unwinding `X a Z ↔ ∃ Y ∈ D, X ⊆ Y ⊆ Z` gives `X ⊆ Z` immediately, i.e.
`a ⊑ I_E`. And Proposition 8.2's other half — `|D| ≅ Fix(a)` — says exactly that these retractions
are *finitary*, with `D` itself as the witnessing domain. So every `retractionOfSubsystem h` is a
finitary projection (`isProjection_retractionOfSubsystem`, `isFinitary_retractionOfSubsystem`).
Scott's remark that the converse fails ("not every retraction... even this condition is not
sufficient") is the content of Theorem 8.5, formalized separately.

Everything here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {D E : NeighborhoodSystem α}

/-- **Definition 8.3, first clause (Scott 1981, PRG-19).** A retraction `a : E → E` is a
*projection* provided `a ⊑ I_E`. (We do not separately require `IsRetraction a` in the
definition, matching Scott's usage where "projection" is applied to a retraction already in
hand; the conjunction is spelled out where needed, e.g. `IsFinitaryProjection`.) -/
def IsProjection (a : ApproximableMap E E) : Prop := IsRetraction a ∧ a ≤ idMap E

/-- **Definition 8.3, second clause (Scott 1981, PRG-19).** A retraction `a : E → E` is *finitary*
iff its fixed-point set `{y ∈ |E| ∣ a(y) = y}` — ordered by the inherited inclusion `⊑` — is
isomorphic to (the element poset of) some neighbourhood system. -/
def IsFinitary (a : ApproximableMap E E) : Prop :=
  ∃ (β : Type u) (F : NeighborhoodSystem β),
    Nonempty ({y : E.Element // a.toElementMap y = y} ≃o F.Element)

/-- A **finitary projection**: both clauses of Definition 8.3 together with `IsRetraction`. -/
def IsFinitaryProjection (a : ApproximableMap E E) : Prop := IsProjection a ∧ IsFinitary a

namespace Subsystem

variable {h : D ◁ E}

/-- **Scott's remark before Definition 8.3.** Every retraction `a = retractionOfSubsystem h` of
Proposition 8.2 satisfies `a ⊑ I_E`: unwinding `X a Z ↔ ∃ Y ∈ D, X ⊆ Y ⊆ Z` gives `X ⊆ Z`
directly. -/
theorem retractionOfSubsystem_le_idMap (h : D ◁ E) : retractionOfSubsystem h ≤ idMap E := by
  intro X Z hr
  obtain ⟨hEX, hEZ, Y, _, hXY, hYZ⟩ := (retractionOfSubsystem_rel h).mp hr
  exact ⟨hEX, hEZ, hXY.trans hYZ⟩

/-- **Every `retractionOfSubsystem h` is a projection** (Definition 8.3). -/
theorem isProjection_retractionOfSubsystem (h : D ◁ E) :
    IsProjection (retractionOfSubsystem h) :=
  ⟨isRetraction_retractionOfSubsystem h, retractionOfSubsystem_le_idMap h⟩

/-- **Every `retractionOfSubsystem h` is finitary** (Definition 8.3): its fixed-point set is
isomorphic to `|D|` itself, by Proposition 8.2's `elementIso`. -/
theorem isFinitary_retractionOfSubsystem (h : D ◁ E) :
    IsFinitary (retractionOfSubsystem h) :=
  ⟨α, D, ⟨(elementIso h).symm⟩⟩

/-- **Every `retractionOfSubsystem h` is a finitary projection** (Definition 8.3, both clauses). -/
theorem isFinitaryProjection_retractionOfSubsystem (h : D ◁ E) :
    IsFinitaryProjection (retractionOfSubsystem h) :=
  ⟨isProjection_retractionOfSubsystem h, isFinitary_retractionOfSubsystem h⟩

end Subsystem

end Scott1980.Neighborhood

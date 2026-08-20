/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Definition81
import Scott1980.Neighborhood.Proposition612

/-!
# Lecture VIII — Proposition 8.2 (Scott 1981, PRG-19): `D ◁ E` induces a retraction

**Proposition 8.2.** If `D ◁ E` and `a : E → E` is defined by

`X a Z` iff `∃ Y ∈ D. X ⊆ Y ⊆ Z`

for all `X, Z ∈ E`, then `a` is a retraction and `|D|` is isomorphic to the fixed-point set of `a`,
`{y ∈ |E| ∣ a(y) = y}`, under inclusion.

## The construction

Scott's own proof observes that the relation above is exactly `a = i ∘ j`, where `i : D → E`,
`j : E → D` are the injection/projection of Proposition 6.12 (`Subsystem.inj`/`Subsystem.proj`).
We take this as the *definition* (`retractionOfSubsystem`), which makes both halves of the theorem
short calculations with the category laws of Theorem 2.5:

* **`a` is a retraction.** `a ∘ a = i∘j∘i∘j = i∘(j∘i)∘j = i∘I_D∘j = i∘j = a`, using
  `Subsystem.proj_comp_inj : j ∘ i = I_D` (`isRetraction_retractionOfSubsystem`).
* **`|D| ≅ Fix(a)`.** The forward map `x ↦ i(x)` lands in `Fix(a)` because
  `a(i(x)) = i(j(i(x))) = i((j∘i)(x)) = i(x)`; the inverse is `y ↦ j(y)`, using
  `Subsystem.proj_comp_inj` again for the round trip `j(i(x)) = x`, and the fixed-point equation
  `a(y) = y` itself (unfolded to `i(j(y)) = y`) for the other round trip. Both `i` and `j` are
  monotone, and applying `j` to `i(x) ⊑ i(x')` recovers `x ⊑ x'` (again via `j ∘ i = I_D`), so the
  correspondence is an order-isomorphism, not just a bijection (`elementIso`).

Everything here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`), since Proposition 6.12
and Theorem 2.5 are.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem

/-- **Proposition 8.2's retraction `a = i ∘ j`.** As a neighbourhood relation (unfolding `inj`/
`proj`), `X a Z ↔ ∃ Y ∈ D, X ⊆ Y ⊆ Z` — exactly Scott's formula. -/
def retractionOfSubsystem (h : D ◁ E) : ApproximableMap E E := h.inj.comp h.proj

@[simp] theorem retractionOfSubsystem_rel (h : D ◁ E) {X Z : Set α} :
    (retractionOfSubsystem h).rel X Z ↔ E.mem X ∧ E.mem Z ∧ ∃ Y, D.mem Y ∧ X ⊆ Y ∧ Y ⊆ Z := by
  simp only [retractionOfSubsystem, comp_rel, inj_rel, proj_rel]
  constructor
  · rintro ⟨Y, ⟨hEX, hDY, hXY⟩, hDY', hEZ, hYZ⟩
    exact ⟨hEX, hEZ, Y, hDY, hXY, hYZ⟩
  · rintro ⟨hEX, hEZ, Y, hDY, hXY, hYZ⟩
    exact ⟨Y, ⟨hEX, hDY, hXY⟩, hDY, hEZ, hYZ⟩

/-- **Proposition 8.2, first half.** `retractionOfSubsystem h` is a retraction: `a ∘ a = a`, via
`a ∘ a = i∘(j∘i)∘j = i∘I_D∘j = i∘j = a`. -/
theorem isRetraction_retractionOfSubsystem (h : D ◁ E) :
    IsRetraction (retractionOfSubsystem h) := by
  show (h.inj.comp h.proj).comp (h.inj.comp h.proj) = h.inj.comp h.proj
  rw [comp_assoc, ← comp_assoc h.proj h.inj h.proj, h.proj_comp_inj, idMap_comp]

/-- `retractionOfSubsystem h` fixes exactly `i(x)` for `x ∈ |D|`: `a(i(x)) = i(x)`. -/
theorem retractionOfSubsystem_toElementMap_inj (h : D ◁ E) (x : D.Element) :
    (retractionOfSubsystem h).toElementMap (h.inj.toElementMap x) = h.inj.toElementMap x := by
  have h1 : (retractionOfSubsystem h).toElementMap (h.inj.toElementMap x)
      = h.inj.toElementMap (h.proj.toElementMap (h.inj.toElementMap x)) :=
    toElementMap_comp h.inj h.proj (h.inj.toElementMap x)
  have h2 : h.proj.toElementMap (h.inj.toElementMap x) = (h.proj.comp h.inj).toElementMap x :=
    (toElementMap_comp h.proj h.inj x).symm
  rw [h1, h2, h.proj_comp_inj, toElementMap_idMap]

/-- **Proposition 8.2, second half.** `|D|` is order-isomorphic to the fixed-point set of
`a = retractionOfSubsystem h`, via `x ↦ i(x)` with inverse `y ↦ j(y)`. -/
def elementIso (h : D ◁ E) :
    D.Element ≃o {y : E.Element // (retractionOfSubsystem h).toElementMap y = y} where
  toFun x := ⟨h.inj.toElementMap x, retractionOfSubsystem_toElementMap_inj h x⟩
  invFun y := h.proj.toElementMap y.1
  left_inv x := by
    have h1 : h.proj.toElementMap (h.inj.toElementMap x) = (h.proj.comp h.inj).toElementMap x :=
      (toElementMap_comp h.proj h.inj x).symm
    show h.proj.toElementMap (h.inj.toElementMap x) = x
    rw [h1, h.proj_comp_inj, toElementMap_idMap]
  right_inv y := by
    apply Subtype.ext
    have hfix : (h.inj.comp h.proj).toElementMap y.1 = y.1 := y.2
    have h1 : (h.inj.comp h.proj).toElementMap y.1 = h.inj.toElementMap (h.proj.toElementMap y.1) :=
      toElementMap_comp h.inj h.proj y.1
    show h.inj.toElementMap (h.proj.toElementMap y.1) = y.1
    rw [← h1]; exact hfix
  map_rel_iff' := by
    intro x x'
    show h.inj.toElementMap x ≤ h.inj.toElementMap x' ↔ x ≤ x'
    constructor
    · intro hle
      have hmono := h.proj.toElementMap_mono hle
      have h1 : h.proj.toElementMap (h.inj.toElementMap x) = (h.proj.comp h.inj).toElementMap x :=
        (toElementMap_comp h.proj h.inj x).symm
      have h2 : h.proj.toElementMap (h.inj.toElementMap x') = (h.proj.comp h.inj).toElementMap x' :=
        (toElementMap_comp h.proj h.inj x').symm
      rw [h1, h2, h.proj_comp_inj, toElementMap_idMap, toElementMap_idMap] at hmono
      exact hmono
    · intro hle
      exact h.inj.toElementMap_mono hle

/-- **Proposition 8.2 (Scott 1981, PRG-19), packaged.** `D ◁ E` induces a retraction `a` on `E`
whose fixed-point set is (order-isomorphic to) `|D|`. -/
theorem retraction_of_subsystem (h : D ◁ E) :
    IsRetraction (retractionOfSubsystem h) ∧
      Nonempty (D.Element ≃o {y : E.Element // (retractionOfSubsystem h).toElementMap y = y}) :=
  ⟨isRetraction_retractionOfSubsystem h, ⟨elementIso h⟩⟩

end Subsystem

end Scott1980.Neighborhood

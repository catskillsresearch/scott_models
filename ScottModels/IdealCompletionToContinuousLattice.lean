import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Directed
import Scott1972.ContinuousLattice.WayBelow

/-!
# Algebraic complete lattices → continuous lattices (ideal-completion → 1972)

An **algebraic** complete lattice — every element is the directed supremum of the
compact elements below it — is a continuous lattice in Scott's sense
(`IsContinuousLattice`). Compact elements are way-below anything they lie under,
via Scott-openness of `Set.Ici k`.

This is the classical frontier of this article’s blueprint
(`idealCompletion_to_continuousLattice`): Scott's `≪` is topological.
-/

namespace ScottModels

open Scott1972.ContinuousLattice
open scoped Scott1972.ContinuousLattice

namespace IdealCompletionToContinuousLattice

variable {D : Type*} [CompleteLattice D]

/-- Order-theoretic compactness: inaccessible by nonempty directed suprema. -/
def IsCompactElement (k : D) : Prop :=
  ∀ ⦃S : Set D⦄, S.Nonempty → DirectedOn (· ≤ ·) S → k ≤ sSup S → ∃ s ∈ S, k ≤ s

/-- Compactness implies `Set.Ici k` is Scott-open. -/
theorem scottOpen_Ici_of_compact {k : D} (hk : IsCompactElement k) :
    ScottOpen (Set.Ici k) := by
  refine ⟨isUpperSet_Ici k, fun S hS hSdir hmem => ?_⟩
  obtain ⟨s, hsS, hks⟩ := hk hS hSdir (Set.mem_Ici.1 hmem)
  exact ⟨s, hsS, Set.mem_Ici.2 hks⟩

/-- Compact elements are way below anything above them. -/
theorem compact_wayBelow {k y : D} (hk : IsCompactElement k) (hky : k ≤ y) : k ≪ y :=
  ⟨Set.Ici k, scottOpen_Ici_of_compact hk, Set.mem_Ici.2 hky, subset_rfl⟩

/-- Algebraicity: every element is the directed lub of compact elements below it. -/
def IsAlgebraicLattice (D : Type*) [CompleteLattice D] : Prop :=
  ∀ y : D,
    let S := {x : D | IsCompactElement x ∧ x ≤ y}
    S.Nonempty ∧ DirectedOn (· ≤ ·) S ∧ sSup S = y

/-- **Blueprint:** algebraic complete lattice ⇒ continuous lattice (Scott Def. 2.3). -/
theorem isContinuousLattice_of_algebraic (hA : IsAlgebraicLattice D) :
    IsContinuousLattice D := by
  intro y
  obtain ⟨hne, hdir, hsup⟩ := hA y
  refine ⟨?_, fun z hz => ?_⟩
  · -- y is an upper bound of `{x | x ≪ y}`
    intro x hx
    exact hx.le
  · -- any upper bound of the way-belows is ≥ y
    -- every compact ≤ y is ≪ y, hence ≤ z
    have hle : sSup {x : D | IsCompactElement x ∧ x ≤ y} ≤ z := by
      refine sSup_le fun x hx => ?_
      exact hz (compact_wayBelow hx.1 hx.2)
    exact hsup ▸ hle

end IdealCompletionToContinuousLattice

/-- Blueprint name. -/
abbrev idealCompletion_to_continuousLattice {D : Type*} [CompleteLattice D]
    (hA : IdealCompletionToContinuousLattice.IsAlgebraicLattice D) :
    IsContinuousLattice D :=
  IdealCompletionToContinuousLattice.isContinuousLattice_of_algebraic hA

end ScottModels

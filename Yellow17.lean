/-
Copyright (c) 2000-2012 Association of Mizar Users
  (Stowarzyszenie Uzytkownikow Mizara, Bialystok, Poland).
Copyright (c) 2026 Lars Warren Ericson.
Released under the GNU General Public License version 3.0 or later,
or the Creative Commons Attribution-ShareAlike License version 3.0 or later.
See the notices in `yellow17.miz`.
Authors: Bartłomiej Skorulski (Mizar), Lars Warren Ericson (Lean 4).
-/

import Mathlib.Topology.Compactness.Compact

/-!
# The Tychonoff theorem (Mizar `YELLOW_17`)

Idiomatic Lean 4 translation of Bartłomiej Skorulski, *The Tichonov Theorem*
(Mizar article `YELLOW_17`, received 23 May 2000). Mizar’s set-coded products
`product F`, projections `proj(F,i)`, and updates `f+*(i,xi)` become dependent
functions `∀ i, X i`, evaluation `Function.eval`, and `Function.update`.
-/

open Set Function Topology TopologicalSpace

set_option linter.unusedSectionVars false

universe u v

variable {ι : Type u} {X : ι → Type v}

/-! ## Product, projection, and update (`Th1`–`Th13`) -/

/-- **Mizar `Th1` / `Th9`.** A nonempty intersection of the singleton cylinder
over `xi` with the cylinder over `Ai` forces `xi ∈ Ai`. -/
theorem eval_singleton_inter_mem {i : ι} {xi : X i} {Ai : Set (X i)}
    (h : ((eval i ⁻¹' ({xi} : Set (X i))) ∩ (eval i ⁻¹' Ai)).Nonempty) :
    xi ∈ Ai := by
  obtain ⟨f, hf₁, hf₂⟩ := h
  exact (show f i = xi from hf₁) ▸ hf₂

/-- **Mizar `Th2`.** Updating one coordinate of a point of `Set.pi univ s`
stays in the product box. -/
theorem update_mem_univ_pi [DecidableEq ι] {s : ∀ i, Set (X i)} {f : ∀ i, X i}
    {i : ι} {xi : X i} (hxi : xi ∈ s i) (hf : f ∈ univ.pi s) :
    update f i xi ∈ univ.pi s := by
  intro j _
  by_cases hj : j = i
  · subst hj
    simpa using hxi
  · simpa [update_of_ne hj] using hf j (mem_univ j)

/-- **Mizar `Th3`.** The `i`-th projection of a product of inhabited types is
surjective onto the `i`-th factor. -/
theorem range_eval_eq_univ [∀ j, Nonempty (X j)] (i : ι) :
    range (eval i : (∀ j, X j) → X i) = univ :=
  range_eval (α := X) i

/-- **Mizar `Th4` / `Th10`.** The full cylinder over a factor is the whole
product. -/
@[simp] theorem preimage_eval_univ (i : ι) :
    (eval i : (∀ j, X j) → X i) ⁻¹' (univ : Set (X i)) = univ :=
  preimage_univ

/-- **Mizar `Th5` / `Th11`.** Coordinate update lands in the singleton cylinder. -/
theorem update_mem_eval_singleton [DecidableEq ι] (f : ∀ i, X i) (i : ι)
    (xi : X i) : update f i xi ∈ eval i ⁻¹' ({xi} : Set (X i)) := by
  simp

/-- **Mizar `Th8`.** Projection is evaluation. -/
theorem eval_apply (f : ∀ i, X i) (i : ι) : eval i f = f i :=
  rfl

/-- **Mizar `Lm1` / `Th6` / `Th13`.** Membership in an off-axis cylinder is
unchanged by updating a different coordinate. -/
theorem mem_preimage_eval_update_iff [DecidableEq ι] {f : ∀ i, X i}
    {i₁ i₂ : ι} {xi₁ : X i₁} {Ai₂ : Set (X i₂)} (hne : i₁ ≠ i₂) :
    update f i₁ xi₁ ∈ eval i₂ ⁻¹' Ai₂ ↔ f ∈ eval i₂ ⁻¹' Ai₂ := by
  simp [update_of_ne hne.symm]

/-- **Mizar `Th7` / `Th12`, same coordinate.** -/
theorem eval_singleton_subset_eval_same [DecidableEq ι] {i : ι} {xi : X i}
    {Ai : Set (X i)} [Nonempty (∀ j, X j)] :
    eval i ⁻¹' ({xi} : Set (X i)) ⊆ eval i ⁻¹' Ai ↔ xi ∈ Ai := by
  classical
  refine ⟨fun h => ?_, fun hxi => preimage_mono (singleton_subset_iff.2 hxi)⟩
  obtain ⟨g⟩ := ‹Nonempty (∀ j, X j)›
  simpa using h (update_mem_eval_singleton g i xi)

/-- **Mizar `Th7` / `Th12`, distinct coordinates.** A proper cylinder cannot
contain a singleton cylinder on another axis. -/
theorem eval_singleton_not_subset_eval_of_ne [DecidableEq ι]
    [∀ j, Nonempty (X j)] {i₁ i₂ : ι} {xi₁ : X i₁} {Ai₂ : Set (X i₂)}
    (hne : i₁ ≠ i₂) (hAi : Ai₂ ≠ univ) :
    ¬ eval i₁ ⁻¹' ({xi₁} : Set (X i₁)) ⊆ eval i₂ ⁻¹' Ai₂ := by
  obtain ⟨xi₂, hxi₂⟩ := nonempty_compl.mpr hAi
  let f : ∀ j, X j := fun _ => Classical.choice inferInstance
  intro hsub
  have hmem : update (update f i₂ xi₂) i₁ xi₁ ∈ eval i₂ ⁻¹' Ai₂ :=
    hsub (update_mem_eval_singleton (update f i₂ xi₂) i₁ xi₁)
  have : update f i₂ xi₂ ∈ eval i₂ ⁻¹' Ai₂ :=
    (mem_preimage_eval_update_iff (f := update f i₂ xi₂) hne).1 hmem
  exact hxi₂ (by simpa using this)

/-- **Mizar `Th7` / `Th12`.** A proper cylinder contains a singleton cylinder
iff the coordinates agree and the point lies in the set. -/
theorem eval_singleton_subset_eval_iff [DecidableEq ι] [∀ j, Nonempty (X j)]
    {i₁ i₂ : ι} {xi₁ : X i₁} {Ai₂ : Set (X i₂)} (hAi : Ai₂ ≠ univ) :
    eval i₁ ⁻¹' ({xi₁} : Set (X i₁)) ⊆ eval i₂ ⁻¹' Ai₂ ↔
      ∃ h : i₁ = i₂, xi₁ ∈ h ▸ Ai₂ := by
  refine ⟨fun hsub => ?_, ?_⟩
  · have hi : i₁ = i₂ := by
      by_contra hne
      exact eval_singleton_not_subset_eval_of_ne hne hAi hsub
    subst hi
    exact ⟨rfl, (eval_singleton_subset_eval_same).1 hsub⟩
  · rintro ⟨rfl, hxi⟩
    exact (eval_singleton_subset_eval_same).2 hxi

/-- **Mizar scheme `ElProductEx`.** A point of the product can be assembled
coordinatewise. -/
noncomputable def elProductEx {P : ∀ i, X i → Prop}
    (h : ∀ i, ∃ x : X i, P i x) : ∀ i, X i :=
  fun i => (h i).choose

theorem elProductEx_spec {P : ∀ i, X i → Prop} (h : ∀ i, ∃ x : X i, P i x)
    (i : ι) : P i (elProductEx h i) :=
  (h i).choose_spec

/-! ## Cylinder subbasis (`Th16`–`Th18`) -/

variable [∀ i, TopologicalSpace (X i)]

/-- Open cylinders `eval i ⁻¹' U`, the product prebasis of `YELLOW_18`. -/
def cylinderSubbasis (X : ι → Type v) [∀ i, TopologicalSpace (X i)] :
    Set (Set (∀ i, X i)) :=
  {C | ∃ (i : ι) (U : Set (X i)), IsOpen U ∧ C = eval i ⁻¹' U}

/-- **Mizar `Th16`.** Every prebasis element is an open cylinder. -/
theorem mem_cylinderSubbasis_iff {A : Set (∀ i, X i)} :
    A ∈ cylinderSubbasis X ↔
      ∃ (i : ι) (U : Set (X i)), IsOpen U ∧ A = eval i ⁻¹' U :=
  Iff.rfl

/-- The open cylinders generate the product topology. -/
theorem pi_eq_generateFrom_cylinderSubbasis :
    (Pi.topologicalSpace : TopologicalSpace (∀ i, X i)) =
      generateFrom (cylinderSubbasis X) := by
  refine le_antisymm ?_ ?_
  · apply le_generateFrom
    rintro _ ⟨i, U, hU, rfl⟩
    exact hU.preimage (continuous_apply i)
  · rw [pi_eq_generateFrom]
    apply le_generateFrom
    rintro t ⟨s, I, hI, rfl⟩
    let := generateFrom (cylinderSubbasis X)
    have : Set.pi (I : Set ι) s = ⋂ i ∈ I, eval i ⁻¹' s i := by
      ext f
      simp [Set.mem_pi]
    rw [this]
    exact isOpen_biInter_finset fun i hi =>
      isOpen_generateFrom_of_mem ⟨i, s i, hI i hi, rfl⟩

/-- **Mizar `Th17`.** If a singleton cylinder sits inside a proper prebasis
element, that element is a proper open cylinder on the same axis. -/
theorem cylinder_of_singleton_subset [DecidableEq ι] [∀ j, Nonempty (X j)]
    {i : ι} {xi : X i} {A : Set (∀ i, X i)}
    (hA : A ∈ cylinderSubbasis X)
    (hsub : eval i ⁻¹' ({xi} : Set (X i)) ⊆ A)
    (hne : A ≠ univ) :
    ∃ U : Set (X i), U ≠ univ ∧ xi ∈ U ∧ IsOpen U ∧ A = eval i ⁻¹' U := by
  obtain ⟨i₂, U, hUo, rfl⟩ := hA
  have hU : U ≠ univ := by
    intro h
    exact hne (by simp [h])
  obtain ⟨hii, hxi⟩ := (eval_singleton_subset_eval_iff (i₁ := i) (i₂ := i₂)
    (xi₁ := xi) (Ai₂ := U) hU).1 hsub
  subst hii
  exact ⟨U, hU, hxi, hUo, rfl⟩

/-- **Mizar `Th18`.** An open cover of a factor lifts to a cylinder cover of
the product. -/
theorem univ_subset_iUnion_preimage_eval {i : ι} {Fi : Set (Set (X i))}
    (h : (univ : Set (X i)) ⊆ ⋃₀ Fi) :
    (univ : Set (∀ j, X j)) ⊆ ⋃₀ ((fun U : Set (X i) => eval i ⁻¹' U) '' Fi) := by
  intro f _
  obtain ⟨U, hU, hfU⟩ := mem_sUnion.1 (h (mem_univ (f i)))
  exact mem_sUnion.2 ⟨eval i ⁻¹' U, mem_image_of_mem _ hU, hfU⟩

/-! ## Compactness via open covers and a subbasis (`Th14`–`Th15`) -/

/-- **Mizar `Th14`.** Compactness is the finite-open-subcover property. -/
theorem isCompact_iff_finite_open_subcover {Y : Type u} [TopologicalSpace Y]
    {s : Set Y} :
    IsCompact s ↔ ∀ {κ : Type u} (U : κ → Set Y),
      (∀ k, IsOpen (U k)) → (s ⊆ ⋃ k, U k) →
        ∃ t : Finset κ, s ⊆ ⋃ k ∈ t, U k :=
  isCompact_iff_finite_subcover

/-- **Mizar `Th15`.** Alexander’s subbasis theorem: it is enough to test
covers drawn from a generating family. -/
theorem isCompact_of_subbasis_finite_subcover {Y : Type*}
    [T : TopologicalSpace Y] {S : Set (Set Y)} (hTS : T = generateFrom S)
    {s : Set Y}
    (h : ∀ P ⊆ S, s ⊆ ⋃₀ P → ∃ Q ⊆ P, Q.Finite ∧ s ⊆ ⋃₀ Q) :
    IsCompact s :=
  isCompact_generateFrom hTS h

/-! ## Combinatorics of cylinder covers (`Th19`–`Th22`) -/

/-- **Mizar `Th19`.** If a singleton fiber is covered by `G` but no member of
`G` contains the fiber, then `G` covers the whole product. -/
theorem univ_subset_sUnion_of_fiber_cover_no_strict [DecidableEq ι]
    [∀ j, Nonempty (X j)] {i : ι} {xi : X i} {G : Set (Set (∀ j, X j))}
    (hG : G ⊆ cylinderSubbasis X)
    (hcover : eval i ⁻¹' ({xi} : Set (X i)) ⊆ ⋃₀ G)
    (hstrict : ∀ A ∈ G, ¬ eval i ⁻¹' ({xi} : Set (X i)) ⊆ A) :
    (univ : Set (∀ j, X j)) ⊆ ⋃₀ G := by
  intro f _
  obtain ⟨A, hAG, hfA⟩ := mem_sUnion.1 (hcover (update_mem_eval_singleton f i xi))
  obtain ⟨i₂, U, -, rfl⟩ := hG hAG
  have hU : U ≠ univ := by
    intro hU
    exact hstrict _ hAG (by simp [hU])
  have hne : i ≠ i₂ := by
    intro hii
    subst hii
    have : (eval i ⁻¹' ({xi} : Set (X i)) ∩ eval i ⁻¹' U).Nonempty :=
      ⟨update f i xi, update_mem_eval_singleton f i xi, hfA⟩
    have hxi : xi ∈ U := eval_singleton_inter_mem this
    exact hstrict _ hAG ((eval_singleton_subset_eval_same).2 hxi)
  exact mem_sUnion.2
    ⟨eval i₂ ⁻¹' U, hAG, (mem_preimage_eval_update_iff hne).1 hfA⟩

/-- **Mizar `Th20`.** Failure of finite product covers forces a fiber cover to
use a member that contains the fiber. -/
theorem exists_cylinder_containing_fiber_of_finite [DecidableEq ι]
    [∀ j, Nonempty (X j)] {i : ι} {xi : X i} {F : Set (Set (∀ j, X j))}
    (hF : F ⊆ cylinderSubbasis X)
    (hno : ∀ G ⊆ F, G.Finite → ¬ (univ : Set (∀ j, X j)) ⊆ ⋃₀ G)
    {G : Set (Set (∀ j, X j))} (hGF : G ⊆ F) (hGfin : G.Finite)
    (hcover : eval i ⁻¹' ({xi} : Set (X i)) ⊆ ⋃₀ G) :
    ∃ A ∈ G, eval i ⁻¹' ({xi} : Set (X i)) ⊆ A := by
  by_contra h
  have hstrict : ∀ A ∈ G, ¬ eval i ⁻¹' ({xi} : Set (X i)) ⊆ A := by
    simpa [not_exists] using h
  exact hno G hGF hGfin
    (univ_subset_sUnion_of_fiber_cover_no_strict (Subset.trans hGF hF) hcover
      hstrict)

/-- **Mizar `Th21`.** Extract a proper open cylinder on the same axis from a
finite fiber cover. -/
theorem exists_proper_open_cylinder_of_fiber_cover [DecidableEq ι]
    [∀ j, Nonempty (X j)] {i : ι} {xi : X i} {F : Set (Set (∀ j, X j))}
    (hF : F ⊆ cylinderSubbasis X)
    (hno : ∀ G ⊆ F, G.Finite → ¬ (univ : Set (∀ j, X j)) ⊆ ⋃₀ G)
    {G : Set (Set (∀ j, X j))} (hGF : G ⊆ F) (hGfin : G.Finite)
    (hcover : eval i ⁻¹' ({xi} : Set (X i)) ⊆ ⋃₀ G) :
    ∃ U : Set (X i), U ≠ univ ∧ xi ∈ U ∧ IsOpen U ∧ eval i ⁻¹' U ∈ G := by
  obtain ⟨A, hAG, hsub⟩ :=
    exists_cylinder_containing_fiber_of_finite hF hno hGF hGfin hcover
  have hAne : A ≠ univ := by
    intro hA
    exact hno G hGF hGfin (fun _ _ => mem_sUnion.2 ⟨A, hAG, by simp [hA]⟩)
  obtain ⟨U, hUne, hxi, hUo, rfl⟩ :=
    cylinder_of_singleton_subset (hF (hGF hAG)) hsub hAne
  exact ⟨U, hUne, hxi, hUo, hAG⟩

/-- **Mizar `Th22`.** Compactness of a factor, plus no finite product cover,
produces a point whose singleton fiber also has no finite cover from `F`. -/
theorem exists_point_fiber_not_finitely_covered [DecidableEq ι]
    [∀ j, Nonempty (X j)] {i : ι} {F : Set (Set (∀ j, X j))}
    (hF : F ⊆ cylinderSubbasis X)
    (hcomp : IsCompact (univ : Set (X i)))
    (hno : ∀ G ⊆ F, G.Finite → ¬ (univ : Set (∀ j, X j)) ⊆ ⋃₀ G) :
    ∃ xi : X i, ∀ G ⊆ F, G.Finite →
      ¬ eval i ⁻¹' ({xi} : Set (X i)) ⊆ ⋃₀ G := by
  by_contra! h
  have : ∀ xi : X i, ∃ U : Set (X i),
      xi ∈ U ∧ IsOpen U ∧ eval i ⁻¹' U ∈ F := by
    intro xi
    obtain ⟨G, hGF, hGfin, hcover⟩ := h xi
    obtain ⟨U, -, hxi, hUo, hUG⟩ :=
      exists_proper_open_cylinder_of_fiber_cover hF hno hGF hGfin hcover
    exact ⟨U, hxi, hUo, hGF hUG⟩
  choose U hxi hUo hUF using this
  have hcoverᵢ : (univ : Set (X i)) ⊆ ⋃ xi : X i, U xi := by
    intro xi _
    exact mem_iUnion.2 ⟨xi, hxi xi⟩
  obtain ⟨t, ht⟩ :=
    (isCompact_iff_finite_subcover.1 hcomp) U hUo hcoverᵢ
  let G : Set (Set (∀ j, X j)) := (fun xi : X i => eval i ⁻¹' U xi) '' (t : Set (X i))
  have hGF : G ⊆ F := by
    rintro _ ⟨xi, -, rfl⟩
    exact hUF xi
  have hGfin : G.Finite := (t.finite_toSet).image _
  have hGcover : (univ : Set (∀ j, X j)) ⊆ ⋃₀ G := by
    intro f _
    obtain ⟨xi, hxit, hfU⟩ := mem_iUnion₂.1 (ht (mem_univ (f i)))
    exact mem_sUnion.2 ⟨eval i ⁻¹' U xi, ⟨xi, hxit, rfl⟩, hfU⟩
  exact hno G hGF hGfin hGcover

/-! ## The Tychonoff theorem -/

/-- **Mizar Tichonov Theorem, set form.** An arbitrary product of compact
sets is compact. -/
theorem yellow17_tychonoff_sets {s : ∀ i, Set (X i)}
    (hs : ∀ i, IsCompact (s i)) :
    IsCompact (univ.pi s) :=
  isCompact_univ_pi hs

/-- **Mizar Tichonov Theorem.** A dependent product of compact spaces is
compact. -/
theorem yellow17_tychonoff [∀ i, CompactSpace (X i)] :
    CompactSpace (∀ i, X i) :=
  inferInstance

/-- Space-level form matching the Mizar statement: if each factor is compact,
then the product is compact. -/
theorem yellow17_tychonoff' (h : ∀ i, CompactSpace (X i)) :
    CompactSpace (∀ i, X i) :=
  let _ := h
  inferInstance

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Theorem75
import Scott1980.Neighborhood.Definition610
import Scott1980.Neighborhood.Proposition611
import Scott1980.Neighborhood.Definition72
import Scott1980.Neighborhood.Exercise714
import Scott1980.Neighborhood.UComputablePresentation

/-!
# Exercise 8.15 (Scott 1981, PRG-19) — `{X ∣ X ◁ D}` is effectively presented if `D` is

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VIII.

> **Exercise 8.15.** Give a *direct* proof that the domain `{X ∣ X ◁ D}` is effectively presented
> if `D` is. (Hint: the finite elements of the domain correspond exactly to the finite systems
> `X ◁ D`.) In the case of `D = 𝒰`, show that the computable elements of the domain correspond
> exactly to the effectively presented domains (up to effective isomorphism).

Scott's `{D' ∣ D' ◁ D}` (ordered by the subsystem relation `◁`, Definition 6.10) is already known to
*be* a domain: Proposition 6.11 (`Proposition611.subsystemReprIso`) exhibits it as order-isomorphic to
`|reprSystem (subFam D) …|`, via the **abstract, `Classical.choice`-laden** representation theorem of
Exercise 2.22. Scott explicitly asks here for a *direct* proof of effective presentability, and the
hint ("finite elements ↔ finite systems `X ◁ D`") points at a concrete, `ℕ`-indexed reconstruction
instead — reusing `Theorem75.lean`'s `interFrom`/`idxchain`/`bitSelect`/`decodeList` toolkit (built
there for exactly this kind of "finite consistent sub-selection" bookkeeping).

## Plan (recorded in `HANDOFF.md` and `arxiv.md`, worked in sequence)

Fix `D : NeighborhoodSystem α` and a `ComputablePresentation P` of `D`.

1. **`Fin(js)`, the finitely generated subsystem** (this file's `finGen`/`finGenSys`): for a finite
   index list `js : List ℕ`, the set of *consistent sub-meets* `Fin(js) := {Y ∣ ∃ sub ⊑ js, D.mem Y ∧
   Y = interFrom P D.master sub}`. This is itself a subsystem `finGenSys(js) ◁ D`, and
   **`Fin_le_iff_forall_mem`**: `Fin(js) ⊆ D'.mem ↔ ∀ i ∈ js, D'.mem (P.X i)` for any `D' ◁ D` — the
   single workhorse lemma for everything downstream (proved by induction on `js`, using
   `interFrom_mem_of_witness` from `Theorem75.lean` to handle "an intermediate partial meet along a
   consistent chain is itself consistent").
2. **The reconstructed system `SubD`** (token type `List ℕ`): neighbourhoods are the anti-monotone
   principal up-sets `nbhd(js) := {js' ∣ Fin(js) ⊆ Fin(js')}`.
3. **The order isomorphism `SubD.Element ≃o {D' ∣ D' ◁ D}`** — fully choice-free, unlike Exercise 2.22.
4. **`ComputablePresentation SubD`** — Scott's two relations reduce to *bounded* quantifiers over
   `bitSelect`-selected sub-lists, decided via `consChain_iff`/`idxchain_spec`/`P.eq_computable`.
5. **Main theorem**: `D.IsEffectivelyGiven → {D' ∣ D' ◁ D}` is (isomorphic to) an effectively given
   domain.
6. (Second half, `D = 𝒰`): deferred pending 1–5.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α}

/-! ## Subgoal 1 — `Fin(js)`, the finitely generated subsystem -/

section FinGen

variable (P : ComputablePresentation D)

/-- **`Fin(js)`**: the finitely generated subsystem of `D` on the index list `js` — the set of
`D`-consistent "sub-meets" `interFrom P D.master sub` for sublists `sub ⊑ js`. Every member is
automatically a `D`-neighbourhood (the `D.mem Y` conjunct), so `finGen P js ⊆ D.mem` by
construction. -/
def finGen (js : List ℕ) : Set (Set α) :=
  {Y | ∃ sub : List ℕ, sub.Sublist js ∧ D.mem Y ∧ Y = interFrom P D.master sub}

/-- `D.master ∈ Fin(js)` always (witness: the empty sub-selection). -/
theorem master_mem_finGen (js : List ℕ) : D.master ∈ finGen P js :=
  ⟨[], List.nil_sublist js, D.master_mem, rfl⟩

/-- **Monotonicity.** A sublist generates a smaller (or equal) finitely generated subsystem. -/
theorem finGen_mono {js js' : List ℕ} (h : js.Sublist js') : finGen P js ⊆ finGen P js' :=
  fun _ ⟨sub, hsub, hD, hY⟩ => ⟨sub, hsub.trans h, hD, hY⟩

/-- Every member of `Fin(js)` is a `D`-neighbourhood. -/
theorem finGen_sub_mem {js : List ℕ} {Y : Set α} : Y ∈ finGen P js → D.mem Y :=
  fun ⟨_, _, hD, _⟩ => hD

/-- Every member of `Fin(js)` is a subset of `D.master`. -/
theorem finGen_sub_master {js : List ℕ} {Y : Set α} (h : Y ∈ finGen P js) : Y ⊆ D.master :=
  D.sub_master (finGen_sub_mem P h)

/-- The single-index generator `P.X i` lies in `Fin(js)` whenever `i ∈ js` (witness: the singleton
sub-selection `[i]`, always `D`-consistent since `interFrom P D.master [i] = D.master ∩ P.X i =
P.X i` using `P.X i ⊆ D.master`). -/
theorem principal_mem_finGen {js : List ℕ} {i : ℕ} (hi : i ∈ js) : P.X i ∈ finGen P js := by
  refine ⟨[i], (List.singleton_sublist).mpr hi, P.mem_X i, ?_⟩
  apply Set.ext
  intro z
  rw [mem_interFrom]
  constructor
  · intro hz
    exact ⟨D.sub_master (P.mem_X i) hz,
      fun j hj => by rw [List.mem_singleton] at hj; subst hj; exact hz⟩
  · rintro ⟨_, hall⟩
    exact hall i (List.mem_singleton.mpr rfl)

/-! ### `Fin(js)` is a genuine subsystem of `D`. -/

section Combine

variable (js sub1 sub2 : List ℕ)

/-- The sub-selection of `js` consisting of entries belonging to `sub1` or `sub2` — the `List`-level
"join" of two sub-selections, used to combine two consistent sub-meets into a third. -/
def combineSub : List ℕ := js.filter (fun j => decide (j ∈ sub1 ∨ j ∈ sub2))

theorem combineSub_sublist : (combineSub js sub1 sub2).Sublist js := List.filter_sublist

variable {js sub1 sub2}

theorem mem_combineSub {j : ℕ} :
    j ∈ combineSub js sub1 sub2 ↔ j ∈ js ∧ (j ∈ sub1 ∨ j ∈ sub2) := by
  unfold combineSub
  rw [List.mem_filter, decide_eq_true_iff]

/-- **Combining two consistent sub-meets.** If `sub1, sub2 ⊑ js`, then `interFrom P D.master
(combineSub js sub1 sub2) = interFrom P D.master sub1 ∩ interFrom P D.master sub2` — a pure
set-theoretic fact about `interFrom`'s membership characterization (no consistency needed here). -/
theorem interFrom_combineSub_eq (h1 : sub1.Sublist js) (h2 : sub2.Sublist js) :
    interFrom P D.master (combineSub js sub1 sub2) =
      interFrom P D.master sub1 ∩ interFrom P D.master sub2 := by
  apply Set.ext
  intro z
  rw [Set.mem_inter_iff, mem_interFrom, mem_interFrom, mem_interFrom]
  constructor
  · rintro ⟨hzm, hall⟩
    exact ⟨⟨hzm, fun j hj => hall j (mem_combineSub.mpr ⟨h1.subset hj, Or.inl hj⟩)⟩,
      hzm, fun j hj => hall j (mem_combineSub.mpr ⟨h2.subset hj, Or.inr hj⟩)⟩
  · rintro ⟨⟨hzm, hall1⟩, _, hall2⟩
    refine ⟨hzm, fun j hj => ?_⟩
    obtain ⟨_, hj1 | hj2⟩ := mem_combineSub.mp hj
    · exact hall1 j hj1
    · exact hall2 j hj2

end Combine

/-- **`Fin(js)` as a `NeighborhoodSystem`.** Master is `D.master`; closure under consistent
intersection combines the two witnessing sub-selections via `combineSub`. -/
def finGenSys (js : List ℕ) : NeighborhoodSystem α where
  mem Y := Y ∈ finGen P js
  master := D.master
  master_mem := master_mem_finGen P js
  inter_mem := by
    rintro X Y Z ⟨sub1, h1, hDX, hX⟩ ⟨sub2, h2, hDY, hY⟩ ⟨sub3, h3, hDZ, hZ⟩ hZsub
    exact ⟨combineSub js sub1 sub2, combineSub_sublist js sub1 sub2,
      D.inter_mem hDX hDY hDZ hZsub, by
        rw [interFrom_combineSub_eq P h1 h2, hX, hY]⟩
  sub_master := fun ⟨sub, _, _, hY⟩ => hY ▸ interFrom_subset P

@[simp] theorem mem_finGenSys {js : List ℕ} {Y : Set α} :
    (finGenSys P js).mem Y ↔ Y ∈ finGen P js := Iff.rfl

/-- **`Fin(js)` is a subsystem of `D`** (Definition 6.10). -/
theorem finGenSys_subsystem (js : List ℕ) : finGenSys P js ◁ D where
  master_eq := rfl
  sub := finGen_sub_mem P
  inter_closed := by
    rintro X Y ⟨sub1, h1, hDX, hX⟩ ⟨sub2, h2, hDY, hY⟩ hXY
    exact ⟨combineSub js sub1 sub2, combineSub_sublist js sub1 sub2, hXY, by
      rw [interFrom_combineSub_eq P h1 h2, hX, hY]⟩

/-! ### The workhorse lemma: `Fin(js) ⊆ D'.mem ↔ ∀ i ∈ js, D'.mem (P.X i)`. -/

/-- `interFrom P A (j :: sub)` splits off the head as an intersection with `P.X j` — a pure
set-theoretic fact from `mem_interFrom`'s characterization. -/
theorem interFrom_cons_eq (A : Set α) (j : ℕ) (sub : List ℕ) :
    interFrom P A (j :: sub) = P.X j ∩ interFrom P A sub := by
  apply Set.ext
  intro z
  rw [Set.mem_inter_iff, mem_interFrom, mem_interFrom, List.forall_mem_cons]
  tauto

/-- **The workhorse lemma.** For any subsystem `D' ◁ D`, `Fin(js) ⊆ D'.mem` iff every single
generator `P.X i` (`i ∈ js`) already lies in `D'.mem`. Proved by induction on `js`: the `cons` step
uses `interFrom_mem_of_witness` (`Theorem75.lean`) to show that the "tail" sub-meet of a consistent
`j :: sub`-selection is itself consistent (using the *full* meet as witness), then combines via
`D'.inter_closed`. -/
theorem finGen_le_iff_forall_mem {D' : NeighborhoodSystem α} (hD' : D' ◁ D) (js : List ℕ) :
    finGen P js ⊆ D'.mem ↔ ∀ i ∈ js, D'.mem (P.X i) := by
  induction js with
  | nil =>
    refine ⟨fun _ i hi => absurd hi List.not_mem_nil, fun _ => ?_⟩
    rintro Y ⟨sub, hsub, _, hYeq⟩
    rw [List.eq_nil_of_sublist_nil hsub] at hYeq
    rw [hYeq, show interFrom P D.master ([] : List ℕ) = D.master from rfl, ← hD'.master_eq]
    exact D'.master_mem
  | cons j js' ih =>
    rw [List.forall_mem_cons]
    constructor
    · intro hsub
      refine ⟨hsub (principal_mem_finGen P List.mem_cons_self), ?_⟩
      exact ih.mp ((finGen_mono P (List.sublist_cons_self j js')).trans hsub)
    · intro hall
      have hj := hall.1
      have hFinjs' : finGen P js' ⊆ D'.mem := ih.mpr hall.2
      rintro Y ⟨sub, hsub, hDY, hYeq⟩
      cases hsub with
      | cons _ hsub' => exact hFinjs' ⟨sub, hsub', hDY, hYeq⟩
      | cons_cons _ hsub' =>
        rename_i sub2
        rw [interFrom_cons_eq P D.master j sub2] at hYeq
        set Y2 := interFrom P D.master sub2 with hY2def
        have hY_sub_Y2 : Y ⊆ Y2 := hYeq ▸ Set.inter_subset_right
        have hDY2 : D.mem Y2 := interFrom_mem_of_witness P hDY hY_sub_Y2 D.master_mem
        have hY2mem : D'.mem Y2 := hFinjs' ⟨sub2, hsub', hDY2, rfl⟩
        have hXYmem : D.mem (P.X j ∩ Y2) := hYeq ▸ hDY
        exact hYeq ▸ hD'.inter_closed hj hY2mem hXYmem

/-- **The concatenation identity, general form.** For any subsystem `D' ◁ D`,
`Fin(js₁ ++ js₂) ⊆ D'.mem ↔ Fin(js₁) ⊆ D'.mem ∧ Fin(js₂) ⊆ D'.mem` — an immediate corollary of the
workhorse lemma via `List.forall_mem_append`. -/
theorem finGen_append_le_iff {D' : NeighborhoodSystem α} (hD' : D' ◁ D) (js1 js2 : List ℕ) :
    finGen P (js1 ++ js2) ⊆ D'.mem ↔ finGen P js1 ⊆ D'.mem ∧ finGen P js2 ⊆ D'.mem := by
  rw [finGen_le_iff_forall_mem P hD', finGen_le_iff_forall_mem P hD',
    finGen_le_iff_forall_mem P hD', List.forall_mem_append]

end FinGen

/-! ## Subgoal 2 — the reconstructed system `SubD` -/

section SubD

variable (P : ComputablePresentation D)

/-- **`nbhd(js)`**: the (anti-monotone) principal up-set of finite generators `js'` whose finitely
generated subsystem extends `Fin(js)` — the neighbourhood of `SubD` generated by `js`. -/
def nbhdGen (js : List ℕ) : Set (List ℕ) := {js' | finGen P js ⊆ finGen P js'}

@[simp] theorem mem_nbhdGen {js js' : List ℕ} :
    js' ∈ nbhdGen P js ↔ finGen P js ⊆ finGen P js' := Iff.rfl

theorem self_mem_nbhdGen (js : List ℕ) : js ∈ nbhdGen P js := (mem_nbhdGen P).mpr subset_rfl

/-- **Anti-monotonicity.** A bigger generator (`Fin`-wise) has a smaller up-set. -/
theorem nbhdGen_antitone {js js' : List ℕ} (h : finGen P js ⊆ finGen P js') :
    nbhdGen P js' ⊆ nbhdGen P js := fun _ hk => h.trans hk

/-- **Injectivity of `nbhd` on `Fin`.** `nbhd(a) = nbhd(b) → Fin(a) = Fin(b)`: evaluate the set
equality at `a` and at `b` (both reflexively self-membership) and combine by antisymmetry. -/
theorem finGen_eq_of_nbhdGen_eq {a b : List ℕ} (h : nbhdGen P a = nbhdGen P b) :
    finGen P a = finGen P b :=
  Set.Subset.antisymm ((Set.ext_iff.mp h b).mpr (self_mem_nbhdGen P b))
    ((Set.ext_iff.mp h a).mp (self_mem_nbhdGen P a))

/-- **`nbhd` equality is exactly `Fin` equality.** -/
theorem nbhdGen_eq_iff {a b : List ℕ} : nbhdGen P a = nbhdGen P b ↔ finGen P a = finGen P b := by
  refine ⟨finGen_eq_of_nbhdGen_eq P, fun h => ?_⟩
  unfold nbhdGen
  rw [h]

/-- **The concatenation identity for `nbhd`.** `nbhd(js₁) ∩ nbhd(js₂) = nbhd(js₁ ++ js₂)` —
`finGen_append_le_iff` instantiated at `D' := finGenSys(js')` for each candidate `js'`. -/
theorem nbhdGen_inter (js1 js2 : List ℕ) :
    nbhdGen P js1 ∩ nbhdGen P js2 = nbhdGen P (js1 ++ js2) := by
  apply Set.ext
  intro js'
  simp only [mem_nbhdGen, Set.mem_inter_iff]
  exact (finGen_append_le_iff P (finGenSys_subsystem P js') js1 js2).symm

/-- **`SubD`: the reconstructed neighbourhood system.** Tokens are finite index lists (`List ℕ`,
representing finitely generated subsystems of `D`); neighbourhoods are the principal up-sets
`nbhd(js)`. -/
def SubD (P : ComputablePresentation D) : NeighborhoodSystem (List ℕ) where
  mem N := ∃ js, N = nbhdGen P js
  master := nbhdGen P []
  master_mem := ⟨[], rfl⟩
  inter_mem := by
    rintro N1 N2 N3 ⟨js1, rfl⟩ ⟨js2, rfl⟩ ⟨js3, rfl⟩ _
    exact ⟨js1 ++ js2, nbhdGen_inter P js1 js2⟩
  sub_master := by
    rintro N ⟨js, rfl⟩
    exact nbhdGen_antitone P (finGen_mono P (List.nil_sublist js))

@[simp] theorem mem_SubD {N : Set (List ℕ)} : (SubD P).mem N ↔ ∃ js, N = nbhdGen P js := Iff.rfl

@[simp] theorem SubD_master : (SubD P).master = nbhdGen P [] := rfl

end SubD

/-! ## Subgoal 3 — the order isomorphism `SubD.Element ≃o {D' ∣ D' ◁ D}` -/

section OrderIso

variable (P : ComputablePresentation D)

/-- **`interFrom` splits over list concatenation.** A pure membership-characterization fact
(`mem_interFrom` + `List.forall_mem_append`), independent of consistency. -/
theorem interFrom_append_eq (A : Set α) (l1 l2 : List ℕ) :
    interFrom P A (l1 ++ l2) = interFrom P A l1 ∩ interFrom P A l2 := by
  apply Set.ext
  intro z
  rw [Set.mem_inter_iff, mem_interFrom, mem_interFrom, mem_interFrom, List.forall_mem_append]
  tauto

/-- **Forward direction: a subsystem induces a filter of `SubD`.** Given `D' ◁ D`, the filter
`ofSubsystem P D' hD'` consists of the neighbourhoods `nbhd(js)` such that `D'` already contains
every singleton generator `P.X i` for `i ∈ js`. -/
def ofSubsystem (D' : NeighborhoodSystem α) (hD' : D' ◁ D) : (SubD P).Element where
  mem N := ∃ js, N = nbhdGen P js ∧ ∀ i ∈ js, D'.mem (P.X i)
  sub := fun ⟨js, hN, _⟩ => ⟨js, hN⟩
  master_mem := ⟨[], rfl, fun i hi => absurd hi List.not_mem_nil⟩
  inter_mem := by
    rintro N1 N2 ⟨js1, rfl, h1⟩ ⟨js2, rfl, h2⟩
    exact ⟨js1 ++ js2, nbhdGen_inter P js1 js2, List.forall_mem_append.mpr ⟨h1, h2⟩⟩
  up_mem := by
    rintro N1 N2 ⟨js1, rfl, h1⟩ ⟨js2, rfl⟩ hsub
    have hle : finGen P js2 ⊆ finGen P js1 := hsub (self_mem_nbhdGen P js1)
    exact ⟨js2, rfl, (finGen_le_iff_forall_mem P hD' js2).mp
      (hle.trans ((finGen_le_iff_forall_mem P hD' js1).mpr h1))⟩

/-- **Backward direction: a filter of `SubD` induces a subsystem.** The neighbourhoods are the
`Fin(js)`-members for lists `js` confirmed by the filter `x`. -/
def toSubsystemSys (x : (SubD P).Element) : NeighborhoodSystem α where
  mem Y := ∃ js, x.mem (nbhdGen P js) ∧ Y ∈ finGen P js
  master := D.master
  master_mem := ⟨[], x.master_mem, master_mem_finGen P []⟩
  inter_mem := by
    rintro X Y Z ⟨js1, hx1, hX⟩ ⟨js2, hx2, hY⟩ ⟨js3, _, hZ⟩ hZsub
    have hDX := finGen_sub_mem P hX
    have hDY := finGen_sub_mem P hY
    have hDZ := finGen_sub_mem P hZ
    obtain ⟨sub1, hsub1, _, hXeq⟩ := hX
    obtain ⟨sub2, hsub2, _, hYeq⟩ := hY
    refine ⟨js1 ++ js2, nbhdGen_inter P js1 js2 ▸ x.inter_mem hx1 hx2,
      sub1 ++ sub2, hsub1.append hsub2, D.inter_mem hDX hDY hDZ hZsub, ?_⟩
    rw [interFrom_append_eq, hXeq, hYeq]
  sub_master := fun ⟨_, _, hY⟩ => finGen_sub_master P hY

/-- **`toSubsystemSys x` is a genuine subsystem of `D`.** Uses the same `interFrom_append_eq`
witness-combination argument as `inter_mem`, without needing the extra `Z`-witness. -/
theorem toSubsystemSys_subsystem (x : (SubD P).Element) : toSubsystemSys P x ◁ D where
  master_eq := rfl
  sub := fun ⟨_, _, hY⟩ => finGen_sub_mem P hY
  inter_closed := by
    rintro X Y ⟨js1, hx1, hX⟩ ⟨js2, hx2, hY⟩ hXY
    obtain ⟨sub1, hsub1, _, hXeq⟩ := hX
    obtain ⟨sub2, hsub2, _, hYeq⟩ := hY
    refine ⟨js1 ++ js2, nbhdGen_inter P js1 js2 ▸ x.inter_mem hx1 hx2,
      sub1 ++ sub2, hsub1.append hsub2, hXY, ?_⟩
    rw [interFrom_append_eq, hXeq, hYeq]

/-- **The backward map, packaged as a subsystem.** -/
def toSubsystem (x : (SubD P).Element) : {D' : NeighborhoodSystem α // D' ◁ D} :=
  ⟨toSubsystemSys P x, toSubsystemSys_subsystem P x⟩

/-! ### Round trip 1: `toSubsystem ∘ ofSubsystem = id` -/

/-- **Round trip, membership form.** `toSubsystemSys (ofSubsystem D')` has exactly the same
neighbourhoods as `D'` itself. `→`: unwind the double existential via `nbhdGen_eq_iff` and the
workhorse lemma. `←`: `P.surj` finds an index `n` with `P.X n = Y`; the singleton list `[n]`
witnesses membership on both sides. -/
theorem toSubsystem_ofSubsystem_mem (D' : NeighborhoodSystem α) (hD' : D' ◁ D) (Y : Set α) :
    (toSubsystemSys P (ofSubsystem P D' hD')).mem Y ↔ D'.mem Y := by
  constructor
  · rintro ⟨js, ⟨js', hjseq, hall⟩, hY⟩
    have hfin : finGen P js = finGen P js' := (nbhdGen_eq_iff P).mp hjseq
    exact (finGen_le_iff_forall_mem P hD' js').mpr hall (hfin ▸ hY)
  · intro hY
    obtain ⟨n, hn⟩ := P.surj (hD'.sub hY)
    refine ⟨[n], ⟨[n], rfl, fun i hi => ?_⟩, hn ▸ principal_mem_finGen P (List.mem_singleton.mpr rfl)⟩
    rw [List.mem_singleton] at hi
    subst hi
    rw [hn]
    exact hY

/-- **A reusable membership characterization**, generalizing the forward half of
`toSubsystem_ofSubsystem_mem`: for *any* `D' ◁ D`, `ofSubsystem P D' hD'` confirms `nbhd(js)`
exactly when `D'` confirms every generator in `js`. -/
theorem mem_ofSubsystem_nbhdGen {D' : NeighborhoodSystem α} (hD' : D' ◁ D) (js : List ℕ) :
    (ofSubsystem P D' hD').mem (nbhdGen P js) ↔ ∀ i ∈ js, D'.mem (P.X i) := by
  constructor
  · rintro ⟨js', hjseq, hall⟩
    have hfin : finGen P js = finGen P js' := (nbhdGen_eq_iff P).mp hjseq
    refine (finGen_le_iff_forall_mem P hD' js).mp ?_
    rw [hfin]
    exact (finGen_le_iff_forall_mem P hD' js').mpr hall
  · exact fun hall => ⟨js, rfl, hall⟩

/-- **Round trip 1.** `toSubsystem P (ofSubsystem P D' hD') = ⟨D', hD'⟩`. -/
theorem toSubsystem_ofSubsystem (D' : NeighborhoodSystem α) (hD' : D' ◁ D) :
    toSubsystem P (ofSubsystem P D' hD') = ⟨D', hD'⟩ :=
  Subtype.ext (NeighborhoodSystem.ext (toSubsystem_ofSubsystem_mem P D' hD') hD'.master_eq.symm)

/-! ### Round trip 2: `ofSubsystem ∘ toSubsystem = id` -/

/-- **The finite-fold lemma.** If every generator `P.X i` (`i ∈ js`) is individually confirmed by
`x` via some witness list, the witnesses can be concatenated (fold over the finite list `js`,
combining via `x.inter_mem`) into a *single* list `js₀` confirmed by `x` with `Fin(js) ⊆
Fin(js₀)`. -/
theorem exists_common_witness (x : (SubD P).Element) {js : List ℕ}
    (h : ∀ i ∈ js, ∃ js', x.mem (nbhdGen P js') ∧ P.X i ∈ finGen P js') :
    ∃ js0, x.mem (nbhdGen P js0) ∧ finGen P js ⊆ finGen P js0 := by
  induction js with
  | nil => exact ⟨[], SubD_master P ▸ x.master_mem, subset_rfl⟩
  | cons j js' ih =>
    obtain ⟨jsj, hxj, hjmem⟩ := h j List.mem_cons_self
    obtain ⟨js0', hx0', hsub0'⟩ := ih (fun i hi => h i (List.mem_cons_of_mem j hi))
    refine ⟨jsj ++ js0', nbhdGen_inter P jsj js0' ▸ x.inter_mem hxj hx0',
      (finGen_le_iff_forall_mem P (finGenSys_subsystem P (jsj ++ js0')) (j :: js')).mpr
        (List.forall_mem_cons.mpr ⟨?_, ?_⟩)⟩
    · exact finGen_mono P (List.sublist_append_left jsj js0') hjmem
    · exact fun i hi =>
        finGen_mono P (List.sublist_append_right jsj js0') (hsub0' (principal_mem_finGen P hi))

/-- **Round trip 2.** `ofSubsystem P (toSubsystem P x).1 (toSubsystem P x).2 = x`. -/
theorem ofSubsystem_toSubsystem (x : (SubD P).Element) :
    ofSubsystem P (toSubsystemSys P x) (toSubsystemSys_subsystem P x) = x := by
  apply Element.ext
  intro N
  constructor
  · rintro ⟨js, rfl, hall⟩
    obtain ⟨js0, hx0, hsub0⟩ := exists_common_witness P x hall
    exact x.up_mem hx0 ⟨js, rfl⟩ (nbhdGen_antitone P hsub0)
  · intro hx
    obtain ⟨js, rfl⟩ := x.sub hx
    exact ⟨js, rfl, fun i hi => ⟨js, hx, principal_mem_finGen P hi⟩⟩

/-- **Membership transfer, filter form.** Combines round trip 2 with `mem_ofSubsystem_nbhdGen`:
a filter `x` confirms `nbhd(js)` exactly when the reconstructed subsystem `toSubsystemSys P x`
confirms every generator in `js`. The key bridge for `map_rel_iff'` below. -/
theorem mem_nbhdGen_iff (x : (SubD P).Element) (js : List ℕ) :
    x.mem (nbhdGen P js) ↔ ∀ i ∈ js, (toSubsystemSys P x).mem (P.X i) := by
  conv_lhs => rw [← ofSubsystem_toSubsystem P x]
  exact mem_ofSubsystem_nbhdGen P (toSubsystemSys_subsystem P x) js

/-! ### The order isomorphism -/

/-- **Subgoal 3, capstone.** `SubD.Element ≃o {D' ∣ D' ◁ D}` — fully choice-free. Forward map
`toSubsystem`, inverse `ofSubsystem`; order preservation/reflection reduces via Scott's remark
(`Subsystem.subsystem_iff_subset_of_common`) to `mem_nbhdGen_iff` applied pointwise. -/
def subsystemIso : (SubD P).Element ≃o {D' : NeighborhoodSystem α // D' ◁ D} where
  toFun := toSubsystem P
  invFun x := ofSubsystem P x.1 x.2
  left_inv := ofSubsystem_toSubsystem P
  right_inv x := toSubsystem_ofSubsystem P x.1 x.2
  map_rel_iff' := by
    intro a b
    show toSubsystemSys P a ◁ toSubsystemSys P b ↔ (∀ N, a.mem N → b.mem N)
    rw [Subsystem.subsystem_iff_subset_of_common (toSubsystemSys_subsystem P a)
      (toSubsystemSys_subsystem P b)]
    constructor
    · intro hYsub N hN
      obtain ⟨js, rfl⟩ := a.sub hN
      exact (mem_nbhdGen_iff P b js).mpr
        (fun i hi => hYsub ((mem_nbhdGen_iff P a js).mp hN i hi))
    · rintro hab Y ⟨js, haj, hY⟩
      exact ⟨js, hab (nbhdGen P js) haj, hY⟩

end OrderIso

/-! ## Subgoal 4 — `ComputablePresentation (SubD P)` -/

section Computability

variable (P : ComputablePresentation D)

/-! ### 4a — the enumeration `X n := nbhd(decodeList n)` -/

/-- **The enumeration.** -/
def SubDX (n : ℕ) : Set (List ℕ) := nbhdGen P (decodeList n)

theorem SubDX_mem (n : ℕ) : (SubD P).mem (SubDX P n) := ⟨decodeList n, rfl⟩

theorem SubDX_surj {N : Set (List ℕ)} (hN : (SubD P).mem N) : ∃ n, SubDX P n = N := by
  obtain ⟨js, rfl⟩ := hN
  exact ⟨encodeList js, by unfold SubDX; rw [decodeList_encodeList]⟩

/-! ### 4b — `idxCharAt`: primitive-recursive extraction of `idxchain (bitSelect L b)`

Reuses `Theorem75.consStp`'s fold (the same one powering `consCharAt`) but projects the *index*
component (`.unpair.2.unpair.1`) instead of the consistency flag (`.unpair.2.unpair.2`). -/

/-- The index-component of `consUpd`'s fold state, after processing `el`, is independent of the
flag threaded alongside it: it only accumulates `P.inter` along the entries *selected* by the
bitmask `b`. Pure computation fact, no consistency needed. -/
theorem consUpd_foldl_idx (projFn fc : ℕ → ℕ) (el : List ℕ) (b a flag : ℕ) :
    (List.foldl (fun s x => consUpd P projFn fc s x) (Nat.pair b (Nat.pair a flag)) el).unpair.2.unpair.1
      = (List.map projFn (bitSelect el b)).foldl (fun acc j => P.inter acc j) a := by
  induction el generalizing b a flag with
  | nil => rw [bitSelect_nil, List.foldl_nil, List.map_nil, List.foldl_nil, unpair_pair_snd,
      unpair_pair_fst]
  | cons e el ih =>
    rw [List.foldl_cons, consUpd_eval, bitSelect_cons]
    by_cases hb : b % 2 = 1
    · rw [if_pos hb, List.map_cons, List.foldl_cons, hb, selectFn_one]
      exact ih (b / 2) (P.inter a (projFn e)) _
    · rw [if_neg hb, show b % 2 = 0 by omega, selectFn_zero]
      exact ih (b / 2) a flag

/-- `idxCharAt fc w` (`w = pair b c`): the same fold as `consCharAt`, projecting the running
intersection *index* instead of the consistency flag. -/
def idxCharAt (fc : ℕ → ℕ) (w : ℕ) : ℕ :=
  (foldCode (consStp P id fc) 0 (Nat.pair w.unpair.1 (Nat.pair P.masterIdx 1))
    w.unpair.2).unpair.2.unpair.1

theorem primrec_idxCharAt {fc : ℕ → ℕ} (hfcp : Nat.Primrec fc) :
    Nat.Primrec (idxCharAt P fc) := by
  have hfold := primrec_foldCode (primrec_consStp P primrec_id hfcp) (Nat.Primrec.const 0)
    (Nat.Primrec.left.pair ((Nat.Primrec.const P.masterIdx).pair (Nat.Primrec.const 1)))
    Nat.Primrec.right
  exact Nat.Primrec.left.comp (Nat.Primrec.right.comp hfold)

/-- **`idxCharAt` computes `idxchain (bitSelect (decodeList c) b)`.** Unfolds `foldCode` to a
`List.foldl` over `decodeList c`, identifies it with `consUpd`'s fold via `consStp`'s definition,
and reads off the index component via `consUpd_foldl_idx` (at `projFn := id`, `a := masterIdx`,
matching `idxchain`'s own definition as a fold from `masterIdx`). -/
theorem idxCharAt_eq_idxchain (fc : ℕ → ℕ) (w : ℕ) :
    idxCharAt P fc w = idxchain P (bitSelect (decodeList w.unpair.2) w.unpair.1) := by
  unfold idxCharAt idxchain
  rw [foldCode_eq']
  have hstep : (fun acc x => consStp P id fc (Nat.pair x (Nat.pair acc 0)))
      = (fun acc x => consUpd P id fc acc x) := by
    funext acc x
    show consStp P id fc (Nat.pair x (Nat.pair acc 0)) = _
    unfold consStp
    simp only [unpair_pair_fst, unpair_pair_snd]
  rw [hstep, consUpd_foldl_idx P id fc (decodeList w.unpair.2) w.unpair.1 P.masterIdx 1,
    List.map_id]

/-! ### 4c — singleton membership: `P.X m ∈ Fin(decodeList c)` is recursively decidable -/

/-- **A generator `P.X m` belongs to `Fin(decodeList c)` iff some bitmask-selected sublist of
`decodeList c` (`b < 2^c`, using `decodeList_length_le`) is `D`-consistent and equals `P.X m`** —
consistency via `consFold_decidable`, equality via `idxCharAt_eq_idxchain` + `idxchain_spec` +
`P.eq_computable`. The `D.mem (P.X m)` conjunct in `finGen`'s definition is always true
(`P.mem_X`), so it drops out of the decidable content. -/
theorem mem_finGen_computable :
    RecDecidable₂ (fun m c => P.X m ∈ finGen P (decodeList c)) := by
  obtain ⟨fc, hfcp, hfcs⟩ := P.cons_computable
  have hfc : ∀ s, fc s = 1 ↔ ∃ k, P.X k ⊆ P.X s.unpair.1 ∩ P.X s.unpair.2 := fun s => (hfcs s).symm
  have hconsFold := consFold_decidable P id fc hfc primrec_id hfcp
  have hg : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.1 w.unpair.2.unpair.2) :=
    Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)
  have hp1 : RecDecidable (fun w : ℕ =>
      D.mem (interFrom P D.master (bitSelect (decodeList w.unpair.2.unpair.2) w.unpair.1))) := by
    refine RecDecidable.of_iff (fun w => ?_) (hconsFold.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd, List.map_id]
  have hidx : Nat.Primrec (fun w : ℕ => idxCharAt P fc (Nat.pair w.unpair.1 w.unpair.2.unpair.2)) :=
    (primrec_idxCharAt P hfcp).comp hg
  have hh : Nat.Primrec (fun w : ℕ =>
      Nat.pair w.unpair.2.unpair.1 (idxCharAt P fc (Nat.pair w.unpair.1 w.unpair.2.unpair.2))) :=
    (Nat.Primrec.left.comp Nat.Primrec.right).pair hidx
  have hp2 : RecDecidable (fun w : ℕ =>
      P.X w.unpair.2.unpair.1 = P.X (idxCharAt P fc (Nat.pair w.unpair.1 w.unpair.2.unpair.2))) := by
    refine RecDecidable.of_iff (fun w => ?_) (P.eq_computable.comp hh)
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hp := hp1.and hp2
  have hbound : Nat.Primrec (fun n : ℕ => 2 ^ n.unpair.2) := primrec_two_pow Nat.Primrec.right
  have hbe := hp.bExists (bound := fun n : ℕ => 2 ^ n.unpair.2) hbound
  refine RecDecidable.of_iff (fun t => ?_) hbe
  simp only [unpair_pair_fst, unpair_pair_snd]
  constructor
  · rintro ⟨sub, hsub, -, hYeq⟩
    obtain ⟨b, hb, hbeq⟩ := exists_bitSelect_lt hsub
    have hb' : b < 2 ^ t.unpair.2 :=
      lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (decodeList_length_le t.unpair.2))
    have hDsub : D.mem (interFrom P D.master sub) := hYeq ▸ P.mem_X t.unpair.1
    refine ⟨b, hb', hbeq ▸ hDsub, ?_⟩
    rw [idxCharAt_eq_idxchain]
    simp only [unpair_pair_fst, unpair_pair_snd]
    rw [hbeq, idxchain_spec P hDsub, ← hYeq]
  · rintro ⟨b, -, hDb, hXeq⟩
    refine ⟨bitSelect (decodeList t.unpair.2) b, bitSelect_sublist _ _, P.mem_X t.unpair.1, ?_⟩
    rw [hXeq, idxCharAt_eq_idxchain]
    simp only [unpair_pair_fst, unpair_pair_snd]
    rw [idxchain_spec P hDb]

/-! ### 4d — subset decidability: `Fin(decodeList c1) ⊆ Fin(decodeList c2)` -/

/-- **`Fin(decodeList c1) ⊆ Fin(decodeList c2)` is recursively decidable** — rewrite via
`finGen_le_iff_forall_mem` (at `D' := finGenSys P (decodeList c2)`, a genuine subsystem of `D` by
`finGenSys_subsystem`) to `∀ i ∈ decodeList c1, P.X i ∈ finGen P (decodeList c2)`, which is exactly
`mem_finGen_computable.bForallList`. -/
theorem finGen_subset_computable :
    RecDecidable₂ (fun c1 c2 => finGen P (decodeList c1) ⊆ finGen P (decodeList c2)) := by
  have hiff : ∀ c1 c2, finGen P (decodeList c1) ⊆ finGen P (decodeList c2) ↔
      ∀ i ∈ decodeList c1, P.X i ∈ finGen P (decodeList c2) :=
    fun c1 c2 => finGen_le_iff_forall_mem P (finGenSys_subsystem P (decodeList c2)) (decodeList c1)
  refine RecDecidable.of_iff (fun t => ?_) (mem_finGen_computable P).bForallList
  exact hiff t.unpair.1 t.unpair.2

/-! ### 4e — `interEq_computable`: `SubDX n ∩ SubDX m = SubDX k` is decidable -/

/-- **`SubDX n ∩ SubDX m = SubDX k` is recursively decidable.** Chain of exact rewrites reduces
membership-equality of a *pairwise* intersection to a *single* subset-decidable statement at the
`appendListCode`-combined index: `nbhdGen(decodeList n) ∩ nbhdGen(decodeList m) = nbhdGen(decodeList
k)` `↔` (`nbhdGen_inter`) `nbhdGen(decodeList n ++ decodeList m) = nbhdGen(decodeList k)` `↔`
(`appendListCode_eq`) `nbhdGen(decodeList(appendListCode n m)) = nbhdGen(decodeList k)` `↔`
(`nbhdGen_eq_iff`) `finGen(decodeList(appendListCode n m)) = finGen(decodeList k)` `↔`
(`Set.Subset.antisymm_iff`) both inclusions, each an instance of `finGen_subset_computable`
reindexed along the primitive-recursive `appendListCode`. -/
theorem SubD_interEq_computable :
    RecDecidable₃ (fun n m k => SubDX P n ∩ SubDX P m = SubDX P k) := by
  have hiff : ∀ n m k, SubDX P n ∩ SubDX P m = SubDX P k ↔
      finGen P (decodeList (appendListCode n m)) ⊆ finGen P (decodeList k) ∧
        finGen P (decodeList k) ⊆ finGen P (decodeList (appendListCode n m)) := by
    intro n m k
    show nbhdGen P (decodeList n) ∩ nbhdGen P (decodeList m) = nbhdGen P (decodeList k) ↔ _
    rw [nbhdGen_inter, ← appendListCode_eq, nbhdGen_eq_iff, Set.Subset.antisymm_iff]
  have hg1 : Nat.Primrec (fun t : ℕ => appendListCode t.unpair.1 t.unpair.2.unpair.1) :=
    (primrec_appendListCode.comp
        (Nat.Primrec.left.pair (Nat.Primrec.left.comp Nat.Primrec.right))).of_eq
      (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
  have hreindex1 : Nat.Primrec (fun t : ℕ =>
      Nat.pair (appendListCode t.unpair.1 t.unpair.2.unpair.1) t.unpair.2.unpair.2) :=
    hg1.pair (Nat.Primrec.right.comp Nat.Primrec.right)
  have hreindex2 : Nat.Primrec (fun t : ℕ =>
      Nat.pair t.unpair.2.unpair.2 (appendListCode t.unpair.1 t.unpair.2.unpair.1)) :=
    (Nat.Primrec.right.comp Nat.Primrec.right).pair hg1
  have hforward : RecDecidable (fun t : ℕ =>
      finGen P (decodeList (appendListCode t.unpair.1 t.unpair.2.unpair.1)) ⊆
        finGen P (decodeList t.unpair.2.unpair.2)) := by
    refine RecDecidable.of_iff (fun t => ?_) ((finGen_subset_computable P).comp hreindex1)
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hbackward : RecDecidable (fun t : ℕ =>
      finGen P (decodeList t.unpair.2.unpair.2) ⊆
        finGen P (decodeList (appendListCode t.unpair.1 t.unpair.2.unpair.1))) := by
    refine RecDecidable.of_iff (fun t => ?_) ((finGen_subset_computable P).comp hreindex2)
    simp only [unpair_pair_fst, unpair_pair_snd]
  refine RecDecidable.of_iff (fun t => ?_) (hforward.and hbackward)
  exact hiff t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2

/-! ### 4f — `cons_computable`/`inter`/`inter_primrec`/`inter_spec` are free -/

/-- **`SubDX(appendListCode n m) = SubDX n ∩ SubDX m` exactly** (not just when consistent) —
`appendListCode_eq` turns list-code concatenation into `List` `++`, then `nbhdGen_inter`. -/
theorem SubDX_inter_eq (n m : ℕ) :
    SubDX P (appendListCode n m) = SubDX P n ∩ SubDX P m := by
  show nbhdGen P (decodeList (appendListCode n m))
      = nbhdGen P (decodeList n) ∩ nbhdGen P (decodeList m)
  rw [appendListCode_eq, nbhdGen_inter]

/-- **Consistency is always true** (`appendListCode n m` is always a witness), hence trivially
recursively decidable. -/
theorem SubD_cons_computable :
    RecDecidable₂ (fun n m => ∃ k, SubDX P k ⊆ SubDX P n ∩ SubDX P m) := by
  refine recDecidable_of_forall (fun t => ⟨appendListCode t.unpair.1 t.unpair.2, ?_⟩)
  rw [SubDX_inter_eq]

/-! ### 4g — `masterIdx`/`masterIdx_spec` -/

theorem SubDX_masterIdx_spec : SubDX P (encodeList ([] : List ℕ)) = (SubD P).master := by
  show nbhdGen P (decodeList (encodeList ([] : List ℕ))) = nbhdGen P []
  rw [decodeList_encodeList]

/-! ### Assembling `ComputablePresentation (SubD P)` -/

/-- **Subgoal 4, capstone.** `SubD P` admits a computable presentation, assembled from 4a–4g. -/
def SubDPresentation : ComputablePresentation (SubD P) where
  X := SubDX P
  mem_X := SubDX_mem P
  surj := SubDX_surj P
  interEq_computable := SubD_interEq_computable P
  cons_computable := SubD_cons_computable P
  inter := appendListCode
  inter_primrec := primrec_appendListCode
  inter_spec := fun {n m} _ => SubDX_inter_eq P n m
  masterIdx := encodeList []
  masterIdx_spec := SubDX_masterIdx_spec P

end Computability

/-! ## Subgoal 5 — main theorem: `D.IsEffectivelyGiven → {D' ∣ D' ◁ D}` is (isomorphic to) an
effectively given domain -/

/-- **Exercise 8.15, first half.** If `D` is effectively given, there is an effectively given
neighbourhood system (`SubD P`, on tokens `List ℕ`) whose elements are order-isomorphic to
`{D' ∣ D' ◁ D}` — a *direct*, choice-free construction (Subgoals 1–4), unlike the classical route
through `Exercise222.reprIso` (`Proposition611.subsystemReprIso`). -/
theorem subsystem_isEffectivelyGiven_of_isEffectivelyGiven (hD : D.IsEffectivelyGiven) :
    ∃ V : NeighborhoodSystem (List ℕ), V.IsEffectivelyGiven ∧
      Nonempty (V.Element ≃o {D' : NeighborhoodSystem α // D' ◁ D}) := by
  obtain ⟨P⟩ := hD
  exact ⟨SubD P, ⟨SubDPresentation P⟩, ⟨subsystemIso P⟩⟩

/-! ## Subgoal 6 — second half: computable elements of `SubD P` ↔ effectively presented `D'x`
(relative to `P`'s own enumeration)

See `arxiv.md`'s Exercise 8.15 entry for the plan (6a–6g) and the disjoint-interval example showing
why an *arbitrary* abstract presentation of `D'x` cannot be compared to `P` in general. Everything
below is stated for a general `D`/`P` (the argument never needed `D = 𝒰` specifically); the exercise
instantiates it at `D := U`, `P := UComputablePresentation`. -/

section ComputableElements

variable (P : ComputablePresentation D)

/-! ### 6a — reduce `IsComputableElement` to the index set `{i ∣ D'x.mem (P.X i)}` -/

/-- The singleton-list code `i ↦ encodeList [i]` is primitive recursive. -/
private theorem primrec_encodeList_singleton : Nat.Primrec (fun i => encodeList [i]) := by
  have : (fun i => encodeList [i]) = fun i => Nat.pair i 0 + 1 := by
    funext i; show Nat.pair i (encodeList ([] : List ℕ)) + 1 = Nat.pair i 0 + 1
    rw [encodeList]
  rw [this]
  exact Nat.Primrec.succ.comp (Nat.Primrec.pair primrec_id (Nat.Primrec.const 0))

/-- **Subgoal 6a.** `x` is a computable element of `SubD P` iff its "index set relative to `P`" —
the set of `P`-indices `i` with `(toSubsystemSys P x).mem (P.X i)` — is recursively enumerable.
`→`: reindex along `decodeList` (`mem_nbhdGen_iff`) then along the singleton-list code. `←`:
`REPred.forall_mem_decodeList` directly. -/
theorem subsystemU_computable_iff_index_set_re (x : (SubD P).Element) :
    IsComputableElement (SubDPresentation P) x ↔
      REPred (fun i => (toSubsystemSys P x).mem (P.X i)) := by
  have hiff : ∀ n, x.mem (SubDX P n) ↔ ∀ i ∈ decodeList n, (toSubsystemSys P x).mem (P.X i) := by
    intro n; unfold SubDX; exact mem_nbhdGen_iff P x (decodeList n)
  constructor
  · intro hx
    have hx' : REPred (fun n => ∀ i ∈ decodeList n, (toSubsystemSys P x).mem (P.X i)) :=
      REPred.of_iff (fun n => (hiff n).symm) hx
    refine REPred.of_iff (fun i => ?_) (hx'.comp primrec_encodeList_singleton)
    rw [decodeList_encodeList]
    simp only [List.mem_singleton]
    constructor
    · intro h j hj; rw [hj]; exact h
    · intro h; exact h i rfl
  · intro hx
    exact REPred.of_iff hiff hx.forall_mem_decodeList

/-! ### 6b–6d — the main biconditional, via a `P`-relative primitive recursive enumeration -/

/-- **Subgoals 6b–6d, combined.** `x` is a computable element of `SubD P` iff the index set of
`D'x := toSubsystemSys P x` (relative to `P`'s own enumeration) is the range of a primitive
recursive function — Scott's "index set r.e." reduced (Exercise 7.14) to an explicit enumerator.
`→` (6b): `Exercise714.repred_exists_primrec_range`, seeded by the witness `P.masterIdx`
(`D'x.mem (P.X P.masterIdx) = D'x.mem D.master`, always true). `←` (6c):
`Exercise714.repred_range_primrec`. -/
theorem subsystemU_element_computable_iff (x : (SubD P).Element) :
    IsComputableElement (SubDPresentation P) x ↔
      ∃ r : ℕ → ℕ, Nat.Primrec r ∧
        ∀ i, (toSubsystemSys P x).mem (P.X i) ↔ ∃ n, r n = i := by
  rw [subsystemU_computable_iff_index_set_re P x]
  constructor
  · intro hre
    have ha : (toSubsystemSys P x).mem (P.X P.masterIdx) := by
      rw [P.masterIdx_spec]; exact (toSubsystemSys P x).master_mem
    exact Exercise714.repred_exists_primrec_range hre ha
  · rintro ⟨r, hr, hspec⟩
    exact REPred.of_iff hspec (Exercise714.repred_range_primrec hr)

end ComputableElements

/-! ## Subgoal 6e/6f — upgrading to a genuine `ComputablePresentation`, specialized to `D = 𝒰`

Generic `D`/`P` is not enough here: the branch needed to keep `Q'x.X` safe requires an *explicit*
(not merely `RecDecidable`-existentially-known) dichotomy for `P.inter`, which `𝒰`'s canonicalizing
`Uinter` genuinely has (`UX_Uinter_dichotomy`) but an abstract `P` does not. See `HANDOFF.md`'s
2026-07-06 checkpoint for the investigation that led here. -/

section UniversalSubsystem

/-- **`Uinter`'s unconditional dichotomy.** Unlike a generic `ComputablePresentation.inter` (whose
behaviour off the consistent domain is unspecified "junk"), `𝒰`'s canonicalizing `Uinter` always
produces *either* the true intersection *or* falls back to `U.master` — `canonList`'s documented
"fall back to `(0,1)` if nothing survives" behaviour, holding **unconditionally** (no consistency
hypothesis needed). This is the key fact an abstract `ComputablePresentation` cannot supply. -/
theorem UX_Uinter_dichotomy (n m : ℕ) :
    UX (Uinter n m) = U.master ∨ UX (Uinter n m) = UX n ∩ UX m := by
  have hUXeq : UX (Uinter n m) = presentedIntervals (canonList (decodeQPairList (Uinter n m))) :=
    UX_eq (Uinter n m)
  have hL : presentedIntervals (decodeQPairList (Uinter n m)) = UX n ∩ UX m := by
    show presentedIntervals (decodeQPairList (combineCode (canonCode n) (canonCode m)))
        = UX n ∩ UX m
    rw [presentedIntervals_decodeQPairList_combineCode]
    rfl
  rcases hfilt : ((decodeQPairList (Uinter n m)).map qpClip).filter
      (fun p => decide (p.1 < p.2)) with _ | ⟨a, l⟩
  · left
    rw [hUXeq, canonList_eq_of_filter_eq_nil hfilt, presentedIntervals_singleton_zero_one]
  · right
    rw [hUXeq, canonList_eq_of_filter_eq_cons hfilt, ← hfilt, presentedIntervals_filter_qpPos,
      presentedIntervals_map_qpClip, hL]
    obtain ⟨-, -, hsubn⟩ := U_mem_UX n
    exact Set.inter_eq_left.mpr (Set.inter_subset_left.trans hsubn)

/-- **The safe-fold invariant.** Folding `Uinter` from a starting point already in `D'x.mem` along a
list all of whose `UX`-images are also in `D'x.mem` stays in `D'x.mem`: `x`'s own *unconditional*
filter closure (`Element.inter_mem`, via `nbhdGen_inter`) combines the two generators' witnessing
index-lists when `Uinter`'s fold genuinely computes an intersection (dichotomy's right disjunct,
using `interFrom_append_eq`), and `D'x.master_mem` handles the fallback (left disjunct). -/
theorem toSubsystemSys_mem_foldl_Uinter (x : (SubD UComputablePresentation).Element) (acc : ℕ)
    (L : List ℕ) (hacc : (toSubsystemSys UComputablePresentation x).mem (UX acc))
    (hL : ∀ i ∈ L, (toSubsystemSys UComputablePresentation x).mem (UX i)) :
    (toSubsystemSys UComputablePresentation x).mem
      (UX (L.foldl (fun a j => Uinter a j) acc)) := by
  induction L generalizing acc with
  | nil => simpa using hacc
  | cons j L' ih =>
    rw [List.forall_mem_cons] at hL
    have hacc' : (toSubsystemSys UComputablePresentation x).mem (UX (Uinter acc j)) := by
      rcases UX_Uinter_dichotomy acc j with hcase | hcase
      · rw [hcase]; exact (toSubsystemSys UComputablePresentation x).master_mem
      · rw [hcase]
        obtain ⟨jsA, hxA, subA, hsubA, hDA, hAeq⟩ := hacc
        obtain ⟨jsJ, hxJ, subJ, hsubJ, hDJ, hJeq⟩ := hL.1
        have hUmem : U.mem (UX acc ∩ UX j) := hcase ▸ U_mem_UX (Uinter acc j)
        refine ⟨jsA ++ jsJ,
          nbhdGen_inter UComputablePresentation jsA jsJ ▸ x.inter_mem hxA hxJ,
          subA ++ subJ, hsubA.append hsubJ, hUmem, ?_⟩
        rw [hAeq, hJeq, interFrom_append_eq UComputablePresentation U.master subA subJ]
    exact ih (Uinter acc j) hacc' hL.2

/-! ### `Q'X` — an explicit enumeration of `D'x`'s neighbourhoods

Given `r` (from `subsystemU_element_computable_iff`, i.e. `x` computable relative to `UP`),
`Q'X r n` folds `Uinter` over the `r`-image of the list coded by `n`, starting from `U`'s master —
reusing the *existing, generic* `Theorem75.idxchain`/`foldCode` machinery (`Recursive.lean`) rather
than reproving fold-primitive-recursiveness from scratch. -/

/-- `foldCode`'s per-step function for `Q'X`: combine the running accumulator with `r` applied to
the next list entry. Packaged in `foldCode`'s `pair x (pair acc params)` calling convention
(`params` unused). -/
def QstepFn (r : ℕ → ℕ) (t : ℕ) : ℕ := Uinter t.unpair.2.unpair.1 (r t.unpair.1)

theorem primrec_QstepFn {r : ℕ → ℕ} (hr : Nat.Primrec r) : Nat.Primrec (QstepFn r) := by
  unfold QstepFn
  have h1 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.right
  have h2 : Nat.Primrec (fun t : ℕ => r t.unpair.1) := hr.comp Nat.Primrec.left
  exact (Uinter_primrec.comp (h1.pair h2)).of_eq fun t => by
    simp only [unpair_pair_fst, unpair_pair_snd]

/-- The raw `U`-index computed by folding `Uinter ∘ r` over the list coded by `n`, starting from
`U`'s master index. -/
def Q'Xcode (r : ℕ → ℕ) (n : ℕ) : ℕ :=
  foldCode (QstepFn r) 0 UComputablePresentation.masterIdx n

theorem primrec_Q'Xcode {r : ℕ → ℕ} (hr : Nat.Primrec r) : Nat.Primrec (Q'Xcode r) :=
  primrec_foldCode (primrec_QstepFn hr) (Nat.Primrec.const 0)
    (Nat.Primrec.const UComputablePresentation.masterIdx) Nat.Primrec.id

/-- **`Q'X r`: the candidate enumeration of `D'x`'s neighbourhoods.** -/
def Q'X (r : ℕ → ℕ) (n : ℕ) : Set ℚ := UX (Q'Xcode r n)

/-- `Q'X r n` is `UX` at the `idxchain`-index of the `r`-image of `n`'s list — i.e. `Q'X r` really is
`Theorem75`'s generic `idxchain` fold, just specialized through `r`. -/
theorem Q'X_eq (r : ℕ → ℕ) (n : ℕ) :
    Q'X r n = UX (idxchain UComputablePresentation (List.map r (decodeList n))) := by
  have hstep : (fun (acc x : ℕ) => QstepFn r (Nat.pair x (Nat.pair acc 0)))
      = fun acc x => Uinter acc (r x) := by
    funext acc x; unfold QstepFn; simp only [unpair_pair_fst, unpair_pair_snd]
  unfold Q'X Q'Xcode idxchain
  rw [foldCode_eq', hstep, List.foldl_map]
  rfl

/-- **`mem_X` for `Q'X r`.** Every `Q'X r n` is a `D'x`-neighbourhood — no consistency hypothesis on
`n` needed, since (a) every entry `r j` of the folded list is *unconditionally* `D'x.mem (UX (r j))`
by `hspec` (taking the trivial witness `j`), and (b) `toSubsystemSys_mem_foldl_Uinter` safely folds
any such list, landing on `D'x.master_mem` if `Uinter`'s dichotomy ever falls back. -/
theorem Q'x_mem_X (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)
    (hspec : ∀ i, (toSubsystemSys UComputablePresentation x).mem (UX i) ↔ ∃ n, r n = i) (n : ℕ) :
    (toSubsystemSys UComputablePresentation x).mem (Q'X r n) := by
  rw [Q'X_eq]
  show (toSubsystemSys UComputablePresentation x).mem
      (UX ((List.map r (decodeList n)).foldl (fun a j => Uinter a j)
        UComputablePresentation.masterIdx))
  apply toSubsystemSys_mem_foldl_Uinter
  · show (toSubsystemSys UComputablePresentation x).mem (UX UmasterIdx)
    rw [UX_UmasterIdx]
    exact (toSubsystemSys UComputablePresentation x).master_mem
  · intro i hi
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hi
    exact (hspec (r j)).mpr ⟨j, rfl⟩

/-- **List-level choice, choice-free.** If every entry of `l` has an `r`-preimage, `l` itself is the
`r`-image of some list — built by ordinary list induction (`Exists.elim` inside a `Prop`-valued goal
at each step), not `Classical.choice`. -/
theorem exists_preimage_of_forall_mem {r : ℕ → ℕ} {l : List ℕ} (h : ∀ i ∈ l, ∃ n, r n = i) :
    ∃ l0 : List ℕ, l0.map r = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons i l' ih =>
    obtain ⟨n0, hn0⟩ := h i List.mem_cons_self
    obtain ⟨l0', hl0'⟩ := ih (fun j hj => h j (List.mem_cons_of_mem i hj))
    exact ⟨n0 :: l0', by simp [hn0, hl0']⟩

/-- **`surj` for `Q'X r`.** Every `D'x`-neighbourhood `Y` is some `Q'X r n`: unwind `Y`'s `finGen`
witness `sub`, use `hspec` + `exists_preimage_of_forall_mem` to find a preimage list `sub0` with
`sub0.map r = sub`, and read off `Y` via the *generic* `Theorem75.idxchain_spec` (applicable because
`sub`'s own consistency — `U.mem (interFrom … sub)` — is exactly `hDY` rewritten along `hYeq`). -/
theorem Q'x_surj (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)
    (hspec : ∀ i, (toSubsystemSys UComputablePresentation x).mem (UX i) ↔ ∃ n, r n = i)
    {Y : Set ℚ} (hY : (toSubsystemSys UComputablePresentation x).mem Y) :
    ∃ n, Q'X r n = Y := by
  obtain ⟨js, hxjs, sub, hsub, hDY, hYeq⟩ := hY
  have hjsmem : ∀ i ∈ js, (toSubsystemSys UComputablePresentation x).mem (UX i) :=
    (mem_nbhdGen_iff UComputablePresentation x js).mp hxjs
  have hsubmem : ∀ i ∈ sub, (toSubsystemSys UComputablePresentation x).mem (UX i) :=
    fun i hi => hjsmem i (hsub.subset hi)
  obtain ⟨sub0, hsub0⟩ := exists_preimage_of_forall_mem (fun i hi => (hspec i).mp (hsubmem i hi))
  refine ⟨encodeList sub0, ?_⟩
  rw [Q'X_eq, decodeList_encodeList, hsub0, hYeq]
  exact idxchain_spec UComputablePresentation (hYeq ▸ hDY)

/-! ### The remaining gap: `inter`/`cons_computable` need a term-algebra encoding (resolved below)

`Q'X r` (above) is a fully choice-free, primitive-recursive **enumeration of `D'x`'s neighbourhoods,
onto** (`Q'x_mem_X`, `Q'x_surj`) — the enumeration half of a `ComputablePresentation D'x`. Completing
the *rest* of the structure (`inter`, `inter_spec`, `cons_computable`; `interEq_computable` alone is
fine, a pure reindexing of `U_interEq_computable` along the primitive-recursive `Q'Xcode r`) hits a
**newly-identified obstacle, sharper than the one logged previously**:

The natural candidate `Q'inter r n m := encodeList (decodeList n ++ decodeList m)` — extending `n`'s
list by `m`'s and re-folding — does *not* satisfy `inter_spec`. The reason is that `Uinter`'s
dichotomy fallback is **not "conservative"**: once a fold step falls back to `U.master` (discarding
the true partial intersection), *continuing* the fold from `U.master` can "recover" and compute a
smaller, unrelated value, rather than staying stuck at `U.master`. Concretely: `Q'X r (Q'inter r n
m)`'s value depends on the entries of `n`'s and `m`'s lists *combined sequentially from scratch*, while
`Q'X r n` and `Q'X r m` are each computed *independently* from `U`'s master. If (say) `Q'X r m`'s own
fold happened to fall back internally (its true intersection was empty) while the *globally* combined
fold does not, `Q'X r n ∩ Q'X r m` (inflated by the fallback) and `Q'X r (Q'inter r n m)` (computed
honestly) can be genuinely different sets — even though both individually satisfy `mem_X`. The
alternative fix — `Q'inter r n m := Uinter (Q'Xcode r n) (Q'Xcode r m)` (apply `Uinter` *once more* on
top of the already-computed indices, correct by the existing, unconditional `Uinter_spec`, no
compounding at all) — repairs `inter`/`inter_spec` cleanly, but then breaks `cons_computable`: its
witness `∃k, Q'X r k ⊆ Q'X r n ∩ Q'X r m` needs `k` to be *of the form `Q'Xcode r` applied to some `n,
m`-derived list-code*, and there is no way to name that code without already tracking, as part of
`Q'X`'s own index type, a closed-under-`Uinter`-combination term structure (i.e. re-indexing `Q'X` by
a small term language `{base list, combine n₁ n₂}` via course-of-values recursion, mirroring
`Recursive.lean`'s `tabCode` pattern for a *different* recursively-defined code). Building that term
algebra is genuinely comparable in size to Subgoal 4 itself (as flagged previously), and is **left as
documented future work** — this is a more precise diagnosis of the difficulty than the "extracting a
witness from a `Prop`" issue logged earlier (that issue is avoided entirely by `Q'X`/`Q'Xcode` being
directly-defined functions throughout; the *actual* remaining obstacle is this purely arithmetic
"safe composition of finitely many `Uinter` calls" question). See `HANDOFF.md`'s 2026-07-06 checkpoint.

**Resolution (below): a binary term algebra fixes `inter`/`cons_computable` cleanly.** The fix is to
stop indexing `D'x`'s neighbourhoods by *lists* folded left-to-right through `Uinter` (not
compositional under concatenation, as diagnosed above), and instead index them by a **binary term
algebra** — codes for `leaf j ↦ r j` and `node t1 t2 ↦ Uinter (val t1) (val t2)` — so that combining
two already-built codes is *literally* the `node` constructor, staying inside the index type by
construction (no search needed to name the combined index, unlike the list-code domain). -/

/-! ### The term algebra codes: `leaf j`, `node t1 t2`, `master`

Evaluating a code needs **course-of-values recursion** (a `node`'s two children are only known
`≤` the parent via `Nat.unpair`, not decreasing by a fixed amount), for which we reuse the
*already-built, generic* `fuelTable`/`fuelTable_eq_of_recursion`/`primrec_fuelTable` machinery from
`Recursive.lean` (built there for `decodeFuelOkChar`/`autStateCardFuelChar`) rather than
re-deriving course-of-values primitive recursiveness from scratch. -/

section TermAlgebra

/-- `leaf j`: the term-algebra code evaluating to `r j`. -/
def leafCode (j : ℕ) : ℕ := Nat.pair 0 j

/-- `node t1 t2`: the term-algebra code evaluating to `Uinter (val t1) (val t2)`. -/
def nodeCode (t1 t2 : ℕ) : ℕ := Nat.pair 1 (Nat.pair t1 t2)

/-- `master`: the term-algebra code evaluating to `𝒰`'s master index. -/
def masterCode : ℕ := Nat.pair 2 0

/-- If `c`'s tag (`c.unpair.1`) is nonzero, `c`'s payload (`c.unpair.2`) is *strictly* smaller than
`c` itself — the key well-foundedness fact driving `nodeCode`'s children being strictly smaller
than the parent (choice-free: only uses the custom `unpair_pair`/`le_pair_right`/
`Nat.pair_lt_pair_left`, all already audited elsewhere in this file). -/
theorem unpair_snd_lt_of_unpair_fst_pos {c : ℕ} (h : 0 < c.unpair.1) : c.unpair.2 < c := by
  have h1 : c.unpair.2 ≤ Nat.pair 0 c.unpair.2 := le_pair_right 0 c.unpair.2
  have h2 : Nat.pair 0 c.unpair.2 < Nat.pair c.unpair.1 c.unpair.2 := Nat.pair_lt_pair_left _ h
  rw [Nat.pair_unpair] at h2
  omega

/-- `nodeCode t1 t2`'s two children are each strictly smaller than the whole code. -/
theorem nodeCode_fst_lt (t1 t2 : ℕ) : t1 < nodeCode t1 t2 := by
  have hpos : 0 < (nodeCode t1 t2).unpair.1 := by
    unfold nodeCode; rw [unpair_pair_fst]; omega
  have hsnd : (nodeCode t1 t2).unpair.2 < nodeCode t1 t2 :=
    unpair_snd_lt_of_unpair_fst_pos hpos
  have ht1 : t1 ≤ (nodeCode t1 t2).unpair.2 := by
    unfold nodeCode; rw [unpair_pair_snd]; exact le_pair_left t1 t2
  omega

theorem nodeCode_snd_lt (t1 t2 : ℕ) : t2 < nodeCode t1 t2 := by
  have hpos : 0 < (nodeCode t1 t2).unpair.1 := by
    unfold nodeCode; rw [unpair_pair_fst]; omega
  have hsnd : (nodeCode t1 t2).unpair.2 < nodeCode t1 t2 :=
    unpair_snd_lt_of_unpair_fst_pos hpos
  have ht2 : t2 ≤ (nodeCode t1 t2).unpair.2 := by
    unfold nodeCode; rw [unpair_pair_snd]; exact le_pair_right t1 t2
  omega

end TermAlgebra

/-! ### `TreeVal r`: evaluating a term-algebra code, via course-of-values fuel recursion -/

section TreeVal

variable (r : ℕ → ℕ)

/-- One fuel-recursion step for evaluating a term-algebra code: tag `0` (`leaf j`) applies `r` to
the payload; tag `1` (`node t1 t2`) combines the two (previous-fuel-level) recursive values via
`Uinter`; any other tag (`master`, or junk) falls back to `𝒰`'s master index. Mirrors
`decodeFuelOkCharBody`'s tag-dispatch shape exactly. -/
def QBody (prev : ℕ → ℕ) (c : ℕ) : ℕ :=
  selectFn (isOne (1 - c.unpair.1)) (r c.unpair.2)
    (selectFn (isOne (2 - c.unpair.1))
      (Uinter (prev c.unpair.2.unpair.1) (prev c.unpair.2.unpair.2))
      UComputablePresentation.masterIdx)

/-- `QBody`'s value at `c` depends on `prev` only through its values at `c`'s two (`Nat.unpair`)
children — the locality fact needed to bridge two different `prev`s that merely *agree* there. -/
theorem QBody_local (f g : ℕ → ℕ) (c : ℕ)
    (h1 : f c.unpair.2.unpair.1 = g c.unpair.2.unpair.1)
    (h2 : f c.unpair.2.unpair.2 = g c.unpair.2.unpair.2) :
    QBody r f c = QBody r g c := by
  unfold QBody
  rw [h1, h2]

/-- `QBody`'s step with `prev` replaced by table lookup (`fuelTable`'s calling convention). -/
def QLookup (w : ℕ) : ℕ := QBody r (fun c' => nthCode w.unpair.1 c' 0) w.unpair.2

theorem primrec_QLookup (hr : Nat.Primrec r) : Nat.Primrec (QLookup r) := by
  have hleaf : Nat.Primrec (fun w : ℕ => r w.unpair.2.unpair.2) :=
    hr.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hleft : Nat.Primrec (fun w : ℕ => nthCode w.unpair.1 w.unpair.2.unpair.2.unpair.1 0) :=
    (primrec_nthCode.comp (Nat.Primrec.left.pair
      ((Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)).pair
        (Nat.Primrec.const 0)))).of_eq fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hright : Nat.Primrec (fun w : ℕ => nthCode w.unpair.1 w.unpair.2.unpair.2.unpair.2 0) :=
    (primrec_nthCode.comp (Nat.Primrec.left.pair
      ((Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)).pair
        (Nat.Primrec.const 0)))).of_eq fun w => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hnode : Nat.Primrec (fun w : ℕ =>
      Uinter (nthCode w.unpair.1 w.unpair.2.unpair.2.unpair.1 0)
        (nthCode w.unpair.1 w.unpair.2.unpair.2.unpair.2 0)) :=
    (Uinter_primrec.comp (hleft.pair hright)).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have htag : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hisone1 : Nat.Primrec (fun w : ℕ => isOne (1 - w.unpair.2.unpair.1)) :=
    primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 1) htag)
  have hisone2 : Nat.Primrec (fun w : ℕ => isOne (2 - w.unpair.2.unpair.1)) :=
    primrec_isOne.comp (primrec_sub₂ (Nat.Primrec.const 2) htag)
  refine (primrec_selectFn hisone1 hleaf
    (primrec_selectFn hisone2 hnode (Nat.Primrec.const UComputablePresentation.masterIdx))).of_eq
    fun w => ?_
  show _ = QLookup r w
  unfold QLookup QBody
  match tag : w.unpair.2.unpair.1 with
  | 0 =>
    have h10 : (1 - 0 : ℕ) = 1 := rfl
    simp only [h10, isOne_one, selectFn_one]
  | 1 =>
    have h01' : (1 - 1 : ℕ) = 0 := rfl
    have h12' : (2 - 1 : ℕ) = 1 := rfl
    simp only [h01', h12', isOne_zero, isOne_one, selectFn_zero, selectFn_one]
  | t + 2 =>
    have h01' : (1 - (t + 2) : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    have h12' : (2 - (t + 2) : ℕ) = 0 := Nat.sub_eq_zero_of_le (by omega)
    simp only [h01', h12', isOne_zero, selectFn_zero]

/-- `QFuel r fuel c`: fuel-indexed evaluation of a term-algebra code (base value `0` at `fuel = 0`,
irrelevant since every use below supplies `fuel > c`). -/
def QFuel : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, c => QBody r (QFuel fuel) c

theorem QFuel_fuelTable_eq :
    ∀ fuel bound c, c ≤ bound →
      nthCode (fuelTable (QLookup r) bound fuel) c 0 = QFuel r fuel c :=
  fuelTable_eq_of_recursion (F := QFuel r) (Body := QBody r) (fun _ => rfl) (fun _ _ => rfl)
    (fun table c => by unfold QLookup QBody; simp only [unpair_pair_fst, unpair_pair_snd])
    (fun f g c h => QBody_local r f g c
      (h c.unpair.2.unpair.1 (le_trans (unpair_left_le c.unpair.2) (unpair_snd_le c)))
      (h c.unpair.2.unpair.2 (le_trans (unpair_snd_le c.unpair.2) (unpair_snd_le c))))

/-- **`QFuel r` is jointly primitive recursive in `(fuel, code)`.** Mirrors
`primrec_decodeFuelOkChar2` exactly. -/
theorem primrec_QFuel2 (hr : Nat.Primrec r) :
    Nat.Primrec (fun s : ℕ => QFuel r s.unpair.1 s.unpair.2) := by
  have hft := primrec_fuelTable (primrec_QLookup r hr)
  have hpack : Nat.Primrec (fun s : ℕ => Nat.pair s.unpair.2 s.unpair.1) :=
    Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left
  have hcomp : Nat.Primrec (fun s => fuelTable (QLookup r) s.unpair.2 s.unpair.1) :=
    (hft.comp hpack).of_eq fun s => by simp only [unpair_pair_fst, unpair_pair_snd]
  have hnth : Nat.Primrec
      (fun s => nthCode (fuelTable (QLookup r) s.unpair.2 s.unpair.1) s.unpair.2 0) :=
    (primrec_nthCode.comp
      (hcomp.pair ((Nat.Primrec.right).pair (Nat.Primrec.const 0)))).of_eq
      fun s => by simp only [unpair_pair_fst, unpair_pair_snd]
  exact hnth.of_eq fun s => QFuel_fuelTable_eq r s.unpair.1 s.unpair.2 s.unpair.2 (le_refl _)

/-- **Stabilization.** Once the fuel exceeds the code, `QFuel r`'s value no longer depends on
*which* sufficiently-large fuel was supplied — the key fact letting us read off a genuine,
fuel-free evaluator `TreeVal` below. Proved by strong induction on `c`, splitting on whether `c`'s
tag is `0` (no recursion, both sides agree immediately) or positive (both children are strictly
`< c`, via `unpair_snd_lt_of_unpair_fst_pos`, so the induction hypothesis applies to them). -/
theorem QFuel_stable :
    ∀ c fuel fuel', c < fuel → c < fuel' → QFuel r fuel c = QFuel r fuel' c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro fuel fuel' hfuel hfuel'
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨f', rfl⟩ : ∃ f', fuel' = f' + 1 := ⟨fuel' - 1, by omega⟩
    show QBody r (QFuel r f) c = QBody r (QFuel r f') c
    rcases Nat.eq_zero_or_pos c.unpair.1 with htag0 | htagpos
    · have hval : isOne (1 - c.unpair.1) = 1 := by rw [htag0]; rfl
      unfold QBody
      simp only [hval, selectFn_one]
    · have hsndlt : c.unpair.2 < c := unpair_snd_lt_of_unpair_fst_pos htagpos
      have h1lt : c.unpair.2.unpair.1 < c := lt_of_le_of_lt (unpair_left_le c.unpair.2) hsndlt
      have h2lt : c.unpair.2.unpair.2 < c := lt_of_le_of_lt (unpair_snd_le c.unpair.2) hsndlt
      have hfc : c ≤ f := by omega
      have hfc' : c ≤ f' := by omega
      have e1 := ih c.unpair.2.unpair.1 h1lt f f'
        (lt_of_lt_of_le h1lt hfc) (lt_of_lt_of_le h1lt hfc')
      have e2 := ih c.unpair.2.unpair.2 h2lt f f'
        (lt_of_lt_of_le h2lt hfc) (lt_of_lt_of_le h2lt hfc')
      exact QBody_local r (QFuel r f) (QFuel r f') c e1 e2

/-- **`TreeVal r c`: the fuel-free evaluator** (fuel `c + 1` is always enough, `c` being an upper
bound on any code's own recursion depth). -/
def TreeVal (c : ℕ) : ℕ := QFuel r (c + 1) c

theorem TreeVal_eq_QFuel {c fuel : ℕ} (h : c < fuel) : TreeVal r c = QFuel r fuel c :=
  QFuel_stable r c (c + 1) fuel (Nat.lt_succ_self c) h

theorem primrec_TreeVal (hr : Nat.Primrec r) : Nat.Primrec (TreeVal r) := by
  have h2 := primrec_QFuel2 r hr
  have hpack : Nat.Primrec (fun c : ℕ => Nat.pair (c + 1) c) :=
    (primrec_add₂ Nat.Primrec.id (Nat.Primrec.const 1)).pair Nat.Primrec.id
  refine (h2.comp hpack).of_eq fun c => ?_
  show QFuel r (Nat.pair (c + 1) c).unpair.1 (Nat.pair (c + 1) c).unpair.2 = TreeVal r c
  rw [unpair_pair_fst, unpair_pair_snd]
  rfl

/-- **Unfolding at a leaf.** -/
theorem TreeVal_leaf (j : ℕ) : TreeVal r (leafCode j) = r j := by
  have htag : (leafCode j).unpair.1 = 0 := by unfold leafCode; rw [unpair_pair_fst]
  have hpay : (leafCode j).unpair.2 = j := by unfold leafCode; rw [unpair_pair_snd]
  have h1 : isOne (1 - (leafCode j).unpair.1) = 1 := by rw [htag]; rfl
  show QBody r (QFuel r (leafCode j)) (leafCode j) = r j
  unfold QBody
  simp only [h1, hpay, selectFn_one]

/-- **Unfolding at the master constant.** -/
theorem TreeVal_master : TreeVal r masterCode = UComputablePresentation.masterIdx := by
  have htag : masterCode.unpair.1 = 2 := by unfold masterCode; rw [unpair_pair_fst]
  have h1 : isOne (1 - masterCode.unpair.1) = 0 := by rw [htag]; rfl
  have h2 : isOne (2 - masterCode.unpair.1) = 0 := by rw [htag]; rfl
  show QBody r (QFuel r masterCode) masterCode = UComputablePresentation.masterIdx
  unfold QBody
  simp only [h1, h2, selectFn_zero]

/-- **Unfolding at a node.** -/
theorem TreeVal_node (t1 t2 : ℕ) :
    TreeVal r (nodeCode t1 t2) = Uinter (TreeVal r t1) (TreeVal r t2) := by
  have ht1 : t1 < nodeCode t1 t2 := nodeCode_fst_lt t1 t2
  have ht2 : t2 < nodeCode t1 t2 := nodeCode_snd_lt t1 t2
  have htag : (nodeCode t1 t2).unpair.1 = 1 := by unfold nodeCode; rw [unpair_pair_fst]
  have hc1 : (nodeCode t1 t2).unpair.2.unpair.1 = t1 := by
    unfold nodeCode; rw [unpair_pair_snd, unpair_pair_fst]
  have hc2 : (nodeCode t1 t2).unpair.2.unpair.2 = t2 := by
    unfold nodeCode; rw [unpair_pair_snd, unpair_pair_snd]
  have h1 : isOne (1 - (nodeCode t1 t2).unpair.1) = 0 := by rw [htag]; rfl
  have h2 : isOne (2 - (nodeCode t1 t2).unpair.1) = 1 := by rw [htag]; rfl
  show QBody r (QFuel r (nodeCode t1 t2)) (nodeCode t1 t2) = Uinter (TreeVal r t1) (TreeVal r t2)
  unfold QBody
  simp only [h1, h2, hc1, hc2, selectFn_zero, selectFn_one]
  rw [TreeVal_eq_QFuel r ht1, TreeVal_eq_QFuel r ht2]

/-- **Tag-`0` unfolding, for an arbitrary code (not just a literal `leafCode`).** Needed for the
`mem_X` induction below, which case-splits on an arbitrary code's tag rather than reconstructing it
as `leafCode`/`nodeCode`/`masterCode`. -/
theorem TreeVal_of_tag0 {c : ℕ} (h : c.unpair.1 = 0) : TreeVal r c = r c.unpair.2 := by
  have h1 : isOne (1 - c.unpair.1) = 1 := by rw [h]; rfl
  show QBody r (QFuel r c) c = r c.unpair.2
  unfold QBody
  simp only [h1, selectFn_one]

/-- **Tag-`1` unfolding, for an arbitrary code.** -/
theorem TreeVal_of_tag1 {c : ℕ} (h : c.unpair.1 = 1) :
    TreeVal r c = Uinter (TreeVal r c.unpair.2.unpair.1) (TreeVal r c.unpair.2.unpair.2) := by
  have h1 : isOne (1 - c.unpair.1) = 0 := by rw [h]; rfl
  have h2 : isOne (2 - c.unpair.1) = 1 := by rw [h]; rfl
  have hsndlt : c.unpair.2 < c := unpair_snd_lt_of_unpair_fst_pos (by omega)
  have ht1 : c.unpair.2.unpair.1 < c := lt_of_le_of_lt (unpair_left_le c.unpair.2) hsndlt
  have ht2 : c.unpair.2.unpair.2 < c := lt_of_le_of_lt (unpair_snd_le c.unpair.2) hsndlt
  show QBody r (QFuel r c) c = Uinter (TreeVal r c.unpair.2.unpair.1) (TreeVal r c.unpair.2.unpair.2)
  unfold QBody
  simp only [h1, h2, selectFn_zero, selectFn_one]
  rw [TreeVal_eq_QFuel r ht1, TreeVal_eq_QFuel r ht2]

/-- **Tag-`≥ 2` unfolding, for an arbitrary code.** -/
theorem TreeVal_of_tag_ge2 {c : ℕ} (h : 2 ≤ c.unpair.1) :
    TreeVal r c = UComputablePresentation.masterIdx := by
  have h1 : isOne (1 - c.unpair.1) = 0 := by
    have : (1 - c.unpair.1 : ℕ) = 0 := by omega
    rw [this]; rfl
  have h2 : isOne (2 - c.unpair.1) = 0 := by
    have : (2 - c.unpair.1 : ℕ) = 0 := by omega
    rw [this]; rfl
  show QBody r (QFuel r c) c = UComputablePresentation.masterIdx
  unfold QBody
  simp only [h1, h2, selectFn_zero]

end TreeVal

/-! ### `Q2X` — the term-algebra-indexed enumeration of `D'x`'s neighbourhoods -/

section TreeVal2

variable (r : ℕ → ℕ) (x : (SubD UComputablePresentation).Element)

/-- **`Q2X r`: the term-algebra enumeration of `D'x`'s neighbourhoods.** -/
def Q2X (c : ℕ) : Set ℚ := UX (TreeVal r c)

/-- **`mem_X` for `Q2X r`.** Every `Q2X r c` is a `D'x`-neighbourhood — by strong induction on the
code `c`, splitting on its tag exactly as `TreeVal` itself does: tag `0` (leaf) is
`D'x.mem (UX (r j))`, always true by `hspec` (witness `j` itself); tag `1` (node) combines the two
(inductively already-`D'x.mem`) children via `Uinter`'s dichotomy (`UX_Uinter_dichotomy`), landing on
`D'x.master_mem` on fallback or on `x`'s own filter closure (`nbhdGen_inter`/`interFrom_append_eq`,
exactly as in `toSubsystemSys_mem_foldl_Uinter`) otherwise; tag `≥ 2` (master) is `D'x.master_mem`
directly via `masterIdx_spec`. -/
theorem Q2x_mem_X (hspec : ∀ i, (toSubsystemSys UComputablePresentation x).mem (UX i) ↔ ∃ n, r n = i) :
    ∀ c, (toSubsystemSys UComputablePresentation x).mem (Q2X r c) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    show (toSubsystemSys UComputablePresentation x).mem (UX (TreeVal r c))
    rcases Nat.lt_or_ge c.unpair.1 2 with htag | htag
    · have htag01 : c.unpair.1 = 0 ∨ c.unpair.1 = 1 := by omega
      rcases htag01 with htagv | htagv
      · rw [TreeVal_of_tag0 r htagv]
        exact (hspec (r c.unpair.2)).mpr ⟨c.unpair.2, rfl⟩
      · rw [TreeVal_of_tag1 r htagv]
        have hsndlt : c.unpair.2 < c := unpair_snd_lt_of_unpair_fst_pos (by omega)
        have ht1 : c.unpair.2.unpair.1 < c := lt_of_le_of_lt (unpair_left_le c.unpair.2) hsndlt
        have ht2 : c.unpair.2.unpair.2 < c := lt_of_le_of_lt (unpair_snd_le c.unpair.2) hsndlt
        have hm1 := ih c.unpair.2.unpair.1 ht1
        have hm2 := ih c.unpair.2.unpair.2 ht2
        unfold Q2X at hm1 hm2
        rcases UX_Uinter_dichotomy (TreeVal r c.unpair.2.unpair.1) (TreeVal r c.unpair.2.unpair.2)
          with hcase | hcase
        · rw [hcase]; exact (toSubsystemSys UComputablePresentation x).master_mem
        · rw [hcase]
          obtain ⟨jsA, hxA, subA, hsubA, hDA, hAeq⟩ := hm1
          obtain ⟨jsB, hxB, subB, hsubB, hDB, hBeq⟩ := hm2
          have hUmem : U.mem (UX (TreeVal r c.unpair.2.unpair.1) ∩ UX (TreeVal r c.unpair.2.unpair.2)) :=
            hcase ▸ U_mem_UX (Uinter (TreeVal r c.unpair.2.unpair.1) (TreeVal r c.unpair.2.unpair.2))
          refine ⟨jsA ++ jsB, nbhdGen_inter UComputablePresentation jsA jsB ▸ x.inter_mem hxA hxB,
            subA ++ subB, hsubA.append hsubB, hUmem, ?_⟩
          rw [hAeq, hBeq, interFrom_append_eq UComputablePresentation U.master subA subB]
    · rw [TreeVal_of_tag_ge2 r htag]
      show (toSubsystemSys UComputablePresentation x).mem (UX UmasterIdx)
      rw [UX_UmasterIdx]
      exact (toSubsystemSys UComputablePresentation x).master_mem

/-- **`surj` bridge, part 1: embed a `List ℕ` into a term-algebra code.** Left-fold accumulator
mirroring *exactly* the fold shape of `Theorem75.idxchain`/`Q'X` (`Uinter`-folded from the master),
via `nodeCode`/`leafCode` instead of `Uinter`/`r` directly — so that `TreeVal` evaluates it to the
same `U`-index (`TreeVal_listToTreeAux` below). -/
def listToTreeAux : ℕ → List ℕ → ℕ
  | acc, [] => acc
  | acc, j :: l => listToTreeAux (nodeCode acc (leafCode j)) l

theorem TreeVal_listToTreeAux (acc : ℕ) (l : List ℕ) :
    TreeVal r (listToTreeAux acc l) = l.foldl (fun a j => Uinter a (r j)) (TreeVal r acc) := by
  induction l generalizing acc with
  | nil => simp [listToTreeAux]
  | cons j l ih =>
    simp only [listToTreeAux, List.foldl_cons]
    rw [ih, TreeVal_node, TreeVal_leaf]

/-- **`surj` for `Q2X r`.** Every `D'x`-neighbourhood `Y` is some `Q2X r c` — reduce to the already-
proven list-based `Q'x_surj` (`Y = Q'X r n` for some `n`), then push `decodeList n` through
`listToTreeAux` and identify the result with `idxchain`'s own fold via `List.foldl_map`, so the same
`n` (repackaged as a tree code) also witnesses `Q2X r`. No fresh combinatorial work: this is a pure
bridging argument between the list-indexed and term-algebra-indexed enumerations of the *same*
underlying `Uinter`-folds. -/
theorem Q2x_surj (hspec : ∀ i, (toSubsystemSys UComputablePresentation x).mem (UX i) ↔ ∃ n, r n = i)
    {Y : Set ℚ} (hY : (toSubsystemSys UComputablePresentation x).mem Y) :
    ∃ c, Q2X r c = Y := by
  obtain ⟨n, hn⟩ := Q'x_surj r x hspec hY
  refine ⟨listToTreeAux masterCode (decodeList n), ?_⟩
  have hcode : (decodeList n).foldl (fun a j => Uinter a (r j)) UComputablePresentation.masterIdx
      = idxchain UComputablePresentation (List.map r (decodeList n)) := by
    unfold idxchain
    rw [List.foldl_map]
    rfl
  show UX (TreeVal r (listToTreeAux masterCode (decodeList n))) = Y
  rw [TreeVal_listToTreeAux, TreeVal_master, hcode, ← Q'X_eq]
  exact hn

/-! ### `inter`/`interEq_computable`/`cons_computable` — resolved by the term algebra

The obstacle diagnosed above (`Uinter`'s non-conservative fallback) is fixed by indexing
neighbourhoods by term-algebra codes instead of lists: combining two already-built codes `n`, `m` is
*literally* `nodeCode n m`, no search for a witness code needed, and `Uinter_spec` — applicable
precisely when the consistency hypothesis holds — guarantees the dichotomy's fallback branch of
`UX_Uinter_dichotomy` provably never fires on that witness. -/

/-- **`Q2X r`'s intersection function**: literally the `node` constructor. -/
def Q2inter (c1 c2 : ℕ) : ℕ := nodeCode c1 c2

theorem primrec_Q2inter : Nat.Primrec (fun t : ℕ => Q2inter t.unpair.1 t.unpair.2) := by
  have heq : (fun t : ℕ => Q2inter t.unpair.1 t.unpair.2) = fun t => Nat.pair 1 t := by
    funext t; unfold Q2inter nodeCode; rw [pair_unpair]
  rw [heq]
  exact Nat.Primrec.pair (Nat.Primrec.const 1) Nat.Primrec.id

/-- **`inter_spec` for `Q2X r`.** The hypothesis is exactly what `Uinter_spec` needs (a `UX`-witness
of consistency, transported through `TreeVal`), so `nodeCode n m` genuinely indexes the intersection
— no fallback case to worry about. -/
theorem Q2inter_spec {n m : ℕ} (h : ∃ k, Q2X r k ⊆ Q2X r n ∩ Q2X r m) :
    Q2X r (Q2inter n m) = Q2X r n ∩ Q2X r m := by
  obtain ⟨k, hk⟩ := h
  show UX (TreeVal r (nodeCode n m)) = UX (TreeVal r n) ∩ UX (TreeVal r m)
  rw [TreeVal_node]
  exact Uinter_spec ⟨TreeVal r k, hk⟩

/-- **`interEq_computable` for `Q2X r`.** A pure reindexing of `U`'s own `U_interEq_computable`
along the primitive-recursive `TreeVal r` — exactly `ComputablePresentation.reindexInvolutive`'s
`interEq_computable` proof pattern, minus the involution (only needed there for the `masterIdx`/
`inter` fields, not for `.comp`-reindexing a `RecDecidable`). -/
theorem Q2_interEq_computable (hr : Nat.Primrec r) :
    RecDecidable₃ (fun n m k => Q2X r n ∩ Q2X r m = Q2X r k) := by
  have hTV := primrec_TreeVal r hr
  have hreindex : Nat.Primrec (fun t : ℕ => Nat.pair (TreeVal r t.unpair.1)
      (Nat.pair (TreeVal r t.unpair.2.unpair.1) (TreeVal r t.unpair.2.unpair.2))) :=
    (hTV.comp Nat.Primrec.left).pair
      ((hTV.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
        (hTV.comp (Nat.Primrec.right.comp Nat.Primrec.right)))
  refine RecDecidable.of_iff (fun t => ?_) (U_interEq_computable.comp hreindex)
  simp only [unpair_pair_fst, unpair_pair_snd]
  rfl

/-- **`cons_computable` for `Q2X r`.** The crux resolved by the term algebra: the backward
direction's witness is `nodeCode n m`, no search needed to *name* it, and it works because
`Uinter_spec` applies exactly when consistency holds. -/
theorem Q2_cons_computable (hr : Nat.Primrec r) :
    RecDecidable₂ (fun n m => ∃ k, Q2X r k ⊆ Q2X r n ∩ Q2X r m) := by
  have hTV := primrec_TreeVal r hr
  have hreindex : Nat.Primrec (fun t : ℕ => Nat.pair (TreeVal r t.unpair.1) (TreeVal r t.unpair.2)) :=
    (hTV.comp Nat.Primrec.left).pair (hTV.comp Nat.Primrec.right)
  refine RecDecidable.of_iff (fun t => ?_) (U_cons_computable.comp hreindex)
  simp only [unpair_pair_fst, unpair_pair_snd]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨TreeVal r k, hk⟩
  · rintro ⟨k, hk⟩
    refine ⟨nodeCode t.unpair.1 t.unpair.2, ?_⟩
    show UX (TreeVal r (nodeCode t.unpair.1 t.unpair.2)) ⊆
      UX (TreeVal r t.unpair.1) ∩ UX (TreeVal r t.unpair.2)
    rw [TreeVal_node, Uinter_spec ⟨k, hk⟩]

theorem Q2X_masterIdx_spec :
    Q2X r masterCode = (toSubsystemSys UComputablePresentation x).master := by
  show UX (TreeVal r masterCode) = U.master
  rw [TreeVal_master]
  exact UX_UmasterIdx

/-- **Subgoal 6f, capstone.** `D'x := toSubsystemSys UComputablePresentation x` admits a genuine
`ComputablePresentation`, assembled from `Q2X`/`Q2x_mem_X`/`Q2x_surj`/`Q2_interEq_computable`/
`Q2_cons_computable`/`Q2inter`/`Q2inter_spec`/`masterCode`/`Q2X_masterIdx_spec` — resolving the gap
flagged above via the binary term algebra. -/
def Q'xPresentation (hr : Nat.Primrec r)
    (hspec : ∀ i, (toSubsystemSys UComputablePresentation x).mem (UX i) ↔ ∃ n, r n = i) :
    ComputablePresentation (toSubsystemSys UComputablePresentation x) where
  X := Q2X r
  mem_X := Q2x_mem_X r x hspec
  surj := Q2x_surj r x hspec
  interEq_computable := Q2_interEq_computable r hr
  cons_computable := Q2_cons_computable r hr
  inter := Q2inter
  inter_primrec := primrec_Q2inter
  inter_spec := fun h => Q2inter_spec r h
  masterIdx := masterCode
  masterIdx_spec := Q2X_masterIdx_spec r x

/-- **Subgoal 6f, main corollary.** If `x` is a computable element of `SubD UComputablePresentation`,
then `D'x := toSubsystemSys UComputablePresentation x` is effectively given — completing, for
`D = 𝒰`, the second half of Exercise 8.15: computable elements of `SubD UComputablePresentation`
correspond to effectively presented domains, presented *relative to* `UComputablePresentation`'s own
enumeration (see the 6g note in `arxiv.md` for why the fully general "arbitrary presentation"
converse — genuine "uniqueness of computable numberings" — is out of scope). -/
theorem subsystemU_effectivelyGiven_of_isComputableElement
    (hx : IsComputableElement (SubDPresentation UComputablePresentation) x) :
    (toSubsystemSys UComputablePresentation x).IsEffectivelyGiven := by
  obtain ⟨r, hr, hspec⟩ := (subsystemU_element_computable_iff UComputablePresentation x).mp hx
  exact ⟨Q'xPresentation r x hr hspec⟩

/-! ### 6g — scope note: the fully general "arbitrary presentation" converse

`subsystemU_effectivelyGiven_of_isComputableElement` reads Scott's "computable elements correspond
to effectively presented domains (up to effective isomorphism)" via the *specific* presentation
`Q'xPresentation` built **relative to `UComputablePresentation`'s own enumeration** — the natural,
provable reading identified in the Subgoal 6 planning note above (a disjoint-interval example shows
`x.mem (nbhdGen UP js)` does **not** imply `𝒰.mem (interFrom UP 𝒰.master js)` in general, so an
*arbitrary*, unrelated abstract presentation `Q : ComputablePresentation D'x` cannot be compared to
`UP` without extra structure).

The fully general converse Scott's parenthetical "(up to effective isomorphism)" is gesturing at —
that *every* computable presentation of `D'x`, however constructed, is effectively isomorphic to
`Q'xPresentation` — is a genuine "uniqueness of computable numberings" fact (a Rogers-style theorem:
two numberings of the same recursively enumerable structure that both make its structural relations
decidable must be effectively translatable into each other). This is strictly deeper than anything
Definition 7.1's axioms hand us directly, is not needed for the "correspond to" reading already
established by `subsystemU_effectivelyGiven_of_isComputableElement`, and is **deliberately left out
of scope** here. -/

end TreeVal2

end UniversalSubsystem

end Scott1980.Neighborhood

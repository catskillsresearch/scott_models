/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Exercise715

/-!
# Exercise 7.18 (Scott 1981, PRG-19, §7) — effective isomorphism; `D^∞ ≅ (D^∞)^∞` is effective

> **EXERCISE 7.18.** Two effectively given systems `D` and `E` are *effectively isomorphic* iff …
> (complete the sentence!). Show that if `D` is effectively given then the isomorphism
> `D^∞ ≅ (D^∞)^∞` is effective.

## Completing the sentence (Definition of *effective isomorphism*)

Scott's Definition 1.9 says `D ≅ E` means there is a one-one, inclusion-preserving correspondence
`|D| ≃o |E|`; Theorem 2.7 shows every such correspondence *is* induced by an approximable map. The
*effective* refinement is the obvious one: the isomorphism, together with its inverse, must be
**computable** in the sense of Definition 7.2. We package this symmetrically as a pair of mutually
inverse computable approximable maps:

* `EffectiveIso P Q` — relative to computable presentations `P` of `D` and `Q` of `E`, a pair
  `toMap : D → E`, `invMap : E → D` of approximable maps, **both computable** (`IsComputableMap`),
  that are mutually inverse (`invMap ∘ toMap = I_D` and `toMap ∘ invMap = I_E`).
* `EffectivelyIsomorphic P Q := Nonempty (EffectiveIso P Q)`.

Every effective isomorphism is in particular a domain isomorphism (`EffectiveIso.toDomainIso`,
`EffectivelyIsomorphic.isomorphic`), so this tightens Scott's `≅` (and, via Exercise 7.13's
`reconstruct_isomorphic`, tightens its "essentially the same").

## `D^∞ ≅ (D^∞)^∞` is effective

`D^∞ = iterSys V` (Exercise 3.16) has token type `ℕ × α` and elements the infinite sequences
`⟨x_k⟩` of `|D|`-elements (`iterSeqEquiv`). `(D^∞)^∞ = iterSys (iterSys V)` has token type
`ℕ × (ℕ × α)` and elements the *double* sequences `⟨⟨x_{i,j}⟩_j⟩_i`. The isomorphism is the index
reindexing along `Nat.pair`/`Nat.unpair`: `x_k ↔ x_{(unpair k).1,(unpair k).2}`, i.e.
`x_{i,j} = x_{pair i j}`.

We realise the two directions as explicit approximable maps with clean neighbourhood relations
(`Fmap`, `Gmap`), where the *double-indexed fiber* of a `(D^∞)^∞`-neighbourhood `S` is
`fiber2 S i j = fiber (fiber S i) j`:

* `Fmap.rel W S ↔ ∀ i j, fiber W (pair i j) ⊆ fiber2 S i j`;
* `Gmap.rel S W ↔ ∀ k, fiber2 S (unpair k).1 (unpair k).2 ⊆ fiber W k`.

They are mutually inverse (`Gmap.comp Fmap = I`, `Fmap.comp Gmap = I`), proved directly on the
relations using the reindexing constructions `reindexF`/`reindexG`. Each is **recursively decidable**
(hence computable) over `iterPresentation P` / `iterPresentation (iterPresentation P)`: the relation
on codes reduces to a *bounded* check of `incl_computable` over the coordinates `(i,j)` (resp. `k`)
that the codes actually constrain (everything beyond the coded fiber lengths is `Δ`, so trivially
satisfied). The whole development is choice-free (`⊆ {propext, Quot.sound}`): the one place a finite
maximum is needed (the cofinite bound of `reindexG`) is obtained by a `Prop`-level induction, not by
choosing witnesses.
-/

namespace Scott1980.Neighborhood
namespace Exercise718

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β : Type*}

/-! ## Part 1 — the definition of *effective isomorphism* -/

/-- **Exercise 7.18 (Scott 1981, PRG-19) — effective isomorphism (completing the sentence).** Two
effectively given systems `D` (presentation `P`) and `E` (presentation `Q`) are *effectively
isomorphic* iff there is a pair of mutually inverse approximable maps `toMap : D → E`,
`invMap : E → D`, **both computable** (Definition 7.2). -/
structure EffectiveIso {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (P : ComputablePresentation V) (Q : ComputablePresentation W) where
  /-- The forward map `D → E`. -/
  toMap : ApproximableMap V W
  /-- The inverse map `E → D`. -/
  invMap : ApproximableMap W V
  /-- The forward map is computable. -/
  toMap_computable : IsComputableMap P Q toMap
  /-- The inverse map is computable. -/
  invMap_computable : IsComputableMap Q P invMap
  /-- `invMap ∘ toMap = I_D`. -/
  left_inv : invMap.comp toMap = idMap V
  /-- `toMap ∘ invMap = I_E`. -/
  right_inv : toMap.comp invMap = idMap W

/-- **Exercise 7.18 — effectively isomorphic.** `D` and `E` are effectively isomorphic when an
`EffectiveIso` exists. -/
def EffectivelyIsomorphic {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (P : ComputablePresentation V) (Q : ComputablePresentation W) : Prop :=
  Nonempty (EffectiveIso P Q)

namespace EffectiveIso

variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
  {P : ComputablePresentation V} {Q : ComputablePresentation W}

/-- An effective isomorphism is in particular a domain isomorphism (`|D| ≃o |E|`): the elementwise
maps are mutually inverse (from `left_inv`/`right_inv` via `toElementMap_comp`/`toElementMap_idMap`)
and each is monotone (`toElementMap_mono`), so they reflect as well as preserve `⊑`. -/
def toDomainIso (e : EffectiveIso P Q) : DomainIso V W where
  toFun := e.toMap.toElementMap
  invFun := e.invMap.toElementMap
  left_inv x := by
    rw [← toElementMap_comp, e.left_inv, toElementMap_idMap]
  right_inv y := by
    rw [← toElementMap_comp, e.right_inv, toElementMap_idMap]
  map_rel_iff' := by
    intro x y
    show e.toMap.toElementMap x ≤ e.toMap.toElementMap y ↔ x ≤ y
    refine ⟨fun h => ?_, fun h => e.toMap.toElementMap_mono h⟩
    have hmono := e.invMap.toElementMap_mono h
    rwa [← toElementMap_comp, ← toElementMap_comp, e.left_inv, toElementMap_idMap,
      toElementMap_idMap] at hmono

end EffectiveIso

/-- **Exercise 7.18 — effective isomorphism implies domain isomorphism.** -/
theorem EffectivelyIsomorphic.isomorphic {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    {P : ComputablePresentation V} {Q : ComputablePresentation W}
    (h : EffectivelyIsomorphic P Q) : V ≅ᴰ W :=
  h.elim fun e => ⟨e.toDomainIso⟩

/-! ## Part 2 — `D^∞ ≅ (D^∞)^∞` is effective.

Throughout, `V : NeighborhoodSystem α`; `D^∞ = iterSys V` over `ℕ × α`, and
`(D^∞)^∞ = iterSys (iterSys V)` over `ℕ × (ℕ × α)`. -/

variable {V : NeighborhoodSystem α}

/-- The **double-indexed fiber** of a `(D^∞)^∞`-set: `fiber2 S i j = fiber (fiber S i) j`, the tokens
`a` with `(i, (j, a)) ∈ S`. -/
def fiber2 (S : Set (ℕ × (ℕ × α))) (i j : ℕ) : Set α := fiber (fiber S i) j

@[simp] theorem mem_fiber2 {S : Set (ℕ × (ℕ × α))} {i j : ℕ} {a : α} :
    a ∈ fiber2 S i j ↔ (i, (j, a)) ∈ S := Iff.rfl

theorem fiber2_mono {S S' : Set (ℕ × (ℕ × α))} (h : S ⊆ S') (i j : ℕ) :
    fiber2 S i j ⊆ fiber2 S' i j := fun _ ha => h ha

theorem fiber2_inter (S S' : Set (ℕ × (ℕ × α))) (i j : ℕ) :
    fiber2 (S ∩ S') i j = fiber2 S i j ∩ fiber2 S' i j := rfl

theorem fiber2_master (i j : ℕ) :
    fiber2 ((iterSys (iterSys V)).master) i j = V.master := by
  show fiber (fiber ((iterSys (iterSys V)).master) i) j = V.master
  rw [fiber_iterSys_master, fiber_iterSys_master]

/-- `V.mem (fiber2 S i j)` for every `(D^∞)^∞`-neighbourhood `S`. -/
theorem mem_fiber2_of_mem {S : Set (ℕ × (ℕ × α))} (hS : (iterSys (iterSys V)).mem S) (i j : ℕ) :
    V.mem (fiber2 S i j) := (hS.1 i).1 j

/-! ### The reindexing constructions. -/

/-- The `(D^∞)^∞`-set reindexing a `D^∞`-neighbourhood `W`: `fiber2 (reindexF W) i j = fiber W (pair i j)`. -/
def reindexF (W : Set (ℕ × α)) : Set (ℕ × (ℕ × α)) :=
  {p | p.2.2 ∈ fiber W (Nat.pair p.1 p.2.1)}

@[simp] theorem fiber2_reindexF (W : Set (ℕ × α)) (i j : ℕ) :
    fiber2 (reindexF W) i j = fiber W (Nat.pair i j) := rfl

/-- The `D^∞`-set reindexing a `(D^∞)^∞`-neighbourhood `S`:
`fiber (reindexG S) k = fiber2 S (unpair k).1 (unpair k).2`. -/
def reindexG (S : Set (ℕ × (ℕ × α))) : Set (ℕ × α) :=
  {p | p.2 ∈ fiber2 S (Nat.unpair p.1).1 (Nat.unpair p.1).2}

@[simp] theorem fiber_reindexG (S : Set (ℕ × (ℕ × α))) (k : ℕ) :
    fiber (reindexG S) k = fiber2 S (Nat.unpair k).1 (Nat.unpair k).2 := rfl

theorem reindexF_subset_iff {W : Set (ℕ × α)} {S : Set (ℕ × (ℕ × α))} :
    reindexF W ⊆ S ↔ ∀ i j, fiber W (Nat.pair i j) ⊆ fiber2 S i j := by
  constructor
  · intro h i j
    have := fiber2_mono h i j
    rwa [fiber2_reindexF] at this
  · intro h
    refine subset_of_fiber_subset (fun i => subset_of_fiber_subset (fun j => ?_))
    show fiber2 (reindexF W) i j ⊆ fiber2 S i j
    rw [fiber2_reindexF]; exact h i j

theorem reindexG_subset_iff {S : Set (ℕ × (ℕ × α))} {W : Set (ℕ × α)} :
    reindexG S ⊆ W ↔ ∀ k, fiber2 S (Nat.unpair k).1 (Nat.unpair k).2 ⊆ fiber W k := by
  constructor
  · intro h k
    have := fiber_mono h k
    rwa [fiber_reindexG] at this
  · intro h
    refine subset_of_fiber_subset (fun k => ?_)
    rw [fiber_reindexG]; exact h k

theorem reindexF_mem {W : Set (ℕ × α)} (hW : (iterSys V).mem W) :
    (iterSys (iterSys V)).mem (reindexF W) := by
  obtain ⟨hWf, Nw, hNw⟩ := hW
  refine ⟨fun i => ⟨fun j => ?_, Nw, fun j hj => ?_⟩, Nw, fun i hi => ?_⟩
  · -- inner fibers are `V`-neighbourhoods
    show V.mem (fiber2 (reindexF W) i j)
    rw [fiber2_reindexF]; exact hWf (Nat.pair i j)
  · -- inner cofinite-`Δ` (per `i`)
    show fiber2 (reindexF W) i j = V.master
    rw [fiber2_reindexF]
    exact hNw (Nat.pair i j) (le_trans hj (le_pair_right i j))
  · -- outer cofinite-`Δ`
    apply eq_of_fiber_eq
    intro j
    show fiber2 (reindexF W) i j = fiber ((iterSys V).master) j
    rw [fiber2_reindexF, fiber_iterSys_master]
    exact hNw (Nat.pair i j) (le_trans hi (le_pair_left i j))

/-! #### A choice-free uniform inner bound for `(D^∞)^∞`-neighbourhoods.

`reindexG S` is cofinite-`Δ` because the active coordinates `(i, j)` are finite (`i` below the outer
bound, `j` below each inner bound). We obtain a uniform inner bound `M` over `i < n` by `Prop`-level
induction — no witnesses are *chosen*, so this stays choice-free. -/

theorem exists_inner_bound {S : Set (ℕ × (ℕ × α))} (hS : (iterSys (iterSys V)).mem S) :
    ∀ n, ∃ M, ∀ i, i < n → ∀ j, M ≤ j → fiber2 S i j = V.master := by
  intro n
  induction n with
  | zero => exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    obtain ⟨M, hM⟩ := ih
    obtain ⟨Mn, hMn⟩ := (hS.1 n).2
    refine ⟨max M Mn, fun i hi j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact hM i hlt j (le_trans (le_max_left _ _) hj)
    · subst heq
      exact hMn j (le_trans (le_max_right _ _) hj)

/-- `Nat.pair` is strictly monotone on strict componentwise order (local copy of the
`Proposition77` lemma to avoid the heavy import). -/
private theorem pair_lt_pair_of_lt {x y i j : ℕ} (hx : x < i) (hy : y < j) :
    Nat.pair x y < Nat.pair i j := by
  have hms : ∀ z : ℕ, (z + 1) * (z + 1) = z * z + 2 * z + 1 := fun z => by
    rw [Nat.succ_mul, Nat.mul_succ]; omega
  have hlt : Nat.pair x y < (max x y + 1) * (max x y + 1) := by
    unfold Nat.pair
    rcases lt_or_ge x y with h | h
    · rw [if_pos h, show max x y = y by omega, hms]; omega
    · rw [if_neg (by omega), show max x y = x by omega, hms]; omega
  have hle : max i j * max i j ≤ Nat.pair i j := by
    unfold Nat.pair
    rcases lt_or_ge i j with h | h
    · rw [if_pos h, show max i j = j by omega]; omega
    · rw [if_neg (by omega), show max i j = i by omega]; omega
  have h3 : max x y + 1 ≤ max i j := by
    rcases le_total x y with h | h
    · rw [max_eq_right h]; have := le_max_right i j; omega
    · rw [max_eq_left h]; have := le_max_left i j; omega
  have h4 : (max x y + 1) * (max x y + 1) ≤ max i j * max i j := Nat.mul_le_mul h3 h3
  omega

theorem reindexG_mem {S : Set (ℕ × (ℕ × α))} (hS : (iterSys (iterSys V)).mem S) :
    (iterSys V).mem (reindexG S) := by
  obtain ⟨No, hNo⟩ := hS.2
  obtain ⟨M, hM⟩ := exists_inner_bound hS No
  refine ⟨fun k => ?_, Nat.pair No M, fun k hk => ?_⟩
  · -- fibers are `V`-neighbourhoods
    rw [fiber_reindexG]; exact mem_fiber2_of_mem hS _ _
  · -- cofinite-`Δ`
    rw [fiber_reindexG]
    set i := (Nat.unpair k).1 with hi
    set j := (Nat.unpair k).2 with hj
    by_cases hiN : i < No
    · by_cases hjM : j < M
      · exfalso
        have hklt : Nat.pair i j < Nat.pair No M := pair_lt_pair_of_lt hiN hjM
        rw [pair_unpair] at hklt
        omega
      · exact hM i hiN j (not_lt.mp hjM)
    · have h1 : fiber S i = (iterSys V).master := hNo i (not_lt.mp hiN)
      show fiber2 S i j = V.master
      rw [fiber2, h1, fiber_iterSys_master]

/-! ### The two approximable maps. -/

/-- **The forward map `F : D^∞ → (D^∞)^∞`** of `D^∞ ≅ (D^∞)^∞` (reindexing fibers along `Nat.pair`):
`W F S ↔ ∀ i j, fiber W (pair i j) ⊆ fiber2 S i j`. -/
def Fmap (V : NeighborhoodSystem α) : ApproximableMap (iterSys V) (iterSys (iterSys V)) where
  rel W S := (iterSys V).mem W ∧ (iterSys (iterSys V)).mem S ∧
    ∀ i j, fiber W (Nat.pair i j) ⊆ fiber2 S i j
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(iterSys V).master_mem, (iterSys (iterSys V)).master_mem, fun i j => by
    rw [fiber_iterSys_master, fiber2_master]⟩
  inter_right := by
    rintro W S S' ⟨hW, hS, hf⟩ ⟨-, hS', hf'⟩
    refine ⟨hW, (iterSys (iterSys V)).inter_mem hS hS' (reindexF_mem hW) ?_, fun i j => ?_⟩
    · exact Set.subset_inter (reindexF_subset_iff.mpr hf) (reindexF_subset_iff.mpr hf')
    · rw [fiber2_inter]; exact Set.subset_inter (hf i j) (hf' i j)
  mono := by
    rintro W W' S S' ⟨hW, hS, hf⟩ hW'W hSS' hW' hS'
    exact ⟨hW', hS', fun i j => ((fiber_mono hW'W _).trans (hf i j)).trans (fiber2_mono hSS' i j)⟩

@[simp] theorem Fmap_rel {W : Set (ℕ × α)} {S : Set (ℕ × (ℕ × α))} :
    (Fmap V).rel W S ↔ (iterSys V).mem W ∧ (iterSys (iterSys V)).mem S ∧
      ∀ i j, fiber W (Nat.pair i j) ⊆ fiber2 S i j := Iff.rfl

/-- **The inverse map `G : (D^∞)^∞ → D^∞`** (reindexing fibers along `Nat.unpair`):
`S G W ↔ ∀ k, fiber2 S (unpair k).1 (unpair k).2 ⊆ fiber W k`. -/
def Gmap (V : NeighborhoodSystem α) : ApproximableMap (iterSys (iterSys V)) (iterSys V) where
  rel S W := (iterSys (iterSys V)).mem S ∧ (iterSys V).mem W ∧
    ∀ k, fiber2 S (Nat.unpair k).1 (Nat.unpair k).2 ⊆ fiber W k
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(iterSys (iterSys V)).master_mem, (iterSys V).master_mem, fun k => by
    rw [fiber2_master, fiber_iterSys_master]⟩
  inter_right := by
    rintro S W W' ⟨hS, hW, hg⟩ ⟨-, hW', hg'⟩
    refine ⟨hS, (iterSys V).inter_mem hW hW' (reindexG_mem hS) ?_, fun k => ?_⟩
    · exact Set.subset_inter (reindexG_subset_iff.mpr hg) (reindexG_subset_iff.mpr hg')
    · rw [fiber_inter]; exact Set.subset_inter (hg k) (hg' k)
  mono := by
    rintro S S' W W' ⟨hS, hW, hg⟩ hS'S hWW' hS' hW'
    exact ⟨hS', hW', fun k => ((fiber2_mono hS'S _ _).trans (hg k)).trans (fiber_mono hWW' k)⟩

@[simp] theorem Gmap_rel {S : Set (ℕ × (ℕ × α))} {W : Set (ℕ × α)} :
    (Gmap V).rel S W ↔ (iterSys (iterSys V)).mem S ∧ (iterSys V).mem W ∧
      ∀ k, fiber2 S (Nat.unpair k).1 (Nat.unpair k).2 ⊆ fiber W k := Iff.rfl

/-! ### `F` and `G` are mutually inverse. -/

/-- `G ∘ F = I_{D^∞}`. -/
theorem Gmap_comp_Fmap : (Gmap V).comp (Fmap V) = idMap (iterSys V) := by
  apply ApproximableMap.ext
  intro W W'
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨S, ⟨hW, hS, hf⟩, ⟨-, hW', hg⟩⟩
    refine ⟨hW, hW', subset_of_fiber_subset (fun k => ?_)⟩
    have h1 : fiber W k ⊆ fiber2 S (Nat.unpair k).1 (Nat.unpair k).2 := by
      have := hf (Nat.unpair k).1 (Nat.unpair k).2
      rwa [pair_unpair] at this
    exact h1.trans (hg k)
  · rintro ⟨hW, hW', hWW'⟩
    refine ⟨reindexF W, ⟨hW, reindexF_mem hW, ?_⟩, ⟨reindexF_mem hW, hW', ?_⟩⟩
    · intro i j; rw [fiber2_reindexF]
    · intro k
      rw [fiber2_reindexF, pair_unpair]
      exact fiber_mono hWW' k

/-- `F ∘ G = I_{(D^∞)^∞}`. -/
theorem Fmap_comp_Gmap : (Fmap V).comp (Gmap V) = idMap (iterSys (iterSys V)) := by
  apply ApproximableMap.ext
  intro S S'
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨W, ⟨hS, hW, hg⟩, ⟨-, hS', hf⟩⟩
    refine ⟨hS, hS', subset_of_fiber_subset (fun i => subset_of_fiber_subset (fun j => ?_))⟩
    show fiber2 S i j ⊆ fiber2 S' i j
    have h1 : fiber2 S i j ⊆ fiber W (Nat.pair i j) := by
      have := hg (Nat.pair i j)
      rwa [unpair_pair_fst, unpair_pair_snd] at this
    exact h1.trans (hf i j)
  · rintro ⟨hS, hS', hSS'⟩
    refine ⟨reindexG S, ⟨hS, reindexG_mem hS, ?_⟩, ⟨reindexG_mem hS, hS', ?_⟩⟩
    · intro k; rw [fiber_reindexG]
    · intro i j
      rw [fiber_reindexG, unpair_pair_fst, unpair_pair_snd]
      exact fiber2_mono hSS' i j

/-! ### Computability of `F` and `G`.

We work over `iterPresentation P` (for `D^∞`) and `iterPresentation (iterPresentation P)` (for
`(D^∞)^∞`). The double-indexed fiber of the `(D^∞)^∞`-enumeration reads off as a doubly-indexed
`iterIdx`: -/

variable (P : ComputablePresentation V)

theorem fiber2_iterEnum_iter (m i j : ℕ) :
    fiber2 (iterEnum (iterPresentation P) m) i j
      = P.X (iterIdx P (iterIdx (iterPresentation P) m i) j) := by
  show fiber (fiber (iterEnum (iterPresentation P) m) i) j = _
  rw [fiber_iterEnum, iterPresentation_X, fiber_iterEnum]

theorem masterIdx_iterPresentation : (iterPresentation P).masterIdx = 0 := rfl

variable {P}

/-- **Characterisation of `F`'s relation on codes.** Relative to `iterPresentation P` and
`iterPresentation (iterPresentation P)`, the relation reduces to a *bounded* double inclusion:
beyond the coded fiber lengths every fiber is `Δ`, so only `i < m` and `j < iterIdx (iterᴾ) m i`
matter. -/
theorem Fmap_rel_enum_iff (n m : ℕ) :
    (Fmap V).rel (iterEnum P n) (iterEnum (iterPresentation P) m) ↔
      ∀ i, i < m → ∀ j, j < iterIdx (iterPresentation P) m i →
        P.X (iterIdx P n (Nat.pair i j)) ⊆ P.X (iterIdx P (iterIdx (iterPresentation P) m i) j) := by
  rw [Fmap_rel]
  have hmem₁ := iterEnum_mem (P := P) n
  have hmem₂ := iterEnum_mem (P := iterPresentation P) m
  constructor
  · rintro ⟨-, -, hf⟩ i _ j _
    have := hf i j
    rwa [fiber_iterEnum, fiber2_iterEnum_iter] at this
  · intro hbd
    refine ⟨hmem₁, hmem₂, fun i j => ?_⟩
    rw [fiber_iterEnum, fiber2_iterEnum_iter]
    by_cases hi : i < m
    · by_cases hj : j < iterIdx (iterPresentation P) m i
      · exact hbd i hi j hj
      · -- `j` beyond the inner length ⟹ RHS `= Δ`
        rw [iterIdx_ge (not_lt.mp hj), P.masterIdx_spec]
        exact V.sub_master (P.mem_X _)
    · -- `i` beyond the outer length ⟹ inner code `= 0` ⟹ RHS `= Δ`
      have h0 : iterIdx (iterPresentation P) m i = 0 := by
        rw [iterIdx_ge (not_lt.mp hi), masterIdx_iterPresentation]
      rw [h0, iterIdx_ge (Nat.zero_le j), P.masterIdx_spec]
      exact V.sub_master (P.mem_X _)

/-- **Characterisation of `G`'s relation on codes.** A single bounded inclusion: only `k < n`
matters (the codomain fiber is `Δ` for `k ≥ n`). -/
theorem Gmap_rel_enum_iff (s n : ℕ) :
    (Gmap V).rel (iterEnum (iterPresentation P) s) (iterEnum P n) ↔
      ∀ k, k < n →
        P.X (iterIdx P (iterIdx (iterPresentation P) s (Nat.unpair k).1) (Nat.unpair k).2)
          ⊆ P.X (iterIdx P n k) := by
  rw [Gmap_rel]
  have hmem₁ := iterEnum_mem (P := iterPresentation P) s
  have hmem₂ := iterEnum_mem (P := P) n
  constructor
  · rintro ⟨-, -, hg⟩ k _
    have := hg k
    rwa [fiber2_iterEnum_iter, fiber_iterEnum] at this
  · intro hbd
    refine ⟨hmem₁, hmem₂, fun k => ?_⟩
    rw [fiber2_iterEnum_iter, fiber_iterEnum]
    by_cases hk : k < n
    · exact hbd k hk
    · rw [iterIdx_ge (not_lt.mp hk), P.masterIdx_spec]
      exact V.sub_master (P.mem_X _)

/-- **`F` is computable** (in fact recursively decidable): its index relation reduces to a nested
bounded `∀` of `incl_computable`. -/
theorem Fmap_isComputable :
    IsComputableMap (iterPresentation P) (iterPresentation (iterPresentation P)) (Fmap V) := by
  -- inner predicate `p₂ u`, with `u = ⟨j, ⟨i, ⟨n, m⟩⟩⟩`
  have hLHS : Nat.Primrec (fun u : ℕ =>
      iterIdx P u.unpair.2.unpair.2.unpair.1 (Nat.pair u.unpair.2.unpair.1 u.unpair.1)) := by
    refine (primrec_nthCode.comp
      ((Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)).pair
        (((Nat.Primrec.left.comp Nat.Primrec.right).pair Nat.Primrec.left).pair
          (Nat.Primrec.const P.masterIdx)))).of_eq (fun u => ?_)
    simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
  have hRHS : Nat.Primrec (fun u : ℕ =>
      iterIdx P (iterIdx (iterPresentation P) u.unpair.2.unpair.2.unpair.2 u.unpair.2.unpair.1)
        u.unpair.1) := by
    have hinner : Nat.Primrec (fun u : ℕ =>
        iterIdx (iterPresentation P) u.unpair.2.unpair.2.unpair.2 u.unpair.2.unpair.1) := by
      refine (primrec_nthCode.comp
        ((Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)).pair
          ((Nat.Primrec.left.comp Nat.Primrec.right).pair
            (Nat.Primrec.const (iterPresentation P).masterIdx)))).of_eq (fun u => ?_)
      simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
    refine (primrec_nthCode.comp
      (hinner.pair (Nat.Primrec.left.pair (Nat.Primrec.const P.masterIdx)))).of_eq (fun u => ?_)
    simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
  have hp₂ : RecDecidable (fun u : ℕ =>
      P.X (iterIdx P u.unpair.2.unpair.2.unpair.1 (Nat.pair u.unpair.2.unpair.1 u.unpair.1))
        ⊆ P.X (iterIdx P (iterIdx (iterPresentation P) u.unpair.2.unpair.2.unpair.2
          u.unpair.2.unpair.1) u.unpair.1)) := by
    refine RecDecidable.of_iff (fun u => ?_) (P.incl_computable.comp (hLHS.pair hRHS))
    simp only [unpair_pair_fst, unpair_pair_snd]
  -- inner bound `bound₂ v = iterIdx (iterᴾ) m i`, with `v = ⟨i, ⟨n, m⟩⟩`
  have hbound₂ : Nat.Primrec (fun v : ℕ =>
      iterIdx (iterPresentation P) v.unpair.2.unpair.2 v.unpair.1) := by
    refine (primrec_nthCode.comp
      ((Nat.Primrec.right.comp Nat.Primrec.right).pair
        (Nat.Primrec.left.pair (Nat.Primrec.const (iterPresentation P).masterIdx)))).of_eq
      (fun v => ?_)
    simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
  have hbound₁ : Nat.Primrec (fun t : ℕ => t.unpair.2) := Nat.Primrec.right
  have hp₁ := hp₂.bForall hbound₂
  have hp₀ := hp₁.bForall hbound₁
  refine (RecDecidable.of_iff (fun t => ?_) hp₀).re
  -- match the relation with the nested bounded `∀`
  simp only [iterPresentation_X, unpair_pair_fst, unpair_pair_snd]
  exact Fmap_rel_enum_iff t.unpair.1 t.unpair.2

/-- **`G` is computable** (in fact recursively decidable): a single bounded `∀` of `incl_computable`. -/
theorem Gmap_isComputable :
    IsComputableMap (iterPresentation (iterPresentation P)) (iterPresentation P) (Gmap V) := by
  -- inner predicate `p₂ u`, with `u = ⟨k, ⟨s, n⟩⟩`
  have hLHS : Nat.Primrec (fun u : ℕ =>
      iterIdx P (iterIdx (iterPresentation P) u.unpair.2.unpair.1 u.unpair.1.unpair.1)
        u.unpair.1.unpair.2) := by
    have hinner : Nat.Primrec (fun u : ℕ =>
        iterIdx (iterPresentation P) u.unpair.2.unpair.1 u.unpair.1.unpair.1) := by
      refine (primrec_nthCode.comp
        ((Nat.Primrec.left.comp Nat.Primrec.right).pair
          ((Nat.Primrec.left.comp Nat.Primrec.left).pair
            (Nat.Primrec.const (iterPresentation P).masterIdx)))).of_eq (fun u => ?_)
      simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
    refine (primrec_nthCode.comp
      (hinner.pair ((Nat.Primrec.right.comp Nat.Primrec.left).pair
        (Nat.Primrec.const P.masterIdx)))).of_eq (fun u => ?_)
    simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
  have hRHS : Nat.Primrec (fun u : ℕ =>
      iterIdx P u.unpair.2.unpair.2 u.unpair.1) := by
    refine (primrec_nthCode.comp
      ((Nat.Primrec.right.comp Nat.Primrec.right).pair
        (Nat.Primrec.left.pair (Nat.Primrec.const P.masterIdx)))).of_eq (fun u => ?_)
    simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]
  have hp₂ : RecDecidable (fun u : ℕ =>
      P.X (iterIdx P (iterIdx (iterPresentation P) u.unpair.2.unpair.1 u.unpair.1.unpair.1)
        u.unpair.1.unpair.2) ⊆ P.X (iterIdx P u.unpair.2.unpair.2 u.unpair.1)) := by
    refine RecDecidable.of_iff (fun u => ?_) (P.incl_computable.comp (hLHS.pair hRHS))
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hbound₁ : Nat.Primrec (fun t : ℕ => t.unpair.2) := Nat.Primrec.right
  have hp₀ := hp₂.bForall hbound₁
  refine (RecDecidable.of_iff (fun t => ?_) hp₀).re
  simp only [iterPresentation_X, unpair_pair_fst, unpair_pair_snd]
  exact Gmap_rel_enum_iff t.unpair.1 t.unpair.2

/-! ### Packaging: the effective isomorphism. -/

/-- **Exercise 7.18 (Scott 1981, PRG-19) — `D^∞ ≅ (D^∞)^∞` is an *effective* isomorphism.** Relative
to `iterPresentation P` and `iterPresentation (iterPresentation P)`, the reindexing maps `F`, `G` are
mutually inverse computable approximable maps. -/
def iterIterEffectiveIso (P : ComputablePresentation V) :
    EffectiveIso (iterPresentation P) (iterPresentation (iterPresentation P)) where
  toMap := Fmap V
  invMap := Gmap V
  toMap_computable := Fmap_isComputable
  invMap_computable := Gmap_isComputable
  left_inv := Gmap_comp_Fmap
  right_inv := Fmap_comp_Gmap

/-- **Exercise 7.18 (Scott 1981, PRG-19).** If `D` is effectively given then `D^∞ ≅ (D^∞)^∞` is
effective. -/
theorem iterSys_effectivelyIsomorphic_iterIter (P : ComputablePresentation V) :
    EffectivelyIsomorphic (iterPresentation P) (iterPresentation (iterPresentation P)) :=
  ⟨iterIterEffectiveIso P⟩

/-- As a corollary, `D^∞ ≅ (D^∞)^∞` as domains (Scott's underlying isomorphism). -/
theorem iterSys_isomorphic_iterIter (P : ComputablePresentation V) :
    iterSys V ≅ᴰ iterSys (iterSys V) :=
  (iterSys_effectivelyIsomorphic_iterIter P).isomorphic

end Exercise718
end Scott1980.Neighborhood

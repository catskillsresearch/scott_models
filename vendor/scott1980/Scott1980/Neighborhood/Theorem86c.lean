/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Theorem86
import Scott1980.Neighborhood.Theorem76

/-!
# Theorem 8.6(c) (Scott 1981, PRG-19, Lecture VIII) — `sub` is computable

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Theorem 8.6's
third clause: *"If `E` is effectively given, then `sub` is computable."* Here "`sub`" means the
combinator packaged as an approximable map on the function space (`Sub8_6.subApprox : ApproximableMap
(funSpace E E) (funSpace E E)`, Theorem 8.6(b)(i)), and "computable" is relative to the
function-space presentation that Theorem 7.5 builds out of any presentation of `E`.

## Strategy (choice-free), mirroring Theorem 7.6's `fixMap_isComputable`

`subApprox` was built via Exercise 2.13's `ofContinuous`, so its neighbourhood relation unfolds
(via `ofMono`) to: `subApprox.rel F G ↔ ∃ hF : (funSpace E E).mem F, sub (toApproxMap (↑F)).mem
G`-ish, i.e. (using `toFilter`'s definition) `F subApprox G` holds iff `sub` of `F`'s least map lies
*in* `G` as a literal set of approximable maps (`subApprox_rel_iff`). Specializing `F = Xenum n`,
`G = Xenum m` (Theorem 7.5's enumeration) and unfolding membership via `mem_Xenum_iff_map`:

`(Xenum n) subApprox (Xenum m)` iff, for every coded step `⟨X_{e.1}, X_{e.2}⟩` of (consistent)
`Xenum m`, `sub(ĝₙ)` relates `X_{e.1}` to `X_{e.2}`, where `ĝₙ = toApproxMap(↑(Xenum n))` is
`Xenum n`'s least map (Theorem 7.6's `leastMap_Xenum_rel`).

`sub`'s own formula (`sub_rel`) turns this into an *existential* over a witness neighbourhood `Y`
with `ĝₙ.rel Y Y`; `P.surj` lets `Y` range over presentation indices `y`, and — crucially —
`ĝₙ.rel (X_y) (X_y) ↔ Xenum n ⊆ Xenum (codePair y y)` (Theorem 7.6) is **recursively decidable** via
the function-space presentation's own `incl_computable`. So the whole relation is a *finite*
conjunction (bounded `∀` over the coded list `decodeList m`, guarded by the decidable consistency
flag `gN m = 1`) of an *unbounded* existential (`∃ y`) of a decidable predicate — hence
recursively enumerable, exactly like Theorem 7.6's `fix`. Unlike `fix`, there is no need for a
*chain*: a single witness index `y` suffices (Scott's formula for `sub` has one existential, not an
iterated fixed-point search), so this file is comparably shorter than `Theorem76.lean`.

Everything here is **choice-free** (`⊆ {propext, Quot.sound}`): the search predicate and its
decidability are all built from `RecDecidable`/`REPred` closure lemmas over concrete primitive
recursive characteristic functions, exactly as in `Theorem75.lean`/`Theorem76.lean`.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap Sub8_6

variable {α : Type*} {E : NeighborhoodSystem α}

/-! ### Unfolding `subApprox`'s neighbourhood relation -/

/-- **`subApprox`'s relation, unfolded via `ofMono`/`ofContinuous`/`toFilter`.** `F subApprox G`
holds iff `G` is a genuine function-space neighbourhood containing `sub` of `F`'s least map (any
witnessing proof `hF` of `F`'s membership works, by proof irrelevance). -/
theorem subApprox_rel_iff {F G : Set (ApproximableMap E E)} (hF : (funSpace E E).mem F) :
    (subApprox (E := E)).rel F G ↔
      (funSpace E E).mem G ∧ sub (toApproxMap ((funSpace E E).principal hF)) ∈ G :=
  ⟨fun ⟨_, hG, hmem⟩ => ⟨hG, hmem⟩, fun ⟨hG, hmem⟩ => ⟨hF, hG, hmem⟩⟩

section SubComputable

variable (P : ComputablePresentation E) (gN : ℕ → ℕ)
  (hgN : ∀ c, gN c = 1 ↔
    (stepFun (funListOf P P (decodeList c)) : Set (ApproximableMap E E)).Nonempty)

/-- **`subApprox`'s relation, specialized to `Xenum`.** `(Xenum n) subApprox (Xenum m)` holds iff,
whenever `m` is consistent, `sub` of `Xenum n`'s least map relates every coded step of `Xenum m`. -/
theorem subApprox_rel_Xenum_iff (n m : ℕ) :
    (subApprox (E := E)).rel (Xenum P P gN n) (Xenum P P gN m) ↔
      gN m = 1 → ∀ e ∈ decodeList m,
        (sub (toApproxMap ((funSpace E E).principal (Xenum_mem P P gN hgN n)))).rel
          (P.X e.unpair.1) (P.X e.unpair.2) := by
  rw [subApprox_rel_iff (Xenum_mem P P gN hgN n), and_iff_right (Xenum_mem P P gN hgN m)]
  exact mem_Xenum_iff_map P P gN _ m

/-- **`sub`'s defining existential, reindexed to presentation indices.** `sub f` relates presented
neighbourhoods `X_a`, `X_b` iff some presented `X_y` witnesses Scott's formula (`P.surj` turns the
arbitrary witness neighbourhood `Y` of `sub_rel` into an index `y`). -/
theorem sub_rel_iff_exists_index {f : ApproximableMap E E} {a b : ℕ} :
    (sub f).rel (P.X a) (P.X b) ↔
      ∃ y : ℕ, f.rel (P.X y) (P.X y) ∧ P.X a ⊆ P.X y ∧ P.X y ⊆ P.X b := by
  rw [sub_rel, and_iff_right (P.mem_X a), and_iff_right (P.mem_X b)]
  constructor
  · rintro ⟨Y, ⟨hYE, hYf⟩, haY, hYb⟩
    obtain ⟨y, rfl⟩ := P.surj hYE
    exact ⟨y, hYf, haY, hYb⟩
  · rintro ⟨y, hYf, haY, hYb⟩
    exact ⟨P.X y, ⟨P.mem_X y, hYf⟩, haY, hYb⟩

/-- **`sub` of `Xenum n`'s least map, in fully decidable-existential form.** Combines
`sub_rel_iff_exists_index` with Theorem 7.6's `leastMap_Xenum_rel`/`Xenum_codePair` to turn the
witness condition `ĝₙ.rel (X_y) (X_y)` into the recursively decidable function-space inclusion
`Xenum n ⊆ Xenum (codePair y y)`. -/
theorem sub_leastMap_rel_iff (n a b : ℕ) :
    (sub (toApproxMap ((funSpace E E).principal (Xenum_mem P P gN hgN n)))).rel
        (P.X a) (P.X b) ↔
      ∃ y : ℕ, Xenum P P gN n ⊆ Xenum P P gN (codePair y y) ∧
        P.X a ⊆ P.X y ∧ P.X y ⊆ P.X b := by
  rw [sub_rel_iff_exists_index P]
  refine exists_congr (fun y => ?_)
  rw [leastMap_Xenum_rel P gN hgN n y y, Xenum_codePair P gN hgN y y]

/-! ### The per-witness decidable predicate and its recursive decidability -/

/-- **The per-witness `sub`-step predicate is recursively decidable**, coded as a function of
`w = ⟨y, ⟨n, e⟩⟩`: the function-space inclusion `Xenum n ⊆ Xenum (codePair y y)` (via `fincl`, the
function-space presentation's own inclusion char) conjoined with the two `𝒟`-inclusions bracketing
`y` (via `incl`, `P`'s own inclusion char). -/
theorem subStep_recDecidable (fincl incl : ℕ → ℕ)
    (hfincl : ∀ s, fincl s = 1 ↔ Xenum P P gN s.unpair.1 ⊆ Xenum P P gN s.unpair.2)
    (hfinclp : Nat.Primrec fincl)
    (hincl : ∀ s, incl s = 1 ↔ P.X s.unpair.1 ⊆ P.X s.unpair.2) (hinclp : Nat.Primrec incl) :
    RecDecidable (fun w : ℕ =>
      Xenum P P gN w.unpair.2.unpair.1 ⊆ Xenum P P gN (codePair w.unpair.1 w.unpair.1) ∧
        P.X w.unpair.2.unpair.2.unpair.1 ⊆ P.X w.unpair.1 ∧
          P.X w.unpair.1 ⊆ P.X w.unpair.2.unpair.2.unpair.2) := by
  have hy : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hn : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have he1 : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have he2 : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hcodeYY : Nat.Primrec (fun w : ℕ => codePair w.unpair.1 w.unpair.1) :=
    Nat.Primrec.succ.comp ((hy.pair hy).pair (Nat.Primrec.const 0))
  have h1 : RecDecidable (fun w : ℕ =>
      Xenum P P gN w.unpair.2.unpair.1 ⊆ Xenum P P gN (codePair w.unpair.1 w.unpair.1)) :=
    ⟨fun w => fincl (Nat.pair w.unpair.2.unpair.1 (codePair w.unpair.1 w.unpair.1)),
      hfinclp.comp (hn.pair hcodeYY), fun w => by
        rw [hfincl]; simp only [unpair_pair_fst, unpair_pair_snd]⟩
  have h2 : RecDecidable (fun w : ℕ => P.X w.unpair.2.unpair.2.unpair.1 ⊆ P.X w.unpair.1) :=
    ⟨fun w => incl (Nat.pair w.unpair.2.unpair.2.unpair.1 w.unpair.1), hinclp.comp (he1.pair hy),
      fun w => by rw [hincl]; simp only [unpair_pair_fst, unpair_pair_snd]⟩
  have h3 : RecDecidable (fun w : ℕ => P.X w.unpair.1 ⊆ P.X w.unpair.2.unpair.2.unpair.2) :=
    ⟨fun w => incl (Nat.pair w.unpair.1 w.unpair.2.unpair.2.unpair.2), hinclp.comp (hy.pair he2),
      fun w => by rw [hincl]; simp only [unpair_pair_fst, unpair_pair_snd]⟩
  exact h1.and (h2.and h3)

/-- **Theorem 8.6(c) (Scott 1981, PRG-19), as an `IsComputableMap` statement.** Relative to the
function-space presentation `funPresentation P P …` (Theorem 7.5) built from any presentation `P` of
`E`, `subApprox` is computable: its neighbourhood relation is the recursively enumerable
`¬(consistent m) ∨ ∀ e ∈ decodeList m, ∃ y, …` (a bounded `∀` of an unbounded `∃` of a decidable
predicate). -/
theorem subApprox_isComputable
    (incl eq : ℕ → ℕ)
    (hgNp : Nat.Primrec gN)
    (hincl : ∀ s, incl s = 1 ↔ P.X s.unpair.1 ⊆ P.X s.unpair.2) (hinclp : Nat.Primrec incl)
    (heq : ∀ s, eq s = 1 ↔ P.X s.unpair.1 = P.X s.unpair.2) (heqp : Nat.Primrec eq) :
    IsComputableMap
      (funPresentation P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp heq heqp)
      (funPresentation P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp heq heqp)
      (subApprox (E := E)) := by
  obtain ⟨fincl, hfinclp, hfincls⟩ :=
    (funPresentation P P gN incl incl eq hgN hgNp hincl hinclp hincl hinclp heq heqp).incl_computable
  have hfincl : ∀ s, fincl s = 1 ↔ Xenum P P gN s.unpair.1 ⊆ Xenum P P gN s.unpair.2 :=
    fun s => (hfincls s).symm
  show REPred₂ (fun n m => (subApprox (E := E)).rel (Xenum P P gN n) (Xenum P P gN m))
  have hdec := subStep_recDecidable P gN fincl incl hfincl hfinclp hincl hinclp
  have hre : REPred₂ (fun n e => ∃ y : ℕ,
      Xenum P P gN n ⊆ Xenum P P gN (codePair y y) ∧
        P.X e.unpair.1 ⊆ P.X y ∧ P.X y ⊆ P.X e.unpair.2) := by
    refine REPred.of_iff (fun t => ?_) hdec.re.proj
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hforall : REPred (fun t => ∀ e ∈ decodeList t.unpair.2, ∃ y : ℕ,
      Xenum P P gN t.unpair.1 ⊆ Xenum P P gN (codePair y y) ∧
        P.X e.unpair.1 ⊆ P.X y ∧ P.X y ⊆ P.X e.unpair.2) :=
    REPred.forall_mem_decodeList₂ hre
  have hne1 : REPred (fun t => ¬ gN t.unpair.2 = 1) :=
    ((RecDecidable.natEq (hgNp.comp Nat.Primrec.right) (Nat.Primrec.const 1)).not).re
  refine REPred.of_iff (fun t => ?_) (hne1.or hforall)
  show (subApprox (E := E)).rel (Xenum P P gN t.unpair.1) (Xenum P P gN t.unpair.2) ↔ _
  rw [subApprox_rel_Xenum_iff P gN hgN t.unpair.1 t.unpair.2, Decidable.imp_iff_not_or]
  refine or_congr_right (forall_congr' (fun e => imp_congr_right (fun _ => ?_)))
  exact sub_leastMap_rel_iff P gN hgN t.unpair.1 e.unpair.1 e.unpair.2

end SubComputable

/-- **Theorem 8.6(c) (Scott 1981, PRG-19), in full: "If `E` is effectively given, then `sub` is
computable."** Packages `subApprox_isComputable` with the function-space presentation that Theorem
7.5 (`funSpace_isEffectivelyGiven`'s construction, `funPresentation`) builds out of any computable
presentation of `E`. -/
theorem sub_isComputable_of_isEffectivelyGiven (h : E.IsEffectivelyGiven) :
    ∃ Pfun : ComputablePresentation (funSpace E E),
      IsComputableMap Pfun Pfun (subApprox (E := E)) := by
  obtain ⟨P⟩ := h
  obtain ⟨incl, hinclp, hincls⟩ := P.incl_computable
  obtain ⟨eq, heqp, heqs⟩ := P.eq_computable
  obtain ⟨fc, hfcp, hfcs⟩ := P.cons_computable
  have hincl' : ∀ s, incl s = 1 ↔ P.X s.unpair.1 ⊆ P.X s.unpair.2 := fun s => (hincls s).symm
  have heq' : ∀ s, eq s = 1 ↔ P.X s.unpair.1 = P.X s.unpair.2 := fun s => (heqs s).symm
  have hgN : ∀ c, funConsChar P P fc fc c = 1 ↔
      (stepFun (funListOf P P (decodeList c)) : Set (ApproximableMap E E)).Nonempty :=
    fun c => funConsChar_spec P P fc fc (fun s => (hfcs s).symm) (fun s => (hfcs s).symm) c
  refine ⟨funPresentation P P (funConsChar P P fc fc) incl incl eq hgN
    (primrec_funConsChar P P fc fc hfcp hfcp) hincl' hinclp hincl' hinclp heq' heqp,
    subApprox_isComputable P (funConsChar P P fc fc) hgN incl eq
      (primrec_funConsChar P P fc fc hfcp hfcp) hincl' hinclp heq' heqp⟩

end Scott1980.Neighborhood

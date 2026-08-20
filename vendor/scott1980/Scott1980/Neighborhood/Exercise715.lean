/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Theorem74
import Scott1980.Neighborhood.Exercise510
import Scott1980.Neighborhood.Exercise316

/-!
# Exercise 7.15 (Scott 1981, PRG-19, §7) — effective givenness of `⊗`, `⊕`, `D^∞`

> **EXERCISE 7.15.** Finish the proof of 7.4 and establish similar results for the constructs
> `(D₀ ⊗ D₁)`, `(D₀ ⊕ D₁)` and `D^∞`. Take into account the various appropriate combinators.

Theorem 7.4 (the separated `+` and `×`) is already complete in `Theorem74.lean`, with all
combinators (`projᵢ`, `inᵢ`, `outᵢ`, `⟨f,g⟩`, `f×g`, `f+g`). This file establishes the analogous
results for the three remaining constructs.

## Scott's bare Definition 7.1 vs. the project's "acceptable" presentation

The **smash product** `⊗` and the **coalesced sum** `⊕` *delete the improper tagged copies*
(`0Δ₀`, `1Δ₁`) and re-route them to the master — this is the bottom-collapse that distinguishes them
from the separated `×`/`+`. That re-routing has a sharp consequence for *effective* presentations:

> A primitive-recursive intersection function `inter` (as carried by the project's
> `ComputablePresentation`) **cannot exist** for `⊗`/`⊕`. Concretely, take `a` proper and `b`
> "secretly the master" because one factor is improper while the other is a *V₀-inconsistent* proper
> neighbourhood. Then `(a,b)` is consistent (their intersection is a genuine member), so `inter`
> would have to *detect that `b` is secretly the master* — i.e. decide properness (`Xb = Δ₀`?), a
> recursively decidable but **not primitive-recursive** set-equality test.

Scott's actual **Definition 7.1** only asks that the two relations (i) `Xₙ ∩ Xₘ = X_k` and (ii)
consistency `∃k. X_k ⊆ Xₙ ∩ Xₘ` be *recursively decidable*; it does **not** require a primrec
`inter` (that is a project strengthening, needed only for the function space, Theorem 7.5). So we
introduce Scott's literal notion as `ScottPresentation` and prove `⊗`/`⊕` effectively given with
respect to it. Both of (i),(ii) *are* recursively decidable for `⊗`/`⊕` — they reduce to boolean
combinations of the components' relations together with the (recursively decidable) properness tests.

**Choice discipline.** `ScottPresentation` and the `D^∞` results are choice-free. For `⊗`/`⊕` the
*only* classical input is the **enumeration** `X`, which must branch on the (set-equality) properness
test; we localise `Classical.choice` to that one field (`smashEnum`/`osumEnum`). The recursively
decidable relations (i),(ii) are proved **choice-free** by destructuring the components' deciders.

`D^∞ = iterSys D` (Exercise 3.16) is *uniform* (every cylinder is a genuine member, no deletion), so
it admits a full `ComputablePresentation` and is treated choice-free in the existing interface, with
the coordinate-projection combinators `projN`/`head` computable.
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}

/-! ## Scott's bare presentation (Definition 7.1, no primitive-recursive `inter`)

This is the literal content of Definition 7.1: an enumeration with the two relations recursively
decidable. It is exactly `ComputablePresentation` minus the `inter`/`masterIdx` data fields. -/

/-- **Scott's Definition 7.1 (literal).** A *bare* computable presentation: an enumeration
`X : ℕ → Set α` onto `𝒟`, with relations (i) `Xₙ ∩ Xₘ = X_k` and (ii) consistency recursively
decidable. No primitive-recursive intersection function is carried (cf. the docstring above). -/
structure ScottPresentation (V : NeighborhoodSystem α) where
  /-- The enumeration `𝒟 = {Xₙ ∣ n ∈ ℕ}`. -/
  X : ℕ → Set α
  /-- Every `Xₙ` is a neighbourhood. -/
  mem_X : ∀ n, V.mem (X n)
  /-- The enumeration is onto `𝒟`. -/
  surj : ∀ {Y : Set α}, V.mem Y → ∃ n, X n = Y
  /-- **7.1(i)** `Xₙ ∩ Xₘ = X_k` recursively decidable. -/
  interEq_computable : RecDecidable₃ (fun n m k => X n ∩ X m = X k)
  /-- **7.1(ii)** consistency `∃k. X_k ⊆ Xₙ ∩ Xₘ` recursively decidable. -/
  cons_computable : RecDecidable₂ (fun n m => ∃ k, X k ⊆ X n ∩ X m)

namespace ScottPresentation

variable {V : NeighborhoodSystem α} (P : ScottPresentation V)

/-- Reindexing `(n, m) ↦ (n, m, n)`. -/
private def inclShuffle (t : ℕ) : ℕ := Nat.pair t.unpair.1 (Nat.pair t.unpair.2 t.unpair.1)

private theorem primrec_inclShuffle : Nat.Primrec inclShuffle :=
  Nat.Primrec.pair Nat.Primrec.left (Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left)

private def swapPair (t : ℕ) : ℕ := Nat.pair t.unpair.2 t.unpair.1

private theorem primrec_swapPair : Nat.Primrec swapPair :=
  Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left

/-- The inclusion relation is decidable: `Xₙ ⊆ Xₘ ↔ Xₙ ∩ Xₘ = Xₙ`. -/
theorem incl_computable : RecDecidable₂ (fun n m => P.X n ⊆ P.X m) := by
  refine RecDecidable.of_iff (fun t => ?_) (P.interEq_computable.comp primrec_inclShuffle)
  simp only [inclShuffle, unpair_pair_fst, unpair_pair_snd]
  exact Set.inter_eq_left.symm

/-- Equality of neighbourhoods is decidable. -/
theorem eq_computable : RecDecidable₂ (fun n m => P.X n = P.X m) := by
  refine RecDecidable.of_iff (fun t => ?_)
    (P.incl_computable.and (P.incl_computable.comp primrec_swapPair))
  simp only [swapPair, unpair_pair_fst, unpair_pair_snd]
  exact Set.Subset.antisymm_iff

end ScottPresentation

/-- **Effectively given (Scott's literal Definition 7.1).** -/
def NeighborhoodSystem.IsEffectivelyGivenS (V : NeighborhoodSystem α) : Prop :=
  Nonempty (ScottPresentation V)

/-- A full (`inter`-carrying) presentation forgets to a bare one. Hence the project's
`IsEffectivelyGiven` implies Scott's `IsEffectivelyGivenS`. -/
def ComputablePresentation.toScott {V : NeighborhoodSystem α} (P : ComputablePresentation V) :
    ScottPresentation V where
  X := P.X
  mem_X := P.mem_X
  surj := P.surj
  interEq_computable := P.interEq_computable
  cons_computable := P.cons_computable

theorem NeighborhoodSystem.IsEffectivelyGiven.toS {V : NeighborhoodSystem α}
    (h : V.IsEffectivelyGiven) : V.IsEffectivelyGivenS :=
  h.elim fun P => ⟨P.toScott⟩

/-- **Definition 7.2 relative to bare presentations.** A computable map between bare presentations is
one whose neighbourhood relation `Xₙ f Yₘ` is r.e. (identical to `IsComputableMap`, which only uses
the enumerations). -/
def IsComputableMapS {V : NeighborhoodSystem α} {W : NeighborhoodSystem β}
    (P : ScottPresentation V) (Q : ScottPresentation W) (f : ApproximableMap V W) : Prop :=
  REPred₂ (fun n m => f.rel (P.X n) (Q.X m))

/-! ## The smash product `𝒟₀ ⊗ 𝒟₁` is effectively given (Scott's Definition 7.1)

`smash V₀ V₁` (`Exercise510.lean`) over `α ⊕ β` has neighbourhoods the master `prodNbhd Δ₀ Δ₁`
together with the *proper* products `prodNbhd X Y` (`X ≠ Δ₀`, `Y ≠ Δ₁`). We enumerate it by pairs of
component indices, re-routing improper pairs to the master. The re-routing is the only classical
input (it branches on the set-equality `Xₙ = Δ₀?`). The two relations (i),(ii) are choice-free
recursively decidable. -/

open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

open scoped Classical in
/-- **Smash enumeration.** Index `t ↦` the proper product `prodNbhd X⁰_{t.1} X¹_{t.2}` when both
factors are proper, otherwise the master. The classical `if` (deciding `Xₙ = Δ₀`) is the *only*
classical input of the smash presentation. -/
noncomputable def smashEnum (t : ℕ) : Set (α ⊕ β) :=
  if P₀.X t.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.2 ≠ V₁.master then
    prodNbhd (P₀.X t.unpair.1) (P₁.X t.unpair.2)
  else prodNbhd V₀.master V₁.master

variable {P₀ P₁}

open scoped Classical in
theorem smashEnum_proper {t : ℕ}
    (h : P₀.X t.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.2 ≠ V₁.master) :
    smashEnum P₀ P₁ t = prodNbhd (P₀.X t.unpair.1) (P₁.X t.unpair.2) := if_pos h

open scoped Classical in
theorem smashEnum_master {t : ℕ}
    (h : ¬(P₀.X t.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.2 ≠ V₁.master)) :
    smashEnum P₀ P₁ t = prodNbhd V₀.master V₁.master := if_neg h

theorem smashEnum_mem (t : ℕ) : (smash V₀ V₁).mem (smashEnum P₀ P₁ t) := by
  by_cases h : P₀.X t.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.2 ≠ V₁.master
  · rw [smashEnum_proper h]; exact smash_mem_proper (P₀.mem_X _) h.1 (P₁.mem_X _) h.2
  · rw [smashEnum_master h]; exact (smash V₀ V₁).master_mem

theorem smashEnum_subset_master (k : ℕ) :
    smashEnum P₀ P₁ k ⊆ prodNbhd V₀.master V₁.master := by
  have h := (smash V₀ V₁).sub_master (smashEnum_mem (P₀ := P₀) (P₁ := P₁) k)
  rwa [smash_master] at h

/-- Every enumerated smash neighbourhood is a product `prodNbhd A B` of component neighbourhoods
(the proper form, or the master `prodNbhd Δ₀ Δ₁`). -/
theorem smashEnum_eq_prodNbhd_mem (k : ℕ) :
    ∃ A B, V₀.mem A ∧ V₁.mem B ∧ smashEnum P₀ P₁ k = prodNbhd A B := by
  by_cases h : P₀.X k.unpair.1 ≠ V₀.master ∧ P₁.X k.unpair.2 ≠ V₁.master
  · exact ⟨_, _, P₀.mem_X _, P₁.mem_X _, smashEnum_proper h⟩
  · exact ⟨_, _, V₀.master_mem, V₁.master_mem, smashEnum_master h⟩

/-- **The smash enumeration as a product neighbourhood with *effective* factors.** Given `{0,1}`
deciders `c₀`, `c₁` of properness, `smashEnum t = prodNbhd X⁰_{effL} X¹_{effR}` where the effective
index `effL = (proper? t.1 : masterIdx₀)` is computed primitively by `selectFn`. This is the bridge
that turns the smash relations into the components' relations on the effective indices. -/
theorem smashEnum_eq_eff {c₀ c₁ : ℕ → ℕ} (hc₀le : ∀ n, c₀ n ≤ 1) (hc₁le : ∀ n, c₁ n ≤ 1)
    (hc₀ : ∀ n, P₀.X n ≠ V₀.master ↔ c₀ n = 1) (hc₁ : ∀ n, P₁.X n ≠ V₁.master ↔ c₁ n = 1) (t : ℕ) :
    smashEnum P₀ P₁ t =
      prodNbhd (P₀.X (selectFn (c₀ t.unpair.1 * c₁ t.unpair.2) t.unpair.1 P₀.masterIdx))
        (P₁.X (selectFn (c₀ t.unpair.1 * c₁ t.unpair.2) t.unpair.2 P₁.masterIdx)) := by
  by_cases h : P₀.X t.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.2 ≠ V₁.master
  · have e0 : c₀ t.unpair.1 = 1 := (hc₀ _).mp h.1
    have e1 : c₁ t.unpair.2 = 1 := (hc₁ _).mp h.2
    rw [smashEnum_proper h, e0, e1, mul_one, selectFn_one, selectFn_one]
  · rw [smashEnum_master h]
    have hpf : c₀ t.unpair.1 * c₁ t.unpair.2 = 0 := by
      rcases not_and_or.mp h with h0 | h1
      · have hz : c₀ t.unpair.1 = 0 := by
          have hle := hc₀le t.unpair.1
          rcases (show c₀ t.unpair.1 = 0 ∨ c₀ t.unpair.1 = 1 by omega) with h | h
          · exact h
          · exact absurd ((hc₀ _).mpr h) h0
        rw [hz, Nat.zero_mul]
      · have hz : c₁ t.unpair.2 = 0 := by
          have hle := hc₁le t.unpair.2
          rcases (show c₁ t.unpair.2 = 0 ∨ c₁ t.unpair.2 = 1 by omega) with h | h
          · exact h
          · exact absurd ((hc₁ _).mpr h) h1
        rw [hz, Nat.mul_zero]
    rw [hpf, selectFn_zero, selectFn_zero, P₀.masterIdx_spec, P₁.masterIdx_spec]

variable (P₀ P₁)

/-- The properness predicate `Xₙ ≠ Δ₀` is recursively decidable (negation of `eq_computable`
against the master index). -/
theorem proper₀_dec : RecDecidable (fun n => P₀.X n ≠ V₀.master) := by
  have heq : RecDecidable (fun n => P₀.X n = V₀.master) := by
    refine RecDecidable.of_iff (fun n => ?_)
      (P₀.eq_computable.comp (primrec_id.pair (Nat.Primrec.const P₀.masterIdx)))
    simp only [unpair_pair_fst, unpair_pair_snd, P₀.masterIdx_spec, id_eq]
  exact heq.not

theorem proper₁_dec : RecDecidable (fun n => P₁.X n ≠ V₁.master) := by
  have heq : RecDecidable (fun n => P₁.X n = V₁.master) := by
    refine RecDecidable.of_iff (fun n => ?_)
      (P₁.eq_computable.comp (primrec_id.pair (Nat.Primrec.const P₁.masterIdx)))
    simp only [unpair_pair_fst, unpair_pair_snd, P₁.masterIdx_spec, id_eq]
  exact heq.not

/-- **Exercise 7.15 — `𝒟₀ ⊗ 𝒟₁` is effectively given (Scott's Definition 7.1).** A bare presentation
of the smash product. The enumeration is classical (re-routing improper products to the master); the
two relations (i),(ii) are choice-free recursively decidable, reducing to the components' relations
on the *effective* indices (relation (i)) and the components' consistency together with properness
tests (relation (ii)). -/
noncomputable def smashPresentation : ScottPresentation (smash V₀ V₁) where
  X := smashEnum P₀ P₁
  mem_X := smashEnum_mem
  surj := by
    rintro Z (rfl | ⟨X, Y, hX, hXne, hY, hYne, rfl⟩)
    · refine ⟨Nat.pair P₀.masterIdx P₁.masterIdx, ?_⟩
      rw [smashEnum_master (by
        rw [unpair_pair_fst, P₀.masterIdx_spec]; exact fun h => h.1 rfl)]
    · obtain ⟨n, rfl⟩ := P₀.surj hX
      obtain ⟨m, rfl⟩ := P₁.surj hY
      refine ⟨Nat.pair n m, ?_⟩
      rw [smashEnum_proper (by rw [unpair_pair_fst, unpair_pair_snd]; exact ⟨hXne, hYne⟩),
        unpair_pair_fst, unpair_pair_snd]
  interEq_computable := by
    obtain ⟨f₀, hf₀p, hf₀e⟩ := proper₀_dec P₀
    obtain ⟨f₁, hf₁p, hf₁e⟩ := proper₁_dec P₁
    set c₀ := fun n => isOne (f₀ n) with hc₀def
    set c₁ := fun n => isOne (f₁ n) with hc₁def
    have hc₀le : ∀ n, c₀ n ≤ 1 := fun n => isOne_le_one _
    have hc₁le : ∀ n, c₁ n ≤ 1 := fun n => isOne_le_one _
    have hc₀ : ∀ n, P₀.X n ≠ V₀.master ↔ c₀ n = 1 := fun n => by
      rw [hc₀def, isOne_eq_one_iff]; exact hf₀e n
    have hc₁ : ∀ n, P₁.X n ≠ V₁.master ↔ c₁ n = 1 := fun n => by
      rw [hc₁def, isOne_eq_one_iff]; exact hf₁e n
    have hc₀p : Nat.Primrec c₀ := primrec_isOne.comp hf₀p
    have hc₁p : Nat.Primrec c₁ := primrec_isOne.comp hf₁p
    have hpf : Nat.Primrec (fun n => c₀ n.unpair.1 * c₁ n.unpair.2) :=
      (primrec_mul.comp ((hc₀p.comp Nat.Primrec.left).pair (hc₁p.comp Nat.Primrec.right))).of_eq
        (fun n => by simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd])
    -- effective left/right index of a single code `n`
    have heffLp : Nat.Primrec (fun n => selectFn (c₀ n.unpair.1 * c₁ n.unpair.2)
        n.unpair.1 P₀.masterIdx) :=
      primrec_selectFn hpf Nat.Primrec.left (Nat.Primrec.const _)
    have heffRp : Nat.Primrec (fun n => selectFn (c₀ n.unpair.1 * c₁ n.unpair.2)
        n.unpair.2 P₁.masterIdx) :=
      primrec_selectFn hpf Nat.Primrec.right (Nat.Primrec.const _)
    -- reindexings `t ↦ pair (effL t.1) (pair (effL t.2.1) (effL t.2.2))`, ditto for the right factor
    have hgL : Nat.Primrec (fun t => Nat.pair
        (selectFn (c₀ t.unpair.1.unpair.1 * c₁ t.unpair.1.unpair.2) t.unpair.1.unpair.1 P₀.masterIdx)
        (Nat.pair
          (selectFn (c₀ t.unpair.2.unpair.1.unpair.1 * c₁ t.unpair.2.unpair.1.unpair.2)
            t.unpair.2.unpair.1.unpair.1 P₀.masterIdx)
          (selectFn (c₀ t.unpair.2.unpair.2.unpair.1 * c₁ t.unpair.2.unpair.2.unpair.2)
            t.unpair.2.unpair.2.unpair.1 P₀.masterIdx))) :=
      (heffLp.comp Nat.Primrec.left).pair
        ((heffLp.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
          (heffLp.comp (Nat.Primrec.right.comp Nat.Primrec.right)))
    have hgR : Nat.Primrec (fun t => Nat.pair
        (selectFn (c₀ t.unpair.1.unpair.1 * c₁ t.unpair.1.unpair.2) t.unpair.1.unpair.2 P₁.masterIdx)
        (Nat.pair
          (selectFn (c₀ t.unpair.2.unpair.1.unpair.1 * c₁ t.unpair.2.unpair.1.unpair.2)
            t.unpair.2.unpair.1.unpair.2 P₁.masterIdx)
          (selectFn (c₀ t.unpair.2.unpair.2.unpair.1 * c₁ t.unpair.2.unpair.2.unpair.2)
            t.unpair.2.unpair.2.unpair.2 P₁.masterIdx))) :=
      (heffRp.comp Nat.Primrec.left).pair
        ((heffRp.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
          (heffRp.comp (Nat.Primrec.right.comp Nat.Primrec.right)))
    refine RecDecidable.of_iff (fun t => ?_)
      ((P₀.interEq_computable.comp hgL).and (P₁.interEq_computable.comp hgR))
    dsimp only
    simp only [unpair_pair_fst, unpair_pair_snd]
    rw [smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁, smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁,
      smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁, prodNbhd_inter, prodNbhd_eq_iff]
  cons_computable := by
    obtain ⟨f₀, hf₀p, hf₀e⟩ := proper₀_dec P₀
    obtain ⟨f₁, hf₁p, hf₁e⟩ := proper₁_dec P₁
    -- `cons(a,b) ↔ ¬proper a ∨ ¬proper b ∨ (P₀.cons(a.1,b.1) ∧ P₁.cons(a.2,b.2))`
    have hpa : RecDecidable (fun t => ¬(P₀.X t.unpair.1.unpair.1 ≠ V₀.master
        ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master)) := by
      have h0 : RecDecidable (fun t => P₀.X t.unpair.1.unpair.1 ≠ V₀.master) :=
        (proper₀_dec P₀).comp (Nat.Primrec.left.comp Nat.Primrec.left)
      have h1 : RecDecidable (fun t => P₁.X t.unpair.1.unpair.2 ≠ V₁.master) :=
        (proper₁_dec P₁).comp (Nat.Primrec.right.comp Nat.Primrec.left)
      exact (h0.and h1).not
    have hpb : RecDecidable (fun t => ¬(P₀.X t.unpair.2.unpair.1 ≠ V₀.master
        ∧ P₁.X t.unpair.2.unpair.2 ≠ V₁.master)) := by
      have h0 : RecDecidable (fun t => P₀.X t.unpair.2.unpair.1 ≠ V₀.master) :=
        (proper₀_dec P₀).comp (Nat.Primrec.left.comp Nat.Primrec.right)
      have h1 : RecDecidable (fun t => P₁.X t.unpair.2.unpair.2 ≠ V₁.master) :=
        (proper₁_dec P₁).comp (Nat.Primrec.right.comp Nat.Primrec.right)
      exact (h0.and h1).not
    have hcons0 : RecDecidable (fun t => ∃ k, P₀.X k ⊆ P₀.X t.unpair.1.unpair.1
        ∩ P₀.X t.unpair.2.unpair.1) := by
      refine RecDecidable.of_iff (fun t => ?_) (P₀.cons_computable.comp
        ((Nat.Primrec.left.comp Nat.Primrec.left).pair (Nat.Primrec.left.comp Nat.Primrec.right)))
      simp only [unpair_pair_fst, unpair_pair_snd]
    have hcons1 : RecDecidable (fun t => ∃ k, P₁.X k ⊆ P₁.X t.unpair.1.unpair.2
        ∩ P₁.X t.unpair.2.unpair.2) := by
      refine RecDecidable.of_iff (fun t => ?_) (P₁.cons_computable.comp
        ((Nat.Primrec.right.comp Nat.Primrec.left).pair (Nat.Primrec.right.comp Nat.Primrec.right)))
      simp only [unpair_pair_fst, unpair_pair_snd]
    refine RecDecidable.of_iff (fun t => ?_) (hpa.or (hpb.or (hcons0.and hcons1)))
    constructor
    · rintro ⟨k, hk⟩
      by_cases hpa' : P₀.X t.unpair.1.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master
      · by_cases hpb' : P₀.X t.unpair.2.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.2.unpair.2 ≠ V₁.master
        · refine Or.inr (Or.inr ⟨?_, ?_⟩)
          · rw [smashEnum_proper hpa', smashEnum_proper hpb', prodNbhd_inter] at hk
            obtain ⟨A, B, hA, _, hkeq⟩ := smashEnum_eq_prodNbhd_mem (P₀ := P₀) (P₁ := P₁) k
            rw [hkeq] at hk
            obtain ⟨hAsub, _⟩ := prodNbhd_subset_iff.mp hk
            obtain ⟨j₀, hj₀⟩ := P₀.surj hA
            exact ⟨j₀, by rw [hj₀]; exact hAsub⟩
          · rw [smashEnum_proper hpa', smashEnum_proper hpb', prodNbhd_inter] at hk
            obtain ⟨A, B, _, hB, hkeq⟩ := smashEnum_eq_prodNbhd_mem (P₀ := P₀) (P₁ := P₁) k
            rw [hkeq] at hk
            obtain ⟨_, hBsub⟩ := prodNbhd_subset_iff.mp hk
            obtain ⟨j₁, hj₁⟩ := P₁.surj hB
            exact ⟨j₁, by rw [hj₁]; exact hBsub⟩
        · exact Or.inr (Or.inl hpb')
      · exact Or.inl hpa'
    · intro hp
      by_cases hpa' : P₀.X t.unpair.1.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master
      · by_cases hpb' : P₀.X t.unpair.2.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.2.unpair.2 ≠ V₁.master
        · rcases hp with h | h | ⟨⟨j₀, hj₀⟩, ⟨j₁, hj₁⟩⟩
          · exact absurd hpa' h
          · exact absurd hpb' h
          · have hXint : V₀.mem (P₀.X t.unpair.1.unpair.1 ∩ P₀.X t.unpair.2.unpair.1) :=
              V₀.inter_mem (P₀.mem_X _) (P₀.mem_X _) (P₀.mem_X j₀) hj₀
            have hYint : V₁.mem (P₁.X t.unpair.1.unpair.2 ∩ P₁.X t.unpair.2.unpair.2) :=
              V₁.inter_mem (P₁.mem_X _) (P₁.mem_X _) (P₁.mem_X j₁) hj₁
            have hXne : P₀.X t.unpair.1.unpair.1 ∩ P₀.X t.unpair.2.unpair.1 ≠ V₀.master :=
              inter_ne_master_left (P₀.mem_X _) hpa'.1
            have hYne : P₁.X t.unpair.1.unpair.2 ∩ P₁.X t.unpair.2.unpair.2 ≠ V₁.master :=
              inter_ne_master_left (P₁.mem_X _) hpa'.2
            obtain ⟨p₀, hp₀⟩ := P₀.surj hXint
            obtain ⟨p₁, hp₁⟩ := P₁.surj hYint
            refine ⟨Nat.pair p₀ p₁, ?_⟩
            rw [smashEnum_proper (by
                  rw [unpair_pair_fst, unpair_pair_snd, hp₀, hp₁]; exact ⟨hXne, hYne⟩),
              unpair_pair_fst, unpair_pair_snd, hp₀, hp₁, smashEnum_proper hpa',
              smashEnum_proper hpb', prodNbhd_inter]
        · refine ⟨t.unpair.1, ?_⟩
          rw [smashEnum_master (t := t.unpair.2) hpb',
            Set.inter_eq_left.mpr (smashEnum_subset_master t.unpair.1)]
      · refine ⟨t.unpair.2, ?_⟩
        rw [smashEnum_master (t := t.unpair.1) hpa',
          Set.inter_eq_right.mpr (smashEnum_subset_master t.unpair.2)]

/-- **Exercise 7.15 (Scott 1981, PRG-19) — the smash product `𝒟₀ ⊗ 𝒟₁` is effectively given.**
(Scott's Definition 7.1; the only classical input is the enumeration's properness branch.) -/
theorem smash_isEffectivelyGivenS (h₀ : V₀.IsEffectivelyGiven) (h₁ : V₁.IsEffectivelyGiven) :
    (smash V₀ V₁).IsEffectivelyGivenS := by
  obtain ⟨Q₀⟩ := h₀; obtain ⟨Q₁⟩ := h₁
  exact ⟨smashPresentation Q₀ Q₁⟩

@[simp] theorem smashPresentation_X (t : ℕ) :
    (smashPresentation P₀ P₁).X t = smashEnum P₀ P₁ t := rfl

/-! ### Projections and the strict pairing for `⊗` (the `×`-analogue combinators).

The smash product carries the same *projections* `proj₀`/`proj₁` as the separated product (a smash
member is still a product neighbourhood `prodNbhd A B`, and `Sum.inl ⁻¹' (prodNbhd A B) = A`) and a
*strict pairing* `⟨a, b⟩⊗ : 𝒟₂ → 𝒟₀ ⊗ 𝒟₁`. Because the smash deletes the improper products, the
pairing forces *proper* image factors and otherwise lands on the master. All three are computable:
the projections by `smashEnum_eq_eff` + `incl_computable`, the pairing by `a`,`b`'s r.e. relations on
the (raw) codomain coordinate indices together with the codomain properness tests. -/

/-- **The smash projection `p₀ : 𝒟₀ ⊗ 𝒟₁ → 𝒟₀`**, `(X ∪ Y) p₀ X' ↔ X ⊆ X'`. -/
def smashProj₀ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (smash V₀ V₁) V₀ where
  rel W X' := (smash V₀ V₁).mem W ∧ V₀.mem X' ∧ Sum.inl ⁻¹' W ⊆ X'
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(smash V₀ V₁).master_mem, V₀.master_mem, by simp⟩
  inter_right := by
    rintro W X' X'' ⟨hW, hX', hsub⟩ ⟨-, hX'', hsub'⟩
    obtain ⟨A, B, hA, _, rfl⟩ := smash_mem_prodNbhd_form hW
    rw [inl_preimage_prodNbhd] at hsub hsub' ⊢
    exact ⟨hW, V₀.inter_mem hX' hX'' hA (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W₂ X' X₂' ⟨_, _, hsub⟩ hW₂W hX'X₂' hW₂ hX₂'
    exact ⟨hW₂, hX₂', ((Set.preimage_mono hW₂W).trans hsub).trans hX'X₂'⟩

/-- **The smash projection `p₁ : 𝒟₀ ⊗ 𝒟₁ → 𝒟₁`**, `(X ∪ Y) p₁ Y' ↔ Y ⊆ Y'`. -/
def smashProj₁ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap (smash V₀ V₁) V₁ where
  rel W Y' := (smash V₀ V₁).mem W ∧ V₁.mem Y' ∧ Sum.inr ⁻¹' W ⊆ Y'
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(smash V₀ V₁).master_mem, V₁.master_mem, by simp⟩
  inter_right := by
    rintro W Y' Y'' ⟨hW, hY', hsub⟩ ⟨-, hY'', hsub'⟩
    obtain ⟨A, B, _, hB, rfl⟩ := smash_mem_prodNbhd_form hW
    rw [inr_preimage_prodNbhd] at hsub hsub' ⊢
    exact ⟨hW, V₁.inter_mem hY' hY'' hB (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
  mono := by
    rintro W W₂ Y' Y₂' ⟨_, _, hsub⟩ hW₂W hY'Y₂' hW₂ hY₂'
    exact ⟨hW₂, hY₂', ((Set.preimage_mono hW₂W).trans hsub).trans hY'Y₂'⟩

@[simp] theorem smashProj₀_rel {W : Set (α ⊕ β)} {X' : Set α} :
    (smashProj₀ V₀ V₁).rel W X' ↔ (smash V₀ V₁).mem W ∧ V₀.mem X' ∧ Sum.inl ⁻¹' W ⊆ X' := Iff.rfl

@[simp] theorem smashProj₁_rel {W : Set (α ⊕ β)} {Y' : Set β} :
    (smashProj₁ V₀ V₁).rel W Y' ↔ (smash V₀ V₁).mem W ∧ V₁.mem Y' ∧ Sum.inr ⁻¹' W ⊆ Y' := Iff.rfl

/-- **The strict pairing `⟨a, b⟩⊗ : 𝒟₂ → 𝒟₀ ⊗ 𝒟₁`.** Like Theorem 7.4's `paired`, but the smash
collapse forces the image factors to be proper (else the result is the master/bottom of the smash). -/
def smashPaired {V₂ : NeighborhoodSystem γ} (a : ApproximableMap V₂ V₀)
    (b : ApproximableMap V₂ V₁) : ApproximableMap V₂ (smash V₀ V₁) where
  rel Z W := V₂.mem Z ∧ (smash V₀ V₁).mem W ∧
    (W = prodNbhd V₀.master V₁.master ∨
      ∃ A B, W = prodNbhd A B ∧ A ≠ V₀.master ∧ B ≠ V₁.master ∧ a.rel Z A ∧ b.rel Z B)
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V₂.master_mem, (smash V₀ V₁).master_mem, Or.inl rfl⟩
  inter_right := by
    rintro Z W₁ W₂ ⟨hZ, hW₁, hd₁⟩ ⟨-, hW₂, hd₂⟩
    have key : W₁ ∩ W₂ = prodNbhd V₀.master V₁.master ∨
        ∃ A B, W₁ ∩ W₂ = prodNbhd A B ∧ A ≠ V₀.master ∧ B ≠ V₁.master ∧
          a.rel Z A ∧ b.rel Z B := by
      rcases hd₁ with rfl | ⟨A₁, B₁, rfl, hA₁, hB₁, ha₁, hb₁⟩
      · rw [Set.inter_eq_right.mpr (show W₂ ⊆ prodNbhd V₀.master V₁.master from
          (smash V₀ V₁).sub_master hW₂)]
        exact hd₂
      · rcases hd₂ with rfl | ⟨A₂, B₂, rfl, hA₂, hB₂, ha₂, hb₂⟩
        · rw [Set.inter_eq_left.mpr (show prodNbhd A₁ B₁ ⊆ prodNbhd V₀.master V₁.master from
            (smash V₀ V₁).sub_master hW₁)]
          exact Or.inr ⟨A₁, B₁, rfl, hA₁, hB₁, ha₁, hb₁⟩
        · rw [prodNbhd_inter]
          exact Or.inr ⟨A₁ ∩ A₂, B₁ ∩ B₂, rfl,
            inter_ne_master_left (a.rel_cod ha₁) hA₁,
            inter_ne_master_left (b.rel_cod hb₁) hB₁,
            a.inter_right ha₁ ha₂, b.inter_right hb₁ hb₂⟩
    refine ⟨hZ, ?_, key⟩
    rcases key with hm | ⟨A, B, hWW, hA, hB, ha, hb⟩
    · rw [hm]; exact (smash V₀ V₁).master_mem
    · rw [hWW]; exact smash_mem_proper (a.rel_cod ha) hA (b.rel_cod hb) hB
  mono := by
    rintro Z Z₂ W W₂ ⟨_, _, hd⟩ hZ₂Z hWW₂ hZ₂mem hW₂mem
    refine ⟨hZ₂mem, hW₂mem, ?_⟩
    rcases hd with rfl | ⟨A, B, rfl, hA, hB, ha, hb⟩
    · left; exact Set.Subset.antisymm ((smash V₀ V₁).sub_master hW₂mem) hWW₂
    · rcases smash_mem_iff.mp hW₂mem with rfl | ⟨A₂, B₂, hA₂, hA₂ne, hB₂, hB₂ne, rfl⟩
      · left; rfl
      · obtain ⟨hAA₂, hBB₂⟩ := prodNbhd_subset_iff.mp hWW₂
        exact Or.inr ⟨A₂, B₂, rfl, hA₂ne, hB₂ne,
          a.mono ha hZ₂Z hAA₂ hZ₂mem hA₂, b.mono hb hZ₂Z hBB₂ hZ₂mem hB₂⟩

@[simp] theorem smashPaired_rel {V₂ : NeighborhoodSystem γ} {a : ApproximableMap V₂ V₀}
    {b : ApproximableMap V₂ V₁} {Z : Set γ} {W : Set (α ⊕ β)} :
    (smashPaired a b).rel Z W ↔ V₂.mem Z ∧ (smash V₀ V₁).mem W ∧
      (W = prodNbhd V₀.master V₁.master ∨
        ∃ A B, W = prodNbhd A B ∧ A ≠ V₀.master ∧ B ≠ V₁.master ∧ a.rel Z A ∧ b.rel Z B) :=
  Iff.rfl

/-! ### The appropriate combinator for `⊗`: the functorial action `f ⊗ g`.

The smash product is a (bi)functor; `smashMap f g : 𝒟₀ ⊗ 𝒟₁ → 𝒟₀' ⊗ 𝒟₁'` is the coalesced analogue
of Theorem 7.4's `f × g` (`prodMap`). Because the smash collapses bottoms, the relation forces
*proper* image factors (`A' ≠ Δ₀'`, `B' ≠ Δ₁'`) and otherwise lands on the master (the strict
collapse). It is a genuine `ApproximableMap` and is **computable**: on the effective product indices
its relation decodes to `f`'s and `g`'s r.e. relations together with the codomain properness tests. -/

section SmashFunctor

variable {α' β' : Type*} {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- **The smash of two maps `f ⊗ g : 𝒟₀ ⊗ 𝒟₁ → 𝒟₀' ⊗ 𝒟₁'`.** -/
def smashMap (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    ApproximableMap (smash V₀ V₁) (smash V₀' V₁') where
  rel W W' := (smash V₀ V₁).mem W ∧ (smash V₀' V₁').mem W' ∧
    (W' = prodNbhd V₀'.master V₁'.master ∨
      ∃ A B A' B', W = prodNbhd A B ∧ W' = prodNbhd A' B' ∧
        A' ≠ V₀'.master ∧ B' ≠ V₁'.master ∧ f.rel A A' ∧ g.rel B B')
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(smash V₀ V₁).master_mem, (smash V₀' V₁').master_mem, Or.inl rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ ⟨hW, hW'₁, hd₁⟩ ⟨-, hW'₂, hd₂⟩
    have key : W'₁ ∩ W'₂ = prodNbhd V₀'.master V₁'.master ∨
        ∃ A B A' B', W = prodNbhd A B ∧ W'₁ ∩ W'₂ = prodNbhd A' B' ∧
          A' ≠ V₀'.master ∧ B' ≠ V₁'.master ∧ f.rel A A' ∧ g.rel B B' := by
      rcases hd₁ with rfl | ⟨A, B, A'₁, B'₁, hWAB, rfl, hA'₁, hB'₁, hf₁, hg₁⟩
      · rw [Set.inter_eq_right.mpr (show W'₂ ⊆ prodNbhd V₀'.master V₁'.master from
          (smash V₀' V₁').sub_master hW'₂)]
        exact hd₂
      · rcases hd₂ with rfl | ⟨A₂, B₂, A'₂, B'₂, hWAB₂, rfl, hA'₂, hB'₂, hf₂, hg₂⟩
        · rw [Set.inter_eq_left.mpr (show prodNbhd A'₁ B'₁ ⊆ prodNbhd V₀'.master V₁'.master from
            (smash V₀' V₁').sub_master hW'₁)]
          exact Or.inr ⟨A, B, A'₁, B'₁, hWAB, rfl, hA'₁, hB'₁, hf₁, hg₁⟩
        · obtain ⟨rfl, rfl⟩ := prodNbhd_injective (hWAB.symm.trans hWAB₂)
          rw [prodNbhd_inter]
          exact Or.inr ⟨A, B, A'₁ ∩ A'₂, B'₁ ∩ B'₂, hWAB, rfl,
            inter_ne_master_left (f.rel_cod hf₁) hA'₁,
            inter_ne_master_left (g.rel_cod hg₁) hB'₁,
            f.inter_right hf₁ hf₂, g.inter_right hg₁ hg₂⟩
    refine ⟨hW, ?_, key⟩
    rcases key with hm | ⟨A, B, A', B', -, hWW', hA', hB', hf, hg⟩
    · rw [hm]; exact (smash V₀' V₁').master_mem
    · rw [hWW']; exact smash_mem_proper (f.rel_cod hf) hA' (g.rel_cod hg) hB'
  mono := by
    rintro W W₂ W' W'₂ ⟨hW, hW', hd⟩ hW₂W hW'W'₂ hW₂mem hW'₂mem
    refine ⟨hW₂mem, hW'₂mem, ?_⟩
    rcases hd with rfl | ⟨A, B, A', B', rfl, rfl, hA', hB', hf, hg⟩
    · left; exact Set.Subset.antisymm ((smash V₀' V₁').sub_master hW'₂mem) hW'W'₂
    · obtain ⟨A₂, B₂, hA₂, hB₂, rfl⟩ := smash_mem_prodNbhd_form hW₂mem
      obtain ⟨hA₂A, hB₂B⟩ := prodNbhd_subset_iff.mp hW₂W
      rcases smash_mem_iff.mp hW'₂mem with rfl |
        ⟨A'₂, B'₂, hA'₂, hA'₂ne, hB'₂, hB'₂ne, rfl⟩
      · left; rfl
      · obtain ⟨hA'A'₂, hB'B'₂⟩ := prodNbhd_subset_iff.mp hW'W'₂
        exact Or.inr ⟨A₂, B₂, A'₂, B'₂, rfl, rfl, hA'₂ne, hB'₂ne,
          f.mono hf hA₂A hA'A'₂ hA₂ hA'₂, g.mono hg hB₂B hB'B'₂ hB₂ hB'₂⟩

/-- **`f ⊗ g` is computable.** Writing each smash code via its *effective* product index
(`smashEnum_eq_eff`), the relation `(smashEnum n) (f⊗g) (smashEnum' m)` decodes to: `m` improper
(the codomain master absorbs everything), or `m` proper together with `f`'s and `g`'s r.e. relations
on the effective coordinate indices. R.e.-ness then follows from `hf`, `hg`, the codomain properness
deciders, and closure of r.e. predicates under `∨`/`∧`/primitive-recursive substitution. -/
theorem smashMap_isComputable (P₀' : ComputablePresentation V₀') (P₁' : ComputablePresentation V₁')
    {f : ApproximableMap V₀ V₀'} {g : ApproximableMap V₁ V₁'}
    (hf : IsComputableMapS P₀.toScott P₀'.toScott f)
    (hg : IsComputableMapS P₁.toScott P₁'.toScott g) :
    IsComputableMapS (smashPresentation P₀ P₁) (smashPresentation P₀' P₁') (smashMap f g) := by
  obtain ⟨f₀, hf₀p, hf₀e⟩ := proper₀_dec P₀
  obtain ⟨f₁, hf₁p, hf₁e⟩ := proper₁_dec P₁
  set c₀ := fun n => isOne (f₀ n) with hc₀def
  set c₁ := fun n => isOne (f₁ n) with hc₁def
  have hc₀le : ∀ n, c₀ n ≤ 1 := fun n => isOne_le_one _
  have hc₁le : ∀ n, c₁ n ≤ 1 := fun n => isOne_le_one _
  have hc₀ : ∀ n, P₀.X n ≠ V₀.master ↔ c₀ n = 1 := fun n => by
    rw [hc₀def, isOne_eq_one_iff]; exact hf₀e n
  have hc₁ : ∀ n, P₁.X n ≠ V₁.master ↔ c₁ n = 1 := fun n => by
    rw [hc₁def, isOne_eq_one_iff]; exact hf₁e n
  have hc₀p : Nat.Primrec c₀ := primrec_isOne.comp hf₀p
  have hc₁p : Nat.Primrec c₁ := primrec_isOne.comp hf₁p
  have hpf : Nat.Primrec (fun n => c₀ n.unpair.1 * c₁ n.unpair.2) :=
    (primrec_mul.comp ((hc₀p.comp Nat.Primrec.left).pair (hc₁p.comp Nat.Primrec.right))).of_eq
      (fun n => by simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd])
  have heffLp : Nat.Primrec (fun n => selectFn (c₀ n.unpair.1 * c₁ n.unpair.2)
      n.unpair.1 P₀.masterIdx) :=
    primrec_selectFn hpf Nat.Primrec.left (Nat.Primrec.const _)
  have heffRp : Nat.Primrec (fun n => selectFn (c₀ n.unpair.1 * c₁ n.unpair.2)
      n.unpair.2 P₁.masterIdx) :=
    primrec_selectFn hpf Nat.Primrec.right (Nat.Primrec.const _)
  -- `f`'s r.e. relation on `(effL n, m.1)`; `g`'s on `(effR n, m.2)`
  have Hf : REPred (fun t => f.rel (P₀.toScott.X
      (selectFn (c₀ t.unpair.1.unpair.1 * c₁ t.unpair.1.unpair.2)
        t.unpair.1.unpair.1 P₀.masterIdx)) (P₀'.toScott.X t.unpair.2.unpair.1)) :=
    REPred.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hf.comp ((heffLp.comp Nat.Primrec.left).pair
        (Nat.Primrec.left.comp Nat.Primrec.right)))
  have Hg : REPred (fun t => g.rel (P₁.toScott.X
      (selectFn (c₀ t.unpair.1.unpair.1 * c₁ t.unpair.1.unpair.2)
        t.unpair.1.unpair.2 P₁.masterIdx)) (P₁'.toScott.X t.unpair.2.unpair.2)) :=
    REPred.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hg.comp ((heffRp.comp Nat.Primrec.left).pair
        (Nat.Primrec.right.comp Nat.Primrec.right)))
  have hJP : RecDecidable (fun t => P₀'.X t.unpair.2.unpair.1 ≠ V₀'.master ∧
      P₁'.X t.unpair.2.unpair.2 ≠ V₁'.master) :=
    ((proper₀_dec P₀').comp (Nat.Primrec.left.comp Nat.Primrec.right)).and
      ((proper₁_dec P₁').comp (Nat.Primrec.right.comp Nat.Primrec.right))
  refine REPred.of_iff (fun t => ?_) ((hJP.not.re).or (hJP.re.and (Hf.and Hg)))
  show (smashMap f g).rel (smashEnum P₀ P₁ t.unpair.1) (smashEnum P₀' P₁' t.unpair.2) ↔ _
  have heq : smashEnum P₀ P₁ t.unpair.1 = prodNbhd
      (P₀.X (selectFn (c₀ t.unpair.1.unpair.1 * c₁ t.unpair.1.unpair.2)
        t.unpair.1.unpair.1 P₀.masterIdx))
      (P₁.X (selectFn (c₀ t.unpair.1.unpair.1 * c₁ t.unpair.1.unpair.2)
        t.unpair.1.unpair.2 P₁.masterIdx)) := smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁ t.unpair.1
  by_cases hJPm : P₀'.X t.unpair.2.unpair.1 ≠ V₀'.master ∧ P₁'.X t.unpair.2.unpair.2 ≠ V₁'.master
  · constructor
    · rintro ⟨-, -, hd⟩
      rcases hd with hmaster | ⟨A, B, A', B', hWAB, hW'AB, -, -, hfr, hgr⟩
      · rw [smashEnum_proper hJPm] at hmaster
        exact absurd (prodNbhd_injective hmaster).1 hJPm.1
      · rw [smashEnum_proper hJPm] at hW'AB
        obtain ⟨rfl, rfl⟩ := prodNbhd_injective (heq.symm.trans hWAB)
        obtain ⟨rfl, rfl⟩ := prodNbhd_injective hW'AB
        exact Or.inr ⟨hJPm, hfr, hgr⟩
    · rintro (hnp | ⟨-, hfr, hgr⟩)
      · exact absurd hJPm hnp
      · exact ⟨smashEnum_mem (P₀ := P₀) (P₁ := P₁) t.unpair.1,
          smashEnum_mem (P₀ := P₀') (P₁ := P₁') t.unpair.2,
          Or.inr ⟨_, _, _, _, heq, smashEnum_proper hJPm, hJPm.1, hJPm.2, hfr, hgr⟩⟩
  · constructor
    · intro _; exact Or.inl hJPm
    · intro _
      exact ⟨smashEnum_mem (P₀ := P₀) (P₁ := P₁) t.unpair.1,
        smashEnum_mem (P₀ := P₀') (P₁ := P₁') t.unpair.2,
        Or.inl (smashEnum_master hJPm)⟩

end SmashFunctor

/-- **The smash projection `p₀` is computable.** `(smashEnum n) p₀ X⁰_m ↔ X⁰_{effL n} ⊆ X⁰_m`
(`smashEnum_eq_eff` rewrites `Sum.inl ⁻¹' (smashEnum n)` to the effective left factor), a recursive
slice of `incl_computable`. -/
theorem smashProj₀_isComputable :
    IsComputableMapS (smashPresentation P₀ P₁) P₀.toScott (smashProj₀ V₀ V₁) := by
  obtain ⟨f₀, hf₀p, hf₀e⟩ := proper₀_dec P₀
  obtain ⟨f₁, hf₁p, hf₁e⟩ := proper₁_dec P₁
  set c₀ := fun n => isOne (f₀ n) with hc₀def
  set c₁ := fun n => isOne (f₁ n) with hc₁def
  have hc₀le : ∀ n, c₀ n ≤ 1 := fun n => isOne_le_one _
  have hc₁le : ∀ n, c₁ n ≤ 1 := fun n => isOne_le_one _
  have hc₀ : ∀ n, P₀.X n ≠ V₀.master ↔ c₀ n = 1 := fun n => by
    rw [hc₀def, isOne_eq_one_iff]; exact hf₀e n
  have hc₁ : ∀ n, P₁.X n ≠ V₁.master ↔ c₁ n = 1 := fun n => by
    rw [hc₁def, isOne_eq_one_iff]; exact hf₁e n
  have hc₀p : Nat.Primrec c₀ := primrec_isOne.comp hf₀p
  have hc₁p : Nat.Primrec c₁ := primrec_isOne.comp hf₁p
  have hpf : Nat.Primrec (fun n => c₀ n.unpair.1 * c₁ n.unpair.2) :=
    (primrec_mul.comp ((hc₀p.comp Nat.Primrec.left).pair (hc₁p.comp Nat.Primrec.right))).of_eq
      (fun n => by simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd])
  have heffLp : Nat.Primrec (fun n => selectFn (c₀ n.unpair.1 * c₁ n.unpair.2)
      n.unpair.1 P₀.masterIdx) :=
    primrec_selectFn hpf Nat.Primrec.left (Nat.Primrec.const _)
  have hincl : RecDecidable (fun s => P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) := P₀.incl_computable
  have hr : Nat.Primrec (fun t => Nat.pair
      (selectFn (c₀ t.unpair.1.unpair.1 * c₁ t.unpair.1.unpair.2) t.unpair.1.unpair.1 P₀.masterIdx)
      t.unpair.2) := (heffLp.comp Nat.Primrec.left).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  show (smashProj₀ V₀ V₁).rel (smashEnum P₀ P₁ t.unpair.1) (P₀.X t.unpair.2) ↔ _
  simp only [smashProj₀_rel, unpair_pair_fst, unpair_pair_snd]
  constructor
  · rintro ⟨-, -, hsub⟩
    rw [smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁, inl_preimage_prodNbhd] at hsub
    exact hsub
  · intro h
    refine ⟨smashEnum_mem (P₀ := P₀) (P₁ := P₁) _, P₀.mem_X _, ?_⟩
    rw [smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁, inl_preimage_prodNbhd]
    exact h

/-- **The smash projection `p₁` is computable.** Symmetric to `smashProj₀_isComputable`, using the
effective right factor `Sum.inr ⁻¹' (smashEnum n) = X¹_{effR n}`. -/
theorem smashProj₁_isComputable :
    IsComputableMapS (smashPresentation P₀ P₁) P₁.toScott (smashProj₁ V₀ V₁) := by
  obtain ⟨f₀, hf₀p, hf₀e⟩ := proper₀_dec P₀
  obtain ⟨f₁, hf₁p, hf₁e⟩ := proper₁_dec P₁
  set c₀ := fun n => isOne (f₀ n) with hc₀def
  set c₁ := fun n => isOne (f₁ n) with hc₁def
  have hc₀le : ∀ n, c₀ n ≤ 1 := fun n => isOne_le_one _
  have hc₁le : ∀ n, c₁ n ≤ 1 := fun n => isOne_le_one _
  have hc₀ : ∀ n, P₀.X n ≠ V₀.master ↔ c₀ n = 1 := fun n => by
    rw [hc₀def, isOne_eq_one_iff]; exact hf₀e n
  have hc₁ : ∀ n, P₁.X n ≠ V₁.master ↔ c₁ n = 1 := fun n => by
    rw [hc₁def, isOne_eq_one_iff]; exact hf₁e n
  have hc₀p : Nat.Primrec c₀ := primrec_isOne.comp hf₀p
  have hc₁p : Nat.Primrec c₁ := primrec_isOne.comp hf₁p
  have hpf : Nat.Primrec (fun n => c₀ n.unpair.1 * c₁ n.unpair.2) :=
    (primrec_mul.comp ((hc₀p.comp Nat.Primrec.left).pair (hc₁p.comp Nat.Primrec.right))).of_eq
      (fun n => by simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd])
  have heffRp : Nat.Primrec (fun n => selectFn (c₀ n.unpair.1 * c₁ n.unpair.2)
      n.unpair.2 P₁.masterIdx) :=
    primrec_selectFn hpf Nat.Primrec.right (Nat.Primrec.const _)
  have hincl : RecDecidable (fun s => P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) := P₁.incl_computable
  have hr : Nat.Primrec (fun t => Nat.pair
      (selectFn (c₀ t.unpair.1.unpair.1 * c₁ t.unpair.1.unpair.2) t.unpair.1.unpair.2 P₁.masterIdx)
      t.unpair.2) := (heffRp.comp Nat.Primrec.left).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  show (smashProj₁ V₀ V₁).rel (smashEnum P₀ P₁ t.unpair.1) (P₁.X t.unpair.2) ↔ _
  simp only [smashProj₁_rel, unpair_pair_fst, unpair_pair_snd]
  constructor
  · rintro ⟨-, -, hsub⟩
    rw [smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁, inr_preimage_prodNbhd] at hsub
    exact hsub
  · intro h
    refine ⟨smashEnum_mem (P₀ := P₀) (P₁ := P₁) _, P₁.mem_X _, ?_⟩
    rw [smashEnum_eq_eff hc₀le hc₁le hc₀ hc₁, inr_preimage_prodNbhd]
    exact h

/-- **The strict pairing `⟨a, b⟩⊗` is computable.** `Zₙ ⟨a,b⟩⊗ (smashEnum m) ↔` either `m` improper
(the codomain master absorbs) or `m` proper together with `a`'s and `b`'s r.e. relations on the
(raw) codomain coordinate indices — an `∨`/`∧` of r.e. predicates and the codomain properness tests.
No effective-index bridge is needed: the proper branch reads `smashEnum`'s raw factors directly. -/
theorem smashPaired_isComputable {V₂ : NeighborhoodSystem γ} (P₂ : ComputablePresentation V₂)
    {a : ApproximableMap V₂ V₀} {b : ApproximableMap V₂ V₁}
    (ha : IsComputableMapS P₂.toScott P₀.toScott a)
    (hb : IsComputableMapS P₂.toScott P₁.toScott b) :
    IsComputableMapS P₂.toScott (smashPresentation P₀ P₁) (smashPaired a b) := by
  have Ha : REPred (fun t => a.rel (P₂.toScott.X t.unpair.1) (P₀.toScott.X t.unpair.2.unpair.1)) :=
    REPred.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (ha.comp (Nat.Primrec.left.pair (Nat.Primrec.left.comp Nat.Primrec.right)))
  have Hb : REPred (fun t => b.rel (P₂.toScott.X t.unpair.1) (P₁.toScott.X t.unpair.2.unpair.2)) :=
    REPred.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hb.comp (Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)))
  have hJP : RecDecidable (fun t => P₀.X t.unpair.2.unpair.1 ≠ V₀.master ∧
      P₁.X t.unpair.2.unpair.2 ≠ V₁.master) :=
    ((proper₀_dec P₀).comp (Nat.Primrec.left.comp Nat.Primrec.right)).and
      ((proper₁_dec P₁).comp (Nat.Primrec.right.comp Nat.Primrec.right))
  refine REPred.of_iff (fun t => ?_) ((hJP.not.re).or (hJP.re.and (Ha.and Hb)))
  show (smashPaired a b).rel (P₂.X t.unpair.1) (smashEnum P₀ P₁ t.unpair.2) ↔ _
  by_cases hJPm : P₀.X t.unpair.2.unpair.1 ≠ V₀.master ∧ P₁.X t.unpair.2.unpair.2 ≠ V₁.master
  · constructor
    · rintro ⟨-, -, hd⟩
      rcases hd with hmaster | ⟨A, B, hWAB, -, -, ha', hb'⟩
      · rw [smashEnum_proper hJPm] at hmaster
        exact absurd (prodNbhd_injective hmaster).1 hJPm.1
      · rw [smashEnum_proper hJPm] at hWAB
        obtain ⟨rfl, rfl⟩ := prodNbhd_injective hWAB
        exact Or.inr ⟨hJPm, ha', hb'⟩
    · rintro (hnp | ⟨-, ha', hb'⟩)
      · exact absurd hJPm hnp
      · exact ⟨P₂.mem_X _, smashEnum_mem (P₀ := P₀) (P₁ := P₁) _,
          Or.inr ⟨_, _, smashEnum_proper hJPm, hJPm.1, hJPm.2, ha', hb'⟩⟩
  · constructor
    · intro _; exact Or.inl hJPm
    · intro _
      exact ⟨P₂.mem_X _, smashEnum_mem (P₀ := P₀) (P₁ := P₁) _,
        Or.inl (smashEnum_master hJPm)⟩

end Smash

/-! ## The coalesced sum `𝒟₀ ⊕ 𝒟₁` is effectively given (Scott's Definition 7.1)

`𝒟₀ ⊕ 𝒟₁` (Exercise 6.21, here over `Option (α ⊕ β)`) is the separated sum `+` with the *improper*
tagged copies `0Δ₀`, `1Δ₁` deleted (the two bottoms identified). As with `⊗`, the enumeration must
re-route improper copies to the master (the sole classical input), while the relations (i),(ii) are
choice-free recursively decidable. -/

section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)

/-- **Exercise 7.15 — the coalesced sum system `𝒟₀ ⊕ 𝒟₁`** over `Option (α ⊕ β)`: the separated sum
with the improper copies `0Δ₀`, `1Δ₁` deleted. (Generalises `Exercise621.oplusTok` to an arbitrary
carrier.) -/
def osum : NeighborhoodSystem (Option (α ⊕ β)) where
  mem W := W = sumMaster V₀ V₁ ∨ (∃ X, V₀.mem X ∧ X ≠ V₀.master ∧ W = inj₀ X) ∨
    (∃ Y, V₁.mem Y ∧ Y ≠ V₁.master ∧ W = inj₁ Y)
  master := sumMaster V₀ V₁
  master_mem := Or.inl rfl
  sub_master := by
    rintro W (rfl | ⟨X, hX, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
    · exact subset_rfl
    · exact inj₀_subset_sumMaster hX
    · exact inj₁_subset_sumMaster hY
  inter_mem := by
    have hne : ∀ W, (W = sumMaster V₀ V₁ ∨ (∃ X, V₀.mem X ∧ X ≠ V₀.master ∧ W = inj₀ X) ∨
        (∃ Y, V₁.mem Y ∧ Y ≠ V₁.master ∧ W = inj₁ Y)) → (W : Set (Option (α ⊕ β))).Nonempty := by
      rintro W (rfl | ⟨X, hX, -, rfl⟩ | ⟨Y, hY, -, rfl⟩)
      · exact ⟨none, none_mem_sumMaster⟩
      · exact inj₀_nonempty (h₀ X hX)
      · exact inj₁_nonempty (h₁ Y hY)
    rintro W W' Z hW hW' hZ hZsub
    rcases hW with rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩
    · rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
      · rw [Set.inter_self]; exact Or.inl rfl
      · rw [sumMaster_inter_inj₀ hX']; exact Or.inr (Or.inl ⟨X', hX', hX'ne, rfl⟩)
      · rw [sumMaster_inter_inj₁ hY']; exact Or.inr (Or.inr ⟨Y', hY', hY'ne, rfl⟩)
    · rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
      · rw [Set.inter_comm, sumMaster_inter_inj₀ hX]; exact Or.inr (Or.inl ⟨X, hX, hXne, rfl⟩)
      · rw [inj₀_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z₀, hZ₀, -, rfl⟩ | ⟨Z₁, hZ₁, -, rfl⟩
        · exact absurd (hZsub none_mem_sumMaster) none_mem_inj₀
        · exact Or.inr (Or.inl ⟨X ∩ X', V₀.inter_mem hX hX' hZ₀ (inj₀_subset_inj₀.mp hZsub),
            inter_ne_master_left hX hXne, rfl⟩)
        · obtain ⟨b, hb⟩ := h₁ Z₁ hZ₁
          exact absurd (hZsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
      · rw [inj₀_inter_inj₁] at hZsub
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
    · rcases hW' with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
      · rw [Set.inter_comm, sumMaster_inter_inj₁ hY]; exact Or.inr (Or.inr ⟨Y, hY, hYne, rfl⟩)
      · rw [Set.inter_comm, inj₀_inter_inj₁] at hZsub
        obtain ⟨t, ht⟩ := hne Z hZ; exact absurd (hZsub ht) (Set.notMem_empty t)
      · rw [inj₁_inter] at hZsub ⊢
        rcases hZ with rfl | ⟨Z₀, hZ₀, -, rfl⟩ | ⟨Z₁, hZ₁, -, rfl⟩
        · exact absurd (hZsub none_mem_sumMaster) none_mem_inj₁
        · obtain ⟨a, ha⟩ := h₀ Z₀ hZ₀
          exact absurd (hZsub (il_mem_inj₀.mpr ha)) il_mem_inj₁
        · exact Or.inr (Or.inr ⟨Y ∩ Y', V₁.inter_mem hY hY' hZ₁ (inj₁_subset_inj₁.mp hZsub),
            inter_ne_master_right hY hYne, rfl⟩)

@[simp] theorem osum_master : (osum h₀ h₁).master = sumMaster V₀ V₁ := rfl

theorem osum_mem_iff {W : Set (Option (α ⊕ β))} :
    (osum h₀ h₁).mem W ↔ W = sumMaster V₀ V₁ ∨
      (∃ X, V₀.mem X ∧ X ≠ V₀.master ∧ W = inj₀ X) ∨
      (∃ Y, V₁.mem Y ∧ Y ≠ V₁.master ∧ W = inj₁ Y) := Iff.rfl

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

open scoped Classical in
/-- **Coalesced-sum enumeration.** Tag `0`/`1`/`≥2`; a tag-0/1 code is its proper left/right copy
when the indexed factor is proper, otherwise it is re-routed to the master (the classical input). -/
noncomputable def osumEnum (t : ℕ) : Set (Option (α ⊕ β)) :=
  if t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master then inj₀ (P₀.X t.unpair.2)
  else if t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master then inj₁ (P₁.X t.unpair.2)
  else sumMaster V₀ V₁

variable {P₀ P₁}

open scoped Classical in
theorem osumEnum_left {t : ℕ} (h : t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master) :
    osumEnum P₀ P₁ t = inj₀ (P₀.X t.unpair.2) := if_pos h

open scoped Classical in
theorem osumEnum_right {t : ℕ} (h : t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master) :
    osumEnum P₀ P₁ t = inj₁ (P₁.X t.unpair.2) := by
  have h0 : ¬(t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master) := by
    rintro ⟨hc, -⟩; obtain ⟨h1, -⟩ := h; omega
  unfold osumEnum; rw [if_neg h0, if_pos h]

open scoped Classical in
theorem osumEnum_master {t : ℕ}
    (h0 : ¬(t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master))
    (h1 : ¬(t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master)) :
    osumEnum P₀ P₁ t = sumMaster V₀ V₁ := by
  unfold osumEnum; rw [if_neg h0, if_neg h1]

theorem osumEnum_mem (t : ℕ) : (osum h₀ h₁).mem (osumEnum P₀ P₁ t) := by
  by_cases hL : t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master
  · rw [osumEnum_left hL]; exact Or.inr (Or.inl ⟨_, P₀.mem_X _, hL.2, rfl⟩)
  · by_cases hR : t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master
    · rw [osumEnum_right hR]; exact Or.inr (Or.inr ⟨_, P₁.mem_X _, hR.2, rfl⟩)
    · rw [osumEnum_master hL hR]; exact Or.inl rfl

include h₀ h₁ in
theorem osumEnum_subset_master (t : ℕ) : osumEnum P₀ P₁ t ⊆ sumMaster V₀ V₁ :=
  (osum h₀ h₁).sub_master (osumEnum_mem h₀ h₁ t)

include h₀ h₁ in
theorem osumEnum_nonempty (t : ℕ) : (osumEnum P₀ P₁ t).Nonempty := by
  by_cases hL : t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master
  · rw [osumEnum_left hL]; exact inj₀_nonempty (h₀ _ (P₀.mem_X _))
  · by_cases hR : t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master
    · rw [osumEnum_right hR]; exact inj₁_nonempty (h₁ _ (P₁.mem_X _))
    · rw [osumEnum_master hL hR]; exact ⟨none, none_mem_sumMaster⟩

/-- **Exercise 7.15 — `𝒟₀ ⊕ 𝒟₁` is effectively given (Scott's Definition 7.1).** -/
noncomputable def osumPresentation : ScottPresentation (osum h₀ h₁) where
  X := osumEnum P₀ P₁
  mem_X := osumEnum_mem h₀ h₁
  surj := by
    rintro W (rfl | ⟨X, hX, hXne, rfl⟩ | ⟨Y, hY, hYne, rfl⟩)
    · refine ⟨Nat.pair 2 0, ?_⟩
      rw [osumEnum_master (by rw [unpair_pair_fst]; rintro ⟨h, -⟩; omega)
        (by rw [unpair_pair_fst]; rintro ⟨h, -⟩; omega)]
    · obtain ⟨n, rfl⟩ := P₀.surj hX
      refine ⟨Nat.pair 0 n, ?_⟩
      rw [osumEnum_left (by rw [unpair_pair_fst, unpair_pair_snd]; exact ⟨rfl, hXne⟩),
        unpair_pair_snd]
    · obtain ⟨n, rfl⟩ := P₁.surj hY
      refine ⟨Nat.pair 1 n, ?_⟩
      rw [osumEnum_right (by rw [unpair_pair_fst, unpair_pair_snd]; exact ⟨rfl, hYne⟩),
        unpair_pair_snd]
  interEq_computable := by
    obtain ⟨f₀, hf₀p, hf₀e⟩ := proper₀_dec P₀
    obtain ⟨f₁, hf₁p, hf₁e⟩ := proper₁_dec P₁
    have hc₀1 : ∀ n, isOne (f₀ n) = 1 ↔ P₀.X n ≠ V₀.master := fun n => by
      rw [isOne_eq_one_iff]; exact (hf₀e n).symm
    have hc₁1 : ∀ n, isOne (f₁ n) = 1 ↔ P₁.X n ≠ V₁.master := fun n => by
      rw [isOne_eq_one_iff]; exact (hf₁e n).symm
    classical
    set r : ℕ → ℕ := fun t =>
      if t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master then Nat.pair 0 t.unpair.2
      else if t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master then Nat.pair 1 t.unpair.2
      else Nat.pair 2 0 with hrdef
    have hr_left : ∀ t, (t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master) →
        r t = Nat.pair 0 t.unpair.2 := fun t h => by simp only [hrdef]; exact if_pos h
    have hr_right : ∀ t, ¬(t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master) →
        (t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master) → r t = Nat.pair 1 t.unpair.2 :=
      fun t h0 h1 => by simp only [hrdef]; rw [if_neg h0, if_pos h1]
    have hr_master : ∀ t, ¬(t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master) →
        ¬(t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master) → r t = Nat.pair 2 0 :=
      fun t h0 h1 => by simp only [hrdef]; rw [if_neg h0, if_neg h1]
    have hval : ∀ t, osumEnum P₀ P₁ t = sumEnum P₀ P₁ (r t) := by
      intro t
      by_cases hL : t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master
      · rw [osumEnum_left hL, hr_left t hL, sumEnum_zero (by rw [unpair_pair_fst]),
          unpair_pair_snd]
      · by_cases hR : t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master
        · rw [osumEnum_right hR, hr_right t hL hR, sumEnum_one (by rw [unpair_pair_fst]),
            unpair_pair_snd]
        · rw [osumEnum_master hL hR, hr_master t hL hR,
            sumEnum_master (by rw [unpair_pair_fst]; decide) (by rw [unpair_pair_fst]; decide)]
    have hbit0 : ∀ v, isOne v = if v = 1 then 1 else 0 := fun v => by
      by_cases h : v = 1
      · rw [if_pos h, h]; rfl
      · rw [if_neg h]; have h1 := isOne_le_one v; have h2 := isOne_eq_one_iff v; omega
    have hrp : Nat.Primrec r := by
      have hchr1 : Nat.Primrec (fun t : ℕ => (1 - t.unpair.1) * isOne (f₀ t.unpair.2)) :=
        primrec_mul₂ (primrec_sub₂ (Nat.Primrec.const 1) Nat.Primrec.left)
          (primrec_isOne.comp (hf₀p.comp Nat.Primrec.right))
      have hchr2 : Nat.Primrec (fun t : ℕ => isOne t.unpair.1 * isOne (f₁ t.unpair.2)) :=
        primrec_mul₂ (primrec_isOne.comp Nat.Primrec.left)
          (primrec_isOne.comp (hf₁p.comp Nat.Primrec.right))
      have hA : Nat.Primrec (fun t : ℕ => Nat.pair 0 t.unpair.2) :=
        (Nat.Primrec.const 0).pair Nat.Primrec.right
      have hB : Nat.Primrec (fun t : ℕ => Nat.pair 1 t.unpair.2) :=
        (Nat.Primrec.const 1).pair Nat.Primrec.right
      have hC : Nat.Primrec (fun _ : ℕ => Nat.pair 2 0) := Nat.Primrec.const _
      have hchr1eq : ∀ t : ℕ, (1 - t.unpair.1) * isOne (f₀ t.unpair.2)
          = if (t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master) then 1 else 0 := by
        intro t
        by_cases hc : t.unpair.1 = 0 ∧ P₀.X t.unpair.2 ≠ V₀.master
        · rw [if_pos hc]
          have ht0 := hc.1
          have e1 : 1 - t.unpair.1 = 1 := by omega
          rw [e1, (hc₀1 _).mpr hc.2]
        · rw [if_neg hc]
          rcases not_and_or.mp hc with h | h
          · have e1 : 1 - t.unpair.1 = 0 := by omega
            rw [e1, Nat.zero_mul]
          · have e2 : isOne (f₀ t.unpair.2) = 0 := by
              have hle := isOne_le_one (f₀ t.unpair.2)
              by_contra h0; exact h ((hc₀1 _).mp (by omega))
            rw [e2, Nat.mul_zero]
      have hchr2eq : ∀ t : ℕ, isOne t.unpair.1 * isOne (f₁ t.unpair.2)
          = if (t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master) then 1 else 0 := by
        intro t
        by_cases hc : t.unpair.1 = 1 ∧ P₁.X t.unpair.2 ≠ V₁.master
        · rw [if_pos hc, (by rw [isOne_eq_one_iff]; exact hc.1 : isOne t.unpair.1 = 1),
            (hc₁1 _).mpr hc.2]
        · rw [if_neg hc]
          rcases not_and_or.mp hc with h | h
          · have e1 : isOne t.unpair.1 = 0 := by rw [hbit0]; exact if_neg h
            rw [e1, Nat.zero_mul]
          · have e2 : isOne (f₁ t.unpair.2) = 0 := by
              have hle := isOne_le_one (f₁ t.unpair.2)
              by_contra h0; exact h ((hc₁1 _).mp (by omega))
            rw [e2, Nat.mul_zero]
      refine (primrec_selectFn hchr1 hA (primrec_selectFn hchr2 hB hC)).of_eq (fun t => ?_)
      simp only [hchr1eq, hchr2eq, selectFn_ite, hrdef]
    have hg : Nat.Primrec (fun t => Nat.pair (r t.unpair.1)
        (Nat.pair (r t.unpair.2.unpair.1) (r t.unpair.2.unpair.2))) :=
      (hrp.comp Nat.Primrec.left).pair
        ((hrp.comp (Nat.Primrec.left.comp Nat.Primrec.right)).pair
          (hrp.comp (Nat.Primrec.right.comp Nat.Primrec.right)))
    refine RecDecidable.of_iff (fun t => ?_)
      ((sumPresentation (h₀ := h₀) (h₁ := h₁) P₀ P₁).interEq_computable.comp hg)
    have hXeq : ∀ x, (sumPresentation (h₀ := h₀) (h₁ := h₁) P₀ P₁).X x = sumEnum P₀ P₁ x :=
      fun _ => rfl
    simp only [unpair_pair_fst, unpair_pair_snd, hXeq]
    rw [hval t.unpair.1, hval t.unpair.2.unpair.1, hval t.unpair.2.unpair.2]
  cons_computable := by
    have hLa : RecDecidable (fun t => t.unpair.1.unpair.1 = 0
        ∧ P₀.X t.unpair.1.unpair.2 ≠ V₀.master) :=
      (RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 0)).and
        ((proper₀_dec P₀).comp (Nat.Primrec.right.comp Nat.Primrec.left))
    have hRa : RecDecidable (fun t => t.unpair.1.unpair.1 = 1
        ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master) :=
      (RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 1)).and
        ((proper₁_dec P₁).comp (Nat.Primrec.right.comp Nat.Primrec.left))
    have hLb : RecDecidable (fun t => t.unpair.2.unpair.1 = 0
        ∧ P₀.X t.unpair.2.unpair.2 ≠ V₀.master) :=
      (RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 0)).and
        ((proper₀_dec P₀).comp (Nat.Primrec.right.comp Nat.Primrec.right))
    have hRb : RecDecidable (fun t => t.unpair.2.unpair.1 = 1
        ∧ P₁.X t.unpair.2.unpair.2 ≠ V₁.master) :=
      (RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)).and
        ((proper₁_dec P₁).comp (Nat.Primrec.right.comp Nat.Primrec.right))
    have hMca : RecDecidable (fun t => ¬(t.unpair.1.unpair.1 = 0
        ∧ P₀.X t.unpair.1.unpair.2 ≠ V₀.master)
        ∧ ¬(t.unpair.1.unpair.1 = 1 ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master)) := hLa.not.and hRa.not
    have hMcb : RecDecidable (fun t => ¬(t.unpair.2.unpair.1 = 0
        ∧ P₀.X t.unpair.2.unpair.2 ≠ V₀.master)
        ∧ ¬(t.unpair.2.unpair.1 = 1 ∧ P₁.X t.unpair.2.unpair.2 ≠ V₁.master)) := hLb.not.and hRb.not
    have hcons0 : RecDecidable (fun t => ∃ k, P₀.X k ⊆ P₀.X t.unpair.1.unpair.2
        ∩ P₀.X t.unpair.2.unpair.2) := by
      refine RecDecidable.of_iff (fun t => ?_) (P₀.cons_computable.comp
        ((Nat.Primrec.right.comp Nat.Primrec.left).pair (Nat.Primrec.right.comp Nat.Primrec.right)))
      simp only [unpair_pair_fst, unpair_pair_snd]
    have hcons1 : RecDecidable (fun t => ∃ k, P₁.X k ⊆ P₁.X t.unpair.1.unpair.2
        ∩ P₁.X t.unpair.2.unpair.2) := by
      refine RecDecidable.of_iff (fun t => ?_) (P₁.cons_computable.comp
        ((Nat.Primrec.right.comp Nat.Primrec.left).pair (Nat.Primrec.right.comp Nat.Primrec.right)))
      simp only [unpair_pair_fst, unpair_pair_snd]
    refine RecDecidable.of_iff (fun t => ?_)
      (hMca.or (hMcb.or ((hLa.and (hLb.and hcons0)).or (hRa.and (hRb.and hcons1)))))
    constructor
    · rintro ⟨k, hk⟩
      by_cases hLa' : t.unpair.1.unpair.1 = 0 ∧ P₀.X t.unpair.1.unpair.2 ≠ V₀.master
      · by_cases hLb' : t.unpair.2.unpair.1 = 0 ∧ P₀.X t.unpair.2.unpair.2 ≠ V₀.master
        · rw [osumEnum_left hLa', osumEnum_left hLb', inj₀_inter] at hk
          refine Or.inr (Or.inr (Or.inl ⟨hLa', hLb', ?_⟩))
          rcases osumEnum_mem h₀ h₁ k with hkm | ⟨Xk, hXk, -, hkeq⟩ | ⟨Yk, hYk, -, hkeq⟩
          · exact absurd (hk (hkm ▸ none_mem_sumMaster)) none_mem_inj₀
          · rw [hkeq, inj₀_subset_inj₀] at hk
            obtain ⟨j, hj⟩ := P₀.surj hXk
            exact ⟨j, by rw [hj]; exact hk⟩
          · rw [hkeq] at hk
            obtain ⟨y0, hy0⟩ := h₁ Yk hYk
            exact absurd (hk (ir_mem_inj₁.mpr hy0)) ir_mem_inj₀
        · by_cases hRb' : t.unpair.2.unpair.1 = 1 ∧ P₁.X t.unpair.2.unpair.2 ≠ V₁.master
          · rw [osumEnum_left hLa', osumEnum_right hRb', inj₀_inter_inj₁] at hk
            obtain ⟨m, hm⟩ := osumEnum_nonempty h₀ h₁ k
            exact absurd (hk hm) (Set.notMem_empty m)
          · exact Or.inr (Or.inl ⟨hLb', hRb'⟩)
      · by_cases hRa' : t.unpair.1.unpair.1 = 1 ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master
        · by_cases hRb' : t.unpair.2.unpair.1 = 1 ∧ P₁.X t.unpair.2.unpair.2 ≠ V₁.master
          · rw [osumEnum_right hRa', osumEnum_right hRb', inj₁_inter] at hk
            refine Or.inr (Or.inr (Or.inr ⟨hRa', hRb', ?_⟩))
            rcases osumEnum_mem h₀ h₁ k with hkm | ⟨Xk, hXk, -, hkeq⟩ | ⟨Yk, hYk, -, hkeq⟩
            · exact absurd (hk (hkm ▸ none_mem_sumMaster)) none_mem_inj₁
            · rw [hkeq] at hk
              obtain ⟨x0, hx0⟩ := h₀ Xk hXk
              exact absurd (hk (il_mem_inj₀.mpr hx0)) il_mem_inj₁
            · rw [hkeq, inj₁_subset_inj₁] at hk
              obtain ⟨j, hj⟩ := P₁.surj hYk
              exact ⟨j, by rw [hj]; exact hk⟩
          · by_cases hLb' : t.unpair.2.unpair.1 = 0 ∧ P₀.X t.unpair.2.unpair.2 ≠ V₀.master
            · rw [osumEnum_right hRa', osumEnum_left hLb', Set.inter_comm,
                inj₀_inter_inj₁] at hk
              obtain ⟨m, hm⟩ := osumEnum_nonempty h₀ h₁ k
              exact absurd (hk hm) (Set.notMem_empty m)
            · exact Or.inr (Or.inl ⟨hLb', hRb'⟩)
        · exact Or.inl ⟨hLa', hRa'⟩
    · intro hp
      rcases hp with hMca' | hMcb' | ⟨hLa', hLb', hc0⟩ | ⟨hRa', hRb', hc1⟩
      · refine ⟨t.unpair.2, ?_⟩
        rw [osumEnum_master hMca'.1 hMca'.2]
        exact Set.subset_inter (osumEnum_subset_master h₀ h₁ t.unpair.2) subset_rfl
      · refine ⟨t.unpair.1, ?_⟩
        rw [osumEnum_master hMcb'.1 hMcb'.2]
        exact Set.subset_inter subset_rfl (osumEnum_subset_master h₀ h₁ t.unpair.1)
      · obtain ⟨j, hj⟩ := hc0
        have hRHSmem : V₀.mem (P₀.X t.unpair.1.unpair.2 ∩ P₀.X t.unpair.2.unpair.2) :=
          V₀.inter_mem (P₀.mem_X _) (P₀.mem_X _) (P₀.mem_X j) hj
        have hRHSne : P₀.X t.unpair.1.unpair.2 ∩ P₀.X t.unpair.2.unpair.2 ≠ V₀.master :=
          inter_ne_master_left (P₀.mem_X _) hLa'.2
        have hjne : P₀.X j ≠ V₀.master := fun he =>
          hRHSne (Set.Subset.antisymm (V₀.sub_master hRHSmem) (he ▸ hj))
        refine ⟨Nat.pair 0 j, ?_⟩
        rw [osumEnum_left (by rw [unpair_pair_fst, unpair_pair_snd]; exact ⟨rfl, hjne⟩),
          unpair_pair_snd, osumEnum_left hLa', osumEnum_left hLb', inj₀_inter, inj₀_subset_inj₀]
        exact hj
      · obtain ⟨j, hj⟩ := hc1
        have hRHSmem : V₁.mem (P₁.X t.unpair.1.unpair.2 ∩ P₁.X t.unpair.2.unpair.2) :=
          V₁.inter_mem (P₁.mem_X _) (P₁.mem_X _) (P₁.mem_X j) hj
        have hRHSne : P₁.X t.unpair.1.unpair.2 ∩ P₁.X t.unpair.2.unpair.2 ≠ V₁.master :=
          inter_ne_master_right (P₁.mem_X _) hRa'.2
        have hjne : P₁.X j ≠ V₁.master := fun he =>
          hRHSne (Set.Subset.antisymm (V₁.sub_master hRHSmem) (he ▸ hj))
        refine ⟨Nat.pair 1 j, ?_⟩
        rw [osumEnum_right (by rw [unpair_pair_fst, unpair_pair_snd]; exact ⟨rfl, hjne⟩),
          unpair_pair_snd, osumEnum_right hRa', osumEnum_right hRb', inj₁_inter, inj₁_subset_inj₁]
        exact hj

include h₀ h₁ in
/-- **Exercise 7.15 (Scott 1981, PRG-19) — the coalesced sum `𝒟₀ ⊕ 𝒟₁` is effectively given.**
(Scott's Definition 7.1; the only classical input is the enumeration's properness branch.) -/
theorem osum_isEffectivelyGivenS (e₀ : V₀.IsEffectivelyGiven) (e₁ : V₁.IsEffectivelyGiven) :
    (osum h₀ h₁).IsEffectivelyGivenS := by
  obtain ⟨Q₀⟩ := e₀; obtain ⟨Q₁⟩ := e₁
  exact ⟨osumPresentation h₀ h₁ (P₀ := Q₀) (P₁ := Q₁)⟩

/-! ### The appropriate combinators for `⊕`: injections `in₀`/`in₁` and projections `out₀`/`out₁`.

These are the coalesced analogues of Theorem 7.4's separated-sum combinators (`Exercise318`'s
`inMap₀`/`outMap₀`), re-housed over `osum` (whose members are the *proper* tagged copies + master).
Each is a genuine `ApproximableMap` and is **computable** (`IsComputableMapS`): the neighbourhood
relations decode, tag-by-tag, to slices of the components' `incl_computable` together with the
recursively-decidable properness tests `proper₀_dec`/`proper₁_dec`. -/

variable {h₀ h₁}

/-- An `osum`-member containing `inj₀ Δ₀` is forced to be the master (the bottom-collapse: the only
proper copy `⊇ inj₀ Δ₀` would need `Δ₀ ⊆ X` with `X ≠ Δ₀`). -/
theorem osum_eq_master_of_inj₀master {W : Set (Option (α ⊕ β))} (hW : (osum h₀ h₁).mem W)
    (hsub : inj₀ V₀.master ⊆ W) : W = sumMaster V₀ V₁ := by
  rcases hW with rfl | ⟨X', hX', hX'ne, rfl⟩ | ⟨Y', hY', -, rfl⟩
  · rfl
  · exact absurd (Set.Subset.antisymm (V₀.sub_master hX') (inj₀_subset_inj₀.mp hsub)) hX'ne
  · obtain ⟨a, ha⟩ := h₀ V₀.master V₀.master_mem
    exact absurd (hsub (il_mem_inj₀.mpr ha)) il_mem_inj₁

theorem osum_eq_master_of_inj₁master {W : Set (Option (α ⊕ β))} (hW : (osum h₀ h₁).mem W)
    (hsub : inj₁ V₁.master ⊆ W) : W = sumMaster V₀ V₁ := by
  rcases hW with rfl | ⟨X', hX', -, rfl⟩ | ⟨Y', hY', hY'ne, rfl⟩
  · rfl
  · obtain ⟨b, hb⟩ := h₁ V₁.master V₁.master_mem
    exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
  · exact absurd (Set.Subset.antisymm (V₁.sub_master hY') (inj₁_subset_inj₁.mp hsub)) hY'ne

/-- **Coalesced left injection `in₀ : 𝒟₀ → 𝒟₀ ⊕ 𝒟₁`**, `X (in₀) W ↔ inj₀ X ⊆ W`. -/
def osumInMap₀ : ApproximableMap V₀ (osum h₀ h₁) where
  rel X W := V₀.mem X ∧ (osum h₀ h₁).mem W ∧ inj₀ X ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V₀.master_mem, (osum h₀ h₁).master_mem, inj₀_subset_sumMaster V₀.master_mem⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hsub⟩ ⟨-, hW', hsub'⟩
    refine ⟨hX, ?_, Set.subset_inter hsub hsub'⟩
    by_cases hXm : X = V₀.master
    · subst hXm
      rw [osum_eq_master_of_inj₀master hW hsub, osum_eq_master_of_inj₀master hW' hsub',
        Set.inter_self]
      exact (osum h₀ h₁).master_mem
    · exact (osum h₀ h₁).inter_mem hW hW' (Or.inr (Or.inl ⟨X, hX, hXm, rfl⟩))
        (Set.subset_inter hsub hsub')
  mono := by
    rintro X X' W W' ⟨_, _, hsub⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', (inj₀_subset_inj₀.mpr hX'X).trans (hsub.trans hWW')⟩

/-- **Coalesced right injection `in₁ : 𝒟₁ → 𝒟₀ ⊕ 𝒟₁`**. -/
def osumInMap₁ : ApproximableMap V₁ (osum h₀ h₁) where
  rel Y W := V₁.mem Y ∧ (osum h₀ h₁).mem W ∧ inj₁ Y ⊆ W
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V₁.master_mem, (osum h₀ h₁).master_mem, inj₁_subset_sumMaster V₁.master_mem⟩
  inter_right := by
    rintro Y W W' ⟨hY, hW, hsub⟩ ⟨-, hW', hsub'⟩
    refine ⟨hY, ?_, Set.subset_inter hsub hsub'⟩
    by_cases hYm : Y = V₁.master
    · subst hYm
      rw [osum_eq_master_of_inj₁master hW hsub, osum_eq_master_of_inj₁master hW' hsub',
        Set.inter_self]
      exact (osum h₀ h₁).master_mem
    · exact (osum h₀ h₁).inter_mem hW hW' (Or.inr (Or.inr ⟨Y, hY, hYm, rfl⟩))
        (Set.subset_inter hsub hsub')
  mono := by
    rintro Y Y' W W' ⟨_, _, hsub⟩ hY'Y hWW' hY' hW'
    exact ⟨hY', hW', (inj₁_subset_inj₁.mpr hY'Y).trans (hsub.trans hWW')⟩

/-- **Coalesced left projection `out₀ : 𝒟₀ ⊕ 𝒟₁ → 𝒟₀`**, `W (out₀) X ↔ leftPart W ⊆ X`. -/
def osumOutMap₀ : ApproximableMap (osum h₀ h₁) V₀ where
  rel W X := (osum h₀ h₁).mem W ∧ V₀.mem X ∧ leftPart V₀ W ⊆ X
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(osum h₀ h₁).master_mem, V₀.master_mem, (leftPart_sumMaster V₀ V₁).subset⟩
  inter_right := by
    rintro W X X' ⟨hW, hX, hsub⟩ ⟨-, hX', hsub'⟩
    refine ⟨hW, V₀.inter_mem hX hX' ?_ (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
    rcases hW with rfl | ⟨A, hA, -, rfl⟩ | ⟨B, hB, -, rfl⟩
    · rw [leftPart_sumMaster]; exact V₀.master_mem
    · rw [leftPart_inj₀]; exact hA
    · rw [leftPart_inj₁ V₀ (h₁ B hB)]; exact V₀.master_mem
  mono := by
    rintro W W' X X' ⟨_, _, hsub⟩ hW'W hXX' hW' hX'
    exact ⟨hW', hX', (leftPart_mono V₀ hW'W).trans (hsub.trans hXX')⟩

/-- **Coalesced right projection `out₁ : 𝒟₀ ⊕ 𝒟₁ → 𝒟₁`**. -/
def osumOutMap₁ : ApproximableMap (osum h₀ h₁) V₁ where
  rel W Y := (osum h₀ h₁).mem W ∧ V₁.mem Y ∧ rightPart V₁ W ⊆ Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(osum h₀ h₁).master_mem, V₁.master_mem, (rightPart_sumMaster V₀ V₁).subset⟩
  inter_right := by
    rintro W Y Y' ⟨hW, hY, hsub⟩ ⟨-, hY', hsub'⟩
    refine ⟨hW, V₁.inter_mem hY hY' ?_ (Set.subset_inter hsub hsub'), Set.subset_inter hsub hsub'⟩
    rcases hW with rfl | ⟨A, hA, -, rfl⟩ | ⟨B, hB, -, rfl⟩
    · rw [rightPart_sumMaster]; exact V₁.master_mem
    · rw [rightPart_inj₀ V₁ (h₀ A hA)]; exact V₁.master_mem
    · rw [rightPart_inj₁]; exact hB
  mono := by
    rintro W W' Y Y' ⟨_, _, hsub⟩ hW'W hYY' hW' hY'
    exact ⟨hW', hY', (rightPart_mono V₁ hW'W).trans (hsub.trans hYY')⟩

variable (P₀ P₁)

@[simp] theorem osumPresentation_X (t : ℕ) :
    (osumPresentation h₀ h₁ (P₀ := P₀) (P₁ := P₁)).X t = osumEnum P₀ P₁ t := rfl

/-- **`in₀` is computable.** `X⁰ₙ (in₀) (osumEnum m)` decodes to: `m` a proper left copy with
`X⁰ₙ ⊆ X⁰_{m.2}`, or `m` the master (`inj₀` of a proper neighbourhood always sits under the master);
the proper-right case is impossible (`inj₀` of a nonempty set is not `⊆ inj₁`). -/
theorem osumInMap₀_isComputable :
    IsComputableMapS P₀.toScott (osumPresentation h₀ h₁ (P₀ := P₀) (P₁ := P₁)) osumInMap₀ := by
  have hT0 : RecDecidable (fun t => t.unpair.2.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 0)
  have hT1 : RecDecidable (fun t => t.unpair.2.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)
  have hP0 : RecDecidable (fun t => P₀.X t.unpair.2.unpair.2 ≠ V₀.master) :=
    (proper₀_dec P₀).comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hP1 : RecDecidable (fun t => P₁.X t.unpair.2.unpair.2 ≠ V₁.master) :=
    (proper₁_dec P₁).comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hInc : RecDecidable (fun t => P₀.X t.unpair.1 ⊆ P₀.X t.unpair.2.unpair.2) :=
    RecDecidable.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (P₀.incl_computable.comp (Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)))
  refine (RecDecidable.of_iff (fun t => ?_)
    ((hT0.and (hP0.and hInc)).or ((hT0.and hP0).not.and (hT1.and hP1).not))).re
  show (osumInMap₀ (h₀ := h₀) (h₁ := h₁)).rel (P₀.X t.unpair.1) (osumEnum P₀ P₁ t.unpair.2) ↔ _
  rw [show (osumInMap₀ (h₀ := h₀) (h₁ := h₁)).rel (P₀.X t.unpair.1) (osumEnum P₀ P₁ t.unpair.2)
      ↔ inj₀ (P₀.X t.unpair.1) ⊆ osumEnum P₀ P₁ t.unpair.2 from
    ⟨fun h => h.2.2, fun h => ⟨P₀.mem_X _, osumEnum_mem h₀ h₁ _, h⟩⟩]
  by_cases hL : t.unpair.2.unpair.1 = 0 ∧ P₀.X t.unpair.2.unpair.2 ≠ V₀.master
  · rw [osumEnum_left hL, inj₀_subset_inj₀]
    exact ⟨fun h => Or.inl ⟨hL.1, hL.2, h⟩,
      fun h => h.elim (fun h => h.2.2) (fun h => absurd hL h.1)⟩
  · by_cases hR : t.unpair.2.unpair.1 = 1 ∧ P₁.X t.unpair.2.unpair.2 ≠ V₁.master
    · rw [osumEnum_right hR]
      refine ⟨fun h => ?_, fun h => h.elim (fun h => absurd ⟨h.1, h.2.1⟩ hL)
        (fun h => absurd hR h.2)⟩
      obtain ⟨a, ha⟩ := h₀ _ (P₀.mem_X t.unpair.1)
      exact absurd (h (il_mem_inj₀.mpr ha)) il_mem_inj₁
    · rw [osumEnum_master hL hR]
      exact ⟨fun _ => Or.inr ⟨hL, hR⟩, fun _ => inj₀_subset_sumMaster (P₀.mem_X _)⟩

/-- **`in₁` is computable.** Symmetric to `in₀`. -/
theorem osumInMap₁_isComputable :
    IsComputableMapS P₁.toScott (osumPresentation h₀ h₁ (P₀ := P₀) (P₁ := P₁)) osumInMap₁ := by
  have hT0 : RecDecidable (fun t => t.unpair.2.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 0)
  have hT1 : RecDecidable (fun t => t.unpair.2.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)
  have hP0 : RecDecidable (fun t => P₀.X t.unpair.2.unpair.2 ≠ V₀.master) :=
    (proper₀_dec P₀).comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hP1 : RecDecidable (fun t => P₁.X t.unpair.2.unpair.2 ≠ V₁.master) :=
    (proper₁_dec P₁).comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have hInc : RecDecidable (fun t => P₁.X t.unpair.1 ⊆ P₁.X t.unpair.2.unpair.2) :=
    RecDecidable.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (P₁.incl_computable.comp (Nat.Primrec.left.pair (Nat.Primrec.right.comp Nat.Primrec.right)))
  refine (RecDecidable.of_iff (fun t => ?_)
    ((hT1.and (hP1.and hInc)).or ((hT0.and hP0).not.and (hT1.and hP1).not))).re
  show (osumInMap₁ (h₀ := h₀) (h₁ := h₁)).rel (P₁.X t.unpair.1) (osumEnum P₀ P₁ t.unpair.2) ↔ _
  rw [show (osumInMap₁ (h₀ := h₀) (h₁ := h₁)).rel (P₁.X t.unpair.1) (osumEnum P₀ P₁ t.unpair.2)
      ↔ inj₁ (P₁.X t.unpair.1) ⊆ osumEnum P₀ P₁ t.unpair.2 from
    ⟨fun h => h.2.2, fun h => ⟨P₁.mem_X _, osumEnum_mem h₀ h₁ _, h⟩⟩]
  by_cases hL : t.unpair.2.unpair.1 = 0 ∧ P₀.X t.unpair.2.unpair.2 ≠ V₀.master
  · rw [osumEnum_left hL]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨b, hb⟩ := h₁ _ (P₁.mem_X t.unpair.1)
      exact absurd (h (ir_mem_inj₁.mpr hb)) ir_mem_inj₀
    · rcases h with ⟨h1, -⟩ | ⟨hn0, -⟩
      · rw [hL.1] at h1; exact absurd h1 (by decide)
      · exact absurd hL hn0
  · by_cases hR : t.unpair.2.unpair.1 = 1 ∧ P₁.X t.unpair.2.unpair.2 ≠ V₁.master
    · rw [osumEnum_right hR, inj₁_subset_inj₁]
      exact ⟨fun h => Or.inl ⟨hR.1, hR.2, h⟩,
        fun h => h.elim (fun h => h.2.2) (fun h => absurd hR h.2)⟩
    · rw [osumEnum_master hL hR]
      exact ⟨fun _ => Or.inr ⟨hL, hR⟩, fun _ => inj₁_subset_sumMaster (P₁.mem_X _)⟩

/-- **`out₀` is computable.** `(osumEnum n) (out₀) X⁰_m ↔ leftPart (osumEnum n) ⊆ X⁰_m`; the left
part is `X⁰_{n.2}` on a proper left copy and `Δ₀` on a right copy / the master, so the relation is
`incl` against either `n.2` or the master index `k₀` (`X⁰_{k₀} = Δ₀`). -/
theorem osumOutMap₀_isComputable :
    IsComputableMapS (osumPresentation h₀ h₁ (P₀ := P₀) (P₁ := P₁)) P₀.toScott osumOutMap₀ := by
  obtain ⟨k0, hk0⟩ := P₀.surj V₀.master_mem
  have hT0 : RecDecidable (fun t => t.unpair.1.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 0)
  have hP0 : RecDecidable (fun t => P₀.X t.unpair.1.unpair.2 ≠ V₀.master) :=
    (proper₀_dec P₀).comp (Nat.Primrec.right.comp Nat.Primrec.left)
  have hIncL : RecDecidable (fun t => P₀.X t.unpair.1.unpair.2 ⊆ P₀.X t.unpair.2) :=
    RecDecidable.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (P₀.incl_computable.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right))
  have hIncM : RecDecidable (fun t => V₀.master ⊆ P₀.X t.unpair.2) :=
    RecDecidable.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd, hk0])
      (P₀.incl_computable.comp ((Nat.Primrec.const k0).pair Nat.Primrec.right))
  refine (RecDecidable.of_iff (fun t => ?_)
    ((hT0.and (hP0.and hIncL)).or ((hT0.and hP0).not.and hIncM))).re
  show (osumOutMap₀ (h₀ := h₀) (h₁ := h₁)).rel (osumEnum P₀ P₁ t.unpair.1) (P₀.X t.unpair.2) ↔ _
  rw [show (osumOutMap₀ (h₀ := h₀) (h₁ := h₁)).rel (osumEnum P₀ P₁ t.unpair.1) (P₀.X t.unpair.2)
      ↔ leftPart V₀ (osumEnum P₀ P₁ t.unpair.1) ⊆ P₀.X t.unpair.2 from
    ⟨fun h => h.2.2, fun h => ⟨osumEnum_mem h₀ h₁ _, P₀.mem_X _, h⟩⟩]
  by_cases hL : t.unpair.1.unpair.1 = 0 ∧ P₀.X t.unpair.1.unpair.2 ≠ V₀.master
  · rw [osumEnum_left hL, leftPart_inj₀]
    exact ⟨fun h => Or.inl ⟨hL.1, hL.2, h⟩,
      fun h => h.elim (fun h => h.2.2) (fun h => absurd hL h.1)⟩
  · by_cases hR : t.unpair.1.unpair.1 = 1 ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master
    · rw [osumEnum_right hR, leftPart_inj₁ V₀ (h₁ _ (P₁.mem_X _))]
      exact ⟨fun h => Or.inr ⟨hL, h⟩,
        fun h => h.elim (fun h => absurd ⟨h.1, h.2.1⟩ hL) (fun h => h.2)⟩
    · rw [osumEnum_master hL hR, leftPart_sumMaster]
      exact ⟨fun h => Or.inr ⟨hL, h⟩,
        fun h => h.elim (fun h => absurd ⟨h.1, h.2.1⟩ hL) (fun h => h.2)⟩

/-- **`out₁` is computable.** Symmetric to `out₀` via `rightPart`. -/
theorem osumOutMap₁_isComputable :
    IsComputableMapS (osumPresentation h₀ h₁ (P₀ := P₀) (P₁ := P₁)) P₁.toScott osumOutMap₁ := by
  obtain ⟨k1, hk1⟩ := P₁.surj V₁.master_mem
  have hT1 : RecDecidable (fun t => t.unpair.1.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 1)
  have hP1 : RecDecidable (fun t => P₁.X t.unpair.1.unpair.2 ≠ V₁.master) :=
    (proper₁_dec P₁).comp (Nat.Primrec.right.comp Nat.Primrec.left)
  have hIncR : RecDecidable (fun t => P₁.X t.unpair.1.unpair.2 ⊆ P₁.X t.unpair.2) :=
    RecDecidable.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (P₁.incl_computable.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair Nat.Primrec.right))
  have hIncM : RecDecidable (fun t => V₁.master ⊆ P₁.X t.unpair.2) :=
    RecDecidable.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd, hk1])
      (P₁.incl_computable.comp ((Nat.Primrec.const k1).pair Nat.Primrec.right))
  refine (RecDecidable.of_iff (fun t => ?_)
    ((hT1.and (hP1.and hIncR)).or ((hT1.and hP1).not.and hIncM))).re
  show (osumOutMap₁ (h₀ := h₀) (h₁ := h₁)).rel (osumEnum P₀ P₁ t.unpair.1) (P₁.X t.unpair.2) ↔ _
  rw [show (osumOutMap₁ (h₀ := h₀) (h₁ := h₁)).rel (osumEnum P₀ P₁ t.unpair.1) (P₁.X t.unpair.2)
      ↔ rightPart V₁ (osumEnum P₀ P₁ t.unpair.1) ⊆ P₁.X t.unpair.2 from
    ⟨fun h => h.2.2, fun h => ⟨osumEnum_mem h₀ h₁ _, P₁.mem_X _, h⟩⟩]
  by_cases hR : t.unpair.1.unpair.1 = 1 ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master
  · rw [osumEnum_right hR, rightPart_inj₁]
    exact ⟨fun h => Or.inl ⟨hR.1, hR.2, h⟩,
      fun h => h.elim (fun h => h.2.2) (fun h => absurd hR h.1)⟩
  · by_cases hL : t.unpair.1.unpair.1 = 0 ∧ P₀.X t.unpair.1.unpair.2 ≠ V₀.master
    · rw [osumEnum_left hL, rightPart_inj₀ V₁ (h₀ _ (P₀.mem_X _))]
      exact ⟨fun h => Or.inr ⟨hR, h⟩,
        fun h => h.elim (fun h => absurd ⟨h.1, h.2.1⟩ hR) (fun h => h.2)⟩
    · rw [osumEnum_master hL hR, rightPart_sumMaster]
      exact ⟨fun h => Or.inr ⟨hR, h⟩,
        fun h => h.elim (fun h => absurd ⟨h.1, h.2.1⟩ hR) (fun h => h.2)⟩

/-! ### The appropriate combinator for `⊕`: the functorial action `f ⊕ g`.

`osumMap f g : 𝒟₀ ⊕ 𝒟₁ → 𝒟₀' ⊕ 𝒟₁'` is the coalesced analogue of Theorem 7.4's `f + g` (`sumMap`).
The coalesced relation additionally forces the image copy to be *proper* (`Y' ≠ Δ'`); otherwise the
strict collapse routes to the master. It is a genuine `ApproximableMap` and is **computable**. -/

section CoalescedFunctor

variable {α' β' : Type*} {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
  (h₀' : ∀ X, V₀'.mem X → X.Nonempty) (h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty)

/-- An `osum`-member `⊆ inj₀ X` is a *proper* left copy. -/
theorem osum_mem_subset_inj₀ {W : Set (Option (α ⊕ β))} {X : Set α}
    (hW : (osum h₀ h₁).mem W) (hsub : W ⊆ inj₀ X) :
    ∃ X₂, V₀.mem X₂ ∧ X₂ ≠ V₀.master ∧ W = inj₀ X₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, hne, rfl⟩ | ⟨Y₂, hY₂, hne, rfl⟩
  · exact absurd (hsub none_mem_sumMaster) none_mem_inj₀
  · exact ⟨X₂, hX₂, hne, rfl⟩
  · obtain ⟨b, hb⟩ := h₁ Y₂ hY₂; exact absurd (hsub (ir_mem_inj₁.mpr hb)) ir_mem_inj₀

theorem osum_mem_subset_inj₁ {W : Set (Option (α ⊕ β))} {Y : Set β}
    (hW : (osum h₀ h₁).mem W) (hsub : W ⊆ inj₁ Y) :
    ∃ Y₂, V₁.mem Y₂ ∧ Y₂ ≠ V₁.master ∧ W = inj₁ Y₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, hne, rfl⟩ | ⟨Y₂, hY₂, hne, rfl⟩
  · exact absurd (hsub none_mem_sumMaster) none_mem_inj₁
  · obtain ⟨a, ha⟩ := h₀ X₂ hX₂; exact absurd (hsub (il_mem_inj₀.mpr ha)) il_mem_inj₁
  · exact ⟨Y₂, hY₂, hne, rfl⟩

/-- **The coalesced sum of two maps `f ⊕ g : 𝒟₀ ⊕ 𝒟₁ → 𝒟₀' ⊕ 𝒟₁'`.** -/
def osumMap (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    ApproximableMap (osum h₀ h₁) (osum h₀' h₁') where
  rel W W' := (osum h₀ h₁).mem W ∧ (osum h₀' h₁').mem W' ∧
    (W' = sumMaster V₀' V₁' ∨
      (∃ X Y', W = inj₀ X ∧ W' = inj₀ Y' ∧ Y' ≠ V₀'.master ∧ f.rel X Y') ∨
      (∃ Y Y', W = inj₁ Y ∧ W' = inj₁ Y' ∧ Y' ≠ V₁'.master ∧ g.rel Y Y'))
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(osum h₀ h₁).master_mem, (osum h₀' h₁').master_mem, Or.inl rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ ⟨hW, hW'₁, hd₁⟩ ⟨-, hW'₂, hd₂⟩
    have hmem : ∀ W'' : Set (Option (α' ⊕ β')),
        (W'' = sumMaster V₀' V₁' ∨
          (∃ X Y', W = inj₀ X ∧ W'' = inj₀ Y' ∧ Y' ≠ V₀'.master ∧ f.rel X Y') ∨
          (∃ Y Y', W = inj₁ Y ∧ W'' = inj₁ Y' ∧ Y' ≠ V₁'.master ∧ g.rel Y Y')) →
          (osum h₀' h₁').mem W'' := by
      rintro W'' (rfl | ⟨_, Y', _, rfl, hY'ne, hf⟩ | ⟨_, Y', _, rfl, hY'ne, hg⟩)
      · exact (osum h₀' h₁').master_mem
      · exact Or.inr (Or.inl ⟨Y', f.rel_cod hf, hY'ne, rfl⟩)
      · exact Or.inr (Or.inr ⟨Y', g.rel_cod hg, hY'ne, rfl⟩)
    have key : W'₁ ∩ W'₂ = sumMaster V₀' V₁' ∨
        (∃ X Y', W = inj₀ X ∧ W'₁ ∩ W'₂ = inj₀ Y' ∧ Y' ≠ V₀'.master ∧ f.rel X Y') ∨
        (∃ Y Y', W = inj₁ Y ∧ W'₁ ∩ W'₂ = inj₁ Y' ∧ Y' ≠ V₁'.master ∧ g.rel Y Y') := by
      rcases hd₁ with rfl | ⟨X, Y'₁, hWX₁, rfl, hY'₁ne, hf₁⟩ | ⟨Y, Y'₁, hWY₁, rfl, hY'₁ne, hg₁⟩
      · have he : sumMaster V₀' V₁' ∩ W'₂ = W'₂ :=
          Set.inter_eq_self_of_subset_right
            ((osum h₀' h₁').sub_master hW'₂ : W'₂ ⊆ sumMaster V₀' V₁')
        rw [he]; exact hd₂
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hY'₂ne, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hY'₂ne, hg₂⟩
        · rw [Set.inter_eq_left.mpr (inj₀_subset_sumMaster (f.rel_cod hf₁))]
          exact Or.inr (Or.inl ⟨X, Y'₁, hWX₁, rfl, hY'₁ne, hf₁⟩)
        · obtain rfl : X = X' := inj₀_injective (hWX₁.symm.trans hWX₂)
          rw [inj₀_inter]
          exact Or.inr (Or.inl ⟨X, Y'₁ ∩ Y'₂, hWX₁, rfl,
            inter_ne_master_left (f.rel_cod hf₁) hY'₁ne, f.inter_right hf₁ hf₂⟩)
        · exact absurd (hWX₁.symm.trans hWY₂)
            (fun h => not_inj₀_subset_inj₁ (h₀ X (f.rel_dom hf₁)) h.subset)
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hY'₂ne, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hY'₂ne, hg₂⟩
        · rw [Set.inter_eq_left.mpr (inj₁_subset_sumMaster (g.rel_cod hg₁))]
          exact Or.inr (Or.inr ⟨Y, Y'₁, hWY₁, rfl, hY'₁ne, hg₁⟩)
        · exact absurd (hWY₁.symm.trans hWX₂)
            (fun h => not_inj₁_subset_inj₀ (h₁ Y (g.rel_dom hg₁)) h.subset)
        · obtain rfl : Y = Y' := inj₁_injective (hWY₁.symm.trans hWY₂)
          rw [inj₁_inter]
          exact Or.inr (Or.inr ⟨Y, Y'₁ ∩ Y'₂, hWY₁, rfl,
            inter_ne_master_left (g.rel_cod hg₁) hY'₁ne, g.inter_right hg₁ hg₂⟩)
    exact ⟨hW, hmem _ key, key⟩
  mono := by
    rintro W W₂ W' W'₂ ⟨hW, hW', hd⟩ hW₂W hW'W'₂ hW₂mem hW'₂mem
    refine ⟨hW₂mem, hW'₂mem, ?_⟩
    rcases hd with rfl | ⟨X, Y', rfl, rfl, hY'ne, hf⟩ | ⟨Y, Y', rfl, rfl, hY'ne, hg⟩
    · left; exact Set.Subset.antisymm ((osum h₀' h₁').sub_master hW'₂mem) hW'W'₂
    · obtain ⟨X₂, hX₂, hX₂ne, rfl⟩ := osum_mem_subset_inj₀ hW₂mem hW₂W
      have hXX₂ : X₂ ⊆ X := inj₀_subset_inj₀.mp hW₂W
      rcases hW'₂mem with rfl | ⟨Y'₂, hY'₂, hY'₂ne, rfl⟩ | ⟨Z'₂, hZ'₂, hZ'₂ne, rfl⟩
      · left; rfl
      · exact Or.inr (Or.inl ⟨X₂, Y'₂, rfl, rfl, hY'₂ne,
          f.mono hf hXX₂ (inj₀_subset_inj₀.mp hW'W'₂) hX₂ hY'₂⟩)
      · exact (not_inj₀_subset_inj₁ (h₀' Y' (f.rel_cod hf)) hW'W'₂).elim
    · obtain ⟨Y₂, hY₂, hY₂ne, rfl⟩ := osum_mem_subset_inj₁ hW₂mem hW₂W
      have hYY₂ : Y₂ ⊆ Y := inj₁_subset_inj₁.mp hW₂W
      rcases hW'₂mem with rfl | ⟨X'₂, hX'₂, hX'₂ne, rfl⟩ | ⟨Y'₂, hY'₂, hY'₂ne, rfl⟩
      · left; rfl
      · exact (not_inj₁_subset_inj₀ (h₁' Y' (g.rel_cod hg)) hW'W'₂).elim
      · exact Or.inr (Or.inr ⟨Y₂, Y'₂, rfl, rfl, hY'₂ne,
          g.mono hg hYY₂ (inj₁_subset_inj₁.mp hW'W'₂) hY₂ hY'₂⟩)

/-- **`f ⊕ g` is computable.** The relation `(osumEnum n) (f⊕g) (osumEnum' m)` decodes by tags: `m`
improper (master absorbs), or `m`/`n` both proper left copies with `f`'s r.e. relation, or both
proper right copies with `g`'s. -/
theorem osumMap_isComputable (P₀' : ComputablePresentation V₀') (P₁' : ComputablePresentation V₁')
    {f : ApproximableMap V₀ V₀'} {g : ApproximableMap V₁ V₁'}
    (hf : IsComputableMapS P₀.toScott P₀'.toScott f)
    (hg : IsComputableMapS P₁.toScott P₁'.toScott g) :
    IsComputableMapS (osumPresentation h₀ h₁ (P₀ := P₀) (P₁ := P₁))
      (osumPresentation h₀' h₁' (P₀ := P₀') (P₁ := P₁')) (osumMap h₀' h₁' f g) := by
  have mT0 : RecDecidable (fun t => t.unpair.2.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 0)
  have mT1 : RecDecidable (fun t => t.unpair.2.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.right) (Nat.Primrec.const 1)
  have mP0 : RecDecidable (fun t => P₀'.X t.unpair.2.unpair.2 ≠ V₀'.master) :=
    (proper₀_dec P₀').comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have mP1 : RecDecidable (fun t => P₁'.X t.unpair.2.unpair.2 ≠ V₁'.master) :=
    (proper₁_dec P₁').comp (Nat.Primrec.right.comp Nat.Primrec.right)
  have nT0 : RecDecidable (fun t => t.unpair.1.unpair.1 = 0) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 0)
  have nT1 : RecDecidable (fun t => t.unpair.1.unpair.1 = 1) :=
    RecDecidable.natEq (Nat.Primrec.left.comp Nat.Primrec.left) (Nat.Primrec.const 1)
  have nP0 : RecDecidable (fun t => P₀.X t.unpair.1.unpair.2 ≠ V₀.master) :=
    (proper₀_dec P₀).comp (Nat.Primrec.right.comp Nat.Primrec.left)
  have nP1 : RecDecidable (fun t => P₁.X t.unpair.1.unpair.2 ≠ V₁.master) :=
    (proper₁_dec P₁).comp (Nat.Primrec.right.comp Nat.Primrec.left)
  have Hf : REPred (fun t => f.rel (P₀.toScott.X t.unpair.1.unpair.2)
      (P₀'.toScott.X t.unpair.2.unpair.2)) :=
    REPred.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hf.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair
        (Nat.Primrec.right.comp Nat.Primrec.right)))
  have Hg : REPred (fun t => g.rel (P₁.toScott.X t.unpair.1.unpair.2)
      (P₁'.toScott.X t.unpair.2.unpair.2)) :=
    REPred.of_iff (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])
      (hg.comp ((Nat.Primrec.right.comp Nat.Primrec.left).pair
        (Nat.Primrec.right.comp Nat.Primrec.right)))
  have hImp : RecDecidable (fun t => ¬(t.unpair.2.unpair.1 = 0 ∧ P₀'.X t.unpair.2.unpair.2 ≠ V₀'.master)
      ∧ ¬(t.unpair.2.unpair.1 = 1 ∧ P₁'.X t.unpair.2.unpair.2 ≠ V₁'.master)) :=
    (mT0.and mP0).not.and (mT1.and mP1).not
  refine REPred.of_iff (fun t => ?_)
    ((hImp.re).or ((((mT0.and mP0).and (nT0.and nP0)).re.and Hf).or
      (((mT1.and mP1).and (nT1.and nP1)).re.and Hg)))
  show (osumMap h₀' h₁' f g).rel (osumEnum P₀ P₁ t.unpair.1) (osumEnum P₀' P₁' t.unpair.2) ↔ _
  by_cases hm0 : t.unpair.2.unpair.1 = 0 ∧ P₀'.X t.unpair.2.unpair.2 ≠ V₀'.master
  · rw [osumEnum_left hm0]
    constructor
    · rintro ⟨-, -, hd⟩
      rcases hd with hmaster | ⟨X, Y', hnX, hW'eq, -, hf⟩ | ⟨Y, Y', -, hW'eq, -, -⟩
      · exact absurd hmaster inj₀_ne_sumMaster
      · obtain rfl : Y' = P₀'.X t.unpair.2.unpair.2 := (inj₀_injective hW'eq).symm
        by_cases hn0 : t.unpair.1.unpair.1 = 0 ∧ P₀.X t.unpair.1.unpair.2 ≠ V₀.master
        · rw [osumEnum_left hn0] at hnX
          obtain rfl : P₀.X t.unpair.1.unpair.2 = X := inj₀_injective hnX
          exact Or.inr (Or.inl ⟨⟨hm0, hn0⟩, hf⟩)
        · exfalso
          by_cases hn1 : t.unpair.1.unpair.1 = 1 ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master
          · rw [osumEnum_right hn1] at hnX
            obtain ⟨b, hb⟩ := h₁ _ (P₁.mem_X _)
            exact ir_mem_inj₀ (hnX ▸ ir_mem_inj₁.mpr hb)
          · rw [osumEnum_master hn0 hn1] at hnX
            exact none_mem_inj₀ (hnX ▸ none_mem_sumMaster)
      · obtain ⟨a, ha⟩ := h₀' _ (P₀'.mem_X _)
        exact (il_mem_inj₁ (hW'eq ▸ il_mem_inj₀.mpr ha)).elim
    · rintro (himp | ⟨⟨-, hn0⟩, hf⟩ | ⟨⟨hm1, -⟩, -⟩)
      · exact absurd hm0 himp.1
      · exact ⟨osumEnum_mem h₀ h₁ _, Or.inr (Or.inl ⟨_, P₀'.mem_X _, hm0.2, rfl⟩),
          Or.inr (Or.inl ⟨_, _, osumEnum_left hn0, rfl, hm0.2, hf⟩)⟩
      · obtain ⟨he, -⟩ := hm1; rw [hm0.1] at he; exact absurd he (by decide)
  · by_cases hm1 : t.unpair.2.unpair.1 = 1 ∧ P₁'.X t.unpair.2.unpair.2 ≠ V₁'.master
    · rw [osumEnum_right hm1]
      constructor
      · rintro ⟨-, -, hd⟩
        rcases hd with hmaster | ⟨X, Y', -, hW'eq, -, -⟩ | ⟨Y, Y', hnY, hW'eq, -, hg⟩
        · exact absurd hmaster inj₁_ne_sumMaster
        · exact absurd hW'eq.symm (inj₀_ne_inj₁_of_nonempty (h₁' _ (P₁'.mem_X _)))
        · obtain rfl : Y' = P₁'.X t.unpair.2.unpair.2 := (inj₁_injective hW'eq).symm
          by_cases hn1 : t.unpair.1.unpair.1 = 1 ∧ P₁.X t.unpair.1.unpair.2 ≠ V₁.master
          · rw [osumEnum_right hn1] at hnY
            obtain rfl : P₁.X t.unpair.1.unpair.2 = Y := inj₁_injective hnY
            exact Or.inr (Or.inr ⟨⟨hm1, hn1⟩, hg⟩)
          · exfalso
            by_cases hn0 : t.unpair.1.unpair.1 = 0 ∧ P₀.X t.unpair.1.unpair.2 ≠ V₀.master
            · rw [osumEnum_left hn0] at hnY
              obtain ⟨a, ha⟩ := h₀ _ (P₀.mem_X _)
              exact il_mem_inj₁ (hnY ▸ il_mem_inj₀.mpr ha)
            · rw [osumEnum_master hn0 hn1] at hnY
              exact none_mem_inj₁ (hnY ▸ none_mem_sumMaster)
      · rintro (himp | ⟨⟨hm0', -⟩, -⟩ | ⟨⟨-, hn1⟩, hg⟩)
        · exact absurd hm1 himp.2
        · obtain ⟨he, -⟩ := hm0'; rw [hm1.1] at he; exact absurd he (by decide)
        · exact ⟨osumEnum_mem h₀ h₁ _, Or.inr (Or.inr ⟨_, P₁'.mem_X _, hm1.2, rfl⟩),
            Or.inr (Or.inr ⟨_, _, osumEnum_right hn1, rfl, hm1.2, hg⟩)⟩
    · rw [osumEnum_master hm0 hm1]
      constructor
      · intro _; exact Or.inl ⟨hm0, hm1⟩
      · intro _
        exact ⟨osumEnum_mem h₀ h₁ _, (osum h₀' h₁').master_mem, Or.inl rfl⟩

end CoalescedFunctor

end Coalesced

/-! ## The infinite iterate `D^∞` is effectively given (full `ComputablePresentation`)

`D^∞ = iterSys V` (Exercise 3.16) is *uniform*: a neighbourhood `W` is a member iff every fiber is a
`V`-neighbourhood and all but finitely many fibers equal `Δ`; there is **no deletion/collapse** as in
`⊗`/`⊕`. So it admits the project's *full* `ComputablePresentation` — and **choice-free**.

**Coding.** Given a presentation `P` of `V`, a `D^∞`-code `t : ℕ` codes the finite list of fiber
indices `[i₀, i₁, …, i_{ℓ-1}]` (`Recursive.decodeList`); fiber `j` of the enumerated neighbourhood is
`P.X (iterIdx t j)`, where `iterIdx t j = nthCode t j P.masterIdx` reads the `j`-th list entry,
defaulting to `P.masterIdx` (so all but finitely many fibers are `Δ`). The intersection function is
built by `tabCode`-tabulating `P.inter` coordinate-wise. All three relations and the `inter` function
are primitive recursive because they are bounded computations over `nthCode`/`tabCode`/`P`'s data. -/

section Iterate

open Domain.Recursive

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

/-- The `j`-th fiber **index** of the `D^∞`-code `t`: the `j`-th entry of the coded list, defaulting
to `P.masterIdx` (the master index) beyond the coded length. -/
def iterIdx (t j : ℕ) : ℕ := nthCode t j P.masterIdx

/-- The `D^∞`-enumeration: the neighbourhood whose `j`-th fiber is `P.X (iterIdx t j)`. -/
def iterEnum (t : ℕ) : Set (ℕ × α) := {p | p.2 ∈ P.X (iterIdx P t p.1)}

variable {P}

@[simp] theorem fiber_iterEnum (t j : ℕ) : fiber (iterEnum P t) j = P.X (iterIdx P t j) := rfl

/-- Beyond the coded length the fiber index defaults to the master: if `t ≤ j` then
`iterIdx t j = masterIdx` (the coded list has length `≤ t`). -/
theorem iterIdx_ge {t j : ℕ} (h : t ≤ j) : iterIdx P t j = P.masterIdx := by
  unfold iterIdx
  rw [nthCode_eq, getD_eq_default_cf]
  exact le_trans (decodeList_length_le t) h

theorem iterEnum_mem (t : ℕ) : (iterSys V).mem (iterEnum P t) := by
  refine ⟨fun j => ?_, t, fun j hj => ?_⟩
  · rw [fiber_iterEnum]; exact P.mem_X _
  · rw [fiber_iterEnum, iterIdx_ge hj, P.masterIdx_spec]

/-- **Relation (i) reduces to a bounded coordinate check.** `iterEnum n ∩ iterEnum m = iterEnum k`
iff fiber-wise equality holds for all `j` below `n+m+k` (beyond which every fiber is `Δ`). -/
theorem iterEnum_inter_eq_iff {n m k : ℕ} :
    iterEnum P n ∩ iterEnum P m = iterEnum P k ↔
      ∀ j, j < n + m + k →
        P.X (iterIdx P n j) ∩ P.X (iterIdx P m j) = P.X (iterIdx P k j) := by
  constructor
  · intro h j _
    have := congrArg (fun W => fiber W j) h
    simpa only [fiber_inter, fiber_iterEnum] using this
  · intro h
    apply eq_of_fiber_eq
    intro j
    rw [fiber_inter, fiber_iterEnum, fiber_iterEnum, fiber_iterEnum]
    by_cases hj : j < n + m + k
    · exact h j hj
    · rw [iterIdx_ge (show n ≤ j by omega), iterIdx_ge (show m ≤ j by omega),
        iterIdx_ge (show k ≤ j by omega), P.masterIdx_spec, Set.inter_self]

/-- The coordinate-wise intersection generator: with `s = ⟨j, ⟨n, m⟩⟩`, returns an index of
`X (iterIdx n j) ∩ X (iterIdx m j)` via `P.inter`. -/
def interG (P : ComputablePresentation V) (s : ℕ) : ℕ :=
  P.inter (iterIdx P s.unpair.2.unpair.1 s.unpair.1) (iterIdx P s.unpair.2.unpair.2 s.unpair.1)

/-- The `D^∞`-intersection function: tabulate `interG` over the coordinates `0 … n+m-1`. -/
def iterInter (P : ComputablePresentation V) (n m : ℕ) : ℕ :=
  tabCode (interG P) (Nat.pair (n + m) (Nat.pair n m)) (n + m)

theorem iterInter_idx_lt {n m j : ℕ} (hj : j < n + m) :
    iterIdx P (iterInter P n m) j = P.inter (iterIdx P n j) (iterIdx P m j) := by
  show nthCode (iterInter P n m) j P.masterIdx = _
  rw [iterInter, tabCode_nth_lt hj]
  unfold interG
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem iterInter_idx_ge {n m j : ℕ} (hj : n + m ≤ j) :
    iterIdx P (iterInter P n m) j = P.masterIdx := by
  show nthCode (iterInter P n m) j P.masterIdx = _
  rw [iterInter, tabCode_nth_ge hj]

/-- **Relation (ii) reduces to a bounded coordinate check.** `iterEnum n ∩ iterEnum m` is consistent
iff every coordinate `j < n+m` is consistent in `V`. The witness is `iterInter n m`. -/
theorem iterEnum_cons_iff {n m : ℕ} :
    (∃ k, iterEnum P k ⊆ iterEnum P n ∩ iterEnum P m) ↔
      ∀ j, j < n + m → ∃ i, P.X i ⊆ P.X (iterIdx P n j) ∩ P.X (iterIdx P m j) := by
  constructor
  · rintro ⟨k, hk⟩ j _
    refine ⟨iterIdx P k j, ?_⟩
    have := fiber_mono hk j
    rwa [fiber_inter, fiber_iterEnum, fiber_iterEnum, fiber_iterEnum] at this
  · intro h
    refine ⟨iterInter P n m, ?_⟩
    apply subset_of_fiber_subset
    intro j
    rw [fiber_inter, fiber_iterEnum, fiber_iterEnum, fiber_iterEnum]
    by_cases hj : j < n + m
    · rw [iterInter_idx_lt hj]
      obtain ⟨i, hi⟩ := h j hj
      rw [P.inter_spec ⟨i, hi⟩]
    · rw [iterInter_idx_ge (by omega), iterIdx_ge (show n ≤ j by omega),
        iterIdx_ge (show m ≤ j by omega), P.masterIdx_spec, Set.inter_self]

/-- Build, by induction on `N`, a list of fiber indices reproducing `W`'s first `N` fibers. -/
theorem exists_list_fiber {W : Set (ℕ × α)} (hW : (iterSys V).mem W) :
    ∀ N, ∃ L : List ℕ, L.length = N ∧ ∀ j, j < N → P.X (L.getD j P.masterIdx) = fiber W j := by
  intro N
  induction N with
  | zero => exact ⟨[], rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ N ih =>
    obtain ⟨L, hlen, hL⟩ := ih
    obtain ⟨n, hn⟩ := P.surj (hW.1 N)
    refine ⟨L ++ [n], by simp [List.length_append, hlen], fun j hj => ?_⟩
    by_cases h : j < N
    · rw [getD_append_cf L [n] P.masterIdx (by rw [hlen]; exact h)]
      exact hL j h
    · have hjN : j = N := by omega
      subst hjN
      rw [getD_append_right_cf L [n] P.masterIdx hlen.le, hlen, Nat.sub_self,
        List.getD_cons_zero]
      exact hn

/-- Primitive recursivity of `fun w ↦ iterIdx (codeProj w) (w.unpair.1)` for a primrec `codeProj`. -/
private theorem primrec_iterIdx_proj {codeProj : ℕ → ℕ} (hc : Nat.Primrec codeProj) :
    Nat.Primrec (fun w => iterIdx P (codeProj w) w.unpair.1) := by
  refine (primrec_nthCode.comp (hc.pair (Nat.Primrec.left.pair
    (Nat.Primrec.const P.masterIdx)))).of_eq (fun w => ?_)
  simp only [iterIdx, unpair_pair_fst, unpair_pair_snd]

private theorem primrec_interG : Nat.Primrec (interG P) := by
  have hA : Nat.Primrec (fun s => iterIdx P s.unpair.2.unpair.1 s.unpair.1) :=
    primrec_iterIdx_proj (Nat.Primrec.left.comp Nat.Primrec.right)
  have hB : Nat.Primrec (fun s => iterIdx P s.unpair.2.unpair.2 s.unpair.1) :=
    primrec_iterIdx_proj (Nat.Primrec.right.comp Nat.Primrec.right)
  refine (P.inter_primrec.comp (hA.pair hB)).of_eq (fun s => ?_)
  unfold interG
  simp only [unpair_pair_fst, unpair_pair_snd]

/-- **Exercise 7.15 (Scott 1981, PRG-19) — `D^∞` carries a full computable presentation.** Built
choice-free from a presentation `P` of `V`: the enumeration codes finite fiber-index lists, the two
relations reduce to bounded coordinate checks (`RecDecidable.bForall`), and the intersection function
tabulates `P.inter` coordinate-wise. -/
noncomputable def iterPresentation (P : ComputablePresentation V) :
    ComputablePresentation (iterSys V) where
  X := iterEnum P
  mem_X := iterEnum_mem
  surj := by
    rintro W hW
    obtain ⟨N, hN⟩ := hW.2
    obtain ⟨L, hlen, hL⟩ := exists_list_fiber (P := P) hW N
    refine ⟨encodeList L, ?_⟩
    apply eq_of_fiber_eq
    intro j
    show P.X (nthCode (encodeList L) j P.masterIdx) = fiber W j
    rw [nthCode_eq, decodeList_encodeList]
    by_cases hj : j < N
    · exact hL j hj
    · rw [getD_eq_default_cf L P.masterIdx (by rw [hlen]; omega), P.masterIdx_spec,
        hN j (by omega)]
  interEq_computable := by
    have hbound : Nat.Primrec
        (fun t : ℕ => t.unpair.1 + t.unpair.2.unpair.1 + t.unpair.2.unpair.2) :=
      primrec_add₂ (primrec_add₂ Nat.Primrec.left (Nat.Primrec.left.comp Nat.Primrec.right))
        (Nat.Primrec.right.comp Nat.Primrec.right)
    have hA : Nat.Primrec (fun w => iterIdx P w.unpair.2.unpair.1 w.unpair.1) :=
      primrec_iterIdx_proj (Nat.Primrec.left.comp Nat.Primrec.right)
    have hB : Nat.Primrec (fun w => iterIdx P w.unpair.2.unpair.2.unpair.1 w.unpair.1) :=
      primrec_iterIdx_proj (Nat.Primrec.left.comp (Nat.Primrec.right.comp Nat.Primrec.right))
    have hC : Nat.Primrec (fun w => iterIdx P w.unpair.2.unpair.2.unpair.2 w.unpair.1) :=
      primrec_iterIdx_proj (Nat.Primrec.right.comp (Nat.Primrec.right.comp Nat.Primrec.right))
    have hq : RecDecidable (fun w => P.X (iterIdx P w.unpair.2.unpair.1 w.unpair.1)
        ∩ P.X (iterIdx P w.unpair.2.unpair.2.unpair.1 w.unpair.1)
        = P.X (iterIdx P w.unpair.2.unpair.2.unpair.2 w.unpair.1)) := by
      refine RecDecidable.of_iff (fun w => ?_) (P.interEq_computable.comp (hA.pair (hB.pair hC)))
      simp only [unpair_pair_fst, unpair_pair_snd]
    refine RecDecidable.of_iff (fun t => ?_) (hq.bForall hbound)
    simp only [unpair_pair_fst, unpair_pair_snd]
    exact iterEnum_inter_eq_iff
  cons_computable := by
    have hbound : Nat.Primrec (fun t : ℕ => t.unpair.1 + t.unpair.2) :=
      primrec_add₂ Nat.Primrec.left Nat.Primrec.right
    have hA : Nat.Primrec (fun w => iterIdx P w.unpair.2.unpair.1 w.unpair.1) :=
      primrec_iterIdx_proj (Nat.Primrec.left.comp Nat.Primrec.right)
    have hB : Nat.Primrec (fun w => iterIdx P w.unpair.2.unpair.2 w.unpair.1) :=
      primrec_iterIdx_proj (Nat.Primrec.right.comp Nat.Primrec.right)
    have hq : RecDecidable (fun w => ∃ i, P.X i ⊆ P.X (iterIdx P w.unpair.2.unpair.1 w.unpair.1)
        ∩ P.X (iterIdx P w.unpair.2.unpair.2 w.unpair.1)) := by
      refine RecDecidable.of_iff (fun w => ?_) (P.cons_computable.comp (hA.pair hB))
      simp only [unpair_pair_fst, unpair_pair_snd]
    refine RecDecidable.of_iff (fun t => ?_) (hq.bForall hbound)
    simp only [unpair_pair_fst, unpair_pair_snd]
    exact iterEnum_cons_iff
  inter := iterInter P
  inter_primrec := by
    have hr : Nat.Primrec (fun t => Nat.pair
        (Nat.pair (t.unpair.1 + t.unpair.2) (Nat.pair t.unpair.1 t.unpair.2))
        (t.unpair.1 + t.unpair.2)) :=
      ((primrec_add₂ Nat.Primrec.left Nat.Primrec.right).pair
        (Nat.Primrec.left.pair Nat.Primrec.right)).pair
        (primrec_add₂ Nat.Primrec.left Nat.Primrec.right)
    refine ((primrec_tabCode (primrec_interG (P := P))).comp hr).of_eq (fun t => ?_)
    show tabCode (interG P) _ _ = iterInter P t.unpair.1 t.unpair.2
    unfold iterInter
    simp only [unpair_pair_fst, unpair_pair_snd]
  inter_spec := by
    intro n m hcons
    apply eq_of_fiber_eq
    intro j
    rw [fiber_inter, fiber_iterEnum, fiber_iterEnum, fiber_iterEnum]
    by_cases hj : j < n + m
    · rw [iterInter_idx_lt hj, P.inter_spec ((iterEnum_cons_iff (P := P)).mp hcons j hj)]
    · rw [iterInter_idx_ge (by omega), iterIdx_ge (show n ≤ j by omega),
        iterIdx_ge (show m ≤ j by omega), P.masterIdx_spec, Set.inter_self]
  masterIdx := 0
  masterIdx_spec := by
    apply eq_of_fiber_eq
    intro j
    rw [fiber_iterEnum, fiber_iterSys_master, iterIdx_ge (Nat.zero_le j), P.masterIdx_spec]

@[simp] theorem iterPresentation_X (t : ℕ) : (iterPresentation P).X t = iterEnum P t := rfl

/-- **Exercise 7.15 (Scott 1981, PRG-19) — the infinite iterate `D^∞` is effectively given.** -/
theorem iterSys_isEffectivelyGiven (e : V.IsEffectivelyGiven) :
    (iterSys V).IsEffectivelyGiven := by
  obtain ⟨Q⟩ := e
  exact ⟨iterPresentation (P := Q)⟩

/-! ### The appropriate combinators: the coordinate projections `projN n` are computable.

Scott's "various appropriate combinators" for `D^∞` are the coordinate projections `projN n`
(Exercise 3.16). Relative to the presentation `iterPresentation P`, the relation
`W (projN n) X ↔ fiber W n ⊆ X` reads off as `X_{iterIdx t n} ⊆ X_b` — a recursive slice of
`incl_computable`, hence r.e. (In particular `head = projN 0`.) -/
theorem projN_isComputable (P : ComputablePresentation V) (n : ℕ) :
    IsComputableMap (iterPresentation P) P (projN V n) := by
  have hincl : RecDecidable (fun s => P.X s.unpair.1 ⊆ P.X s.unpair.2) := P.incl_computable
  have hr : Nat.Primrec (fun t => Nat.pair (nthCode t.unpair.1 n P.masterIdx) t.unpair.2) :=
    ((primrec_nthCode.comp (Nat.Primrec.left.pair
      ((Nat.Primrec.const n).pair (Nat.Primrec.const P.masterIdx)))).of_eq
        (fun t => by simp only [unpair_pair_fst, unpair_pair_snd])).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun t => ?_) (hincl.comp hr)).re
  simp only [iterPresentation_X, projN_rel, fiber_iterEnum, iterIdx, unpair_pair_fst,
    unpair_pair_snd]
  exact ⟨fun h => h.2.2, fun h => ⟨iterEnum_mem _, P.mem_X _, h⟩⟩

end Iterate

end Scott1980.Neighborhood

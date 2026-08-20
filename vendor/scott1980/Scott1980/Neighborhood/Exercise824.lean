/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Exercise823

/-!
# Exercise 8.24 (Scott 1981, PRG-19, §8) — mutual fixed points really do solve `D ≅ S(D,E)`,
`E ≅ T(D,E)`

> **EXERCISE 8.24.** Suppose `S` and `T` are two (binary-argument) constructs on domains that can
> be made into computable operators on projections of the universal domain. Show that we can
> therefore find a pair of effectively presented domains such that `D ≅ S(D, E)` and `E ≅ T(D, E)`.

**Answer: yes.** This is the two-variable (mutual-recursion) generalization of Exercise 8.23, and
the whole argument reduces to a *single instance* of Exercise 8.23's own machinery, applied not to
`(E → E)` but to the **product** function space `(E → E) × (E → E)` — Scott's pairs `(a, b)` of
self-maps of `E`. Formalized here (again over an arbitrary neighbourhood system `E`, not just `U`)
for the two purely order-theoretic claims, with the computability clause deferred to prose, exactly
matching Exercise 8.23's own precedent.

## Setup: `s, t` as approximable maps out of the pair space, `paired s t` as the combined operator

Scott's two operators `s, t : (E → E) × (E → E) → (E → E)` are modelled as approximable maps out of
the **pair space** `PairSpace := (funSpace E E) × (funSpace E E)` (Lecture III's `prod`) into the
single function space `funSpace E E`:
`s t : ApproximableMap PairSpace (funSpace E E)`. The induced operators on actual map-pairs are
`binOp s a b := toApproxMap (s.toElementMap (pair (toFilter a) (toFilter b)))` (Scott's `s(a, b)`),
and likewise `binOp t a b` (Scott's `t(a, b)`).

The two operators combine into a **single self-map of the pair space**, `paired s t :
ApproximableMap PairSpace PairSpace` (Definition 3.3's pairing combinator: `⟨s, t⟩(z) =
⟨s(z), t(z)⟩`), to which Theorem 4.1 applies exactly as in Exercise 8.23. Its exact fixed point
`(paired s t).fixElement : PairSpace.Element` splits, via Definition 3.1's projections `.fst`/
`.snd`, into the two components `aStar s t := toApproxMap (paired s t).fixElement.fst` and
`bStar s t := toApproxMap (paired s t).fixElement.snd` — Scott's simultaneous solution
`(‖s‖, ‖t‖)` of the mutual recursion.

The approximants `(paired s t).iterElem n` similarly split into chains `aOp s t n`/`bOp s t n`
(`.fst`/`.snd` again), satisfying the expected mutual recursion
`aOp s t (n+1) = binOp s (aOp s t n) (bOp s t n)`, `bOp s t (n+1) = binOp t (aOp s t n) (bOp s t n)`
(`aOp_succ`/`bOp_succ`), with base case the constant-bottom map on both sides (`aOp_zero`/
`bOp_zero`, reusing Exercise 8.23's `isFinitaryProjection_constMap_bot`).

## Claim 1 — `aStar s t`, `bStar s t` really are finitary projections (`isFinitaryProjection_aStar_bStar`)

Given `hst : ∀ a b, IsFinitaryProjection a → IsFinitaryProjection b → IsFinitaryProjection (binOp s
a b) ∧ IsFinitaryProjection (binOp t a b)` (Scott's hypothesis that `s`/`t` send pairs of
projections to projections), an induction using `aOp_succ`/`bOp_succ` shows every approximant pair
`(aOp s t n, bOp s t n)` consists of finitary projections, exactly as in Exercise 8.23's Claim 1.
The genuinely new step is transporting Theorem 8.6's `sub`/`subFilter` continuity-with-directed-sups
argument through the `.fst`/`.snd` projections: `(paired s t).fixElement.fst` is identified with the
directed union `⊔ₙ (aOp s t n)`'s underlying filter (`hEqA`, a direct membership chase through
`mem_fst`/`mem_fixElement`/`mem_iterElem`, paralleling `Theorem41.fixElement_eq_iSupDirected` one
level down through the product), and `subFilter` fixes it termwise, hence fixes the union
(`hkeyA`/`hkeyB`, `Sub8_6.subFilter_iSupDirected`) — verbatim Exercise 8.23's Claim 1 argument,
just run twice (once per component).

## Claim 2 — `Fix(aStar s t) ≅ S(aStar s t, bStar s t)`, `Fix(bStar s t) ≅ T(aStar s t, bStar s t)`,
and initiality with respect to projections

`(aStar s t, bStar s t)` is a *genuine* (not merely approximate) simultaneous fixed point:
`binOp s (aStar s t) (bStar s t) = aStar s t` and likewise for `t` (`binOp_aStar_bStar_left/right`),
from `toElementMap_fixElement` (Theorem 4.1) plus `toElementMap_paired`/`fst_pair`/`snd_pair`/
`pair_fst_snd` bookkeeping — again a bare substitution, not a colimit argument. Substituting
`a := aStar s t`, `b := bStar s t` into an abstractly-packaged pair of hypotheses `hS a b : Fix(binOp
s a b) ≅ S(a,b)`, `hT a b : Fix(binOp t a b) ≅ T(a,b)` (Scott's `D_{s(a,b)} ≅ S(D_a, D_b)`,
`D_{t(a,b)} ≅ T(D_a, D_b)`, packaged directly in terms of the maps `a, b` as in Exercise 8.23) and
rewriting the two equations gives `Fix(aStar s t) ≅ S(aStar s t, bStar s t)` and `Fix(bStar s t) ≅
T(aStar s t, bStar s t)` **unconditionally** (`fixedDomain_aStar_bStar_iso`) — exactly Scott's
`D ≅ S(D, E)`, `E ≅ T(D, E)`, with `D := Fix(aStar s t)`, `E := Fix(bStar s t)`.

**Initiality with respect to projections** (`fixedNbhd_aStar_bStar_subsystem`): if `a, b` is *any*
other pair of finitary projections that is a pre-fixed point of the same pair of operators
(`binOp s a b ≤ a`, `binOp t a b ≤ b`), then packaging `(a, b)` as `pair (toFilter a) (toFilter b) :
PairSpace.Element`, the pre-fixed-point hypotheses assemble (via `pair_le_pair_iff`) into a single
pre-fixed-point inequality for `paired s t`, so Theorem 4.1's minimality
(`fixElement_le_of_toElementMap_le`) gives `(paired s t).fixElement ≤ pair (toFilter a) (toFilter
b)`; taking `.fst`/`.snd` and transporting through Exercise 8.16's order-isomorphism `a ≤ b ↔ D_a ◁
D_b` gives `fixedNbhd (aStar s t) ◁ fixedNbhd a` and `fixedNbhd (bStar s t) ◁ fixedNbhd b` — Scott's
"the initial solution... with respect to projections", now for *both* components simultaneously.

## Claim 3 — effectively given if `s, t` are computable (not formalized: prose only)

Exactly Exercise 8.23's own deferred computability clause, doubled: if `s` and `t` are computable
(relative to a `ComputablePresentation` of `E`'s function space), then `constMap E E.bot` is
trivially computable, and by a routine joint induction every approximant pair `(aOp s t n, bOp s t
n)` is computable (composition/pairing of computable maps is computable — `binOp`'s definition is
literally `toElementMap` applied to a `pair`, both computable operations). The simultaneous limit
`(aStar s t, bStar s t)` is then a recursively-enumerable union of computable approximant pairs,
indexed by `n : ℕ`, hence computable by the same "effective limit of an effective chain" argument
already carried out in this codebase for Theorem 8.8's back-and-forth `Yₙ`-chain
(`Theorem88b.lean`–`Theorem88m.lean`). Not carried out in Lean here, matching the `sub`- and
Exercise-8.23-computability precedents.

Everything **proved** in this file (Claims 1–2) is **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap Sub8_6 Exercise823

namespace Exercise824

variable {α : Type} {E : NeighborhoodSystem α}

/-! ## The pair space `(E → E) × (E → E)`, and the combined operator `⟨s, t⟩` -/

/-- Scott's pair space `(E → E) × (E → E)`: pairs of self-maps of `E`, as an actual
`NeighborhoodSystem` (Lecture III's product of two copies of the function space). -/
abbrev PairSpace : NeighborhoodSystem (ApproximableMap E E ⊕ ApproximableMap E E) :=
  prod (funSpace E E) (funSpace E E)

/-- Scott's `s(a, b)`: the operator `(E → E) × (E → E) → (E → E)` induced by an approximable map
`s` out of the pair space, applied to two actual maps `a b : E → E`. -/
def binOp (f : ApproximableMap (PairSpace (E := E)) (funSpace E E))
    (a b : ApproximableMap E E) : ApproximableMap E E :=
  toApproxMap (f.toElementMap (pair (toFilter a) (toFilter b)))

/-- Scott's `‖s‖ = fix(⟨s, t⟩)`'s first component, as an actual approximable map `E → E`. -/
def aStar (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) : ApproximableMap E E :=
  toApproxMap (paired s t).fixElement.fst

/-- Scott's `‖t‖ = fix(⟨s, t⟩)`'s second component, as an actual approximable map `E → E`. -/
def bStar (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) : ApproximableMap E E :=
  toApproxMap (paired s t).fixElement.snd

/-- The `n`-th approximant's first component, as an actual approximable map `E → E`. -/
def aOp (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) (n : ℕ) :
    ApproximableMap E E :=
  toApproxMap ((paired s t).iterElem n).fst

/-- The `n`-th approximant's second component, as an actual approximable map `E → E`. -/
def bOp (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) (n : ℕ) :
    ApproximableMap E E :=
  toApproxMap ((paired s t).iterElem n).snd

/-! ## `.fst`/`.snd` are monotone (needed for the directed-union chase in Claim 1) -/

theorem fst_mono {z z' : (PairSpace (E := E)).Element} (h : z ≤ z') : z.fst ≤ z'.fst := by
  intro X hX
  rw [mem_fst] at hX ⊢
  exact ⟨hX.1, h _ hX.2⟩

theorem snd_mono {z z' : (PairSpace (E := E)).Element} (h : z ≤ z') : z.snd ≤ z'.snd := by
  intro X hX
  rw [mem_snd] at hX ⊢
  exact ⟨hX.1, h _ hX.2⟩

/-! ## The bottom of the pair space splits into the two bottoms (base case of the induction) -/

theorem pair_bot_bot : pair ((funSpace E E).bot) ((funSpace E E).bot) = (PairSpace (E := E)).bot := by
  apply Element.ext
  intro W
  rw [mem_pair, mem_bot]
  constructor
  · rintro ⟨X, Y, hX, hY, rfl⟩
    rw [mem_bot] at hX hY
    rw [hX, hY, prod_master]
  · intro hW
    refine ⟨(funSpace E E).master, (funSpace E E).master, ?_, ?_, ?_⟩
    · rw [mem_bot]
    · rw [mem_bot]
    · rw [hW, prod_master]

theorem pairSpace_bot_fst : ((PairSpace (E := E)).bot).fst = (funSpace E E).bot := by
  rw [← pair_bot_bot, fst_pair]

theorem pairSpace_bot_snd : ((PairSpace (E := E)).bot).snd = (funSpace E E).bot := by
  rw [← pair_bot_bot, snd_pair]

/-! ## `⟨s, t⟩`'s iterates (mirroring Exercise 8.23's `iterElem_succ'`/`iterElem_zero'`) -/

theorem iterElem_succ_pair (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) (n : ℕ) :
    (paired s t).iterElem (n + 1) = (paired s t).toElementMap ((paired s t).iterElem n) := by
  show ((paired s t).comp ((paired s t).iterMap n)).toElementMap (PairSpace (E := E)).bot
      = (paired s t).toElementMap (((paired s t).iterMap n).toElementMap (PairSpace (E := E)).bot)
  rw [toElementMap_comp]

theorem iterElem_zero_pair (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) :
    (paired s t).iterElem 0 = (PairSpace (E := E)).bot := by
  show (idMap (PairSpace (E := E))).toElementMap (PairSpace (E := E)).bot
      = (PairSpace (E := E)).bot
  rw [toElementMap_idMap]

/-- The `n`-th approximant of `⟨s, t⟩` is exactly the pairing of `aOp`'s and `bOp`'s `n`-th
approximants (`Product.lean`'s `pair_fst_snd`, transported through the `toFilter`/`toApproxMap`
round trip). -/
theorem iterElem_pair_eq_pair (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) (n : ℕ) :
    (paired s t).iterElem n = pair (toFilter (aOp s t n)) (toFilter (bOp s t n)) := by
  show (paired s t).iterElem n
      = pair (toFilter (toApproxMap ((paired s t).iterElem n).fst))
          (toFilter (toApproxMap ((paired s t).iterElem n).snd))
  rw [toFilter_toApproxMap, toFilter_toApproxMap, pair_fst_snd]

/-- **The mutual recursion on approximants**: `aOp s t (n+1) = binOp s (aOp s t n) (bOp s t n)`. -/
theorem aOp_succ (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) (n : ℕ) :
    aOp s t (n + 1) = binOp s (aOp s t n) (bOp s t n) := by
  show toApproxMap ((paired s t).iterElem (n + 1)).fst
      = toApproxMap (s.toElementMap (pair (toFilter (aOp s t n)) (toFilter (bOp s t n))))
  rw [iterElem_succ_pair, toElementMap_paired, fst_pair, iterElem_pair_eq_pair]

/-- **The mutual recursion on approximants**: `bOp s t (n+1) = binOp t (aOp s t n) (bOp s t n)`. -/
theorem bOp_succ (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) (n : ℕ) :
    bOp s t (n + 1) = binOp t (aOp s t n) (bOp s t n) := by
  show toApproxMap ((paired s t).iterElem (n + 1)).snd
      = toApproxMap (t.toElementMap (pair (toFilter (aOp s t n)) (toFilter (bOp s t n))))
  rw [iterElem_succ_pair, toElementMap_paired, snd_pair, iterElem_pair_eq_pair]

theorem aOp_zero (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) :
    aOp s t 0 = constMap E E.bot := by
  show toApproxMap ((paired s t).iterElem 0).fst = constMap E E.bot
  rw [iterElem_zero_pair, pairSpace_bot_fst, Exercise823.toApproxMap_bot_eq_constMap]

theorem bOp_zero (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) :
    bOp s t 0 = constMap E E.bot := by
  show toApproxMap ((paired s t).iterElem 0).snd = constMap E E.bot
  rw [iterElem_zero_pair, pairSpace_bot_snd, Exercise823.toApproxMap_bot_eq_constMap]

/-! ## Claim 1 — `aStar s t`, `bStar s t` are finitary projections -/

/-- Every approximant pair `(aOp s t n, bOp s t n)` consists of finitary projections, provided
`s`/`t` send pairs of finitary projections to finitary projections. -/
theorem isFinitaryProjection_chain (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E))
    (hst : ∀ a b, IsFinitaryProjection a → IsFinitaryProjection b →
      IsFinitaryProjection (binOp s a b) ∧ IsFinitaryProjection (binOp t a b)) :
    ∀ n, IsFinitaryProjection (aOp s t n) ∧ IsFinitaryProjection (bOp s t n) := by
  intro n
  induction n with
  | zero =>
    rw [aOp_zero, bOp_zero]
    exact ⟨Exercise823.isFinitaryProjection_constMap_bot E,
      Exercise823.isFinitaryProjection_constMap_bot E⟩
  | succ k ih =>
    rw [aOp_succ, bOp_succ]
    exact hst _ _ ih.1 ih.2

/-- **Exercise 8.24, Claim 1.** Provided `s`/`t` map pairs of finitary projections to finitary
projections, the simultaneous fixed point `(aStar s t, bStar s t)` really consists of finitary
projections. -/
theorem isFinitaryProjection_aStar_bStar (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E))
    (hst : ∀ a b, IsFinitaryProjection a → IsFinitaryProjection b →
      IsFinitaryProjection (binOp s a b) ∧ IsFinitaryProjection (binOp t a b)) :
    IsFinitaryProjection (aStar s t) ∧ IsFinitaryProjection (bStar s t) := by
  have hchain := isFinitaryProjection_chain s t hst
  have hsubA : ∀ n, subFilter (((paired s t).iterElem n).fst) = ((paired s t).iterElem n).fst := by
    intro n
    apply toApproxMap_injective
    rw [toApproxMap_subFilter]
    show sub (aOp s t n) = aOp s t n
    exact sub_eq_self_of_isFinitaryProjection (hchain n).1
  have hsubB : ∀ n, subFilter (((paired s t).iterElem n).snd) = ((paired s t).iterElem n).snd := by
    intro n
    apply toApproxMap_injective
    rw [toApproxMap_subFilter]
    show sub (bOp s t n) = bOp s t n
    exact sub_eq_self_of_isFinitaryProjection (hchain n).2
  have hdirA : ∀ i j : ℕ, ∃ k, ((paired s t).iterElem i).fst ≤ ((paired s t).iterElem k).fst ∧
      ((paired s t).iterElem j).fst ≤ ((paired s t).iterElem k).fst :=
    fun i j => ⟨max i j, fst_mono (iterElem_mono (paired s t) (le_max_left i j)),
      fst_mono (iterElem_mono (paired s t) (le_max_right i j))⟩
  have hdirB : ∀ i j : ℕ, ∃ k, ((paired s t).iterElem i).snd ≤ ((paired s t).iterElem k).snd ∧
      ((paired s t).iterElem j).snd ≤ ((paired s t).iterElem k).snd :=
    fun i j => ⟨max i j, snd_mono (iterElem_mono (paired s t) (le_max_left i j)),
      snd_mono (iterElem_mono (paired s t) (le_max_right i j))⟩
  have hdirSubA : ∀ i j : ℕ, ∃ k, subFilter (((paired s t).iterElem i).fst) ≤
      subFilter (((paired s t).iterElem k).fst) ∧
      subFilter (((paired s t).iterElem j).fst) ≤ subFilter (((paired s t).iterElem k).fst) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hdirA i j
    exact ⟨k, by rw [hsubA i, hsubA k]; exact hik, by rw [hsubA j, hsubA k]; exact hjk⟩
  have hdirSubB : ∀ i j : ℕ, ∃ k, subFilter (((paired s t).iterElem i).snd) ≤
      subFilter (((paired s t).iterElem k).snd) ∧
      subFilter (((paired s t).iterElem j).snd) ≤ subFilter (((paired s t).iterElem k).snd) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hdirB i j
    exact ⟨k, by rw [hsubB i, hsubB k]; exact hik, by rw [hsubB j, hsubB k]; exact hjk⟩
  have hEqA : (paired s t).fixElement.fst =
      iSupDirected (fun n => ((paired s t).iterElem n).fst) hdirA := by
    apply Element.ext
    intro X
    rw [mem_fst, mem_fixElement, mem_iSupDirected]
    constructor
    · rintro ⟨hX, n, hn⟩
      exact ⟨n, mem_fst.mpr ⟨hX, (mem_iterElem (paired s t) n).mpr hn⟩⟩
    · rintro ⟨n, hn⟩
      rw [mem_fst] at hn
      exact ⟨hn.1, n, (mem_iterElem (paired s t) n).mp hn.2⟩
  have hEqB : (paired s t).fixElement.snd =
      iSupDirected (fun n => ((paired s t).iterElem n).snd) hdirB := by
    apply Element.ext
    intro X
    rw [mem_snd, mem_fixElement, mem_iSupDirected]
    constructor
    · rintro ⟨hX, n, hn⟩
      exact ⟨n, mem_snd.mpr ⟨hX, (mem_iterElem (paired s t) n).mpr hn⟩⟩
    · rintro ⟨n, hn⟩
      rw [mem_snd] at hn
      exact ⟨hn.1, n, (mem_iterElem (paired s t) n).mp hn.2⟩
  have hkeyA : subFilter ((paired s t).fixElement.fst) = (paired s t).fixElement.fst := by
    rw [hEqA, subFilter_iSupDirected _ hdirA hdirSubA]
    apply Element.ext
    intro Z
    rw [mem_iSupDirected, mem_iSupDirected]
    simp_rw [hsubA]
  have hkeyB : subFilter ((paired s t).fixElement.snd) = (paired s t).fixElement.snd := by
    rw [hEqB, subFilter_iSupDirected _ hdirB hdirSubB]
    apply Element.ext
    intro Z
    rw [mem_iSupDirected, mem_iSupDirected]
    simp_rw [hsubB]
  refine ⟨?_, ?_⟩
  · show IsFinitaryProjection (toApproxMap (paired s t).fixElement.fst)
    apply isFinitaryProjection_of_sub_eq_self
    rw [← toApproxMap_subFilter, hkeyA]
  · show IsFinitaryProjection (toApproxMap (paired s t).fixElement.snd)
    apply isFinitaryProjection_of_sub_eq_self
    rw [← toApproxMap_subFilter, hkeyB]

/-! ## Claim 2 — the simultaneous fixed point genuinely solves the equations, and is initial -/

theorem toElementMap_fixElement_fst (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) :
    s.toElementMap (paired s t).fixElement = (paired s t).fixElement.fst := by
  have h : (paired s t).toElementMap (paired s t).fixElement = (paired s t).fixElement :=
    toElementMap_fixElement (paired s t)
  rw [toElementMap_paired] at h
  have h' := congrArg NeighborhoodSystem.Element.fst h
  rwa [fst_pair] at h'

theorem toElementMap_fixElement_snd (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) :
    t.toElementMap (paired s t).fixElement = (paired s t).fixElement.snd := by
  have h : (paired s t).toElementMap (paired s t).fixElement = (paired s t).fixElement :=
    toElementMap_fixElement (paired s t)
  rw [toElementMap_paired] at h
  have h' := congrArg NeighborhoodSystem.Element.snd h
  rwa [snd_pair] at h'

/-- `(aStar s t, bStar s t)` is a *genuine* fixed point of the pair `(s, t)`. -/
theorem binOp_aStar_bStar_left (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) :
    binOp s (aStar s t) (bStar s t) = aStar s t := by
  unfold binOp aStar bStar
  rw [toFilter_toApproxMap, toFilter_toApproxMap, pair_fst_snd, toElementMap_fixElement_fst]

/-- `(aStar s t, bStar s t)` is a *genuine* fixed point of the pair `(s, t)`. -/
theorem binOp_aStar_bStar_right (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E)) :
    binOp t (aStar s t) (bStar s t) = bStar s t := by
  unfold binOp aStar bStar
  rw [toFilter_toApproxMap, toFilter_toApproxMap, pair_fst_snd, toElementMap_fixElement_snd]

/-- **Exercise 8.24, Claim 2 (the domain equations).** Given any correspondences `S, T` (bundling,
for each pair of maps, a type and a domain over it) with `Fix(binOp s a b) ≅ S(a,b)` and
`Fix(binOp t a b) ≅ T(a,b)` for every pair of finitary projections `a, b` (Scott's hypotheses
`D_{s(a,b)} ≅ S(D_a,D_b)`, `D_{t(a,b)} ≅ T(D_a,D_b)`), substituting the *exact* simultaneous fixed
point `a := aStar s t`, `b := bStar s t` and using `binOp_aStar_bStar_left/right` gives
`Fix(aStar s t) ≅ S(aStar s t, bStar s t)` and `Fix(bStar s t) ≅ T(aStar s t, bStar s t)`
unconditionally — Scott's `D ≅ S(D,E)`, `E ≅ T(D,E)`. -/
theorem fixedDomain_aStar_bStar_iso (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E))
    (hst : ∀ a b, IsFinitaryProjection a → IsFinitaryProjection b →
      IsFinitaryProjection (binOp s a b) ∧ IsFinitaryProjection (binOp t a b))
    (S T : ApproximableMap E E → ApproximableMap E E → Σ β : Type, NeighborhoodSystem β)
    (hS : ∀ a b, IsFinitaryProjection a → IsFinitaryProjection b →
      Nonempty (Fix (binOp s a b) ≃o (S a b).2.Element))
    (hT : ∀ a b, IsFinitaryProjection a → IsFinitaryProjection b →
      Nonempty (Fix (binOp t a b) ≃o (T a b).2.Element)) :
    Nonempty (Fix (aStar s t) ≃o (S (aStar s t) (bStar s t)).2.Element) ∧
      Nonempty (Fix (bStar s t) ≃o (T (aStar s t) (bStar s t)).2.Element) := by
  obtain ⟨hFinA, hFinB⟩ := isFinitaryProjection_aStar_bStar s t hst
  have h1 := hS (aStar s t) (bStar s t) hFinA hFinB
  have h2 := hT (aStar s t) (bStar s t) hFinA hFinB
  rw [binOp_aStar_bStar_left] at h1
  rw [binOp_aStar_bStar_right] at h2
  exact ⟨h1, h2⟩

/-- **Exercise 8.24, Claim 2 (initiality with respect to projections).** If `a, b` is *any* other
pair of finitary projections that is a pre-fixed point of the same pair of operators
(`binOp s a b ≤ a`, `binOp t a b ≤ b`, in particular any exact alternative solution), then
`(aStar s t, bStar s t)`'s domains embed as literal subsystems of `a`'s and `b`'s domains:
`D_{aStar s t} ◁ D_a`, `D_{bStar s t} ◁ D_b` — Scott's "the initial solution... with respect to
projections", for both components simultaneously. -/
theorem fixedNbhd_aStar_bStar_subsystem (s t : ApproximableMap (PairSpace (E := E)) (funSpace E E))
    (hst : ∀ a b, IsFinitaryProjection a → IsFinitaryProjection b →
      IsFinitaryProjection (binOp s a b) ∧ IsFinitaryProjection (binOp t a b))
    {a b : ApproximableMap E E} (ha : IsFinitaryProjection a) (hb : IsFinitaryProjection b)
    (hpreA : binOp s a b ≤ a) (hpreB : binOp t a b ≤ b) :
    fixedNbhd (aStar s t) ◁ fixedNbhd a ∧ fixedNbhd (bStar s t) ◁ fixedNbhd b := by
  have h1 : s.toElementMap (pair (toFilter a) (toFilter b)) ≤ toFilter a := by
    have hpreA' : toApproxMap (s.toElementMap (pair (toFilter a) (toFilter b))) ≤
        toApproxMap (toFilter a) := by
      show binOp s a b ≤ toApproxMap (toFilter a)
      rw [toApproxMap_toFilter]
      exact hpreA
    have hiff := (funSpaceEquiv E E).le_iff_le
      (x := s.toElementMap (pair (toFilter a) (toFilter b))) (y := toFilter a)
    rw [funSpaceEquiv_apply, funSpaceEquiv_apply] at hiff
    exact hiff.mp hpreA'
  have h2 : t.toElementMap (pair (toFilter a) (toFilter b)) ≤ toFilter b := by
    have hpreB' : toApproxMap (t.toElementMap (pair (toFilter a) (toFilter b))) ≤
        toApproxMap (toFilter b) := by
      show binOp t a b ≤ toApproxMap (toFilter b)
      rw [toApproxMap_toFilter]
      exact hpreB
    have hiff := (funSpaceEquiv E E).le_iff_le
      (x := t.toElementMap (pair (toFilter a) (toFilter b))) (y := toFilter b)
    rw [funSpaceEquiv_apply, funSpaceEquiv_apply] at hiff
    exact hiff.mp hpreB'
  have hle : (paired s t).toElementMap (pair (toFilter a) (toFilter b)) ≤
      pair (toFilter a) (toFilter b) := by
    rw [toElementMap_paired]
    exact pair_le_pair_iff.mpr ⟨h1, h2⟩
  have hfix : (paired s t).fixElement ≤ pair (toFilter a) (toFilter b) :=
    fixElement_le_of_toElementMap_le (paired s t) hle
  have hfstle : (paired s t).fixElement.fst ≤ toFilter a := by
    have := fst_mono hfix; rwa [fst_pair] at this
  have hsndle : (paired s t).fixElement.snd ≤ toFilter b := by
    have := snd_mono hfix; rwa [snd_pair] at this
  have hAle : aStar s t ≤ a := by
    show toApproxMap (paired s t).fixElement.fst ≤ a
    rw [← toApproxMap_toFilter a]
    exact toApproxMap_monotone hfstle
  have hBle : bStar s t ≤ b := by
    show toApproxMap (paired s t).fixElement.snd ≤ b
    rw [← toApproxMap_toFilter b]
    exact toApproxMap_monotone hsndle
  obtain ⟨hFinA, hFinB⟩ := isFinitaryProjection_aStar_bStar s t hst
  exact ⟨(isFinitaryProjection_le_iff_fixedNbhd_subsystem hFinA ha).mp hAle,
    (isFinitaryProjection_le_iff_fixedNbhd_subsystem hFinB hb).mp hBle⟩

end Exercise824

end Scott1980.Neighborhood

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Approximable
import Scott1980.Neighborhood.Example12
import Scott1980.Neighborhood.ExampleB

/-!
# Example 2.3 (Scott 1981, PRG-19, §2) — the parity map `f : B → T`

Scott's first approximable mapping. Reading a binary sequence left to right, count the number `n`
of `0`'s seen *before the first* `1`; the output is `true` if `n` is even, `false` if `n` is odd,
and `⊥` while the input is still an unbroken string of `0`'s (which has consistent extensions of
both parities). Concretely

`f(0ⁿ1⊥) = true` if `n` even, `false` if `n` odd; `f(0^∞) = ⊥`.

Here `B` is the binary system (`ExampleB`) and `T` is the two-token domain of Example 1.2, whose two
total elements we use as `true`/`false` and whose unique partial element is `⊥`.

We model the relation by a parity scanner `scan : Σ* → Option Bool`:
`scan` returns `none` while no `1` has appeared and `some b` (with `b` the parity-of-leading-zeros)
once the first `1` is found. The neighbourhood relation is

`X f Y ↔ ∃ σ, X = σΣ* ∧ Y ∈ valElt (scan σ)`,

where `valElt none = ⊥`, `valElt (some true) = true`, `valElt (some false) = false`. The cone `σΣ*`
has a unique generating prefix (`cone_injective`), so this is well defined, and `scan` is *stable*
under extension (`scan_append`), which is exactly the monotonicity (Def 2.1(iii)).

Definition 2.1(i)–(iii) all check out, giving `parityMap : ApproximableMap B T`. (The `B`-side
reasoning is choice-free; `parityMap` nonetheless pulls `Classical.choice` through the concrete
codomain `T` of Example 1.2, whose `simp`/`fin_cases` proofs already do — pre-existing and harmless.)
-/

namespace Scott1980.Neighborhood.Example23

open Scott1980.Neighborhood NeighborhoodSystem ExampleB

/-- The two-token codomain `T` of Example 1.2. -/
abbrev T : NeighborhoodSystem Example12.Token := Example12.neighborhoodSystem

/-- Scott's `true`: the total element `{Δ, {0}}` of `T`. -/
def trueElt : T.Element := Example12.neighborhoodSystem.elemZero

/-- Scott's `false`: the total element `{Δ, {1}}` of `T`. -/
def falseElt : T.Element := Example12.neighborhoodSystem.elemOne

/-- Scott's `⊥`: the unique partial element `{Δ}` of `T`. -/
def botElt : T.Element := Example12.neighborhoodSystem.bot

/-- The codomain element selected by a parity reading: `none ↦ ⊥`, `some true ↦ true`,
`some false ↦ false`. -/
def valElt : Option Bool → T.Element
  | none => botElt
  | some true => trueElt
  | some false => falseElt

/-- `⊥` approximates every element of `T` (the local `{Δ}` form, proved directly). -/
theorem botElt_le (x : T.Element) : botElt ≤ x := by
  intro Z hZ
  have : Z = Example12.master := hZ
  subst this
  exact x.master_mem

/-- **`⊥` is the unique common lower bound of `true` and `false`.** Any `a : |𝒯|` approximated by
*both* total elements is `⊥` — `𝒯`'s flatness. (Exercise 2.16's uniqueness argument: reading no
tokens yet is the only state consistent with committing to either verdict.) -/
theorem eq_botElt_of_le {a : T.Element} (h0 : a ≤ trueElt) (h1 : a ≤ falseElt) : a = botElt :=
  Example12.neighborhoodSystem.eq_bot_of_le_elemZero_of_le_elemOne h0 h1

/-- **The parity scanner.** `scan σ = none` while `σ` is an unbroken run of `0`'s; once a `1`
appears, `scan σ = some b` with `b = true` iff an even number of `0`'s preceded it. A leading `0`
flips the parity of the rest; a leading `1` fixes parity `true` (zero preceding zeros). -/
def scan : Str → Option Bool
  | [] => none
  | true :: _ => some true
  | false :: t => (scan t).map (!·)

@[simp] theorem scan_nil : scan [] = none := rfl
@[simp] theorem scan_true (t : Str) : scan (true :: t) = some true := rfl
@[simp] theorem scan_false (t : Str) : scan (false :: t) = (scan t).map (!·) := rfl

/-- **A leading `1` always commits to `true`, whatever follows.** `scan([1]++τ) = true`, for
*every* tail `τ`. (Exercise 2.16's first equation, at the token level.) -/
theorem scan_append_true (τ : Str) : scan ([true] ++ τ) = some true :=
  scan_true τ

/-- **A leading `01` always commits to `false`, whatever follows.** `scan([0,1]++τ) = false`, for
*every* tail `τ`. (Exercise 2.16's second equation, at the token level.) -/
theorem scan_append_falseTrue (τ : Str) : scan ([false, true] ++ τ) = some false := by
  show scan (false :: true :: τ) = some false
  simp [scan_false, scan_true]

/-- **Two leading `0`'s cancel.** `scan([0,0]++τ) = scan τ`: reading two extra zeros flips the
parity twice, i.e. not at all (`Bool.not_not`). (Exercise 2.16's third equation, at the token
level — the recursive step behind the uniqueness argument for the parity map.) -/
theorem scan_append_falseFalse (τ : Str) : scan ([false, false] ++ τ) = scan τ := by
  show scan (false :: false :: τ) = scan τ
  cases h : scan τ with
  | none => simp [scan_false, h]
  | some b => simp [scan_false, h, Bool.not_not]

/-- **Stability of the scan under extension.** Once `scan σ` has committed to a parity `some b`,
every extension `σ ++ t` keeps that value. This is the engine of monotonicity for `parityMap`. -/
theorem scan_append {σ : Str} {b : Bool} (h : scan σ = some b) (t : Str) :
    scan (σ ++ t) = some b := by
  induction σ generalizing b with
  | nil => simp at h
  | cons c σ₀ ih =>
    cases c with
    | true => simp only [scan_true] at h ⊢; exact h
    | false =>
      simp only [List.cons_append, scan_false] at h ⊢
      rw [Option.map_eq_some_iff] at h
      obtain ⟨a, ha, rfl⟩ := h
      rw [ih ha]
      rfl

/-- **Monotonicity of the parity value.** A longer prefix `σ <+: σ'` yields a (weakly) more defined
value: `valElt (scan σ) ⊑ valElt (scan σ')`. If `scan σ = none` then `valElt = ⊥ ⊑ _`; otherwise the
value is fixed by `scan_append`. -/
theorem valElt_scan_mono {σ σ' : Str} (h : σ <+: σ') :
    valElt (scan σ) ≤ valElt (scan σ') := by
  obtain ⟨t, rfl⟩ := h
  cases hσ : scan σ with
  | none => simpa [valElt, hσ] using botElt_le _
  | some b => rw [scan_append hσ t]

/-- **Example 2.3 — the parity mapping `f : B → T`.** `X f Y` iff `X` is the cone `σΣ*` of some
prefix `σ` and `Y` is approximated by the parity verdict `valElt (scan σ)`. Definition 2.1:
(i) the empty prefix scans to `none = ⊥`, and `⊥` contains `Δ_T`; (ii) for a fixed cone the verdict
is a *single* filter (cones have a unique prefix), closed under `∩`; (iii) extending the prefix only
sharpens the verdict (`valElt_scan_mono`). -/
def parityMap : ApproximableMap B T where
  rel X Y := ∃ σ, X = cone σ ∧ (valElt (scan σ)).mem Y
  rel_dom := fun ⟨σ, hX, _⟩ => ⟨σ, hX⟩
  rel_cod := fun ⟨_, _, hY⟩ => (valElt _).sub hY
  master_rel := by
    refine ⟨[], cone_nil.symm, ?_⟩
    show (botElt).mem Example12.master
    rfl
  inter_right := by
    rintro X Y Y' ⟨σ, hX, hY⟩ ⟨σ', hX', hY'⟩
    have hσ : σ = σ' := cone_injective (hX ▸ hX')
    subst hσ
    exact ⟨σ, hX, (valElt (scan σ)).inter_mem hY hY'⟩
  mono := by
    rintro X X' Y Y' ⟨σ, hX, hY⟩ hX'X hYY' hX'mem hY'mem
    obtain ⟨σ', hX'cone⟩ := hX'mem
    have hpre : σ <+: σ' := by
      apply cone_subset_cone.mp
      rw [← hX'cone, ← hX]; exact hX'X
    have hYmem' : (valElt (scan σ)).mem Y' := (valElt (scan σ)).up_mem hY hY'mem hYY'
    exact ⟨σ', hX'cone, valElt_scan_mono hpre Y' hYmem'⟩

/-- **`parityMap`'s relation on a cone, read off.** `cone σ f Y ↔ Y ∈ valElt(scan σ)` — the
defining existential collapses since a cone has a *unique* generating prefix (`cone_injective`).
(Used throughout Exercise 2.16's uniqueness argument.) -/
theorem parityMap_rel_cone (σ : Str) (Y : Set Example12.Token) :
    parityMap.rel (cone σ) Y ↔ (valElt (scan σ)).mem Y := by
  constructor
  · rintro ⟨ρ, hρ, hval⟩
    rw [cone_injective hρ]
    exact hval
  · intro hval
    exact ⟨σ, rfl, hval⟩

/-- **`parityMap`'s elementwise value, read off cone-by-cone.** `f(x).mem Y` iff *some* cone
`σΣ* ∈ x` already witnesses `Y ∈ valElt(scan σ)` — every neighbourhood of `x` is a cone
(`Element.sub`), and `parityMap`'s relation is exactly `parityMap_rel_cone`. -/
theorem parityMap_toElementMap_mem (x : B.Element) (Y : Set Example12.Token) :
    (parityMap.toElementMap x).mem Y ↔ ∃ τ, x.mem (cone τ) ∧ (valElt (scan τ)).mem Y := by
  constructor
  · rintro ⟨X, hX, hrel⟩
    obtain ⟨τ, rfl⟩ := x.sub hX
    exact ⟨τ, hX, (parityMap_rel_cone τ Y).mp hrel⟩
  · rintro ⟨τ, hτ, hval⟩
    exact ⟨cone τ, hτ, (parityMap_rel_cone τ Y).mpr hval⟩

/-- **The "shift formula" for `parityMap`.** Reading off the parity of `σx` depends on `x` only
through *some* cone `cone τ ∈ x`, via the scan of the concatenation `σ ++ τ`: any deeper cone in
`sigmaElt`'s built-in up-closure is subsumed by monotonicity (`valElt_scan_mono`), so the longest
one — `σ ++ τ` itself — already witnesses the answer. This is the key computation behind Exercise
2.16's second half: `parityMap` genuinely satisfies its own defining equations. -/
theorem parityMap_toElementMap_sigmaElt (σ : Str) (x : B.Element) (Y : Set Example12.Token) :
    (parityMap.toElementMap (sigmaElt σ x)).mem Y ↔
      ∃ τ, x.mem (cone τ) ∧ (valElt (scan (σ ++ τ))).mem Y := by
  constructor
  · rintro ⟨Z, ⟨_, X, hX, hsub⟩, ρ, rfl, hval⟩
    obtain ⟨τ, rfl⟩ := x.sub hX
    rw [prepend_cone] at hsub
    exact ⟨τ, hX, valElt_scan_mono (cone_subset_cone.mp hsub) Y hval⟩
  · rintro ⟨τ, hτ, hval⟩
    exact ⟨cone (σ ++ τ), ⟨memB_cone _, cone τ, hτ, (prepend_cone σ τ).le⟩, σ ++ τ, rfl, hval⟩

end Scott1980.Neighborhood.Example23

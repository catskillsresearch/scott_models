/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Approximable
import Scott1980.Neighborhood.ExampleB

/-!
# Example 2.4 (Scott 1981, PRG-19, §2) — eliminating the first run of `1`'s, `g : B → B`

Scott's second approximable mapping reads a binary sequence left to right and "eliminates the first
consecutive run of `1`'s while copying all the other digits." Thus

`g(0ⁿ 1ᵏ 0 x) = 0ⁿ⁺¹ x`   (for `k > 0`),   `g(1^∞) = ⊥`,   `g(0ⁿ 1^∞) = 0ⁿ`.

It is instructive because it turns *total* inputs (e.g. `1^∞`) into *partial* outputs.

We give the **guaranteed finite output** `out : Σ* → Σ*` for each finite input prefix via a two-state
scan: `out` copies leading `0`'s and, on the first `1`, hands over to `del`, which swallows the run
of `1`'s and — on the terminating `0` — emits that single `0` and copies the rest verbatim. The
elementwise value on the finite element `↑(σΣ*)` is `↑((out σ)Σ*)`, so the neighbourhood relation is

`X g Y ↔ ∃ σ, X = σΣ* ∧ (out σ)Σ* ⊆ Y ∧ Y ∈ B`.

`out` is prefix-monotone (`out_mono`: `σ <+: σ' → out σ <+: out σ'`), which gives Definition
2.1(iii); (i) and (ii) are the principal-filter facts for the cone `(out σ)Σ*`. Constructive.

**Exercise 2.17, second half.** Scott also asks to show that `runMap` is *uniquely* determined
among approximable mappings by the four equations `g(0x) = 0g(x)`, `g(11x) = g(1x)`,
`g(10x) = 0x`, `g(1) = ⊥` (`SatisfiesRunEquations`). We check `runMap` itself satisfies them
(`runMap_satisfies`, using the two "shift formulas" `runMap_toElementMap_sigmaElt` /
`sigmaElt_runMap_toElementMap`, so the statement is non-vacuous) and then prove uniqueness
(`eq_runMap_of_satisfies`): the recursive core (`key`) pins down any such `g` on every principal
element `σ⊥`, peeling *one* token of `σ` at a time, mirroring `out`'s own case split; the base case
`σ = []` is the only place order theory (`B.bot_le`) enters, everything else being pure
substitution into the equations. Constructive except for the `by_cases` in `ApproximableMap.ext`
(`#print axioms ⊆ {propext, Classical.choice, Quot.sound}`). -/

namespace Scott1980.Neighborhood.Example24

open Scott1980.Neighborhood NeighborhoodSystem ExampleB

/-- Inside the first run of `1`'s: swallow `1`'s; on the first `0`, emit it and copy the rest. -/
def del : Str → Str
  | [] => []
  | true :: t => del t
  | false :: t => false :: t

@[simp] theorem del_nil : del [] = [] := rfl
@[simp] theorem del_true (t : Str) : del (true :: t) = del t := rfl
@[simp] theorem del_false (t : Str) : del (false :: t) = false :: t := rfl

/-- The guaranteed output prefix: copy leading `0`'s; on the first `1`, eliminate the run via `del`.
-/
def out : Str → Str
  | [] => []
  | false :: t => false :: out t
  | true :: t => del t

@[simp] theorem out_nil : out [] = [] := rfl
@[simp] theorem out_false (t : Str) : out (false :: t) = false :: out t := rfl
@[simp] theorem out_true (t : Str) : out (true :: t) = del t := rfl

/-- `del` only grows under extension: `del s <+: del (s ++ t)`. -/
theorem del_append (s t : Str) : del s <+: del (s ++ t) := by
  induction s with
  | nil => simp
  | cons c s₀ ih =>
    cases c with
    | true => simpa using ih
    | false => exact ⟨t, rfl⟩

/-- `out` only grows under extension: `out σ <+: out (σ ++ t)`. -/
theorem out_append (σ t : Str) : out σ <+: out (σ ++ t) := by
  induction σ with
  | nil => simp
  | cons c σ₀ ih =>
    cases c with
    | true => simpa using del_append σ₀ t
    | false =>
      simp only [List.cons_append, out_false]
      obtain ⟨u, hu⟩ := ih
      exact ⟨u, by rw [List.cons_append, hu]⟩

/-- **Prefix-monotonicity of the output.** Extending the input prefix can only extend the guaranteed
output: `σ <+: σ' → out σ <+: out σ'`. This is the heart of Definition 2.1(iii) for `g`. -/
theorem out_mono {σ σ' : Str} (h : σ <+: σ') : out σ <+: out σ' := by
  obtain ⟨t, rfl⟩ := h
  exact out_append σ t

/-- **A leading `0` always emits it and continues copying.** `out([0]++τ) = 0::out τ`, for every
tail `τ`. (Exercise 2.17's first equation, at the token level.) -/
theorem out_append_false (τ : Str) : out ([false] ++ τ) = false :: out τ := rfl

/-- **A second consecutive `1` changes nothing.** `out([1,1]++τ) = out([1]++τ)`: once inside the
run of `1`'s, an extra `1` is simply swallowed by `del`. (Exercise 2.17's second equation, at the
token level — the recursive step behind the uniqueness argument for `runMap`.) -/
theorem out_append_trueTrue (τ : Str) : out ([true, true] ++ τ) = out ([true] ++ τ) := rfl

/-- **`10` terminates the run and emits the `0`, whatever follows.** `out([1,0]++τ) = 0::τ`, for
every tail `τ`. (Exercise 2.17's third equation, at the token level.) -/
theorem out_append_trueFalse (τ : Str) : out ([true, false] ++ τ) = false :: τ := rfl

/-- Cons-form restatement of `out_append_trueTrue`, for peeling one token at a time in `key`. -/
theorem out_true_true (t : Str) : out (true :: true :: t) = out (true :: t) := rfl

/-- Cons-form restatement of `out_append_trueFalse`, for peeling one token at a time in `key`. -/
theorem out_true_false (t : Str) : out (true :: false :: t) = false :: t := rfl

/-- **Example 2.4 — the run-eliminating mapping `g : B → B`.** `X g Y` iff `X = σΣ*` and the cone of
the guaranteed output `(out σ)Σ*` approximates `Y`. Definition 2.1: (i) `out [] = []` so `Δ g Δ`;
(ii) a fixed cone has a unique prefix, and the value is the principal filter `↑((out σ)Σ*)`, closed
under `∩`; (iii) `out_mono` shrinks the output cone as the input cone shrinks. -/
def runMap : ApproximableMap B B where
  rel X Y := ∃ σ, X = cone σ ∧ B.mem Y ∧ cone (out σ) ⊆ Y
  rel_dom := fun ⟨σ, hX, _, _⟩ => ⟨σ, hX⟩
  rel_cod := fun ⟨_, _, hYmem, _⟩ => hYmem
  master_rel := by
    refine ⟨[], (B_master).trans cone_nil.symm, B.master_mem, ?_⟩
    rw [out_nil, B_master, cone_nil]
  inter_right := by
    rintro X Y Y' ⟨σ, hX, hYmem, hYsub⟩ ⟨σ', hX', hY'mem, hY'sub⟩
    have hσ : σ = σ' := cone_injective (hX ▸ hX')
    subst hσ
    have hsub : cone (out σ) ⊆ Y ∩ Y' := Set.subset_inter hYsub hY'sub
    exact ⟨σ, hX, B.inter_mem hYmem hY'mem (memB_cone (out σ)) hsub, hsub⟩
  mono := by
    rintro X X' Y Y' ⟨σ, hX, _, hYsub⟩ hX'X hYY' hX'mem hY'mem
    obtain ⟨σ', hX'cone⟩ := hX'mem
    have hpre : σ <+: σ' := by
      apply cone_subset_cone.mp
      rw [← hX'cone, ← hX]; exact hX'X
    have hcone : cone (out σ') ⊆ cone (out σ) := cone_subset_cone.mpr (out_mono hpre)
    exact ⟨σ', hX'cone, hY'mem, (hcone.trans hYsub).trans hYY'⟩

/-! ## `runMap`'s relation and elementwise value, read off cones (mirrors `Example23`). -/

/-- **`runMap`'s relation on a cone, read off.** `σΣ* g Y ↔ Y ∈ B ∧ (out σ)Σ* ⊆ Y` — the defining
existential collapses since a cone has a *unique* generating prefix (`cone_injective`). -/
theorem runMap_rel_cone (σ : Str) (Y : Set Str) :
    runMap.rel (cone σ) Y ↔ B.mem Y ∧ cone (out σ) ⊆ Y := by
  constructor
  · rintro ⟨ρ, hρ, hYmem, hsub⟩
    obtain rfl : ρ = σ := (cone_injective hρ).symm
    exact ⟨hYmem, hsub⟩
  · rintro ⟨hYmem, hsub⟩
    exact ⟨σ, rfl, hYmem, hsub⟩

/-- **`runMap`'s elementwise value, read off cone-by-cone.** `g(x).mem Y` iff *some* cone
`σΣ* ∈ x` already witnesses `Y ∈ B` and `(out σ)Σ* ⊆ Y`. -/
theorem runMap_toElementMap_mem (x : B.Element) (Y : Set Str) :
    (runMap.toElementMap x).mem Y ↔ ∃ τ, x.mem (cone τ) ∧ B.mem Y ∧ cone (out τ) ⊆ Y := by
  constructor
  · rintro ⟨X, hX, hrel⟩
    obtain ⟨τ, rfl⟩ := x.sub hX
    exact ⟨τ, hX, (runMap_rel_cone τ Y).mp hrel⟩
  · rintro ⟨τ, hτ, hYmem, hsub⟩
    exact ⟨cone τ, hτ, (runMap_rel_cone τ Y).mpr ⟨hYmem, hsub⟩⟩

/-- **The "shift formula" for `runMap` (input side).** Reading off `g(σx)` depends on `x` only
through *some* cone `cone τ ∈ x`, via the output of the concatenation `σ ++ τ`: any deeper cone in
`sigmaElt`'s built-in up-closure is subsumed by monotonicity (`out_mono`), so the longest one —
`σ ++ τ` itself — already witnesses the answer. -/
theorem runMap_toElementMap_sigmaElt (σ : Str) (x : B.Element) (Y : Set Str) :
    (runMap.toElementMap (sigmaElt σ x)).mem Y ↔
      ∃ τ, x.mem (cone τ) ∧ B.mem Y ∧ cone (out (σ ++ τ)) ⊆ Y := by
  constructor
  · rintro ⟨Z, ⟨_, X, hX, hsub⟩, ρ, rfl, hYmem, hsubOut⟩
    obtain ⟨τ, rfl⟩ := x.sub hX
    rw [prepend_cone] at hsub
    exact ⟨τ, hX, hYmem, (cone_subset_cone.mpr (out_mono (cone_subset_cone.mp hsub))).trans hsubOut⟩
  · rintro ⟨τ, hτ, hYmem, hsub⟩
    exact ⟨cone (σ ++ τ), ⟨memB_cone _, cone τ, hτ, (prepend_cone σ τ).le⟩,
      (runMap_rel_cone (σ ++ τ) Y).mpr ⟨hYmem, hsub⟩⟩

/-- **The "shift formula" for `runMap` (output side).** Since `g(x)`'s membership predicate is
itself a cone-monotone family (`runMap_toElementMap_mem`), prepending `τ₀` to `g(x)` collapses the
same way: the up-closure of neighbourhoods `Z ⊇ (out τ)Σ*` is absorbed because `(out τ)Σ*` itself
is the *deepest* (hence hardest-to-satisfy, so witness-minimal) choice. -/
theorem sigmaElt_runMap_toElementMap (τ₀ : Str) (x : B.Element) (Y : Set Str) :
    (sigmaElt τ₀ (runMap.toElementMap x)).mem Y ↔
      ∃ τ, x.mem (cone τ) ∧ B.mem Y ∧ cone (τ₀ ++ out τ) ⊆ Y := by
  constructor
  · rintro ⟨hYmem, Z, hZ, hsub⟩
    obtain ⟨τ, hτ, _, hZsub⟩ := (runMap_toElementMap_mem x Z).mp hZ
    refine ⟨τ, hτ, hYmem, ?_⟩
    rw [← prepend_cone]
    exact (prepend_mono τ₀ hZsub).trans hsub
  · rintro ⟨τ, hτ, hYmem, hsub⟩
    refine ⟨hYmem, cone (out τ),
      (runMap_toElementMap_mem x _).mpr ⟨τ, hτ, memB_cone _, subset_rfl⟩, ?_⟩
    rw [prepend_cone]
    exact hsub

/-! ## Exercise 2.17, second half — `runMap` is *uniquely* determined by its equations -/

/-- **The four equations of Exercise 2.17.** `g(0x) = 0g(x)`, `g(11x) = g(1x)`, `g(10x) = 0x` for
*every* `x : |B|`, plus the single value equation `g(1) = ⊥` (this last one is *not* quantified
over `x`: it pins down `g` at the single finite element `1⊥`, matching Scott's literal statement
"`g(1) = ⊥`"). -/
structure SatisfiesRunEquations (g : ApproximableMap B B) : Prop where
  zero : ∀ x : B.Element, g.toElementMap (sigmaElt [false] x) = sigmaElt [false] (g.toElementMap x)
  oneOne : ∀ x : B.Element, g.toElementMap (sigmaElt [true, true] x) = g.toElementMap (sigmaElt [true] x)
  oneZero : ∀ x : B.Element, g.toElementMap (sigmaElt [true, false] x) = sigmaElt [false] x
  one : g.toElementMap (sigmaElt [true] B.bot) = B.bot

/-- **`runMap` satisfies its own defining equations.** `zero`/`oneOne`/`oneZero` are direct
instances of the two "shift formulas" (`runMap_toElementMap_sigmaElt` on the input side,
`sigmaElt_runMap_toElementMap` on the output side), using that the output of a leading `0`
(resp. `11`, `10`) is fixed by `out_append_false`/`out_append_trueTrue`/`out_append_trueFalse`
regardless of the tail. `one` reads off the unique cone (`Λ`) that `⊥` sits in
(`bot_mem_cone_iff`), where `out [true] = []`. -/
theorem runMap_satisfies : SatisfiesRunEquations runMap where
  zero x := by
    apply Element.ext
    intro Y
    rw [runMap_toElementMap_sigmaElt, sigmaElt_runMap_toElementMap]
    constructor
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      exact ⟨τ, hτ, hYmem, by rwa [out_append_false] at hsub⟩
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      exact ⟨τ, hτ, hYmem, by rwa [out_append_false]⟩
  oneOne x := by
    apply Element.ext
    intro Y
    rw [runMap_toElementMap_sigmaElt, runMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      exact ⟨τ, hτ, hYmem, by rwa [out_append_trueTrue] at hsub⟩
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      exact ⟨τ, hτ, hYmem, by rwa [← out_append_trueTrue] at hsub⟩
  oneZero x := by
    apply Element.ext
    intro Y
    rw [runMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      rw [out_append_trueFalse] at hsub
      exact ⟨hYmem, cone τ, hτ, by rw [prepend_cone]; exact hsub⟩
    · rintro ⟨hYmem, X, hX, hsub⟩
      obtain ⟨τ, rfl⟩ := x.sub hX
      rw [prepend_cone] at hsub
      exact ⟨τ, hX, hYmem, by rwa [out_append_trueFalse]⟩
  one := by
    apply Element.ext
    intro Y
    rw [runMap_toElementMap_sigmaElt]
    constructor
    · rintro ⟨τ, hτ, hYmem, hsub⟩
      obtain rfl : τ = [] := bot_mem_cone_iff.mp hτ
      rw [show out ([true] ++ ([] : Str)) = ([] : Str) from rfl, cone_nil] at hsub
      rw [mem_bot]
      exact Set.eq_univ_of_univ_subset hsub
    · intro hY
      rw [mem_bot] at hY
      refine ⟨[], bot_mem_cone_iff.mpr rfl, hY ▸ B.master_mem, ?_⟩
      rw [show out ([true] ++ ([] : Str)) = ([] : Str) from rfl, cone_nil, hY, B_master]

/-- **The recursive core of uniqueness.** Any `g` satisfying the four equations agrees with
`runMap` on every principal (finite) element `σ⊥`. The recursion peels *one* token at a time,
matching `out`'s own case split: a leading `0` recurses via `hg.zero` (`Basic decreasing case`);
inside a run of `1`'s, a further `1` recurses via `hg.oneOne` (peeling to `1τ`, still one token
shorter); a `1` followed by `0` is pinned *directly* by `hg.oneZero` for any tail (no recursion);
the lone token `1` (nothing more) is pinned directly by `hg.one`; and the base case `σ = []` is
the one place order theory enters: `⊥ ≤ 1⊥` forces `g(⊥) ≤ g(1⊥) = ⊥` by monotonicity, and `⊥` is
already the least element, so `g(⊥) = ⊥`. -/
theorem key (g : ApproximableMap B B) (hg : SatisfiesRunEquations g) :
    ∀ σ : Str, g.toElementMap (sigmaElt σ B.bot) = sigmaElt (out σ) B.bot
  | [] => by
      rw [show out ([] : Str) = ([] : Str) from rfl, sigmaElt_nil]
      have hm := g.toElementMap_mono (B.bot_le (sigmaElt [true] B.bot))
      rw [hg.one] at hm
      exact le_antisymm hm (B.bot_le _)
  | [true] => by
      rw [show out [true] = ([] : Str) from rfl, sigmaElt_nil]
      exact hg.one
  | true :: false :: t => by
      rw [out_true_false, show (true :: false :: t : Str) = [true, false] ++ t from rfl,
        sigmaElt_append, hg.oneZero, ← sigmaElt_append]
      rfl
  | true :: true :: t => by
      rw [out_true_true, show (true :: true :: t : Str) = [true, true] ++ t from rfl,
        sigmaElt_append, hg.oneOne, ← sigmaElt_append]
      exact key g hg (true :: t)
  | false :: t => by
      rw [out_false, show (false :: t : Str) = [false] ++ t from rfl, sigmaElt_append, hg.zero,
        key g hg t, show (false :: out t : Str) = [false] ++ out t from rfl, sigmaElt_append]

/-- **Exercise 2.17, second half.** `runMap` is the *unique* approximable map `B → B` satisfying
`g(0x) = 0g(x)`, `g(11x) = g(1x)`, `g(10x) = 0x`, `g(1) = ⊥`. Every neighbourhood of `B` is a cone
(`memB_cone`), so `ApproximableMap.ext` reduces `g = runMap` to matching relations on cones, which
is exactly `key` read through `rel_iff_mem_principal`/`runMap_rel_cone`. -/
theorem eq_runMap_of_satisfies {g : ApproximableMap B B} (hg : SatisfiesRunEquations g) :
    g = runMap := by
  apply ApproximableMap.ext
  intro X Y
  by_cases hX : B.mem X
  · obtain ⟨σ, rfl⟩ := hX
    rw [g.rel_iff_mem_principal (memB_cone σ)]
    show (g.toElementMap (sigmaBot σ)).mem Y ↔ runMap.rel (cone σ) Y
    rw [← sigmaElt_bot, key g hg σ, sigmaElt_bot, runMap_rel_cone]
    show (B.principal (memB_cone (out σ))).mem Y ↔ B.mem Y ∧ cone (out σ) ⊆ Y
    exact B.mem_principal (memB_cone (out σ))
  · exact ⟨fun hr => absurd (g.rel_dom hr) hX, fun hr => absurd (runMap.rel_dom hr) hX⟩

end Scott1980.Neighborhood.Example24

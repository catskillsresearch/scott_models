/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Exercise722Regular
import Mathlib.Computability.EpsilonNFA

/-!
# Exercise 7.22 — the concatenation automaton (the crux mathlib lacks)

mathlib provides NFA/εNFA/DFA with intersection (`DFA.inter`) and complement, but **no
language-concatenation automaton**. This file builds one and proves it correct, choice-free.

Given two NFAs `M₁`, `M₂` we form an `εNFA` `catEps M₁ M₂` on the sum state type `σ₁ ⊕ σ₂`:
copies of `M₁` (on the `inl` side) and `M₂` (on the `inr` side), with an **ε-edge from every
accept state of `M₁` to every start state of `M₂`**. The headline result is

  `(catEps M₁ M₂).accepts = M₁.accepts * M₂.accepts`   (`catEps_accepts`)

proved via the closed form (`catEps_eval`)

  `(catEps M₁ M₂).eval x = inl '' (M₁.eval x) ∪ inr '' { t | ∃ u v, x = u ++ v ∧ u ∈ M₁.accepts ∧
                                                                  t ∈ M₂.eval v }`

i.e. the reachable `inr`-states after reading `x` are exactly the `M₂`-states reachable from some
split `x = u ++ v` with the `M₁`-prefix `u` accepted. The `Sum` state type stays `Fintype`, so this
plugs into the `Fintype`-DFA/NFA decision route (`Exercise722DFA.lean`).
-/

namespace Scott1980.Neighborhood

namespace Exercise722

open scoped Computability
open Sum Set

variable {σ₁ σ₂ : Type}

/-- The concatenation `εNFA`: `M₁` on `inl`, `M₂` on `inr`, ε-edges from `M₁`-accept to `M₂`-start. -/
def catEps (M₁ : NFA Bool σ₁) (M₂ : NFA Bool σ₂) : εNFA Bool (σ₁ ⊕ σ₂) where
  step s a :=
    match s, a with
    | inl s, some c => inl '' M₁.step s c
    | inl s, none   => {t | s ∈ M₁.accept ∧ t ∈ inr '' M₂.start}
    | inr s, some c => inr '' M₂.step s c
    | inr _, none   => ∅
  start := inl '' M₁.start
  accept := inr '' M₂.accept

variable (M₁ : NFA Bool σ₁) (M₂ : NFA Bool σ₂)

@[simp] theorem catEps_step_inl_some (s : σ₁) (c : Bool) :
    (catEps M₁ M₂).step (inl s) (some c) = inl '' M₁.step s c := rfl
@[simp] theorem catEps_step_inl_none (s : σ₁) :
    (catEps M₁ M₂).step (inl s) none = {t | s ∈ M₁.accept ∧ t ∈ inr '' M₂.start} := rfl
@[simp] theorem catEps_step_inr_some (s : σ₂) (c : Bool) :
    (catEps M₁ M₂).step (inr s) (some c) = inr '' M₂.step s c := rfl
@[simp] theorem catEps_step_inr_none (s : σ₂) :
    (catEps M₁ M₂).step (inr s) none = ∅ := rfl
@[simp] theorem catEps_start : (catEps M₁ M₂).start = inl '' M₁.start := rfl
@[simp] theorem catEps_accept : (catEps M₁ M₂).accept = inr '' M₂.accept := rfl

/-- ε-closure: the only ε-edges go from an `inl`-accept state to `inr`-start states, so the closure
of `T` adds `inr '' M₂.start` exactly when `T` already contains some `inl`-accept state. -/
theorem catEps_mem_εClosure_iff (T : Set (σ₁ ⊕ σ₂)) (s : σ₁ ⊕ σ₂) :
    s ∈ (catEps M₁ M₂).εClosure T ↔
      s ∈ T ∨ ((∃ q ∈ M₁.accept, (inl q : σ₁ ⊕ σ₂) ∈ T) ∧ s ∈ inr '' M₂.start) := by
  constructor
  · intro h
    induction h with
    | base s hs => exact Or.inl hs
    | @step u t ht _hclos ih =>
      -- a `none`-step `u → t`; nonempty only when `u = inl q`, `q ∈ M₁.accept`, `t ∈ inr '' start`
      cases u with
      | inl q =>
        rcases ih with hT | ⟨_, hmem⟩
        · simp only [catEps_step_inl_none, mem_setOf_eq] at ht
          exact Or.inr ⟨⟨q, ht.1, hT⟩, ht.2⟩
        · obtain ⟨w, _, hw⟩ := hmem; exact absurd hw.symm (by simp)
      | inr q => simp only [catEps_step_inr_none] at ht; exact absurd ht (by simp)
  · rintro (hs | ⟨⟨q, hq, hqT⟩, hs⟩)
    · exact εNFA.εClosure.base s hs
    · obtain ⟨t, ht, rfl⟩ := hs
      have hbase : (inl q : σ₁ ⊕ σ₂) ∈ (catEps M₁ M₂).εClosure T := εNFA.εClosure.base _ hqT
      refine εNFA.εClosure.step (inl q) (inr t) ?_ hbase
      simp only [catEps_step_inl_none, mem_setOf_eq]
      exact ⟨hq, t, ht, rfl⟩

/-- **Closed form for `eval`.** After reading `x`, the reachable `inl`-states mirror `M₁.eval x`, and
the reachable `inr`-states are exactly the `M₂`-states reachable from some prefix-split `x = u ++ v`
with the `M₁`-prefix `u` accepted. This is the engine behind `catEps_accepts`. -/
theorem catEps_mem_eval_iff (x : List Bool) (s : σ₁ ⊕ σ₂) :
    s ∈ (catEps M₁ M₂).eval x ↔
      (∃ s₁, s = inl s₁ ∧ s₁ ∈ M₁.eval x) ∨
      (∃ t, s = inr t ∧ ∃ u v, x = u ++ v ∧ u ∈ M₁.accepts ∧ t ∈ M₂.eval v) := by
  induction x using List.reverseRecOn generalizing s with
  | nil =>
    show s ∈ (catEps M₁ M₂).εClosure (catEps M₁ M₂).start ↔ _
    rw [catEps_start, catEps_mem_εClosure_iff]
    constructor
    · rintro (hs | ⟨⟨q, hq, hqs⟩, hs⟩)
      · obtain ⟨s₁, hs₁, rfl⟩ := hs
        exact Or.inl ⟨s₁, rfl, hs₁⟩
      · obtain ⟨t, ht, rfl⟩ := hs
        refine Or.inr ⟨t, rfl, [], [], rfl, ?_, ht⟩
        obtain ⟨q', hq', hqq⟩ := hqs
        cases hqq
        exact ⟨q, hq, hq'⟩
    · rintro (⟨s₁, rfl, hs₁⟩ | ⟨t, rfl, u, v, hx, hu, hv⟩)
      · exact Or.inl ⟨s₁, hs₁, rfl⟩
      · obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp hx.symm
        obtain ⟨q, hq, hqstart⟩ := hu
        exact Or.inr ⟨⟨q, hq, q, hqstart, rfl⟩, t, hv, rfl⟩
  | append_singleton x a ih =>
    rw [εNFA.eval_append_singleton, εNFA.mem_stepSet_iff]
    constructor
    · rintro ⟨t, ht, hs⟩
      rw [ih] at ht
      rcases ht with ⟨s₁, rfl, hs₁⟩ | ⟨t₂, rfl, u, v, hx, hu, hv⟩
      · -- came from an `inl` state of `M₁`
        rw [catEps_step_inl_some, catEps_mem_εClosure_iff] at hs
        rcases hs with hs | ⟨⟨q, hq, hqmem⟩, hs⟩
        · -- still in `M₁`: extends the `inl` form
          obtain ⟨s', hs', rfl⟩ := hs
          exact Or.inl ⟨s', rfl, by rw [NFA.eval_append_singleton, NFA.mem_stepSet]; exact ⟨s₁, hs₁, hs'⟩⟩
        · -- `M₁` just reached an accept state on reading `a`: cross to `M₂` (split `v = []`)
          obtain ⟨q', hq', hqq⟩ := hqmem
          cases hqq
          obtain ⟨t', ht', rfl⟩ := hs
          refine Or.inr ⟨t', rfl, x ++ [a], [], (List.append_nil _).symm, ?_, ht'⟩
          rw [NFA.mem_accepts]
          refine ⟨q, hq, ?_⟩
          change q ∈ M₁.eval (x ++ [a])
          rw [NFA.eval_append_singleton, NFA.mem_stepSet]
          exact ⟨s₁, hs₁, hq'⟩
      · -- came from an `inr` state of `M₂`: extends the `inr` form (split `v ↦ v ++ [a]`)
        rw [catEps_step_inr_some, catEps_mem_εClosure_iff] at hs
        rcases hs with hs | ⟨⟨q, _, hqmem⟩, _⟩
        · obtain ⟨t', ht', rfl⟩ := hs
          refine Or.inr ⟨t', rfl, u, v ++ [a], by rw [hx, List.append_assoc], hu, ?_⟩
          rw [NFA.eval_append_singleton, NFA.mem_stepSet]; exact ⟨t₂, hv, ht'⟩
        · exact absurd hqmem (by simp)
    · rintro (⟨s', rfl, hs'⟩ | ⟨t', rfl, u, v, hx, hu, hv⟩)
      · -- `inl` form: step `M₁` one more
        rw [NFA.eval_append_singleton, NFA.mem_stepSet] at hs'
        obtain ⟨s₁, hs₁, hstep⟩ := hs'
        exact ⟨inl s₁, (ih (inl s₁)).mpr (Or.inl ⟨s₁, rfl, hs₁⟩),
          by rw [catEps_step_inl_some, catEps_mem_εClosure_iff]; exact Or.inl ⟨s', hstep, rfl⟩⟩
      · -- `inr` form: the split `x ++ [a] = u ++ v`; cases on whether `v` is empty
        rcases List.eq_nil_or_concat v with rfl | ⟨v', c, rfl⟩
        · -- `v = []`: `u = x ++ [a] ∈ L₁`; cross via the ε-edge after reading `a`
          rw [List.append_nil] at hx; subst hx
          rw [NFA.mem_accepts] at hu
          obtain ⟨q, hq, hqe⟩ := hu
          change q ∈ M₁.eval (x ++ [a]) at hqe
          rw [NFA.eval_append_singleton, NFA.mem_stepSet] at hqe
          obtain ⟨s₁, hs₁, hstep⟩ := hqe
          refine ⟨inl s₁, (ih (inl s₁)).mpr (Or.inl ⟨s₁, rfl, hs₁⟩), ?_⟩
          rw [catEps_step_inl_some, catEps_mem_εClosure_iff]
          exact Or.inr ⟨⟨q, hq, q, hstep, rfl⟩, t', hv, rfl⟩
        · -- `v = v' ++ [c]`: necessarily `c = a`, `x = u ++ v'`; step `M₂` one more
          rw [List.concat_eq_append] at hx hv
          rw [← List.append_assoc] at hx
          obtain ⟨hxe, hac⟩ := List.append_inj' hx rfl
          have hca : c = a := by simpa using hac.symm
          subst hca
          rw [NFA.eval_append_singleton, NFA.mem_stepSet] at hv
          obtain ⟨t₂, ht₂, hstep⟩ := hv
          refine ⟨inr t₂, (ih (inr t₂)).mpr (Or.inr ⟨t₂, rfl, u, v', hxe, hu, ht₂⟩), ?_⟩
          rw [catEps_step_inr_some, catEps_mem_εClosure_iff]
          exact Or.inl ⟨t', hstep, rfl⟩

/-- **The concatenation automaton recognises exactly the concatenation language.** -/
theorem catEps_accepts :
    (catEps M₁ M₂).accepts = concat M₁.accepts M₂.accepts := by
  ext x
  constructor
  · rintro ⟨S, hS, hSeval⟩
    obtain ⟨t, ht, rfl⟩ := hS
    rw [catEps_mem_eval_iff] at hSeval
    rcases hSeval with ⟨s₁, hc, _⟩ | ⟨t', heq, u, v, hx, hu, hv⟩
    · exact absurd hc (by simp)
    · cases heq
      exact ⟨u, hu, v, ⟨t, ht, hv⟩, hx.symm⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    obtain ⟨t, ht, hteval⟩ := hv
    refine ⟨inr t, ⟨t, ht, rfl⟩, ?_⟩
    rw [catEps_mem_eval_iff]
    exact Or.inr ⟨t, rfl, u, v, rfl, hu, hteval⟩

/-- The concatenation automaton keeps a `Fintype` state space (so it plugs into the `Fintype`-based
decision route): `Sum` of two `Fintype`s is a `Fintype`. -/
example [Fintype σ₁] [Fintype σ₂] : Fintype (σ₁ ⊕ σ₂) := inferInstance

end Exercise722

end Scott1980.Neighborhood

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Exercise722Regular
import Mathlib.Computability.DFA
import Mathlib.Data.Fintype.Option

/-!
# Exercise 7.22 — toward effective givenness: explicit `Fintype` DFAs (WIP)

This is **work in progress** toward a choice-free decision procedure for the two Definition-7.1
relations of `Ssys` (`Exercise722.lean`), reduced in `Exercise722Regular.lean` to *language
equivalence on `SExpr`*. The plan (Route A): give every `SExpr` an explicit deterministic finite
automaton with a genuine `Fintype` state type, so that emptiness/equivalence become **structural**
finite searches (no Brzozowski-finiteness/ACI theorem needed).

mathlib supplies the closure operations we need *for free*:
* `DFA.inter` (`accepts_inter : (M₁.inter M₂).accepts = M₁.accepts ⊓ M₂.accepts`) — handles `cap`;
* `DFA.compl` (`accepts_compl`) + `inter` + emptiness — handles equivalence (`A = B ↔ A △ B = ∅`).

What mathlib does **not** supply, and what remains the crux (designated for a high-compute session):
* a **language-concatenation automaton** (`cat`): no NFA/εNFA concatenation exists in mathlib, so it
  must be built (εNFA with ε-links from `a`'s accept states to `b`'s start) and proved correct
  (`accepts = denote a * denote b`) via `εNFA.IsPath`/`isPath_append`;
* a `Finset`-based subset construction (mathlib's `NFA.n` determinizes to `Set σ`, which lacks
  `DecidableEq`), needed so the final emptiness/equivalence search is decidable data;
* the bridge from the resulting `Decidable` search to the project's `RecDecidable` (`Nat.Primrec`).

**This file (Medium pass) provides the leaf automata, proven correct, and the framework.** The `cat`
construction and the decision bridge are the remaining (high-compute) work.
-/

namespace Scott1980.Neighborhood

namespace Exercise722

open scoped Computability

/-! ## `Σ` (the universal language) -/

/-- The one-state DFA recognising `Σ = {0,1}*` (every word accepted). -/
def sigmaDFA : DFA Bool Unit where
  step _ _ := ()
  start := ()
  accept := Set.univ

@[simp] theorem sigmaDFA_accepts : sigmaDFA.accepts = Set.univ :=
  Set.eq_univ_of_forall fun _ => Set.mem_univ _

theorem sigmaDFA_accepts_denote : sigmaDFA.accepts = denote .sigma := by
  rw [sigmaDFA_accepts, denote_sigma]

/-! ## A singleton `{σ}` -/

/-- States of the single-word DFA for `σ`: `some i` means "the input so far is the length-`i` prefix
of `σ`" (`i ≤ |σ|`); `none` is the dead/sink state (input has diverged from `σ`). -/
abbrev SingleState (σ : List Bool) : Type := Option (Fin (σ.length + 1))

/-- The single-word DFA recognising `{σ}`. From `some i` (`i < |σ|`) reading the correct next
character advances to `some (i+1)`; any mismatch — or any character once `σ` is fully consumed — goes
to the dead state `none`. -/
def singleDFA (σ : List Bool) : DFA Bool (SingleState σ) where
  step s b := s.bind fun i =>
    if h : (i : ℕ) < σ.length then
      if σ.get ⟨i, h⟩ = b then some ⟨i + 1, by omega⟩ else none
    else none
  start := some ⟨0, by omega⟩
  accept := {some ⟨σ.length, by omega⟩}

/-- The dead state `none` is a sink. -/
theorem singleDFA_evalFrom_none (σ : List Bool) (w : List Bool) :
    (singleDFA σ).evalFrom none w = none := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [DFA.evalFrom_cons]; exact ih

/-- From state `some k`, reading `w` reaches `some (k+|w|)` exactly when `w` is a prefix of the
suffix `σ.drop k` (i.e. `w` continues `σ` from position `k` without diverging); otherwise it dies. -/
theorem singleDFA_evalFrom (σ : List Bool) (w : List Bool) (k : Fin (σ.length + 1)) :
    (singleDFA σ).evalFrom (some k) w =
      if h : w <+: List.drop (k : ℕ) σ
      then some ⟨(k : ℕ) + w.length, by
        have hlen := h.length_le
        rw [List.length_drop] at hlen
        have := k.isLt
        omega⟩
      else none := by
  induction w generalizing k with
  | nil =>
    rw [DFA.evalFrom_nil, dif_pos List.nil_prefix]
    simp
  | cons b w ih =>
    rw [DFA.evalFrom_cons]
    show (singleDFA σ).evalFrom ((singleDFA σ).step (some k) b) w = _
    by_cases hk : (k : ℕ) < σ.length
    · have hdrop : List.drop (k : ℕ) σ = σ.get ⟨k, hk⟩ :: List.drop ((k : ℕ) + 1) σ := by
        rw [List.get_eq_getElem]; exact List.drop_eq_getElem_cons hk
      have hcondiff : ((b :: w) <+: List.drop (k : ℕ) σ) ↔ (b = σ.get ⟨k, hk⟩ ∧ w <+: List.drop ((k : ℕ) + 1) σ) := by
        rw [hdrop, List.cons_prefix_cons]
      by_cases hchar : σ.get ⟨k, hk⟩ = b
      · have hstep : (singleDFA σ).step (some k) b = some ⟨(k : ℕ) + 1, by omega⟩ := by
          simp only [singleDFA, Option.bind_some, dif_pos hk, if_pos hchar]
        rw [hstep, ih ⟨(k : ℕ) + 1, by omega⟩]
        by_cases hpre : w <+: List.drop ((k : ℕ) + 1) σ
        · rw [dif_pos hpre, dif_pos (hcondiff.mpr ⟨hchar.symm, hpre⟩)]
          congr 1
          apply Fin.ext
          simp only [List.length_cons]
          omega
        · rw [dif_neg hpre, dif_neg (fun hc => hpre (hcondiff.mp hc).2)]
      · have hstep : (singleDFA σ).step (some k) b = none := by
          simp only [singleDFA, Option.bind_some, dif_pos hk, if_neg hchar]
        rw [hstep, singleDFA_evalFrom_none, dif_neg]
        intro hc
        exact hchar (hcondiff.mp hc).1.symm
    · have hstep : (singleDFA σ).step (some k) b = none := by
        simp only [singleDFA, Option.bind_some, dif_neg hk]
      rw [hstep, singleDFA_evalFrom_none, dif_neg]
      have hd : List.drop (k : ℕ) σ = [] := by
        rw [List.drop_eq_nil_iff]; have := k.isLt; omega
      rw [hd]; exact (by simp : ¬ (b :: w) <+: [])

/-- **The single-word DFA recognises exactly `{σ}`.** -/
theorem singleDFA_accepts (σ : List Bool) : (singleDFA σ).accepts = {σ} := by
  ext w
  show (singleDFA σ).evalFrom (some ⟨0, by omega⟩) w ∈ (singleDFA σ).accept ↔ _
  rw [singleDFA_evalFrom]
  by_cases h : w <+: List.drop (0 : ℕ) (σ : List Bool)
  · rw [dif_pos h, List.drop_zero] at *
    show some (⟨0 + w.length, _⟩ : Fin (σ.length + 1)) ∈ ({some ⟨σ.length, _⟩} : Set _) ↔ w ∈ ({σ} : Set _)
    rw [Set.mem_singleton_iff, Set.mem_singleton_iff, Option.some.injEq, Fin.mk.injEq, Nat.zero_add]
    constructor
    · intro hlen; exact h.eq_of_length hlen
    · intro hw; subst hw; rfl
  · rw [dif_neg h, List.drop_zero] at *
    show (none : SingleState σ) ∈ ({some ⟨σ.length, _⟩} : Set _) ↔ w ∈ ({σ} : Set _)
    rw [Set.mem_singleton_iff, Set.mem_singleton_iff]
    constructor
    · intro hcontra; exact absurd hcontra (by simp)
    · intro hw; subst hw; exact absurd List.prefix_rfl h

theorem singleDFA_accepts_denote (σ : List Bool) : (singleDFA σ).accepts = denote (.single σ) := by
  rw [singleDFA_accepts]; exact (denote_single σ).symm

/-! ## Intersection (`cap`) and complement — free from mathlib

`cap` needs no new automaton: mathlib's `DFA.inter` is the product construction, and the resulting
state type `σ₁ × σ₂` keeps `Fintype`/`DecidableEq`. The wrapper below packages it against `denote`,
and `complDFA_accepts` records the complement (used to reduce equivalence to emptiness). -/

/-- The product DFA evaluates componentwise. (Choice-free; avoids mathlib's classical
`accepts_inter`.) -/
theorem inter_eval {σ₁ σ₂ : Type} (M₁ : DFA Bool σ₁) (M₂ : DFA Bool σ₂) (w : List Bool) :
    (M₁.inter M₂).eval w = (M₁.eval w, M₂.eval w) := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
    rw [DFA.eval_append_singleton, DFA.eval_append_singleton, DFA.eval_append_singleton, ih]
    rfl

/-- If `M₁`, `M₂` recognise `denote a`, `denote b`, their product DFA recognises `denote (a ∩ b)`. -/
theorem interDFA_accepts {σ₁ σ₂ : Type} (M₁ : DFA Bool σ₁) (M₂ : DFA Bool σ₂)
    (a b : SExpr) (h₁ : M₁.accepts = denote a) (h₂ : M₂.accepts = denote b) :
    (M₁.inter M₂).accepts = denote (.cap a b) := by
  rw [denote_cap, ← h₁, ← h₂]
  ext w
  constructor
  · intro hw
    have hp : (M₁.inter M₂).eval w ∈ (M₁.inter M₂).accept := hw
    rw [inter_eval] at hp
    exact hp
  · intro hw
    show (M₁.inter M₂).eval w ∈ (M₁.inter M₂).accept
    rw [inter_eval]
    exact hw

/-- The complement DFA recognises the set-complement of the original language (over all of `Σ*`).
(Choice-free; avoids mathlib's classical `accepts_compl`.) -/
theorem complDFA_accepts {σ : Type} (M : DFA Bool σ) (a : SExpr) (h : M.accepts = denote a) :
    (Mᶜ).accepts = (denote a)ᶜ := by
  rw [← h]
  ext w
  exact Iff.rfl

/-! ## State-space finiteness is structural

The whole point of Route A: the state types of the leaf/closure automata carry `Fintype` *and*
`DecidableEq` instances automatically (`Unit`, `Option (Fin _)`, products), so the eventual
emptiness/equivalence search is a finite, decidable computation — no Brzozowski-finiteness theorem is
needed. (`cat` will determinize to a `Finset`-state DFA, preserving both instances.) -/

example : Fintype (Unit) := inferInstance
example : DecidableEq (Unit) := inferInstance
example (σ : List Bool) : Fintype (SingleState σ) := by unfold SingleState; infer_instance
example (σ : List Bool) : DecidableEq (SingleState σ) := by unfold SingleState; infer_instance
example {σ₁ σ₂ : Type} [Fintype σ₁] [Fintype σ₂] : Fintype (σ₁ × σ₂) := inferInstance
example {σ₁ σ₂ : Type} [DecidableEq σ₁] [DecidableEq σ₂] : DecidableEq (σ₁ × σ₂) := inferInstance

end Exercise722

end Scott1980.Neighborhood

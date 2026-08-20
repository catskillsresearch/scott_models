/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Exercise722DFA
import Scott1980.Neighborhood.Exercise722Cat
import Scott1980.Neighborhood.Exercise722Words

/-!
# Exercise 7.22 — every fragment expression has a `Fintype` automaton (`denote e = accepts`)

Assembles the leaf automata (`Exercise722DFA.lean`) and the concatenation automaton
(`Exercise722Cat.lean`) into a single uniform recogniser

  `toNFA : (e : SExpr) → NFA Bool (autState e)`     with     `toNFA_accepts : (toNFA e).accepts = denote e`

where the state type `autState e` is a `Fintype` (built from `Unit`, `Option (Fin _)`, `×`, `⊕`).
This is the constructive, **choice-free** realisation of Scott's "the sets in `S` are regular events":
every fragment language is the accepted language of an explicit finite automaton. It is the platform
for the emptiness/equivalence decision procedure (and hence Definition 7.1 effective givenness).

The missing combinator beyond the leaves+`cat` is intersection, handled here by the standard product
construction `NFAinter` (mathlib has `DFA.inter` but no `NFA` intersection).
-/

namespace Scott1980.Neighborhood

namespace Exercise722

open scoped Computability
open Sum Set

variable {σ₁ σ₂ : Type}

section NFAinterLemmas

/-! ## NFA intersection (product) -/

/-- Product NFA recognising the intersection: states `σ₁ × σ₂`, stepping/starting/accepting
componentwise. -/
def NFAinter (M₁ : NFA Bool σ₁) (M₂ : NFA Bool σ₂) : NFA Bool (σ₁ × σ₂) where
  step s a := {t | t.1 ∈ M₁.step s.1 a ∧ t.2 ∈ M₂.step s.2 a}
  start := {s | s.1 ∈ M₁.start ∧ s.2 ∈ M₂.start}
  accept := {s | s.1 ∈ M₁.accept ∧ s.2 ∈ M₂.accept}

variable (M₁ : NFA Bool σ₁) (M₂ : NFA Bool σ₂)

theorem NFAinter_mem_eval_iff (x : List Bool) (p : σ₁ × σ₂) :
    p ∈ (NFAinter M₁ M₂).eval x ↔ p.1 ∈ M₁.eval x ∧ p.2 ∈ M₂.eval x := by
  induction x using List.reverseRecOn generalizing p with
  | nil => exact Iff.rfl
  | append_singleton x a ih =>
    rw [NFA.eval_append_singleton, NFA.mem_stepSet]
    constructor
    · rintro ⟨q, hq, hstep⟩
      rw [ih] at hq
      rw [NFA.eval_append_singleton, NFA.mem_stepSet, NFA.eval_append_singleton, NFA.mem_stepSet]
      exact ⟨⟨q.1, hq.1, hstep.1⟩, ⟨q.2, hq.2, hstep.2⟩⟩
    · rintro ⟨h1, h2⟩
      rw [NFA.eval_append_singleton, NFA.mem_stepSet] at h1 h2
      obtain ⟨q1, hq1, hs1⟩ := h1
      obtain ⟨q2, hq2, hs2⟩ := h2
      exact ⟨(q1, q2), (ih (q1, q2)).mpr ⟨hq1, hq2⟩, hs1, hs2⟩

theorem NFAinter_mem_accepts_iff (x : List Bool) :
    x ∈ (NFAinter M₁ M₂).accepts ↔ x ∈ M₁.accepts ∧ x ∈ M₂.accepts := by
  constructor
  · rintro ⟨p, hp, hpe⟩
    rw [NFAinter_mem_eval_iff] at hpe
    exact ⟨⟨p.1, hp.1, hpe.1⟩, ⟨p.2, hp.2, hpe.2⟩⟩
  · rintro ⟨⟨s, hs, hse⟩, ⟨t, ht, hte⟩⟩
    exact ⟨(s, t), ⟨hs, ht⟩, (NFAinter_mem_eval_iff M₁ M₂ x (s, t)).mpr ⟨hse, hte⟩⟩

end NFAinterLemmas

/-! ## Choice-free DFA → NFA recognition

mathlib's `DFA.toNFA_correct` depends on `Classical.choice`; we reprove it choice-free (the leaf
automata are DFAs, so the uniform `toNFA` must convert them without pulling choice). -/

/-- The NFA from a DFA tracks the single deterministic state as a singleton. -/
theorem dfaToNFA_eval {σ : Type} (M : DFA Bool σ) (x : List Bool) :
    M.toNFA.eval x = {M.eval x} := by
  induction x using List.reverseRecOn with
  | nil => rfl
  | append_singleton x a ih =>
    rw [NFA.eval_append_singleton, ih]
    ext s
    rw [NFA.mem_stepSet]
    constructor
    · rintro ⟨t, ht, hs⟩
      rw [Set.mem_singleton_iff] at ht
      subst ht
      rw [Set.mem_singleton_iff, DFA.eval_append_singleton]
      exact hs
    · intro hs
      rw [Set.mem_singleton_iff, DFA.eval_append_singleton] at hs
      exact ⟨M.eval x, Set.mem_singleton _, hs⟩

/-- Choice-free version of `DFA.toNFA_correct`. -/
theorem dfaToNFA_accepts {σ : Type} (M : DFA Bool σ) : M.toNFA.accepts = M.accepts := by
  ext x
  constructor
  · rintro ⟨S, hS, hSe⟩
    rw [dfaToNFA_eval, Set.mem_singleton_iff] at hSe
    rw [DFA.mem_accepts, ← hSe]
    exact hS
  · intro hx
    rw [DFA.mem_accepts] at hx
    exact ⟨M.eval x, hx, by rw [dfaToNFA_eval]; exact Set.mem_singleton _⟩

/-! ## The uniform recogniser `toNFA` -/

/-- State type of the automaton for an `SExpr` (a `Fintype`, see `instFintypeAutState`). -/
def autState : SExpr → Type
  | .sigma => Unit
  | .single σ => Option (Fin (σ.length + 1))
  | .cap a b => autState a × autState b
  | .cat a b => autState a ⊕ autState b

instance instFintypeAutState : (e : SExpr) → Fintype (autState e)
  | .sigma => inferInstanceAs (Fintype Unit)
  | .single σ => inferInstanceAs (Fintype (Option (Fin (σ.length + 1))))
  | .cap a b => by
      letI := instFintypeAutState a; letI := instFintypeAutState b
      exact inferInstanceAs (Fintype (autState a × autState b))
  | .cat a b => by
      letI := instFintypeAutState a; letI := instFintypeAutState b
      exact inferInstanceAs (Fintype (autState a ⊕ autState b))

instance instDecidableEqAutState : (e : SExpr) → DecidableEq (autState e)
  | .sigma => inferInstanceAs (DecidableEq Unit)
  | .single σ => inferInstanceAs (DecidableEq (Option (Fin (σ.length + 1))))
  | .cap a b => by
      letI := instDecidableEqAutState a; letI := instDecidableEqAutState b
      exact inferInstanceAs (DecidableEq (autState a × autState b))
  | .cat a b => by
      letI := instDecidableEqAutState a; letI := instDecidableEqAutState b
      exact inferInstanceAs (DecidableEq (autState a ⊕ autState b))

example : DecidableEq (autState (.sigma : SExpr)) := inferInstance
example : DecidableEq (autState (.single [true, false] : SExpr)) := inferInstance

/-- A crude upper bound on `Fintype.card (autState e)` (used to bound word search length). -/
def autStateCard : SExpr → ℕ
  | .sigma => 1
  | .single σ => σ.length + 2
  | .cap a b => autStateCard a * autStateCard b
  | .cat a b => autStateCard a + autStateCard b

theorem autStateCard_le_card (e : SExpr) : autStateCard e ≤ Fintype.card (autState e) := by
  induction e with
  | sigma => simp [autStateCard, autState]
  | single σ =>
    have heq : autStateCard (.single σ) = Fintype.card (autState (.single σ)) := by
      simp only [autStateCard, autState]
      have h1 : Fintype.card (Option (Fin (σ.length + 1))) =
          Fintype.card (Fin (σ.length + 1)) + 1 :=
        Fintype.card_option (α := Fin (σ.length + 1))
      have h2 : Fintype.card (Fin (σ.length + 1)) = σ.length + 1 :=
        Fintype.card_fin (σ.length + 1)
      calc σ.length + 2
          = (σ.length + 1) + 1 := rfl
        _ = Fintype.card (Fin (σ.length + 1)) + 1 := (congrArg (fun n => n + 1) h2).symm
        _ = Fintype.card (Option (Fin (σ.length + 1))) := h1.symm
    exact Nat.le_of_eq heq
  | cap a b ih_a ih_b =>
    simp only [autStateCard, autState]
    exact (Nat.mul_le_mul ih_a ih_b).trans (Fintype.card_prod (autState a) (autState b)).ge
  | cat a b ih_a ih_b =>
    simp only [autStateCard, autState]
    exact (Nat.add_le_add ih_a ih_b).trans (Fintype.card_sum (α := autState a) (β := autState b)).ge

/-- The uniform automaton for a fragment expression: leaves from `Exercise722DFA.lean`, `cap` by the
product construction, `cat` by the concatenation automaton (`Exercise722Cat.lean`). -/
def toNFA : (e : SExpr) → NFA Bool (autState e)
  | .sigma => sigmaDFA.toNFA
  | .single σ => (singleDFA σ).toNFA
  | .cap a b => NFAinter (toNFA a) (toNFA b)
  | .cat a b => (catEps (toNFA a) (toNFA b)).toNFA

/-- **The automaton recognises exactly the language it should.** -/
theorem toNFA_accepts : (e : SExpr) → (toNFA e).accepts = denote e
  | .sigma => by
      change sigmaDFA.toNFA.accepts = denote .sigma
      rw [dfaToNFA_accepts sigmaDFA, sigmaDFA_accepts, denote_sigma]
  | .single σ => by
      change (singleDFA σ).toNFA.accepts = denote (.single σ)
      rw [dfaToNFA_accepts (singleDFA σ)]
      exact singleDFA_accepts_denote σ
  | .cap a b => by
      ext x
      change x ∈ (NFAinter (toNFA a) (toNFA b)).accepts ↔ _
      rw [NFAinter_mem_accepts_iff, toNFA_accepts a, toNFA_accepts b, denote_cap]
      exact (Set.mem_inter_iff x (denote a) (denote b)).symm
  | .cat a b => by
      change (catEps (toNFA a) (toNFA b)).toNFA.accepts = denote (.cat a b)
      rw [εNFA.toNFA_correct, catEps_accepts, toNFA_accepts a, toNFA_accepts b, denote_cat]

/-! ## Emptiness reduces to reachability of an accept state

Since the state space is a `Fintype`, this reduces Definition 7.1's relation (ii) — consistency,
which by positivity of `Ssys` (`Exercise722.lean`) is exactly `∩`-non-emptiness — to a **finite**
reachability question. The two clean routes to a primitive-recursive decider from here are flagged in
the module docstring of `Exercise722DFA.lean`. -/

variable {σ : Type}

/-- A nonempty accepted language ⟺ some accept state is reachable by reading some word. -/
theorem nfa_accepts_nonempty_iff (M : NFA Bool σ) :
    M.accepts.Nonempty ↔ ∃ s ∈ M.accept, ∃ x, s ∈ M.eval x := by
  constructor
  · rintro ⟨x, S, hS, hSe⟩; exact ⟨S, hS, x, hSe⟩
  · rintro ⟨S, hS, x, hSe⟩; exact ⟨x, S, hS, hSe⟩

/-- **Definition 7.1 relation (ii) as a reachability problem.** `denote e` is empty iff no accept
state of its `Fintype` automaton is reachable. The right-hand side ranges over the finite state set
`autState e`; the only non-finite-looking quantifier (`∀ x`) is what a reachability search eliminates. -/
theorem denote_eq_empty_iff (e : SExpr) :
    denote e = ∅ ↔ ∀ s ∈ (toNFA e).accept, ∀ x, s ∉ (toNFA e).eval x := by
  rw [Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h s hs x hse
    exact h x (by rw [← toNFA_accepts e]; exact ⟨s, hs, hse⟩)
  · intro h x hx
    rw [← toNFA_accepts e] at hx
    obtain ⟨s, hs, hse⟩ := hx
    exact h s hs x hse

/-! ## Short-word search (Session C4)

If an `n`-state NFA accepts some word, it accepts one of length `< n` (pigeonhole on a concrete
accepting path). This is tighter than mathlib's `NFA.pumping_lemma`, which bounds via `card (Set σ)`.
-/

section ShortWord

variable {σ : Type} [Fintype σ] {M : NFA Bool σ}

/-- State after reading the first `n` symbols along a concrete path (`n ≤ x.length`). -/
def pathStateAtAux {s t : σ} {x : List Bool} : M.Path s t x → ∀ n, n ≤ x.length → σ
  | .nil s, 0, _ => s
  | .nil _, n + 1, hn => (Nat.not_succ_le_zero n hn).elim
  | .cons _ s' _ _ _ _ p', 0, _ => s'
  | .cons _ _ _ _ _ _ p', n + 1, hn =>
      pathStateAtAux p' n (Nat.le_of_succ_le_succ hn)

def pathStateAt {s t : σ} {x : List Bool} (p : M.Path s t x) (n : ℕ) (hn : n ≤ x.length) : σ :=
  pathStateAtAux p n hn

@[simp] theorem pathStateAt_zero {s t : σ} {x : List Bool} (p : M.Path s t x) :
    pathStateAt p 0 (Nat.zero_le _) = s := by
  cases x with
  | nil =>
    cases p <;> simp [pathStateAt, pathStateAtAux]
  | cons a xs =>
    cases p with
    | cons _ s' _ _ _ _ _ => simp [pathStateAt, pathStateAtAux]

theorem pathStateAt_succ {sMid s' u : σ} {a : Bool} {xs : List Bool}
    (hstep : sMid ∈ M.step s' a) (p' : M.Path sMid u xs) (n : ℕ) (hn : n ≤ xs.length) :
    pathStateAt (.cons sMid s' u a xs hstep p') (n + 1) (Nat.succ_le_succ hn) =
      pathStateAt p' n hn := by
  simp [pathStateAt, pathStateAtAux]

theorem pathStateAt_last {s t : σ} {x : List Bool} (p : M.Path s t x) :
    pathStateAt p x.length (Nat.le_refl _) = t := by
  induction p with
  | nil s => simp [pathStateAt, pathStateAtAux]
  | cons sMid s' u a xs hstep p' ih =>
    simp [pathStateAt, pathStateAtAux, List.length_cons]
    exact ih

/-- Append two paths meeting at the middle state. -/
def pathAppend {s u t : σ} {a b : List Bool} (p : M.Path s u a) (p' : M.Path u t b) :
    M.Path s t (a ++ b) :=
  match p with
  | .nil _ => p'
  | .cons sMid s' _ a' xs hstep p'' =>
      .cons sMid s' _ a' (xs ++ b) hstep (pathAppend p'' p')

structure PathSplit {s t : σ} {x : List Bool} (p : M.Path s t x) (n : ℕ) (hn : n ≤ x.length) where
  u : σ
  hp : M.Path s u (x.take n)
  ht : M.Path u t (x.drop n)
  hu : pathStateAt p n hn = u

noncomputable def pathAppend_take_drop {s t : σ} {x : List Bool} (p : M.Path s t x) (n : ℕ)
    (hn : n ≤ x.length) : PathSplit p n hn := by
  revert n hn
  induction p with
  | nil s =>
    intro n hn
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    subst hn0
    exact { u := s, hp := .nil s, ht := .nil s, hu := by rfl }
  | cons sMid s' u a xs hstep p' ih =>
    intro n hn
    cases n with
    | zero =>
      exact { u := s', hp := .nil s', ht := .cons sMid s' u a xs hstep p', hu := by rfl }
    | succ n' =>
      have hn' : n' ≤ xs.length := by simpa [List.length_cons] using hn
      have split := ih n' hn'
      exact {
        u := split.u
        hp := .cons sMid s' split.u a (xs.take n') hstep split.hp
        ht := split.ht
        hu := by rw [pathStateAt_succ hstep p' n' hn']; exact split.hu
      }

theorem mem_accepts_of_path {s t : σ} {x : List Bool} (hs : s ∈ M.start) (ht : t ∈ M.accept)
    (p : M.Path s t x) : x ∈ M.accepts := by
  rw [NFA.accepts_iff_exists_path]
  exact ⟨s, hs, t, ht, ⟨p⟩⟩

theorem accepts_skip_loop {s t : σ} {x : List Bool} {i j : ℕ}
    (hi : i ≤ x.length) (hj : j ≤ x.length) (_hij : i < j)
    (hs : s ∈ M.start) (ht : t ∈ M.accept) (hp : M.Path s t x)
    (heq : pathStateAt hp i hi = pathStateAt hp j hj) :
    x.take i ++ x.drop j ∈ M.accepts := by
  let splitI := pathAppend_take_drop hp i hi
  let splitJ := pathAppend_take_drop hp j hj
  have hqq' : splitI.u = splitJ.u := by rw [← splitI.hu, heq, splitJ.hu]
  exact mem_accepts_of_path hs ht (pathAppend splitI.hp (hqq' ▸ splitJ.ht))

theorem accepts_card_zero (hσ : Fintype.card σ = 0) {w : List Bool} (hw : w ∈ M.accepts) : False := by
  rw [NFA.mem_accepts] at hw
  obtain ⟨t, ht, hte⟩ := hw
  rw [NFA.mem_evalFrom_iff_exists (S := M.start) (s := t) (x := w)] at hte
  obtain ⟨s, hs, _⟩ := hte
  exact (Fintype.card_eq_zero_iff.mp hσ).elim s

theorem accepts_shorten_step {x : List Bool} (hx : x ∈ M.accepts)
    (hlen : Fintype.card σ ≤ x.length) :
    ∃ y, y ∈ M.accepts ∧ y.length < x.length := by
  rw [NFA.accepts_iff_exists_path] at hx
  obtain ⟨s, hs, t, ht, ⟨hp⟩⟩ := hx
  obtain ⟨i, j, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (f := fun k : Fin (x.length + 1) => pathStateAt hp k.val (Nat.le_of_lt_succ k.isLt))
      (by rw [Fintype.card_fin]; exact Nat.lt_succ_iff.mpr hlen)
  have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hval with hij | hij
  · refine ⟨x.take i.val ++ x.drop j.val, ?_, ?_⟩
    · exact accepts_skip_loop (by omega) (by omega) hij hs ht hp heq
    · have hi' : i.val ≤ x.length := by omega
      have hj' : j.val ≤ x.length := by omega
      have : j.val - i.val > 0 := Nat.sub_pos_of_lt hij
      simp [List.length_append, List.length_take, List.length_drop, hi', hj']
      omega
  · refine ⟨x.take j.val ++ x.drop i.val, ?_, ?_⟩
    · exact accepts_skip_loop (by omega) (by omega) hij hs ht hp heq.symm
    · have hi' : i.val ≤ x.length := by omega
      have hj' : j.val ≤ x.length := by omega
      have : i.val - j.val > 0 := Nat.sub_pos_of_lt hij
      simp [List.length_append, List.length_take, List.length_drop, hj', hi']
      omega

theorem exists_accepted_word_short (h : M.accepts.Nonempty) :
    ∃ w, w.length < Fintype.card σ ∧ w ∈ M.accepts := by
  by_cases hσ : Fintype.card σ = 0
  · obtain ⟨x, hx⟩ := h
    exact (accepts_card_zero hσ hx).elim
  · obtain ⟨x, hx⟩ := h
    exact Nat.strongRecOn x.length
      (motive := fun n =>
        ∀ w, w.length = n → w ∈ M.accepts → ∃ u, u.length < Fintype.card σ ∧ u ∈ M.accepts)
      (fun n ih w hwlen hw => by
        by_cases hlt : n < Fintype.card σ
        · exact ⟨w, hwlen ▸ hlt, hw⟩
        · have hge : Fintype.card σ ≤ n := Nat.not_lt.mp hlt
          obtain ⟨y, hy, hylt⟩ := accepts_shorten_step hw (hwlen.symm ▸ hge)
          exact ih y.length (Nat.lt_of_lt_of_eq hylt hwlen) y rfl hy)
      x rfl hx

theorem nfa_accepts_nonempty_iff_short :
    M.accepts.Nonempty ↔ ∃ w, w ∈ wordsUpTo (Fintype.card σ) ∧ w ∈ M.accepts := by
  constructor
  · intro h
    obtain ⟨w, hwlt, hw⟩ := exists_accepted_word_short h
    refine ⟨w, ?_, hw⟩
    rw [mem_wordsUpTo]
    omega
  · intro ⟨w, _, hw⟩
    exact ⟨w, hw⟩

theorem autStateCard_eq_card (e : SExpr) : autStateCard e = Fintype.card (autState e) := by
  induction e with
  | sigma => simp [autStateCard, autState]
  | single σ =>
    simp only [autStateCard, autState]
    have h1 : Fintype.card (Option (Fin (σ.length + 1))) =
        Fintype.card (Fin (σ.length + 1)) + 1 :=
      Fintype.card_option (α := Fin (σ.length + 1))
    have h2 : Fintype.card (Fin (σ.length + 1)) = σ.length + 1 :=
      Fintype.card_fin (σ.length + 1)
    calc autStateCard (.single σ)
        = σ.length + 2 := rfl
      _ = (σ.length + 1) + 1 := rfl
      _ = Fintype.card (Fin (σ.length + 1)) + 1 := (congrArg (fun n => n + 1) h2).symm
      _ = Fintype.card (Option (Fin (σ.length + 1))) := h1.symm
  | cap a b ih_a ih_b =>
    simp [autStateCard, autState, ih_a, ih_b]
    exact (Fintype.card_prod (autState a) (autState b)).symm
  | cat a b ih_a ih_b =>
    simp [autStateCard, autState, ih_a, ih_b]
    exact (Fintype.card_sum (α := autState a) (β := autState b)).symm

theorem denote_nonempty_iff_short (e : SExpr) :
    (denote e).Nonempty ↔ ∃ w ∈ wordsUpTo (autStateCard e), matchesB e w = true := by
  have hc : autStateCard e = Fintype.card (autState e) := autStateCard_eq_card e
  constructor
  · intro hne
    rw [← toNFA_accepts e] at hne
    obtain ⟨w, hwlt, hw⟩ := exists_accepted_word_short hne
    refine ⟨w, ?_, ?_⟩
    · rw [mem_wordsUpTo, hc]; omega
    · rw [matchesB_iff, ← toNFA_accepts e]; exact hw
  · intro ⟨w, hwmem, hmatch⟩
    rw [mem_wordsUpTo, hc] at hwmem
    exact ⟨w, (matchesB_iff e w).mp hmatch⟩

end ShortWord

/-! ## Emptiness decider (Session C5) -/

/-- Search `wordsUpTo (autStateCard e)` for a word accepted by `matchesB e`. -/
def decideNonemptyB (e : SExpr) : Bool :=
  anyMatchesB e (wordsUpTo (autStateCard e))

/-- Decidable emptiness of `denote e` via bounded word search. -/
def decideEmptyB (e : SExpr) : Bool := !decideNonemptyB e

@[simp] theorem decideNonemptyB_iff (e : SExpr) :
    decideNonemptyB e = true ↔ (denote e).Nonempty := by
  simp [decideNonemptyB, anyMatchesB, List.any_eq_true, denote_nonempty_iff_short]

@[simp] theorem decideEmptyB_iff (e : SExpr) :
    decideEmptyB e = true ↔ denote e = ∅ := by
  rw [decideEmptyB, Bool.not_eq_true_eq_eq_false, ← Bool.eq_false_eq_not_eq_true,
    decideNonemptyB_iff, Set.not_nonempty_iff_eq_empty]

instance decidableEmptyDenote (e : SExpr) : Decidable (denote e = ∅) :=
  if h : decideEmptyB e then .isTrue (decideEmptyB_iff e |>.mp h)
  else .isFalse fun he => h (decideEmptyB_iff e |>.mpr he)

#eval decideEmptyB (.cap (.single [false]) (.single [true])) -- should be `true` (disjoint singletons)

/-! ## Consistency decider (Session C6) — Definition 7.1 relation (ii)

For `X, Y ∈ S`, Scott's consistency `∃ Z ∈ S, Z ⊆ X ∩ Y` is equivalent to `(X ∩ Y).Nonempty`
by positivity (`Ssys_isPositive`). On syntax, this is non-emptiness of `denote (cap a b)`. -/

/-- Decides relation (ii) on a pair of expressions: `true` iff `denote a ∩ denote b` is non-empty. -/
def consistentB (a b : SExpr) : Bool := !decideEmptyB (.cap a b)

@[simp] theorem consistentB_iff (a b : SExpr) :
    consistentB a b = true ↔ (denote (.cap a b)).Nonempty := by
  have h : consistentB a b = decideNonemptyB (.cap a b) := by
    simp [consistentB, decideEmptyB, decideNonemptyB]
  rw [h, decideNonemptyB_iff]

@[simp] theorem capNonempty_iff_consistent (a b : SExpr) :
    (denote a ∩ denote b).Nonempty ↔ consistentB a b = true := by
  rw [← denote_cap, consistentB_iff]

/-- **Definition 7.1 (ii) for encoded neighbourhoods:** when `denote a`, `denote b ∈ S`,
`consistentB` agrees with membership of the intersection in `S`. -/
theorem consistentB_iff_Ssys (a b : SExpr) (ha : InS (denote a)) (hb : InS (denote b)) :
    consistentB a b = true ↔ InS (denote a ∩ denote b) := by
  rw [← denote_cap, consistentB_iff]
  exact Iff.symm (Ssys_isPositive (Ssys_mem.mpr ha) (Ssys_mem.mpr hb))

/-! ## Relation (i) `interEq` — what `decideEmptyB` / `consistentB` do *not* decide (Session C7a)

**Definition 7.1 (i)** on an encoded presentation is the ternary relation
`Xₙ ∩ Xₘ = Xₖ`. On `SExpr` syntax this is *exactly regular-language equivalence*
(`interEq_iff` in `Exercise722Regular.lean`):

  `denote a ∩ denote b = denote k  ↔  denote (cap a b) = denote k`.

Relation (ii) consistency is now mechanised (`consistentB` / `decideEmptyB` on `cap a b`).
Relation (i) is **strictly harder**: it asks whether two *different* syntactic caps denote the
*same* language, not merely whether their intersection is empty.

**Why emptiness alone is insufficient.** The fragment is not closed under complement or set-difference
(`L₁ ⊆ L₂ ↔ L₁ \ L₂ = ∅` needs `\`). The concrete obstruction is `sigma_ne_containsZero`:
`denote .sigma ≠ denote containsZero` (witness `[true] ∈ Σ` but `[true] ∉ Σ·{0}·Σ`), yet no
fragment-emptiness query on `cap`/`cat`/`single`/`sigma` alone exposes this inequality — detecting
`Σ \ "contains 0"` needs the complement language `{1}*`, which is **not expressible** in the
fragment. Hence `decideEmptyB` and `consistentB` cannot decide (i).

**What a full (i) decider would need (Session C7b, DEFER).** Language equivalence
`denote e₁ = denote e₂` reduces to emptiness of the symmetric difference, hence to deciding
`(e₁ ∩ e₂ᶜ)` and `(e₂ ∩ e₁ᶜ)` — i.e. **complement** (`complDFA` exists) wired into a uniform
`toDFA` / product construction, or an alternative such as Myhill–Nerode bisimulation on the
`autState` types. Until C7b lands, `Ssys_partially_effectively_given` will carry (ii) only. -/

end Exercise722

end Scott1980.Neighborhood

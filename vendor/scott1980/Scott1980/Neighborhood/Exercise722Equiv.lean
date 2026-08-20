/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Exercise722Decide

/-!
# Exercise 7.22k — language equivalence via a `Finset`-valued subset construction (Session C7b)

`toNFA e : NFA Bool (autState e)` is genuinely nondeterministic once `.cat` is involved (the
concatenation automaton's ε-closure fans a single state out to several live states), so deciding
`denote e₁ = denote e₂` cannot be reduced to a simple bounded search over `matchesB` alone:
"`e₂` rejects `w`" is a *universal* statement over `e₂`'s nondeterministic paths, and universal
statements over NFA paths don't pump the way existential ones do (`exists_accepted_word_short`).

The fix is a **choice-free `Finset`-valued subset-construction simulation** of `toNFA e`: track the
*entire* set of live NFA states as a `Finset (autState e)` (decidable, since `autState e` already
carries `Fintype`/`DecidableEq`, `Exercise722Decide.lean`), evolving **deterministically**. Once
both `e₁`'s and `e₂`'s live-state-sets are tracked simultaneously (as one `Finset`-pair state), the
question "is there a word `e₁` accepts but `e₂` rejects" becomes an ordinary NFA-emptiness question
on a *deterministic* (singleton-step) NFA, to which `exists_accepted_word_short` applies directly.
-/

namespace Scott1980.Neighborhood

namespace Exercise722

open scoped Computability
open Sum Set

/-! ## `Finset`-valued simulation of `toNFA e`

`acceptFin`/`startFin`/`stepFinSingle` mirror `toNFA`'s own recursive cases exactly, computing the
same sets as `Finset`s (decidable data) instead of `Set`s. Correctness (`coe_acceptFin` etc.) shows
each agrees with `toNFA e`'s actual `Set`-valued semantics. -/

/-- The accept states of `toNFA e`, as a `Finset`. -/
def acceptFin : (e : SExpr) → Finset (autState e)
  | .sigma => Finset.univ
  | .single σ => {(some ⟨σ.length, Nat.lt_succ_self _⟩ : SingleState σ)}
  | .cap a b => (acceptFin a) ×ˢ (acceptFin b)
  | .cat a b => (acceptFin b).image (inr : autState b → autState a ⊕ autState b)

theorem coe_acceptFin : ∀ e : SExpr, (↑(acceptFin e) : Set (autState e)) = (toNFA e).accept
  | .sigma => by
      show (↑(Finset.univ : Finset Unit) : Set Unit) = sigmaDFA.toNFA.accept
      show (↑(Finset.univ : Finset Unit) : Set Unit) = Set.univ
      ext x; cases x; simp
  | .single σ => by
      change (↑({(some ⟨σ.length, Nat.lt_succ_self _⟩ : SingleState σ)} : Finset _) : Set _)
        = (singleDFA σ).toNFA.accept
      simp [DFA.toNFA, singleDFA]
  | .cap a b => by
      change (↑((acceptFin a) ×ˢ (acceptFin b)) : Set (autState a × autState b))
        = (NFAinter (toNFA a) (toNFA b)).accept
      rw [Finset.coe_product, coe_acceptFin a, coe_acceptFin b]
      rfl
  | .cat a b => by
      show (↑((acceptFin b).image (inr : autState b → autState a ⊕ autState b)) :
        Set (autState a ⊕ autState b)) = (catEps (toNFA a) (toNFA b)).toNFA.accept
      show (↑((acceptFin b).image (inr : autState b → autState a ⊕ autState b)) :
        Set (autState a ⊕ autState b)) = inr '' (toNFA b).accept
      rw [Finset.coe_image, coe_acceptFin b]

/-- The start states of `toNFA e`, as a `Finset`. The `.cat` case handles the one-hop
ε-closure directly (`catEps`'s only ε-edges go from an `M₁`-accept state to `M₂`-start states,
`catEps_mem_εClosure_iff`): if some start state of `a` is already accepting, `b`'s start states
are also immediately live. -/
def startFin : (e : SExpr) → Finset (autState e)
  | .sigma => Finset.univ
  | .single σ => {(some ⟨0, Nat.succ_pos _⟩ : SingleState σ)}
  | .cap a b => (startFin a) ×ˢ (startFin b)
  | .cat a b =>
      if ((startFin a) ∩ (acceptFin a)).Nonempty
      then (startFin a).image (inl : autState a → autState a ⊕ autState b) ∪
        (startFin b).image (inr : autState b → autState a ⊕ autState b)
      else (startFin a).image (inl : autState a → autState a ⊕ autState b)

theorem coe_startFin : ∀ e : SExpr, (↑(startFin e) : Set (autState e)) = (toNFA e).start
  | .sigma => by
      show (↑(Finset.univ : Finset Unit) : Set Unit) = sigmaDFA.toNFA.start
      show (↑(Finset.univ : Finset Unit) : Set Unit) = {sigmaDFA.start}
      ext x; cases x; simp
  | .single σ => by
      show (↑({(some ⟨0, Nat.succ_pos _⟩ : SingleState σ)} : Finset (SingleState σ)) : Set _)
        = (singleDFA σ).toNFA.start
      simp [DFA.toNFA, singleDFA]
  | .cap a b => by
      show (↑((startFin a) ×ˢ (startFin b)) : Set (autState a × autState b))
        = (NFAinter (toNFA a) (toNFA b)).start
      rw [Finset.coe_product, coe_startFin a, coe_startFin b]
      rfl
  | .cat a b => by
      show (↑(if ((startFin a) ∩ (acceptFin a)).Nonempty
          then (startFin a).image (inl : autState a → autState a ⊕ autState b) ∪
            (startFin b).image (inr : autState b → autState a ⊕ autState b)
          else (startFin a).image (inl : autState a → autState a ⊕ autState b)) :
          Set (autState a ⊕ autState b)) = (catEps (toNFA a) (toNFA b)).toNFA.start
      show _ = (catEps (toNFA a) (toNFA b)).εClosure (catEps (toNFA a) (toNFA b)).start
      rw [catEps_start]
      by_cases hne : ((startFin a) ∩ (acceptFin a)).Nonempty
      · rw [if_pos hne]
        ext x
        rw [catEps_mem_εClosure_iff, ← coe_startFin a, ← coe_acceptFin a, ← coe_startFin b]
        simp only [Finset.coe_union, Finset.coe_image, mem_union, mem_image, Finset.mem_coe]
        constructor
        · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
          · exact Or.inl ⟨q, hq, rfl⟩
          · refine Or.inr ⟨?_, q, hq, rfl⟩
            obtain ⟨q0, hq0⟩ := hne
            rw [Finset.mem_inter] at hq0
            exact ⟨q0, hq0.2, q0, hq0.1, rfl⟩
        · rintro (⟨q, hq, rfl⟩ | ⟨_, q, hq, rfl⟩)
          · exact Or.inl ⟨q, hq, rfl⟩
          · exact Or.inr ⟨q, hq, rfl⟩
      · rw [if_neg hne]
        ext x
        rw [catEps_mem_εClosure_iff, ← coe_startFin a, ← coe_acceptFin a, ← coe_startFin b]
        simp only [Finset.coe_image, mem_image, Finset.mem_coe]
        constructor
        · rintro ⟨q, hq, rfl⟩; exact Or.inl ⟨q, hq, rfl⟩
        · rintro (⟨q, hq, rfl⟩ | ⟨⟨q, hq1, q', hq2, heq⟩, _⟩)
          · exact ⟨q, hq, rfl⟩
          · cases heq
            exact absurd ⟨q, Finset.mem_inter.mpr ⟨hq2, hq1⟩⟩ hne

/-- The step function of `toNFA e` from a single state, as a `Finset`. The `.cat` case's `inl`
branch mirrors `startFin`'s epsilon-closure handling exactly (one hop, on reaching an `a`-accept
state after the step). -/
def stepFinSingle : (e : SExpr) → autState e → Bool → Finset (autState e)
  | .sigma => fun _ _ => Finset.univ
  | .single σ => fun s c => {(singleDFA σ).step s c}
  | .cap a b => fun s c => (stepFinSingle a s.1 c) ×ˢ (stepFinSingle b s.2 c)
  | .cat a b => fun s c =>
      match s with
      | inl s' =>
          if ((stepFinSingle a s' c) ∩ (acceptFin a)).Nonempty
          then (stepFinSingle a s' c).image (inl : autState a → autState a ⊕ autState b) ∪
            (startFin b).image (inr : autState b → autState a ⊕ autState b)
          else (stepFinSingle a s' c).image (inl : autState a → autState a ⊕ autState b)
      | inr s' => (stepFinSingle b s' c).image (inr : autState b → autState a ⊕ autState b)

theorem coe_stepFinSingle : ∀ (e : SExpr) (s : autState e) (c : Bool),
    (↑(stepFinSingle e s c) : Set (autState e)) = (toNFA e).step s c
  | .sigma, s, c => by
      show (↑(Finset.univ : Finset Unit) : Set Unit) = sigmaDFA.toNFA.step s c
      show (↑(Finset.univ : Finset Unit) : Set Unit) = {sigmaDFA.step s c}
      ext x; cases x; simp
  | .single σ, s, c => by
      show (↑({(singleDFA σ).step s c} : Finset (SingleState σ)) : Set _)
        = (singleDFA σ).toNFA.step s c
      simp [DFA.toNFA]
  | .cap a b, (s1, s2), c => by
      show (↑((stepFinSingle a s1 c) ×ˢ (stepFinSingle b s2 c)) : Set (autState a × autState b))
        = (NFAinter (toNFA a) (toNFA b)).step (s1, s2) c
      rw [Finset.coe_product, coe_stepFinSingle a s1 c, coe_stepFinSingle b s2 c]
      rfl
  | .cat a b, inl s, c => by
      show (↑(if ((stepFinSingle a s c) ∩ (acceptFin a)).Nonempty
          then (stepFinSingle a s c).image (inl : autState a → autState a ⊕ autState b) ∪
            (startFin b).image (inr : autState b → autState a ⊕ autState b)
          else (stepFinSingle a s c).image (inl : autState a → autState a ⊕ autState b)) :
          Set (autState a ⊕ autState b)) = (catEps (toNFA a) (toNFA b)).toNFA.step (inl s) c
      show _ = (catEps (toNFA a) (toNFA b)).εClosure
        ((catEps (toNFA a) (toNFA b)).step (inl s) (some c))
      rw [catEps_step_inl_some]
      by_cases hne : ((stepFinSingle a s c) ∩ (acceptFin a)).Nonempty
      · rw [if_pos hne]
        ext x
        rw [catEps_mem_εClosure_iff, ← coe_stepFinSingle a s c, ← coe_acceptFin a,
          ← coe_startFin b]
        simp only [Finset.coe_union, Finset.coe_image, mem_union, mem_image, Finset.mem_coe]
        constructor
        · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
          · exact Or.inl ⟨q, hq, rfl⟩
          · refine Or.inr ⟨?_, q, hq, rfl⟩
            obtain ⟨q0, hq0⟩ := hne
            rw [Finset.mem_inter] at hq0
            exact ⟨q0, hq0.2, q0, hq0.1, rfl⟩
        · rintro (⟨q, hq, rfl⟩ | ⟨_, q, hq, rfl⟩)
          · exact Or.inl ⟨q, hq, rfl⟩
          · exact Or.inr ⟨q, hq, rfl⟩
      · rw [if_neg hne]
        ext x
        rw [catEps_mem_εClosure_iff, ← coe_stepFinSingle a s c, ← coe_acceptFin a,
          ← coe_startFin b]
        simp only [Finset.coe_image, mem_image, Finset.mem_coe]
        constructor
        · rintro ⟨q, hq, rfl⟩; exact Or.inl ⟨q, hq, rfl⟩
        · rintro (⟨q, hq, rfl⟩ | ⟨⟨q, hq1, q', hq2, heq⟩, _⟩)
          · exact ⟨q, hq, rfl⟩
          · cases heq
            exact absurd ⟨q, Finset.mem_inter.mpr ⟨hq2, hq1⟩⟩ hne
  | .cat a b, inr s, c => by
      show (↑((stepFinSingle b s c).image (inr : autState b → autState a ⊕ autState b)) :
        Set (autState a ⊕ autState b)) = (catEps (toNFA a) (toNFA b)).toNFA.step (inr s) c
      show _ = (catEps (toNFA a) (toNFA b)).εClosure
        ((catEps (toNFA a) (toNFA b)).step (inr s) (some c))
      rw [catEps_step_inr_some]
      ext x
      rw [catEps_mem_εClosure_iff, ← coe_stepFinSingle b s c]
      simp only [Finset.coe_image, mem_image, Finset.mem_coe]
      constructor
      · rintro ⟨q, hq, rfl⟩; exact Or.inl ⟨q, hq, rfl⟩
      · rintro (⟨q, hq, rfl⟩ | ⟨⟨q, _, hqmem⟩, _⟩)
        · exact ⟨q, hq, rfl⟩
        · exact absurd hqmem (by simp)

/-- The `Finset`-lifted step (mirrors `NFA.stepSet`). -/
def stepFin (e : SExpr) (S : Finset (autState e)) (c : Bool) : Finset (autState e) :=
  S.biUnion (fun s => stepFinSingle e s c)

theorem coe_stepFin (e : SExpr) (S : Finset (autState e)) (c : Bool) :
    (↑(stepFin e S c) : Set (autState e)) = (toNFA e).stepSet ↑S c := by
  ext x
  rw [Finset.mem_coe]
  unfold stepFin
  rw [Finset.mem_biUnion, NFA.mem_stepSet]
  constructor
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [← coe_stepFinSingle e s c]; exact Finset.mem_coe.mpr hx⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [← coe_stepFinSingle e s c] at hx; exact Finset.mem_coe.mp hx⟩

/-- The live-state `Finset` after reading `w` (mirrors `NFA.eval`, folding `stepFin` left to
right from `startFin`). -/
def evalFin (e : SExpr) (w : List Bool) : Finset (autState e) :=
  w.foldl (stepFin e) (startFin e)

theorem coe_foldl_stepFin (e : SExpr) (w : List Bool) (S : Finset (autState e)) :
    (↑(w.foldl (stepFin e) S) : Set (autState e)) = (toNFA e).evalFrom ↑S w := by
  induction w generalizing S with
  | nil => rfl
  | cons c w ih =>
    show (↑(w.foldl (stepFin e) (stepFin e S c)) : Set (autState e)) = _
    rw [ih (stepFin e S c), NFA.evalFrom_cons, coe_stepFin e S c]

theorem coe_evalFin (e : SExpr) (w : List Bool) :
    (↑(evalFin e w) : Set (autState e)) = (toNFA e).eval w := by
  show (↑(w.foldl (stepFin e) (startFin e)) : Set (autState e))
    = (toNFA e).evalFrom (toNFA e).start w
  rw [coe_foldl_stepFin e w (startFin e), coe_startFin e]

/-- **`denote e` via the `Finset` simulation.** `w` matches `e` iff some live state after reading
`w` is accepting — a decidable `Finset` intersection test. -/
theorem denote_iff_evalFin (e : SExpr) (w : List Bool) :
    w ∈ denote e ↔ (evalFin e w ∩ acceptFin e).Nonempty := by
  rw [← toNFA_accepts e]
  constructor
  · rintro ⟨s, hs, hse⟩
    refine ⟨s, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · rw [← Finset.mem_coe, coe_evalFin]; exact hse
    · rw [← Finset.mem_coe, coe_acceptFin]; exact hs
  · rintro ⟨s, hs⟩
    rw [Finset.mem_inter] at hs
    obtain ⟨hs1, hs2⟩ := hs
    refine ⟨s, ?_, ?_⟩
    · rw [← Finset.mem_coe, coe_acceptFin] at hs2; exact hs2
    · rw [← Finset.mem_coe, coe_evalFin] at hs1; exact hs1

/-! ## The "difference" automaton: `e₁` is live and `e₂` is dead

Tracks `e₁`'s and `e₂`'s live-state `Finset`s *simultaneously* as one deterministic (singleton
step/start) NFA, so `exists_accepted_word_short` — genuinely generic over any `Fintype` NFA state
space — bounds the length of a shortest word witnessing `denote e₁ ⊄ denote e₂`. -/

/-- Tracks `(evalFin e₁ w, evalFin e₂ w)` deterministically; accepts `w` iff `e₁` is live-accepting
and `e₂` is not — i.e. `w ∈ denote e₁ \ denote e₂`. -/
def diffNFA (e1 e2 : SExpr) : NFA Bool (Finset (autState e1) × Finset (autState e2)) where
  step S c := {(stepFin e1 S.1 c, stepFin e2 S.2 c)}
  start := {(startFin e1, startFin e2)}
  accept := {S | (S.1 ∩ acceptFin e1).Nonempty ∧ S.2 ∩ acceptFin e2 = ∅}

theorem diffNFA_evalFrom (e1 e2 : SExpr) (w : List Bool)
    (S1 : Finset (autState e1)) (S2 : Finset (autState e2)) :
    (diffNFA e1 e2).evalFrom {(S1, S2)} w =
      {(w.foldl (stepFin e1) S1, w.foldl (stepFin e2) S2)} := by
  induction w generalizing S1 S2 with
  | nil => rfl
  | cons c w ih =>
    show (diffNFA e1 e2).evalFrom ((diffNFA e1 e2).stepSet {(S1, S2)} c) w = _
    rw [NFA.stepSet_singleton]
    show (diffNFA e1 e2).evalFrom {(stepFin e1 S1 c, stepFin e2 S2 c)} w = _
    exact ih (stepFin e1 S1 c) (stepFin e2 S2 c)

theorem diffNFA_eval (e1 e2 : SExpr) (w : List Bool) :
    (diffNFA e1 e2).eval w = {(evalFin e1 w, evalFin e2 w)} := by
  show (diffNFA e1 e2).evalFrom (diffNFA e1 e2).start w = _
  show (diffNFA e1 e2).evalFrom {(startFin e1, startFin e2)} w = _
  exact diffNFA_evalFrom e1 e2 w (startFin e1) (startFin e2)

/-- **`diffNFA` accepts exactly `denote e₁ \ denote e₂`.** -/
theorem diffNFA_mem_accepts_iff (e1 e2 : SExpr) (w : List Bool) :
    w ∈ (diffNFA e1 e2).accepts ↔ w ∈ denote e1 ∧ w ∉ denote e2 := by
  constructor
  · rintro ⟨s, hs, hse⟩
    rw [diffNFA_eval, Set.mem_singleton_iff] at hse
    subst hse
    obtain ⟨hacc1, hacc2⟩ := hs
    refine ⟨(denote_iff_evalFin e1 w).mpr hacc1, fun hmem => ?_⟩
    rw [denote_iff_evalFin] at hmem
    rw [hacc2] at hmem
    exact Finset.not_nonempty_empty hmem
  · rintro ⟨h1, h2⟩
    refine ⟨(evalFin e1 w, evalFin e2 w), ⟨(denote_iff_evalFin e1 w).mp h1, ?_⟩, ?_⟩
    · show evalFin e2 w ∩ acceptFin e2 = ∅
      by_contra hcontra
      exact h2 ((denote_iff_evalFin e2 w).mpr (Finset.nonempty_iff_ne_empty.mpr hcontra))
    · rw [diffNFA_eval]; rfl

/-- **The shortest witness of `denote e₁ ⊄ denote e₂`, if any, is short.** Generic
`exists_accepted_word_short` applied to `diffNFA`. -/
theorem exists_diff_word_short {e1 e2 : SExpr} (h : ¬ denote e1 ⊆ denote e2) :
    ∃ w, w.length < Fintype.card (Finset (autState e1) × Finset (autState e2)) ∧
      w ∈ denote e1 ∧ w ∉ denote e2 := by
  rw [Set.not_subset] at h
  have hne : (diffNFA e1 e2).accepts.Nonempty := by
    obtain ⟨x, hx1, hx2⟩ := h
    exact ⟨x, (diffNFA_mem_accepts_iff e1 e2 x).mpr ⟨hx1, hx2⟩⟩
  obtain ⟨w, hlen, hmem⟩ := exists_accepted_word_short hne
  exact ⟨w, hlen, (diffNFA_mem_accepts_iff e1 e2 w).mp hmem⟩

/-! ## Bounded-word-search deciders for `⊆` and `=` -/

/-- `denote e₁ ⊆ denote e₂`, decided by a bounded search: if no word up to the `diffNFA` state
bound witnesses `e₁ \ e₂`, none exists at all (`exists_diff_word_short`). -/
def subsetB (e1 e2 : SExpr) : Bool :=
  (wordsUpTo (Fintype.card (Finset (autState e1) × Finset (autState e2)))).all
    (fun w => !matchesB e1 w || matchesB e2 w)

theorem subsetB_iff (e1 e2 : SExpr) : subsetB e1 e2 = true ↔ denote e1 ⊆ denote e2 := by
  unfold subsetB
  rw [List.all_eq_true]
  constructor
  · intro h
    by_contra hsub
    obtain ⟨w, hlen, hw1, hw2⟩ := exists_diff_word_short hsub
    have hwmem : w ∈ wordsUpTo (Fintype.card (Finset (autState e1) × Finset (autState e2))) :=
      (mem_wordsUpTo _).mpr (le_of_lt hlen)
    have hor := h w hwmem
    have he1 : matchesB e1 w = true := (matchesB_iff e1 w).mpr hw1
    rw [he1] at hor
    simp only [Bool.not_true, Bool.false_or] at hor
    exact hw2 ((matchesB_iff e2 w).mp hor)
  · intro hsub w _
    by_cases hw1 : w ∈ denote e1
    · have he2 : matchesB e2 w = true := (matchesB_iff e2 w).mpr (hsub hw1)
      simp [he2]
    · have he1 : matchesB e1 w = false := by
        rw [Bool.eq_false_iff]
        intro hc
        exact hw1 ((matchesB_iff e1 w).mp hc)
      simp [he1]

/-- **Exercise 7.22k.** Relation (i) on `SExpr` syntax — language equivalence — decided by
`subsetB` in both directions. -/
def interEqB (e1 e2 : SExpr) : Bool := subsetB e1 e2 && subsetB e2 e1

theorem interEqB_iff (e1 e2 : SExpr) : interEqB e1 e2 = true ↔ denote e1 = denote e2 := by
  unfold interEqB
  rw [Bool.and_eq_true, subsetB_iff, subsetB_iff, ← Set.Subset.antisymm_iff]

end Exercise722

end Scott1980.Neighborhood

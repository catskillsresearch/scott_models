/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Exercise722Regular

/-!
# Exercise 7.22 — bounded word enumeration for emptiness search

Lists every `List Bool` of length at most `n` (`wordsUpTo n`), and provides `anyMatchesB` to test
whether any word in a finite list is accepted by the `matchesB` matcher. The characterisation
`mem_wordsUpTo` is the length bound used later for pumping-based short-word search (Session C4).
-/

namespace Scott1980.Neighborhood

namespace Exercise722

/-- Every word over `{false,true}` of length at most `n`, listed without duplicates. -/
def wordsUpTo : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
    (wordsUpTo n) ++ (wordsUpTo n).flatMap fun w => [[false] ++ w, [true] ++ w]

theorem mem_wordsUpTo (n : ℕ) {w : List Bool} : w ∈ wordsUpTo n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero =>
    simp only [wordsUpTo, List.mem_singleton]
    constructor
    · rintro (rfl : w = [])
      simp
    · intro h
      exact (List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero h)).symm ▸ rfl
  | succ n ih =>
    simp only [wordsUpTo]
    rw [List.mem_append, List.mem_flatMap]
    constructor
    · intro h
      rcases h with h | ⟨w', hw', hmem⟩
      · exact Nat.le_succ_of_le (ih.mp h)
      · rw [List.mem_cons, List.mem_singleton] at hmem
        rcases hmem with rfl | rfl
        · simpa [List.length_cons] using Nat.succ_le_succ (ih.mp hw')
        · simpa [List.length_cons] using Nat.succ_le_succ (ih.mp hw')
    · intro hlen
      by_cases hw : w.length ≤ n
      · exact Or.inl (ih.mpr hw)
      · match w with
        | [] => exfalso; exact hw (by simp)
        | hd :: tl =>
          have htl_len : tl.length ≤ n := by
            have : tl.length + 1 ≤ n + 1 := by simpa [List.length_cons] using hlen
            exact Nat.le_of_succ_le_succ this
          have htl : tl ∈ wordsUpTo n := ih.mpr htl_len
          refine Or.inr ⟨tl, htl, ?_⟩
          rw [List.mem_cons, List.mem_singleton]
          cases hd with
          | false => exact Or.inl rfl
          | true => exact Or.inr rfl

/-- True iff some word in `ws` is accepted by `matchesB e`. -/
def anyMatchesB (e : SExpr) (ws : List (List Bool)) : Bool := ws.any (matchesB e)

#eval anyMatchesB .sigma (wordsUpTo 0) -- should be `true` (the empty word lies in Σ)

end Exercise722

end Scott1980.Neighborhood

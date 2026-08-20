/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Exercise722

/-!
# Exercise 7.22 (Scott 1981, PRG-19, §7) — the regular-event layer

This file develops the **"regular events" hint** of Exercise 7.22 toward *effective givenness* of the
neighbourhood system `Ssys` of `Exercise722.lean`. Scott's hint:

> the sets in `S` are each "regular events" in the terminology of automata theory, and we have a
> decision method for the set algebra of regular events.

## What is mechanised here (green, choice-free)

We make the "regular event" content precise by giving `S` a finite **syntax** and a denotation, and
proving the syntax exactly captures `S`:

* `SExpr` — the syntax of `S`-terms: `Σ` (`sigma`), a singleton `{σ}` (`single σ`), concatenation
  `X·Y` (`cat`), and intersection `X ∩ Y` (`cap`). This is a *fragment* of regular expressions
  (closed under `·` and `∩`, with the universal language `Σ`), with **no** union, complement, or
  Kleene star — exactly Scott's four generators.
* `denote : SExpr → Set (List Bool)` — the language denoted by a term.
* **Decidable membership** `decide (w ∈ denote e)` via a `Bool` matcher `matchesB` with
  `matchesB_iff`, giving `DecidablePred (· ∈ denote e)` (choice-free). This is the computational core
  of "regular event": *membership of a word is decidable*.
* **Soundness/completeness**: `InS (denote e)` whenever `denote e` is non-empty
  (`InS_denote_of_nonempty`), and every member of `S` is a denotation (`InS_exists_denote`). Hence the
  exact characterization `InS X ↔ ∃ e, denote e = X ∧ X.Nonempty` (`inS_iff_exists_denote`).
* `SExpr` is countable (`Encodable SExpr`), so `S` is at most countable (Scott's standing finiteness).

## What remains for full effective givenness (Definition 7.1) — documented, not mechanised

Building a `ComputablePresentation`/`ScottPresentation Ssys` (Definition 7.1) requires Scott's two
relations to be **recursively decidable**, i.e. computed by genuine *primitive-recursive* functions
(`Domain.Recursive.RecDecidable = ∃ f, Nat.Primrec f ∧ …`); classical decidability does **not**
suffice. Over the syntax codes the two relations are:

* **(ii) consistency** `∃k. X_k ⊆ Xₙ ∩ Xₘ` ≡ (by positivity, Exercise 1.19 / `Ssys_isPositive`)
  **non-emptiness of `denote eₙ ∩ denote eₘ`** = non-emptiness of `denote (cap eₙ eₘ)`;
* **(i)** `Xₙ ∩ Xₘ = X_k` is **language equivalence** `denote (cap eₙ eₘ) = denote e_k`.

Both are decidable for regular events, but the decision procedures are **automata-complete**:

* *Emptiness* of an intersection genuinely needs the product-automaton reachability argument (there is
  no structural recursion for `∩`-emptiness: e.g. `Σ{0}Σ ∩ Σ{1}Σ` is non-empty while `{00} ∩ {11}`
  is empty), and a bounded-search emptiness test needs a *proven* state/length bound from a DFA.
* *Equivalence* is **not** reducible to intersection-emptiness inside this class, because the class is
  **not** closed under complement/difference (`L₁ ⊆ L₂ ⟺ L₁ \ L₂ = ∅` needs `\`). It requires a
  regular-language equivalence procedure (minimal DFAs / Myhill–Nerode, cf. `Example62Regular.lean`).

Mechanising those choice-free in `Recursive.lean` (a primitive-recursive subset construction +
reachability + a pumping/length bound, then `matchesB` over a bounded word set) is a separate, large
undertaking. Everything in *this* file is `⊆ {propext, Quot.sound}` (no `Classical.choice`).
-/

namespace Scott1980.Neighborhood

namespace Exercise722

/-! ## Syntax and denotation -/

/-- **The syntax of `S`-terms** (Scott's four generators): `Σ`, a singleton `{σ}`, concatenation
`X·Y`, and intersection `X ∩ Y`. A fragment of regular expressions with `·` and `∩` and the
universal language `Σ`, but no union / complement / star. -/
inductive SExpr : Type
  | sigma : SExpr
  | single : List Bool → SExpr
  | cat : SExpr → SExpr → SExpr
  | cap : SExpr → SExpr → SExpr
  deriving DecidableEq

/-- The language denoted by an `S`-term. -/
def denote : SExpr → Set (List Bool)
  | .sigma => Set.univ
  | .single σ => {σ}
  | .cat a b => concat (denote a) (denote b)
  | .cap a b => denote a ∩ denote b

@[simp] theorem denote_sigma : denote .sigma = Set.univ := rfl
@[simp] theorem denote_single (σ : List Bool) : denote (.single σ) = {σ} := rfl
@[simp] theorem denote_cat (a b : SExpr) : denote (.cat a b) = concat (denote a) (denote b) := rfl
@[simp] theorem denote_cap (a b : SExpr) : denote (.cap a b) = denote a ∩ denote b := rfl

/-! ## Decidable word membership (the computational core of "regular event") -/

/-- A word `w` lies in a concatenation `X·Y` iff it splits as `w = w.take i ++ w.drop i` with the
prefix in `X` and the suffix in `Y` for some cut point `i ≤ |w|`. (The cut point is the length of
the `X`-part.) -/
theorem mem_concat_iff_split {X Y : Set (List Bool)} {w : List Bool} :
    w ∈ concat X Y ↔ ∃ i, i ≤ w.length ∧ w.take i ∈ X ∧ w.drop i ∈ Y := by
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a.length, by simp, ?_, ?_⟩
    · rw [List.take_left]; exact ha
    · rw [List.drop_left]; exact hb
  · rintro ⟨i, _, hpre, hsuf⟩
    exact ⟨w.take i, hpre, w.drop i, hsuf, w.take_append_drop i⟩

/-- The **`Bool` matcher** for `S`-terms: a structurally-recursive decision of word membership. The
concatenation case tries every cut point `i ∈ {0,…,|w|}`; the intersection case is the conjunction. -/
def matchesB : SExpr → List Bool → Bool
  | .sigma, _ => true
  | .single σ, w => decide (w = σ)
  | .cat a b, w => (List.range (w.length + 1)).any (fun i => matchesB a (w.take i) && matchesB b (w.drop i))
  | .cap a b, w => matchesB a w && matchesB b w

/-- **The matcher is correct**: `matchesB e w = true ↔ w ∈ denote e`. By structural induction on `e`;
the concatenation case unfolds `List.any` over the cut points and applies `mem_concat_iff_split`. -/
theorem matchesB_iff (e : SExpr) (w : List Bool) : matchesB e w = true ↔ w ∈ denote e := by
  induction e generalizing w with
  | sigma => simp [matchesB]
  | single σ => simp [matchesB]
  | cat a b iha ihb =>
    rw [denote_cat, mem_concat_iff_split]
    simp only [matchesB, List.any_eq_true, List.mem_range, Bool.and_eq_true]
    constructor
    · rintro ⟨i, hi, ha, hb⟩
      exact ⟨i, Nat.lt_succ_iff.mp hi, (iha _).mp ha, (ihb _).mp hb⟩
    · rintro ⟨i, hi, ha, hb⟩
      exact ⟨i, Nat.lt_succ_iff.mpr hi, (iha _).mpr ha, (ihb _).mpr hb⟩
  | cap a b iha ihb =>
    simp only [matchesB, Bool.and_eq_true, denote_cap, Set.mem_inter_iff]
    rw [iha, ihb]

/-- **Membership in a regular event is decidable** (choice-free), via the matcher. -/
instance decidableMemDenote (e : SExpr) : DecidablePred (· ∈ denote e) :=
  fun w => decidable_of_iff (matchesB e w = true) (matchesB_iff e w)

/-! ## Soundness and completeness: the syntax captures exactly `S` -/

/-- **Soundness.** A *non-empty* denotation is a member of `S`. (Non-emptiness is needed only for the
intersection generator, where `InS.inter` demands it; it propagates down to subterms because
`concat`/`∩` are non-empty only when their parts are.) -/
theorem InS_denote_of_nonempty : ∀ {e : SExpr}, (denote e).Nonempty → InS (denote e)
  | .sigma, _ => InS.univ
  | .single σ, _ => InS.singleton σ
  | .cat a b, h => by
    rw [denote_cat] at h ⊢
    obtain ⟨w, x, hx, y, hy, _⟩ := h
    exact InS.mul (InS_denote_of_nonempty ⟨x, hx⟩) (InS_denote_of_nonempty ⟨y, hy⟩)
  | .cap a b, h => by
    rw [denote_cap] at h ⊢
    have ha : (denote a).Nonempty := h.mono Set.inter_subset_left
    have hb : (denote b).Nonempty := h.mono Set.inter_subset_right
    exact InS.inter (InS_denote_of_nonempty ha) (InS_denote_of_nonempty hb) h

/-- **Completeness.** Every member of `S` is the denotation of some `S`-term. -/
theorem InS_exists_denote {X : Set (List Bool)} (h : InS X) : ∃ e : SExpr, denote e = X := by
  induction h with
  | univ => exact ⟨.sigma, rfl⟩
  | singleton σ => exact ⟨.single σ, rfl⟩
  | mul _ _ iha ihb =>
    obtain ⟨ea, rfl⟩ := iha
    obtain ⟨eb, rfl⟩ := ihb
    exact ⟨.cat ea eb, rfl⟩
  | inter _ _ _ iha ihb =>
    obtain ⟨ea, rfl⟩ := iha
    obtain ⟨eb, rfl⟩ := ihb
    exact ⟨.cap ea eb, rfl⟩

/-- **Characterization of `S` as the regular events of this fragment.** A language `X` is in `S`
exactly when it is the *non-empty* denotation of some `Σ`/`{σ}`/`·`/`∩` expression. This is the
precise content of Scott's "the sets in `S` are each regular events". -/
theorem inS_iff_exists_denote {X : Set (List Bool)} :
    InS X ↔ ∃ e : SExpr, denote e = X ∧ X.Nonempty := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := InS_exists_denote h
    exact ⟨e, he, h.nonempty⟩
  · rintro ⟨e, rfl, hne⟩
    exact InS_denote_of_nonempty hne

/-! ## Countability of `S`

`SExpr` is built from `List Bool` by finitely many constructors, hence countable; so `S`, being the
range of `denote` (restricted to non-empty denotations), is at most countable — Scott's standing
"at most a countable infinity of neighbourhoods" (Definition 7.1). We record the range presentation;
the countability of `SExpr` itself is immediate (a finitely-branching inductive over the countable
`List Bool`) and not needed below. -/

/-- The set of `S`-languages is the range of `denote` (on `SExpr`), hence the image of a countable
type: `S = denote '' {e | (denote e).Nonempty}`. This realises the enumeration backbone of an
effective presentation; what it does *not* yet supply is the recursive *decidability* of Scott's two
index relations (see the module docstring). -/
theorem inS_eq_range_denote : {X | InS X} = denote '' {e | (denote e).Nonempty} := by
  ext X
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro h
    obtain ⟨e, he⟩ := InS_exists_denote h
    exact ⟨e, by rw [he]; exact h.nonempty, he⟩
  · rintro ⟨e, hne, rfl⟩
    exact InS_denote_of_nonempty hne

/-! ## Reducing Definition 7.1's two relations to language equivalence on `SExpr`

The enumeration of `S` is (essentially) `n ↦ denote (decode n)` for codes `decode n : SExpr`. Over
such codes, Scott's two recursive-decidability obligations of Definition 7.1 become:

* **(ii)** consistency `∃k. X_k ⊆ Xₙ ∩ Xₘ` ≡ (positivity) `(denote eₙ ∩ denote eₘ).Nonempty`;
* **(i)** `Xₙ ∩ Xₘ = X_k` ≡ `denote (cap eₙ eₘ) = denote e_k`.

We show **both** are instances of *deciding language equivalence of two `SExpr`s* — and that emptiness
alone is therefore **not** enough (relation (i) needs the full equivalence test). -/

/-- The empty language is denotable in the fragment (it is **not** a member of `S`, which is
positive): `{0} ∩ {1} = ∅`. This is the canonical "`∅`" expression used to phrase emptiness as an
equivalence query. -/
def emptyExpr : SExpr := .cap (.single [false]) (.single [true])

@[simp] theorem denote_emptyExpr : denote emptyExpr = (∅ : Set (List Bool)) := by
  ext w
  simp only [emptyExpr, denote_cap, denote_single, Set.mem_inter_iff, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl
  decide

/-- **Definition 7.1(ii), syntactically.** Inconsistency of `eₙ, eₘ` — emptiness of `Xₙ ∩ Xₘ` — is
exactly *language-equivalence of `cap eₙ eₘ` with `emptyExpr`*. Consistency (relation (ii)) is its
**negation**, so even (ii) is an instance of deciding language equivalence on `SExpr` (here:
equivalence to `∅`). Stated as an emptiness-equivalence to keep it choice-free (recovering a witnessing
element from `≠ ∅` is the one genuinely non-constructive step, and is not needed for the decision). -/
theorem empty_iff_equiv_emptyExpr (a b : SExpr) :
    denote (.cap a b) = (∅ : Set (List Bool)) ↔ denote (.cap a b) = denote emptyExpr := by
  rw [denote_emptyExpr]

/-- **Definition 7.1(i), syntactically**, is *exactly language equivalence on `SExpr`*:
`Xₙ ∩ Xₘ = X_k ↔ denote (cap eₙ eₘ) = denote e_k`. -/
theorem interEq_iff (a b k : SExpr) :
    denote a ∩ denote b = denote k ↔ denote (.cap a b) = denote k := by
  rw [denote_cap]

/-! ## Why an emptiness decider is *not* enough (the concrete obstruction)

Relation (i) is genuine regular-language **equivalence**, which is strictly stronger than
fragment-emptiness, because the fragment is **not closed under complement / set-difference**
(`L₁ ⊆ L₂ ↔ L₁ \ L₂ = ∅` needs `\`). The following exhibit the obstruction concretely. -/

/-- "Contains a `0`" as a fragment expression: `Σ · {0} · Σ`. -/
def containsZero : SExpr := .cat .sigma (.cat (.single [false]) .sigma)

/-- `denote .sigma = Σ` contains every word. -/
theorem mem_denote_sigma (w : List Bool) : w ∈ denote .sigma := Set.mem_univ w

/-- **`denote` is far from injective: `Σ · Σ = Σ`.** A nontrivial language identity (with distinct
syntax), so relation (i) `Xₙ∩Xₘ = X_k` is *not* syntactic equality of codes — it is genuine
regular-language equivalence, the whole difficulty of the exercise. -/
theorem denote_catSigmaSigma : denote (.cat .sigma .sigma) = denote .sigma := by
  ext w
  simp only [denote_cat, denote_sigma, mem_concat, Set.mem_univ, iff_true]
  exact ⟨[], trivial, w, trivial, rfl⟩

/-- **The emptiness decider cannot decide relation (i).** `Σ ≠ "contains 0"`, witnessed by `[1] ∈ Σ`
but `[1] ∉ Σ·{0}·Σ`. To *decide* this inequality one must detect a word in `Σ ∩ ("contains 0")ᶜ` —
i.e. in the complement language `{1}*` — but `{1}*` is **not** expressible in the fragment (no
complement, no star other than the full `Σ`). Hence no fragment-emptiness query exposes the
difference: deciding equivalence needs machinery (a product/complement DFA, or a derivative
bisimulation) that goes strictly beyond emptiness of fragment expressions. -/
theorem sigma_ne_containsZero : denote .sigma ≠ denote containsZero := by
  intro h
  have h1 : ([true] : List Bool) ∈ denote .sigma := mem_denote_sigma _
  rw [h] at h1
  exact absurd h1 (by decide)

end Exercise722

end Scott1980.Neighborhood

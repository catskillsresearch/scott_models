/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Proposition810b

/-!
# Exercise 8.26 (Scott 1981, PRG-19) — untyped `λ`-calculus in `𝒰`, and translating typed calculus back

> **Exercise 8.26.** Discuss in more detail the "pay-off" for `𝒰`, namely the translation of
> "untyped" `λ`-calculus into `𝒰` as shown by the equations at the end of the lecture after the
> proof of 8.9. In particular show how the whole of the **typed** `λ`-calculus can be retranslated
> back into `𝒰` with the aid of projections. (Hint: whenever you want to write `f : D_a → D_b`,
> write instead `f = b∘f∘a`, where `a, b` are finitary projections. Whenever you want to form a
> `λ`-abstraction `λx^{D_a}.σ`, where `σ` is of type `D_b`, instead form `λx. b(σ'[a(x)/x])`, where
> `σ'` is the further translation of `σ` into untyped `λ`-calculus. Be sure to show that this
> result "has the right type" in the sense defined above.)

This is a genuinely **expository** exercise ("discuss in more detail"), unlike 8.17–8.25's crisp
existence/uniqueness claims — Scott is asking the reader to *unpack and verify* a translation
scheme he has already sketched, not to discover new mathematics. The formalization below extracts
the three pieces of that scheme that are actually checkable claims, and proves each:

1. **The end-of-lecture equations** (self-hosted application/abstraction): `𝒰` becomes its own
   model of untyped `λ`-calculus once we fix `i_→ : (𝒰→𝒰) → 𝒰`, `j_→ : 𝒰 → (𝒰→𝒰)` (Definition
   8.9). Application of one `𝒰`-element to another is `u(x) := j_→(u)(x)` (`Uapply`); abstraction
   of an "outside" function `f : 𝒰 → 𝒰` is `λx.f ≅ i_→(f)` (`Ulam`). The content beyond bare
   notation is **faithfulness**: the self-hosted calculus computes the same thing as the outside
   one, `Uapply (Ulam f) x = f(x)` (`Uapply_Ulam`) — i.e. `β`-reduction inside `𝒰`'s internal
   `λ`-calculus is sound, using exactly `jArrow_comp_iArrow : j_→∘i_→ = I`.
2. **The hint's translation recipe for `λ`-abstraction, and "has the right type."** Generalizing
   away from `𝒰` to *any* neighbourhood system `E` and *any* retractions `a, b : E → E` (in
   particular finitary projections, Definition 8.3): given the further-translated body
   `body : E → E` (Scott's `σ'`), the recipe `λx. b(σ'[a(x)/x])` is `translateAbs a b body :=
   b∘body∘a`, and it **always** satisfies the defining sandwich equation `f = b∘f∘a`
   (`translateAbs_sandwich`) — this is exactly "has the right type," and needs nothing about
   `body`'s own well-typedness, only idempotence of `a`, `b`. A one-line corollary
   (`translateApp_hasType`) checks the matching claim for **application**: if `f = b∘f∘a` and `x`
   already has type `D_a` (`a(x) = x`), then `f(x)` already has type `D_b` (`b(f(x)) = f(x)`).
3. **The correspondence `f = b∘f∘a` really does capture `D_a → D_b`.** This is *not* new content —
   it is exactly Proposition 8.10(b)'s `arrowComb_elementIso`/`finitaryProjection_arrowComb`
   (`Proposition810b.lean`), which for finitary projections `a, b` produces
   `(D_a → D_b).Element ≃o {f : 𝒰.Element ∣ (a→b)(f) = f}` — i.e. every `g : D_a → D_b` *is*
   (uniquely) some `f` with `f = b∘f∘a`, and conversely. We do not reprove this; we cite it as
   answering the hint's opening sentence directly.

**What is deliberately out of scope.** A full formal syntax + typing judgment for the typed
`λ`-calculus (variables, application, abstraction, a base-type context, substitution, and a
structural induction assembling 1–3 above into "every typed term translates to an untyped one of
the right type") is not built. The reason is the same one already used to defer the *effectiveness*
clauses of Theorem 8.6/Exercise 8.23/Exercise 8.25: this project's convention is to formalize the
mathematical content precisely (here: the two checkable claims 1–2, plus citing 3) while leaving
genuinely open-ended "build a term language and induct over it" scaffolding as prose discussion,
since the payoff — the induction is a routine unfolding of 1–3 at each syntax constructor, with
`+`/`×` cases following `→`'s pattern exactly (`sumComb`/`prodComb`'s own `IsRetraction`/sandwich
facts are already in `Proposition810.lean`/`Proposition810b.lean`, so `translateAbs_sandwich`
applies to *any* of the three combinators, not just `→`) — is not itself a new mathematical
question. Scott's own hint stops at exactly this level of detail ("whenever you want to..."),
i.e. a *recipe*, not a compiler; we formalize the recipe and its correctness.

Axiom audit: `Uapply_Ulam` mentions `𝒰`, hence inherits `𝒰`'s own `Classical.choice` footprint
(⊆ `{propext, Classical.choice, Quot.sound}`, not new). `translateAbs_sandwich`/
`translateApp_hasType` are fully general (no mention of `𝒰`) and **choice-free**
(`⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap

/-! ## Part 1 (of the exercise write-up): the end-of-lecture equations, self-hosted in `𝒰` -/

/-- **Self-application inside `𝒰`** (the end-of-lecture equation `u(x) := j_→(u)(x)`): decode
`u : 𝒰` into an actual function `𝒰 → 𝒰` via `j_→` (`jArrow`, Definition 8.9), then apply it to
`x`. -/
noncomputable def Uapply (u x : U.Element) : U.Element :=
  (evalMap U U).toElementMap (pair (jArrow.toElementMap u) x)

/-- **Self-abstraction inside `𝒰`** (the end-of-lecture equation `λx.τ ≅ i_→(λx.τ)`): given the
"outside" function `f : 𝒰 → 𝒰` (`τ`'s ordinary denotation as an approximable map), encode it into
`𝒰` via `i_→` (`iArrow`, Definition 8.9). -/
noncomputable def Ulam (f : ApproximableMap U U) : U.Element :=
  iArrow.toElementMap (toFilter f)

/-- **Faithfulness (`β`-soundness) of the self-hosted encoding.** Applying the self-hosted
abstraction of `f` recovers `f` itself: `Uapply (Ulam f) x = f(x)`. The internal `λ`-calculus of
`𝒰` literally computes the same thing as the "outside" one it is modelling — this is the actual
content of "the pay-off," beyond bare notation. Uses only `jArrow_comp_iArrow : j_→∘i_→ = I` (the
retraction half of Definition 8.9's fixed pair) and `evalMap`'s defining equation
(`evalMap_apply`). -/
theorem Uapply_Ulam (f : ApproximableMap U U) (x : U.Element) :
    Uapply (Ulam f) x = f.toElementMap x := by
  have hround : toApproxMap (toFilter f) = f := by
    have he := (funSpaceEquiv U U).apply_symm_apply f
    rwa [funSpaceEquiv_apply, funSpaceEquiv_symm_apply] at he
  unfold Uapply Ulam
  have h1 : jArrow.toElementMap (iArrow.toElementMap (toFilter f))
      = (jArrow.comp iArrow).toElementMap (toFilter f) :=
    (toElementMap_comp jArrow iArrow (toFilter f)).symm
  rw [h1, jArrow_comp_iArrow, toElementMap_idMap, evalMap_apply, hround]

/-! ## Part 2 (of the exercise write-up): the abstraction recipe, and "has the right type" -/

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

/-- **Scott's translation recipe for a `λ`-abstraction**, `λx^{D_a}.σ ↦ λx. b(σ'[a(x)/x])`: given
the further-translated body `body : E → E` (Scott's `σ'`, the untyped realization of `σ` as a
function of `x`), form the projection-sandwiched abstraction `b∘body∘a`. Stated for an arbitrary
neighbourhood system `E` and arbitrary `a, b : E → E` — specializes to Scott's `𝒰`/finitary
projections, but needs nothing special about `E`. -/
def translateAbs (a b body : ApproximableMap E E) : ApproximableMap E E :=
  b.comp (body.comp a)

/-- **"Be sure to show that this result has the right type."** `translateAbs a b body` always
satisfies the defining sandwich equation `f = b∘f∘a` of Scott's `D_a → D_b` translation scheme
(the "sense defined above" — see `Proposition810b.elementIsoOfProjectionPair`/
`arrowComb_elementIso`), **regardless of `body`** — the *only* thing this uses is idempotence of
`a` and `b` (true of every retraction, Definition 8.1, in particular every finitary projection,
Definition 8.3). Pure associativity + idempotence, mirroring the book's own one-line proof
("`(a×b)∘(a×b) = ... = a×b`," `Proposition 8.10`'s proof) transplanted to the abstraction case. -/
theorem translateAbs_sandwich {a b body : ApproximableMap E E}
    (ha : IsRetraction a) (hb : IsRetraction b) :
    b.comp ((translateAbs a b body).comp a) = translateAbs a b body := by
  show b.comp ((b.comp (body.comp a)).comp a) = b.comp (body.comp a)
  rw [comp_assoc b (body.comp a) a, comp_assoc body a a, ha, ← comp_assoc b b (body.comp a), hb]

/-- **The matching claim for application**: if `f` already "has the right type" (`f = b∘f∘a`) and
`x` already "has type `D_a`" (`a(x) = x`), then `f(x)` already "has type `D_b`" (`b(f(x)) = f(x)`).
Together with `translateAbs_sandwich`, this is the type-soundness invariant that both the
`λ`-abstraction and application clauses of the typed-to-untyped translation preserve. -/
theorem translateApp_hasType {a b f : ApproximableMap E E} (hsandwich : b.comp (f.comp a) = f)
    {x : E.Element} (hx : a.toElementMap x = x) :
    b.toElementMap (f.toElementMap x) = f.toElementMap x := by
  conv_rhs => rw [← hsandwich, toElementMap_comp, toElementMap_comp, hx]

/-- **A sanity check: the identity abstraction translates to the identity, and the recipe applied
to `body = id` (the trivial "translation" of a bare variable `σ = x`) already has the right type
for free** — `translateAbs a b (idMap E) = b∘a`, matching that a bare variable of type `D_a` fed
through the `a`-then-`b` sandwich needs no further work. Included as a `0`-th case of the
induction discussed above (the base case: variables). -/
theorem translateAbs_idMap {a b : ApproximableMap E E} : translateAbs a b (idMap E) = b.comp a := by
  unfold translateAbs
  rw [idMap_comp]

end Scott1980.Neighborhood

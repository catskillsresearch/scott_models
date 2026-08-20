/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Exercise717Part2
import Scott1980.Neighborhood.Definition89
import Scott1980.Neighborhood.Proposition810
import Scott1980.Neighborhood.Proposition810b
import Scott1980.Neighborhood.Lemma615

/-!
# Exercise 8.21 (Scott 1981, PRG-19)

> **Exercise 8.21.** Using the fixed-point construction, show that there is a continuous and
> computable operator `λa. a§`, such that if `a` is a finitary projection of `U`, then
> `D_{a§} ≅ (D_a)§`.

Here `D§` is Scott's tree algebra of Example 6.1 (`Dsharp`, already fully formalized with computable
combinators `in`/`pair`/`proj₀`/`proj₁` in `Example61.lean`/`Combinators77.lean`/`Exercise717.lean`,
and the universal catamorphism `g : D§ → E` of Exercise 7.17 Part 2, `gMap`).

## What is formalized here

**The construction of `a§`, and the properties that are tractable without new "uniqueness of
catamorphism" infrastructure.**

* **`U§ ⊴ U`** (`dsharpU_trianglelefteq_U`): since `dsharpPresentation` (Prop 7.7) makes `U§`
  effectively given, `theorem_8_8_b_strong` (Theorem 8.8(b)) hands it a *computable* projection
  pair `iSharp : U§ → U`, `jSharp : U → U§` into `U`, exactly as Definition 8.9 fixes `i₊/j₊`,
  `i_×/j_×`, `i_→/j_→` for `U+U`, `U×U`, `U→U`.

* **The operator itself** (`aSharp`). Scott's recipe for `a§`, read off Example 6.1's own
  defining equations `out(x§) = x`, `pair(x,y)`, is: recurse `a` on the `D`-summand and leave the
  pairing structure alone, i.e. `a§` should satisfy `a§(x§) = (a x)§` and
  `a§(⟨y,z⟩) = ⟨a§(y), a§(z)⟩`. But these are *exactly* the two defining equations
  (`gMap_in`/`gMap_pair`) of Exercise 7.17 Part 2's catamorphism `gMap u v` specialized to
  `u := in ∘ a` and `v := pair` (the tree algebra's own pairing) — so the "fixed-point
  construction" the exercise asks for is already on hand as `gMap`, and no new recursion needs to
  be built:
  ```
  aSharpInner a := gMap (inSharpMap.comp a) pairSharpMap hU : U§ → U§
  aSharp a      := iSharp ∘ aSharpInner a ∘ jSharp : U → U
  ```
  This mirrors Definition 8.9's own conjugation-through-a-projection-pair pattern for `+`, `×`, `→`.

* **Computable** (`aSharp_isComputable`): `gMap_isComputable` (the heart of Exercise 7.17 Part 2)
  applies directly, since `in`/`pair` are computable (`inSharp_isComputable`/
  `pairSharp_isComputable`) and composition of computable maps is computable
  (`comp_isComputable`); chaining through `iSharp`/`jSharp`'s own computability
  (`theorem_8_8_b_strong`) gives computability of `aSharp a` whenever `a` is computable.

* **`a ≤ I ⟹ a§ ≤ I`** (`aSharp_le_idMap_of_le`, half of "`a` a projection ⟹ `a§` a projection",
  Proposition 8.10's proof recipe `a ⊑ I ⟹ a+b ⊑ I+I = i∘j ⊑ I` transcribed to `§`): the new general
  tool is **`gMap_mono`** — monotonicity of the catamorphism in `u`, `v` — proved by a direct
  structural induction on the `GRel` derivation exactly parallel to `gRel_mono` (Exercise 7.17
  Part 2), using that `≤` on `ApproximableMap` unfolds to pointwise relation inclusion
  (`ApproximableMap.le_iff`). Combined with the new characterization
  **`gMap_inSharp_pairSharp_eq_idMap`** (`gMap in pair = I_{D§}`, proved by two structural
  inductions — on `GRel` and on `MemS` — mirroring `gMap_in`/`gMap_pair`'s own style) and
  `comp_mono_gen`, monotonicity of `a§` in `a` gives `a ≤ I → a§ ≤ I` cleanly.

* **Exercise 8.21(b) — the other half of "`a` a projection ⟹ `a§` a projection", idempotence**
  (`a = a∘a ⟹ a§ = a§∘a§`). Unlike `×`/`→`/`+` in `Proposition810.lean`, there is no elementwise
  closed form for `gMap`'s action on a *general* element of `D§` (its elements are potentially
  *infinite* trees, unlike `pair`/`fst`/`snd` or `curry`/`eval` which have one-step defining
  equations valid everywhere), so this needs a genuine **uniqueness-of-catamorphism** lemma
  (`gMap_eq_of_satisfies`: `k` strict, satisfying the two `g`-equations for `(u, v) ⟹ k = gMap u v`)
  — precisely Scott's own remark in the Example 6.1 discussion ("`g` is unique because the values
  on finite elements are fixed"), proved by induction on the `MemS`-derivation of the input
  neighbourhood (bridging `k`'s abstract relation to the assumed element-level equations via
  `rel_iff_mem_principal` and two small "principal of constructor = constructor of principals"
  identities, `inSharp_principal`/`pairSharp_principal`). Idempotence of `aSharpInner a`
  (`gMap_selfComp_eq_of_isRetraction`, proved in the same general form as the uniqueness lemma) then
  transports through the `U§ ⊴ U` projection pair exactly as `Proposition810.lean`'s
  `isRetraction_prodComb`/`isRetraction_arrowComb` do (`isRetraction_aSharp`), completing
  `isProjection_aSharp`: `a` a projection ⟹ `a§` a projection, in full.

* **Exercise 8.21(c) — the headline isomorphism `D_{a§} ≅ (D_a)§`.** The key realization is that
  `D ↦ D§` is *functorial* on morphisms, not just on domains: precomposing `inSharpMap` with any
  `f : D' → D` and recursing via `gMap` (`dsharpMap`) extends `f` to `D'§ → D§`, satisfying the
  functor laws `id§ = id` (`dsharpMap_id`, literally `gMap_inSharp_pairSharp_eq_idMap`) and
  `(f' ∘ f)§ = f'§ ∘ f§` (`dsharpMap_comp`, via `gMap_eq_of_satisfies` — verbatim
  `gMap_selfComp_eq_of_isRetraction`'s proof, but *without* needing a retraction hypothesis, since
  composing two different maps needs no idempotence). Transporting `iSharp`/`jSharp` through
  `dsharpMap`'s action on the injection/projection pair `(fixedNbhd_subsystem a).inj/.proj` of
  `D_a := fixedNbhd a ◁ U` (Proposition 6.12) produces a *new* projection pair
  `I : (D_a)§ → U`, `J : U → (D_a)§` (`ISharpComb`/`JSharpComb`) with `J ∘ I = I_{(D_a)§}`
  (`dsharpMap`'s functor laws applied to `j_a ∘ i_a = I_{D_a}`) and, when `a` is a finitary
  projection, `I ∘ J = a§` (the functor laws applied to `i_a ∘ j_a = a`, Theorem 8.6's
  `inj_comp_proj_eq_self`, noting `aSharpInner a` is literally `dsharpMap` applied to
  `i_a ∘ j_a = a`). `elementIsoOfProjectionPair` (`Proposition810b.lean`) then hands us
  `(D_a)§.Element ≅ Fix(a§)` directly — Scott's headline isomorphism, in the same "domain of a
  projection = its `toElementMap`-fixed-point set" convention `Proposition810b.lean` already uses
  for `D_{a+b} ≅ D_a+D_b` etc. This also re-proves `IsFinitary (a§)`, so combined with 8.21(a)/(b)'s
  `isProjection_aSharp`, `a` a *finitary* projection of `U` `⟹` `a§` a finitary projection, in full.

Axiom footprint: everything here mentions `U`, so (as with `Definition89.lean`/`Proposition810.lean`)
it inherits `U`'s own `Classical.choice` footprint — `⊆ {propext, Classical.choice, Quot.sound}`,
confirmed not new; `dsharpMap`/`dsharpMap_id` (mentioning no `U`) are fully choice-free
`⊆ {propext, Quot.sound}`, while `dsharpMap_comp` inherits `Classical.choice` from
`gMap_eq_of_satisfies` (matching 8.21(b)'s own baseline, nothing new).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-! ## `gMap` is monotone in `u`, `v` -/

/-- **`GRel` is monotone in `u`, `v`.** Direct structural induction on the `GRel` derivation,
parallel to `gRel_mono`'s induction on shape. -/
theorem GRel.mono_uv (_hD : ∀ X, D.mem X → X.Nonempty)
    {u u' : ApproximableMap D E} {v v' : ApproximableMap (prod E E) E}
    (hu : u ≤ u') (hv : v ≤ v') :
    ∀ {W Z}, GRel u v W Z → GRel u' v' W Z := by
  intro W Z h
  induction h with
  | gamma hZ => exact GRel.gamma hZ
  | leaf hrel => exact GRel.leaf (hu _ _ hrel)
  | node hP hQ hvrel ihP ihQ => exact GRel.node ihP ihQ (hv _ _ hvrel)

/-- **`gMap` is monotone in `u`, `v`.** -/
theorem gMap_mono (hD : ∀ X, D.mem X → X.Nonempty)
    {u u' : ApproximableMap D E} {v v' : ApproximableMap (prod E E) E}
    (hu : u ≤ u') (hv : v ≤ v') : gMap u v hD ≤ gMap u' v' hD := by
  rw [ApproximableMap.le_iff]
  intro W Z h
  exact GRel.mono_uv hD hu hv h

/-! ## `gMap in pair = I_{D§}` -/

variable {hD : ∀ X, D.mem X → X.Nonempty}

/-- Forward direction: every `GRel (inSharpMap) (pairSharpMap)`-related pair is an `idMap`-related
pair (`MemS`-membership on both sides plus `⊆`). -/
theorem grel_inSharp_pairSharp_imp_idMap_rel :
    ∀ {W Z}, GRel (inSharpMap hD) (pairSharpMap hD) W Z → MemS D W ∧ MemS D Z ∧ W ⊆ Z := by
  intro W Z h
  induction h with
  | gamma hZ => exact ⟨MemS.gamma, hZ ▸ MemS.gamma, hZ ▸ subset_rfl⟩
  | leaf hrel => exact ⟨MemS.zero hrel.1, hrel.2.1, hrel.2.2⟩
  | @node P Q Z₁ Z₂ Z hP hQ hvrel ihP ihQ =>
      obtain ⟨hPmem, hZ1mem, hPZ1⟩ := ihP
      obtain ⟨hQmem, hZ2mem, hQZ2⟩ := ihQ
      obtain ⟨-, hZmem, A, B, hAmem, hBmem, heq, hsub⟩ := hvrel
      obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
      exact ⟨MemS.pair hPmem hQmem, hZmem, (embPair_subset.mpr ⟨hPZ1, hQZ2⟩).trans hsub⟩

/-- Backward direction: every `idMap`-related pair is `GRel (inSharpMap) (pairSharpMap)`-related,
by structural induction on `W`'s `MemS`-derivation (generalizing over `Z`). -/
theorem idMap_rel_imp_grel_inSharp_pairSharp :
    ∀ {W}, MemS D W → ∀ {Z}, MemS D Z → W ⊆ Z → GRel (inSharpMap hD) (pairSharpMap hD) W Z := by
  intro W hW
  induction hW with
  | gamma =>
      intro Z hZ hsub
      have hZeq : Z = Gamma D := Set.Subset.antisymm (memS_subset_gamma hZ) hsub
      subst hZeq
      exact GRel.gamma rfl
  | @zero X hX =>
      intro Z hZ hsub
      exact GRel.leaf ⟨hX, hZ, hsub⟩
  | @pair P Q hP hQ ihP ihQ =>
      intro Z hZ hsub
      exact GRel.node (ihP hP subset_rfl) (ihQ hQ subset_rfl)
        ⟨prod_mem_prodNbhd hP hQ, hZ, P, Q, hP, hQ, rfl, hsub⟩

/-- **`gMap in pair = I_{D§}`**: the catamorphism instantiated at `u := in`, `v := pair` (the tree
algebra's own structure maps) is the identity on `D§`. -/
theorem gMap_inSharp_pairSharp_eq_idMap :
    gMap (inSharpMap hD) (pairSharpMap hD) hD = idMap (Dsharp D hD) := by
  apply le_antisymm
  · rw [ApproximableMap.le_iff]
    intro W Z h
    exact grel_inSharp_pairSharp_imp_idMap_rel h
  · rw [ApproximableMap.le_iff]
    intro W Z h
    exact idMap_rel_imp_grel_inSharp_pairSharp h.1 h.2.1 h.2.2

/-! ## Uniqueness of the catamorphism (Exercise 8.21(b), step 1)

Scott's own justification for idempotence-transport ("`g` is unique because the values on finite
elements are fixed") is made precise here: any *strict* map `k : D^§ → E` satisfying the same two
defining equations as `gMap u v hD` (on the nose, at the *element* level) is literally equal to it as
an `ApproximableMap`. The proof works with `k`'s neighbourhood relation directly, by induction on the
`MemS`-derivation of the input neighbourhood `W` — mirroring `gMap_in`/`gMap_pair`'s own proof style,
using `rel_iff_mem_principal` to bridge between `k`'s abstract relation and the assumed *element*-level
equations at the principal element of each `MemS`-shape. Two small "principal of the constructor is
the constructor of principals" identities do the bridging work (`inSharp_principal`,
`pairSharp_principal`); the general `pair_principal_eq_principal_prodNbhd` (about `prod`, not
`Dsharp` specifically) underlies the second one. -/

/-- **`⟨↑P, ↑Q⟩ = ↑(P∪Q)`** (general, for any two neighbourhood systems): the pairing of two
principal elements is the principal element of the product neighbourhood. -/
theorem pair_principal_eq_principal_prodNbhd {γ δ : Type*} {V₀ : NeighborhoodSystem γ}
    {V₁ : NeighborhoodSystem δ} {P : Set γ} {Q : Set δ} (hP : V₀.mem P) (hQ : V₁.mem Q) :
    pair (V₀.principal hP) (V₁.principal hQ)
      = (prod V₀ V₁).principal (prod_mem_prodNbhd hP hQ) := by
  apply Element.ext
  intro W
  simp only [mem_pair, mem_principal, prod_mem_iff]
  constructor
  · rintro ⟨P', Q', ⟨hP', hPP'⟩, ⟨hQ', hQQ'⟩, rfl⟩
    exact ⟨⟨P', Q', hP', hQ', rfl⟩, prodNbhd_subset_iff.mpr ⟨hPP', hQQ'⟩⟩
  · rintro ⟨⟨P', Q', hP', hQ', rfl⟩, hsub⟩
    obtain ⟨hPP', hQQ'⟩ := prodNbhd_subset_iff.mp hsub
    exact ⟨P', Q', ⟨hP', hPP'⟩, ⟨hQ', hQQ'⟩, rfl⟩

/-- **`x^§|_{↑X} = ↑(0X)`**: `inSharp` sends the principal element `↑X` to the principal element of
the leaf neighbourhood `0X`. -/
theorem inSharp_principal {X : Set α} (hX : D.mem X) :
    inSharp D hD (D.principal hX) = (Dsharp D hD).principal (MemS.zero hX) := by
  rw [← inSharpMap_toElementMap hD]
  apply Element.ext
  intro W
  simp only [mem_principal, ← rel_iff_mem_principal (inSharpMap hD) hX, inSharpMap_rel]
  exact ⟨fun h => h.2, fun h => ⟨hX, h⟩⟩

/-- **`⟨↑P, ↑Q⟩^§ = ↑(1P∪2Q)`**: `pairSharp` sends a pair of principal elements to the principal
element of the corresponding node neighbourhood. -/
theorem pairSharp_principal {P Q : Set (List Bool × α)} (hP : MemS D P) (hQ : MemS D Q) :
    pairSharp D hD ((Dsharp D hD).principal hP) ((Dsharp D hD).principal hQ)
      = (Dsharp D hD).principal (MemS.pair hP hQ) := by
  rw [← pairSharpMap_toElementMap hD, pair_principal_eq_principal_prodNbhd hP hQ]
  apply Element.ext
  intro W
  rw [mem_principal, ← rel_iff_mem_principal (pairSharpMap hD) (prod_mem_prodNbhd hP hQ),
    pairSharpMap_rel]
  constructor
  · rintro ⟨-, hW, A, B, hA, hB, heq, hsub⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hW, hsub⟩
  · rintro ⟨hW, hsub⟩
    exact ⟨prod_mem_prodNbhd hP hQ, hW, P, Q, hP, hQ, rfl, hsub⟩

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- **Uniqueness of the catamorphism** (Exercise 8.21(b)(1), Scott's own remark "`g` is unique
because the values on finite elements are fixed"). Any *strict* `k : D^§ → E` satisfying `gMap`'s two
defining equations at the *element* level — `k(x^§) = u(x)` and `k(⟨y,z⟩) = v(⟨k(y),k(z)⟩)` — is
literally the catamorphism `gMap u v hD`. Proved by induction on the `MemS`-derivation of the input
neighbourhood, generalizing over the output: the `Γ` case is strictness plus `master_rel`; the leaf
case reads the hypothesis off at the principal element `↑X` via `inSharp_principal` and
`rel_iff_mem_principal`; the node case does the same with `pairSharp_principal`, using the induction
hypotheses to identify the two recursive outputs. -/
theorem gMap_eq_of_satisfies {k : ApproximableMap (Dsharp D hD) E} (hk : IsStrict k)
    (hu : ∀ x : D.Element, k.toElementMap (inSharp D hD x) = u.toElementMap x)
    (hv : ∀ y z : (Dsharp D hD).Element,
      k.toElementMap (pairSharp D hD y z)
        = v.toElementMap (pair (k.toElementMap y) (k.toElementMap z))) :
    k = gMap u v hD := by
  have main : ∀ {W}, MemS D W → ∀ Z, k.rel W Z ↔ GRel u v W Z := by
    intro W hW
    induction hW with
    | gamma =>
        intro Z
        constructor
        · intro h; exact GRel.gamma (hk h)
        · intro h
          have hZ : Z = E.master := gRel_gamma_inv hD h
          subst hZ
          exact k.master_rel
    | @zero X hX =>
        intro Z
        have key := hu (D.principal hX)
        rw [inSharp_principal hX] at key
        constructor
        · intro h
          have h1 := (rel_iff_mem_principal k (MemS.zero hX)).mp h
          rw [key] at h1
          exact GRel.leaf ((rel_iff_mem_principal u hX).mpr h1)
        · intro h
          have h1 := (rel_iff_mem_principal u hX).mp (gRel_embZero_inv hD h)
          rw [← key] at h1
          exact (rel_iff_mem_principal k (MemS.zero hX)).mpr h1
    | @pair P Q hP hQ ihP ihQ =>
        intro Z
        have key := hv ((Dsharp D hD).principal hP) ((Dsharp D hD).principal hQ)
        rw [pairSharp_principal hP hQ] at key
        constructor
        · intro h
          have h1 := (rel_iff_mem_principal k (MemS.pair hP hQ)).mp h
          rw [key] at h1
          obtain ⟨V, hVmem, hVrel⟩ := h1
          obtain ⟨Z1, Z2, hZ1, hZ2, rfl⟩ := hVmem
          have hkZ1 : k.rel P Z1 := (rel_iff_mem_principal k hP).mpr hZ1
          have hkZ2 : k.rel Q Z2 := (rel_iff_mem_principal k hQ).mpr hZ2
          exact GRel.node ((ihP Z1).mp hkZ1) ((ihQ Z2).mp hkZ2) hVrel
        · intro h
          obtain ⟨Z1, Z2, hg1, hg2, hvrel⟩ := gRel_embPair_inv hD h
          have h1 := (rel_iff_mem_principal k hP).mp ((ihP Z1).mpr hg1)
          have h2 := (rel_iff_mem_principal k hQ).mp ((ihQ Z2).mpr hg2)
          have h3 : (v.toElementMap (pair (k.toElementMap ((Dsharp D hD).principal hP))
              (k.toElementMap ((Dsharp D hD).principal hQ)))).mem Z :=
            ⟨prodNbhd Z1 Z2, ⟨Z1, Z2, h1, h2, rfl⟩, hvrel⟩
          rw [← key] at h3
          exact (rel_iff_mem_principal k (MemS.pair hP hQ)).mpr h3
  apply ApproximableMap.ext
  intro W Z
  by_cases hW : MemS D W
  · exact main hW Z
  · exact ⟨fun h => absurd (k.rel_dom h) hW, fun h => absurd (gRel_dom h) hW⟩

/-- **Exercise 8.21(b)(2), general form.** If `a : D → D` is a retraction, so is the recursive
extension `gMap ((inSharpMap hD).comp a) (pairSharpMap hD) hD` of `a`'s tree algebra (`aSharpInner a`
specializes this at `D := U`). Applies `gMap_eq_of_satisfies` to `k := g.comp g` (`g` the catamorphism
itself): both defining equations of `k` reduce, via `gMap_in`/`gMap_pair` applied twice, to the
corresponding equation for `g` composed with `a`'s own idempotence. -/
theorem gMap_selfComp_eq_of_isRetraction {a : ApproximableMap D D} (ha : IsRetraction a) :
    (gMap ((inSharpMap hD).comp a) (pairSharpMap hD) hD).comp
        (gMap ((inSharpMap hD).comp a) (pairSharpMap hD) hD)
      = gMap ((inSharpMap hD).comp a) (pairSharpMap hD) hD := by
  set u : ApproximableMap D (Dsharp D hD) := (inSharpMap hD).comp a with hu_def
  set v : ApproximableMap (prod (Dsharp D hD) (Dsharp D hD)) (Dsharp D hD) :=
    pairSharpMap hD with hv_def
  set g : ApproximableMap (Dsharp D hD) (Dsharp D hD) := gMap u v hD with hg_def
  have hu_eq : ∀ y : D.Element, u.toElementMap y = inSharp D hD (a.toElementMap y) := by
    intro y; rw [hu_def, toElementMap_comp, inSharpMap_toElementMap]
  show g.comp g = g
  apply gMap_eq_of_satisfies
  · rw [hg_def]; exact isStrict_comp (gMap_strict hD) (gMap_strict hD)
  · intro x
    have e1 : g.toElementMap (inSharp D hD x) = u.toElementMap x := by
      rw [hg_def]; exact gMap_in hD x
    have e2 : g.toElementMap (u.toElementMap x) = u.toElementMap (a.toElementMap x) := by
      rw [hu_eq x, hg_def]; exact gMap_in hD (a.toElementMap x)
    calc (g.comp g).toElementMap (inSharp D hD x)
        = g.toElementMap (g.toElementMap (inSharp D hD x)) := toElementMap_comp _ _ _
      _ = g.toElementMap (u.toElementMap x) := by rw [e1]
      _ = u.toElementMap (a.toElementMap x) := e2
      _ = inSharp D hD (a.toElementMap (a.toElementMap x)) := hu_eq _
      _ = inSharp D hD (a.toElementMap x) := by rw [toElementMap_idem_of_isRetraction ha]
      _ = u.toElementMap x := (hu_eq x).symm
  · intro y z
    have e1 : g.toElementMap (pairSharp D hD y z)
        = v.toElementMap (pair (g.toElementMap y) (g.toElementMap z)) := by
      rw [hg_def]; exact gMap_pair hD y z
    have e2 : v.toElementMap (pair (g.toElementMap y) (g.toElementMap z))
        = pairSharp D hD (g.toElementMap y) (g.toElementMap z) := by
      rw [hv_def]; exact pairSharpMap_toElementMap hD _ _
    have e3 : g.toElementMap (pairSharp D hD (g.toElementMap y) (g.toElementMap z))
        = v.toElementMap
            (pair (g.toElementMap (g.toElementMap y)) (g.toElementMap (g.toElementMap z))) := by
      rw [hg_def]; exact gMap_pair hD _ _
    calc (g.comp g).toElementMap (pairSharp D hD y z)
        = g.toElementMap (g.toElementMap (pairSharp D hD y z)) := toElementMap_comp _ _ _
      _ = g.toElementMap (v.toElementMap (pair (g.toElementMap y) (g.toElementMap z))) := by
          rw [e1]
      _ = g.toElementMap (pairSharp D hD (g.toElementMap y) (g.toElementMap z)) := by rw [e2]
      _ = v.toElementMap
            (pair (g.toElementMap (g.toElementMap y)) (g.toElementMap (g.toElementMap z))) := e3
      _ = v.toElementMap (pair ((g.comp g).toElementMap y) ((g.comp g).toElementMap z)) := by
          rw [toElementMap_comp, toElementMap_comp]

/-! ## `U§ ⊴ U` -/

/-- **`i§ : U§ → U`** (Definition-8.9-style fixed computable projection pair for `U§`). -/
noncomputable def iSharp : ApproximableMap (Dsharp U U_mem_nonempty) U :=
  (theorem_8_8_b_strong (dsharpPresentation UComputablePresentation U_mem_nonempty)).choose

/-- **`j§ : U → U§`**. -/
noncomputable def jSharp : ApproximableMap U (Dsharp U U_mem_nonempty) :=
  (theorem_8_8_b_strong (dsharpPresentation UComputablePresentation U_mem_nonempty)).choose_spec.choose

theorem jSharp_comp_iSharp : jSharp.comp iSharp = idMap _ :=
  (theorem_8_8_b_strong (dsharpPresentation UComputablePresentation U_mem_nonempty)).choose_spec.choose_spec.1

theorem iSharp_comp_jSharp_le : iSharp.comp jSharp ≤ idMap U :=
  (theorem_8_8_b_strong (dsharpPresentation UComputablePresentation U_mem_nonempty)).choose_spec.choose_spec.2.1

theorem iSharp_isComputableMap :
    IsComputableMap (dsharpPresentation UComputablePresentation U_mem_nonempty)
      UComputablePresentation iSharp :=
  (theorem_8_8_b_strong (dsharpPresentation UComputablePresentation U_mem_nonempty)).choose_spec.choose_spec.2.2.1

theorem jSharp_isComputableMap :
    IsComputableMap UComputablePresentation
      (dsharpPresentation UComputablePresentation U_mem_nonempty) jSharp :=
  (theorem_8_8_b_strong (dsharpPresentation UComputablePresentation U_mem_nonempty)).choose_spec.choose_spec.2.2.2

/-- **`U§ ⊴ U`.** -/
theorem dsharpU_trianglelefteq_U : Dsharp U U_mem_nonempty ⊴ U :=
  trianglelefteq_of_projectionPair iSharp jSharp jSharp_comp_iSharp iSharp_comp_jSharp_le

/-! ## The operator `λa. a§` -/

/-- **The "inner" recursive extension of `a : U → U` to `U§ → U§`**, satisfying `a§(x§) = (a x)§`
and `a§(⟨y,z⟩) = ⟨a§(y), a§(z)⟩` by `gMap_in`/`gMap_pair` — Scott's fixed-point construction for
`a§`, realized directly by Exercise 7.17 Part 2's catamorphism `gMap`. -/
noncomputable def aSharpInner (a : ApproximableMap U U) :
    ApproximableMap (Dsharp U U_mem_nonempty) (Dsharp U U_mem_nonempty) :=
  gMap ((inSharpMap U_mem_nonempty).comp a) (pairSharpMap U_mem_nonempty) U_mem_nonempty

/-- **Scott's operator `a§ : U → U`** (Exercise 8.21), conjugating `aSharpInner a` through the
`U§ ⊴ U` projection pair, exactly as Definition 8.9 builds `a+b`, `a×b`, `a→b`. -/
noncomputable def aSharp (a : ApproximableMap U U) : ApproximableMap U U :=
  iSharp.comp ((aSharpInner a).comp jSharp)

theorem aSharp_eq (a : ApproximableMap U U) :
    aSharp a = iSharp.comp ((aSharpInner a).comp jSharp) := rfl

/-- **`a§` is computable whenever `a` is.** -/
theorem aSharp_isComputable {a : ApproximableMap U U}
    (ha : IsComputableMap UComputablePresentation UComputablePresentation a) :
    IsComputableMap UComputablePresentation UComputablePresentation (aSharp a) := by
  have hu : IsComputableMap UComputablePresentation
      (dsharpPresentation UComputablePresentation U_mem_nonempty)
      ((inSharpMap U_mem_nonempty).comp a) :=
    comp_isComputable ha (inSharp_isComputable U_mem_nonempty UComputablePresentation)
  have hInner : IsComputableMap (dsharpPresentation UComputablePresentation U_mem_nonempty)
      (dsharpPresentation UComputablePresentation U_mem_nonempty) (aSharpInner a) :=
    gMap_isComputable U_mem_nonempty UComputablePresentation
      (dsharpPresentation UComputablePresentation U_mem_nonempty) hu
      (pairSharp_isComputable U_mem_nonempty UComputablePresentation)
  exact comp_isComputable (comp_isComputable jSharp_isComputableMap hInner) iSharp_isComputableMap

/-- **`a ≤ I ⟹ a§ ≤ I`** (half of "`a` a projection ⟹ `a§` a projection", Proposition 8.10's
proof recipe transcribed to `§`). -/
theorem aSharp_le_idMap_of_le {a : ApproximableMap U U} (ha : a ≤ idMap U) :
    aSharp a ≤ idMap U := by
  have h1 : (inSharpMap U_mem_nonempty).comp a ≤ inSharpMap U_mem_nonempty := by
    calc (inSharpMap U_mem_nonempty).comp a
        ≤ (inSharpMap U_mem_nonempty).comp (idMap U) := comp_mono_gen le_rfl ha
      _ = inSharpMap U_mem_nonempty := comp_idMap _
  have h2 : aSharpInner a ≤ idMap (Dsharp U U_mem_nonempty) := by
    calc aSharpInner a
        ≤ gMap (inSharpMap U_mem_nonempty) (pairSharpMap U_mem_nonempty) U_mem_nonempty :=
          gMap_mono U_mem_nonempty h1 le_rfl
      _ = idMap (Dsharp U U_mem_nonempty) := gMap_inSharp_pairSharp_eq_idMap
  calc aSharp a = iSharp.comp ((aSharpInner a).comp jSharp) := aSharp_eq a
    _ ≤ iSharp.comp ((idMap (Dsharp U U_mem_nonempty)).comp jSharp) :=
        comp_mono_gen le_rfl (comp_mono_gen h2 le_rfl)
    _ = iSharp.comp jSharp := by rw [idMap_comp]
    _ ≤ idMap U := iSharp_comp_jSharp_le

/-! ## Idempotence of `a§` (Exercise 8.21(b)) -/

theorem aSharpInner_eq (a : ApproximableMap U U) :
    aSharpInner a = gMap ((inSharpMap U_mem_nonempty).comp a) (pairSharpMap U_mem_nonempty)
      U_mem_nonempty := rfl

/-- **Exercise 8.21(b)(2).** If `a` is a retraction (`a∘a = a`), so is its recursive extension
`aSharpInner a`: the specialization of `gMap_selfComp_eq_of_isRetraction` to `D := U`. -/
theorem aSharpInner_idem_of_isRetraction {a : ApproximableMap U U} (ha : IsRetraction a) :
    IsRetraction (aSharpInner a) := by
  show (aSharpInner a).comp (aSharpInner a) = aSharpInner a
  rw [aSharpInner_eq]
  exact gMap_selfComp_eq_of_isRetraction ha

/-- **`a§`, unfolded one step through the `U§ ⊴ U` projection pair.** Mirrors
`Proposition810.lean`'s `toElementMap_prodComb`/`toElementMap_arrowComb` pattern. -/
theorem toElementMap_aSharp (a : ApproximableMap U U) (x : U.Element) :
    (aSharp a).toElementMap x
      = iSharp.toElementMap ((aSharpInner a).toElementMap (jSharp.toElementMap x)) := by
  rw [aSharp_eq]
  simp only [toElementMap_comp]

/-- **Exercise 8.21(b)(3).** Idempotence of `aSharpInner a` transports through the projection pair
`iSharp`/`jSharp` to idempotence of `aSharp a` itself — exactly `Proposition810.lean`'s
`isRetraction_prodComb`/`isRetraction_arrowComb` recipe (`toElementMap_of_comp_eq_idMap` +
`toElementMap_idem_of_isRetraction`), conjugated through `jSharp_comp_iSharp` instead of
`jTimes_comp_iTimes`/`jArrow_comp_iArrow`. -/
theorem isRetraction_aSharp {a : ApproximableMap U U} (ha2 : IsRetraction (aSharpInner a)) :
    IsRetraction (aSharp a) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_aSharp a ((aSharp a).toElementMap x),
    toElementMap_aSharp a x, toElementMap_of_comp_eq_idMap jSharp_comp_iSharp,
    toElementMap_idem_of_isRetraction ha2]

/-- **Exercise 8.21(b), assembled.** `a` a projection of `U` `⟹` `a§` a projection: the `≤ I` half
is 8.21(a)'s `aSharp_le_idMap_of_le`; the retraction half chains `aSharpInner_idem_of_isRetraction`
(the `gMap`-level idempotence, via the catamorphism-uniqueness lemma `gMap_eq_of_satisfies`) with
`isRetraction_aSharp` (transport through `U§ ⊴ U`). This completes "`a` a projection ⟹ `a§` a
projection" in full, matching `Proposition810.lean`'s `isProjection_sumComb`/`isProjection_prodComb`/
`isProjection_arrowComb`. -/
theorem isProjection_aSharp {a : ApproximableMap U U} (ha : IsProjection a) :
    IsProjection (aSharp a) :=
  ⟨isRetraction_aSharp (aSharpInner_idem_of_isRetraction ha.1), aSharp_le_idMap_of_le ha.2⟩

/-! ## `Dsharp` is functorial (Exercise 8.21(c), step 1)

The tree-algebra construction `D ↦ D§` acts on morphisms too: precomposing the injection leaf-map
`inSharpMap` with any `f : D' → D` and recursing via `gMap` extends `f` to a map `D'§ → D§`,
satisfying the expected functor laws `id§ = id` (literally `gMap_inSharp_pairSharp_eq_idMap`) and
`(f' ∘ f)§ = f'§ ∘ f§` (`dsharpMap_comp`, via the catamorphism-uniqueness lemma
`gMap_eq_of_satisfies`, exactly parallel to `gMap_selfComp_eq_of_isRetraction`'s proof but without
needing a retraction hypothesis: composing two *different* maps needs no idempotence).
`aSharpInner a` is the special case `D₀ = D₁ = U`, `f := a`. -/

section DsharpFunctor

variable {γ δ ε : Type*} {D₀ : NeighborhoodSystem γ} {D₁ : NeighborhoodSystem δ}
  {D₂ : NeighborhoodSystem ε}
variable (hD₀ : ∀ X, D₀.mem X → X.Nonempty) (hD₁ : ∀ X, D₁.mem X → X.Nonempty)
  {hD₂ : ∀ X, D₂.mem X → X.Nonempty}

/-- **The action of `D ↦ D§` on morphisms.** Recurses `f : D₁ → D₀` through the leaves via `gMap`,
leaving the pairing structure alone — the general form of `aSharpInner` (which specializes this at
`D₀ = D₁ = U`, `f := a`). -/
noncomputable def dsharpMap (f : ApproximableMap D₁ D₀) :
    ApproximableMap (Dsharp D₁ hD₁) (Dsharp D₀ hD₀) :=
  gMap ((inSharpMap hD₀).comp f) (pairSharpMap hD₀) hD₁

theorem dsharpMap_eq (f : ApproximableMap D₁ D₀) :
    dsharpMap hD₀ hD₁ f = gMap ((inSharpMap hD₀).comp f) (pairSharpMap hD₀) hD₁ := rfl

/-- **`id§ = id`.** -/
theorem dsharpMap_id : dsharpMap hD₀ hD₀ (idMap D₀) = idMap (Dsharp D₀ hD₀) := by
  rw [dsharpMap_eq, comp_idMap]
  exact gMap_inSharp_pairSharp_eq_idMap

/-- **`(f' ∘ f)§ = f'§ ∘ f§`.** Applies `gMap_eq_of_satisfies` to `k := (dsharpMap f').comp
(dsharpMap f)`: both defining equations of `k` reduce, via `gMap_in`/`gMap_pair` applied twice, to
the corresponding equation for `dsharpMap (f'.comp f)` — verbatim
`gMap_selfComp_eq_of_isRetraction`'s proof, generalized away from `f' = f` (so no retraction
hypothesis is needed here). -/
theorem dsharpMap_comp (f : ApproximableMap D₂ D₁) (f' : ApproximableMap D₁ D₀) :
    dsharpMap hD₀ hD₂ (f'.comp f) = (dsharpMap hD₀ hD₁ f').comp (dsharpMap hD₁ hD₂ f) := by
  set g1 : ApproximableMap (Dsharp D₂ hD₂) (Dsharp D₁ hD₁) := dsharpMap hD₁ hD₂ f with hg1_def
  set g2 : ApproximableMap (Dsharp D₁ hD₁) (Dsharp D₀ hD₀) := dsharpMap hD₀ hD₁ f' with hg2_def
  symm
  show g2.comp g1 = dsharpMap hD₀ hD₂ (f'.comp f)
  rw [dsharpMap_eq]
  apply gMap_eq_of_satisfies
  · exact isStrict_comp (by rw [hg2_def, dsharpMap_eq]; exact gMap_strict hD₁)
      (by rw [hg1_def, dsharpMap_eq]; exact gMap_strict hD₂)
  · intro x
    have e1 : g1.toElementMap (inSharp D₂ hD₂ x) = inSharp D₁ hD₁ (f.toElementMap x) := by
      rw [hg1_def, dsharpMap_eq, gMap_in hD₂ x, toElementMap_comp, inSharpMap_toElementMap]
    have e2 : g2.toElementMap (inSharp D₁ hD₁ (f.toElementMap x))
        = inSharp D₀ hD₀ (f'.toElementMap (f.toElementMap x)) := by
      rw [hg2_def, dsharpMap_eq, gMap_in hD₁ (f.toElementMap x), toElementMap_comp,
        inSharpMap_toElementMap]
    calc (g2.comp g1).toElementMap (inSharp D₂ hD₂ x)
        = g2.toElementMap (g1.toElementMap (inSharp D₂ hD₂ x)) := toElementMap_comp _ _ _
      _ = g2.toElementMap (inSharp D₁ hD₁ (f.toElementMap x)) := by rw [e1]
      _ = inSharp D₀ hD₀ (f'.toElementMap (f.toElementMap x)) := e2
      _ = ((inSharpMap hD₀).comp (f'.comp f)).toElementMap x := by
          rw [toElementMap_comp, toElementMap_comp, inSharpMap_toElementMap]
  · intro y z
    have e1 : g1.toElementMap (pairSharp D₂ hD₂ y z)
        = pairSharp D₁ hD₁ (g1.toElementMap y) (g1.toElementMap z) := by
      rw [hg1_def, dsharpMap_eq, gMap_pair hD₂ y z, pairSharpMap_toElementMap]
    have e2 : g2.toElementMap (pairSharp D₁ hD₁ (g1.toElementMap y) (g1.toElementMap z))
        = pairSharp D₀ hD₀ (g2.toElementMap (g1.toElementMap y))
          (g2.toElementMap (g1.toElementMap z)) := by
      rw [hg2_def, dsharpMap_eq, gMap_pair hD₁ (g1.toElementMap y) (g1.toElementMap z),
        pairSharpMap_toElementMap]
    calc (g2.comp g1).toElementMap (pairSharp D₂ hD₂ y z)
        = g2.toElementMap (g1.toElementMap (pairSharp D₂ hD₂ y z)) := toElementMap_comp _ _ _
      _ = g2.toElementMap (pairSharp D₁ hD₁ (g1.toElementMap y) (g1.toElementMap z)) := by
          rw [e1]
      _ = pairSharp D₀ hD₀ (g2.toElementMap (g1.toElementMap y))
          (g2.toElementMap (g1.toElementMap z)) := e2
      _ = (pairSharpMap hD₀).toElementMap
          (pair (g2.toElementMap (g1.toElementMap y)) (g2.toElementMap (g1.toElementMap z))) :=
        (pairSharpMap_toElementMap hD₀ _ _).symm
      _ = (pairSharpMap hD₀).toElementMap
          (pair ((g2.comp g1).toElementMap y) ((g2.comp g1).toElementMap z)) := by
        rw [toElementMap_comp, toElementMap_comp]

/-- **`aSharpInner` is `dsharpMap` at `D₀ = D₁ = U`, `f := a`.** -/
theorem dsharpMap_self_eq_aSharpInner (a : ApproximableMap U U) :
    dsharpMap U_mem_nonempty U_mem_nonempty a = aSharpInner a := rfl

end DsharpFunctor

/-! ## Exercise 8.21(c): `D_{a§} ≅ (D_a)§`

For a *finitary projection* `a` of `U`, transport `iSharp`/`jSharp` through `dsharpMap`'s
functorial action on the injection/projection pair `(fixedNbhd_subsystem a).inj/.proj` of
`D_a := fixedNbhd a ◁ U` (Proposition 6.12), producing a genuine projection pair
`I : (D_a)§ → U`, `J : U → (D_a)§`. The functor laws `dsharpMap_id`/`dsharpMap_comp` turn
`j_a ∘ i_a = I_{D_a}` (Proposition 6.12's own `proj_comp_inj`) into `J ∘ I = I_{(D_a)§}`
immediately, and `i_a ∘ j_a = a` (Theorem 8.6's `inj_comp_proj_eq_self`, using that `a` is a
finitary projection) into `I ∘ J = a§` — exactly `aSharp`'s own definition, once one notices
`aSharpInner a` is literally `dsharpMap` applied to `i_a ∘ j_a = a`.
`elementIsoOfProjectionPair` (`Proposition810b.lean`) then hands us the isomorphism directly, in
the same "domain of a projection = its `toElementMap`-fixed-point set" convention already used
throughout `Proposition810b.lean` for `D_{a+b} ≅ D_a+D_b` etc. -/

/-- **`I : (D_a)§ → U`**, transporting `iSharp` through `dsharpMap`'s action on the subsystem
injection `(fixedNbhd_subsystem a).inj : D_a → U`. -/
noncomputable def ISharpComb (a : ApproximableMap U U) :
    ApproximableMap (Dsharp (fixedNbhd a) (fixedNbhd_mem_nonempty a)) U :=
  iSharp.comp (dsharpMap U_mem_nonempty (fixedNbhd_mem_nonempty a) (fixedNbhd_subsystem a).inj)

/-- **`J : U → (D_a)§`**, symmetric to `ISharpComb`, via the subsystem projection
`(fixedNbhd_subsystem a).proj : U → D_a`. -/
noncomputable def JSharpComb (a : ApproximableMap U U) :
    ApproximableMap U (Dsharp (fixedNbhd a) (fixedNbhd_mem_nonempty a)) :=
  (dsharpMap (fixedNbhd_mem_nonempty a) U_mem_nonempty (fixedNbhd_subsystem a).proj).comp jSharp

/-- **`J ∘ I = I_{(D_a)§}`**, unconditionally (no finitary/projection hypothesis on `a` needed). -/
theorem JSharpComb_comp_ISharpComb (a : ApproximableMap U U) :
    (JSharpComb a).comp (ISharpComb a) =
      idMap (Dsharp (fixedNbhd a) (fixedNbhd_mem_nonempty a)) := by
  unfold JSharpComb ISharpComb
  rw [comp_assoc, ← comp_assoc jSharp iSharp (dsharpMap _ _ _), jSharp_comp_iSharp, idMap_comp,
    ← dsharpMap_comp, (fixedNbhd_subsystem a).proj_comp_inj, dsharpMap_id]

/-- **`I ∘ J = a§`**, when `a` is a finitary projection. -/
theorem ISharpComb_comp_JSharpComb {a : ApproximableMap U U} (ha : IsFinitaryProjection a) :
    (ISharpComb a).comp (JSharpComb a) = aSharp a := by
  unfold ISharpComb JSharpComb
  rw [comp_assoc, ← comp_assoc (dsharpMap _ _ _) (dsharpMap _ _ _) jSharp, ← dsharpMap_comp,
    inj_comp_proj_eq_self ha, dsharpMap_self_eq_aSharpInner]
  exact (aSharp_eq a).symm

/-- **Exercise 8.21(c) (Scott 1981, PRG-19).** For a finitary projection `a` of `U`, the tree
algebra `(D_a)§` of `D_a := fixedNbhd a` is order-isomorphic to `a§`'s own fixed-point domain —
Scott's headline isomorphism `D_{a§} ≅ (D_a)§`. -/
noncomputable def dsharp_fixedNbhd_elementIso {a : ApproximableMap U U}
    (ha : IsFinitaryProjection a) :
    (Dsharp (fixedNbhd a) (fixedNbhd_mem_nonempty a)).Element ≃o
      {y : U.Element // (aSharp a).toElementMap y = y} :=
  elementIsoOfProjectionPair (ISharpComb a) (JSharpComb a) (JSharpComb_comp_ISharpComb a)
    (ISharpComb_comp_JSharpComb ha).symm

/-- **`a§` is finitary whenever `a` is a finitary projection.** -/
theorem isFinitary_aSharp {a : ApproximableMap U U} (ha : IsFinitaryProjection a) :
    IsFinitary (aSharp a) :=
  isFinitary_of_projectionPair (ISharpComb a) (JSharpComb a) (JSharpComb_comp_ISharpComb a)
    (ISharpComb_comp_JSharpComb ha).symm

/-- **Exercise 8.21, in full (Scott 1981, PRG-19).** `a` a finitary projection of `U` `⟹` `a§` is
a finitary projection of `U`, with `D_{a§} ≅ (D_a)§`. -/
theorem isFinitaryProjection_aSharp {a : ApproximableMap U U} (ha : IsFinitaryProjection a) :
    IsFinitaryProjection (aSharp a) :=
  ⟨isProjection_aSharp ha.1, isFinitary_aSharp ha⟩

end Scott1980.Neighborhood

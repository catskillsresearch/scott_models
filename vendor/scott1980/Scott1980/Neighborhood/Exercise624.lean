/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Exercise619PartB

/-!
# Exercise 6.24 (Scott 1981, PRG-19, §6) — a **double fixed point** for a system of domain equations

> **EXERCISE 6.24.** Show that there must exist domains satisfying
> `D ≅ D + (D × E)` and `E ≅ D + E`,
> by using a double fixed-point method. First decide what the underlying set of tokens should be, and
> then define `D` and `E` by simultaneous fixed points. (Syntactical domains as in 6.23 may very well
> require several simultaneous equations.)

This is the **simultaneous** analogue of Exercise 6.20/6.21: there the conclusion was a single
`Γ` with `Γ = tok(T({Γ}))`, so that `{Γ} ◁ T({Γ})` and Theorem 6.14 applies; here we produce a
**pair** `(Γ_D, Γ_E)` of token sets that solve the two coupled token equations
**simultaneously**, so that the two singleton systems sit as subsystems of the two right-hand sides
at once — exactly the joint hypothesis the simultaneous form of Theorem 6.14 needs.

## Deciding the tokens

Both `D` and `E` are taken to be `∅`-free neighbourhood systems over the **single** token type
`Str = {0,1}*` (Scott's uniform category of Exercise 6.19). The two right-hand sides are built from
the uniform sum `+` (`ScottSys.sum`) and product `×` (`ScottSys.prod`), whose *master* (token set)
is in both cases the tagged union `{Λ} ∪ 0·(…) ∪ 1·(…)`. Writing `tok(𝒟) = 𝒟.master` and `{Γ}` for
the one-neighbourhood system `singletonSys Γ`, the two token recursions are

* `gTok p q = tok((D + E))      = {Λ} ∪ 0p ∪ 1q`  (for `D = {p}`, `E = {q}`),
* `fTok p q = tok((D + (D×E)))  = {Λ} ∪ 0p ∪ 1(gTok p q)`,

so `fTok p q = gTok p (gTok p q)` (the product `D × E` and the sum `D + E` have the *same* tagged
master shape).

## The double fixed point

The pair map `Φ(p, q) = (fTok p q, gTok p q)` is iterated from the bottom pair `({Λ}, {Λ})`
(`pIter`); its two component unions

`Γ_D = ⋃ₙ (Φⁿ).₁`,  `Γ_E = ⋃ₙ (Φⁿ).₂`

solve `fTok Γ_D Γ_E = Γ_D` and `gTok Γ_D Γ_E = Γ_E` (`fTok_GammaD_GammaE`, `gTok_GammaD_GammaE`).
Both `fTok`/`gTok` are *fully additive* (built from `insert`, `embBit`, `∪`), and — crucially — every
token of `fTok`/`gTok` references **at most one** of the two coordinates, so each membership is
witnessed at a *single* finite stage (no directedness merge is needed). This is the elementary
token-level continuity that makes the Kleene union a fixed point.

## The conclusion (`{Γ_D} ◁ D + (D×E)` and `{Γ_E} ◁ D + E`)

Setting `D = {Γ_D}`, `E = {Γ_E}`, the fixed-point equations say exactly that `Γ_D` (resp. `Γ_E`) is
the master of `D + (D×E)` (resp. `D + E`), so the singleton systems are subsystems of the two
right-hand sides — `Dsol_subsystem`, `Esol_subsystem`. These two facts *together* are the hypotheses
of the simultaneous Theorem 6.14, which then yields the required isomorphisms
`D ≅ D + (D×E)` and `E ≅ D + E`.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem Scott1980.Neighborhood.Exercise619
open Scott1980.Neighborhood.Example62 Scott1980.Neighborhood.ExampleB

namespace Exercise624

/-! ## The two token recursions `gTok` and `fTok` -/

/-- `gTok p q = tok((D + E))` for `D = {p}`, `E = {q}`: the tagged union `{Λ} ∪ 0p ∪ 1q`. It is also
the master of the product `{p} × {q}` (sum and product share the master shape over `{0,1}*`). -/
def gTok (p q : Set Str) : Set Str := insert ([] : Str) (embBit false p ∪ embBit true q)

/-- `fTok p q = tok((D + (D×E)))` for `D = {p}`, `E = {q}`: `{Λ} ∪ 0p ∪ 1(gTok p q)`, equivalently
`gTok p (gTok p q)`. -/
def fTok (p q : Set Str) : Set Str := gTok p (gTok p q)

theorem nil_mem_gTok (p q : Set Str) : ([] : Str) ∈ gTok p q := Set.mem_insert _ _

theorem nil_mem_fTok (p q : Set Str) : ([] : Str) ∈ fTok p q := Set.mem_insert _ _

/-- `gTok` is monotone in both arguments. -/
theorem gTok_mono {p p' q q' : Set Str} (hp : p ⊆ p') (hq : q ⊆ q') : gTok p q ⊆ gTok p' q' := by
  rintro w (rfl | ⟨w', rfl, hw'⟩ | ⟨w', rfl, hw'⟩)
  · exact Set.mem_insert _ _
  · exact Or.inr (Or.inl ⟨w', rfl, hp hw'⟩)
  · exact Or.inr (Or.inr ⟨w', rfl, hq hw'⟩)

/-- `fTok` is monotone in both arguments. -/
theorem fTok_mono {p p' q q' : Set Str} (hp : p ⊆ p') (hq : q ⊆ q') : fTok p q ⊆ fTok p' q' :=
  gTok_mono hp (gTok_mono hp hq)

/-! ## Token-level continuity over a chain: a membership reaches a single finite stage -/

/-- **Additivity of `gTok`.** Every token of `gTok (⋃ₙ aₙ) (⋃ₙ bₙ)` already lies in some
`gTok aₙ bₙ` — each token references at most one coordinate. -/
theorem mem_gTok_iUnion {a b : ℕ → Set Str} {w : Str}
    (hw : w ∈ gTok (⋃ n, a n) (⋃ n, b n)) : ∃ n, w ∈ gTok (a n) (b n) := by
  rcases hw with rfl | ⟨w', rfl, hw'⟩ | ⟨w', rfl, hw'⟩
  · exact ⟨0, nil_mem_gTok _ _⟩
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw'
    exact ⟨n, Or.inr (Or.inl ⟨w', rfl, hn⟩)⟩
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw'
    exact ⟨n, Or.inr (Or.inr ⟨w', rfl, hn⟩)⟩

/-- **Additivity of `fTok`.** Every token of `fTok (⋃ₙ aₙ) (⋃ₙ bₙ)` already lies in some
`fTok aₙ bₙ`. The nested `true`-branch (the product copy `0p` inside `1(gTok p q)`) still references
at most one coordinate, so a single finite stage suffices. -/
theorem mem_fTok_iUnion {a b : ℕ → Set Str} {w : Str}
    (hw : w ∈ fTok (⋃ n, a n) (⋃ n, b n)) : ∃ n, w ∈ fTok (a n) (b n) := by
  rcases hw with rfl | ⟨w', rfl, hw'⟩ | ⟨u, rfl, hu⟩
  · exact ⟨0, nil_mem_fTok _ _⟩
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw'
    exact ⟨n, Or.inr (Or.inl ⟨w', rfl, hn⟩)⟩
  · rcases hu with rfl | ⟨u', rfl, hu'⟩ | ⟨u', rfl, hu'⟩
    · exact ⟨0, Or.inr (Or.inr ⟨[], rfl, nil_mem_gTok _ _⟩)⟩
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hu'
      exact ⟨n, Or.inr (Or.inr ⟨false :: u', rfl, Or.inr (Or.inl ⟨u', rfl, hn⟩)⟩)⟩
    · obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hu'
      exact ⟨n, Or.inr (Or.inr ⟨true :: u', rfl, Or.inr (Or.inr ⟨u', rfl, hn⟩)⟩)⟩

/-! ## The simultaneous Kleene iteration `Φⁿ({Λ}, {Λ})` -/

/-- The pair iteration `Φ(p, q) = (fTok p q, gTok p q)` from the bottom pair `({Λ}, {Λ})`. -/
def pIter : ℕ → Set Str × Set Str
  | 0 => ({([] : Str)}, {([] : Str)})
  | n + 1 => (fTok (pIter n).1 (pIter n).2, gTok (pIter n).1 (pIter n).2)

/-- The first component of the double fixed point, `Γ_D = ⋃ₙ (Φⁿ).₁`. -/
def GammaD : Set Str := ⋃ n, (pIter n).1

/-- The second component of the double fixed point, `Γ_E = ⋃ₙ (Φⁿ).₂`. -/
def GammaE : Set Str := ⋃ n, (pIter n).2

theorem nil_mem_GammaD : ([] : Str) ∈ GammaD := Set.mem_iUnion.mpr ⟨0, rfl⟩

theorem nil_mem_GammaE : ([] : Str) ∈ GammaE := Set.mem_iUnion.mpr ⟨0, rfl⟩

/-- Each stage sits inside the colimit `Γ_D` (choice-free; avoids `Set.subset_iUnion`). -/
theorem pIter_fst_subset_GammaD (m : ℕ) : (pIter m).1 ⊆ GammaD :=
  fun _ hx => Set.mem_iUnion.mpr ⟨m, hx⟩

/-- Each stage sits inside the colimit `Γ_E` (choice-free). -/
theorem pIter_snd_subset_GammaE (m : ℕ) : (pIter m).2 ⊆ GammaE :=
  fun _ hx => Set.mem_iUnion.mpr ⟨m, hx⟩

/-! ## The double fixed point -/

/-- **First equation of the double fixed point:** `fTok Γ_D Γ_E = Γ_D`, i.e. `tok(D + (D×E)) = Γ_D`
for `D = {Γ_D}`, `E = {Γ_E}`. -/
theorem fTok_GammaD_GammaE : fTok GammaD GammaE = GammaD := by
  apply Set.Subset.antisymm
  · intro w hw
    obtain ⟨n, hn⟩ :=
      mem_fTok_iUnion (a := fun n => (pIter n).1) (b := fun n => (pIter n).2) hw
    exact Set.mem_iUnion.mpr ⟨n + 1, hn⟩
  · intro w hw
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw
    cases n with
    | zero =>
        have hw0 : w = [] := hn; subst hw0; exact nil_mem_fTok _ _
    | succ m =>
        exact fTok_mono (pIter_fst_subset_GammaD m) (pIter_snd_subset_GammaE m) hn

/-- **Second equation of the double fixed point:** `gTok Γ_D Γ_E = Γ_E`, i.e. `tok(D + E) = Γ_E`. -/
theorem gTok_GammaD_GammaE : gTok GammaD GammaE = GammaE := by
  apply Set.Subset.antisymm
  · intro w hw
    obtain ⟨n, hn⟩ :=
      mem_gTok_iUnion (a := fun n => (pIter n).1) (b := fun n => (pIter n).2) hw
    exact Set.mem_iUnion.mpr ⟨n + 1, hn⟩
  · intro w hw
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw
    cases n with
    | zero =>
        have hw0 : w = [] := hn; subst hw0; exact nil_mem_gTok _ _
    | succ m =>
        exact gTok_mono (pIter_fst_subset_GammaD m) (pIter_snd_subset_GammaE m) hn

/-- **The double fixed point (token level).** There is a pair of token sets `(Γ_D, Γ_E)`, both
containing `Λ`, that solve the two coupled token equations `tok(D + (D×E)) = Γ_D` and
`tok(D + E) = Γ_E` simultaneously. -/
theorem exists_double_fixedPoint :
    ∃ Γd Γe : Set Str, ([] : Str) ∈ Γd ∧ ([] : Str) ∈ Γe ∧
      fTok Γd Γe = Γd ∧ gTok Γd Γe = Γe :=
  ⟨GammaD, GammaE, nil_mem_GammaD, nil_mem_GammaE, fTok_GammaD_GammaE, gTok_GammaD_GammaE⟩

/-! ## The two solution systems and the simultaneous subsystem facts -/

/-- The solution system `D = {Γ_D}`. -/
def Dsol : ScottSys := singletonSys GammaD ⟨[], nil_mem_GammaD⟩

/-- The solution system `E = {Γ_E}`. -/
def Esol : ScottSys := singletonSys GammaE ⟨[], nil_mem_GammaE⟩

/-- The first right-hand side `D + (D × E)`. -/
def Fsol (D E : ScottSys) : ScottSys := D.sum (D.prod E)

/-- The second right-hand side `D + E`. -/
def Gsol (D E : ScottSys) : ScottSys := D.sum E

/-- The master (token set) of `D + (D×E)` is `fTok Γ_D Γ_E` — definitionally, the sum/product
masters expand to the tagged-union shape `gTok`/`fTok`. -/
theorem master_Fsol : (Fsol Dsol Esol).sys.master = fTok GammaD GammaE := rfl

/-- The master (token set) of `D + E` is `gTok Γ_D Γ_E`. -/
theorem master_Gsol : (Gsol Dsol Esol).sys.master = gTok GammaD GammaE := rfl

/-- **`{Γ_D} ◁ D + (D × E)`.** The singleton system `D = {Γ_D}` is a subsystem of `D + (D×E)`: by the
fixed point its only neighbourhood `Γ_D` is the master of `D + (D×E)`. -/
theorem Dsol_subsystem : Dsol.sys ◁ (Fsol Dsol Esol).sys := by
  have hmaster : (Fsol Dsol Esol).sys.master = GammaD := master_Fsol.trans fTok_GammaD_GammaE
  refine ⟨hmaster.symm, ?_, ?_⟩
  · intro X hX
    have hXeq : X = GammaD := hX
    rw [hXeq, ← hmaster]
    exact (Fsol Dsol Esol).sys.master_mem
  · intro X Y hX hY _
    show X ∩ Y = GammaD
    rw [show X = GammaD from hX, show Y = GammaD from hY, Set.inter_self]

/-- **`{Γ_E} ◁ D + E`.** The singleton system `E = {Γ_E}` is a subsystem of `D + E`: by the fixed
point its only neighbourhood `Γ_E` is the master of `D + E`. -/
theorem Esol_subsystem : Esol.sys ◁ (Gsol Dsol Esol).sys := by
  have hmaster : (Gsol Dsol Esol).sys.master = GammaE := master_Gsol.trans gTok_GammaD_GammaE
  refine ⟨hmaster.symm, ?_, ?_⟩
  · intro X hX
    have hXeq : X = GammaE := hX
    rw [hXeq, ← hmaster]
    exact (Gsol Dsol Esol).sys.master_mem
  · intro X Y hX hY _
    show X ∩ Y = GammaE
    rw [show X = GammaE from hX, show Y = GammaE from hY, Set.inter_self]

/-- **Exercise 6.24 (object level).** By the double fixed-point method there exist `∅`-free systems
`D`, `E` over `{0,1}*` such that `{D} ◁ D + (D×E)` and `{E} ◁ D + E` **simultaneously**. These two
facts are exactly the joint hypothesis of the simultaneous Theorem 6.14, which then yields the
required isomorphisms `D ≅ D + (D×E)` and `E ≅ D + E`. -/
theorem exists_simultaneous_subsystems :
    ∃ D E : ScottSys, D.sys ◁ (D.sum (D.prod E)).sys ∧ E.sys ◁ (D.sum E).sys :=
  ⟨Dsol, Esol, Dsol_subsystem, Esol_subsystem⟩

end Exercise624

end Scott1980.Neighborhood

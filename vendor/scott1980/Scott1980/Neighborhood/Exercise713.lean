/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Definition71

/-!
# Exercise 7.13 (Scott 1981, PRG-19, §7) — effectively given domains ↔ an `INCL` relation on `ℕ`

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19, Lecture VII.

> **Exercise 7.13.** Show that an effectively given domain can always be identified with a relation
> `INCL(n, m)` on integers, where the two derived relations
>
> * `CONS(n, m)  :↔  ∃ k. INCL(k, n) ∧ INCL(k, m)`               (consistency), and
> * `MEET(n, m, k) :↔ ∀ j. (INCL(j, k) ↔ INCL(j, n) ∧ INCL(j, m))` (binary meet)
>
> are both recursively decidable, and where the axioms hold:
>
> * (i)   `∀ n. INCL(n, n)`                                   (reflexive)
> * (ii)  `∀ n m k. INCL(n, m) ∧ INCL(m, k) → INCL(n, k)`      (transitive)
> * (iii) `∃ m ∀ n. INCL(n, m)`                               (a greatest code — the master `Δ`)
> * (iv)  `∀ n m. CONS(n, m) → ∃ k. MEET(n, m, k)`            (consistent pairs have a meet)
>
> (Hint: consider the neighbourhood system `𝒟 = { {m ∣ INCL(m, n)} ∣ n }`. Is this essentially any
> effectively given system?)

## What this file proves

`INCL(n, m)` is the integer image of `Xₙ ⊆ Xₘ`. The exercise is an **equivalence**, formalized here
in both directions plus the two round-trips:

* **`InclStructure`** — the abstract data Scott asks for: a relation `INCL` with recursively decidable
  `INCL`/`CONS`/`MEET`, and axioms (i)–(iv). Following the project's `ComputablePresentation`
  convention (which carries `inter` as primitive-recursive *data* rather than recovering it by an
  unbounded μ-search), we carry the *witnesses* of (iii)/(iv) as a master index `topIdx` and a
  primitive-recursive meet function `meetIdx`; the literal existential axioms (iii)/(iv) are then
  recovered as theorems (`axiom_iii`/`axiom_iv`).
* **(⇐) `InclStructure.toSystem` / `toPresentation` / `toSystem_isEffectivelyGiven`** — Scott's hint
  system `Sₙ = {m ∣ INCL(m, n)}` is a neighbourhood system and is *effectively given*. The crux is
  `toNbhd_subset_iff : Sₙ ⊆ Sₖ ↔ INCL(n, k)` (← by transitivity (ii), → because `n ∈ Sₙ` by
  reflexivity (i)); relation 7.1(i) is `MEET` (`toNbhd_inter_eq_iff`), 7.1(ii) is `CONS`.
* **(⇒) `ofPresentation`** — every effectively given domain yields such an `InclStructure` with
  `INCL n m := Xₙ ⊆ Xₘ`. The only non-trivial decidability is `MEET`: on an effectively given system
  `MEET(n, m, k) ↔ Xₙ ∩ Xₘ = Xₖ` (`meet_iff_interEq`; ⇒ uses that a `MEET` witness makes `(n, m)`
  consistent, hence `Xₙ ∩ Xₘ ∈ 𝒟` by `inter_mem`, hence enumerated by `surj`), so `MEET` is decided
  by the presentation's `interEq`.
* **Round-trip A `ofPresentation_toPresentation_INCL`** — `INCL ↦ 𝒟 ↦ INCL` recovers `INCL` exactly.
* **Round-trip B `reconstruct_isomorphic`** — `toSystem (ofPresentation P) ≅ᴰ V`: the reconstructed
  system *is* (domain-)isomorphic to the original, answering Scott's "Is this essentially any
  effectively given system?" with **yes**. (Exercise 7.18's *effective* isomorphism would tighten
  "essentially" to the effective level.)

## Choice discipline

The `INCL`/`CONS`/`MEET` deciders and the presentation *data* are built on the choice-free
`Recursive.lean` layer and audit `⊆ {propext, Quot.sound}`. `Set`-equality/membership reasoning over
the arbitrary carrier `α` (the `MEET ↔ interEq` proof, the isomorphism's filter/`OrderIso` laws)
pulls `Classical.choice` at the `Prop` level only — the same pattern as Theorems 7.4/7.5/7.10.
-/

namespace Scott1980.Neighborhood.Exercise713

open NeighborhoodSystem Domain.Recursive

/-- **Exercise 7.13 — the abstract data.** A relation `INCL : ℕ → ℕ → Prop` together with the
witnesses and decidability/axiom data Scott requires. The derived relations are
`CONS`/`MEET` (below); the literal existential axioms (iii)/(iv) are `axiom_iii`/`axiom_iv`.

We carry `topIdx` (a master code) and a primitive-recursive `meetIdx` as *data* — exactly mirroring
`ComputablePresentation`, which carries its `inter` function as primitive-recursive data rather than
recovering it by an unbounded search. This is the faithful "effective" reading of axioms (iii)/(iv).
-/
structure InclStructure where
  /-- Scott's integer inclusion relation `INCL(n, m)` (the image of `Xₙ ⊆ Xₘ`). -/
  INCL : ℕ → ℕ → Prop
  /-- A primitive-recursive meet function: an index of the binary meet of consistent codes. -/
  meetIdx : ℕ → ℕ → ℕ
  /-- A master code (witness of axiom (iii)). -/
  topIdx : ℕ
  /-- `INCL` is recursively decidable. -/
  incl_dec : RecDecidable₂ INCL
  /-- `CONS(n, m) ↔ ∃ k. INCL(k, n) ∧ INCL(k, m)` is recursively decidable. -/
  cons_dec : RecDecidable₂ (fun n m => ∃ k, INCL k n ∧ INCL k m)
  /-- `MEET(n, m, k) ↔ ∀ j. (INCL(j, k) ↔ INCL(j, n) ∧ INCL(j, m))` is recursively decidable. -/
  meet_dec : RecDecidable₃ (fun n m k => ∀ j, INCL j k ↔ (INCL j n ∧ INCL j m))
  /-- The meet function is primitive recursive (on the `Nat.pair` coding of `n, m`). -/
  meetIdx_primrec : Nat.Primrec (fun t => meetIdx t.unpair.1 t.unpair.2)
  /-- **(i)** `INCL` is reflexive. -/
  incl_refl : ∀ n, INCL n n
  /-- **(ii)** `INCL` is transitive. -/
  incl_trans : ∀ {n m k}, INCL n m → INCL m k → INCL n k
  /-- **(iii)** the master code `topIdx` is `INCL`-greatest. -/
  topIdx_spec : ∀ n, INCL n topIdx
  /-- **(iv)** `meetIdx n m` is a `MEET` of `n, m` whenever `(n, m)` is consistent. -/
  meetIdx_spec : ∀ {n m}, (∃ k, INCL k n ∧ INCL k m) →
    ∀ j, INCL j (meetIdx n m) ↔ (INCL j n ∧ INCL j m)

namespace InclStructure

variable (I : InclStructure)

/-- Scott's consistency relation `CONS(n, m) :↔ ∃ k. INCL(k, n) ∧ INCL(k, m)`. -/
def CONS (n m : ℕ) : Prop := ∃ k, I.INCL k n ∧ I.INCL k m

/-- Scott's binary-meet relation `MEET(n, m, k) :↔ ∀ j. (INCL(j, k) ↔ INCL(j, n) ∧ INCL(j, m))`. -/
def MEET (n m k : ℕ) : Prop := ∀ j, I.INCL j k ↔ (I.INCL j n ∧ I.INCL j m)

/-- **Axiom (i).** `INCL` is reflexive. -/
theorem axiom_i (n : ℕ) : I.INCL n n := I.incl_refl n

/-- **Axiom (ii).** `INCL` is transitive. -/
theorem axiom_ii {n m k : ℕ} (h1 : I.INCL n m) (h2 : I.INCL m k) : I.INCL n k := I.incl_trans h1 h2

/-- **Axiom (iii).** There is an `INCL`-greatest code. -/
theorem axiom_iii : ∃ m, ∀ n, I.INCL n m := ⟨I.topIdx, I.topIdx_spec⟩

/-- **Axiom (iv).** Consistent pairs have a meet. -/
theorem axiom_iv (n m : ℕ) (h : I.CONS n m) : ∃ k, I.MEET n m k :=
  ⟨I.meetIdx n m, I.meetIdx_spec h⟩

/-! ### (⇐) Scott's hint system `Sₙ = {m ∣ INCL(m, n)}` -/

/-- The hint neighbourhood `Sₙ = {m ∣ INCL(m, n)}` over the token type `ℕ`. -/
def toNbhd (n : ℕ) : Set ℕ := {m | I.INCL m n}

@[simp] theorem mem_toNbhd {n m : ℕ} : m ∈ I.toNbhd n ↔ I.INCL m n := Iff.rfl

/-- **The key inclusion law:** `Sₙ ⊆ Sₖ ↔ INCL(n, k)`. `→` reads off `INCL(n, k)` from `n ∈ Sₙ`
(reflexivity (i)); `←` is transitivity (ii). -/
theorem toNbhd_subset_iff {n k : ℕ} : I.toNbhd n ⊆ I.toNbhd k ↔ I.INCL n k := by
  constructor
  · intro h
    exact h (I.incl_refl n)
  · intro hnk m hm
    exact I.incl_trans hm hnk

/-- `S_{topIdx} = ℕ`: the master code's neighbourhood is everything (axiom (iii)). -/
theorem toNbhd_top : I.toNbhd I.topIdx = Set.univ := by
  ext m
  simp only [mem_toNbhd, Set.mem_univ, iff_true]
  exact I.topIdx_spec m

/-- `Sₖ ⊆ Sₙ ∩ Sₘ ↔ INCL(k, n) ∧ INCL(k, m)`. -/
theorem toNbhd_subset_inter_iff (k n m : ℕ) :
    I.toNbhd k ⊆ I.toNbhd n ∩ I.toNbhd m ↔ (I.INCL k n ∧ I.INCL k m) := by
  rw [Set.subset_inter_iff, I.toNbhd_subset_iff, I.toNbhd_subset_iff]

/-- `Sₙ ∩ Sₘ = Sₖ ↔ MEET(n, m, k)` — Scott's relation 7.1(i) *is* `MEET`. -/
theorem toNbhd_inter_eq_iff (n m k : ℕ) :
    I.toNbhd n ∩ I.toNbhd m = I.toNbhd k ↔ I.MEET n m k := by
  unfold MEET
  rw [Set.ext_iff]
  refine forall_congr' fun j => ?_
  rw [Set.mem_inter_iff, mem_toNbhd, mem_toNbhd, mem_toNbhd]
  exact iff_comm

/-- **Exercise 7.13 (⇐) — the hint system is a neighbourhood system.** `Sₙ = {m ∣ INCL(m, n)}` over
tokens `ℕ`, master `Δ = ℕ = S_{topIdx}`; closure under intersection is axiom (iv) via `MEET`. -/
def toSystem : NeighborhoodSystem ℕ where
  mem Y := ∃ n, Y = I.toNbhd n
  master := Set.univ
  master_mem := ⟨I.topIdx, I.toNbhd_top.symm⟩
  inter_mem := by
    rintro X Y Z ⟨n, rfl⟩ ⟨m, rfl⟩ ⟨l, rfl⟩ hZsub
    have hln : I.INCL l n := I.toNbhd_subset_iff.mp (hZsub.trans Set.inter_subset_left)
    have hlm : I.INCL l m := I.toNbhd_subset_iff.mp (hZsub.trans Set.inter_subset_right)
    exact ⟨I.meetIdx n m, (I.toNbhd_inter_eq_iff n m (I.meetIdx n m)).mpr
      (I.meetIdx_spec ⟨l, hln, hlm⟩)⟩
  sub_master := by rintro X _; exact Set.subset_univ X

@[simp] theorem toSystem_mem {Y : Set ℕ} : I.toSystem.mem Y ↔ ∃ n, Y = I.toNbhd n := Iff.rfl

/-- **Exercise 7.13 (⇐) — the hint system is effectively given.** The enumeration is `Sₙ`; relation
7.1(i) `Sₙ ∩ Sₘ = Sₖ` is `MEET` (`meet_dec`); relation 7.1(ii) consistency is `CONS` (`cons_dec`);
the intersection function is `meetIdx`; the master code is `topIdx`. -/
def toPresentation : ComputablePresentation I.toSystem where
  X := I.toNbhd
  mem_X n := ⟨n, rfl⟩
  surj := by rintro Y ⟨n, rfl⟩; exact ⟨n, rfl⟩
  interEq_computable :=
    RecDecidable.of_iff
      (fun t => (I.toNbhd_inter_eq_iff t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2))
      I.meet_dec
  cons_computable :=
    RecDecidable.of_iff
      (fun t => by
        refine exists_congr fun k => ?_
        exact I.toNbhd_subset_inter_iff k t.unpair.1 t.unpair.2)
      I.cons_dec
  inter := I.meetIdx
  inter_primrec := I.meetIdx_primrec
  inter_spec := by
    intro n m hcons
    obtain ⟨k, hk⟩ := hcons
    rw [Set.subset_inter_iff] at hk
    have hcons' : I.CONS n m := ⟨k, I.toNbhd_subset_iff.mp hk.1, I.toNbhd_subset_iff.mp hk.2⟩
    exact ((I.toNbhd_inter_eq_iff n m (I.meetIdx n m)).mpr (I.meetIdx_spec hcons')).symm
  masterIdx := I.topIdx
  masterIdx_spec := I.toNbhd_top

/-- **Exercise 7.13 (⇐).** The hint system is effectively given. -/
theorem toSystem_isEffectivelyGiven : I.toSystem.IsEffectivelyGiven := ⟨I.toPresentation⟩

end InclStructure

/-! ### (⇒) Every effectively given domain yields an `InclStructure` -/

variable {α : Type*} {V : NeighborhoodSystem α}

/-- **The `MEET ↔ interEq` reduction.** On an effectively given system, Scott's `MEET(n, m, k)` is
equivalent to `Xₙ ∩ Xₘ = Xₖ`, so it is decidable by relation 7.1(i).

`⇐` is `Set.subset_inter_iff`. `⇒`: from `MEET` at `j = k` we get `Xₖ ⊆ Xₙ ∩ Xₘ`, so `Xₖ` witnesses
consistency of `(n, m)`; `inter_mem` then makes `Xₙ ∩ Xₘ` a neighbourhood, `surj` enumerates it as
some `Xₚ`, and `MEET` at `j = p` gives `Xₙ ∩ Xₘ = Xₚ ⊆ Xₖ`. -/
theorem meet_iff_interEq (P : ComputablePresentation V) (n m k : ℕ) :
    (∀ j, P.X j ⊆ P.X k ↔ (P.X j ⊆ P.X n ∧ P.X j ⊆ P.X m)) ↔ (P.X n ∩ P.X m = P.X k) := by
  constructor
  · intro h
    have hk : P.X k ⊆ P.X n ∩ P.X m :=
      Set.subset_inter ((h k).mp subset_rfl).1 ((h k).mp subset_rfl).2
    refine Set.Subset.antisymm ?_ hk
    have hmem : V.mem (P.X n ∩ P.X m) := V.inter_mem (P.mem_X n) (P.mem_X m) (P.mem_X k) hk
    obtain ⟨p, hp⟩ := P.surj hmem
    have hpk : P.X p ⊆ P.X k :=
      (h p).mpr (by rw [hp]; exact ⟨Set.inter_subset_left, Set.inter_subset_right⟩)
    exact hp ▸ hpk
  · intro h j
    rw [← h, Set.subset_inter_iff]

/-- **Exercise 7.13 (⇒) — every effectively given domain is an `INCL` relation.** Given a computable
presentation `P` of `V`, set `INCL(n, m) := Xₙ ⊆ Xₘ`. Reflexivity/transitivity are those of `⊆`; the
master code is `P.masterIdx` (`Xₙ ⊆ master`); the meet function is `P.inter`. `INCL`/`CONS` decidability
are `P.incl_computable`/`P.cons_computable`; `MEET` decidability is `meet_iff_interEq` ∘
`P.interEq_computable`. -/
def ofPresentation (P : ComputablePresentation V) : InclStructure where
  INCL n m := P.X n ⊆ P.X m
  meetIdx := P.inter
  topIdx := P.masterIdx
  incl_dec := P.incl_computable
  cons_dec :=
    RecDecidable.of_iff
      (fun t => by
        refine exists_congr fun k => ?_
        exact (Set.subset_inter_iff).symm)
      P.cons_computable
  meet_dec :=
    RecDecidable.of_iff
      (fun t => meet_iff_interEq P t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2)
      P.interEq_computable
  meetIdx_primrec := P.inter_primrec
  incl_refl := fun _ => subset_rfl
  incl_trans := fun h1 h2 => h1.trans h2
  topIdx_spec := by
    intro n
    show P.X n ⊆ P.X P.masterIdx
    rw [P.masterIdx_spec]
    exact V.sub_master (P.mem_X n)
  meetIdx_spec := by
    intro n m hcons j
    obtain ⟨k, h1, h2⟩ := hcons
    have hcons' : ∃ k, P.X k ⊆ P.X n ∩ P.X m := ⟨k, Set.subset_inter h1 h2⟩
    show P.X j ⊆ P.X (P.inter n m) ↔ _
    rw [P.inter_spec hcons', Set.subset_inter_iff]

@[simp] theorem ofPresentation_INCL (P : ComputablePresentation V) (n m : ℕ) :
    (ofPresentation P).INCL n m ↔ P.X n ⊆ P.X m := Iff.rfl

@[simp] theorem mem_ofPresentation_toNbhd (P : ComputablePresentation V) (j n : ℕ) :
    j ∈ (ofPresentation P).toNbhd n ↔ P.X j ⊆ P.X n := Iff.rfl

/-- For `S = ofPresentation P`, two hint neighbourhoods coincide iff the underlying neighbourhoods
do: `Sₙ = Sₘ ↔ Xₙ = Xₘ`. -/
theorem ofPresentation_toNbhd_eq_iff (P : ComputablePresentation V) (n m : ℕ) :
    (ofPresentation P).toNbhd n = (ofPresentation P).toNbhd m ↔ P.X n = P.X m := by
  rw [Set.Subset.antisymm_iff, (ofPresentation P).toNbhd_subset_iff,
    (ofPresentation P).toNbhd_subset_iff]
  show (P.X n ⊆ P.X m ∧ P.X m ⊆ P.X n) ↔ P.X n = P.X m
  exact (Set.Subset.antisymm_iff).symm

/-! ### Round-trip A: `INCL ↦ 𝒟 ↦ INCL` recovers `INCL` -/

/-- **Round-trip A.** Starting from an abstract `InclStructure I`, building the hint system and its
presentation, then reading off the integer inclusion relation recovers `I.INCL` exactly. -/
theorem ofPresentation_toPresentation_INCL (I : InclStructure) (n m : ℕ) :
    (ofPresentation I.toPresentation).INCL n m ↔ I.INCL n m := by
  show I.toNbhd n ⊆ I.toNbhd m ↔ I.INCL n m
  exact I.toNbhd_subset_iff

/-! ### Round-trip B: `toSystem (ofPresentation P) ≅ᴰ V`

Scott's "Is this essentially any effectively given system?" — the reconstructed system is
domain-isomorphic to the original. The finite-element correspondence is `Xₙ ↔ Sₙ` (inclusion-
preserving, since `Sₙ ⊆ Sₘ ↔ Xₙ ⊆ Xₘ`); we extend it to all elements (filters) via the mutually
inverse `reconElem`/`reconElemInv`, in the style of Exercise 1.20's `powerIso`. -/

/-- The reconstructed system `toSystem (ofPresentation P)` over tokens `ℕ`. -/
abbrev reconstruct (P : ComputablePresentation V) : NeighborhoodSystem ℕ :=
  (ofPresentation P).toSystem

/-- The element of the reconstructed system corresponding to `x ∈ |V|`: the filter
`{Sₙ ∣ Xₙ ∈ x}`. -/
def reconElem (P : ComputablePresentation V) (x : V.Element) : (reconstruct P).Element where
  mem Y := ∃ n, Y = (ofPresentation P).toNbhd n ∧ x.mem (P.X n)
  sub := by rintro Y ⟨n, rfl, _⟩; exact ⟨n, rfl⟩
  master_mem :=
    ⟨P.masterIdx, (ofPresentation P).toNbhd_top.symm, by rw [P.masterIdx_spec]; exact x.master_mem⟩
  inter_mem := by
    rintro X Y ⟨n, rfl, hxn⟩ ⟨m, rfl, hxm⟩
    have hmem : V.mem (P.X n ∩ P.X m) := x.sub (x.inter_mem hxn hxm)
    obtain ⟨q, hq⟩ := P.surj hmem
    refine ⟨q, ?_, ?_⟩
    · ext j
      rw [Set.mem_inter_iff, mem_ofPresentation_toNbhd, mem_ofPresentation_toNbhd,
        mem_ofPresentation_toNbhd, hq, Set.subset_inter_iff]
    · have : x.mem (P.X q) := by rw [hq]; exact x.inter_mem hxn hxm
      exact this
  up_mem := by
    rintro X Y ⟨n, rfl, hxn⟩ ⟨m, rfl⟩ hsub
    have hnm : P.X n ⊆ P.X m := (ofPresentation P).toNbhd_subset_iff.mp hsub
    exact ⟨m, rfl, x.up_mem hxn (P.mem_X m) hnm⟩

/-- The element of `|V|` corresponding to `y` in the reconstructed system: the filter
`{Xₙ ∣ Sₙ ∈ y}`. -/
def reconElemInv (P : ComputablePresentation V) (y : (reconstruct P).Element) : V.Element where
  mem W := ∃ n, W = P.X n ∧ y.mem ((ofPresentation P).toNbhd n)
  sub := by rintro W ⟨n, rfl, _⟩; exact P.mem_X n
  master_mem :=
    ⟨P.masterIdx, P.masterIdx_spec.symm, by
      rw [show (ofPresentation P).toNbhd P.masterIdx = Set.univ from (ofPresentation P).toNbhd_top]
      exact y.master_mem⟩
  inter_mem := by
    rintro X Y ⟨n, rfl, hyn⟩ ⟨m, rfl, hym⟩
    obtain ⟨p, hp⟩ := y.sub (y.inter_mem hyn hym)
    have hpmem : p ∈ (ofPresentation P).toNbhd n ∩ (ofPresentation P).toNbhd m :=
      hp ▸ ((ofPresentation P).mem_toNbhd.mpr ((ofPresentation P).incl_refl p))
    rw [Set.mem_inter_iff, mem_ofPresentation_toNbhd, mem_ofPresentation_toNbhd] at hpmem
    have hwit : P.X p ⊆ P.X n ∩ P.X m := Set.subset_inter hpmem.1 hpmem.2
    have hmem : V.mem (P.X n ∩ P.X m) := V.inter_mem (P.mem_X n) (P.mem_X m) (P.mem_X p) hwit
    obtain ⟨q, hq⟩ := P.surj hmem
    refine ⟨q, hq.symm, ?_⟩
    have htoNbhd : (ofPresentation P).toNbhd q
        = (ofPresentation P).toNbhd n ∩ (ofPresentation P).toNbhd m := by
      ext j
      rw [Set.mem_inter_iff, mem_ofPresentation_toNbhd, mem_ofPresentation_toNbhd,
        mem_ofPresentation_toNbhd, hq, Set.subset_inter_iff]
    rw [htoNbhd]
    exact y.inter_mem hyn hym
  up_mem := by
    rintro W Z ⟨n, rfl, hyn⟩ hZ hWZ
    obtain ⟨p, hp⟩ := P.surj hZ
    refine ⟨p, hp.symm, ?_⟩
    have hnp : (ofPresentation P).toNbhd n ⊆ (ofPresentation P).toNbhd p :=
      (ofPresentation P).toNbhd_subset_iff.mpr (by show P.X n ⊆ P.X p; rw [hp]; exact hWZ)
    exact y.up_mem hyn ⟨p, rfl⟩ hnp

/-- **Round-trip B (the isomorphism).** `reconElem`/`reconElemInv` are mutually inverse and preserve
and reflect the approximation order, giving `|V| ≃o |toSystem (ofPresentation P)|`. -/
def reconIso (P : ComputablePresentation V) : V.Element ≃o (reconstruct P).Element where
  toFun := reconElem P
  invFun := reconElemInv P
  left_inv := by
    intro x
    apply Element.ext
    intro W
    constructor
    · rintro ⟨n, rfl, m, hWm, hxm⟩
      rw [ofPresentation_toNbhd_eq_iff] at hWm
      rw [hWm]; exact hxm
    · intro hxW
      obtain ⟨n, hn⟩ := P.surj (x.sub hxW)
      exact ⟨n, hn.symm, n, rfl, by rw [hn]; exact hxW⟩
  right_inv := by
    intro y
    apply Element.ext
    intro T
    constructor
    · rintro ⟨n, rfl, m, hXm, hym⟩
      have : (ofPresentation P).toNbhd n = (ofPresentation P).toNbhd m :=
        (ofPresentation_toNbhd_eq_iff P n m).mpr hXm
      rw [this]; exact hym
    · intro hyT
      obtain ⟨n, hn⟩ := y.sub hyT
      exact ⟨n, hn, n, rfl, by rw [← hn]; exact hyT⟩
  map_rel_iff' := by
    intro x x'
    constructor
    · intro h W hxW
      obtain ⟨n, hn⟩ := P.surj (x.sub hxW)
      have hmem : (reconElem P x).mem ((ofPresentation P).toNbhd n) :=
        ⟨n, rfl, by rw [hn]; exact hxW⟩
      obtain ⟨m, hm, hx'm⟩ := h ((ofPresentation P).toNbhd n) hmem
      rw [ofPresentation_toNbhd_eq_iff] at hm
      rw [← hn, hm]; exact hx'm
    · intro h Y hY
      obtain ⟨n, rfl, hxn⟩ := hY
      exact ⟨n, rfl, h (P.X n) hxn⟩

/-- **Exercise 7.13 (⇒, "essentially any effectively given system").** The system reconstructed from
an effectively given `V` via its `INCL` relation is domain-isomorphic to `V`. -/
theorem reconstruct_isomorphic (P : ComputablePresentation V) : reconstruct P ≅ᴰ V :=
  ⟨(reconIso P).symm⟩

end Scott1980.Neighborhood.Exercise713

/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Recursive

/-!
# A choice-free Gödel numbering of `ℚ`, with primitive-recursive comparison/max/min

Theorem 8.8(b) (Scott 1981, PRG-19) needs `𝒰` (Definition 8.7) to have a genuine
`ComputablePresentation` (Definition 7.1). `𝒰`'s neighbourhoods are finite unions of rational
intervals `presentedIntervals L` for `L : List (ℚ × ℚ)`, so we first need `ℚ` itself — and hence
`List (ℚ × ℚ)` — coded by naturals, with the *arithmetic* operations `combineIntervals` actually
performs (`⊔`, `⊓`, `≤`, `=`) realized as genuinely `Nat.Primrec` functions on the codes.

## The encoding

An integer `z : ℤ` is coded as an (unnormalized) **difference pair** `Nat.pair z.toNat (-z).toNat`
— deliberately *not* a zig-zag bijection, since a difference pair turns every integer comparison
into a cross-*addition* of naturals (`a₁ - b₁ ≤ a₂ - b₂ ↔ a₁ + b₂ ≤ a₂ + b₁`), avoiding truncated
subtraction (and its case splits) entirely in the downstream `Nat.Primrec` proofs. A rational
`q : ℚ` is coded as `Nat.pair (encodeInt q.num) (q.den - 1)` (the `- 1`/`+ 1` shift keeps the
denominator positive without a separate side condition). Both round-trip **exactly** on every input
(`decodeInt_encodeInt`, `decodeRat_encodeRat`), not just on some "canonical" sub-class of codes —
mirroring `Recursive.lean`'s `decodeList_encodeList`/`encodeList_decodeList` exact round trips, and
for the same reason: it lets downstream code freely compose `encode ∘ decode` without tracking a
canonicality invariant.

`decodeRat`'s surjectivity (`decodeRat_surjective`) is what lets `𝒰`'s presentation enumerate *every*
rational, and `mkRat_self` (core Lean, choice-free) is the only fact about `Rat`'s internal
normalization we need.

## Primitive-recursive comparison arithmetic

`ratLeCode`/`ratLtCode`/`ratEqCode` decide `≤`/`</`/`=` between two rational codes by cross-clearing
denominators (again via addition, not subtraction, exactly as for `Int`); `ratMaxCode`/`ratMinCode`
select one of the two input codes via `Domain.Recursive.selectFn`, mirroring
`Domain.Recursive.primrec_max`'s pattern exactly. `zeroCode`/`oneCode` are fixed codes for the
constants `0, 1 : ℚ` used by `Definition87.lean`'s `clip`.

Everything here is `⊆ {propext, Quot.sound}` — no `Classical.choice` — since it is all direct
`Nat.Primrec` construction and finite case-splitting on `≤`/`<` (decidable, not classical, for `ℤ`
and `ℚ`).
-/

namespace Scott1980.Neighborhood

open Domain.Recursive

/-! ### Integers as difference-pairs of naturals -/

/-- Decode a natural code as an integer: `pair a b ↦ a - b`. -/
def decodeInt (c : ℕ) : ℤ := (c.unpair.1 : ℤ) - (c.unpair.2 : ℤ)

/-- Encode an integer as the difference-pair `(z.toNat, (-z).toNat)` (one of the two is always
`0`). -/
def encodeInt (z : ℤ) : ℕ := Nat.pair z.toNat (-z).toNat

/-- **Exact round trip**: `decodeInt (encodeInt z) = z` for *every* `z : ℤ`, not just a canonical
sub-class of codes. -/
@[simp] theorem decodeInt_encodeInt (z : ℤ) : decodeInt (encodeInt z) = z := by
  unfold decodeInt encodeInt
  rw [unpair_pair]
  by_cases h : 0 ≤ z
  · have hz : (z.toNat : ℤ) = z := Int.toNat_of_nonneg h
    have hnz : ((-z).toNat : ℤ) = 0 := by
      have := Int.toNat_of_nonpos (show -z ≤ 0 by omega); simp [this]
    rw [hz, hnz]; ring
  · have h' : z < 0 := by omega
    have hz : (z.toNat : ℤ) = 0 := by
      have := Int.toNat_of_nonpos (show z ≤ 0 from h'.le); simp [this]
    have hnz : ((-z).toNat : ℤ) = -z := Int.toNat_of_nonneg (by omega)
    rw [hz, hnz]; ring

/-! ### Rationals as (integer numerator code, denominator `- 1`) pairs -/

/-- Decode a natural code as a rational via `mkRat`: `pair c d ↦ mkRat (decodeInt c) (d + 1)`. -/
def decodeRat (c : ℕ) : ℚ := mkRat (decodeInt c.unpair.1) (c.unpair.2 + 1)

/-- Encode a rational `q` using its own reduced `num`/`den`. -/
def encodeRat (q : ℚ) : ℕ := Nat.pair (encodeInt q.num) (q.den - 1)

/-- **Exact round trip**: `decodeRat (encodeRat q) = q` for *every* `q : ℚ`, via `mkRat_self`. -/
@[simp] theorem decodeRat_encodeRat (q : ℚ) : decodeRat (encodeRat q) = q := by
  unfold decodeRat encodeRat
  rw [unpair_pair, decodeInt_encodeInt]
  have hden : q.den - 1 + 1 = q.den := by
    have := q.den_nz; omega
  rw [hden, Rat.mkRat_self]

/-- `decodeRat` is surjective: every rational number is `decodeRat` of some code (namely
`encodeRat q`). -/
theorem decodeRat_surjective : Function.Surjective decodeRat :=
  fun q => ⟨encodeRat q, decodeRat_encodeRat q⟩

/-! ### Primitive-recursive comparison of rational codes

`ratLeCode (pair c₁ c₂)` decides `decodeRat c₁ ≤ decodeRat c₂` by cross-clearing denominators:
writing `cᵢ` for `(aᵢ, bᵢ, dᵢ)` (so `decodeRat cᵢ = (aᵢ - bᵢ)/(dᵢ + 1)`), the comparison
`(a₁-b₁)/(d₁+1) ≤ (a₂-b₂)/(d₂+1)` (denominators positive) is equivalent, after moving every `bᵢ`
term to the other side to avoid subtraction, to `a₁(d₂+1) + b₂(d₁+1) ≤ a₂(d₁+1) + b₁(d₂+1)`. -/

/-- The numerator's positive part `a` of a rational code. -/
def qNumP (c : ℕ) : ℕ := c.unpair.1.unpair.1

/-- The numerator's negative part `b` of a rational code (so the numerator is `a - b`). -/
def qNumN (c : ℕ) : ℕ := c.unpair.1.unpair.2

/-- The denominator (`d + 1`, always positive) of a rational code. -/
def qDen (c : ℕ) : ℕ := c.unpair.2 + 1

theorem primrec_qNumP : Nat.Primrec qNumP := Nat.Primrec.left.comp Nat.Primrec.left
theorem primrec_qNumN : Nat.Primrec qNumN := Nat.Primrec.right.comp Nat.Primrec.left
theorem primrec_qDen : Nat.Primrec qDen :=
  Nat.Primrec.succ.comp Nat.Primrec.right

theorem qDen_pos (c : ℕ) : 0 < qDen c := Nat.succ_pos _

theorem decodeRat_eq (c : ℕ) :
    decodeRat c = mkRat ((qNumP c : ℤ) - (qNumN c : ℤ)) (qDen c) := by
  unfold decodeRat decodeInt qNumP qNumN qDen; rfl

/-- The `{0,1}`-valued cross-cleared comparison test `a₁·d₂ + b₂·d₁ ≤ a₂·d₁ + b₁·d₂`, applied to
`t = pair c₁ c₂`. -/
def ratLeCode (t : ℕ) : ℕ :=
  let c1 := t.unpair.1; let c2 := t.unpair.2
  isZero ((qNumP c1 * qDen c2 + qNumN c2 * qDen c1) -
    (qNumP c2 * qDen c1 + qNumN c1 * qDen c2))

theorem primrec_ratLeCode : Nat.Primrec ratLeCode := by
  have hc1 : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hc2 : Nat.Primrec (fun t : ℕ => t.unpair.2) := Nat.Primrec.right
  have hlhs : Nat.Primrec (fun t : ℕ =>
      qNumP t.unpair.1 * qDen t.unpair.2 + qNumN t.unpair.2 * qDen t.unpair.1) :=
    primrec_add₂ (primrec_mul₂ (primrec_qNumP.comp hc1) (primrec_qDen.comp hc2))
      (primrec_mul₂ (primrec_qNumN.comp hc2) (primrec_qDen.comp hc1))
  have hrhs : Nat.Primrec (fun t : ℕ =>
      qNumP t.unpair.2 * qDen t.unpair.1 + qNumN t.unpair.1 * qDen t.unpair.2) :=
    primrec_add₂ (primrec_mul₂ (primrec_qNumP.comp hc2) (primrec_qDen.comp hc1))
      (primrec_mul₂ (primrec_qNumN.comp hc1) (primrec_qDen.comp hc2))
  exact (primrec_isZero.comp (primrec_sub₂ hlhs hrhs)).of_eq fun t => by
    simp only [ratLeCode]

/-- **Correctness of `ratLeCode`**: it is `1` exactly when the decoded rationals compare `≤`. -/
theorem ratLeCode_eq_one_iff (c1 c2 : ℕ) :
    ratLeCode (Nat.pair c1 c2) = 1 ↔ decodeRat c1 ≤ decodeRat c2 := by
  unfold ratLeCode
  rw [unpair_pair_fst, unpair_pair_snd, isZero_eq_one_iff, Nat.sub_eq_zero_iff_le]
  rw [decodeRat_eq c1, decodeRat_eq c2, Rat.mkRat_eq_div, Rat.mkRat_eq_div,
    div_le_div_iff₀ (by exact_mod_cast qDen_pos c1) (by exact_mod_cast qDen_pos c2),
    ← Nat.cast_le (α := ℚ)]
  push_cast
  constructor <;> intro h <;> nlinarith [h]

theorem ratLeCode_le_one (t : ℕ) : ratLeCode t ≤ 1 := isZero_le_one _

/-- `ratLtCode (pair c₁ c₂)` decides `decodeRat c₁ < decodeRat c₂` via `¬ (decodeRat c₂ ≤ decodeRat c₁)`. -/
def ratLtCode (t : ℕ) : ℕ := 1 - ratLeCode (Nat.pair t.unpair.2 t.unpair.1)

theorem primrec_ratLtCode : Nat.Primrec ratLtCode :=
  primrec_sub₂ (Nat.Primrec.const 1)
    (primrec_ratLeCode.comp (Nat.Primrec.right.pair Nat.Primrec.left))

theorem ratLtCode_le_one (t : ℕ) : ratLtCode t ≤ 1 := by unfold ratLtCode; omega

theorem ratLtCode_eq_one_iff (c1 c2 : ℕ) :
    ratLtCode (Nat.pair c1 c2) = 1 ↔ decodeRat c1 < decodeRat c2 := by
  unfold ratLtCode
  rw [unpair_pair_fst, unpair_pair_snd]
  have h1 := ratLeCode_le_one (Nat.pair c2 c1)
  rw [show (1 : ℕ) - ratLeCode (Nat.pair c2 c1) = 1 ↔ ratLeCode (Nat.pair c2 c1) = 0 from by omega,
    show ratLeCode (Nat.pair c2 c1) = 0 ↔ ¬ ratLeCode (Nat.pair c2 c1) = 1 from by omega,
    ratLeCode_eq_one_iff, not_le]

/-- **`<` on rational codes is recursively decidable.** Packaged as `RecDecidable₂` (rather than the
raw `{0,1}` characteristic `ratLtCode`) so it composes directly with `Recursive.lean`'s closure
lemmas (`.not`, `.and`, `.bExistsList`, `.swap`, ...). -/
theorem ratLtCode_recDecidable₂ : RecDecidable₂ (fun c1 c2 => decodeRat c1 < decodeRat c2) := by
  refine RecDecidable₂.of_paired_zero_one_char primrec_ratLtCode
    (fun t => by have := ratLtCode_le_one t; omega) (fun n m => ?_)
  exact (ratLtCode_eq_one_iff n m).symm

/-! ### Max/min of rational codes, and constants -/

/-- `ratMaxCode (pair c₁ c₂)` selects whichever of `c₁, c₂` decodes to the larger rational. -/
def ratMaxCode (t : ℕ) : ℕ := selectFn (ratLeCode t) t.unpair.2 t.unpair.1

/-- `ratMinCode (pair c₁ c₂)` selects whichever of `c₁, c₂` decodes to the smaller rational. -/
def ratMinCode (t : ℕ) : ℕ := selectFn (ratLeCode t) t.unpair.1 t.unpair.2

theorem primrec_ratMaxCode : Nat.Primrec ratMaxCode :=
  primrec_selectFn primrec_ratLeCode Nat.Primrec.right Nat.Primrec.left

theorem primrec_ratMinCode : Nat.Primrec ratMinCode :=
  primrec_selectFn primrec_ratLeCode Nat.Primrec.left Nat.Primrec.right

theorem decodeRat_ratMaxCode (c1 c2 : ℕ) :
    decodeRat (ratMaxCode (Nat.pair c1 c2)) = max (decodeRat c1) (decodeRat c2) := by
  unfold ratMaxCode
  rw [unpair_pair_fst, unpair_pair_snd]
  by_cases h : decodeRat c1 ≤ decodeRat c2
  · rw [(ratLeCode_eq_one_iff c1 c2).mpr h, selectFn_one, max_eq_right h]
  · have hf : ratLeCode (Nat.pair c1 c2) ≠ 1 := fun he => h ((ratLeCode_eq_one_iff c1 c2).mp he)
    have hf0 : ratLeCode (Nat.pair c1 c2) = 0 := by
      have := ratLeCode_le_one (Nat.pair c1 c2); omega
    rw [hf0, selectFn_zero, max_eq_left ((not_le.mp h).le)]

theorem decodeRat_ratMinCode (c1 c2 : ℕ) :
    decodeRat (ratMinCode (Nat.pair c1 c2)) = min (decodeRat c1) (decodeRat c2) := by
  unfold ratMinCode
  rw [unpair_pair_fst, unpair_pair_snd]
  by_cases h : decodeRat c1 ≤ decodeRat c2
  · rw [(ratLeCode_eq_one_iff c1 c2).mpr h, selectFn_one, min_eq_left h]
  · have hf : ratLeCode (Nat.pair c1 c2) ≠ 1 := fun he => h ((ratLeCode_eq_one_iff c1 c2).mp he)
    have hf0 : ratLeCode (Nat.pair c1 c2) = 0 := by
      have := ratLeCode_le_one (Nat.pair c1 c2); omega
    rw [hf0, selectFn_zero, min_eq_right ((not_le.mp h).le)]

/-- A fixed code for the rational `0`. -/
def zeroCode : ℕ := Nat.pair (Nat.pair 0 0) 0

/-- A fixed code for the rational `1`. -/
def oneCode : ℕ := Nat.pair (Nat.pair 1 0) 0

@[simp] theorem decodeRat_zeroCode : decodeRat zeroCode = 0 := by
  rw [decodeRat_eq]; norm_num [zeroCode, qNumP, qNumN, qDen, unpair_pair]

@[simp] theorem decodeRat_oneCode : decodeRat oneCode = 1 := by
  rw [decodeRat_eq]; norm_num [oneCode, qNumP, qNumN, qDen, unpair_pair]

/-! ### The midpoint of two rational codes (needed for Theorem 8.8(b) Part 4's `splitU`)

`ratMidCode (pair c₁ c₂)` codes `(decodeRat c₁ + decodeRat c₂) / 2` **without performing any
division**: cross-clearing denominators as in `ratLeCode` turns the sum into a single fraction over
`d₁·d₂`, and halving a fraction is simply *doubling its denominator* (`n/d / 2 = n/(2d)`), so no
`gcd`/reduction step is ever needed — `decodeRat`'s own `mkRat` call normalizes the result. -/

/-- The midpoint code `(c₁+c₂)/2` of two rational codes, via denominator cross-clearing (as in
`ratLeCode`) for the sum, then doubling the denominator to halve. -/
def ratMidCode (t : ℕ) : ℕ :=
  let c1 := t.unpair.1; let c2 := t.unpair.2
  Nat.pair (Nat.pair (qNumP c1 * qDen c2 + qNumP c2 * qDen c1)
                      (qNumN c1 * qDen c2 + qNumN c2 * qDen c1))
    (2 * qDen c1 * qDen c2 - 1)

theorem primrec_ratMidCode : Nat.Primrec ratMidCode := by
  have hc1 : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hc2 : Nat.Primrec (fun t : ℕ => t.unpair.2) := Nat.Primrec.right
  have hnumP : Nat.Primrec (fun t : ℕ =>
      qNumP t.unpair.1 * qDen t.unpair.2 + qNumP t.unpair.2 * qDen t.unpair.1) :=
    primrec_add₂ (primrec_mul₂ (primrec_qNumP.comp hc1) (primrec_qDen.comp hc2))
      (primrec_mul₂ (primrec_qNumP.comp hc2) (primrec_qDen.comp hc1))
  have hnumN : Nat.Primrec (fun t : ℕ =>
      qNumN t.unpair.1 * qDen t.unpair.2 + qNumN t.unpair.2 * qDen t.unpair.1) :=
    primrec_add₂ (primrec_mul₂ (primrec_qNumN.comp hc1) (primrec_qDen.comp hc2))
      (primrec_mul₂ (primrec_qNumN.comp hc2) (primrec_qDen.comp hc1))
  have hden : Nat.Primrec (fun t : ℕ => 2 * qDen t.unpair.1 * qDen t.unpair.2 - 1) :=
    primrec_sub₂
      (primrec_mul₂ (primrec_mul₂ (Nat.Primrec.const 2) (primrec_qDen.comp hc1))
        (primrec_qDen.comp hc2))
      (Nat.Primrec.const 1)
  exact (Nat.Primrec.pair (Nat.Primrec.pair hnumP hnumN) hden).of_eq fun t => by
    simp only [ratMidCode]

theorem qDen_ratMidCode (c1 c2 : ℕ) : qDen (ratMidCode (Nat.pair c1 c2)) = qDen c1 * qDen c2 * 2 := by
  have h1 : 1 ≤ 2 * qDen c1 * qDen c2 := by
    have hd1 := qDen_pos c1
    have hd2 := qDen_pos c2
    have : 0 < 2 * qDen c1 * qDen c2 :=
      Nat.mul_pos (Nat.mul_pos (by norm_num) hd1) hd2
    omega
  show (ratMidCode (Nat.pair c1 c2)).unpair.2 + 1 = qDen c1 * qDen c2 * 2
  simp only [ratMidCode, unpair_pair_fst, unpair_pair_snd]
  rw [Nat.sub_add_cancel h1]; ring

/-- **Correctness of `ratMidCode`**: it decodes to the arithmetic mean of the two decoded
rationals. -/
theorem decodeRat_ratMidCode (c1 c2 : ℕ) :
    decodeRat (ratMidCode (Nat.pair c1 c2)) = (decodeRat c1 + decodeRat c2) / 2 := by
  have hqnp : qNumP (ratMidCode (Nat.pair c1 c2)) =
      qNumP c1 * qDen c2 + qNumP c2 * qDen c1 := by
    show (ratMidCode (Nat.pair c1 c2)).unpair.1.unpair.1 = _
    simp only [ratMidCode, unpair_pair_fst, unpair_pair_snd]
  have hqnn : qNumN (ratMidCode (Nat.pair c1 c2)) =
      qNumN c1 * qDen c2 + qNumN c2 * qDen c1 := by
    show (ratMidCode (Nat.pair c1 c2)).unpair.1.unpair.2 = _
    simp only [ratMidCode, unpair_pair_fst, unpair_pair_snd]
  rw [decodeRat_eq, hqnp, hqnn, qDen_ratMidCode, Rat.mkRat_eq_div,
    decodeRat_eq c1, decodeRat_eq c2, Rat.mkRat_eq_div, Rat.mkRat_eq_div]
  have hd1 : (qDen c1 : ℚ) ≠ 0 := by exact_mod_cast (qDen_pos c1).ne'
  have hd2 : (qDen c2 : ℚ) ≠ 0 := by exact_mod_cast (qDen_pos c2).ne'
  push_cast
  field_simp
  ring

/-- **`decodeRat_ratMidCode`, un-paired**: lets callers apply it to an arbitrary code `e`
(typically itself obtained by decoding a list, e.g. `firstElemCode`) without first having to
rewrite `e` as `Nat.pair e.unpair.1 e.unpair.2` in the ambient goal — doing that rewrite directly
on a term still containing `e` risks the `whnf`-blowup this project has hit before whenever `e`
is (or unfolds to) a large composite expression. -/
theorem decodeRat_ratMidCode' (e : ℕ) :
    decodeRat (ratMidCode e) = (decodeRat e.unpair.1 + decodeRat e.unpair.2) / 2 := by
  have h := decodeRat_ratMidCode e.unpair.1 e.unpair.2
  rwa [Nat.pair_unpair] at h

end Scott1980.Neighborhood

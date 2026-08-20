/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Definition71
import Scott1980.Neighborhood.Exercise722Decide

/-!
# Exercise 7.22 — computable presentation backbone (`SsysX`)

Enumeration `n ↦ SsysX n` for Scott's positive neighbourhood system `Ssys` (`Exercise722.lean`),
toward Definition 7.1 effective givenness. Indices decode to `SExpr` codes; non-empty denotations
are listed, while junk / empty-syntax indices map to the master neighbourhood `Σ` so every index
still names a member of `S` (`SsysX_mem`). Surjectivity onto `S` uses
`inS_iff_exists_denote` (`Exercise722Regular.lean`).

Sessions C9–C10 will add `RecDecidable₂` consistency and the `ComputablePresentation` structure;
relation (i) `interEq` remains deferred (see `Exercise722Decide.lean`, Session C7a).
-/

namespace Scott1980.Neighborhood

namespace Exercise722

open Set Domain.Recursive

/-! ## Gödel codes for `SExpr` -/

private def boolNat (b : Bool) : ℕ := if b then 1 else 0

theorem boolNat_eq_one_iff (b : Bool) : boolNat b = 1 ↔ b := by
  cases b <;> simp [boolNat]

theorem boolNat_zero_one (b : Bool) : boolNat b = 0 ∨ boolNat b = 1 := by
  cases b <;> simp [boolNat]

private def natBool (n : ℕ) : Option Bool :=
  match n with | 0 => some false | 1 => some true | _ => none

private def encodeListBool (σ : List Bool) : ℕ := encodeList (σ.map boolNat)

private def decodeListBool (n : ℕ) : Option (List Bool) :=
  (decodeList n).mapM natBool

private theorem decodeListBool_encodeListBool (σ : List Bool) :
    decodeListBool (encodeListBool σ) = some σ := by
  simp [decodeListBool, encodeListBool, decodeList_encodeList, List.mapM_map, List.map_map]
  induction σ with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp [boolNat, natBool, ih]

private theorem natBool_isSome_iff (n : ℕ) :
    (natBool n).isSome = true ↔ n = 0 ∨ n = 1 := by
  match n with
  | 0 => simp [natBool]
  | 1 => simp [natBool]
  | n + 2 => simp [natBool]

private theorem natBinDigit_of_natBool_some (n : ℕ) {b : Bool} (h : natBool n = some b) :
    n = 0 ∨ n = 1 := by
  match n with
  | 0 => simp [natBool] at h; exact Or.inl rfl
  | 1 => simp [natBool] at h; exact Or.inr rfl
  | n + 2 => simp [natBool] at h

private theorem mapM_natBool_isSome_iff (l : List ℕ) :
    (l.mapM natBool).isSome = true ↔ ∀ x ∈ l, x = 0 ∨ x = 1 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.mapM_cons]
    constructor
    · intro h
      cases hnx : natBool x with
      | none => simp [hnx] at h
      | some b =>
        cases htx : xs.mapM natBool with
        | none => simp [hnx, htx] at h
        | some ts =>
          have hxs' : (xs.mapM natBool).isSome = true := by simp [htx, h]
          intro y hy
          rcases List.mem_cons.mp hy with hEq | hyTail
          · rw [hEq]
            exact natBinDigit_of_natBool_some x hnx
          · exact ih.mp hxs' y hyTail
    · intro h
      have hx : (natBool x).isSome = true :=
        (natBool_isSome_iff x).2 (h x (List.mem_cons_self ..))
      have hxs : (xs.mapM natBool).isSome = true :=
        ih.mpr fun y hy => h y (List.mem_cons_of_mem x hy)
      cases hnx : natBool x with
      | none =>
        rcases h x (List.mem_cons_self ..) with h0 | h1
        · subst h0; simp [natBool] at hnx
        · subst h1; simp [natBool] at hnx
      | some b =>
        cases htx : xs.mapM natBool with
        | none => simp [htx] at hxs
        | some ts => simp [hnx, htx, hx, hxs]

/-- **7.22i(b)1(d):** list decode succeeds iff every coded entry is a binary digit. -/
theorem decodeListBool_isSome_iff (n : ℕ) :
    (decodeListBool n).isSome = true ↔ allBinDigitsChar n = 1 := by
  simp only [decodeListBool, mapM_natBool_isSome_iff, allBinDigitsChar_eq_one_iff]

/-- Subexpression depth (for fuelled decoding). -/
def sexprDepth : SExpr → ℕ
  | .sigma => 1
  | .single _ => 1
  | .cat a b => 1 + max (sexprDepth a) (sexprDepth b)
  | .cap a b => 1 + max (sexprDepth a) (sexprDepth b)

/-- Tag-based Gödel code for an `SExpr` (tags `0..3` for the four constructors). -/
def SExpr.encode : SExpr → ℕ
  | .sigma => Nat.pair 0 0
  | .single σ => Nat.pair 1 (encodeListBool σ)
  | .cat a b => Nat.pair 2 (Nat.pair (encode a) (encode b))
  | .cap a b => Nat.pair 3 (Nat.pair (encode a) (encode b))

/-- Fuelled decoder: `fuel` bounds recursive unfoldings. -/
def decodeFuel (fuel : ℕ) (n : ℕ) : Option SExpr :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match n.unpair.1 with
    | 0 => if n.unpair.2 = 0 then some .sigma else none
    | 1 => (decodeListBool n.unpair.2).map (.single ·)
    | 2 =>
      match decodeFuel fuel n.unpair.2.unpair.1, decodeFuel fuel n.unpair.2.unpair.2 with
      | some a, some b => some (.cat a b)
      | _, _ => none
    | 3 =>
      match decodeFuel fuel n.unpair.2.unpair.1, decodeFuel fuel n.unpair.2.unpair.2 with
      | some a, some b => some (.cap a b)
      | _, _ => none
    | _ => none

theorem decodeFuel_encode {fuel : ℕ} {e : SExpr} (h : sexprDepth e ≤ fuel) :
    decodeFuel fuel (SExpr.encode e) = some e := by
  induction e generalizing fuel with
  | sigma =>
    cases fuel with
    | zero => simp [sexprDepth] at h
    | succ fuel =>
      simp [decodeFuel, SExpr.encode, sexprDepth]
  | single σ =>
    cases fuel with
    | zero => simp [sexprDepth] at h
    | succ fuel =>
      simp [decodeFuel, SExpr.encode, decodeListBool_encodeListBool σ]
  | cat a b iha ihb =>
    cases fuel with
    | zero => simp [sexprDepth] at h
    | succ fuel =>
      have ha : sexprDepth a ≤ fuel := by
        simp only [sexprDepth] at h ⊢
        omega
      have hb : sexprDepth b ≤ fuel := by
        simp only [sexprDepth] at h ⊢
        omega
      simp [decodeFuel, SExpr.encode, iha ha, ihb hb]
  | cap a b iha ihb =>
    cases fuel with
    | zero => simp [sexprDepth] at h
    | succ fuel =>
      have ha : sexprDepth a ≤ fuel := by
        simp only [sexprDepth] at h ⊢
        omega
      have hb : sexprDepth b ≤ fuel := by
        simp only [sexprDepth] at h ⊢
        omega
      simp [decodeFuel, SExpr.encode, iha ha, ihb hb]

private theorem decodeFuel_succ_sigma (fuel c : ℕ) (h : c.unpair.1 = 0) (hσ : c.unpair.2 = 0) :
    decodeFuel (fuel + 1) c = some .sigma := by simp [decodeFuel, h, hσ]

private theorem decodeFuel_succ_not_sigma (fuel c : ℕ) (h : c.unpair.1 = 0) (hσ : c.unpair.2 ≠ 0) :
    decodeFuel (fuel + 1) c = none := by simp [decodeFuel, h, hσ]

private theorem decodeFuel_succ_single (fuel c : ℕ) (h : c.unpair.1 = 1) :
    decodeFuel (fuel + 1) c = (decodeListBool c.unpair.2).map (.single ·) := by
  simp [decodeFuel, h]

private theorem decodeFuel_succ_cat (fuel c : ℕ) (h : c.unpair.1 = 2) :
    decodeFuel (fuel + 1) c =
      match decodeFuel fuel c.unpair.2.unpair.1, decodeFuel fuel c.unpair.2.unpair.2 with
      | some a, some b => some (.cat a b)
      | _, _ => none := by simp [decodeFuel, h]

private theorem decodeFuel_succ_cap (fuel c : ℕ) (h : c.unpair.1 = 3) :
    decodeFuel (fuel + 1) c =
      match decodeFuel fuel c.unpair.2.unpair.1, decodeFuel fuel c.unpair.2.unpair.2 with
      | some a, some b => some (.cap a b)
      | _, _ => none := by simp [decodeFuel, h]

private theorem decodeFuel_succ_junk (fuel c : ℕ) (h : 4 ≤ c.unpair.1) :
    decodeFuel (fuel + 1) c = none := by
  match tag : c.unpair.1 with
  | 0 | 1 | 2 | 3 => omega
  | t + 4 => simp [decodeFuel, tag]

private theorem decodeFuel_pair_cat_isSome_iff (fuel c : ℕ) :
    (match decodeFuel fuel c.unpair.2.unpair.1, decodeFuel fuel c.unpair.2.unpair.2 with
      | some a, some b => some (SExpr.cat a b) | _, _ => none).isSome = true ↔
      (decodeFuel fuel c.unpair.2.unpair.1).isSome = true ∧
        (decodeFuel fuel c.unpair.2.unpair.2).isSome = true := by
  cases decodeFuel fuel c.unpair.2.unpair.1 <;> cases decodeFuel fuel c.unpair.2.unpair.2 <;> simp

private theorem decodeFuel_pair_cap_isSome_iff (fuel c : ℕ) :
    (match decodeFuel fuel c.unpair.2.unpair.1, decodeFuel fuel c.unpair.2.unpair.2 with
      | some a, some b => some (SExpr.cap a b) | _, _ => none).isSome = true ↔
      (decodeFuel fuel c.unpair.2.unpair.1).isSome = true ∧
        (decodeFuel fuel c.unpair.2.unpair.2).isSome = true := by
  cases decodeFuel fuel c.unpair.2.unpair.1 <;> cases decodeFuel fuel c.unpair.2.unpair.2 <;> simp

/-- **7.22i(b)1(e):** shallow link between fuel-bounded char decode and `decodeFuel`. -/
theorem decodeFuelOkChar_eq_one_iff (fuel c : ℕ) :
    decodeFuelOkChar fuel c = 1 ↔ (decodeFuel fuel c).isSome = true := by
  induction fuel generalizing c with
  | zero =>
    simp [decodeFuelOkChar, decodeFuel]
  | succ fuel ih =>
    simp only [decodeFuelOkChar]
    rw [decodeFuelOkCharBody_eq]
    match tag : c.unpair.1 with
    | 0 =>
      rw [show decodeFuel (fuel + 1) c = if c.unpair.2 = 0 then some .sigma else none from by
        by_cases hσ : c.unpair.2 = 0 <;> simp [decodeFuel, tag, hσ]]
      simp [selectFn_isOne_one_sub_sigma]
    | 1 =>
      rw [decodeFuel_succ_single fuel c tag]
      simp [decodeListBool_isSome_iff, Option.isSome_map]
    | 2 =>
      rw [decodeFuel_succ_cat fuel c tag, mulBit_eq_one_iff, decodeFuel_pair_cat_isSome_iff]
      have ih1 := ih c.unpair.2.unpair.1
      have ih2 := ih c.unpair.2.unpair.2
      constructor
      · intro ⟨h1, h2⟩
        exact ⟨ih1.mp h1, ih2.mp h2⟩
      · intro ⟨h1, h2⟩
        exact ⟨ih1.mpr h1, ih2.mpr h2⟩
    | 3 =>
      rw [decodeFuel_succ_cap fuel c tag, mulBit_eq_one_iff, decodeFuel_pair_cap_isSome_iff]
      have ih1 := ih c.unpair.2.unpair.1
      have ih2 := ih c.unpair.2.unpair.2
      constructor
      · intro ⟨h1, h2⟩
        exact ⟨ih1.mp h1, ih2.mp h2⟩
      · intro ⟨h1, h2⟩
        exact ⟨ih1.mpr h1, ih2.mpr h2⟩
    | t + 4 =>
      rw [decodeFuel_succ_junk fuel c (by omega)]
      simp [tag]

/-- Index for the enumeration: code plus depth (fuel for decoding). -/
def SExpr.index (e : SExpr) : ℕ := Nat.pair (encode e) (sexprDepth e)

/-- Decoder: `Nat.unpair n` supplies `(code, fuel)` with `fuel = sexprDepth e` on valid indices. -/
def SExpr.decode (n : ℕ) : Option SExpr := decodeFuel (n.unpair.2 + 1) n.unpair.1

theorem SExpr.decode_index (e : SExpr) : decode (index e) = some e := by
  simp [decode, index]
  exact decodeFuel_encode (Nat.le_succ (sexprDepth e))

/-! ## The enumeration `SsysX` -/

/-- Default neighbourhood for junk / empty-syntax indices: the master `Σ = Set.univ`. -/
private def SsysX_default : Set (List Bool) := Set.univ

/-- **Definition 7.1 enumeration backbone.** Decode `n` to an `SExpr`; if the denotation is
non-empty (`decideNonemptyB`), use it; otherwise (or on junk codes) use `Σ` so every index names a
member of the positive system `S`. -/
def SsysX (n : ℕ) : Set (List Bool) :=
  match SExpr.decode n with
  | none => SsysX_default
  | some e =>
    if decideNonemptyB e then denote e else SsysX_default

theorem SsysX_mem (n : ℕ) : InS (SsysX n) := by
  unfold SsysX
  cases hdec : SExpr.decode n with
  | none => simp; exact InS.univ
  | some e =>
    by_cases h : decideNonemptyB e = true
    · simp [h]
      exact InS_denote_of_nonempty ((decideNonemptyB_iff e).1 h)
    · simp [h]
      exact InS.univ

theorem SsysX_surj {Y : Set (List Bool)} (hY : InS Y) : ∃ n, SsysX n = Y := by
  obtain ⟨e, he, hne⟩ := inS_iff_exists_denote.mp hY
  refine ⟨SExpr.index e, ?_⟩
  unfold SsysX
  rw [SExpr.decode_index e]
  have hne' : (denote e).Nonempty := he ▸ hne
  have hb : decideNonemptyB e = true := (decideNonemptyB_iff e).2 hne'
  simp [hb, he]

/-! ## Definition 7.1 (ii) — recursively decidable consistency (Session C9)

Scott's consistency `∃ k, X_k ⊆ X_n ∩ X_m` on a positive system is equivalent to
`(X_n ∩ X_m).Nonempty` (`Ssys_isPositive`). On the `SsysX` enumeration, inactive indices
(decode failure / empty denotation → `SsysX = Σ`) make consistency automatic; active-active
pairs reduce to `consistentB` on decoded expressions. -/

/-- Inactive index: decode fails or denotes the empty language (mapped to `Σ` in `SsysX`). -/
def ssysActive (n : ℕ) : Bool :=
  match SExpr.decode n with
  | none => false
  | some e => decideNonemptyB e

/-- Canonical representative for `SsysX n` as a fragment expression (junk → `Σ`). -/
def safeDecodeActive (n : ℕ) : SExpr :=
  match SExpr.decode n with
  | none => .sigma
  | some e => if decideNonemptyB e then e else .sigma

theorem SsysX_eq_denote_safe (n : ℕ) : SsysX n = denote (safeDecodeActive n) := by
  unfold SsysX safeDecodeActive
  cases hdec : SExpr.decode n with
  | none => simp [hdec, denote_sigma, SsysX_default]
  | some e =>
    by_cases hb : decideNonemptyB e = true
    · simp [hdec, hb]
    · simp [hdec, hb, denote_sigma, SsysX_default]

theorem ssys_inter_nonempty_iff_consistent (n m : ℕ) :
    (SsysX n ∩ SsysX m).Nonempty ↔ consistentB (safeDecodeActive n) (safeDecodeActive m) = true := by
  rw [SsysX_eq_denote_safe, SsysX_eq_denote_safe, ← denote_cap, consistentB_iff]

theorem ssys_cons_positivity (n m : ℕ) :
    (∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) ↔ (SsysX n ∩ SsysX m).Nonempty := by
  constructor
  · intro ⟨k, hk⟩
    exact Set.Nonempty.mono hk (InS.nonempty (SsysX_mem k))
  · intro hne
    have hIn : InS (SsysX n ∩ SsysX m) :=
      (Ssys_isPositive (Ssys_mem.mpr (SsysX_mem n)) (Ssys_mem.mpr (SsysX_mem m))).2 hne
    obtain ⟨k, hk⟩ := SsysX_surj hIn
    exact ⟨k, hk.subset⟩

theorem ssys_cons_iff (n m : ℕ) :
    (∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) ↔
      consistentB (safeDecodeActive n) (safeDecodeActive m) = true := by
  rw [ssys_cons_positivity, ssys_inter_nonempty_iff_consistent]

/-- `{0,1}` consistency decider on index pairs (active-active uses `consistentB`). -/
def ssysConsistentB (n m : ℕ) : Bool :=
  if !ssysActive n || !ssysActive m then true
  else
    match SExpr.decode n, SExpr.decode m with
    | some a, some b => consistentB a b
    | _, _ => true

theorem safeDecodeActive_inactive (n : ℕ) (h : ssysActive n = false) : safeDecodeActive n = .sigma := by
  dsimp only [ssysActive, safeDecodeActive] at h ⊢
  cases hdec : SExpr.decode n with
  | none => rfl
  | some e =>
    by_cases hb : decideNonemptyB e
    · exfalso
      simp [hdec, hb] at h
    · simp [hdec, hb]

theorem safeDecodeActive_nonempty (n : ℕ) : (denote (safeDecodeActive n)).Nonempty := by
  unfold safeDecodeActive
  cases hdec : SExpr.decode n with
  | none => exact Set.univ_nonempty
  | some e =>
    by_cases hb : decideNonemptyB e = true
    · have hne : (denote e).Nonempty := (decideNonemptyB_iff e).1 hb
      simpa [hdec, hb] using hne
    · simpa [hdec, hb, denote_sigma] using Set.univ_nonempty

theorem consistentB_sigma_safe (m : ℕ) : consistentB .sigma (safeDecodeActive m) = true := by
  rw [consistentB_iff, denote_cap, denote_sigma, Set.univ_inter]
  exact safeDecodeActive_nonempty m

theorem consistentB_safe_sigma (n : ℕ) : consistentB (safeDecodeActive n) .sigma = true := by
  rw [consistentB_iff, denote_cap, denote_sigma, Set.inter_univ]
  exact safeDecodeActive_nonempty n

theorem ssysConsistentB_iff (n m : ℕ) :
    ssysConsistentB n m = true ↔
      consistentB (safeDecodeActive n) (safeDecodeActive m) = true := by
  by_cases hn : ssysActive n
  · by_cases hm : ssysActive m
    · cases hdecn : SExpr.decode n with
      | none => exfalso; simp [ssysActive, hdecn] at hn
      | some a =>
        cases hdecm : SExpr.decode m with
        | none => exfalso; simp [ssysActive, hdecm] at hm
        | some b =>
          have ha : decideNonemptyB a := by simpa [ssysActive, hdecn] using hn
          have hb : decideNonemptyB b := by simpa [ssysActive, hdecm] using hm
          have hsa : safeDecodeActive n = a := by simp [safeDecodeActive, hdecn, ha]
          have hsb : safeDecodeActive m = b := by simp [safeDecodeActive, hdecm, hb]
          constructor
          · intro h
            rw [hsa, hsb]
            have heq : ssysConsistentB n m = consistentB a b := by
              unfold ssysConsistentB
              simp [hn, hm, hdecn, hdecm]
            rw [heq] at h
            exact h
          · intro hcons
            rw [hsa, hsb] at hcons
            have heq : ssysConsistentB n m = consistentB a b := by
              unfold ssysConsistentB
              simp [hn, hm, hdecn, hdecm]
            rw [heq]
            exact hcons
    · have hm' : ssysActive m = false := by simpa using hm
      constructor
      · intro _; rw [safeDecodeActive_inactive m hm', consistentB_safe_sigma n]
      · intro _; unfold ssysConsistentB; simp [hn, hm']
  · have hn' : ssysActive n = false := by simpa using hn
    constructor
    · intro _; rw [safeDecodeActive_inactive n hn', consistentB_sigma_safe m]
    · intro _; unfold ssysConsistentB; simp [hn']

theorem ssys_cons_char_iff (n m : ℕ) :
    ssysConsistentB n m = true ↔ ∃ k, SsysX k ⊆ SsysX n ∩ SsysX m := by
  rw [ssysConsistentB_iff, ssys_cons_iff]

/-- Scott's consistency relation (Definition 7.1 (ii)) on the `SsysX` indices is decidable via
`ssysConsistentB` (choice-free on the `Bool` side; see axiom audit of `decideNonemptyB_iff`). -/
instance decidableSsysCons (n m : ℕ) :
    Decidable (∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) :=
  decidable_of_iff (ssysConsistentB n m = true) (ssys_cons_char_iff n m)

/-! ### Session C9 — `RecDecidable₂` (primitive-recursive bridge)

The mathematics is finished (`ssys_cons_char_iff`). The generic packaging lemma is
`RecDecidable₂.of_paired_zero_one_char` in `Recursive.lean`: once a `{0,1}`-valued characteristic is
`Nat.Primrec`, `RecDecidable₂` follows immediately.

**Numeric characteristic** for the existing Bool decider (no new algorithm).

Unfolding `ssys_cons_char_iff` (which chains through `ssys_cons_iff` / `consistentB_iff`) can exceed
the default 200000 heartbeat budget; raise the limit for this section only. -/

set_option maxHeartbeats 5000000

/-- `{0,1}` packaging of `ssysConsistentB` on `Nat.pair`-coded index pairs. -/
def ssysConsChar (t : ℕ) : ℕ := boolNat (ssysConsistentB t.unpair.1 t.unpair.2)

theorem ssysConsChar_eq_one_iff (t : ℕ) :
    ssysConsChar t = 1 ↔ ssysConsistentB t.unpair.1 t.unpair.2 = true := by
  simp [ssysConsChar, boolNat_eq_one_iff]

theorem ssysConsChar_zero_one (t : ℕ) : ssysConsChar t = 0 ∨ ssysConsChar t = 1 :=
  boolNat_zero_one _

theorem ssys_cons_char_eq_one_iff (n m : ℕ) :
    (∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) ↔ ssysConsChar (Nat.pair n m) = 1 := by
  rw [ssysConsChar_eq_one_iff, ssys_cons_char_iff, unpair_pair_fst, unpair_pair_snd]

/-- **Conditional C9 closure.** Instantiated once the sole missing primitive-recursive link below
is proved. -/
theorem Ssys_cons_computable_of_primrec_ssysConsChar (hf : Nat.Primrec ssysConsChar) :
    RecDecidable₂ (fun n m => ∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) :=
  RecDecidable₂.of_paired_zero_one_char hf ssysConsChar_zero_one ssys_cons_char_eq_one_iff

/-! ### Session C9b7 — `ssysActiveChar`, `ssysConsistentBChar`

`Recursive.lean` cannot import this file (it would cycle: `Presentation → Definition71 →
Recursive`), so its C9b5/C9b6 Gödel mirror (`c9b5_sexprGodelEncode`/`c9b5_sexprDepth`) is a
self-contained *structural* copy of `SExpr.encode`/`sexprDepth` above, not literally the same
function. The bridge equalities below (provable here, downstream, where both sides are visible)
let every C9b5/C9b6 correctness theorem be re-applied against the *real* `SExpr.encode`/
`sexprDepth`/`denote`, without re-deriving any of their induction. -/

theorem c9b5_boolNat_eq (b : Bool) : Domain.Recursive.c9b5_boolNat b = boolNat b := by
  cases b <;> rfl

theorem c9b5_encodeListBool_eq (σ : List Bool) :
    Domain.Recursive.c9b5_encodeListBool σ = encodeListBool σ := by
  unfold Domain.Recursive.c9b5_encodeListBool encodeListBool
  congr 1

theorem c9b5_sexprDepth_eq (e : SExpr) : Domain.Recursive.c9b5_sexprDepth e = sexprDepth e := by
  induction e with
  | sigma => rfl
  | single _ => rfl
  | cat a b iha ihb => simp [Domain.Recursive.c9b5_sexprDepth, sexprDepth, iha, ihb]
  | cap a b iha ihb => simp [Domain.Recursive.c9b5_sexprDepth, sexprDepth, iha, ihb]

theorem c9b5_sexprGodelEncode_eq (e : SExpr) :
    Domain.Recursive.c9b5_sexprGodelEncode e = SExpr.encode e := by
  induction e with
  | sigma => rfl
  | single σ => simp [Domain.Recursive.c9b5_sexprGodelEncode, SExpr.encode, c9b5_encodeListBool_eq]
  | cat a b iha ihb => simp [Domain.Recursive.c9b5_sexprGodelEncode, SExpr.encode, iha, ihb]
  | cap a b iha ihb => simp [Domain.Recursive.c9b5_sexprGodelEncode, SExpr.encode, iha, ihb]

/-! #### Decode soundness: `decodeFuel` recovers exactly the canonical encoding, within fuel

Needed to instantiate C9b5/C9b6's `_eq_one_iff` theorems (stated at `c9b5_sexprGodelEncode e` /
`c9b5_sexprDepth e ≤ fuel`) against a code `n.unpair.1` that merely *decodes* to some `e` under
`SExpr.decode` — not one already known to equal `SExpr.encode e` syntactically. -/

private theorem natBool_eq_some_iff (n : ℕ) (b : Bool) : natBool n = some b ↔ n = boolNat b := by
  match n with
  | 0 => cases b <;> simp [natBool, boolNat]
  | 1 => cases b <;> simp [natBool, boolNat]
  | n + 2 => cases b <;> simp [natBool, boolNat]

private theorem mapM_natBool_eq_some (l : List ℕ) (σ : List Bool)
    (h : l.mapM natBool = some σ) : l = σ.map boolNat := by
  induction l generalizing σ with
  | nil => rw [List.mapM_nil] at h; simpa using h.symm
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    cases hnx : natBool x with
    | none => simp [hnx] at h
    | some b =>
      cases htx : xs.mapM natBool with
      | none => simp [hnx, htx] at h
      | some ys =>
        simp only [hnx, htx] at h
        obtain rfl : σ = b :: ys := by simpa using h.symm
        simp [ih ys htx, (natBool_eq_some_iff x b).mp hnx]

private theorem decodeListBool_eq_some (n : ℕ) (σ : List Bool) (h : decodeListBool n = some σ) :
    n = encodeListBool σ := by
  have hl : decodeList n = σ.map boolNat := mapM_natBool_eq_some (decodeList n) σ h
  calc n = encodeList (decodeList n) := (encodeList_decodeList n).symm
    _ = encodeList (σ.map boolNat) := by rw [hl]
    _ = encodeListBool σ := rfl

/-- **Soundness:** any code `c` that `decodeFuel` accepts is the canonical `SExpr.encode` of the
recovered expression (`decodeList`/`decodeListBool`/`Nat.pair` are all injective in the relevant
direction, so nothing "junk" can decode). -/
theorem decodeFuel_sound {fuel c : ℕ} {e : SExpr} (h : decodeFuel fuel c = some e) :
    c = SExpr.encode e := by
  induction fuel generalizing c e with
  | zero => simp [decodeFuel] at h
  | succ fuel ih =>
    match tag : c.unpair.1 with
    | 0 =>
      by_cases hσ : c.unpair.2 = 0
      · have hc : c = Nat.pair 0 0 := by
          have hpu := Nat.pair_unpair c; rw [tag, hσ] at hpu; exact hpu.symm
        rw [decodeFuel_succ_sigma fuel c tag hσ] at h
        simp only [Option.some.injEq] at h
        simp [SExpr.encode, ← h, hc]
      · rw [decodeFuel_succ_not_sigma fuel c tag hσ] at h; simp at h
    | 1 =>
      have hc1 : c = Nat.pair 1 c.unpair.2 := by
        have hpu := Nat.pair_unpair c; rw [tag] at hpu; exact hpu.symm
      rw [decodeFuel_succ_single fuel c tag] at h
      cases hb : decodeListBool c.unpair.2 with
      | none => simp [hb] at h
      | some σ =>
        rw [hb] at h
        simp only [Option.map_some, Option.some.injEq] at h
        have hσc : c.unpair.2 = encodeListBool σ := decodeListBool_eq_some c.unpair.2 σ hb
        rw [← h, SExpr.encode, hc1, hσc]
    | 2 =>
      have hc2 : c = Nat.pair 2 c.unpair.2 := by
        have hpu := Nat.pair_unpair c; rw [tag] at hpu; exact hpu.symm
      rw [decodeFuel_succ_cat fuel c tag] at h
      cases ha : decodeFuel fuel c.unpair.2.unpair.1 with
      | none => simp [ha] at h
      | some a =>
        cases hb : decodeFuel fuel c.unpair.2.unpair.2 with
        | none => simp [ha, hb] at h
        | some b =>
          simp only [ha, hb, Option.some.injEq] at h
          have hac : c.unpair.2.unpair.1 = SExpr.encode a := ih ha
          have hbc : c.unpair.2.unpair.2 = SExpr.encode b := ih hb
          have hpc : c.unpair.2 = Nat.pair (SExpr.encode a) (SExpr.encode b) := by
            have hpu := Nat.pair_unpair c.unpair.2; rw [hac, hbc] at hpu; exact hpu.symm
          rw [← h, SExpr.encode, hc2, hpc]
    | 3 =>
      have hc3 : c = Nat.pair 3 c.unpair.2 := by
        have hpu := Nat.pair_unpair c; rw [tag] at hpu; exact hpu.symm
      rw [decodeFuel_succ_cap fuel c tag] at h
      cases ha : decodeFuel fuel c.unpair.2.unpair.1 with
      | none => simp [ha] at h
      | some a =>
        cases hb : decodeFuel fuel c.unpair.2.unpair.2 with
        | none => simp [ha, hb] at h
        | some b =>
          simp only [ha, hb, Option.some.injEq] at h
          have hac : c.unpair.2.unpair.1 = SExpr.encode a := ih ha
          have hbc : c.unpair.2.unpair.2 = SExpr.encode b := ih hb
          have hpc : c.unpair.2 = Nat.pair (SExpr.encode a) (SExpr.encode b) := by
            have hpu := Nat.pair_unpair c.unpair.2; rw [hac, hbc] at hpu; exact hpu.symm
          rw [← h, SExpr.encode, hc3, hpc]
    | _ + 4 =>
      rw [decodeFuel_succ_junk fuel c (by omega)] at h; simp at h

/-- **Fuel sufficiency:** the recovered expression never needs more depth than the fuel it was
decoded with. -/
theorem decodeFuel_depth_le {fuel c : ℕ} {e : SExpr} (h : decodeFuel fuel c = some e) :
    sexprDepth e ≤ fuel := by
  induction fuel generalizing c e with
  | zero => simp [decodeFuel] at h
  | succ fuel ih =>
    match tag : c.unpair.1 with
    | 0 =>
      by_cases hσ : c.unpair.2 = 0
      · rw [decodeFuel_succ_sigma fuel c tag hσ] at h
        simp only [Option.some.injEq] at h
        simp [← h, sexprDepth]
      · rw [decodeFuel_succ_not_sigma fuel c tag hσ] at h; simp at h
    | 1 =>
      rw [decodeFuel_succ_single fuel c tag] at h
      cases hb : decodeListBool c.unpair.2 with
      | none => simp [hb] at h
      | some σ =>
        rw [hb] at h
        simp only [Option.map_some, Option.some.injEq] at h
        simp [← h, sexprDepth]
    | 2 =>
      rw [decodeFuel_succ_cat fuel c tag] at h
      cases ha : decodeFuel fuel c.unpair.2.unpair.1 with
      | none => simp [ha] at h
      | some a =>
        cases hb : decodeFuel fuel c.unpair.2.unpair.2 with
        | none => simp [ha, hb] at h
        | some b =>
          simp only [ha, hb, Option.some.injEq] at h
          have hda := ih ha
          have hdb := ih hb
          simp only [← h, sexprDepth]
          omega
    | 3 =>
      rw [decodeFuel_succ_cap fuel c tag] at h
      cases ha : decodeFuel fuel c.unpair.2.unpair.1 with
      | none => simp [ha] at h
      | some a =>
        cases hb : decodeFuel fuel c.unpair.2.unpair.2 with
        | none => simp [ha, hb] at h
        | some b =>
          simp only [ha, hb, Option.some.injEq] at h
          have hda := ih ha
          have hdb := ih hb
          simp only [← h, sexprDepth]
          omega
    | _ + 4 =>
      rw [decodeFuel_succ_junk fuel c (by omega)] at h; simp at h

/-- `{0,1}` packaging of `ssysActive` via `decodeFuelOkChar` (C9b1) + `decideNonemptyBChar`
(C9b6), operating purely on the Gödel code `n.unpair.1` with fuel `n.unpair.2 + 1` (mirroring
`SExpr.decode`). -/
def ssysActiveChar (n : ℕ) : ℕ :=
  mulBit (decodeFuelOkChar (n.unpair.2 + 1) n.unpair.1)
    (decideNonemptyBChar (n.unpair.2 + 1) n.unpair.1)

theorem ssysActiveChar_le_one (n : ℕ) : ssysActiveChar n ≤ 1 :=
  mulBit_le_one (decodeFuelOkChar_le_one _ _) (bExistsFn_le_one _ _ _)

theorem ssysActiveChar_eq_one_iff (n : ℕ) : ssysActiveChar n = 1 ↔ ssysActive n = true := by
  simp only [ssysActiveChar, ssysActive, SExpr.decode, mulBit_eq_one_iff,
    decodeFuelOkChar_eq_one_iff]
  cases hdec : decodeFuel (n.unpair.2 + 1) n.unpair.1 with
  | none => simp [hdec]
  | some e =>
    have hc : n.unpair.1 = SExpr.encode e := decodeFuel_sound hdec
    have hdepth : Domain.Recursive.c9b5_sexprDepth e ≤ n.unpair.2 + 1 := by
      rw [c9b5_sexprDepth_eq]; exact decodeFuel_depth_le hdec
    simp only [Option.isSome_some, true_and]
    rw [hc, ← c9b5_sexprGodelEncode_eq, decideNonemptyBChar_eq_one_iff hdepth, decideNonemptyB_iff]

/-- `{0,1}` packaging of `ssysConsistentB`: inactive-either defaults to `1` (consistent), while
active-active reduces to `consistentBChar` (C9b6). Fuel `n.unpair.2 + m.unpair.2 + 2` is generous
enough for the `.cap` of both decoded expressions regardless of which side is deeper. -/
def ssysConsistentBChar (n m : ℕ) : ℕ :=
  selectFn (mulBit (ssysActiveChar n) (ssysActiveChar m))
    (consistentBChar (n.unpair.2 + m.unpair.2 + 2) n.unpair.1 m.unpair.1)
    1

private theorem ssysActive_exists_decode {n : ℕ} (hn : ssysActive n = true) :
    ∃ e, SExpr.decode n = some e := by
  unfold ssysActive at hn
  cases hdec : SExpr.decode n with
  | none => simp [hdec] at hn
  | some e => exact ⟨e, rfl⟩

theorem ssysConsistentBChar_eq_one_iff (n m : ℕ) :
    ssysConsistentBChar n m = 1 ↔ ssysConsistentB n m = true := by
  unfold ssysConsistentBChar ssysConsistentB
  by_cases hn : ssysActive n = true
  · by_cases hm : ssysActive m = true
    · have hnc : ssysActiveChar n = 1 := (ssysActiveChar_eq_one_iff n).mpr hn
      have hmc : ssysActiveChar m = 1 := (ssysActiveChar_eq_one_iff m).mpr hm
      obtain ⟨a, hdecn⟩ := ssysActive_exists_decode hn
      obtain ⟨b, hdecm⟩ := ssysActive_exists_decode hm
      have hac : n.unpair.1 = SExpr.encode a := decodeFuel_sound hdecn
      have hbc : m.unpair.1 = SExpr.encode b := decodeFuel_sound hdecm
      have hda : sexprDepth a ≤ n.unpair.2 + 1 := decodeFuel_depth_le hdecn
      have hdb : sexprDepth b ≤ m.unpair.2 + 1 := decodeFuel_depth_le hdecm
      have hfuel : Domain.Recursive.c9b5_sexprDepth (.cap a b) ≤ n.unpair.2 + m.unpair.2 + 2 := by
        rw [c9b5_sexprDepth_eq]
        simp only [sexprDepth]
        omega
      simp only [hnc, hmc, mulBit, mul_one, selectFn_one]
      rw [hac, hbc, ← c9b5_sexprGodelEncode_eq, ← c9b5_sexprGodelEncode_eq,
        consistentBChar_eq_one_iff hfuel]
      have hnotinactive : (!ssysActive n || !ssysActive m) = false := by simp [hn, hm]
      rw [hnotinactive, if_neg (by decide)]
      simp only [hdecn, hdecm]
      exact (consistentB_iff a b).symm
    · have hm0 : ssysActiveChar m = 0 := by
        have hle := ssysActiveChar_le_one m
        have hne : ssysActiveChar m ≠ 1 := fun h => hm ((ssysActiveChar_eq_one_iff m).mp h)
        omega
      have hmf : ssysActive m = false := by
        cases hAm : ssysActive m with
        | false => rfl
        | true => exact absurd hAm hm
      simp only [hm0, mulBit, mul_zero, selectFn_zero, hmf, Bool.not_false, Bool.or_true, if_true]
  · have hn0 : ssysActiveChar n = 0 := by
      have hle := ssysActiveChar_le_one n
      have hne : ssysActiveChar n ≠ 1 := fun h => hn ((ssysActiveChar_eq_one_iff n).mp h)
      omega
    have hnf : ssysActive n = false := by
      cases hAn : ssysActive n with
      | false => rfl
      | true => exact absurd hAn hn
    simp only [hn0, mulBit, zero_mul, selectFn_zero, hnf, Bool.not_false, Bool.true_or, if_true]

/-! ### Session C9b8 — closing the `C9b` umbrella

`decodeFuelOkChar`/`autStateCardFuelChar`/`matchesBChar`/`decideNonemptyBChar`/`consistentBChar`
are jointly primitive recursive in `(fuel, code)` (see `Recursive.lean`'s course-of-values
sections), so `ssysActiveChar`/`ssysConsistentBChar` compose directly, with no further new
infrastructure needed here. -/

theorem primrec_ssysActiveChar : Nat.Primrec ssysActiveChar := by
  have hpack : Nat.Primrec (fun n : ℕ => Nat.pair (n.unpair.2 + 1) n.unpair.1) :=
    Nat.Primrec.pair (primrec_add₂ Nat.Primrec.right (Nat.Primrec.const 1)) Nat.Primrec.left
  have h1 : Nat.Primrec (fun n => decodeFuelOkChar (n.unpair.2 + 1) n.unpair.1) :=
    (primrec_decodeFuelOkChar2.comp hpack).of_eq fun n => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have h2 : Nat.Primrec (fun n => decideNonemptyBChar (n.unpair.2 + 1) n.unpair.1) :=
    (primrec_decideNonemptyBChar2.comp hpack).of_eq fun n => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_mulBit.comp (Nat.Primrec.pair h1 h2)).of_eq fun n => by
    simp only [unpair_pair_fst, unpair_pair_snd, ssysActiveChar]

theorem primrec_ssysConsistentBChar :
    Nat.Primrec (fun t => ssysConsistentBChar t.unpair.1 t.unpair.2) := by
  have hcond : Nat.Primrec
      (fun t => mulBit (ssysActiveChar t.unpair.1) (ssysActiveChar t.unpair.2)) :=
    (primrec_mulBit.comp (Nat.Primrec.pair (primrec_ssysActiveChar.comp Nat.Primrec.left)
      (primrec_ssysActiveChar.comp Nat.Primrec.right))).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  have hfuel : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.2 + t.unpair.2.unpair.2 + 2) :=
    primrec_add₂ (primrec_add₂ (Nat.Primrec.right.comp Nat.Primrec.left)
      (Nat.Primrec.right.comp Nat.Primrec.right)) (Nat.Primrec.const 2)
  have hpack : Nat.Primrec (fun t : ℕ => Nat.pair (t.unpair.1.unpair.2 + t.unpair.2.unpair.2 + 2)
      (Nat.pair t.unpair.1.unpair.1 t.unpair.2.unpair.1)) :=
    Nat.Primrec.pair hfuel (Nat.Primrec.pair (Nat.Primrec.left.comp Nat.Primrec.left)
      (Nat.Primrec.left.comp Nat.Primrec.right))
  have hcons : Nat.Primrec (fun t => consistentBChar
      (t.unpair.1.unpair.2 + t.unpair.2.unpair.2 + 2) t.unpair.1.unpair.1 t.unpair.2.unpair.1) :=
    (primrec_consistentBChar2.comp hpack).of_eq fun t => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_selectFn hcond hcons (Nat.Primrec.const 1)).of_eq fun t => by
    simp only [ssysConsistentBChar]

theorem ssysConsistentBChar_le_one (n m : ℕ) : ssysConsistentBChar n m ≤ 1 := by
  unfold ssysConsistentBChar
  rcases (show mulBit (ssysActiveChar n) (ssysActiveChar m) = 0 ∨
      mulBit (ssysActiveChar n) (ssysActiveChar m) = 1 by
    have h1 := ssysActiveChar_le_one n
    have h2 := ssysActiveChar_le_one m
    unfold mulBit
    rcases (show ssysActiveChar n = 0 ∨ ssysActiveChar n = 1 by omega) with hn | hn <;>
      rcases (show ssysActiveChar m = 0 ∨ ssysActiveChar m = 1 by omega) with hm | hm <;>
      simp [hn, hm]) with h0 | h1
  · rw [h0, selectFn_zero]
  · rw [h1, selectFn_one]; exact consistentBChar_le_one _ _ _

theorem ssysConsChar_le_one (t : ℕ) : ssysConsChar t ≤ 1 := by
  have := boolNat_zero_one (ssysConsistentB t.unpair.1 t.unpair.2)
  unfold ssysConsChar
  omega

theorem ssysConsChar_eq_ssysConsistentBChar (t : ℕ) :
    ssysConsChar t = ssysConsistentBChar t.unpair.1 t.unpair.2 := by
  apply eq_of_le_one_iff_one (ssysConsChar_le_one t) (ssysConsistentBChar_le_one _ _)
  rw [ssysConsChar_eq_one_iff, ssysConsistentBChar_eq_one_iff]

/-- **7.22i(b)8 / closes the C9b umbrella.** -/
theorem primrec_ssysConsChar : Nat.Primrec ssysConsChar :=
  (primrec_ssysConsistentBChar).of_eq fun t => (ssysConsChar_eq_ssysConsistentBChar t).symm

/-- **Definition 7.1 (ii) is recursively decidable** (Exercise 7.22, closing C9). -/
theorem Ssys_cons_computable : RecDecidable₂ (fun n m => ∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) :=
  Ssys_cons_computable_of_primrec_ssysConsChar primrec_ssysConsChar

/-! ### Session C7b — `ssysInterEqChar` (Exercise 7.22k)

Definition 7.1 relation (i) — `SsysX n ∩ SsysX m = SsysX k` — via the `Exercise722Equiv.lean` /
`Recursive.lean` language-equivalence decider `interEqChar`. `safeDecodeActive` already gives a
uniform canonical `SExpr` representative for every index (junk/inactive ↦ `.sigma`,
`SsysX_eq_denote_safe`), so unlike `ssysConsistentBChar` (where inactive indices are *trivially*
consistent with anything, since `Σ` is the top element) there is no active/inactive case split
here: equality is genuinely about the canonical representative in every case. -/

/-- The Gödel code of `safeDecodeActive n` (`ssysCanonicalCode_eq`): `n`'s own decoded code if
active, else the code of `.sigma` (matching `safeDecodeActive`'s junk fallback). -/
@[irreducible] def ssysCanonicalCode (n : ℕ) : ℕ :=
  Domain.Recursive.selectFn (ssysActiveChar n) n.unpair.1 (SExpr.encode .sigma)

theorem ssysCanonicalCode_eq (n : ℕ) : ssysCanonicalCode n = SExpr.encode (safeDecodeActive n) := by
  unfold ssysCanonicalCode
  by_cases hn : ssysActive n = true
  · rw [(ssysActiveChar_eq_one_iff n).mpr hn, Domain.Recursive.selectFn_one]
    obtain ⟨e, hdec⟩ := ssysActive_exists_decode hn
    have hac : n.unpair.1 = SExpr.encode e := decodeFuel_sound hdec
    rw [hac]
    congr 1
    unfold safeDecodeActive
    rw [hdec]
    have : decideNonemptyB e = true := by
      unfold ssysActive at hn; rw [hdec] at hn; exact hn
    simp [this]
  · have hn0 : ssysActiveChar n = 0 := by
      have hle := ssysActiveChar_le_one n
      have hne : ssysActiveChar n ≠ 1 := fun h => hn ((ssysActiveChar_eq_one_iff n).mp h)
      omega
    have hnf : ssysActive n = false := by
      cases hAn : ssysActive n with
      | false => rfl
      | true => exact absurd hAn hn
    rw [hn0, Domain.Recursive.selectFn_zero, safeDecodeActive_inactive n hnf]

theorem sexprDepth_safeDecodeActive_le (n : ℕ) : sexprDepth (safeDecodeActive n) ≤ n.unpair.2 + 1 := by
  by_cases hn : ssysActive n = true
  · obtain ⟨e, hdec⟩ := ssysActive_exists_decode hn
    have hda : sexprDepth e ≤ n.unpair.2 + 1 := decodeFuel_depth_le hdec
    have heq : safeDecodeActive n = e := by
      unfold safeDecodeActive
      rw [hdec]
      have : decideNonemptyB e = true := by
        unfold ssysActive at hn; rw [hdec] at hn; exact hn
      simp [this]
    rw [heq]; exact hda
  · have hnf : ssysActive n = false := by
      cases hAn : ssysActive n with
      | false => rfl
      | true => exact absurd hAn hn
    rw [safeDecodeActive_inactive n hnf]
    simp [sexprDepth]

theorem ssys_interEq_iff (n m k : ℕ) :
    SsysX n ∩ SsysX m = SsysX k ↔
      denote (.cap (safeDecodeActive n) (safeDecodeActive m)) = denote (safeDecodeActive k) := by
  rw [SsysX_eq_denote_safe, SsysX_eq_denote_safe, SsysX_eq_denote_safe, denote_cap]

/-- **Exercise 7.22k.** `{0,1}` decider for Definition 7.1 relation (i) on `SsysX` indices,
`Nat.pair`-coded as `pair n (pair m k)`. -/
def ssysInterEqChar (t : ℕ) : ℕ :=
  let n := t.unpair.1
  let m := t.unpair.2.unpair.1
  let k := t.unpair.2.unpair.2
  Domain.Recursive.interEqChar (n.unpair.2 + m.unpair.2 + k.unpair.2 + 3)
    (Domain.Recursive.capCode (ssysCanonicalCode n) (ssysCanonicalCode m)) (ssysCanonicalCode k)

theorem ssysInterEqChar_le_one (t : ℕ) : ssysInterEqChar t ≤ 1 := by
  unfold ssysInterEqChar
  exact Domain.Recursive.interEqChar_le_one _ _ _

theorem ssysInterEqChar_eq_one_iff (n m k : ℕ) :
    ssysInterEqChar (Nat.pair n (Nat.pair m k)) = 1 ↔ SsysX n ∩ SsysX m = SsysX k := by
  unfold ssysInterEqChar
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [ssys_interEq_iff]
  have hfuel : n.unpair.2 + m.unpair.2 + k.unpair.2 + 3 ≥
      c9b5_sexprDepth (.cap (safeDecodeActive n) (safeDecodeActive m)) ∧
      n.unpair.2 + m.unpair.2 + k.unpair.2 + 3 ≥ c9b5_sexprDepth (safeDecodeActive k) := by
    rw [c9b5_sexprDepth_eq, c9b5_sexprDepth_eq]
    have hn := sexprDepth_safeDecodeActive_le n
    have hm := sexprDepth_safeDecodeActive_le m
    have hk := sexprDepth_safeDecodeActive_le k
    simp only [sexprDepth]
    omega
  rw [show Domain.Recursive.capCode (ssysCanonicalCode n) (ssysCanonicalCode m) =
      c9b5_sexprGodelEncode (.cap (safeDecodeActive n) (safeDecodeActive m)) from ?_,
    show ssysCanonicalCode k = c9b5_sexprGodelEncode (safeDecodeActive k) from ?_,
    Domain.Recursive.interEqChar_eq_one_iff hfuel.1 hfuel.2]
  · rw [c9b5_sexprGodelEncode_eq]; exact ssysCanonicalCode_eq k
  · unfold Domain.Recursive.capCode
    rw [ssysCanonicalCode_eq, ssysCanonicalCode_eq, ← c9b5_sexprGodelEncode_eq,
      ← c9b5_sexprGodelEncode_eq]
    rfl

theorem primrec_ssysInterEqChar : Nat.Primrec ssysInterEqChar := by
  have hn : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hk : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hcanon : Nat.Primrec (fun n : ℕ => ssysCanonicalCode n) := by
    have := primrec_ssysActiveChar
    refine (Domain.Recursive.primrec_selectFn this Nat.Primrec.left
      (Nat.Primrec.const (SExpr.encode .sigma))).of_eq fun n => ?_
    unfold ssysCanonicalCode; rfl
  have hcn : Nat.Primrec (fun t : ℕ => ssysCanonicalCode t.unpair.1) := hcanon.comp hn
  have hcm : Nat.Primrec (fun t : ℕ => ssysCanonicalCode t.unpair.2.unpair.1) := hcanon.comp hm
  have hck : Nat.Primrec (fun t : ℕ => ssysCanonicalCode t.unpair.2.unpair.2) := hcanon.comp hk
  have hfuel : Nat.Primrec (fun t : ℕ =>
      t.unpair.1.unpair.2 + t.unpair.2.unpair.1.unpair.2 + t.unpair.2.unpair.2.unpair.2 + 3) :=
    Domain.Recursive.primrec_add₂
      (Domain.Recursive.primrec_add₂
        (Domain.Recursive.primrec_add₂
          (Nat.Primrec.right.comp hn) (Nat.Primrec.right.comp hm))
        (Nat.Primrec.right.comp hk))
      (Nat.Primrec.const 3)
  have hcap : Nat.Primrec (fun t : ℕ =>
      Domain.Recursive.capCode (ssysCanonicalCode t.unpair.1)
        (ssysCanonicalCode t.unpair.2.unpair.1)) := by
    have hp : Nat.Primrec (fun t : ℕ => Nat.pair 3 (Nat.pair (ssysCanonicalCode t.unpair.1)
        (ssysCanonicalCode t.unpair.2.unpair.1))) :=
      Nat.Primrec.pair (Nat.Primrec.const 3) (Nat.Primrec.pair hcn hcm)
    refine hp.of_eq fun t => ?_
    unfold Domain.Recursive.capCode; rfl
  have hpack : Nat.Primrec (fun t : ℕ => Nat.pair
      (t.unpair.1.unpair.2 + t.unpair.2.unpair.1.unpair.2 + t.unpair.2.unpair.2.unpair.2 + 3)
      (Nat.pair (Domain.Recursive.capCode (ssysCanonicalCode t.unpair.1)
          (ssysCanonicalCode t.unpair.2.unpair.1))
        (ssysCanonicalCode t.unpair.2.unpair.2))) :=
    Nat.Primrec.pair hfuel (Nat.Primrec.pair hcap hck)
  refine (Domain.Recursive.primrec_interEqChar.comp hpack).of_eq fun t => ?_
  unfold ssysInterEqChar
  simp only [unpair_pair_fst, unpair_pair_snd]

/-- **Exercise 7.22k.** Definition 7.1 relation (i) is recursively decidable for `Ssys`. -/
theorem Ssys_interEq_computable :
    RecDecidable₃ (fun n m k => SsysX n ∩ SsysX m = SsysX k) :=
  RecDecidable₃.of_triple_zero_one_char primrec_ssysInterEqChar
    (fun t => by
      rcases (show ssysInterEqChar t = 0 ∨ ssysInterEqChar t = 1 from by
        have := ssysInterEqChar_le_one t; omega) with h | h <;> simp [h])
    (fun n m k => (ssysInterEqChar_eq_one_iff n m k).symm)

/-! ### Session C10 — Definition 7.1 packaging for `Ssys` (Exercise 7.22j)

**Historical note (superseded by C7b / 7.22k, kept for the record).** At the time this session ran,
relation (i) — `Xₙ ∩ Xₘ = X_k`, i.e. whether two *different* syntactic caps denote the *same*
language — was open: strictly harder than emptiness/consistency, since the fragment
`{sigma, single, cat, cap}` is not closed under complement, so `consistentB`/`decideNonemptyB`
(which only ever test emptiness) cannot expose language inequality (concrete obstruction:
`sigma_ne_containsZero`, see `Exercise722Decide.lean`). So `Ssys` got a **partial** presentation
carrying only what was proved then: the enumeration onto `S` (`SsysX`/`SsysX_mem`/`SsysX_surj`)
plus relation (ii) (`Ssys_cons_computable`).

**Session C7b since closed relation (i)** (`Ssys_interEq_computable`, below) via a choice-free
`Finset`-subset-construction automaton simulation (`Exercise722Equiv.lean`) — so `Ssys` now
satisfies **all of Definition 7.1 exactly as Scott states it** (enumeration, plus both relations
recursively decidable), between `SsysPres`/`Ssys_partially_effectively_given` here and
`Ssys_interEq_computable` in the C7b section. What is *not* provided is an instance of this
codebase's stronger `ComputablePresentation` (`Definition71.lean`) — used throughout the rest of
Lecture VII's formalisation (Theorem 7.4–7.6, Exercise 7.13–7.18, Proposition 7.7/7.10) — which
additionally carries a primitive-recursive intersection witness `inter`/`inter_primrec`/
`inter_spec` and a `masterIdx`. Those two fields are not part of Definition 7.1's text and are not
asked for by Exercise 7.22; completing them would be mechanical (7.22k's `ssysCanonicalCode`/
`capCode` already compute the right index) and is worth doing only if a later exercise wants to
feed `Ssys` into that shared apparatus. -/

/-- Definition 7.1 restricted to relation (ii) only (no `interEq_computable`, unlike
`ComputablePresentation`/`ScottPresentation` in `Definition71.lean`/`Exercise715.lean`, whose
pattern this mirrors). -/
structure ConsistencyPresentation (V : NeighborhoodSystem α) where
  /-- The enumeration `𝒟 = {Xₙ ∣ n ∈ ℕ}`. -/
  X : ℕ → Set α
  /-- Every `Xₙ` is a neighbourhood. -/
  mem_X : ∀ n, V.mem (X n)
  /-- The enumeration is onto `𝒟`. -/
  surj : ∀ {Y : Set α}, V.mem Y → ∃ n, X n = Y
  /-- **7.1(ii)** — consistency `∃ k. X_k ⊆ Xₙ ∩ Xₘ` is recursively decidable in `n, m`. -/
  cons_computable : RecDecidable₂ (fun n m => ∃ k, X k ⊆ X n ∩ X m)

/-- A neighbourhood system is *partially* effectively given when it admits a presentation
carrying relation (ii) (but not necessarily (i)). Named at top level (not `NeighborhoodSystem.…`)
since `Definition71.lean` — where `NeighborhoodSystem`/`ComputablePresentation` live — is outside
this session's edit scope; a future session may hoist `ConsistencyPresentation` there alongside
them for dot-notation parity with `IsEffectivelyGiven`. -/
def IsPartiallyEffectivelyGiven (V : NeighborhoodSystem α) : Prop :=
  Nonempty (ConsistencyPresentation V)

/-- The partial presentation of `Ssys`: enumeration `SsysX` onto `S`, consistency via
`Ssys_cons_computable`. -/
def SsysPres : ConsistencyPresentation Ssys where
  X := SsysX
  mem_X n := Ssys_mem.mpr (SsysX_mem n)
  surj hY := SsysX_surj (Ssys_mem.mp hY)
  cons_computable := Ssys_cons_computable

/-- **Exercise 7.22j.** `Ssys` — Scott's positive system generated by singleton languages under
concatenation and consistent intersection — is partially effectively given: Definition 7.1
relation (ii) is recursively decidable (`Ssys_cons_computable`, closing C9 / **7.22i(b)**).

The name "partially" now undersells the full picture: relation (i) is *also* proven, separately,
as `Ssys_interEq_computable` (Exercise 7.22k, `ConsistencyPresentation` was never extended with an
`interEq_computable` field to absorb it). Together, `SsysPres` and `Ssys_interEq_computable` show
`Ssys` satisfies Definition 7.1 **exactly as Scott states it** — enumeration, plus both relations
recursively decidable — with nothing deferred. What remains unbuilt is only this codebase's
*stronger* `ComputablePresentation` (`Definition71.lean`), which the rest of Lecture VII's
formalisation relies on but which is not part of Definition 7.1's text; see the section docstring
above. -/
theorem Ssys_partially_effectively_given : IsPartiallyEffectivelyGiven Ssys := ⟨SsysPres⟩

end Exercise722

end Scott1980.Neighborhood

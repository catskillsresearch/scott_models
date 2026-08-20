/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/scott1980
-/

import Scott1980.Neighborhood.Theorem88f

/-!
# Theorem 8.8(b), strengthened — a *direct* computable projection pair `D ⇄ U`

`theorem_8_8_b` (`Theorem88g.lean`) gives, for an effectively given `D`, an isomorphic copy
`D' : NeighborhoodSystem ℚ` (`= DprimeUCode P`) with a *literal* subsystem relation `D' ◁ U` whose
Proposition 6.12 projection pair (`h.inj`/`h.proj`) is computable — but it stops there, leaving
`D ≅ᴰ D'` a bare `Nonempty (OrderIso …)` fact, with no computable projection pair `D ⇄ U` for `D`
*itself*. Definition 8.9 needs exactly that (fixed projection pairs `𝒰+𝒰 → 𝒰`, `𝒰×𝒰 → 𝒰`,
`𝒰→𝒰 → 𝒰` and back), so this file supplies it.

## Why the iso is computable after all

`Theorem 2.7` (`ApproximableMap.ofIso`, `Approximable.lean`) turns *any* order-isomorphism
`e : D.Element ≃o D'.Element` into an approximable map, choice-free. Applied to `domainIsoCode P`
this gives `isoInj P : D → D''`/`isoProj P : D'' → D` (`D'' := DprimeUCode P`) with the projection-pair laws
as plain equalities (Theorem 2.7 + `ext_of_toElementMap`, mirroring `Exercise618.lean`'s
`jmap_comp_imap`).

The point of this file is that `isoInj`/`isoProj` are **also computable**, because `domainIsoCode` is built
(`Theorem88e.lean`) to match `D`'s and `D''`'s raw indices *literally* along the primitive-recursive
involution `eIdx P` (`Theorem88b.lean`): unfolding `ofIso`/`toDprimeUCode`/`toDCode` and using the
raw-index correspondence `embed_eq_iff_raw_code` (`e P i = e P j ↔ Yc P i = Yc P j`) collapses both
relations to a single reindexed `incl_computable` query —

* `isoInj_rel_iff_incl`: `(isoInj P).rel (P.X a) (Yc P b) ↔ P.X a ⊆ P.X (eIdx P b)`;
* `isoProj_rel_iff_incl`: `(isoProj P).rel (Yc P b) (P.X a) ↔ Yc P b ⊆ Yc P (eIdx P a)`

(using that `n := b`, resp. `m := eIdx P a`, is already the "same-index" witness the general
existential ranges over — no other witness can give a different answer, by `embed_eq_iff_raw_code`).
Composing `isoInj`/`isoProj` with `(DprimeUCode_subsystem P).inj`/`.proj` (computable, `Theorem88f.lean`) via
`comp_isComputable` then gives the headline `theorem_8_8_b_strong`: a *single* computable projection
pair `D ⇄ U`, no intermediate `D'` in sight.

The reasoning in this file is itself **choice-free**: `isoInj`/`isoProj` are built relationally
(`ofIso`), and all the analysis is `Exists`-elimination into `Prop` goals or plain rewriting. But
`theorem_8_8_b_strong` (like `theorem_8_8_b`/`DprimeUCode_subsystem`/`YseqCode` themselves) audits
`⊆ {propext, Classical.choice, Quot.sound}` — this is **inherited**, not new taint: `U`
(`Definition87.lean`) already audits with `Classical.choice` (Mathlib's `Rat` order instance path),
and everything downstream that mentions `U`/`UComputablePresentation` inherits it (confirmed
directly: `U_isEffectivelyGiven`, `DprimeUCode_subsystem`, `YseqCode` all show the same footprint).
-/

namespace Scott1980.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-! ## `isoInj`, `isoProj`: the code-level iso `D ≅ᴰ DprimeUCode P` as approximable maps -/

/-- **`isoInj : D → D''`**, Theorem 2.7 applied to `domainIsoCode P`. -/
noncomputable def isoInj : ApproximableMap D (DprimeUCode P) := ofIso (domainIsoCode P)

/-- **`isoProj : D'' → D`**, Theorem 2.7 applied to the inverse iso. -/
noncomputable def isoProj : ApproximableMap (DprimeUCode P) D := ofIso (domainIsoCode P).symm

/-- `isoProj ∘ isoInj = I_D` (Theorem 2.7's `toElementMap_ofIso`, both ways, plus `OrderIso.symm_apply_apply`). -/
theorem isoProj_comp_isoInj : (isoProj P).comp (isoInj P) = idMap D := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp]
  show (isoProj P).toElementMap ((isoInj P).toElementMap x) = _
  rw [isoInj, isoProj, toElementMap_ofIso, toElementMap_ofIso, OrderIso.symm_apply_apply,
    toElementMap_idMap]

/-- `isoInj ∘ isoProj = I_D''`. -/
theorem isoInj_comp_isoProj : (isoInj P).comp (isoProj P) = idMap (DprimeUCode P) := by
  apply ext_of_toElementMap
  intro y
  rw [toElementMap_comp]
  show (isoInj P).toElementMap ((isoProj P).toElementMap y) = _
  rw [isoInj, isoProj, toElementMap_ofIso, toElementMap_ofIso, OrderIso.apply_symm_apply,
    toElementMap_idMap]

/-! ## Reducing `isoInj.rel`/`isoProj.rel` to raw-index inclusion tests -/

/-- **`isoInj`'s relation at raw indices reduces to a single reindexed inclusion.** `n := b` is always
a valid witness (`Yc P b = Yc P b`), and any *other* witness `n` with `Yc P b = Yc P n` forces
`e P b = e P n` (`embed_eq_iff_raw_code`), so it gives no new information. -/
theorem isoInj_rel_iff_incl {a b : ℕ} :
    (isoInj P).rel (P.X a) (Yc P b) ↔ P.X a ⊆ P.X (eIdx P b) := by
  show (∃ _ : D.mem (P.X a), (toDprimeUCode P (D.principal (P.mem_X a))).mem (Yc P b)) ↔ _
  simp only [toDprimeUCode, mem_principal]
  have hb : e P b = P.X (eIdx P b) := rfl
  constructor
  · rintro ⟨-, n, hn, -, hsub⟩
    rwa [← hb, (embed_eq_iff_raw_code P b n).mpr hn]
  · intro hsub
    exact ⟨P.mem_X a, b, rfl, (P0 P).mem_X b, hb ▸ hsub⟩

/-- **`isoProj`'s relation at raw indices reduces to a single reindexed inclusion.** `m := eIdx P a`
is always a valid witness (`e P (eIdx P a) = P.X a` by involutivity), and any *other* witness `m`
with `P.X a = e P m` forces `Yc P (eIdx P a) = Yc P m` (via `embed_eq_iff_raw_code` and
`eIdx_involutive`), so it gives no new information. -/
theorem isoProj_rel_iff_incl {b a : ℕ} :
    (isoProj P).rel (Yc P b) (P.X a) ↔ Yc P b ⊆ Yc P (eIdx P a) := by
  show (∃ _ : (DprimeUCode P).mem (Yc P b),
      (toDCode P ((DprimeUCode P).principal ⟨b, rfl⟩)).mem (P.X a)) ↔ _
  simp only [toDCode, mem_principal]
  have hea : e P (eIdx P a) = P.X a := by
    show P.X (eIdx P (eIdx P a)) = P.X a
    rw [eIdx_involutive P a]
  constructor
  · rintro ⟨-, m, hm, -, hsub⟩
    have heq : e P (eIdx P a) = e P m := hea.trans hm
    rw [(embed_eq_iff_raw_code P (eIdx P a) m).mp heq]
    exact hsub
  · intro hsub
    exact ⟨⟨b, rfl⟩, eIdx P a, hea.symm, ⟨eIdx P a, rfl⟩, hsub⟩

/-! ## Computability of `isoInj`, `isoProj` -/

/-- **`isoInj` is computable** relative to `P`/`DprimeUCodePresentation P`: its raw-index relation is
`incl_computable` reindexed by the primitive-recursive `eIdx P` in the second argument. -/
theorem isoInj_isComputableMap : IsComputableMap P (DprimeUCodePresentation P) (isoInj P) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 (eIdx P t.unpair.2)) :=
    Nat.Primrec.pair Nat.Primrec.left ((eIdx_primrec P).comp Nat.Primrec.right)
  have hp : RecDecidable (fun t : ℕ => P.X t.unpair.1 ⊆ P.X (eIdx P t.unpair.2)) := by
    refine RecDecidable.of_iff (fun t => ?_) (P.incl_computable.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
  refine REPred.of_iff (fun t => ?_) hp.re
  show (isoInj P).rel (P.X t.unpair.1) ((DprimeUCodePresentation P).X t.unpair.2) ↔ _
  exact isoInj_rel_iff_incl P

/-- **`isoProj` is computable** relative to `DprimeUCodePresentation P`/`P`: its raw-index relation is
`DprimeUCodePresentation`'s `incl_computable` reindexed by `eIdx P` in the second argument. -/
theorem isoProj_isComputableMap : IsComputableMap (DprimeUCodePresentation P) P (isoProj P) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair t.unpair.1 (eIdx P t.unpair.2)) :=
    Nat.Primrec.pair Nat.Primrec.left ((eIdx_primrec P).comp Nat.Primrec.right)
  have hp : RecDecidable (fun t : ℕ => Yc P t.unpair.1 ⊆ Yc P (eIdx P t.unpair.2)) := by
    refine RecDecidable.of_iff (fun t => ?_) ((DprimeUCodePresentation P).incl_computable.comp hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
    rfl
  refine REPred.of_iff (fun t => ?_) hp.re
  show (isoProj P).rel ((DprimeUCodePresentation P).X t.unpair.1) (P.X t.unpair.2) ↔ _
  exact isoProj_rel_iff_incl P

/-! ## Assembly: a direct computable projection pair `D ⇄ U` -/

/-- **`theorem_8_8_b`, strengthened.** For any effectively given `D` (via `P`), there is a
*single* computable projection pair `i : D → U`, `j : U → D` directly (no intermediate isomorphic
copy): compose `isoInj`/`isoProj` (the code-level iso, computable) with `DprimeUCode`'s own projection pair
into `U` (Theorem 8.8(b)(vii), computable). -/
theorem theorem_8_8_b_strong :
    ∃ (i : ApproximableMap D U) (j : ApproximableMap U D),
      j.comp i = idMap D ∧ i.comp j ≤ idMap U ∧
        IsComputableMap P UComputablePresentation i ∧
        IsComputableMap UComputablePresentation P j := by
  set h := DprimeUCode_subsystem P with hh
  refine ⟨h.inj.comp (isoInj P), (isoProj P).comp h.proj, ?_, ?_, ?_, ?_⟩
  · rw [comp_assoc, ← comp_assoc h.proj h.inj (isoInj P), h.proj_comp_inj, idMap_comp]
    exact isoProj_comp_isoInj P
  · have heq : (h.inj.comp (isoInj P)).comp ((isoProj P).comp h.proj) = h.inj.comp h.proj := by
      rw [comp_assoc, ← comp_assoc (isoInj P) (isoProj P) h.proj, isoInj_comp_isoProj, idMap_comp]
    rw [heq]
    exact h.inj_comp_proj_le
  · exact comp_isComputable (isoInj_isComputableMap P) (DprimeUCode_inj_isComputableMap P)
  · exact comp_isComputable (DprimeUCode_proj_isComputableMap P) (isoProj_isComputableMap P)

end Scott1980.Neighborhood

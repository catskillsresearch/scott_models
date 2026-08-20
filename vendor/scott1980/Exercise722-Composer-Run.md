# Exercise 7.22 — Composer Autorun (single @ file)

> **Framing (2026-07-01):** Scott's Exercise 7.22 is **formalized**, and the inventory is
> **complete** (`arxiv.md` rows **7.22a–h**, **7.22i(a)–(b)8**, **7.22j**, **7.22k**, **7.22l** all
> Pass). Only an optional extension remains: upgrading `Ssys_partially_effectively_given` to a full
> `ComputablePresentation` (`inter`/`inter_primrec`/`inter_spec`/`masterIdx`).
>
> **You (the agent) were invoked with `@Exercise722-Composer-Run.md` only.**
> **The user will not paste anything else.** Follow § AUTORUN below.

---

## AUTORUN — execute this now

You are a Lean 4 proof engineer in `/home/catskills/Desktop/scott1980` (mathlib v4.30.0).

### Step 0 — orient (minimal reads)

1. Read `HANDOFF.md` lines 1–18 (Resume Protocol only).
2. Read **this file's Progress tracker** (next section). Find the **first row with status `☐`** whose prerequisites are all `☑` (or empty). That is **YOUR SESSION** — execute **only that one**.
3. If every session is `☑` or `DEFER`, report DONE and stop.
4. If the next session is **C7b** (optional, **7.22k**), skip it unless the user explicitly requests it; take the next eligible `☐`.
5. If **C4** is blocked in HANDOFF, you may run **C11** instead if still `☐`.

### Step 1 — rules (non-negotiable)

- Read ONLY files listed under YOUR SESSION's **READ**.
- Edit ONLY files listed under YOUR SESSION's **EDIT**.
- Zero `sorry`. After **3 failed build-fix attempts** on the same error → **STOP** (§ Stop protocol).
- Choice-free: new proofs must audit to `⊆ {propext, Quot.sound}`.
  **Do NOT use** mathlib's `DFA.toNFA_correct`, `DFA.accepts_inter`, `DFA.accepts_compl` (they pull `Classical.choice`). Use our `dfaToNFA_accepts`, `inter_eval`, `complDFA_accepts`.
- Build: `lake build <module> 2>&1 | grep -vE 'LEAN_PATH|trace:' | tail -25`
- Do **not** git commit unless the user asks.

### Step 2 — execute YOUR SESSION

- Find the session section below (e.g. `## Session C1`).
- Follow **TASK**, use **Skeleton** if present (fill in, do not redesign).
- Do **not** start the next session in the same chat.

### Step 3 — on SUCCESS

1. Append one dated checkpoint to the **end** of `HANDOFF.md` (do not rewrite its middle).
2. In **this file**, change that session's `☐` → `☑` in the Progress tracker below.
3. Report: session id, files changed, build command, axiom audit if new theorems.

### Step 4 — on STOP / BLOCKED

1. Revert broken files if needed (`git checkout -- <file>`).
2. Append `SESSION Cx BLOCKED` checkpoint to HANDOFF.md with exact error.
3. Leave progress tracker unchanged (stay `☐`).
4. Report what to retry.

### Already done — do NOT reprove

- `Exercise722.lean` — Ssys, mulElem, emb
- `Exercise722Regular.lean` — SExpr, denote, matchesB, inS_iff_exists_denote
- `Exercise722DFA.lean` — sigmaDFA, singleDFA, inter/compl
- `Exercise722Cat.lean` — catEps, catEps_accepts
- `Exercise722Decide.lean` — toNFA, toNFA_accepts, denote_eq_empty_iff, dfaToNFA_accepts

---

## Progress tracker

**Agent: after success, edit `☐` → `☑` in this table.**

| Session | Goal | Status | Needs | arxiv |
|---------|------|--------|-------|-------|
| C1 | `instDecidableEqAutState` | ☑ | — | 7.22e |
| C2 | `autStateCard` + bound | ☑ | C1 | 7.22e |
| C3 | `wordsUpTo` + `anyMatchesB` | ☑ | — | 7.22f |
| C4 | short-word bound (pumping) | ☑ | C2, C3 | 7.22f |
| C5 | `decideEmptyB` + `Decidable` | ☑ | C4 | 7.22f |
| C6 | `consistentB` (relation ii) | ☑ | C5 | 7.22f |
| C7a | document interEq gap | ☑ | C5 | 7.22k |
| C7b | full equivalence | Pass | C5 | 7.22k |
| C8 | `SsysX` enumeration | ☑ | C5 | 7.22g |
| **C9a** | first missing **generic** `Nat.Primrec` lemma in `Recursive.lean` | ☑ | C6, C8 | 7.22i(a) |
| **C9b** | `primrec_ssysConsChar` + `Ssys_cons_computable` (umbrella) | Pass | C9a | 7.22i(b) |
| **C9b1** | `decodeFuelOkChar` umbrella (**7.22i(b)1(a–e)**) | ☑ | C9a | 7.22i(b)1 |
| **C9b1a** | `mulBit` + `primrec` | ☑ | C9a | 7.22i(b)1(a) |
| **C9b1b** | `decodeFuelOkChar` + `primrec` | ☑ | C9b1a | 7.22i(b)1(b) |
| **C9b1c** | dispatch lemmas (`Body_eq`, …) | ☑ | C9b1b | 7.22i(b)1(c) |
| **C9b1d** | `decodeListBool_isSome_iff` | ☑ | C9b1b | 7.22i(b)1(d) |
| **C9b1e** | `decodeFuelOkChar_eq_one_iff` | ☑ | C9b1c, C9b1d | 7.22i(b)1(e) |
| **C9b2** | `listLenChar` + `primrec` | ☑ | C9b1b | 7.22i(b)2 |
| **C9b3** | `listEqChar` + `primrec` | ☑ | C9b2 | 7.22i(b)3 |
| **C9b4** | `appendListCode`, `takeCode`, `dropCode` + `primrec` | ☑ | C9b3 | 7.22i(b)4 |
| **C9b5** | `autStateCardFuelChar`, `matchesBChar` + `primrec` | Pass | C9b4 | 7.22i(b)5 |
| **C9b6** | `decideNonemptyBChar`, `consistentBChar` + `primrec` | Pass | C9b5 | 7.22i(b)6 |
| **C9b7** | `ssysConsistentBChar` + shallow Bool `_eq` lemmas | Pass | C9b6 | 7.22i(b)7 |
| **C9b8** | `primrec_ssysConsChar` → `Ssys_cons_computable` | Pass | C9b7 | 7.22i(b)8 |
| C10 | `ComputablePresentation` | Pass | C9b8 | 7.22j |
| C11 | infinite-word prose | ☑ | — | 7.22h |
| C12 | arxiv + audit | ☑ | C6+ | — |

**Targets:** **7.22a–h** = Scott construction formalized (Pass). **7.22i(a)–j** = Def 7.1 (ii) in
`Recursive.lean` via C9a–C10. **7.22k–l** = optional extensions.

**C9 rule:** Do **not** assign "finish C9" as one monolith. **C9a** proves one reusable primrec
closure (decode, bounded fold, or similar)—whichever is the **first missing generic** lemma after
auditing `Recursive.lean` vs the Exercise 7.22 Bool stack. **C9b** is **eight slices** (**C9b1–C9b8** /
inventory **7.22i(b)1–8**); land each green before the next; **C9b8** is the short Presentation
instantiation only.

---

## Stop protocol

STOP when: 3 build failures on same error · 30 min no green · need file outside EDIT · need `Classical.choice` in proof.

```bash
cd /home/catskills/Desktop/scott1980
git status --short
git checkout -- Scott1980/Neighborhood/Exercise722Decide.lean  # example
lake build Scott1980 2>&1 | grep -vE 'LEAN_PATH|trace:' | tail -5
```

---

## Session C1 — `instDecidableEqAutState`

**READ:** `Domain/Neighborhood/Exercise722Decide.lean` (lines 105–130)  
**EDIT:** `Domain/Neighborhood/Exercise722Decide.lean`  
**BUILD:** `lake build Scott1980.Neighborhood.Exercise722Decide`

**TASK:** Add `instDecidableEqAutState : (e : SExpr) → DecidableEq (autState e)` mirroring `instFintypeAutState`. Two `example` lines for `.sigma` and `.single [true, false]`.

**Skeleton:**

```lean
instance instDecidableEqAutState : (e : SExpr) → DecidableEq (autState e)
  | .sigma => inferInstance
  | .single σ => inferInstance
  | .cap a b => by
      letI := instDecidableEqAutState a; letI := instDecidableEqAutState b
      infer_instance
  | .cat a b => by
      letI := instDecidableEqAutState a; letI := instDecidableEqAutState b
      infer_instance
```

---

## Session C2 — `autStateCard`

**READ:** `Domain/Neighborhood/Exercise722Decide.lean`  
**EDIT:** `Domain/Neighborhood/Exercise722Decide.lean`  
**BUILD:** `lake build Scott1980.Neighborhood.Exercise722Decide`  
**Needs:** C1 ☑

**TASK:** Define `autStateCard` (sigma→1, single→|σ|+2, cap→product, cat→sum). Prove `autStateCard_le_card`.

**Skeleton:**

```lean
def autStateCard : SExpr → ℕ
  | .sigma => 1
  | .single σ => σ.length + 2
  | .cap a b => autStateCard a * autStateCard b
  | .cat a b => autStateCard a + autStateCard b

theorem autStateCard_le_card (e : SExpr) : autStateCard e ≤ Fintype.card (autState e) := by
  induction e with
  | sigma => simp [autStateCard, autState]
  | single σ => simp [autStateCard, autState]; exact Nat.le_refl _
  | cap a b ih_a ih_b =>
    simp only [autStateCard, autState, Fintype.card_prod]
    exact Nat.mul_le_mul ih_a ih_b
  | cat a b ih_a ih_b =>
    simp only [autStateCard, autState, Fintype.card_sum]
    exact Nat.add_le_add ih_a ih_b
```

---

## Session C3 — `wordsUpTo`

**READ:** `Domain/Neighborhood/Exercise722Regular.lean` (`matchesB`, `matchesB_iff`)  
**EDIT:** **NEW** `Domain/Neighborhood/Exercise722Words.lean`, wire `Domain.lean`  
**BUILD:** `lake build Scott1980.Neighborhood.Exercise722Words`

**TASK:** `wordsUpTo n`, `anyMatchesB`, prove `mem_wordsUpTo`. `#eval anyMatchesB .sigma (wordsUpTo 0)` = true.

**Skeleton:**

```lean
import Scott1980.Neighborhood.Exercise722Regular

namespace Scott1980.Neighborhood.Exercise722

def wordsUpTo : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
    (wordsUpTo n) ++ (wordsUpTo n).flatMap fun w => [[false] ++ w, [true] ++ w]

theorem mem_wordsUpTo {n w : List Bool} : w ∈ wordsUpTo n ↔ w.length ≤ n := by
  -- induction on n
  sorry -- MUST NOT remain in final file

def anyMatchesB (e : SExpr) (ws : List (List Bool)) : Bool := ws.any (matchesB e)

end Exercise722
```

---

## Session C4 — short-word bound (HARD)

**READ:** `.lake/packages/mathlib/Mathlib/Computability/NFA.lean` (263–334), `Exercise722Decide.lean`, `Exercise722Words.lean`  
**EDIT:** `Exercise722Decide.lean` and/or `Exercise722Words.lean`  
**BUILD:** `lake build Scott1980.Neighborhood.Exercise722Decide`  
**Needs:** C2 ☑, C3 ☑

**TASK:** Prove `nfa_accepts_nonempty_iff_short` and `denote_nonempty_iff_short`. Audit choice-free.

**Skeleton:**

```lean
variable {σ : Type} [Fintype σ] (M : NFA Bool σ)

theorem exists_accepted_word_short (h : M.accepts.Nonempty) :
    ∃ w, w.length < Fintype.card σ ∧ w ∈ M.accepts := by
  obtain ⟨x, hx⟩ := h
  by_cases hlen : x.length < Fintype.card σ
  · exact ⟨x, hlen, hx⟩
  · have hcard : Fintype.card σ ≤ x.length := by omega
    obtain ⟨a, b, c, rfl, hbound, hbne, hpump⟩ := M.pumping_lemma hx hcard
    have hab : a ++ b ∈ M.accepts := by
      -- extract from Language {a}*{b}*{c}; see Language.mem_mul, mem_kstar
      sorry
    have hshort : (a ++ b).length < Fintype.card σ := by
      simp only [List.length_append]; omega
    exact ⟨a ++ b, hshort, hab⟩

theorem nfa_accepts_nonempty_iff_short :
    M.accepts.Nonempty ↔ ∃ w, w ∈ wordsUpTo (Fintype.card σ) ∧ w ∈ M.accepts := by
  constructor
  · intro h; obtain ⟨w, hwlt, hw⟩ := exists_accepted_word_short M h
    exact ⟨w, by rw [mem_wordsUpTo]; omega, hw⟩
  · intro ⟨w, _, hw⟩; exact ⟨w, hw⟩

theorem denote_nonempty_iff_short (e : SExpr) :
    (denote e).Nonempty ↔ ∃ w ∈ wordsUpTo (autStateCard e), matchesB e w = true := by
  -- via toNFA_accepts + matchesB_iff; watch Language/Set defeq
  sorry
```

**If stuck >30 min:** STOP, HANDOFF "C4 BLOCKED", user may re-@ for C11.

---

## Session C5 — `decideEmptyB`

**READ:** C4 theorems, `Exercise722Regular.lean`  
**EDIT:** `Exercise722Decide.lean` or `Exercise722Words.lean`  
**BUILD:** `lake build Scott1980.Neighborhood.Exercise722Decide`  
**Needs:** C4 ☑

**TASK:** `decideNonemptyB`, `decideEmptyB`, iff theorems, `Decidable (denote e = ∅)`. Sanity: `#eval decideEmptyB (.cap (.single [false]) (.single [true]))` = true.

**Skeleton:**

```lean
def decideNonemptyB (e : SExpr) : Bool :=
  anyMatchesB e (wordsUpTo (autStateCard e))
def decideEmptyB (e : SExpr) : Bool := !decideNonemptyB e

@[simp] theorem decideNonemptyB_iff (e : SExpr) :
    decideNonemptyB e = true ↔ (denote e).Nonempty := by
  simp [decideNonemptyB, anyMatchesB, List.any_eq_true, denote_nonempty_iff_short]

@[simp] theorem decideEmptyB_iff (e : SExpr) :
    decideEmptyB e = true ↔ denote e = ∅ := by
  simp [decideEmptyB, Bool.not_eq_true, Set.not_nonempty_iff_eq_empty, decideNonemptyB_iff]

instance decidableEmptyDenote (e : SExpr) : Decidable (denote e = ∅) :=
  if h : decideEmptyB e then .isTrue (decideEmptyB_iff e |>.mp h)
  else .isFalse fun he => h (decideEmptyB_iff e |>.mpr he)
```

---

## Session C6 — `consistentB`

**READ:** `Exercise722Regular.lean`, `Exercise722.lean` (`Ssys_isPositive`)  
**EDIT:** `Exercise722Decide.lean`  
**BUILD:** `lake build Scott1980.Neighborhood.Exercise722Decide`  
**Needs:** C5 ☑

**TASK:** `consistentB a b := !decideEmptyB (.cap a b)`. Prove `consistentB_iff`. Link to Def 7.1 (ii).

```lean
def consistentB (a b : SExpr) : Bool := !decideEmptyB (.cap a b)
theorem consistentB_iff (a b : SExpr) :
    consistentB a b = true ↔ (denote (.cap a b)).Nonempty := by
  simp [consistentB, decideEmptyB_iff, Set.not_nonempty_iff_eq_empty, denote_cap]
```

---

## Session C7a — interEq gap (document)

**READ:** `Exercise722Regular.lean` (`interEq_iff`, `sigma_ne_containsZero`)  
**EDIT:** `Exercise722Decide.lean` (docstring)  
**BUILD:** `lake build Scott1980.Neighborhood.Exercise722Decide`  
**Needs:** C5 ☑

**TASK:** Docstring: relation (i) = language equivalence; emptiness insufficient (`sigma_ne_containsZero`); full decider needs complement + C7b.

---

## Session C7b — DONE (2026-07-01)

Completed: `Exercise722Equiv.lean` (choice-free `Finset`-subset-construction simulation of `toNFA e`,
`interEqB`) + `Recursive.lean` (`interEqChar` primrec mirror, routed through the existing
`matchesBChar` joint fuel/code primrec rather than a new automaton-level encoding) +
`Exercise722Presentation.lean` (`Ssys_interEq_computable`). See `arxiv.md` 7.22k and `HANDOFF.md`
2026-07-01 checkpoint for the full design/perf-pitfall notes.

---

## Session C8 — `SsysX`

**READ:** `Definition71.lean`, `Exercise722Regular.lean` (`inS_iff_exists_denote`)  
**EDIT:** **NEW** `Exercise722Presentation.lean`, `Domain.lean`  
**BUILD:** `lake build Scott1980.Neighborhood.Exercise722Presentation`  
**Needs:** C5 ☑

**TASK:** `SsysX : ℕ → Set (List Bool)`, `SsysX_mem`, `SsysX_surj`. Use `decideEmptyB` to skip empty. Encode/decode SExpr from ℕ.

---

## Session C9a — generic `Nat.Primrec` closure (interface)

**READ:** `Recursive.lean` (`foldCode`, `existsListChar`, `primrec_selectFn`, `RecDecidable₂.of_paired_zero_one_char`); skim `Exercise722Presentation.lean` C9 TODO  
**EDIT:** `Recursive.lean` only (unless audit proves the gap is elsewhere—then STOP and report)  
**BUILD:** `lake build Scott1980.Neighborhood.Recursive`  
**Needs:** C6 ☑, C8 ☑  
**arxiv:** 7.22i(a)

**TASK:** Audit the Exercise 7.22 Bool stack vs existing `Recursive.lean` primrec infrastructure.
Prove the **first missing generic** lemma that reusable future exercises will need—e.g. fuel-bounded
decode primrec, bounded `∃`/`∀` over word indices via `foldCode`/`bExistsFn`, or list-of-Bool encoding.
**Do not** duplicate `SExpr` encode/decode in a monolith. **Do not** prove `primrec_ssysConsChar`
in this session—that is **C9b**. **If stuck >30 min:** STOP, HANDOFF "C9a BLOCKED" with the exact
missing lemma identified.

---

## Session C9b — `Ssys_cons_computable` (eight slices)

**READ:** `Example78.lean` (`PNpres.cons_computable`), `Exercise722Presentation.lean` (C9 section),
`arxiv.md` rows **7.22i(b)1–8**  
**EDIT:** **`Recursive.lean`** for **C9b1–C9b6**; **`Exercise722Presentation.lean`** for **C9b7–C9b8**
only  
**BUILD:** `lake build Scott1980.Neighborhood.Recursive` (slices 1–6) or
`lake build Scott1980.Neighborhood.Exercise722Presentation` (slices 7–8)  
**Needs:** C9a ☑  
**arxiv:** 7.22i(b) umbrella; one sub-row per session

| Slice | Target | Status | arxiv |
|-------|--------|--------|-------|
| **C9b1** | umbrella (closes when **1(a–e)** Pass) | ☑ | 7.22i(b)1 |
| **C9b1a** | `mulBit` + `primrec` | ☑ | 7.22i(b)1(a) |
| **C9b1b** | `decodeFuelOkChar` + `primrec` | ☑ | 7.22i(b)1(b) |
| **C9b1c** | `decodeFuelOkCharBody_eq` + tag-0 helpers | ☑ | 7.22i(b)1(c) |
| **C9b1d** | `decodeListBool_isSome_iff` | ☑ | 7.22i(b)1(d) |
| **C9b1e** | `decodeFuelOkChar_eq_one_iff` | ☑ | 7.22i(b)1(e) |
| **C9b2** | `listLenChar` + `primrec` | ☑ | 7.22i(b)2 |
| **C9b3** | `listEqChar` + `primrec` | ☑ | 7.22i(b)3 |
| **C9b4** | `appendListCode`, `takeCode`, `dropCode` + `primrec` | ☑ | 7.22i(b)4 |
| **C9b5** | `autStateCardFuelChar`, `matchesBChar` + `primrec` | Pass | 7.22i(b)5 |
| **C9b6** | `decideNonemptyBChar`, `consistentBChar` + `primrec` | Pass | 7.22i(b)6 |
| **C9b7** | `ssysConsistentBChar` + shallow Bool `_eq` lemmas | Pass | 7.22i(b)7 |
| **C9b8** | `primrec_ssysConsChar` → `Ssys_cons_computable` | Pass | 7.22i(b)8 |

**One slice per session.** Use shallow char lemmas for iff links—do not unfold `ssys_cons_char_iff`
chains at WHNF. **If stuck >30 min:** STOP, HANDOFF "C9bN BLOCKED" (N = slice number). **C9b3**
resolved: synchronized **`foldCode`** (no **`reForallChar`**/**`tabCode`**). **Next:** **C9b4**.

### Session C9b1 — `decodeFuelOkChar` (sub-slices **1(a–e)**)

**TASK:** **(a–b)** in `Recursive.lean` (in tree ☑). **(c–e)** shallow link ↔ `decodeFuel` — see
**`arxiv.md` rows 7.22i(b)1(c–e)** for strategy; land **(c)** then **(d)** then **(e)**; one
sub-slice per session.

### Session C9b8 — close umbrella

**TASK:** `primrec_ssysConsChar : Nat.Primrec ssysConsChar`; then
`Ssys_cons_computable := Ssys_cons_computable_of_primrec_ssysConsChar primrec_ssysConsChar`.

---

## Session C10 — `ComputablePresentation`

**READ:** `Definition71.lean`, `Example78.lean`  
**EDIT:** `Exercise722Presentation.lean`  
**BUILD:** `lake build Scott1980.Neighborhood.Exercise722Presentation`  
**Needs:** C9b ☑  
**arxiv:** 7.22j

**TASK:** `SsysPres : ComputablePresentation …` with (ii). `interEq_computable` only if C7b done; else `Ssys_partially_effectively_given`.

---

## Session C11 — infinite words (prose)

**READ:** `Exercise722.lean` docstring, `sources/PRG19_vision.md` (grep 7.22)  
**EDIT:** `Exercise722.lean` docstring only  
**BUILD:** `lake build Scott1980.Neighborhood.Exercise722`

**TASK:** Answer Scott's equations in prose. Define σ⃗ as `{X ∈ S | ∀n, σⁿ ∈ X}`. Likely: σ⃗σ⃗=σ⃗ YES; 01⃗…=01⃗01⃗ NO.

---

## Session C13 — `streamArrow` (DONE, 2026-07-01)

Completed: `Exercise722.lean` — Scott's infinite words `σ⃗`, defined *literally as he asks*, as a
genuine least fixed point `σ⃗ = σσ⃗` in the domain `|S|` (`Theorem41.lean`'s `fixElement`, applied to
a new approximable self-map `prependMap σ`, mirroring `Example44.lean`'s `a = 0(1a)`). All four of
Scott's equations hold unconditionally (`streamArrow_mul_self` and friends), superseding the
`streamElem`/`powerLang` proxy's open side-question (`InS (powerLang w)`, kept for reference, not
part of Scott's actual question). Fully choice-free (`⊆ {propext, Quot.sound}`). See `arxiv.md`
7.22l and `HANDOFF.md`'s 2026-07-01 checkpoint for the full design.

---

## Session C12 — arxiv + audit

**READ:** HANDOFF tail; `grep "Exercise 7.22" arxiv.md` (rows 7.22a–h, 7.22i(a)–l)  
**EDIT:** `arxiv.md` (Exercise 7.22 sub-rows), HANDOFF Resume Protocol  
**BUILD:** `lake build Domain`  
**Needs:** C6 ☑ minimum

**TASK:** Update arxiv row (escape `\|` in cells). Audit `decideEmptyB_iff`, `consistentB_iff`.

---

## File map

| File | Touch when |
|------|------------|
| `Exercise722Decide.lean` | C1–C2, C4–C7a |
| `Exercise722Words.lean` | C3–C5 (new in C3) |
| `Exercise722Presentation.lean` | C8, C9b, C10 |
| `Recursive.lean` | C9a |
| `Exercise722.lean` | C11 docstring only |
| `arxiv.md`, `HANDOFF.md` | C12 + every success |

---

## Axiom audit (after C5)

Temp file `Domain/Audit722Decide.lean`:

```lean
import Scott1980.Neighborhood.Exercise722Decide
open Scott1980.Neighborhood.Exercise722
#print axioms decideEmptyB_iff
#print axioms consistentB_iff
```

Delete after audit. Expect `[propext, Quot.sound]` only.

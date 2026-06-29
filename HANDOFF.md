# Handoff — Scott 1981 (PRG-19): Lectures I–IV COMPLETE (IV spine Thm 4.1/4.2, Ex 4.3/4.4, Def 4.5 + Thm 4.6, **all Exercises 4.7–4.25**); **Lecture V COMPLETE** (Table 5.5, Thm 5.1/5.2/5.6, Prop 5.3/5.4, **Exercises 5.7–5.16 — including 5.16's full Thue–Morse `t`: unfolding, digit-sum-mod-2 (Lambek), and overlap-freeness**); **Lecture VI: Example 6.1 (D<sup>§</sup> ≅ D + (D<sup>§</sup>×D<sup>§</sup>)), Example 6.2 (`B ≅ B+B`, `C ≅ {{Λ}}+C+C`, the generalization `A ≅ Aⁿ + Aⁿ`, and eventually-periodic trees ↔ regular events via Myhill–Nerode) + categorical spine (Defs 6.3–6.5, Props 6.6–6.7) Definition 6.8 (functors *continuous on maps*, over the strict function space), and **Theorem 6.9 (homomorphisms out of a fixed point `D ≅ T(D)`)**, and **Theorem 6.14 (initial `T`-algebra: existence + uniqueness/initiality among strict algebras)**, **Lemma 6.15 (projection pair ⟹ `D ⊴ E`)** and **Theorem 6.16 (an initial `T`-algebra embeds in every solution: `D ⊴ E` for all `E ≅ T(E)`)** COMPLETE**; **Lecture VII: Definition 7.1 (computable presentation), Definition 7.2 (computable map / computable element), and Proposition 7.3 (identity + composition computable; computable map ∘ computable element), and **Theorem 7.4 — BOTH halves** (`D₀×D₁` *and* `D₀+D₁` effectively given; `projᵢ`/`inᵢ`/`outᵢ`, `⟨f,g⟩`, `f×g`/`f+g` computable) COMPLETE & CHOICE-FREE** over a bespoke choice-free recursion theory + r.e. closure layer (`Recursive.lean`, incl. truncated subtraction, `RecDecidable.natEq`/`.not`/`.em`/`.or`, `REPred.or`, **and now a choice-free primitive-recursive bitwise OR `myLor`**); **Example 7.8 (the powerset `PN` is effectively given) COMPLETE & fully choice-free (`Example78.lean`)**; **Definition 7.9 (the Smyth power domain `ℙ𝒟` family: down-set `↓X`=Ex 1.20 `upSet`, preparation `𝒟†`=`powerSystem`, finite-union family `PDmem`, the two intersection remarks) COMPLETE & fully choice-free (`Definition79.lean`)**; rest of VI + VII–VIII transcribed & inventoried

You are a Lean 4 proof engineer formalizing Dana Scott's 1981 *Lectures on a Mathematical Theory of
Computation* (PRG-19) in:

`/home/catskills/Desktop/domain_theory` — mathlib `v4.30.0`, Lean toolchain per `lean-toolchain`.

## Resume Protocol (read this first)

A session may begin after a context reset; chat memory is not durable, these files are. To resume:

1. Read this `HANDOFF.md` top-to-bottom (it is the source of truth for status + recent work).
2. For the inventory of every item and its status, **`Grep` `arxiv.md`** for the item (e.g.
   `Theorem 6.9`) and read only that row — do **not** read `arxiv.md` whole (~2.5k lines).
   Do **not** use `arxiv_with_code.md` (generated PDF artifact; stale; in `.cursorignore`).
3. Per-item details live in the relevant `Domain/Neighborhood/*.lean` docstring/proof notes.
4. Build with `lake build Domain` (filter output: `| grep -vE 'LEAN_PATH|trace:' | tail`).
5. Follow `.cursor/rules/handoff-discipline.mdc` (choice discipline, axiom audits, and the
   end-of-item checklist that keeps this file + `arxiv.md` current).
6. **To finish Exercise 7.22 decider in Composer bites:** `@Exercise722-Composer-Run.md` only
   (one @ per session, no pasting — agent picks next ☐ from progress tracker). Reference:
   `Exercise722-Composer-Playbook.md` (extended notes, same content). **Composer tracker (2026-06-28):**
   C1–C8 ☑, C11 ☑, C12 ☑; **C9 BLOCKED** (needs `Nat.Primrec` char for `ssysConsistentB`; monolith `Exercise722Primrec.lean` abandoned 2026-06-29); C10 waits on C9; C7b DEFER.

**Just completed — Exercise 7.22 (algebraic core) is DONE** (`Exercise722.lean` green, wired, zero
`sorry`, **fully choice-free `⊆{propext,Quot.sound}`**). Scott's domain over `Σ={0,1}*=List Bool`
built by least fixed point: inductive **`InS`** (`S` = closure of `Σ`/`{σ}`/`concat`/*non-empty* `∩`),
`InS.nonempty` ⟹ **`Ssys`** a **positive neighbourhood system** (`ofPositive`, master `Δ=Σ=univ`;
`Ssys_isPositive`). Bespoke `concat X Y={a++b}` (own mono/assoc/singleton/nonempty lemmas, to keep
`∩`/`univ`/`{σ}` native `Set` ops). **Multiplication `mulElem`** (`xy={Z∈S∣∃X∈x∃Y∈y,XY⊆Z}`) a filter,
**`mulElem_assoc`** ⟹ `|S|` a semigroup; **`emb σ={X∈S∣σ∈X}`** with **`emb_mul`** (homomorphism) +
**`emb_injective`**. **Deliberately NOT mechanised (discussed in docstring, no `sorry`):** *effectively
given* (the regular-event decision algebra — needs automata decision procedures rebuilt choice-free in
`Recursive.lean`; relation (ii) consistency ≡ non-emptiness by positivity) and the *infinite-word*
fixed-point equations (Scott poses them as open investigations). **Follow-up `Exercise722Regular.lean`
adds the regular-event layer**: syntax `SExpr` (`Σ`/`{σ}`/`·`/`∩`), `denote`, **decidable word
membership** (`matchesB`/`decidableMemDenote`), and the characterization
`InS X ↔ ∃e, denote e=X ∧ X.Nonempty` — making the "regular events" hint precise. **The choice-free
decision layer (Route A: explicit `Fintype` automata) is now built across THREE files**:
`Exercise722DFA.lean` (leaf DFAs `sigmaDFA`/`singleDFA` + `interDFA`/`complDFA`),
`Exercise722Cat.lean` (**the concatenation εNFA `catEps` + `catEps_accepts = concat`, the crux mathlib
lacks**, via the closed-form `catEps_mem_eval_iff`), and `Exercise722Decide.lean` (`NFAinter` product,
the uniform **`toNFA : SExpr → NFA Bool (autState e)` with `toNFA_accepts : (toNFA e).accepts =
denote e`**, and **`denote_eq_empty_iff`** reducing Def-7.1 relation (ii) to finite-state
reachability). All `⊆{propext,Quot.sound}` (incl. a hand-rolled choice-free `dfaToNFA_accepts`, since
mathlib's `DFA.toNFA_correct` pulls `Classical.choice`). Remaining: turn the `∀x` in
`denote_eq_empty_iff` into a terminating search (reachability Finset, or pigeonhole pump-down +
`matchesB`), equivalence (needs `Finset`-state determinization), and the `RecDecidable`/`Nat.Primrec`
bridge. See the **two latest dated checkpoints at the very bottom**.

**Just completed — Exercise 7.21 is DONE** (`Exercise721.lean` green, wired, zero `sorry`). Headline
combinator **`papply : ℙ(D→E) → (ℙD → ℙE)`** = the Smyth power-domain lift of evaluation:
**`papplyEval V W : ApproximableMap₂ ℙ(funSpace V W) ℙV ℙW`** with `rel Φ A B := … ∧ ∀G∈Φ,∀X∈A,∃Y∈B,
(eval V W).rel G X Y` (the two-variable analogue of Ex 7.19's `ℙf`), made `papplyB = ofMap₂ papplyEval`
and **curried (Thm 3.12)** to the exact type `papply = curry papplyB`. Non-trivial
(`papplyEval_step_witness`: `↓[X₀,Y₀] papply ↓X₀ ↦ ↓Y₀`). **Computable when `eval` is**
(`papplyEval_isComputable`, reduces on Prop-7.10 codes to `∀g∈dl,∀x∈dl,∃y∈dl, eval(…)` via the new
**choice-free** helper `re_forallG_forallX_existsY` = `bExists_decodeList_re` + `forall_mem_decodeList₂`×2;
base `heval` = Thm 7.5 `evalMap_isComputable`). Docstring answers the other 3 questions: Q2 (no isos
among `D→ℙE`, `ℙ(D×E)`, `ℙD×ℙE` in general — `ℙ` doesn't distribute over `×`), Q3 (yes, relational
composition `ℙ(D×E)×ℙ(E×F)→ℙ(D×F)`, same Smyth-lift recipe), Q4 (`ℙN⊴PN`, the finitary/computable core,
not isomorphic). Helper `⊆{propext,Quot.sound}`; all other decls carry Prop-level `Classical.choice`
inherited from the power domain (none added, as in 7.19/7.20). See the **latest dated checkpoint at
the very bottom**.

**Just completed — Exercise 7.20 is DONE** (`Exercise720.lean` green, wired, zero `sorry`). The
flattening combinator **`union : ℙ(ℙD) → ℙD`** (the power-domain monad multiplication `μ`):
**`unionMap`** with rep-independent `rel A B := ℙℙD.PDmem A ∧ ℙD.PDmem B ∧ ∀ S∈A, ∀ X∈S, ∃ Y∈B, X⊆Y`,
matching Scott's display `∀i<n∀j<m_i∃k<q. X_{ij}⊆Y_k` (`unionMap_rel_fin`). **Computable — in fact
recursively decidable** (`unionMap_isComputable`, reduces on codes to a nested bounded `∀∀∃` via one
extra `bForallList` over Prop 7.10's `subCode_computable`; the `ℙℙD` presentation is a *double*
`PDPresentation` with inner `ℙ𝒟`-cons `= fun _ => 1`). Discussion: `union({{x},{y,z}})={x,y,z}`;
`ℙℙD ≇ ℙD` in general. All decls `⊆{propext,Classical.choice,Quot.sound}` (choice Prop-level,
inherited from the power domain, as in 7.19). See the **latest dated checkpoint at the very bottom**.

**Just completed — Exercise 7.19 is DONE** (`Exercise719.lean` green, wired, zero `sorry`). `D↦ℙD` is
a functor: **`PFmap f : ℙD→ℙE`** (rep-independent `rel A B := PDmem A ∧ PDmem B ∧ ∀X∈A,∃Y∈B, X f Y`,
matching Scott's `∀i<n∃j<m. Xᵢ f Yⱼ` via `PFmap_rel_fin`), approximable, with functor laws
`PFmap_idMap`/`PFmap_comp` (the latter builds the middle nbhd via choice-free `comp_witness`).
**`ℙf` is computable when `f` is** (`PFmap_isComputable*`, new `bExists_decodeList_re` +
`REPred.forall_mem_decodeList₂`). All decls `⊆{propext,Classical.choice,Quot.sound}` — the choice is
Prop-level and **inherited** from `ℙ𝒟`'s ∩-closure (Prop 7.10), not added here. See the **latest
dated checkpoint at the very bottom**.

**Just completed — Exercise 7.17 is DONE (both parts)** (`Exercise717.lean` + `Exercise717Part2.lean`
green, wired, zero `sorry`). Part 2 builds the universal strict catamorphism `g : D^§ → E` as a
neighbourhood relation `GRel u v` → `ApproximableMap gMap`, proves the defining equations `gMap_in`/
`gMap_pair` + `gMap_strict` (choice-free `⊆{propext,Quot.sound}`), and `gMap_isComputable` via a fresh
course-of-values **certificate evaluator** `gEval` with soundness/completeness. See the **latest dated
checkpoint at the very bottom** for the full design + gotchas.

**Just completed — Exercise 7.13 is DONE** (`Exercise713.lean` green, wired, zero `sorry`, **fully
choice-free `⊆{propext,Quot.sound}` including the reconstruction isomorphism**). Full equivalence
"effectively given domain ⇔ an `INCL(n,m)` relation on `ℕ`": abstract **`InclStructure`** (INCL +
primrec `meetIdx`/`topIdx` witnesses + `INCL`/`CONS`/`MEET` recursively decidable + axioms (i)–(iv)
as `axiom_i..iv`); **(⇐)** hint system `Sₙ={m∣INCL m n}` (`toSystem`/`toPresentation`/
`toSystem_isEffectivelyGiven`, key `toNbhd_subset_iff : Sₙ⊆Sₖ↔INCL n k`); **(⇒)** `ofPresentation`
(`INCL n m:=Xₙ⊆Xₘ`, with `meet_iff_interEq : MEET↔Xₙ∩Xₘ=Xₖ`); **round-trip A**
`ofPresentation_toPresentation_INCL`; **round-trip B** `reconstruct_isomorphic : toSystem
(ofPresentation P) ≅ᴰ V` (answers "essentially any effectively given system?" — yes), via
`reconElem`/`reconElemInv`/`reconIso`. See the **latest dated checkpoint at the very bottom**.

**Just completed — Exercise 7.14 is DONE** (`Exercise714.lean` green, wired, zero `sorry`, **all four
headline decls fully choice-free `⊆{propext,Quot.sound}`**). Both halves: **Half 1** the
"non-empty r.e. ⇔ range of a primrec function" facts after Def 7.2 (`repred_range_primrec`,
`repred_exists_primrec_range` via `r w:=selectFn (isOne (qc w)) w.2 a`, and the map form
`repred₂_exists_primrec_enum`); **Half 2** `computableElement_eq_decreasing_iUnion_principal`
(`y=⋃ᵢ↑Y_{t(i)}` with `t` primrec + decreasing, via running intersections `tFun Q r₀` built with
`Nat.Primrec.prec`). See the **latest dated checkpoint at the very bottom**.

**Just completed — Exercise 7.16 is DONE** (`Exercise716.lean` green, wired, zero `sorry`, **fully
choice-free `⊆{propext,Quot.sound}`**). Completes the proof of Theorem 7.5: writes `curry` out as a
neighbourhood relation (`curryComb_rel`, via the *least map* `toApproxMap_principal_mem`) and settles
Scott's question — **`curry` is a *recursive* (recursively decidable) set, not merely r.e.**, just like
`eval`. Reuses Table 5.5's combinator `curryC` (no redefinition). The code-level relation reduces to a
*bounded* double-`∀` over `decodeList` whose atom is product-function-space inclusion (`incl_computable`,
decidable); see `curryComb_rel_recDecidable`/`curryComb_isComputable`. Helper `curryStepCode`
(`Xenum`-singleton) + reductions `mem_Xenum_iff_map`/`curry_rel_Xenum_iff`/`Xenum_singleton`. See the
**latest dated checkpoint at the very bottom**.

**Just completed — Exercise 7.15 is DONE incl. ALL combinators** (`Exercise715.lean` green, wired,
zero `sorry`). All three constructs effectively given: **`⊗`/`⊕`** via Scott's *bare* Def 7.1
(`ScottPresentation`, no primrec `inter` — provably impossible under bottom-collapse;
`smash_isEffectivelyGivenS`/`osum_isEffectivelyGivenS`, classical input localised to the enumeration),
and **`D`<sup>∞</sup>** `= iterSys V` via the *full* `ComputablePresentation` **fully choice-free
`⊆{propext,Quot.sound}`** (`iterSys_isEffectivelyGiven`/`iterPresentation`; codes = fiber-index lists,
`inter` tabulated with the new `Recursive.tabCode`/`nthCode`; combinator `projN_isComputable`).
**Combinators now at full Theorem-7.4 parity:** **`⊕`** has `osumInMap₀/₁` (in), `osumOutMap₀/₁` (out),
`osumMap` (`f⊕g`); **`⊗`** has `smashProj₀/₁` (proj), `smashPaired` (`⟨a,b⟩⊗`), `smashMap` (`f⊗g`);
**`D`<sup>∞</sup>** has `projN` (`head=projN 0`) — every `*_isComputable` proven via `IsComputableMapS`.
Axiom audit: `projN_isComputable ⊆ {propext, Quot.sound}` (choice-free); the `⊗`/`⊕` combinators carry
`Classical.choice` (Prop-level only — inherited from the classical `smashEnum`/`osumEnum` branch, as
documented). **Watch:** mathlib's `grind`-proved `List.getD_eq_default`/`getD_eq_getElem`/
`getD_append(_right)` pull `Classical.choice` — re-proved choice-free as `getD_*_cf` in `Recursive.lean`.
See the **latest dated checkpoint at the very bottom**.

**Just completed — Exercise 7.17 Part 1 is DONE** (`Exercise717.lean` green, wired, zero `sorry`).
Clause 1 of 7.17 — "complete 7.7 including *all* the Example 6.1 combinators of `D^§`". Adds the rest
of the combinator set beyond `Combinators77.lean`'s selection (`inSharp`+`proj₀`): **`proj1Map`** (2nd
projection, `proj1_toElementMap_pairSharp`/`proj1_isComputable`) and **`pairSharpMap`** (the joint
pairing `D^§×D^§→D^§`, `pairSharpMap_toElementMap : pair(x,y)↦⟨x,y⟩^§`/`pairSharp_isComputable`, index
rel `V_{2·t+2}⊆V_k` via `Vsharp_even`). Data + faithfulness `⊆{propext,Quot.sound}`; the two
`*_isComputable` carry `Classical.choice` (as in Combinators77). **Remaining for 7.17 Part 2: the
universal strict `g:D^§→E`** (catamorphism + computability). See the **latest dated checkpoint at the
very bottom**.

**Just completed — Exercise 7.18 is DONE** (`Exercise718.lean` green, wired, zero `sorry`, **fully
choice-free `⊆{propext,Quot.sound}` including computability**). Part 1: defines *effective
isomorphism* (`EffectiveIso` = mutually inverse computable approximable maps; `EffectivelyIsomorphic`;
`EffectivelyIsomorphic.isomorphic : D≅ᴰE`). Part 2: `D∞ ≅ (D∞)∞` is effective — reindexing maps
`Fmap`/`Gmap` (recursively *decidable*) over `iterPresentation`, inverse laws via `reindexF`/
`reindexG`. See the **latest dated checkpoint at the very bottom**.

**Next concrete target: open Lecture VII items** —
**Exercise 7.19** (`D↦PD` is a functor), **Exercise 7.23**
(finish `PN`). The Ex-7.13 infra to reuse: `ComputablePresentation`,
`incl_computable`/`cons_computable`/`inter`, `RecDecidable`/`REPred`, and now the
`InclStructure`/`ofPresentation`/`reconIso` layer in `Exercise713.lean`.

**Just completed — Proposition 7.12 is fully RESOLVED** (`Proposition712.lean` green, wired, zero
`sorry`). Parts A, B, D hold for every `𝒟`; **Part C (`D ⊴ ℙD`) is FALSE in general and is formalized
as a counterexample** (`Counterexample712C.vshape_not_trianglelefteq_powerDomain`). See the
**"Prop 7.12 Part C REFUTED" checkpoint near the bottom**. (Scott's text *does* assert `D≅D†⊴ℙD` on
PRG-19 p.129–130, but his proof glosses the empty-union edge case: a monotone retraction `ℙ𝒟→𝒟`
must send `⊤_{ℙ𝒟}=↑∅` to a greatest element of `\|𝒟\|`, which a general bounded-complete domain
lacks. The claim holds iff `\|𝒟\|` has a top, e.g. `∅∈𝒟`.) Other open Lecture VII items:
**Exercise 7.14** (the post-Def-7.2 r.e. facts + `y=⋃↑Y_{t(i)}` decreasing-primrec form),
**Exercise 7.17**
(the full combinator finish), **Exercise 7.23** (finish `PN`: `fun`/`graph`/`∩`/`∪`/`+` computable,
building on `Example78.lean`).
**Prop 7.7 is fully DONE** across `Proposition77.lean` + `Combinators77.lean` (green, wired): the
`Vsharp` layer, the primitive-recursive course-of-values deciders (`dsharpStep`/`gOf`/`intI` memo
evaluator, `dsharp_decider_spec`), the assembled `dsharpPresentation` + `dsharp_isEffectivelyGiven`
(**`D^§` effectively given whenever `D` is**), **and** a selection of Example 6.1 combinators computable
(`inSharpMap`/`inSharp_isComputable` for `λx.x^§`, `proj0Map`/`proj0_isComputable` for `proj₀`, each
with an elementwise faithfulness theorem). All *data* is choice-free `⊆{propext,Quot.sound}`; only the
`Prop`-level computability/correctness proofs pull `Classical.choice` (unavoidable — `Set` equality over
arbitrary `α`). Full design is in the **two latest dated checkpoints at the very bottom.** **Theorem 7.6 is DONE** (`fix:(D→D)→D`
computable, `Theorem76.lean`, `fixMap_isComputable`, choice-free) — see the **latest dated checkpoint
at the very bottom**. **Theorem 7.5 is DONE in full** (all four parts: `(D₀→D₁)` effectively
given via `funPresentation`/`funSpace_isEffectivelyGiven`; `eval` computable `evalMap_isComputable`;
computable elements = computable maps `isComputableElement_funPresentation_iff`; `curry` computable
`curry_isComputable`), green, wired into `Domain.lean`, every decl `⊆ {propext, Quot.sound}`.
Theorem 7.4 is also **DONE in full** (both halves, choice-free; see below).

**`omega` / choice gotcha (important, cost me a debugging cycle):** `omega` invoked on a goal whose
type is **not** arithmetic — e.g. a `Set` equality `A = B`, even when it closes the goal purely by a
contradiction among the `ℕ` hypotheses — **silently pulls `Classical.choice`** (it needs `Decidable`
of the goal prop and falls back to `Classical`). Fix: `exfalso` first (then the goal is `False`,
arithmetic-compatible) — `exfalso; omega` audits `⊆ {propext, Quot.sound}`. Same trap as `omega` on
an `↔`. Also `Set.Nonempty.ne_empty` is classical; instead `obtain ⟨x,hx⟩ := …nonempty; rw [← h] at
hx; exact absurd hx (Set.notMem_empty x)`.

**Theorem 7.4 × half is COMPLETE and CHOICE-FREE** (`Theorem74.lean`): `prodPresentation P₀ P₁`
(`W_k = X⁰_{k.1} ∪ X¹_{k.2}`, uniform so 7.1(i)/(ii) split into *conjunctions* of the factors'
relations via `prodNbhd_inter`/`prodNbhd_subset_iff` — handled by `RecDecidable.and`/`.comp`/`.of_iff`,
no new RT), `prod_isEffectivelyGiven`, `proj₀_isComputable`/`proj₁_isComputable` (recursive slice of
`incl`), `paired_isComputable` (conjunction of two r.e.), `prodMap_isComputable` (`f×g=⟨f∘p₀,g∘p₁⟩`
(Ex 3.19) + `comp_isComputable`). New choice-free RT in `Recursive.lean`: `primrec_pred`/`primrec_sub`,
`RecDecidable.natEq`/`.not`/`.em`/`.or`, `REPred.or` — all `⊆ {propext, Quot.sound}`.
**Proposition 7.3 is COMPLETE and CHOICE-FREE** (`Definition72.lean`): `idMap_isComputable`
(identity), `comp_isComputable` (composition of computable maps — `∃l, Xₙ f Yₗ ∧ Yₗ g Zₖ` via
`Q.surj`), and `apply_isComputableElement` (computable map ∘ computable element = computable element).
Powered by a new **choice-free r.e. closure layer** in `Recursive.lean`: `REPred.comp` (primrec
reindex), `REPred.and` (conjunction, pair search vars), `REPred.proj` (`∃` over ℕ, fold into search
var); all audit `⊆ {propext, Quot.sound}`.
**Definition 7.2 is COMPLETE and CHOICE-FREE** (`Definition72.lean`, ns `Domain.Neighborhood`):
`IsComputableMap P Q f := REPred₂ (fun n m ↦ f.rel (Xₙ) (Yₘ))` (Scott's *computable map* = r.e.
neighbourhood relation `Xₙ f Yₘ`), `IsComputableElement Q y := REPred (fun m ↦ y.mem (Yₘ))` (the
`𝟙→W` degeneration), `idMap_isComputable` (identity computable, via `incl_computable.re`),
`principal_isComputableElement` (finite/principal elements computable — recursive slice of
`incl_computable`). New choice-free r.e. layer in `Recursive.lean`: `REPred`/`REPred₂` (= projection
of a `RecDecidable` relation, `∃i, q⟨i,n⟩`), `RecDecidable.re`/`RecDecidable₂.re`, `REPred.of_iff`,
`rePred_of_forall`; all audit `⊆ {propext, Quot.sound}`.
**Definition 7.1 is COMPLETE and CHOICE-FREE** (`Definition71.lean` + `Recursive.lean`, ns
`Domain.Neighborhood`): `ComputablePresentation V` (enumeration `X:ℕ→Set α` onto 𝒟 + Scott's two
relations interEq/cons as `RecDecidable₃`/`RecDecidable₂`), `incl_computable`, `eq_computable`,
`NeighborhoodSystem.IsEffectivelyGiven`, sanity inhabitant `unitSys_isEffectivelyGiven` — all audit
`{propext, Quot.sound}`. **RECURSION-THEORY NOTE for all of Lecture VII — we roll our own and
rejected Mathlib because it opens Classical and we are trying to avoid that:** Mathlib's
`Computable`/`ComputablePred`/`Primrec`/`Partrec`/`REPred` correctness lemmas are proved via
`grind`/`lia` or the `@[simp]` `Nat.unpair_pair`, all of which pull `Classical.choice` (even
`Computable.const` does). Rather than inherit that, `Recursive.lean` rebuilds the slice we need
choice-free: `RecDecidable p := ∃ f, Nat.Primrec f ∧ ∀n, p n ↔ f n = 1`; choice-free `Nat.sqrt`
correctness (`iter_sq_le`/`lt_iter_succ_sq`/`sqrt_le`/`lt_succ_sqrt`/`sqrt_eq_of`, porting mathlib's
proofs with `grind`/`lia`→`omega` and a local choice-free `lt_of_mul_lt_mul_left'`); the
`Nat.pair`/`unpair` round-trips (`unpair_pair`/`pair_unpair`); primitive-recursive `id`/`+`/`*`
(`primrec_id`/`primrec_add`/`primrec_mul`, built only from the choice-free `Nat.Primrec`
*constructors*); and closure lemmas `RecDecidable.of_iff`/`.comp` (reindex)/`.and`. Everything is
`⊆ {propext, Quot.sound}`. Use these (not mathlib's recursion theory) for 7.2 onward.
**Exercise 6.29 is COMPLETE** (`Exercise629.lean`,
ns `Exercise629`): infinitary `∏_i D_i` (`iprod`, cylinders + finite support; headline
`iprodEquiv : |∏_i D_i| ≃o ∀ i, |D_i|`), `∑_i D_i` (`isum`, separated sum + `isum_trichotomy`),
`⊕_i D_i` (`ioplus`, coalesced) — these **generalize**; `⊗_i D_i` (`iotimes`) **degenerates** over an
infinite index (`iotimes_subsingleton`: only the basepoint). So `+`,`×`,`⊕` generalize, `⊗` does not.
Finite support is the *positive* `List` form `∀ i, i∉l → X i = master` (keeps `FinSupp.inter`/recon
choice-free). Data + `isum_summand_unique` are `⊆ {propext, Quot.sound}`; only `isum_trichotomy` (EM)
and the `⊗` degeneracy (classical `Set.Finite`) use `Classical.choice` (Prop-level, flagged). See the
dated checkpoint at end.
**Exercise 6.28 is COMPLETE** (`Exercise628.lean`, namespace `Domain.Neighborhood`): the finite
Cantor–Schröder–Bernstein Plotkin suggested — if `|𝒟|,|ℰ|` are finite and `𝒟 ⊴ ℰ ⊴ 𝒟` then
`𝒟 ≅ᴰ ℰ` (`isomorphic_of_trianglelefteq_both`; faithful nbhd-count version
`isomorphic_of_finite_system`). Crux: `⊴` already yields an **order embedding** `|D| ↪o |E|`
(`Trianglelefteq.elementEmbedding`, via Prop 6.12's `i,j` and `projElementEmbedding`); mutual
embeddings of finite types ⟹ iso (`orderIso_of_embeddings`, `Fintype.card` antisymm). Infinite
question answered **No** (finite cardinality count, no infinite analogue) — counterexample as prose.
Relational core choice-free; the finite count uses `Classical.choice` (extract `Fintype`). See dated
checkpoint at end.
**Exercise 6.27 is COMPLETE** (`Exercise627.lean`, namespace `Domain.Neighborhood.Exercise627`):
which `⊴` subsystem relations hold — **the first five hold for all `𝒟,ℰ`, the sixth `𝒟 ⊴ 𝒟⊗ℰ`
fails in general**. `(1) (𝒟⊗ℰ)◁(𝒟×ℰ)`, `(3) (𝒟⊕ℰ)◁(𝒟+ℰ)` are literal subsystems; `(2) 𝒟⊴𝒟×ℰ`,
`(4) 𝒟⊴𝒟⊕ℰ` are projection pairs (Lemma 6.15); `(5) (𝒟→⊥ℰ)⊴(𝒟→ℰ)` is the inclusion/strictification
pair `inclMap`/`strctMap` (choice-free, general systems); `(6)` is refuted by `ℰ=𝟙` collapsing
`𝒟⊗𝟙` to a one-point lattice. Part 4's `oplus_mem_leftN` (the `X=Δ₀?` split) is the **only**
`Classical.choice` use; rest `⊆ {propext, Quot.sound}`. See dated checkpoint at end.
**Exercise 6.26 is COMPLETE** (`Exercise626.lean`, namespace `Domain.Neighborhood.Exercise619`):
the **lift** `liftTok D _hD = {{Λ}∪0Δ}∪{0X∣X∈𝒟}` over `Str={0,1}*` (`∅`-free, packaged `ScottSys.lift`).
**Elements** `|𝒟_⊥|≅|𝒟|_⊥`: fresh bottom `liftBot`, embedding `liftUp` with `liftBot_le`,
`liftUp_le_liftUp_iff`, `liftBot_lt_liftUp`, `unlift`/`liftUp_unlift`, covering `eq_liftBot_or_exists_liftUp`
(its lone `Classical.choice`, for the `z.mem 0Δ?` split; everything else choice-free). **Functor** (yes,
strict): `liftMapTok`, `liftMapTok_isStrict`/`_id`/`_comp`. **`𝒟_⊥⊕ℰ_⊥≅ᴰ𝒟+ℰ`** (`lift_oplus_lift_iso_sum`,
elementwise `OrderIso` `toSumLift`/`fromSumLift`, deletes the inner `0`). **`𝒟_⊥⊗ℰ_⊥≅ᴰ(𝒟×ℰ)_⊥`**
(`lift_otimes_lift_iso_lift_prod` — answer to Scott's `??`; `toLiftProd`/`fromLiftProd`). See dated
checkpoint at end. **Exercise 6.25 is COMPLETE** (`Exercise625.lean`, namespace `Domain.Neighborhood.Subsystem.ProjectionPair`):
the projection pair `g=inj`, `h=proj` of `ProjectionPair D E` carries the two laws on elements
(`proj_inj_apply : h(g x)=x`, `inj_proj_apply_le : g(h y)⊑y`); from them the **Galois connection**
`galois : g(x)⊑y ↔ x⊑h(y)` (monotonicity in each direction), the two **extremal formulas**
`proj_eq_sSup : h(y)=⊔{x∣g(x)⊑y}` (the set is the down-set of `h(y)` — bounded + `lowerSet_directed`)
and `inj_eq_sInf : g(x)=⊓{y∣x⊑h(y)}` (the up-set of `g(x)` — `upperSet_nonempty`), and finally `g`
**maps consistent (=bounded) sets to consistent sets** (`inj_bounded`) and **preserves all lubs**
`inj_sSup : g(⊔S)=⊔{g(s)}` (lower-adjoint property, proved via `galois`). Choice-free; see the dated
checkpoint at the end. **Exercise 6.24 is COMPLETE**
(`Exercise624.lean`, namespace `Domain.Neighborhood.Exercise624`): the **double fixed-point** method
for the coupled system `D ≅ D+(D×E)`, `E ≅ D+E`. Tokens `Str={0,1}*`; token recursions
`gTok p q = insert [] (0p ∪ 1q) = tok(D+E)` and `fTok p q = gTok p (gTok p q) = tok(D+(D×E))`; the
pair Kleene iteration `pIter` gives `GammaD/GammaE` with `fTok_GammaD_GammaE`/`gTok_GammaD_GammaE`
(continuity = each token references ≤1 coordinate, so a single stage suffices, no merge). Object level:
`Dsol={Γ_D}`, `Esol={Γ_E}`, `Dsol_subsystem : {Γ_D} ◁ D+(D×E)` and `Esol_subsystem : {Γ_E} ◁ D+E`
simultaneously (`exists_simultaneous_subsystems`) — the joint hypothesis of the simultaneous Thm 6.14.
Choice-free; see the dated checkpoint at the end.
**Exercise 6.23 is COMPLETE — all four phases** (`Exercise623.lean`: the concrete solution domain
`Exp` for `Exp ≅ N ⊕ ((Exp×Exp)+(Exp×Exp))`; the strict-map `Category ScottSys` + `Texp` as an
`Endofunctor` + the algebra `ExpAlg`; the **evaluation homomorphism** `descAlgHom : AlgHom (ExpAlg N
hN) B` for every algebra `B` (Scott's `val(s)`, existence), built as the Kleene fixed point
`⋃ₙ k∘T(·)∘j`; and **uniqueness/initiality `ExpInitial : IsInitial (ExpAlg N hN)`** via the projection
chain `ρₙ = iₙ∘jₙ`, the functor-carries-the-projection-pair crux `GExpr.map_inj/map_proj`, the key
equation `key_rho : ρₙ₊₁ = i∘T(ρₙ)∘j`, and `g`-independence `gcomp_rho_eq : g∘ρₙ = valₙ` ⟹
`descMap_eq_algHom`). Choice-free `{propext, Quot.sound}`. **Exercise 6.24 is COMPLETE**
(double fixed point — see above and the dated checkpoint). **Exercise 6.22 is
COMPLETE** (`Exercise622.lean`: the three domain equations recognised as `GExpr` fixed points).
**Exercise 6.21 is COMPLETE** (`Exercise621.lean`: coalesced sum `⊕`, smash product `⊗`, the
6-constructor functor algebra `GExpr`, its 6.20 fixed point, and the n-ary generalization). Earlier completed milestones below
for context. **Exercise 6.17 is COMPLETE — both parts** (`Exercise617.lean`,
`Exercise617Gen.lean`). Part 1: `CisInitial : IsInitial Calg`, `C` is the initial `T`-algebra for
`T(X)=𝟙+X+X`. Part 2 (`Exercise617Gen.lean`): the development is generalized over an arbitrary
alphabet `A : Type [DecidableEq A]` — domain `Cn A` of finite/infinite `A`-sequences, endofunctor
`Tsig(X)=𝟙+Σ_{a:A}X` (`sumSig`/`sumMapSig`/`Tsig`), iso `Cn_domain_equation : Cn A ≅ᴰ 𝟙+Σ_a Cn A`,
and **initiality `CnisInitial : IsInitial Cnalg`**; instantiating `A := Fin (n+1)` gives Scott's `Cₙ`
(`Cfin_domain_equation`, `CfinIsInitial`), and `n=1` (`Fin 2 ≃ Bool`) recovers the binary case. See
the dated checkpoint at the end of this file. **Exercise 6.18 is COMPLETE** (`Exercise618.lean`,
`iterIsInitial : IsInitial (iterAlg Dom)` — `𝒟^∞` is the initial algebra of `T(X)=𝒟×X`, the
domain-equation half being Exercise 3.16's `iter_isomorphic`; see the dated checkpoint at the end).
**Exercise 6.19 Part A is COMPLETE** (`Exercise619.lean`): the concrete `{0,1}*` sum/product
`sumTok`/`prodTok` and their *"correct up to isomorphism"* results `sumTok_iso_sum`,
`prodTok_iso_prod` (see the dated checkpoint at the end). **Part B is COMPLETE**
(`Exercise619PartB.lean`): the functor algebra `FExpr` (constants/identity/sum/product over the fixed
token type `{0,1}*`), with `FExpr.map_id`/`map_comp`/`map_isStrict` (functors), `FExpr.map_mono` +
`FExpr.map_continuous` (continuous on maps = approximable in `f`), `FExpr.obj_subsystem` (monotone on
domains) and `FExpr.obj_continuous` (continuous on domains); see the dated checkpoint at the end.
**Theorem 6.16 is COMPLETE** (`Theorem616.lean`,
`trianglelefteq_of_isInitial`). **Exercise 6.20 is COMPLETE** (`Exercise619PartB.lean`):
`λΓ. tok(T({Γ}))` is continuous on `{Γ ∣ Λ∈Γ}` (`mFun`/`mFun_mono`/`mFun_continuous`), its Kleene
fixed point gives `Γ=tok(T({Γ}))` (`exists_tok_fixedPoint`) and `{Γ}◁T({Γ})`
(`exists_singleton_subsystem`), so Thm 6.14 applies; see the dated checkpoint at the end.
**Lemma 6.15 is COMPLETE**
(`Lemma615.lean`, the converse of Prop 6.12: a projection pair `i,j` with `j∘i=I_D`, `i∘j⊆I_E`
between systems over *possibly different* token types ⟹ `D ⊴ E`). **Theorem 6.14 is COMPLETE** (existence *and* uniqueness/initiality —
`Theorem614.lean`). `key_rho`, the `gₙ=g∘ρₙ` recursion,
`g`-independence and initiality-among-strict-algebras all build green and choice-free.
**Definition 6.13 is now DONE** (`Definition613.lean`, the
functor predicates *monotone on domains* `D◁E ⟹ T(D)◁T(E)` with `i,j` carried to `T(i),T(j)`, and
*continuous on domains* `λD.T(D)` on `{D∣D◁E}` approximable = preserves directed unions of
subsystems) — see the checkpoint at the end of this file. **Proposition 6.12 is also DONE**
(`Proposition612.lean`, the projection pair `i,j` from `D◁E`). **Proposition 6.11**
(`Proposition611.lean`, the subsystems `{D ∣ D ◁ E}` form a domain), **Definition 6.10**
(`Definition610.lean`, the subsystem relation `D ◁ E`) and **Theorem 6.9** (`Theorem69.lean`) are
also DONE.

## Where things stand

- **`lake build Domain` is green, zero `sorry`s** (≈3082 jobs). **Lecture VI's categorical spine is
  now formalized** — see the "Lecture VI" section below. **Theorem 5.6 is now complete
  end-to-end**: `Theorem56Full.lean` proves *every partial recursive function is λ-definable*
  (`partrec_lamDef`) against Mathlib's `Nat.Partrec'`, plus Scott's 1-ary corollary `partrec_one`.
- **Lecture I (43), Lecture II (22), Lecture III (29) = 94 numbered results/exercises are Pass.**
  Lecture III is now **complete end-to-end**: the spine (Def 3.1 → Thm 3.13) *and* every §3 exercise
  (3.14–3.28).
- **Lecture IV spine is Pass.** Theorems 4.1/4.2 are in `Domain/Neighborhood/Theorem41.lean`
  (`fixElement`, `fixMap`, both choice-free; only `fixMap_unique` uses `Classical.choice` via the
  permitted `ext_of_toElementMap`); Example 4.3 (`Example43.lean`), Example 4.4 (`Example44.lean`),
  and Definition 4.5 + Theorem 4.6 (`Theorem46.lean`). The §4 exercises 4.7–4.25 are all Pass —
  **the most recent work (4.21–4.25) is detailed in the "What's next" section below.**
- **Lectures IV–VIII are fully transcribed** in `sources/PRG19_vision.md` (152/152 OCR pages,
  ≈5365 lines) **and inventoried** in `arxiv.md` §4.2.IV–VIII as Goal Lists. **Lecture IV is now
  complete end-to-end**: the spine (Theorems 4.1/4.2, Examples 4.3/4.4, Definition 4.5 + Theorem 4.6)
  *and* **every §4 exercise (4.7–4.25)** are **Pass**. **Lecture V is now COMPLETE end-to-end**
  (including all of Exercise 5.16's Thue–Morse `t` follow-up — see next section); **Lecture VI's
  Example 6.1 (the tree algebra `D`<sup>§</sup> + the domain equation D<sup>§</sup> ≅ D + (D<sup>§</sup>×D<sup>§</sup>)), Example 6.2
  (the concrete equations `B ≅ B + B` and `C ≅ {{Λ}} + C + C`, the generalization `A ≅ Aⁿ + Aⁿ`, and
  the eventually-periodic-tree ↔ regular-event aside via Myhill–Nerode), and categorical
  spine (Defs 6.3–6.5, Props 6.6–6.7) and Definition 6.8 (continuous on maps) are now Pass**; the rest of VI and VII–VIII are `—`.
  Pages 108–111 were re-OCR'd to fix a page-order scramble
  (Thm 6.14 tail, Lemma 6.15, Thm 6.16, Exercises 6.17–6.20 now in correct order).

### Lecture VI — categorical spine 6.3–6.7 + Definition 6.8 (most recent work)

Lecture VI ("Introduction to domain equations") is heavily category-theoretic. The cleanly tractable,
self-contained chunk — the abstract categorical vocabulary plus the two abstract propositions — is now
formalized. All three modules build alone, are **choice-free** (`#print axioms` reports *no* axioms at
all), and are imported from `Domain.lean`; the full `Domain` build is green.

- **`Definition63.lean`** — the abstract framework, generic over an arbitrary `Category` (a bespoke
  lightweight `class Category` with `Hom`/`id`/`comp` + the three laws; `⊚` is the composition
  notation, "`g` after `f`", matching `ApproximableMap.comp`).
  - **Definition 6.3** — `Endofunctor` (`obj`/`map` + `map_id`/`map_comp`). Named `Endofunctor`
    (not `Functor`) to avoid shadowing Lean core's `Functor`.
  - **Definition 6.4** — `TAlgebra T` (`carrier`, `str : T(carrier) → carrier`) and `AlgHom A B`
    (`hom` + the commuting square `comm : hom ⊚ A.str = B.str ⊚ T.map hom`). Helpers `AlgHom.id`,
    `AlgHom.comp` (the `T`-algebras form a category) with `@[simp]` projections `id_hom`/`comp_hom`.
  - **Definition 6.5** — `IsInitial A` (data: `desc B : AlgHom A B` for every algebra + `uniq`), and
    `Iso X Y` (mutually inverse morphisms).
  - **The concrete category** `instance : Category DomainObj` where `DomainObj` bundles a token type
    with a `NeighborhoodSystem`; `Hom = ApproximableMap`, laws = Theorem 2.5 (`idMap_comp`/
    `comp_idMap`/`comp_assoc`). This witnesses that the abstract definitions are non-vacuous (Scott's
    prose before 6.3: the systems "form quite an interesting category").
- **`Proposition66.lean`** — **Proposition 6.6**: any two initial `T`-algebras are uniquely
  isomorphic. `comp_desc_eq_id` (the round-trip `g∘f` equals `id` by uniqueness), `initialIso`
  (the `Iso` on carriers), `iso_hom_unique` (the realising homomorphism is the only one).
- **`Proposition67.lean`** — **Proposition 6.7 (Lambek's lemma)**: the structure map `i : T(D)→D` of
  an initial algebra is an isomorphism. `tStr` (the algebra `(T D, T i)`), `strHom` (`i` is a
  homomorphism `(TD,Ti)→(D,i)`), `str_comp_desc` (`i∘j = id_D`), and the capstone `lambek` (the `Iso
  (T.obj D) D`, with `j∘i = id` via functoriality `T(i∘j)=T(id)` + the `j` homomorphism square — done
  by an explicit `calc`, since `rw [j.comm]` failed to match on implicit composition args).
- **`Definition68.lean`** — **Definition 6.8**: a functor `T` is *continuous on maps* when, for all
  domains `D, E`, the induced `λf. T(f)` on Scott's **strict** function space `(D →⊥ E)` is
  approximable. Stated verbatim over strict maps by reusing `Exercise510.lean`'s `strictFun`/
  `StrictMap`/`strictFunEquiv` (the `(D →⊥ E)` domain, whose elements are exactly the strict maps).
  "is approximable" = ∃ a representing `Φ : ApproximableMap (strictFun D E) (strictFun (TD) (TE))`
  with `(toStrictMap (Φ.toElementMap (toStrictFilter f))).1 = T.map f.1` (Prop 2.2 / Thm 3.10).
  `ContinuousOnMaps.isStrict_map` shows this forces `T` to preserve strictness (LHS is a `StrictMap`'s
  underlying map), so `T` restricts to Scott's strict subcategory. `continuousOnMaps_id` (witness via
  `idEndofunctor` + `idMap`) gives non-vacuity. **Choice-free** `[propext, Quot.sound]`.

**Theorem 6.9 — DONE (`Theorem69.lean`, fully choice-free `[propext, Quot.sound]`).** *Statement:* if
`T` is continuous on maps and `D ≅ T(D)` (so `D` is a `T`-algebra via `i : T(D) → D`, inverse
`j : D → T(D)`), then for any `T`-algebra `k : T(E) → E` (taken **strict**, as a morphism of Scott's
strict category) there is a homomorphism `h : D → E`. Formalized as
`nonempty_algHom_of_continuousOnMaps … : Nonempty (AlgHom ⟨D, iso.hom⟩ B)` (Scott's *existence*).
*How:* the design point resolved in favour of the **strict** function space `(D →⊥ E)` throughout
(matching Def 6.8). A homomorphism satisfies `h = k ∘ T(h) ∘ j`, the least fixed point of
`Op = homOp ∘ Φ` on `strictFun D.sys E.sys`:
- `Φ` is Def 6.8's witness that `λf. T(f)` is approximable (`(toStrictMap (Φ.toElementMap (toStrictFilter
  f))).1 = T.map f.1`);
- `homOp` (Ex 2.8 `ofMono`) is the post/pre-composition `g ↦ k ∘ g ∘ j : (T(D)→⊥T(E)) → (D→⊥E)`;
  `homOpComp` is the strict composite (strictness of `k∘g∘j` needs `j` strict — `isStrict_of_comp_eq_id`
  from `j∘i=I`, any split iso preserves `⊥` — and `k` strict by hypothesis), and the **action lemma**
  `homOp_apply_filter : homOp(f̂) = (k∘f∘j)^` is proved by reducing to single step nbhds `[X,Z]` **via
  `strictFunEquiv` injectivity** (so the only "finite factoring" needed is `N := [Y₁,Y₂]` — no list
  induction);
- `Op.fixElement` (Thm 4.1) represents `h`; `toElementMap_fixElement` + `Φ`'s eq + `homOp_apply_filter`
  give `h = k∘T(h)∘j`, rearranged via `j∘i=I` (`comp_assoc`, `comp_idMap`) into the `AlgHom` square
  `h∘i = k∘T(h)`. The `Nonempty` conclusion lets `Φ` be pulled from the `Prop`-valued `ContinuousOnMaps`
  by `Exists.elim` — **no `Classical.choice`**.
*New reusable helpers (top of `Theorem69.lean`):* `isStrict_comp`, `isStrict_of_comp_eq_id`,
`comp_mono_gen` (general-arity composition monotonicity), `toStrictMap_mono`, `toStrictFilter_mono`,
`toStrictFilter_toStrictMap` (the left-inverse mirror of `toStrictMap_toStrictFilter`).
*Pitfall:* `rw [toStrictFilter_toStrictMap]` can fail to fire under `set`-introduced let-vars (implicit
`V₀/V₁` metavariables) — close with `exact (toStrictFilter_toStrictMap _).symm` instead.

**Pitfalls (Lecture VI):** (1) name the functor `Endofunctor`, not `Functor` (core clash). (2) For the
`AlgHom.comp` commuting square, the rewrite chain is
`assoc, α.comm, ←assoc, β.comm, assoc, ←map_comp`. (3) `rw [(desc …).comm]` can fail to find its own
LHS pattern (implicit object-args of `⊚` elaborate differently); use the equation as the first step of
a `calc` instead. (4) `(tStr A).str` is *defeq* but not *syntactically* `T.map A.str` — bridge with a
`rfl` `calc` step or `show`.

### Lecture VI — Example 6.1, the tree algebra `D`<sup>§</sup> and its domain equation (most recent work)

**`Example61.lean` — DONE, fully choice-free `[propext, Quot.sound]`** (even the equation iso and the
order-injection lemmas; no `ext_of_toElementMap` needed). Scott's `D`<sup>§</sup> over a fixed domain `D`:
- **Tokens** `Γ = {1,2}* 0 Δ` modelled as `List Bool × α` (`true=1`, `false=2`), master
  `Gamma D = {t ∣ t.2 ∈ Δ}`. Three set embeddings `embZero X = 0X`, `embL P = 1P`, `embR Q = 2Q`,
  `embPair P Q = 1P ∪ 2Q` (set-builder, *not* `Set.image` — membership lemmas are `Iff.rfl`), with a
  tight intersection/subset/injectivity/disjointness API (`embPair_inter`, `embPair_subset`,
  `embZero_inter_embPair`, `embPair_injective`, …).
- **The system** `Dsharp D hD` (`hD : ∀ X, 𝒟.mem X → X.Nonempty` = Scott's standing `∅∉𝒟`). Its `mem`
  is the inductive `MemS D` (least family with `Γ`, `0X`, `1P∪2Q`). The crux **`memS_inter`** is
  Scott's "induction on the number of steps to put `X`,`Y` into `𝒟`<sup>§</sup>": cross cases collapse to `∅`,
  killed by `memS_nonempty` (every member non-empty, the only use of `hD`); the `0A∩0B` case uses
  `𝒟`'s own closure, the `(1P∪2Q)∩(1P'∪2Q')` case recurses. Inversions `memS_embZero_inv`/
  `memS_embPair_inv` recover the constructor from the shape (the `generalize … cases` idiom).
- **The domain equation** `dsharp_domain_equation : Dsharp D hD ≅ᴰ sum D (prod (Dsharp D hD)
  (Dsharp D hD)) hD (prod_dsharp_nonempty D hD)` — i.e. D<sup>§</sup> ≅ D + (D<sup>§</sup> × D<sup>§</sup>) against the project's
  `+` (Ex 3.18) and `×` (Def 3.1). Built as the explicit order-iso `dsharpEquiv` from the filter maps
  `toS` (forward) / `fromS` (inverse), inverse laws `fromS_toS`/`toS_fromS`, and `map_rel_iff'`. The
  three-way branch (⊥ / `0`-branch / pair-branch) is forced by non-emptiness; sum-side inversions
  `sum_mem_inj₀_inv`/`sum_mem_inj₁_inv` and the helper iffs `toS_mem_inj₀`/`toS_mem_inj₁`/
  `fromS_mem_embZero`/`fromS_mem_embPair` keep the inverse-law proofs short.
- **Injections** `inSharp` (x<sup>§</sup> = {Γ}∪{0X∣X∈x}, `inSharp_le_iff`) and `pairSharp`
  (`⟨x,y⟩ = {Γ}∪{1P∪2Q∣P∈x,Q∈y}`, `pairSharp_le_iff`) — Scott's *isomorphic injections*
  λx.x<sup>§</sup> : D→D<sup>§</sup> and λx,y.⟨x,y⟩ : D<sup>§</sup>×D<sup>§</sup>→D<sup>§</sup>; `⊥ = {Γ}` is the system's own `bot`.
- **Pitfalls (re)learned:** (1) section `variable`s used *only in a proof body* (e.g. `hD` in the
  `≠`-shape lemmas whose statement mentions only `D`) are **not** auto-included — add `include hD`.
  (2) `Set.notMem_empty` (not `not_mem_empty`). (3) feeding a member `(p',a)∈P` to `hP : P ⊆ Gamma D`
  when the goal is `(p,a)∈Gamma D` fails elaboration order (it unifies `?x` from the goal) — bind
  `have h := hP …; exact h` so the membership is elaborated first and `exact` closes by defeq.

**What's NOT done in VI (good stopping point):** the
*initial-algebra/homomorphism* g : D<sup>§</sup> → E part of Example 6.1 (the `out`/`proj`/`atom` predecessors
and the fixed-point `g` — connects `D`<sup>§</sup> to the 6.4 `T`-algebra spine, but needs the `cond`-style
recursion over `D`<sup>§</sup>), and everything from Definition 6.8 onward (functors continuous on maps, Theorem
6.9, the subsystem relation `D◁E` and its lattice 6.10–6.12, monotone/continuous functors 6.13, the
existence Theorem 6.14, Lemma 6.15, Theorem 6.16, and Exercises 6.17–6.29) — these need substantial new
domain-theoretic machinery (continuous functors, the subsystem lattice, projection pairs, and the
iterated-functor colimit construction).

### Lecture VI — Example 6.2, the domain equations `B ≅ B+B`, `C ≅ {{Λ}}+C+C`, the generalization `A ≅ Aⁿ + Aⁿ`, and the eventually-periodic ↔ regular aside (most recent work)

Scott's Example 6.2 exhibits his two running concrete domains as solutions of domain equations. Both
modules build alone, are **fully choice-free** (`#print axioms` reports `[propext, Quot.sound]` for the
systems, the order-isos, and the equation theorems), and are imported from `Domain.lean`; the full
`Domain` build is green.

- **`Example62.lean` — `B ≅ B + B`** (`B` = `ExampleB`, binary streams over `Str = List Bool`).
  - The single-bit prepend `embBit b X = bX` (`= prepend [b] X`) with its API: `embBit_cone`,
    `embBit_inter`, `embBit_inter_ne`, `embBit_injective`, `memB_embBit`, and the inversion
    `memB_embBit_inv` (if `embBit b W ∈ B` then `W ∈ B` — this fixes the type-mismatch when feeding
    `x.sub` into the sum's `inter_mem`). `B_nonempty` (every `B`-nbhd is non-empty).
  - The neighbourhood-shape classifier `memB_cases`: any `B`-nbhd is the master `Σ*` (`Set.univ`),
    `embBit false X`, or `embBit true Y`. This three-way split drives the iso.
  - `BB := sum B B B_nonempty B_nonempty` (the project's `+`, Ex 3.18, over `Option (Str ⊕ Str)`).
    Inversions `sum_mem_inj0_inv`/`sum_mem_inj1_inv`/`sum_mem_nonempty`.
  - The filter maps `toBB : |B| → |BB|` (its `inter_mem` is a 9-case analysis over the three shapes ×
    three shapes) and `fromBB : |BB| → |B|`, mutual-inverse laws `fromBB_toBB`/`toBB_fromBB`, bundled
    as `bbEquiv : |B| ≃o |BB|`; capstone `B_domain_equation : B ≅ᴰ BB`.
- **`Example62C.lean` — `C ≅ {{Λ}} + C + C`** (`C` = `Example44`, finite+infinite binary streams;
  `{{Λ}} = unitSys`, the one-point domain `𝟙`, Exercise 3.15).
  - **The genuine three-way separated sum** `sum3 V₀ V₁ V₂ : NeighborhoodSystem (Option (α ⊕ β ⊕ γ))`
    — built fresh rather than nesting binary `sum`, because `(𝟙 + C) + C` would add a **spurious extra
    bottom** that breaks the iso (`C` has exactly three atoms above its bottom). Tags `t0`/`t1`/`t2`,
    injections `j0`/`j1`/`j2`, master `master3`, with the full disjointness/intersection API
    (`jX_inter_jX`, `jX_inter_jY`, `master3_inter_jX`, `eq_master3_of_subset`, …) and a 16-case
    `inter_mem`. Inversions `sum3_mem_j1_inv`/`sum3_mem_j2_inv`/`sum3_mem_nonempty`.
  - `C`-side helpers: `embBit` reused for `C` (`memC_embBit`/`memC_embBit_inv`, `embBit_singleton`),
    the `{Λ} = {[]}` terminator lemmas (`singleton_nil_inter_embBit`, `singleton_nil_ne_univ`,
    `singleton_nil_ne_embBit`), `C_nonempty`/`unitSys_nonempty`, and the four-way classifier
    `memC_cases`: any `C`-nbhd is the master `Σ*` (`Set.univ`), the terminator `{Λ}`, `embBit false X`,
    or `embBit true Y`.
  - `CC := sum3 unitSys C C …`; the filter maps `toCC : |C| → |CC|` (the `{Λ}` terminator goes to the
    unit summand `j0`, `0X`/`1X` to the two `C` copies `j1`/`j2`; `inter_mem` is the 16-case analysis)
    and `fromCC`, mutual-inverse laws `fromCC_toCC`/`toCC_fromCC`, bundled as `ccEquiv : |C| ≃o |CC|`;
    capstone `C_domain_equation : C ≅ᴰ CC`. **Pitfall:** `fromCC`'s `sub` field has goal `C.mem univ`,
    an `Or` (two constructors) — the anonymous `⟨…⟩` constructor fails; write `Or.inl ⟨[], cone_nil.symm⟩`.
- **`Example62A.lean` — the generalization `A ≅ Aⁿ + Aⁿ`** (Scott's "simple, yet interesting
  generalization of `B`", now done).
  - **`npow V n` — the flat `n`-fold product `Vⁿ`** over `Fin n × β`: neighbourhoods are the proper
    products `prodN X = ⋃_j {j}×X_j` (each `X j ∈ V`), with the API `prodN_inter`/`prodN_subset`/
    `prodN_injective`. `inter_mem` is **componentwise** — there are no tags to disambiguate, so unlike
    the sum it needs **no** non-emptiness. `npow_nonempty` (needs `0<n`, a coordinate to witness).
  - **Scott's domain `A` over `{0,1}*`**: the slot prefix `slotPre i j = i 1ʲ0` with the parsing/
    uniqueness lemmas `slot_list_inj`/`slotPre_inj` (the first `0` after the `1`-run pins down the slot),
    the tag-`i` tuple `embTuple i X = i ⋃_{j<n} 1ʲ0 X_j` and its API (`embTuple_inter`,
    `embTuple_inter_ne` for distinct tags, `embTuple_subset`, `embTuple_injective`, `embTuple_ne`).
    The inductive least family `MemA n` (`univ` ∣ `tuple i X`), `memA_nonempty`/`memA_inter`
    (`tag_eq_of_subset` recovers the tag from a non-empty witness) and the inversion `memA_tuple_inv`,
    packaged as `Asys n hn : NeighborhoodSystem Str` (needs `0<n`).
  - `Apow hn := npow (Asys n hn) n`, `AAsys hn := sum (Apow hn) (Apow hn) …`; the filter maps
    `toAA`/`fromAA` (9-case `inter_mem`, mirroring `Example61.toS`/`fromS`, with `embTuple false X ↦
    inj₀ (prodN X)`, `embTuple true Y ↦ inj₁ (prodN Y)`), mutual inverses, bundled as
    `aaEquiv : |A| ≃o |Aⁿ + Aⁿ|`; capstone `A_domain_equation : Asys n hn ≅ᴰ AAsys hn`. `n=1` recovers
    `B ≅ B+B`. **Fully choice-free** `[propext, Quot.sound]`.
- **`Example62Regular.lean` — eventually-periodic trees ↔ regular events** (Scott's closing aside).
  - Scott's total `+/−`-labelled `n`-ary trees are `Tree n = List (Fin n) → Bool`; `pos a = a []`, the
    subtree selector `select a σ` (Scott's `aσ`, with the recursion `aΛ=a`, `a(iσ)=(aᵢ)σ` and
    `select_append`), and the language `treeLang a = L_a = {σ ∣ pos(aσ)=true}`.
  - The bridge `treeLang_select : L_{aσ} = (treeLang a).leftQuotient σ` identifies the subtree reached
    by reading `σ` with the residual/left quotient ("`a` is the initial state, `aσ` the state after
    reading `σ`"), and `treeLang` is injective. Hence `EventuallyPeriodic a` (`{aσ}` finite) iff
    finitely many left quotients iff regular — `eventuallyPeriodic_iff_isRegular` +
    `isRegular_iff_exists_eventuallyPeriodic`, i.e. **Myhill–Nerode** via Mathlib's
    `Language.isRegular_iff_finite_range_leftQuotient`. (Prop-level; uses `Classical.choice` through
    Mathlib, which is fine for a regularity statement.)

### Lecture V §5 completed (most recent work)

All nine modules build alone, pass the audit, and are imported from `Domain.lean`; the full `Domain`
build is green. Lecture V is interpreted **semantically** inside the approximable-map framework
(closure properties + combinator identities), matching Scott's informal presentation rather than
building a separate λ-syntax.

- **Table 5.5** (`Table55.lean`) — the combinators as approximable maps with value equations: `P₀`,
  `P₁`, `pairC`, `diagC` (`= λx.⟨x,x⟩`), `swapC`, `evalC`, `constC`, `curryC`, `compC` (`= g∘f`,
  `compC_eq_comp`), `funpairC` (`= ⟨f,g⟩`), `fixC` (`= fixMap`). Internal uncurried helpers are
  `compMapTbl`/`funpairMapTbl` (**renamed** from `compMap`/`funpairMap` and `diag→diagC` to avoid
  clashes with `Exercise322.compMap` / `Exercise314.diag` at the `Domain.Neighborhood` namespace).
- **Theorem 5.1** (`Theorem51.lean`) — every typed λ-term denotes an approximable map: closure of the
  interpretation under variables/constants/tuples/application/abstraction.
- **Theorem 5.2** (`Theorem52.lean`) — the β/substitution rule as combinator identities (`beta`,
  `beta_tuple`, `beta_abs`) via `curry`/`eval`.
- **Proposition 5.3** (`Proposition53.lean`) — Bekić: least fixed point of `⟨τ,σ⟩` is
  `⟨!x.τ(x,!y.σ(x,y)), !y.σ(!x.τ(x,y),y)⟩` (`fixElement_paired_eq`).
- **Proposition 5.4** (`Proposition54.lean`) — `λx.!y.τ(x,y) = !g.λx.τ(x,g x)`
  (`pfix_eq_fixElement_recOp`).
- **Exercise 5.7** (`Exercise507.lean`) — multi-variable λ/application from one-variable forms:
  surjective pairing `⟨p₀ z,p₁ z⟩=z`, `uncurry_apply` / `app_two_args` (apply one arg at a time),
  `lam_two_vars` (= `curry`), and the three-variable generalisation `curry₃`.
- **Exercise 5.8** (`Exercise508.lean`) — **combinatory completeness** (bracket abstraction). The
  combinators `I = idMap`, `K = curry(p₀)`, `S = curry(curry(eval∘…))` as elements (`Ielem`/`Kelem`/
  `Selem`) with value equations `I(x)=x`, `K(c)(x)=c`, `S(F)(G)(x)=F(x)(G(x)`. An intrinsically-typed
  syntax `Poly X A` of λ-bodies with one free variable (`var`/`con`/`app`) and a variable-free
  combinator syntax `CL A` (`con`/`app` — application is the *only* mode of combination). `bracket :
  Poly X A → CL (X.arrow A)` is `[x]x=I`, `[x]c=K c`, `[x](f a)=S([x]f)([x]a)`, and the capstone
  `bracket_spec` proves `(bracket t).denote` denotes exactly `λx.t` — turning Table 5.5 around.
  Domains bundled as `Dom` over `Type` (covers `N`/`T`/`C`); fully choice-free (`[propext,
  Quot.sound]`). **Pitfall:** bundling universe-polymorphic systems (`NeighborhoodSystem`/
  `ApproximableMap`) into a `Type u`-polymorphic `Dom` produced unsolvable `max u u` universe
  constraints in the inductives — monomorphise `Dom` to `Type 0`. Also `rw [toElementMap_curry_apply]`
  can fail to match a `toApproxMap`-wrapped curry even when displayed identically (elaboration-order
  term differences); prove via `have h := toElementMap_curry_apply …; … ; exact h` (defeq) instead.
- **Exercise 5.9** (`Exercise509.lean`) — commuting `f∘g=g∘f` ⟹ least common fixed point;
  `f(⊥)=g(⊥) ⟹ fix f = fix g`; `fix f = fix f²`.
- **Exercise 5.11** (`Exercise511.lean`) — D<sup>∞</sup> = iterSys D as stacks: `head`/`tail`/`push` from
  `iterProdIso` with the stack laws (`head_push`, `tail_push`, `push_head_tail`); `diag` by the
  recursion `diag x = push(x,diag x)` with **all components `= x`** (`component_diag`); and `map` by
  recursion with `component_map` (`map(⟨fₙ⟩,x)ₙ = fₙ(x)`). **Fully choice-free** (`[propext,
  Quot.sound]`).
- **Exercise 5.12** (`Exercise512.lean`) — the `while` combinator as the least fixed point of
  `Wop(w) = λx.cond(p x, w(f x), x)`: recursion `whileMap_rec`, the three unfoldings
  `whileMap_true/false/bot`, and leastness `whileMap_least`. `cond` from Exercise 3.26, so the data
  inherits `Classical.choice` only through the truth domain `T` (Example 1.2), exactly as `cond` does.
- **Theorem 5.6** (`Theorem56.lean`) — recursive functions are λ-definable, formalised as the
  constructive heart of Scott's proof over `N` (Example 4.3) and `cond` (Exercise 3.26):
  - **strict starting functions** `λx.cond(zero x, x, x)`: `strictId` (`strictId_natElem`/`_bot`) and
    `strictProj₀` (strict in *both* args: `strictProj₀_natElem`/`_bot_left`/`_bot_right`);
  - **primitive recursion** `primRec f g = !k λx,y.cond(zero x, f y, g(pred x, y, k(pred x, y)))`
    with the scheme equations `primRec_zero` (`h̄(0,m)=f m`), `primRec_succ`
    (`h̄(n+1,m)=g(n,m,h̄(n,m))`), `primRec_bot` (strict);
  - **μ-scheme** `muRec f = !g λx,y.cond(zero(f(x,y)), x, g(succ x, y))`, `muMap = λy.ḡ(0,y)`, with
    `muRec_found`/`muRec_step`/`muRec_bot` and the **capstone** `muMap_eq_least` (least zero of
    `f(·,m)` ⟹ `μ(m) = n₀`, via the `muRec_climb` run-of-positives induction).
  Helper `T_bot_eq : T.bot = botElt` bridges `zeroMap_bot` (lands in `T.bot`) and `cond_bot` (phrased
  with `Example23.botElt`) since `bot` is not reducible. All `cond`-based maps inherit
  `Classical.choice` structurally from `T`, as `cond`/`zeroMap` already do.
- **Theorem 5.6 — the FULL meta-theorem** (`Theorem56Full.lean`, **done, no `sorry`**) — *every
  partial recursive function is λ-definable*, wired against Mathlib's arity-aware inductive predicates
  `Nat.Primrec'`/`Nat.Partrec'` (over `List.Vector ℕ n`), whose constructors are exactly Scott's
  generation grammar.
  - **Universal argument domain** `𝒩 := iterSys N` (`N`<sup>∞</sup>, Exercise 3.16): a `k`-ary function is one
    map `φ : 𝒩 → N` depending only on coordinates `0..k-1`. Builders `optElem`/`argElem`/`vecElem`,
    `ArgLike`, components through `push` (`component_push_zero/succ`).
  - **Spec** `LamDef φ f` (very strict): `defined` (value on totals), `undef` (`⊥` where `f↑`),
    `strict` (`⊥` on any arg-like input with a `⊥` in coords `0..n-1`). Strictifier
    `guard1`/`strictGuardN` (Scott's `cond(zero ·,·,·)` device) makes `strict` automatic via the
    **master constructor** `lamDef_of_inner`.
  - **Primrec' closure** `primrec_lamDef`: `zero`/`succ`/`get` (base), `lamDef_(prim)comp` via
    `tupleMap` + `mem_mOfFn`, and `lamDef_prec` (the `recOp`/`recMap` fixed point with `recMap_eval`
    by induction on the recursion variable).
  - **Partrec' closure** `partrec_lamDef`: `prim` reuses `primrec_lamDef`; `comp` reuses
    `lamDef_comp`; `rfind` is the μ-search `searchMap = fix(findOp)` started at counter `0` by
    `findMap`, with `searchMap_step_found/next`, the `searchMap_climb` capstone (least zero ⟹ value),
    and the **divergence** lemma `searchMap_diverge` — the one genuinely hard step: push evaluation
    through the directed sup `fix = ⊔ₙ Sⁿ(⊥)` (Thm 4.2(iii) `fixElement_eq_iSupDirected` +
    continuity `toElementMap_iSupDirected` via `evalAt`), then show every approximant is `⊥` along the
    no-zero trace (`iterVal_bot`, with helper `toApproxMap_bot`).
  - **Scott's 1-ary corollary** `partrec_one`: any partial recursive `h : ℕ →. ℕ` is denoted by a
    single `τ : N → N` correct on values, divergent where `h↑`, and strict (`oneArg` inject + the
    three `LamDef` clauses). Axiom profile `[propext, Classical.choice, Quot.sound]` — identical to the
    `Theorem56` baseline (choice enters only via the flat-domain `zeroMap`/`cond` primitives and
    Mathlib's `Nat.rfind`; all combinator *data* is choice-free).

- **Exercise 5.10** (`Exercise510.lean`) — the **smash product** `D₀⊗D₁`, the **strict function
  space** `D₀→⊥D₁`, and the **adjunction** between them. Three pieces:
  - `smash V₀ V₁ : NeighborhoodSystem (α ⊕ β)` — neighbourhoods are the master `Δ₀∪Δ₁` together with
    the *proper* product nbhds `X∪Y` (both factors `≠` their masters); the strict pairing
    `smashPair x y` collapses to `⊥` whenever a coordinate is `⊥` (`smashPair_eq_bot_iff`), realising
    Scott's bottom-gluing. Key `inter_mem` case: two proper nbhds with a consistency witness `Z`
    force `Z` proper (`inter_ne_master_*`).
  - `strictFun V₀ V₁ : NeighborhoodSystem (StrictMap V₀ V₁)` — tokens are the **strict** approximable
    maps (`IsStrict f ↔ f(⊥)=⊥`), nbhds are non-empty finite intersections of step sets `sstep`.
    `strictFunEquiv : |D₀→⊥D₁| ≃o StrictMap` is the strict mirror of Theorem 3.10; strictness is
    automatic because `[Δ₀,Y]` with `Y≠Δ₁` is empty, hence never a nbhd.
  - `smashCurryEquiv : StrictMap (smash V₀ V₁) V₂ ≃o StrictMap V₀ (strictFun V₁ V₂)` — the adjunction,
    via `smashCurryMap`/`smashUncurryMap` and the decisive computation `section_uncurry_rel`
    (`g(⟨x,y⟩⊗) = curry⊥(g)(x)(y)`, with boundary collapse handled by strictness). **Axioms:** all
    *data* (`smash`, `strictFun`, `smashCurryMap`, `smashUncurryMap`) and `strictFunEquiv` are
    choice-free `[propext, Quot.sound]` (the `⊥`-collapse uses one-directional choice-free lemmas
    `smashPair_bot_left`/`_right`); `Classical.choice` enters only the `smashCurryEquiv` *proof* via
    the genuinely-classical `X=Δ₀?`/`Y=Δ₁?` boundary case split.

- **Exercise 5.13** (`Exercise513.lean`) — the one-one pairing `num : N × N → N`. `num n m =
  (n+m)(n+m+1)/2 + m` (Cantor's diagonal enumeration via triangular numbers `tri`), verifying Scott's
  three recurrences (`num_zero_zero`, `num_succ_right`, `num_succ_left`) and one-one-ness
  (`num_injective`). In fact a **bijection** `numEquiv : ℕ × ℕ ≃ ℕ`, built **choice-free** from an
  explicit inverse `unnum` (iterate the diagonal walk `nextCell` from `(0,0)`; `numP_nextCell`,
  `numP_unnum`, then `unnum_numP` by injectivity). Power-set domains modelled as `(Set A, ⊆)` (per
  Exercise 4.17); the generic order-iso `setCongr : (α ≃ β) → (Set α ≃o Set β)` (choice-free — proves
  `map_rel_iff'` by hand to avoid the choice-y `Set.image_subset_image_iff`) gives the three
  isomorphisms `PN_orderIso_PNN` (`P N ≅ P(N×N)` via `numEquiv`), `PN_orderIso_prod`
  (`P N ≅ P N × P N` via `Equiv.natSumNatEquivNat` + Mathlib's `Set.sumEquiv`), and
  `PNN_orderIso_prod`. **Fully choice-free** (`[propext, Quot.sound]`). **Pitfall:**
  `Nat.even_mul_succ_self` is proved by `grind` (pulls `Classical.choice`) — proved `2 ∣ k(k+1)` by
  hand (`two_dvd_mul_succ`) to keep `tri`/`num`/`numEquiv` choice-free.

- **Exercise 5.14** (`Exercise514.lean`) — the Scott **`Pω` graph model**. The coding device is the
  **tag** `tag [n₀,…,n_{k-1}] m = [n₀+1,…,n_{k-1}+1,0,m]`, built from 5.13's `num`
  (`tag [] m = num 0 m`, `tag (n::ns) m = num (n+1) (tag ns m)`); it is a **bijection**
  `(List ℕ)×ℕ ≃ ℕ`: `tag_injective` (induction + `num_injective`) and `tag_surjective` (strong
  induction on the value, decreasing via `num_succ_left_gt : b < num (n+1) b`). With `entries ns`
  the finite set of list entries, `Fun u x = {m ∣ ∃ ns⊆x, tag ns m ∈ u}` and
  `Graph f = {tag ns m ∣ m ∈ f(entries ns)}`, and `IsApprox f` (monotone + finite-approximation):
  `Fun_Graph` (`fun∘graph = λf.f` for continuous `f`), `id_le_Graph_Fun` (`graph∘fun ⊇ λx.x`,
  genuinely `⊇`), and `Fun_isApprox` (every `Fun u` is approximable). `Pω = (Set ℕ, ⊆)` per 4.17/5.13.
  **Fully choice-free** (`[propext, Quot.sound]`). **Pitfall:** phrasing `IsApprox` with Mathlib's
  `Monotone f` (over `Set ℕ`) pulls `Classical.choice` — the `≤` resolves through the
  `CompleteLattice (Set _)` instance, whose construction uses choice — so *any* lemma merely
  *mentioning* such an `IsApprox` is choice-tainted. Phrase monotonicity as an explicit
  `∀ ⦃x x'⦄, x ⊆ x' → f x ⊆ f x'` (`⊆` = `Set.Subset`, defeq to `≤` but instance-free) to stay
  choice-free.
- **Exercise 5.15** (`Exercise515.lean`) — the **free-semigroup powerset + Arden's lemma**. Works in
  the **Kleene algebra** `(Set S, ∪, ·, ∅, {1})` for *any* monoid `S` (`open Pointwise`). `star z = ⋃ₙ zⁿ`
  is defined by an explicit recursion `kpow` (not `⋃`) with `star_eq : z* = Λ ∪ z·z*`. The engine is
  **Arden's lemma** `arden : lfpSet (λw. z·w ∪ v) = z*·v` (least solution of `w = z·w ∪ v`), proved
  *without* `Monotone`: the `⊆` half is `lfpSet_least` applied to the fixed point `star_mul_isFixed`,
  the `⊇` half is `star_mul_subset_prefixed` (induction `zⁿ·v ⊆ w₀` into the lfp intersection).
  **(1)** `part1`: `lfpSet (λz.{e}·z ∪ {e'}) = star{e}·{e'}`, with `mem_star_singleton` showing
  `star{e} = e* = {Λ,e,e²,…}`; specialised to `S = FreeMonoid Bool = {0,1}*` (`part1_freeMonoid`).
  **(2)** David Park: the explicit `parkX = (a ∪ b·a*·b)*·(c ∪ b·a*·d)`, `parkY = a*·(b·x₀ ∪ d)`
  *solve* the system (`park_solves`, via `star_mul_isFixed` + Kleene-algebra `simp`) and are *below*
  every solution (`park_least`, Gaussian elimination: solve the 2nd eq for `y` by `arden`, substitute,
  apply `arden` again) — i.e. the **least** solution. **Fully choice-free** (`[propext, Quot.sound]`).
  **Major pitfall (this toolchain):** Mathlib's `Set`-level `mul_assoc`/`Set.union_mul`/`Set.mul_union`/
  `Set.singleton_mul_singleton`, the order lemmas `Set.subset_iUnion`/`Set.iUnion_subset`, `Set`-power
  (`pow_succ'` on `Set`), `Submonoid.mem_powers_iff`, and `Monotone`-over-`Set` **all pull
  `Classical.choice`** (they route through `Set.image2`/`CompleteLattice` choice machinery). The
  *membership* iffs (`Set.mem_mul`/`mem_union`/`mem_one`/`mem_singleton_iff`) and *element-level*
  monoid lemmas are choice-free. So reprove the needed Kleene slice (`smul_assoc`/`sunion_mul`/
  `smul_union`) by membership `ext`, define `star` by recursion, and avoid `Monotone`/`⋃`-order
  lemmas/`Submonoid.powers` entirely.

**Lecture V exercises 5.7–5.16 are formalized — Lecture V is now COMPLETE end-to-end, including all of
Exercise 5.16's Thue–Morse `t` follow-up (see the next two subsections).** Exercise
5.16's `neg`/`merge`/`d` core (`Exercise516.lean`):

- **`tailMap : C → C`** (`tail(bx)=x`, `tail(Λ)=⊥`, Example 4.4's "left to the reader" item) via
  `Exercise419.liftC` (`tail_hcone`/`tail_hsing`).
- **`negMap : C → C`** (`neg(0x)=1·neg(x)`, `neg(1x)=0·neg(x)`) solved in closed form via `liftC`:
  `neg(σ⊥)=(flip σ)⊥`, `neg(σ)=flip σ` with `flip = List.map not`. Recursion eqs `neg_cons_false`/
  `neg_cons_true` (it is *the* solution) and the involution **`negMap_negMap : neg(neg x)=x` for all
  `x∈|C|`**. The continuity argument flagged in the old plan was **avoided**: instead of "agreement on
  the sup-dense basis + continuity", use Exercise 2.8's `eq_of_toElementMap_principal` — a map is
  determined by its values on the finite elements `σ⊥`, `σ`, so `neg∘neg=id` reduces to `flip∘flip=id`
  on those (helper `map_ext_C`). Much shorter than the directed-sup route.
- **`dMap : C → C`** (`d(0x)=00·d(x)`, etc.) via `liftC` (`d(σ)=double σ`).
- **`mergeMap : C × C → C`** (`merge(εx,δy)=ε·δ·merge(x,y)`) built **directly** as an `ApproximableMap
  (prod C C) C` from an explicit interleave value function `mergeVal` on tagged strings `(b,σ)`
  (`b`=total/partial flag), with output element `mergeElem`. **Scott's boundary trouble resolved**: the
  *only* monotone convention is `merge(Λ,y)=Λ`, `merge(⊥,y)=⊥`, and `merge(εx,y)=ε⊥` once `y` runs out
  (NOT `merge(εx,Λ)=Λ`, which breaks monotonicity since `⊥⊑Λ` but `ε⊥⋢Λ`). The crux is the
  monotonicity lemma `mergeVal_SLe`/`mergeElem_mono` (order `SLe` on tagged strings, `shapeElem_le_iff`).
  Value-on-pairs lemma `mergeMap_pair` (the product analogue of `liftC_strBot`), product
  extensionality `prodMap_ext` (via `prod_principal_pair`), recursion eq `mergeMap_cons` (all `x,y`),
  and **`mergeMap_diag : merge(x,x)=d(x)`** (only needs the *diagonal* principals — `mergeVal_diag`).
- **Choice:** all *data* (`tailMap`/`negMap`/`dMap`/`mergeMap`) is `[propext, Quot.sound]`; the map
  equalities pull `Classical.choice` only via `eq_of_toElementMap_principal` (the sanctioned exception).

### Exercise 5.16 follow-up — the Thue–Morse sequence `t` (DONE)

The whole Thue–Morse follow-up is now formalized across two modules. **No `sorry`; full `Domain` build
green (≈3064 jobs).**

**`Exercise516ThueMorse.lean` — Step 0 + property (a) (digit-sum mod 2).** Fully choice-free even at the
`Prop` level (`[propext, Quot.sound]`).
- **Step 0.** `tmOp = Φ = (consMap false).comp (mergeMap.comp (paired negMap tailMap))`,
  `tElt = t = tmOp.fixElement`, and the unfolding `tElt_unfold : 0·merge(neg t, tail t) = t`.
- **The bridge (the real idea).** The fixed-point approximants are exactly the iterates of the
  **Thue–Morse morphism** `expand` (`0 ↦ 01`, `1 ↦ 10`): `iterElem_succ_eq : Φᵏ⁺¹(⊥) = (expandᵏ[0])⊥`.
  The crux `tmOp_strBot_expand` shows `Φ` *is* `expand` on a partial element `(0σ)⊥` (computed from
  `mergeMap_pair` + the interleave lemma `weave_head`: `merge((flip σ)⊥,(tail σ)⊥) = (expand σ minus
  head)…`). The key shortcut that makes the bridge work: `step σ = false :: weave σ` equals `expand σ`
  **whenever `σ` starts with `0`**, and every approximant string does.
- **The parity bit-function** `tm n := (Nat.bits n).foldr xor false` (= ⊕ of the binary digits of `n`),
  with recurrences `tm_zero`, `tm_two_mul : tm(2n)=tm n`, `tm_two_mul_add_one : tm(2n+1)=¬tm n`
  (proved from Mathlib's `Nat.bit0_bits`/`bit1_bits`). The prefix `tmList n = (List.range n).map tm`,
  and `expand_iterate_eq : expandᵏ[0] = tmList(2ᵏ)` (via `expand_tmList : expand(tmList m)=tmList(2m)`,
  which is the even/odd recurrence in disguise).
- **Property (a)** = `tElt_mem_cone_iff : tElt.mem (cone σ) ↔ σ = tmList σ.length` — a string is a prefix
  of `t` *iff* it is the length-matched Thue–Morse parity prefix. So the `n`-th digit of `t` is `tm n`,
  Lambek's digit-sum-mod-2 description. Corollary `tElt_digit : (tmList n ++ [tm n])⊥ ⊑ t`.

**`Exercise516Overlap.lean` — property (b), overlap-freeness.** A self-contained combinatorics-on-words
theorem (no domain theory; `Prop`-level so `Classical.choice` is fine).
- `Overlap i p := 1 ≤ p ∧ ∀ k ≤ p, tm(i+k)=tm(i+p+k)` (a factor of length `2p+1` with period `p`).
- Base facts: `odd_of_consec_eq` (`tm x = tm(x+1) ⟹ x` odd, since `tm(2m)≠tm(2m+1)`) and
  `no_three_consec` (no three equal in a row — the period-1 case).
- **`no_overlap : ∀ i p, ¬ Overlap i p`** by strong induction on `p`: **even `p=2q`** contracts to a
  period-`q` overlap (subsample even/odd positions, `tm_two_mul`/`tm_two_mul_add_one`); **odd `p≥5`**
  forces a run of three equal symbols (relations at `k=0..4`); the corner **`p=3`** is a direct
  4-relation `Bool` contradiction; **`p=1`** is `no_three_consec`.
- Scott's literal cube form: `no_cube` (no `a·a·a` in `tm`, since a cube is an overlap) and
  **`tElt_cube_free : a ≠ [] → ¬ (u·a·a·a)⊥ ⊑ t`** (`t ≠ u·a·a·a·v`), via `tElt_mem_cone_iff` + the
  bit-reading lemma `tmList_getElem?` + the periodicity lemma `append_three_period`.

**Mathlib reality check (still accurate, mathlib `v4.30.0`):** there is **no** `ThueMorse` /
combinatorics-on-words development to reuse; `tm` was built on `Nat.bits` (`bit0_bits`/`bit1_bits`),
and property (b) was proved entirely from scratch.

**Available API (all verified, in `Exercise516.lean`):** `negMap`/`negMap_strBot`/`negMap_strElem`,
`tailMap`/`tailMap_strBot`/`tailMap_strElem`/`tailMap_consMap_strElem`, `mergeMap`/`mergeMap_cons`
(the recursion `merge(εx,δy)=ε·δ·merge(x,y)`)/`mergeMap_pair`/`mergeMap_diag`, `dMap`, `consMap`
(Example 4.4), `Theorem41.fixElement`/`toElementMap_fixElement`/`fixElement_eq_iSupDirected`, and the
`Example44`/`ExampleB` element/prefix lemmas. Thue–Morse-side API now in `Exercise516ThueMorse.lean`
(`tmOp`/`tElt`/`expand`/`tm`/`tmList`, `tElt_mem_cone_iff`) and `Exercise516Overlap.lean`
(`Overlap`/`no_overlap`/`no_cube`/`tElt_cube_free`).

<details><summary>Original 5.16 formalization plan (superseded — kept for reference)</summary>

### Exercise 5.16 — formalization plan (`neg`/`merge` on `C`; the Thue–Morse sequence)

**Statement.** On `C` (Example 4.4, finite+infinite binary sequences): give fixed-point definitions of
`neg : C → C` (`neg(0x)=1·neg(x)`, `neg(1x)=0·neg(x)`) and `merge : C × C → C`
(`merge(εx,δy)=ε·δ·merge(x,y)`); prove `neg(neg x)=x`, `merge(x,x)=d(x)` (`d` = the bit-doubling map of
4.4), and study `t = 0·merge(neg t, tail t)` (its `n`-th digit = digit-sum-of-`n`-in-binary mod 2 — the
**Thue–Morse** sequence, Lambek's suggestion — and `t` is overlap-free: `t ≠ u·a·a·a·v`, `a ≠ Λ`).
Suggested module `Exercise516.lean`, `import Domain.Neighborhood.Exercise419`.

**Available API (verified) — and a correction.** Unlike 5.14/5.15 this exercise lives entirely in the
**approximable-map / neighborhood framework** (no raw `Set` pointwise algebra), so the `Classical.choice`
taints discovered in 5.14/5.15 (`Set` `mul_assoc`/`union_mul`/`subset_iUnion`/`Monotone`-over-`Set`/
`Submonoid.powers`) **do not apply here**. What actually exists to reuse:
- `Exercise419.liftC V coneVal singVal hcone hsing : ApproximableMap C V` — the head-test combinator
  (a map out of `C` fixed by its values `coneVal σ` on `σ⊥` and `singVal σ` on `σ`); **choice-free
  data**, with computation rules `liftC_strBot`/`liftC_strElem`. The tests are `Exercise419.emptyMap`/
  `zeroMap`/`oneMap : ApproximableMap C T` (note: named `…Map`, **not** `empty`/`zero`/`one`).
- `Exercise326.cond V : ApproximableMap (prod T (prod V V)) V` — the conditional (instantiate at `V=C`);
  `condT_bot` (`cond(⊥,x,y)=⊥`) is in Exercise419.
- `Example44`: `C`, `consMap b : C → C` (`consMap_strElem`/`consMap_strBot`), `strElem`/`strBot`,
  `altElt`. `Exercise314.diag V : V → prod V V` (also `Table55.diagC`).
- **`tail` is NOT yet implemented** — Example 4.4/Exercise 4.19 only *note* it ("left to the reader").
  So **step 0** of 5.16 is to *build* `tail : C → C` (`tail(bσ)=σ`, `tail(Λ)=⊥`) via `liftC`
  (drop-the-head: `coneVal []`/`singVal [] = ⊥`, `coneVal (b::σ)=strBot σ`, `singVal (b::σ)=strElem σ`),
  with value lemmas `tail_consMap`/`tail_strElem`/`tail_strBot`/`tail_bot`.

**The combinators (the tractable core).**
- `tail` first (see step 0).
- `neg := fixElement` of `Nop(g) = λx. cond(zero x, cons true (g (tail x)), cons false (g (tail x)))`
  (flip the head bit, recurse on the tail) — build via `Theorem41.fixMap`/`fixElement` on
  `funSpace C C`. Computation rules `neg_cons0`/`neg_cons1` from `consMap`/`tail`/`cond` value eqs;
  `neg_bot`/`neg_strBot σ` for the partial elements.
- `merge` similarly as a fixed point on `funSpace (prod C C) C`, with the boundary choice for
  `merge(Λ, y)` made explicit (Scott flags it — pick `merge(Λ,y)=Λ`, i.e. strict in the first coord, or
  document the alternative).
- `d := merge ∘ diag` (so `merge(x,x)=d(x)` is then *definitional*) — or define `d` independently and
  prove the equation.

**`neg(neg x)=x` — the hard (continuity) step.** Prove first on finite approximants by induction on
`σ : Str`: `neg (neg (strBot σ)) = strBot σ` and `neg (neg (strElem σ)) = strElem σ` (head-bit flips
twice = identity; `tail`/`cons` bookkeeping). Then extend to **all** `x ∈ |C|` by continuity: every
element is the directed sup of its finite approximants (the cone/singleton principals), and
`neg ∘ neg` is continuous (`toElementMap` of a composite of approximable maps preserves
`iSupDirected`, cf. `Theorem41.fixElement_eq_iSupDirected` / `toElementMap_iSupDirected`), so agreement
on the sup-dense basis forces `neg∘neg = id` on `|C|`. This continuity/approximation argument is the
crux flagged in the status notes.

**The Thue–Morse properties (stretch / optional).** `t = 0·merge(neg t, tail t)` is a fixed point in
`|C|`; proving (a) `t`'s `n`-th digit `= (Nat.digits 2 n).sum % 2` and (b) overlap-freeness
(`t ≠ u·a·a·a·v`, `a ≠ Λ`, `u` finite) are real **combinatorics-on-words** theorems about Thue–Morse,
largely orthogonal to domain theory. Recommend landing `tail`/`neg`/`merge`/`neg∘neg=id`/`merge(x,x)=d(x)`
first as the "Pass" core, and treating (a)/(b) as a separate follow-up (they may warrant their own
module and a `Nat.digits`/word-combinatorics detour).

**Choice discipline.** `tail`/`neg`/`merge`/`d` *data* are choice-free except the structural
`Classical.choice` inherited from `cond`/`T` (Example 1.2), exactly as Exercise 4.19's `oneDef` and
Theorem 5.6's `cond`-based maps already are — not new choice (the `liftC`-built `tail` is itself
choice-free). Prefer the choice-free relational `ApproximableMap.ext` for map equalities; fall back to
`ext_of_toElementMap` (the standing allowed exception) only when comparing via `toElementMap`. Audit
each result with the scratch file as usual.

</details>

### Lecture IV §4 completed (most recent work)

- **Example 4.3** (`Example43.lean`) — the natural-number domain `N` (flat domain over `ℕ`, tokens
  `{n}`/`ℕ`, built by `ofNestedOrDisjoint`); total elements `natElem n = n̂`. One reusable strict-lift
  combinator `constLiftN V val : ApproximableMap N V` (sends `n̂ ↦ val n`, `⊥ ↦ ⊥`) with computation
  rules `constLiftN_natElem`/`constLiftN_bot`; from it `succMap`, `predMap` (codomain `N`,
  choice-free) and `zeroMap : N → T` with all the value equations (`succMap_natElem`,
  `predMap_natElem_succ`/`_zero`, `zeroMap_natElem_zero`/`_succ`, `*_bot`). **Pitfall:** `le_antisymm`
  on `Set` pulled `Classical.choice` — use `Set.Subset.antisymm` to stay choice-free.
- **Example 4.4** (`Example44.lean`) — the binary-sequence domain `C = {σΣ*} ∪ {{σ}}` over
  `Str = List Bool` (again `ofNestedOrDisjoint`, reusing `ExampleB.cone`/`prepend`); elements
  `strBot σ = σ⊥`, `strElem σ = σ`. The two successors `consMap b` (prepend a bit) with
  `consMap_strElem`/`consMap_strBot`, and the fixed-point element `altElt = a = 01a`
  (`((consMap false).comp (consMap true)).fixElement`, equation `altElt_eq`). `tail` and the tests
  `empty`/`zero`/`one : C → T` are Scott's own "left to the reader" (Exercise 4.19) — out of scope.
- **Definition 4.5 + Theorem 4.6** (`Theorem46.lean`) — `PeanoModel N` (zero, succ; `0 ≠ n⁺`,
  injective succ, induction). Theorem 4.6 `peano_models_isomorphic`: any two models are isomorphic.
  Scott's least-fixed-point relation `r` is realized as the inductive `Graph` (the least relation
  with `(0,□)` and closed under `(n,m) ↦ (n⁺,m#)`); `exists_unique_right`/`exists_unique_left`
  (induction 4.5(iii) + inversions from 4.5(i)/(ii)) show it is a one-one correspondence.
  **Pitfall:** inverting an indexed inductive whose indices are *abstract terms* (`P.zero`,
  `P.succ m`) — plain `cases` fails ("dependent elimination failed"); first
  `generalize hz : P.zero = z at h`, then `cases h`, recovering the equation `hz` to refute the
  impossible constructor. Everything is choice-free except the final packaging of the bijection
  `M ≃ N` (which must pull `Classical.choice` from a functional+total relation — a Dedekind/
  recursion theorem).

### Lecture IV §4 exercises completed (most recent work)

All six build alone and pass the audit; the full `Domain` build is green. Each is one module
`Domain/Neighborhood/Exercise<NN>.lean`, imported from `Domain.lean`.

- **Exercise 4.7** (`Exercise407.lean`) — *a fixed point above `a` when `a ⊑ f(a)`*. `iterFrom f a n
  = fⁿ(a)`; `fixAbove f ha = ⊔ₙ fⁿ(a)` (`iSupDirected`), with `fixAbove_isFixed` (continuity
  `toElementMap_iSupDirected`), `le_fixAbove`, `fixAbove_least`. **Pitfall (re)learned:**
  `monotone_nat_of_le_succ` pulls `Classical.choice` — for a choice-free *data* construction, prove
  the chain monotone by hand via induction on `n ≤ m` (`iterFrom_mono`, mirroring `rel_master_mono`).
  All `[propext, Quot.sound]`.
- **Exercise 4.8** (`Exercise408.lean`) — *fixed-point induction*. `fix_induction (P ⊥; P x→P(f x);
  closure under monotone-chain sups `supChain`) ⟹ P(fix f)`, via `fixElement_eq_supChain` +
  `iterElem_zero`/`iterElem_succ`. Corollary `fix_induction_eq` for `S={x∣a(x)=b(x)}`
  (`a(⊥)=b(⊥)`, `f∘a=a∘f`, `f∘b=b∘f` ⟹ `a(fix f)=b(fix f)`). Choice-free.
- **Exercise 4.10** (`Exercise410.lean`) — *the relativized domain `Dₐ`*. `relSystem a` (neighbourhoods
  = members of the filter `a`); `relIso : |Dₐ| ≃o {x∣x⊑a}` from `embed`/`restrict` (note the `V.mem X`
  guard in `embed`). When `f(a)=a`: `relMap f ha : Dₐ→Dₐ` restricts `f` (codomain check via
  `↑X⊑a ⟹ Y∈f(↑X)⊑f(a)=a`), agreeing by `relMap_toElementMap_embed`. `f'` over `D_{fix f}` has a
  **unique** fixed point (`relMap_unique_fixed`, from `fixElement_below_unique`). Choice-free.
- **Exercise 4.12** (`Exercise412.lean`) — *no maximum fixed point*. `I_T` on Example 1.2 has 3 fixed
  points; the two total ones are incomparable (`elemZero_not_le_elemOne` + converse) so
  `no_greatest_fixedPoint`. Classical only through Example 1.2's finite classification.
- **Exercise 4.18** (`Exercise418.lean`) — *the assertions about `N`*. `element_classification` (`|N|`
  is `⊥` + the numerals `n̂` — flat; classical), plus choice-free Peano facts `natElem_injective`,
  `succMap_injective`, `natElem_zero_ne_succ`/`zero_ne_succMap`. (`pred∘succ=id` already in
  `Example43`.)
- **Exercise 4.20** (`Exercise420.lean`) — *`fix(f∘g)=f(fix(g∘f))`*. The rolling rule
  `fixElement_comp_comm`, pure element-level algebra (`toElementMap_comp`, `toElementMap_fixElement`,
  `fixElement_le_of_toElementMap_le`, `toElementMap_mono`). Choice-free.

### Lecture III exercises completed (earlier work)

- **3.16** (`Exercise316.lean`) — the infinite iterate `𝒟`<sup>∞</sup> over `ℕ × Δ` via fibers + cofinite-`Δ`
  bound: `iterSys` is a system, iterSeqEquiv : |𝒟<sup>∞</sup>| ≃o (ℕ → |𝒟|), and 𝒟<sup>∞</sup> ≅ 𝒟 × 𝒟<sup>∞</sup>
  (`iter_isomorphic`); plus `component`, `ofSeq`, `projN`.
- **3.17** (`Exercise317.lean`) — `B` is a **retract** of `T`<sup>∞</sup>: section f : B → T<sup>∞</sup>, retraction
  g : T<sup>∞</sup> → B, with `gf_eq_id : g ∘ f = I_B`, fg_le_id : f ∘ g ⊑ I_{T<sup>∞</sup>}, and `f_injective`.
  Encoding `encSet σ` pins copy `i` to `bitNbhd σ[i]`; key lemma `prefix_of_encSet_subset`.
- **3.24(ii)** (`Exercise324Iter.lean`) — (𝒟₀→𝒟₁<sup>∞</sup>) ≅ (𝒟₀→𝒟₁)<sup>∞</sup> (`funIter_isomorphic`), via
  `mapOfSeq` and a local `piCongrOrderIso`.
- **3.24(iii)(iv)** (`Exercise324Distrib.lean`) — canonical **mapping relationships** (not isos, due
  to the separated-sum bottom): `copair : (D₀+D₁)→D₂` with section/retract packaging `copairProj`,
  plus the distribution map `distribMap` for (iii).
- **3.25** (`Exercise325.lean`) — open subsets of `|𝒟|` form a domain: `openIso` matches opens to
  approximable maps `𝒟 → 𝒪` (Sierpiński), then `funSpaceEquiv` (Thm 3.10) gives
  `opensReprIso : {U // IsOpen U} ≃o |𝒟 → 𝒪|`.
- **3.27** (`Exercise327.lean`) — alternate proof that `(D₀→D₁)` is a domain via the Ex 2.22
  representation theorem: the family `C` of graphs is closed under non-empty intersections
  (`meetMap`) and directed unions (`joinMap`), giving `funSpaceReprIso`.

*Note on choice for 3.26:* `cond`/`condSum`/`whichMap` report `Classical.choice` in their audit, but
this is inherited structurally from the truth domain `T = Example12.neighborhoodSystem` (whose own
`inter_mem` uses `fin_cases`/`simp`), exactly as `Example23.parityMap` does — not new choice.

---

## What's next: Lectures V–VIII (transcribed, NOT yet formalized)

The Goal Lists are in `arxiv.md`:

| Lecture | arxiv § | Rows | Theme | Source lines |
| ------- | ------- | ---- | ----- | ------------ |
| IV  | §4.2.IV   | 25 | Fixed points & recursion (**25/25 done — Lecture IV complete**) | 1647–2382 |
| V   | §4.2.V    | 16 | Typed λ-calculus, λ-definability of partial recursive (**16/16 formalized — Lecture V COMPLETE**, incl. 5.16's full Thue–Morse `t`: unfolding, digit-sum-mod-2, overlap-freeness) | 2383–3207 |
| VI  | §4.2.VI   | 29 | Domain equations, functors, initial `T`-algebras (**14/29: Example 6.1 (D<sup>§</sup>≅D+(D<sup>§</sup>×D<sup>§</sup>)), Example 6.2 (`B≅B+B`, `C≅{{Λ}}+C+C`, the generalization `A≅Aⁿ+Aⁿ`, eventually-periodic ↔ regular), Defs 6.3–6.5, Props 6.6–6.7, Def 6.8 (continuous on maps), Thm 6.9 (homomorphisms out of a fixed point), Def 6.10 (the subsystem relation `D◁E`), Prop 6.11 (the subsystems of `E` form a domain), Prop 6.12 (`D◁E` ⟹ a projection pair `i,j`), Def 6.13 (monotone / continuous on domains), Thm 6.14 **existence half** (the colimit `𝒟=⋃ₙTⁿ({Γ})`, `T(𝒟)=𝒟`, the algebra, homomorphism existence via 6.9, and the `⋃ₙρₙ=I_𝒟` chain; **uniqueness/initiality still TODO** — the `T(ρₙ)=ρₙ₊₁` HEq lemma) — categorical spine + concrete equations + the homomorphism-existence theorem + the subsystem relation + its domain structure + the projection pair + the domain-level functor continuity conditions + the iterated-functor colimit solution + Lemma 6.15 (projection pair ⟹ `D⊴E`, the converse of 6.12)**) | 3208–4188 |
| VII | §4.2.VII  | 24 | Computability in effectively given domains, power domain | 4189–4728 |
| VIII| §4.2.VIII | 27 | Retracts of the universal domain `U` | 4729–5336 |

**Done so far in §4 (ALL of Lecture IV):** Theorems 4.1/4.2 (`Theorem41.lean`), Examples 4.3/4.4
(`Example43.lean`, `Example44.lean`), Definition 4.5 + Theorem 4.6 (`Theorem46.lean`), and Exercises
**4.7–4.25** (`Exercise407/408/409/410/411/412/413/414/415/416/417/418/419/420/421/422/423/424/425.lean`).

**Most recent batch (4.9, 4.11, 4.13–4.17, 4.19):**
- **4.9** (`Exercise409.lean`) — `bigPsi = curry(eval∘⟨π_G,eval⟩) : E→E` (E=(D→D)→D), the operator
  `Ψ(θ)(f)=f(θ(f))` (`bigPsi_apply`); `fix_eq_fixElement_bigPsi : fix = fix(Ψ)` from `bigPsi_fix` +
  `bigPsi_least`. Operator data choice-free; equalities go through `ext_of_toElementMap`/`funSpaceEquiv`.
- **4.11** (`Exercise411.lean`) — Plotkin uniqueness. `fixElement_uniform` (fix satisfies (iii) via
  `h(fⁿ⊥)=fⁿ⊥` + directed-union preservation); `fix_unique_of_uniform` applies (iii) along the
  inclusion `inclMap : Dₐ↪D` and Ex 4.10's unique fixed point of `f'`. `inclMap` choice-free.
- **4.13** (`Exercise413.lean`) — `monoFix = ⋂{x∣f(x)⊑x}` (monotone least fixed point, choice-free);
  `exists_unique_nat_rec` / `nat_iterate_unique` (primitive recursion, kills the 4.1↔4.6 circularity).
- **4.14** (`Exercise414.lean`) — Knaster–Tarski `gfpSet`/`lfpSet` on `PA`, choice-free.
- **4.15** (`Exercise415.lean`) — `exists_maximal_fixedPoint` (Zorn on post-fixed points) +
  `exists_least_fixedPoint`. Classical.
- **4.16** (`Exercise416.lean`) — `f_sInf_le : f(⋂S)⊑⋂S`; `optimalFix` below/consistent with every
  fixed point in `S`. Data choice-free.
- **4.17** (`Exercise417.lean`) — `lfpSet_eq_closure` (least solution = `Submonoid.closure {a,b}`);
  `fixedPoint_not_unique` (`Set.univ` also fixed).
- **4.19** (`Exercise419.lean`) — Peano axioms for `{0,1}*`; reusable head-test `liftC`; `empty`/`zero`/
  `one : C→T`; `one_def_strElem`/`one_def_strBot` define `one` from `empty`,`zero`,`cond` (`oneDef`
  inherits only the accepted structural `Classical.choice` from `cond`/`T`).

**Most recent batch (4.21–4.25 — finishing Lecture IV):**
- **4.21** (`Exercise421.lean`) — `≤` as a *unique* fixed point. Operator `leOp` on `P(ℕ×ℕ)`;
  `leRel_isFixed` + `leOp_unique` (induction on the 2nd coordinate; the `(n,m⁺)` clause never yields
  a `0`, so the relation is pinned down). The 4.13(3) function `[m] = upSet m` (`upSet_zero`/`_succ`/
  `_unique`); the addition iso `addIso : ℕ ≃ {k//m≤k}` is `n ↦ m+n` (`addIso_apply`/`_zero`/`_succ`);
  multiplication `mulOp_lfp_eq_multiples` (least solution = multiples of `n`). Data choice-free.
- **4.22** (`Exercise422.lean`) — carving a full Peano model from a partial one. `nats = lfpSet
  ({0}∪x⁺)` in `P(N*)` (choice-free membership facts `zero_mem_nats`/`succ_mem_nats` proved *directly
  from the `lfpSet` def*, not via the monotone fixed point, to stay choice-free); `nats_induction`
  (minimality). `peanoSub : PeanoModel {m // m∈nats}` (all three axioms; (i)/(ii) inherited, (iii) by
  minimality) ⟹ `exists_peano_submodel`. Existence of `N*` = axiom of infinity (`natPeano`).
- **4.23** (`Exercise423.lean`) — Eilenberg's criterion. `f_unique_fixedPoint`: under the scheme
  `aₙ` ((i) `a₀=⊥`, (ii)+(iii) packaged as pointwise `IsLUB {aₙ(x)} x`, (iv) `aₙ₊₁∘f=aₙ₊₁∘f∘aₙ`),
  `fix f` is the unique fixed point. Hint realized as `approx_le : aₙ(x)⊑aₙ(fix)` by induction (uses
  (iv) twice). Choice-free.
- **4.24** (`Exercise424.lean`) — Schröder–Bernstein via Tarski. `sbSet = lfpSet ((A−g B)∪g(f X))`
  (choice-free); `sbFun` (= `f` on `sbSet`, `g⁻¹` off it) with `sbFun_injective`/`sbFun_surjective`
  ⟹ `schroeder_bernstein` + `schroeder_bernstein_equiv : A ≃ B`. Inherently classical.
- **4.25** (`Exercise425.lean`) — the unary domain `C₁` over `{1}* ≅ ℕ`. Nested-or-disjoint `C1`
  (tails `tail n = {m∣n≤m}` + singletons `{n}`); elements `oneElem n = 1ⁿ`, `oneBot n = 1ⁿ⊥`;
  successor `consMap` (shift, `consMap_oneElem`/`_oneBot`). Key point of the exercise: `C₁` is
  *non-flat* — the successor has an infinite fixed point infElt = 1<sup>∞</sup> (`infElt_eq`) absent from the
  flat `N` — so `C₁` (= unary analogue of `C₂`) is **not** analogous to `N`. Relating map
  `relateNToC1 : N → C₁` (`n̂ ↦ 1ⁿ`, strict) via `Example43.constLiftN`. Data choice-free.

Reusable API now also: `Exercise414.lfpSet`/`gfpSet` (Knaster–Tarski on `P A`), `Exercise413.monoFix`
+ `exists_unique_nat_rec`, `Theorem46.PeanoModel`, `Example43.constLiftN` (strict lift `N → V`).

**OCR anomalies to be aware of (documented in arxiv.md notes):**
- Lecture V: "Table 5.5" is a combinator table, not a numbered theorem.
- Lecture VI: `Example 6.1` (line 3214) is not bold-tagged; Scott labels **Lemma 6.15** (3952) but
  later calls it **Theorem 6.15** (4863) — same item, original inconsistency.
- Lecture VIII: item 8.4 is `EXAMPLES 8.4` (plural, line 4773); `7.9` has a double period (4461).

**Parallel track (not keyed to PRG-19 numbering):** `Domain/ContinuousLattice/*` already explores
fixed points / domain equations / inverse limits (`FunctionSpaceTower.lean`, `InverseLimits.lean`,
`Theorem212.lean`). Consult these for proof ideas before building Lecture IV/VI from scratch, but the
deliverable is a `Domain/Neighborhood/Exercise<NN>.lean`-style module keyed to PRG-19.

---

## Working rules (read first)

- **One module per exercise**, named `Domain/Neighborhood/Exercise<NN>.lean` (or `Exercise<NN>Foo.lean`
  for a second piece). Add `import Domain.Neighborhood.Exercise<NN>` to `Domain.lean` (keep imports in
  numeric order). For theorems/definitions you may use `Theorem<NN>.lean` / `Definition<NN>.lean`.
- **Goal:** `lake build Domain` green, **zero `sorry`**.
- **Choice discipline:** keep every *data construction* (a `NeighborhoodSystem`, `ApproximableMap`,
  `OrderIso`/`≃o`, `Equiv`) choice-free: `#print axioms <name>` must be `⊆ {propext, Quot.sound}`.
  Map/structure *equalities* and *uniqueness* lemmas may pull `Classical.choice` **only** through the
  project's established `ApproximableMap.ext_of_toElementMap` and the `leastMap`/`rel_interYs` case
  split. Do not introduce *new* choice in constructions.
- **Prefer relational extensionality** `ApproximableMap.ext` (compares `.rel`) — it is choice-free,
  unlike `ext_of_toElementMap`.
- After each module: build it alone, run the axiom audit, then update `arxiv.md` (flip the row from
  `—` to **Pass** with the module name) and the status section of this file.

### Commands

```bash
cd /home/catskills/Desktop/domain_theory
lake build Domain.Neighborhood.Exercise<NN>      # build one module
lake build Domain                                 # full build (≈3016 jobs)
```

Axiom audit (scratch file, delete after):

```bash
cat > scratch_axioms.lean <<'EOF'
import Domain.Neighborhood.Exercise<NN>
open Domain.Neighborhood
#print axioms <name1>
EOF
lake env lean scratch_axioms.lean ; rm -f scratch_axioms.lean
```

---

## Reusable API cheat-sheet

### Core (`Basic.lean`)
- `structure NeighborhoodSystem (α)`: `mem : Set α → Prop`, `master : Set α`, `master_mem`,
  `inter_mem : mem X → mem Y → mem Z → Z ⊆ X∩Y → mem (X∩Y)`, `sub_master`.
- `V.Element` = filters: `mem`, `up_mem`, `master_mem`, `inter_mem`; `Element.ext` (by `mem`),
  order `x ≤ y ⟺ x.mem ⊆ y.mem`.
- `V.principal (hX : V.mem X) : V.Element`, `V.bot`, `mem_bot`.
- `DomainIso V₀ V₁ := V₀.Element ≃o V₁.Element`; `Isomorphic V₀ V₁` (`V₀ ≅ᴰ V₁`).
  **Pitfall:** superscript `ᴰ` is fine in *notation* `≅ᴰ` but **cannot** appear in identifiers — use `D`.

### Approximable maps (`Approximable.lean`, `ApproximableExercises.lean`)
- `structure ApproximableMap V₀ V₁`: `rel`, `rel_dom`, `rel_cod`, `master_rel`, `inter_right`, `mono`.
  `ApproximableMap.ext` (relational), `ext_of_toElementMap`.
- `toElementMap f`, `rel_iff_mem_principal`, `idMap`, `comp`
  (`(A.comp B).rel x z = ∃ y, B.rel x y ∧ A.rel y z`), `toElementMap_comp`, `ofIso`.
- `ofMono`, `interMap`, `iSupMap`, `ApproximableMap₂` (curried two-arg), `toElementMap₂`.

### Products (`Product.lean`)
- `prod V₀ V₁ : NeighborhoodSystem (α ⊕ β)`; `prodNbhd X Y = Sum.inl '' X ∪ Sum.inr '' Y`.
- `pair x y`, `Element.fst`/`.snd`, `prodEquiv : (prod V₀ V₁).Element ≃o V₀.Element × V₁.Element`.
- `proj₀`/`proj₁`, `paired`, `constMap`, `toMap₂`/`ofMap₂`/`map₂Equiv`, `substitution_toElementMap`.

### Sum (`Exercise318.lean`, `Exercise319Sum.lean`)
- Tokens `Option (α ⊕ β)`: `Λ = none`, `il a = some (inl a)`, `ir b = some (inr b)`.
- `inj₀`/`inj₁`, membership simp lemmas, `sum V₀ V₁ (h₀) (h₁)` (non-emptiness drives `inter_mem`).
- `inMap₀`/`inMap₁`, `outMap₀`/`outMap₁`, `sumMap` (`f+g`).

### Function space (`FunctionSpace.lean`, `Exercise321.lean`, `Exercise328.lean`)
- `step X Y = {f | f.rel X Y}` (`[X,Y]`), `stepFun L`, `step_inter_right`, `step_subset`, `step_mem`.
- `funSpace V₀ V₁`, `funSpaceEquiv : (funSpace V₀ V₁).Element ≃o ApproximableMap V₀ V₁`.
- `interYs`, `leastMap L hL hcons`, `leastMap_rel`, `rel_interYs`, `leastMap_le`.
- `eval`/`evalMap`/`evalMap_apply`, `curry`/`uncurry`/`curryEquiv`, `le_iff_toElementMap_le`,
  pointwise-bdd/sup (`mapsBounded_iff_pointwiseBounded`, `sSupMaps`, `toElementMap_sSupMaps`).
- 3.15 helpers (`Exercise315.lean`): `unitSys` (terminal `𝟙`), `prodCongrOrderIso`,
  `prodUniqueOrderIso`, `uniqueProdOrderIso`. **mathlib lacks `OrderIso.prodCongr`/`prodUnique` for
  non-lex products** — use these.

### Infinite iterate (`Exercise316.lean`) — for Lecture IV/VI recursion work
- `iterSys V : NeighborhoodSystem (ℕ × α)` (the `𝒟`<sup>∞</sup>), `component n`, `ofSeq`, `projN`,
  `iterSeqEquiv : |iterSys V| ≃o (ℕ → V.Element)`, `iter_isomorphic : iterSys V ≅ᴰ prod V (iterSys V)`.

### Fixed points (`Theorem41.lean`) — Lecture IV §4, Theorems 4.1 & 4.2
- `f.iterMap n` (`fⁿ`, `f⁰=idMap`, f<sup>n+1</sup>=f.comp (fⁿ)); `iterMap_mono_map`, `iter_comm`,
  `rel_master_mono` (extend `Δ fⁿ X` chains).
- `f.fixElement : V.Element` (least fixed point `{X ∣ ∃ n, Δ fⁿ X}`); `toElementMap_fixElement`
  (`f(x)=x`), `fixElement_le_of_toElementMap_le` (least pre-fixed), `fixElement_mono`.
- `f.iterElem n = fⁿ(⊥)`, `iterElem_eq_iterate` (`= (f(·))^[n] ⊥`), `fixElement_eq_iSupDirected`.
- `fixMap V : ApproximableMap (funSpace V V) V` (the operator); key bridge
  `fixMap_toElementMap : fix.toElementMap φ = (toApproxMap φ).fixElement` (Scott's eq. ∗), proved via
  `exists_principal_iterMap` (a finite `f`-chain factors through one finite approximant `F ∈ φ`).
  Then `fixMap_fixed` (i), `fixMap_least` (ii), `fixMap_eq_iSup` (iii), `fixMap_unique`, and
  `fixMap_toElementMap_toFilter` (bridge to "for any `f`"). **All data choice-free**; `fixMap_unique`
  uses `Classical.choice` only via `ext_of_toElementMap`.

### Natural numbers / binary sequences / Peano (`Example43.lean`, `Example44.lean`, `Theorem46.lean`)
- **`Example43`**: `N : NeighborhoodSystem ℕ` (flat, `memN X ↔ X = univ ∨ ∃ n, X = {n}`); `natElem n`
  (`= n̂`), `mem_natElem_iff`, `N_bot_mem`. Strict-lift `constLiftN V val : ApproximableMap N V`
  with `constLiftN_natElem` (`f(n̂)=val n`) / `constLiftN_bot` (`f(⊥)=⊥`). Maps `succMap`,
  `predMap` (codomain `N`), `zeroMap : N → T` + value equations. Helpers `univ_ne_singleton`,
  `singleton_nat_inj`.
- **`Example44`**: `C : NeighborhoodSystem Str` (`memC X ↔ (∃σ,X=cone σ) ∨ (∃σ,X={σ})`); `strBot σ`
  (`σ⊥`), `strElem σ` (`σ`). Successors `consMap b` + `consMap_strBot`/`consMap_strElem`; fixed-point
  element `altElt` (`a=01a`, `altElt_eq`). Reuses `ExampleB.cone`/`prepend`; new `prepend_singleton`,
  `prepend_mono`, `memC_prepend`.
- **`Theorem46`**: `PeanoModel N` (`zero`, `succ`, `zero_ne_succ`, `succ_injective`, `induction`).
  `Graph` (least-fixed-point relation), `exists_unique_right`/`_left`, `peano_models_isomorphic`
  (Theorem 4.6). Inversions `graph_zero_right`/`graph_succ_right` use the `generalize`-then-`cases`
  idiom for abstract indices.

### Examples reused
- **`Example12.lean`** (`= Example23.T`): truth domain `T` over `Token = Fin 2`, `{master, zero={0},
  one={1}}`; `mem_iff`, `elemZero`/`elemOne`. `Example23`: `trueElt`, `falseElt`, `botElt`.
- **`ExampleB.lean`**: binary system `B` over `Str = List Bool`; `cone σ = {w | σ <+: w}`.
- **`Exercise222.lean`**: abstract representation theorem — `reprSystem`, `reprIso` (`≃o C`).
- **`Exercise213.lean`**: continuous ⟺ approximable, topology bridge for `|D|`.

---

## Pitfalls learned (don't relearn)
- **`monotone_nat_of_le_succ` pulls `Classical.choice`** (so does `Monotone` packaging through it).
  For a *choice-free* directed-sup data construction (e.g. `Exercise407.fixAbove`), prove the chain
  `n ≤ m ⟹ sₙ ⊑ sₘ` by hand: a one-step lemma `sₙ ⊑ sₙ₊₁` (induction on `n`) + induction on `n ≤ m`
  (`induction hnm with | refl | step`), exactly as `Theorem41.rel_master_mono` does. The
  directedness witness fed to `iSupDirected` is then `⟨max i j, …, …⟩`.
- **`ᴰ` in identifiers fails to parse.** Notation `≅ᴰ` is fine; names must use `D`.
- **`simpa`/`simp` can pull `Classical.choice`** into a construction. In choice-free lemmas use
  explicit term-mode or `simp only [...]`. `Set.image_mono`/`image_subset` were choice-y — unfold and
  `obtain ⟨a, ha, rfl⟩`.
- **`rw` needs syntactic match:** `(sum …).master` is defeq but not syntactically `sumMaster …`.
- **`OrderIso.prodCongr`/`prodUnique`/`uniqueProd` don't exist for plain `Prod`** — use `Exercise315`
  helpers. `OrderIso.prodAssoc` is `(A×B)×C ≃o A×(B×C)`; `.symm` for the other way.
- **Don't `choose` from existentials in a construction** (pulls choice). Carry witnesses as data.
- **`map_rel_iff'` may not reduce definitionally** — open the proof with an explicit
  `show <lhs map> ≤ <rhs map> ↔ a ≤ b` to force reduction (learned in `Exercise325`/`Exercise327`).
- **Subset/`≤` on `ApproximableMap`** needs `import Domain.Neighborhood.FunctionSpace` for the
  `PartialOrder` instance.

## Files map
- New work: `Domain/Neighborhood/Exercise<NN>.lean` (or `Theorem<NN>.lean`), imported from `Domain.lean`.
- Source statements: `sources/PRG19_vision.md` — Lecture IV from 1647, V 2383, VI 3208, VII 4189,
  VIII 4729 (exact per-item line numbers are in the arxiv.md Goal Lists §4.2.IV–VIII).
- Inventory/status: **`arxiv.md` only** (§4.2.IV–VIII Goal Lists; flip `—` → **Pass** as you formalize).
- `arxiv_with_code.md` is **generated** (`scripts/generate_arxiv_with_code.py`) for PDF packaging —
  **not** for agents; it inlines all Lean and goes stale; listed in `.cursorignore`.
- This file: update the status section as you complete modules.

---

## Checkpoint 2026-06-21 — Theorem 6.9 (homomorphisms out of a fixed point) DONE

`Domain/Neighborhood/Theorem69.lean` formalizes **Theorem 6.9**: a continuous-on-maps functor `T`
with `D ≅ T(D)` admits a homomorphism `D → E` into any (strict) `T`-algebra `(E, k)`. Statement:
`nonempty_algHom_of_continuousOnMaps (T) (hT : ContinuousOnMaps T) (iso : Iso (T.obj D) D)
(B : TAlgebra T) (hk : IsStrict B.str) : Nonempty (AlgHom ⟨D, iso.hom⟩ B)`.

- **Construction.** The homomorphism is the least fixed point of `λh. k ∘ T(h) ∘ j` (`j = iso.inv`)
  on Scott's **strict** function space `strictFun D.sys E.sys`. The operator is `Op = homOp ∘ Φ`:
  `Φ` is Definition 6.8's witness (`λf.T(f)` approximable), `homOp` is the post/pre-composition
  `g ↦ k∘g∘j` (Ex 2.8 `ofMono`). The crux is the action lemma `homOp_apply_filter` — proved by
  collapsing to **single** step neighbourhoods `[X,Z]` through `strictFunEquiv` injectivity, so the
  finite factoring is just `N := [Y₁,Y₂]` (no list induction). `Op.fixElement` gives `h`; the
  fixed-point equation rearranges (`j∘i=I`, `comp_assoc`, `comp_idMap`) to the `AlgHom` square.
- **Strictness inputs.** `j` strict is *derived* (`isStrict_of_comp_eq_id`: a split iso preserves `⊥`);
  `k` strict is a hypothesis (`k` is a morphism of Scott's strict-map category). New general helpers:
  `isStrict_comp`, `isStrict_of_comp_eq_id`, `comp_mono_gen`, `toStrictMap_mono`, `toStrictFilter_mono`,
  `toStrictFilter_toStrictMap`.
- **Choice.** Conclusion is `Nonempty` (a `Prop`), so `Φ` is pulled from the `Prop`-valued
  `ContinuousOnMaps` by `Exists.elim` — `#print axioms` is `[propext, Quot.sound]` (and so are `homOp`,
  `homOpComp`). Wired into `Domain.lean`; full `lake build Domain` green (3077 jobs, zero `sorry`).
- **Next:** Definition 6.10 (`D ◁ E`), Props 6.11/6.12 (subsystem domain + projection pair), Def 6.13
  (monotone/continuous on domains), then the existence Theorem 6.14 — these need the new subsystem
  lattice / projection-pair machinery flagged earlier.

## Checkpoint 2026-06-21 — Definition 6.10 (the subsystem relation `D ◁ E`) DONE

`Domain/Neighborhood/Definition610.lean` formalizes **Definition 6.10**: the subdomain relation
`D ◁ E` between two neighbourhood systems over the same token type.

- **The relation.** `structure Subsystem (D E : NeighborhoodSystem α) : Prop` (notation `D ◁ E`,
  `infix:50`) with exactly Scott's three pieces: `master_eq : D.master = E.master` (same `Δ`),
  `sub : D.mem X → E.mem X` (`D ⊆ E`), and the essential `inter_closed : D.mem X → D.mem Y →
  E.mem (X∩Y) → D.mem (X∩Y)` ("consistency in `D` is the same as in `E`").
- **API (Scott's prose).** `Subsystem.refl`, `Subsystem.trans` (the `inter_closed` clause threads
  through `E`: `X,Y∈D⊆E`, `X∩Y∈F`, `E◁F` puts `X∩Y∈E`, `D◁E` puts `X∩Y∈D`), `Subsystem.antisymm`
  (`D◁E ∧ E◁D ⟹ D=E`), and **`Subsystem.subsystem_iff_subset_of_common`** — Scott's remark that once
  `D₀◁E` and `D₁◁E`, `D₀◁D₁ ↔ D₀⊆D₁` (the `←` direction's `inter_closed` routes `X∩Y∈D₁⊆E` back into
  `D₀` via `D₀◁E`). New general helper `NeighborhoodSystem.ext` (equal `mem` + equal `master` ⟹ equal
  system; the other three fields are `Prop`s).
- **Choice.** `refl` and `subsystem_iff_subset_of_common` depend on **no axioms**; `antisymm`/`ext`
  are `[propext, Quot.sound]`. Wired into `Domain.lean`; full `lake build Domain` green (3078 jobs,
  zero `sorry`).
- **Next:** Proposition 6.11 (the directed-union remark ⟹ `{D ∣ D ◁ E}` forms a domain), then
  Proposition 6.12 (the projection pair `i(x)={Y∈E ∣ ∃X∈x, X⊆Y}`, `j(y)=y∩D`, with `j∘i=I_D`,
  `i∘j⊆I_E`), Def 6.13 (monotone/continuous on domains), and the existence Theorem 6.14.

## Checkpoint 2026-06-21 — Proposition 6.11 (the subsystems of `E` form a domain) DONE

`Domain/Neighborhood/Proposition611.lean` formalizes **Proposition 6.11**: for a neighbourhood
system `E`, the set of subsystems `{D ∣ D ◁ E}`, ordered by the subdomain relation `◁`, *forms a
domain in its own right*. Capstone:
`subsystemReprIso (E) : {D // D ◁ E} ≃o (reprSystem (subFam E) …).Element`.

- **Route.** Scott derives this as a one-line corollary of the directed-union remark, "as a
  consequence of this remark". We use the project's **abstract representation theorem** (Exercise
  2.22, `Exercise222.reprIso`) — the same "forms a domain" route as Ex 3.25 (open sets) / Ex 3.27
  (function space). A subsystem `D ◁ E` is *determined by* its neighbourhood-family `{X ∣ D.mem X}`
  (by `NeighborhoodSystem.ext` + the standing `D.master = E.master`), so the poset is represented by
  `subFam E = {{X ∣ D.mem X} ∣ D ◁ E} ⊆ 𝒫(𝒫(Δ))` ordered by `⊆`.
- **`subIso : {D // D ◁ E} ≃o {𝒮 // 𝒮 ∈ subFam E}`.** Forward `D ↦ {X ∣ D.mem X}`, inverse `ofMem`
  (rebuild the system from `𝒮`: `mem := (· ∈ 𝒮)`, `master := E.master`, proofs from `subFam`
  membership). Order is preserved *and reflected* by Scott's remark
  `Subsystem.subsystem_iff_subset_of_common` (`◁` between subsystems-of-`E` = `⊆` of their
  neighbourhood-families). A `PartialOrder {D // D ◁ E}` instance (`subPartialOrder`) gives the
  `◁`-order (refl/trans/antisymm from Definition 6.10's API).
- **The two Exercise 2.22 hypotheses.** `subFam E` is closed under **non-empty intersections**
  (`subFam_sInter_mem`: the intersection subdomain `interSys`, nbhds = the *common* nbhds) and
  **directed unions** (`subFam_sUnion_mem`: the union subdomain `unionSys` — Scott's remark;
  directedness is used *exactly* to verify closure under consistent intersection). Both `interSys`
  and `unionSys` are full `NeighborhoodSystem`s with `master := E.master`; their inter-closure goes
  through `E.inter_mem` + `inter_closed` (so the `inter_mem` only needs `X,Y` in a *single* member,
  not the witness `Z` — `Z` only supplies `E.mem (X∩Y)`). Reusable extraction lemmas
  `subFam_master_mem`/`subFam_mem_E`/`subFam_inter_closed` (Definition 6.10's data out of `subFam`
  membership) keep the system proofs short.
- **Choice.** The combinatorial core is **choice-free**: `subFam`, `interSys`, `unionSys` depend on
  *no* axioms; `subFam_sInter_mem`/`subFam_sUnion_mem`/`subIso` on `[propext, Quot.sound]`. The final
  `subsystemReprIso` reports `[propext, Classical.choice, Quot.sound]`, the `Classical.choice`
  entering **solely** through Exercise 2.22's `reprIso` (the documented "for set theorists"
  exercise — `hne.choose` for the bottom token + finite-set induction), exactly as Ex 3.27. Wired
  into `Domain.lean`; full `lake build Domain` green (3079 jobs, zero `sorry`).
- **Next:** Proposition 6.12 (`D ◁ E` ⟹ the projection pair `i, j`), Def 6.13 (monotone/continuous
  on domains), then the existence Theorem 6.14.

## Checkpoint 2026-06-21 — Proposition 6.12 (`D ◁ E` ⟹ a projection pair) DONE

`Domain/Neighborhood/Proposition612.lean` formalizes **Proposition 6.12**: every subdomain relation
`D ◁ E` gives a *projection pair* `i : D → E`, `j : E → D` with `j ∘ i = I_D` and `i ∘ j ⊆ I_E`.
Scott leaves the proof "for the exercises"; done here directly at the level of the neighbourhood
relations (Definition 2.1), which keeps everything **choice-free**.

- **The two maps (in `namespace Subsystem`, taking `h : D ◁ E`).**
  - `Subsystem.inj h : ApproximableMap D E` — the relation `X i Y ↔ D.mem X ∧ E.mem Y ∧ X ⊆ Y`;
    element-wise `Subsystem.toElementMap_inj` gives Scott's `i(x) = {Y ∈ E ∣ ∃ X ∈ x, X ⊆ Y}`.
    `master_rel` uses `h.master_eq.subset` (same `Δ`).
  - `Subsystem.proj h : ApproximableMap E D` — the relation `Y j X ↔ E.mem Y ∧ D.mem X ∧ Y ⊆ X`;
    element-wise `Subsystem.toElementMap_proj` gives Scott's `j(y) = y ∩ D` (the `D`-neighbourhoods
    already in `y`; the `←` of the elementwise iff takes `Y := X`, the `→` uses `y.up_mem`). **The
    `inter_right` law of `proj` is the one place Definition 6.10's `inter_closed` is used:** from
    `X,X' ∈ D` and `Y ⊆ X∩X'` with `Y ∈ E`, `E.inter_mem` puts `X∩X' ∈ E`, then `h.inter_closed`
    returns `X∩X' ∈ D`.
- **The two laws.**
  - `Subsystem.proj_comp_inj : h.proj.comp h.inj = idMap D` — proved with the **choice-free**
    relational `ApproximableMap.ext` (+ `comp_rel`/`idMap_rel`). Forward: a round trip `X ⊆ Y ⊆ Z`
    collapses to `X ⊆ Z`. Backward: `X ⊆ Z` factors through the witness `Y := Z`.
  - `Subsystem.inj_comp_proj_le : h.inj.comp h.proj ≤ idMap E` — the `≤` is the `FunctionSpace`
    `PartialOrder` (inclusion of relations). A round trip `Y ⊆ X ⊆ Y'` through a common
    `D`-neighbourhood `X` is in particular `Y ⊆ Y'` on `E`; the reverse fails (not every consistent
    `E`-pair factors through `D`), so this is genuinely only `⊆`.
- **Bundled.** `Subsystem.ProjectionPair D E` (fields `inj`/`proj`/`proj_comp_inj`/
  `inj_comp_proj_le`) + `Subsystem.projectionPair h : ProjectionPair D E`, ready for Def 6.13 /
  Thm 6.14 reuse.
- **Choice.** All of `inj`/`proj`/`proj_comp_inj`/`inj_comp_proj_le`/`toElementMap_inj`/
  `toElementMap_proj`/`projectionPair` report `[propext, Quot.sound]`. Wired into `Domain.lean`;
  full `lake build Domain` green (3080 jobs, zero `sorry`).
- **Next:** Definition 6.13 (functors monotone / continuous *on domains*, phrased via this
  projection pair) and the existence **Theorem 6.14** (the iterated-functor colimit `𝒟 = ⋃ₙ Tⁿ({Γ})`
  with the `ρₙ = iₙ∘jₙ` chain `⋃ₙρₙ = I_𝒟` for homomorphism-uniqueness).

## Checkpoint 2026-06-21 — Definition 6.13 (functors monotone / continuous on domains) DONE

`Domain/Neighborhood/Definition613.lean` formalizes **Definition 6.13**: the two domain-level
continuity conditions on a functor `T : Endofunctor DomainObj` (Definition 6.3). Both are `Prop`
predicates; the identity functor satisfies both (`monotoneOnDomains_id`, `continuousOnDomains_id`),
witnessing non-vacuity. **Fully choice-free** `[propext, Quot.sound]`.

- **The carrier-type subtlety (the one design decision).** `D ◁ E` (Definition 6.10) requires `D, E`
  over the **same** token type `α`; the abstract `T` need not preserve token types, so
  `T.obj ⟨α,D⟩` and `T.obj ⟨α,E⟩` may have *different* carriers and "`T(D) ◁ T(E)`" does not even
  typecheck until the carriers are identified. So **monotone on domains** is packaged pointwise as
  `structure MonotoneAt T (h : D ◁ E)` with fields: `carrier_eq` (`(T.obj⟨α,E⟩).carrier =
  (T.obj⟨α,D⟩).carrier`), `sub` (the transported `(T.obj⟨α,D⟩).sys ◁ carrier_eq ▸ (T.obj⟨α,E⟩).sys`),
  and `inj_heq`/`proj_heq` (Scott's "the pair `i,j` is mapped to `T(i),T(j)`": the canonical 6.12
  pair `sub.inj`/`sub.proj` equals `T.map h.inj`/`T.map h.proj`, up to the carrier transport — hence
  `HEq`). `MonotoneOnDomains T := ∀ {α D E} (h : D ◁ E), MonotoneAt T h`.
- **Continuous on domains.** Scott's `λD.T(D) : {D∣D◁E} → {D'∣D'◁T(E)}` *approximable* is rendered,
  in the concrete neighbourhood framework, as **preservation of directed unions of subsystems**:
  `ContinuousOnDomains T := ∃ hmono : MonotoneOnDomains T, ∀ {α E} (ℱ : Set (NeighborhoodSystem α))
  (hℱ : ∀ D∈ℱ, D◁E) (hne) (hdir : DirectedOn (·◁·) ℱ) {U} (hUE : U◁E) (hU : U's family = ⋃ℱ's),
  targetFam T hmono hUE = ⋃ D∈ℱ, targetFam T hmono (hℱ D)`. Here `targetFam T hmono (h : D◁E) :
  Set (Set (T.obj⟨α,E⟩).carrier)` is the neighbourhood family of `T(D)` pushed to `T(E)`'s carrier
  via `MonotoneAt.carrier_eq` (a `▸`-transport of the test set; legal as data because it goes through
  `Eq.rec`'s large elimination, even though `MonotoneAt` is a `Prop`). This is exactly the continuity
  Scott invokes in 6.14: `T(⋃ₙ Tⁿ{Γ}) = ⋃ₙ T(Tⁿ⁺¹{Γ})`.
- **Identity-functor proofs.** `idEndofunctor` fixes objects/maps, so `carrier_eq := rfl`, `sub := h`,
  `inj_heq/proj_heq := HEq.rfl`; `targetFam (idEndofunctor) _ h` collapses (proof-irrelevance makes
  `carrier_eq` defeq `rfl`, so `carrier_eq ▸ Y = Y`) to the plain family `{Y∣D.mem Y}`, and
  continuity becomes the union hypothesis `hU` after `simp [targetFam, Set.mem_iUnion, exists_prop]`.
- **Pitfall.** `∃ D ∈ ℱ, P` desugars to `∃ D, D∈ℱ ∧ P` (an `And`), whereas the bounded union
  `⋃ D, ⋃ hD : D∈ℱ, …` unfolds (via `Set.mem_iUnion`) to `∃ D, ∃ _:D∈ℱ, …` (an `Exists`); bridge
  them with `exists_prop` in the simp set so the final `exact hU Y` unifies by defeq.
- **Choice.** `MonotoneOnDomains`/`MonotoneAt`/`targetFam`/`ContinuousOnDomains`/`monotoneOnDomains_id`/
  `continuousOnDomains_id` all report `[propext, Quot.sound]`. Wired into `Domain.lean`; full
  `lake build Domain` green (3081 jobs, zero `sorry`).
- **Next:** the existence **Theorem 6.14** (`{Γ}◁T({Γ})` ⟹ initial `T`-algebra via the iterated
  colimit `𝒟 = ⋃ₙ Tⁿ({Γ})`, `𝒟≅T(𝒟)` the identity, uniqueness via the `ρₙ = iₙ∘jₙ` chain
  `⋃ₙρₙ = I_𝒟`). It will *use* `MonotoneOnDomains` (to get each `Tⁿ{Γ} ◁ 𝒟` and `T(ρₙ)=ρₙ₊₁`) and
  `ContinuousOnDomains` (to get `T(𝒟)=𝒟`).

## Checkpoint 2026-06-21 — Theorem 6.14 EXISTENCE HALF done (`Theorem614.lean`)

`Domain/Neighborhood/Theorem614.lean` formalizes the **existence half** of Theorem 6.14: the
iterated-functor colimit `𝒟 = ⋃ₙ Tⁿ({Γ})` is a `T`-algebra with `T(𝒟) = 𝒟` (the iso is the
identity), and it admits a homomorphism into every strict `T`-algebra (Theorem 6.9). Full
`lake build Domain` green (3082 jobs, zero `sorry`); **all data choice-free** `[propext, Quot.sound]`
(audited: `colim`, `Dsys`, `colimIso`, `colimAlg`, `rho`, `iSupRho`, `iSupRho_eq_id`,
`Tcolim_eq_colim`, `nonempty_algHom`).

- **Hypotheses bundled in `Setup`**: `T` (an `Endofunctor DomainObj.{w}`), `hmaps : ContinuousOnMaps`,
  `hmono : MonotoneOnDomains` (kept separate from `hcont` so it is usable in **data**, choice-free,
  rather than `Exists.choose`-extracted), `hcont : ContinuousOnDomains`, token type `Tok`, generating
  system `Γ`, the carrier identification `ceq : (T.obj⟨Tok,Γ⟩).carrier = Tok`, and Scott's
  `hsub : Γ ◁ (ceq ▸ T(Γ).sys)` (`= {Γ}◁T({Γ})`).
- **The carrier-transport toolkit (the crux difficulty).** The abstract `T` need not preserve token
  types, so each `Tⁿ({Γ})` a priori lives over a different carrier. Four **choice-free** transport
  lemmas (all proved by `cases`/`subst` on a *generalized* carrier-eq variable `β = α`) tame this:
  `subsystem_cast` (transport `D◁E`), `rec_trans` (`e'▸(e▸x)=(e.trans e')▸x` for systems),
  `mem_cast` (`(e▸V).mem X ↔ V.mem (e.symm▸X)`), `set_rec_trans` (the `Set` analogue). **Key trick:**
  carrier-eq proofs into the *same* type are `Prop`s, so **proof irrelevance makes them defeq** —
  e.g. `carrier_eq.trans (Dceq s n)` and `colimCeq s` are interchangeable for free, which is what
  makes `Dsys_sub_Tcolim` close by a bare `exact h` after `rw [rec_trans]`.
- **The tower** `iter s n : Σ' S, Σ' (ceq : (T.obj⟨Tok,S⟩).carrier=Tok), S ◁ (ceq ▸ T(S).sys)`
  (structural recursion; the successor step feeds `chainₙ` to `s.hmono` to get the next `carrier_eq`
  and `MonotoneAt.sub`, transported by `subsystem_cast`+`rec_trans`). Accessors `Dsys`/`Dceq`/`Dchain`
  (`Dsys_succ : Dsys(n+1) = Dceq n ▸ T(Dsys n).sys` is `rfl`), `Dsys_master` (all over `Δ=Γ`),
  `chain_le` (`Tⁿ◁Tᵐ` for `n≤m`).
- **The colimit** `colim s` (`mem X := ∃n, (Dsys s n).mem X`; `inter_mem` lifts `X,Y,Z` to one level
  `max …` via `chain_le` then uses that level's own `inter_mem`). `Dsys_sub_colim` (`Tⁿ◁𝒟`),
  `colimCeq` (`(T.obj⟨Tok,𝒟⟩).carrier = Tok`, from `MonotoneAt` of `T⁰◁𝒟`), `Tcolim` (`=T(𝒟)` over
  `Tok`), `Dsys_sub_Tcolim` (`Tⁿ⁺¹◁T(𝒟)`), `Tcolim_master`, `colim_sub_Tcolim` (easy `𝒟⊆T(𝒟)`).
- **The continuity step** `Tcolim_sub_colim` (the only use of `ContinuousOnDomains`): apply the
  directed-union-preservation to `ℱ := Set.range (Dsys s)`, `E=U=𝒟`, `hUE = Subsystem.refl 𝒟`.
  Pull `X : Set Tok` back to `Y₀ := colimCeq.symm ▸ X` on `T(𝒟)`'s carrier; `X∈T(𝒟)` ⟺ `Y₀ ∈
  targetFam(refl)` (the `carrier_eq ▸ Y₀ = Y₀` step is defeq by proof irrelevance), rewrite by the
  continuity equation, and read off `∃n, (Dsys s (n+1)).mem X` (the `set_rec_trans` + proof-irrel
  identification `ceqₙ ▸ Y₀ = (Dceq s n).symm ▸ X` is the `key` step). Hence `Tcolim_eq_colim`
  (`T(𝒟)=𝒟` via `NeighborhoodSystem.ext` + mutual `⊆`), the `DomainObj` equality `colimObj_eq` (via
  `domainObj_ext`: carrier-eq + transported-sys-eq ⟹ `⟨c,σ⟩=⟨Tok,𝒟⟩`), the identity iso
  `colimIso : Iso (T.obj⟨Tok,𝒟⟩) ⟨Tok,𝒟⟩` (via `isoOfEq`, an object-equality ⟹ identity iso in any
  `Category`), and `colimAlg`.
- **Existence** `nonempty_algHom s B hk : Nonempty (AlgHom (colimAlg s) B)` for strict `B` — directly
  `nonempty_algHom_of_continuousOnMaps s.T s.hmaps (colimIso s) B hk` (Theorem 6.9). Capstone
  `exists_algebra_with_hom`.
- **The projection chain (uniqueness engine, ready)** `rho s n := iₙ.comp jₙ` (`iₙ,jₙ` from
  Prop 6.12 on `Dsys_sub_colim s n`), `rho_rel` (`X ρₙ Y ↔ ∃z∈Tⁿ, X⊆z⊆Y`), `rho_mono` (`ρₙ⊆ρₘ`),
  `iSupRho` (`⋃ₙρₙ` via `ApproximableMap.iSupMap`), and **`iSupRho_eq_id : ⋃ₙρₙ = I_𝒟`** (forward
  `X⊆z⊆Y⟹X⊆Y`; reverse factors the identity step `X⊆X⊆Y` through the level witnessing `X∈𝒟`).

**What remains for full 6.14 (uniqueness ⟹ initial `T`-algebra among strict algebras).** The gate is
`key_rho : rho s (n+1) = (colimIso s).hom ∘ T.map (rho s n) ∘ (colimIso s).inv` — i.e. Scott's
`T(ρₙ)=ρₙ₊₁`. This is a heavy **heterogeneous-equality** lemma: it must thread `MonotoneAt.inj_heq`/
`proj_heq` (`HEq (T.map iₙ) sub.inj`, `HEq (T.map jₙ) sub.proj`) through the carrier transports and
the `colimObj_eq` cast. The structural obstacle: `colimObj_eq : T.obj⟨Tok,𝒟⟩ = ⟨Tok,𝒟⟩` is between
**non-variable terms**, so it cannot be `subst`/`cases`-eliminated to collapse the casts. A promising
de-risk already noted: `Subsystem` is a `Prop` and `Subsystem.inj`/`proj`'s `rel` fields depend only
on `(D,E)` (not on the proof), so the *transported* `sub.inj` is **defeq** to `(Dsys_sub_colim s
(n+1)).inj = iₙ₊₁`; the remaining work is converting the `T.map iₙ` HEq into a map equality over
`Tok` (an `ApproximableMap` cast lemma). With `key_rho` in hand: for any strict `AlgHom g`,
`gₙ := g.hom ∘ rho s n` satisfies `g₀=⊥` (`g` strict, `ρ₀=⊥`-map) and `gₙ₊₁ = k∘T(gₙ)` (via `key_rho`
+ `g.comm` with `str=colimIso.hom`), so the sequence is `g`-independent; then
`g.hom = ⋃ₙ gₙ` (continuity of comp + `iSupRho_eq_id`) forces any two strict homomorphisms equal.
This re-uses no new external API beyond exposing the fixed-point sup, but the `key_rho` HEq surgery is
comparable in size to Theorem 6.9 itself — budget it as its own work item.

---

## Checkpoint — 2026-06-21: **Theorem 6.14 COMPLETE (uniqueness/initiality)**

`lake build Domain` green (3082 jobs, zero `sorry`). Axiom audit of `exists_unique_strict_algHom`,
`exists_algebra_with_hom`, `key_rho`, `gcomp_eq`, `algHom_unique` ⟹ all `[propext, Quot.sound]`
(**choice-free**, including the `Prop`-level uniqueness). The uniqueness half of 6.14 is finished;
`Theorem614.lean` now proves `𝒟 = ⋃ₙ Tⁿ({Γ})` is the **initial** `T`-algebra among strict algebras.

- **`key_rho : rho s (n+1) = (colimIso s).hom ⊚ T(ρₙ) ⊚ (colimIso s).inv`** (Scott's `T(ρₙ)=ρₙ₊₁`,
  conjugated by the structure iso). Built bottom-up from `HEq` surgery:
  - `transport_heq` (`HEq (e ▸ f) f` for an endo-`Hom` along an object-eq) and `isoOfEq_conj`
    (`(isoOfEq e).hom ⊚ f ⊚ (isoOfEq e).inv = e ▸ f`, by `cases e` + id-laws). Since `colimIso = isoOfEq
    colimObj_eq`, conjugation by it **is** the carrier-transport along `colimObj_eq`.
  - `map_comp_proj_heq` (**the crux**): given the *monotone-on-domains* data `Tmi/Tmj` HEq-equal to the
    Prop-6.12 pair `sub.inj/sub.proj` of the image subsystem, `Tmi ∘ Tmj` is HEq to `iₙ₊₁ ∘ jₙ₊₁`. Proof:
    `subst` the two carrier equalities (`cn : Pc=Tok`, `cc : Qc=Tok`), then `obtain rfl` the two
    transported-system equalities; **proof irrelevance** collapses the two `Subsystem` proofs so
    `eq_of_heq` turns the `HEq`s into `Tmi=sub.inj`, `Tmj=sub.proj` and `rw` closes.
  - `map_rho_heq : HEq (T(ρₙ)) ρₙ₊₁` = `T.map_comp` (`T(iₙ∘jₙ)=T(iₙ)∘T(jₙ)`) then `map_comp_proj_heq`
    fed with `s.hmono (Dsys_sub_colim s n)`'s `carrier_eq`/`sub`/`inj_heq`/`proj_heq`.
  - `key_rho` = `isoOfEq_conj` to turn the RHS into `colimObj_eq ▸ T(ρₙ)`, then `eq_of_heq` against
    `map_rho_heq.symm.trans (transport_heq …).symm`.
- **The `g`-independent recursion** (`g₀=⊥`, `gₙ₊₁=k∘T(gₙ)∘j`):
  - `rho_zero_rel` (needs **`{Γ}` one-point**, `hΓ : ∀X, Γ.mem X → X=Γ.master`): `ρ₀` relates `X` only
    to `𝒟.master`. `strict_rel_master` (`g.rel master Z ↔ Z=master` for strict `g`) then gives
    `gcomp_rho_zero_rel` and `gcomp_rho_zero_indep` (the base case, `g`-independent).
  - `gcomp_rho_succ : g∘ρₙ₊₁ = k ∘ T(g∘ρₙ) ∘ j` — proved as a `calc` **at the categorical `⊚` level**
    (so the implicit args are concrete `DomainObj`s, dodging the system-level `rw` fragility): `key_rho`,
    then `Category.assoc` term-mode steps + `g.comm` (`g∘str = k∘T(g)`, `str=colimIso.hom`) + `T.map_comp`.
    The two congruence steps use `congrArg (g.hom ⊚ ·)`/`congrArg (fun m => B.str ⊚ (m ⊚ inv))` so `calc`
    bridges by **defeq** rather than syntactic match.
  - `gcomp_rho_indep` (induction on `n`), `gcomp_eq` (`g = g∘I = g∘⋃ρₙ = ⋃(g∘ρₙ)` g-independent, via
    `iSupRho_eq_id` + `comp_idMap`), `algHom_ext` (commuting square is a `Prop`), `algHom_unique`.
- **Initiality**: `exists_unique_strict_algHom` — for every strict `T`-algebra `B`, a **unique** strict
  homomorphism `𝒟 → B`. Required strengthening `Theorem69.nonempty_algHom_of_continuousOnMaps` to return
  `Nonempty {g // IsStrict g.hom}` (the Theorem-6.9 homomorphism is in fact strict), threaded through
  `nonempty_strict_algHom`.
- **Lean gotcha logged**: `rw` with explicit args at the `ApproximableMap`/`NeighborhoodSystem` level
  repeatedly failed "did not find pattern" on **defeq-but-not-syntactic** implicits (`colim s` vs
  `(colimAlg s).carrier.sys` vs `(objColim s).sys`; abbrev `objColim` vs literal `⟨Tok,colim s⟩`). Fixes:
  work at the `⊚`/`Category.assoc` level (object-indexed, concrete), prefer `congrArg`/`calc` term-mode
  proofs (defeq-tolerant), and bind `comp_idMap`/etc. facts via a `have` with the *desired* `colim s`
  type (the `have` unifies by defeq) before rewriting.

---

## Checkpoint — 2026-06-21: **Lemma 6.15 COMPLETE (converse of Prop 6.12)**

`Domain/Neighborhood/Lemma615.lean` formalizes **Lemma 6.15**: a projection pair `i : D → E`,
`j : E → D` with `j ∘ i = I_D` and `i ∘ j ⊆ I_E` — for `D, E` over **possibly different** token
types — exhibits `D` as a subdomain of `E`. Capstone
`trianglelefteq_of_projectionPair (i) (j) (hji : j.comp i = idMap D) (hij : i.comp j ≤ idMap E) :
D ⊴ E`. Full `lake build Domain` green (3083 jobs, zero `sorry`); **fully choice-free**
`[propext, Quot.sound]` (audited: `trianglelefteq_of_projectionPair`, `Dprime`, `Dprime_subsystem`,
`dprimeEquiv`, `Subsystem.trianglelefteq`).

- **`Trianglelefteq` (`⊴`, `infix:50`).** Scott's `D ⊴ E := ∃ D' : NeighborhoodSystem β, D' ◁ E ∧
  (D ≅ᴰ D')` ("`D ≅ D'` for some `D' ◁ E`"). Note `◁` (Definition 6.10) needs the **same** token
  type, but `⊴` does not — the witness `D'` lives over `E`'s tokens `β`.
- **The whole proof is relational** (Definition 2.1 level) — *cleaner than Scott's* filter-by-filter
  argument. The one idea: the predicate `IsGen i j X Y := i.rel X Y ∧ j.rel Y X` ("`Y` generates
  `i(↑X)`", i.e. `i(↑X) = ↑Y`). Everything follows from:
  - **`isGen_exists`** (uses `hji`): every `X ∈ D` has a generator — apply `j∘i = I_D` to the identity
    relation `X I_D X` (`(j.comp i).rel X X` after `rw [hji]`, then `comp_rel` gives `∃Y, …`).
  - **`isGen_mono`** (uses `hji`) / **`isGen_mono'`** (uses `hij`): the correspondence is `⊆`-monotone
    both ways — `Z ⊆ W → X ⊆ X'` (widen `X i Z` to `X i W`, compose with `W j X'`, read off via
    `j∘i=I_D`) and the dual via `i∘j⊆I_E`. Their two-way use gives uniqueness in each argument
    (`isGen_fst_unique` needs only `hji`, `isGen_snd_unique` only `hij`).
  - **`isGen_inter`** (just `mono`/`inter_right` of `i,j`; the `E.mem (Y∩Y')` hypothesis licenses the
    `j.mono` steps): generators are closed under `∩`, generating `X∩X'`. **`D.mem (X∩X')` is obtained
    from `j.inter_right` — not from `D`'s own closure** (no need for a `D`-consistency witness).
- **`Dprime i j`** (`mem Y := ∃ X, IsGen i j X Y`, `master := E.master`): a nbhd system (condition
  (ii) from `isGen_inter`, deriving `E.mem (Y₁∩Y₂)` from the witness via `E.inter_mem`), with
  **`Dprime_subsystem : Dprime i j ◁ E`** whose `inter_closed` clause is *literally* `isGen_inter`.
- **`dprimeEquiv : D.Element ≃o (Dprime i j).Element`** = `toEl x = {Y ∣ ∃ X ∈ x, IsGen X Y}`,
  `ofEl y = {X ∣ ∃ Y ∈ y, IsGen X Y}`. Filter laws: `up_mem` of `toEl`/`ofEl` is `isGen_mono`/
  `isGen_mono'` (+`isGen_exists`); inverse laws + `map_rel_iff'` are generator uniqueness +
  existence. (`map_rel_iff'`: apply the `≤` positionally — the Element-order binder is named `X`, so
  `h (Y := …)` fails; use `h Y _`.)
- **`Subsystem.trianglelefteq : D ◁ E → D ⊴ E`** (take `D' = D`) — so together with the capstone,
  `D ⊴ E ↔ ∃` projection pair `D ⇄ E` (Prop 6.12 ⇆ Lemma 6.15).
- **Pitfall (re)learned:** a `theorem`/`def` binder list with an **unused implicit** (`{X Y X' Y' :
  Set α}` when only `X, X'` appear) leaves the spurious metavariable **unsolved** at every call site,
  surfacing as a stray `⊢ Set α` goal in the *caller*. Trim binders to exactly what the statement
  mentions.
- **Next:** **Theorem 6.16** (initial `T`-algebra `D` ⟹ `D ⊴ E` for any `E ≅ T(E)`) is the natural
  consumer: `h:D→E`, `g:E→D` from Theorem 6.9, `g∘h=I_D` by initiality (Thm 6.14), then `h∘g⊆I_E` via
  a `gₙ/hₙ` directed-sup argument, and finally `trianglelefteq_of_projectionPair`.

## Checkpoint — 2026-06-21 — Theorem 6.16 COMPLETE (`Theorem616.lean`, choice-free)

**`trianglelefteq_of_isInitial (T) (hT : ContinuousOnMaps T) (Dalg) (hinit : IsInitial Dalg) (E)
(isoE : Iso (T.obj E) E) : Dalg.carrier.sys ⊴ E.sys`** — Scott's Theorem 6.16 verbatim: an initial
`T`-algebra embeds as a subdomain of every solution of the domain equation. `lake build Domain` green,
zero `sorry`, axiom audit `[propext, Quot.sound]` (incl. the `Prop`-level initiality use).

How the proof goes (it reuses Theorem 6.9's machinery rather than re-deriving it):

- **Setup.** Lambek (Prop 6.7) gives `isoD := lambek Dalg hinit : T(D)≅D`, so `i=isoD.hom` (which is
  *defeq* `Dalg.str`), `j=isoD.inv`; `u=isoE.hom`, `v=isoE.inv`. All four maps are strict via
  `isStrict_of_comp_eq_id` applied to the split-iso laws. The Definition-6.8 witnesses `Φ` for the
  three strict hom-spaces `(D,E)`, `(E,D)`, `(E,E)` are `obtain`-ed from `hT` (choice-free since the
  goal `D ⊴ E` is a `Prop`).
- **`opStep` (the shared per-step lemma, top-level).** For Theorem 6.9's operator
  `Op = (homOp T D E j k)⊚Φ`, `toStrictMap(Op x).1 = k ∘ T(toStrictMap x).1 ∘ j`. Pure
  `homOp_apply_filter` + the defining property `hΦ` of `Φ`; no `T`-strictness needed (it comes from
  `hΦ`). This is the *only* place the 6.9 internals are touched.
- **Three approximant chains** `H,G,K n := (toStrictMap (Op·.iterElem n)).1`. Base
  `iterElem 0 = ⊥` (local `iterElem_zero`) + **`botStrict_rel`** (top-level: `⊥`'s strict map relates
  `X↦master`, i.e. it is the constant-`⊥` least map). Recursions `Hₙ₊₁=u∘T(Hₙ)∘j` etc. via
  `iterElem_succ`+`opStep`.
- **Ladder** `Hₙ∘Gₙ=Kₙ` by induction. Step rewrites with **`key`** (`(u∘a∘j)∘(i∘b∘v)=u∘(a∘b)∘v`,
  using `j∘i=I_{T(D)}`) then functoriality **`hTcomp`** (`T(p)∘T(q)=T(p∘q)`) + IH. Base by
  `ApproximableMap.ext` + the three `botStrict_rel`s.
- **`⊔`-decomposition** `*_fix_rel` (`fixElement_eq_iSupDirected`+`mem_iSupDirected`, `toStrictMap_rel`
  is `Iff.rfl`). Gives **`hgk : h∘g = k`** by diagonalizing the doubly-indexed directed family at
  `max m n` (monotonicity `H_mono`/`G_mono` from `iterElem_mono`+`toStrictMap_mono`).
- **`hk_le : k ≤ I_E`** because `I_E` is a fixed point of `Op_k` (`opStep`+`T.map_id`+`u∘v=I`, then
  `fixElement_le_of_toElementMap_le`).
- **`hgh_id : g∘h = I_D`** by initiality: `h,g` are `AlgHom`s (`h_comm`/`g_comm` derived from the
  fixed-point equations `h_fixeq`/`g_fixeq` via `toElementMap_fixElement`), so both `g∘h` and `id`
  equal `hinit.desc`.
- **Capstone:** `trianglelefteq_of_projectionPair h g hgh_id (le_of_eq_of_le hgk hk_le)` (Lemma 6.15).

**`⊚`-vs-`.comp` friction (the main time sink, as warned for 6.14):** `opStep`/`homOpComp` produce
`ApproximableMap.comp`, but the categorical laws (`Iso.hom_inv_id`, `T.map_id`, `T.map_comp`,
`AlgHom` comm) are stated with `⊚`/`Category.id`. These are *defeq* but `rw` needs syntactic matches.
Fix: keep everything in `.comp` and make **defeq `.comp`-form copies** of each law up front —
`hji`/`hvu`/`huv` (iso laws), `hmapid` (`T.map_id`), `hTcomp` (`T.map_comp`). `Iso.hom`/`Dalg.str`
agree by defeq (lambek's `hom := A.str`), so the `AlgHom` comm fields typecheck without conversion.

**Reusable bits worth remembering:** `opStep` and `botStrict_rel` are general (any `T`, `j`, `k`, `Φ`)
and would serve any future "run 6.9 and read off the approximant ladder" argument (e.g. Exercises
6.17–6.19).

## Checkpoint — 2026-06-21 — Exercise 6.17 scaffold COMPLETE (`Exercise617.lean`, choice-free; initiality pending)

**What is green now** (`lake build Domain.Neighborhood.Exercise617` ✓, axiom audit `[propext, Quot.sound]`
on `sumMap3`/`sumMap3_id`/`sumMap3_comp`/`isStrict_sumMap3`/`Tc`/`Calg`/`cStr`):

- **Bespoke `∅`-free category `StrictDomainObj`** (`carrier : Type w`, `sys`, `nonempty : ∀X, sys.mem X → X.Nonempty`),
  `instance : Category StrictDomainObj` with `Hom := StrictMap`, id/comp from Thm 2.5 +
  `isStrict_idMap`/`isStrict_comp`. **Why bespoke and not `DomainObj`:** the separated sum needs `∅∉𝒟`
  (an empty nbhd of one summand becomes a spurious consistency witness for the other tag, breaking
  `inter_mem`), so `T(X)=𝟙+X+X` is **not** a total endofunctor of `DomainObj` ⟹ **Theorem 6.14 cannot
  be invoked**. This is exactly Scott's "category of strict maps" (Ex 6.19). (User chose this "bespoke"
  route over rebuilding the whole 6.9/6.14 spine over the `∅`-free subcategory.)
- **Endofunctor `Tc = 𝟙+X+X`** complete: `tcObj` (reuses Example 6.2 `sum3 unitSys D D`, `∅`-free by
  `sum3_nonempty`); the three-way sum map **`sumMap3 = f₀+f₁+f₂`** (full `inter_right`/`mono`; shape
  lemmas `mem_subset_jᵢ_inv` say a nbhd `⊆ jᵢ` is itself a `jᵢ`-copy); `isStrict_sumMap3`; and
  **functoriality** `sumMap3_id`/`sumMap3_comp` ⟹ `Tc : Endofunctor StrictDomainObj` (`tcMapHom` =
  `I_𝟙 + f + f`). `@[simp] Tc_obj`/`Tc_map_val`.
- **`C` is a `Tc`-algebra** `Calg = ⟨Cobj, cStr⟩`: `Cobj = ⟨Str, C, C_nonempty⟩`,
  `cStr = ⟨ofIso ccEquiv.symm, isStrict_ofIso _⟩` (Example 6.2's iso `C ≅ 𝟙+C+C`, inverse direction;
  strict because an `OrderIso` preserves `⊥` — `isStrict_ofIso` via `isStrict_iff_apply_bot` +
  `toElementMap_ofIso` + `OrderIso.map_bot`).

**Remaining to finish Ex 6.17 (precise, validated plan):**

1. **`desc : C → E` (existence)** via **`Exercise419.liftC`** (build a map out of `C` from per-string
   values, NO function-space fixed point needed because the recursion is on the *finite* string σ, not
   on `desc`). For a `Tc`-algebra `B=(E,k)` (`k : 𝟙+E+E → E`):
   - `e := k.toElementMap term` (the terminator element; `term :=` element of `sum3 unitSys E E` gen'd by `j0 univ`).
   - `f_b y := k.toElementMap (inj_b y)` where `inj1,inj2 : E.Element → (sum3 unitSys E E).Element` are
     the canonical sum injections (NEW: build them like Example62C `toCC`, ~40-60 lines each;
     `inj1(y).mem W := W=master3 ∨ ∃Y, W=j1 Y ∧ y.mem Y`).
   - `singVal [] = e`, `singVal (b::σ) = f_b (singVal σ)`; `coneVal [] = E.bot`, `coneVal (b::σ) = f_b (coneVal σ)`.
   - `hcone`/`hsing` monotonicity by `peano_induction` on σ using `f_b` monotone (`toElementMap` mono)
     + `coneVal σ ≤ singVal σ`.
2. **AlgHom square** `desc ⊚ cStr = k ⊚ Tc(desc)`. Prove on **elements**: every `s ∈ |𝟙+C+C|` is
   `toCC x` (ccEquiv onto), and `cStr.toElementMap (toCC x) = fromCC(toCC x) = x`, so the square ⟺
   **`desc(x) = k(Tc(desc)(toCC x))` for all `x∈|C|`** (★). Case on `x` via `memC_cases`:
   - `x=Λ̂`: `toCC Λ̂ = term`; `sumMap3 id desc desc` fixes the unit copy ⟹ `term`; `k term = e = desc Λ̂`.
   - `x=0·y` (`= consMap false y`): **`toCC (consMap false y) = inj1 y`** (key lemma:
     `toCC(0y).mem(j1 X) ↔ (0y).mem(0X) ↔ y.mem X`); `sumMap3 id desc desc (inj1 y) = inj1 (desc y)`;
     `k(inj1(desc y)) = f₀(desc y) = desc(0y)`. Likewise `1·y` with `inj2`/`f₁`.
   - NEW supporting lemmas: `toCC_consMap_eq_inj` and `sumMap3` toElementMap action on `term`/`inj_b`.
3. **Uniqueness** ⟹ `IsInitial Calg`: any `AlgHom h'` satisfies the same recursion equations
   (`h'(Λ)=e`, `h'(b·x)=f_b(h' x)` — read off the square the same way), so `h'` agrees with `desc` on
   every finite generator `strElem σ`/`strBot σ` by `peano_induction`, hence `h'=desc` by
   `map_ext_C` / `eq_of_toElementMap_principal` (Ex 2.8; cf. `Exercise516` neg∘neg).
4. **Generalization `Cₙ ≅ 𝟙 + Cₙⁿ + Cₙⁿ`** matching `A ≅ Aⁿ + Aⁿ` (Example 6.2's `A`): same recipe with
   an `n`-fold sum/product; the algebras are domains with a point + `2n` (or `n`-ary) strict ops.
5. Wire is **already done** (`Domain.lean` imports `Exercise617`); on completion run the axiom audit on
   `desc`/`IsInitial Calg` and flip `arxiv.md` 6.17 row to **Pass**.

**Reusables for step 1–2:** `liftC`/`liftC_strBot`/`liftC_strElem` (`Exercise419`), `toElementMap_ofIso`,
`Example62C.{toCC,fromCC,ccEquiv, toCC_mem_j0/j1/j2, fromCC_mem_nil/embF/embT, memC_cases}`,
`Example44.{consMap, strElem, strBot, embBit_*}`.

---

## Checkpoint — Exercise 6.17 part 1 (initiality) COMPLETE (2026-06-21)

`Exercise617.lean` builds green, zero `sorry`. **`CisInitial : IsInitial Calg`** — `C` is the initial
`T`-algebra for `T(X)=𝟙+X+X`. The plan above was executed with one simplification: the AlgHom square is
*not* proved by `memC_cases` on a general element (that fails for infinite `x`), but by showing
`descMap = M` for `M := (k ⊚ T(desc)) ⊚ ofIso ccEquiv` via **`map_ext_C`** (agreement on every finite
`strBot σ`/`strElem σ`), which then yields the square by iso-cancellation.

**What was built (in `Exercise617.lean`, namespace `Domain.Neighborhood` / section `Initial`):**
- **Separated-sum element injections** `sinj0/sinj1/sinj2 : Vᵢ.Element → (sum3 …).Element` with
  `sinjᵢ_mem_jᵢ` (membership iff), monotonicity `sinj1_mono`/`sinj2_mono`, and the **action of the
  three-way sum map** `sumMap3_sinj0/1/2` (`(f₀+f₁+f₂)(injᵢ x) = injᵢ(fᵢ x)`).
- **C-side bridges** (`namespace Example62C`): `ccEquiv_apply` (`ccEquiv x = toCC x`),
  `consMap_mem_embBit` (`(b·z).mem(bX) ↔ z.mem X`), the cross-tag/terminator emptiness lemmas, and the
  headline **`toCC_consMap : toCC(b·z) = condᵇ (inj₂ z)(inj₁ z)`** and **`toCC_strElem_nil : toCC Λ̂ = inj₀ ⊤`**.
- **`descMap : C→E`** via `liftC` with `descVal z` (head-recursion `z`, `b::σ ↦ f_b(descVal z σ)`),
  `e := descE = k(inj₀ ⊤)`, `f_b := descF b = k∘cond_b(inj₂,inj₁)`. Monotonicity helpers `descF_mono`,
  `descVal_mono_z`, `descVal_append` ⟹ `hcone`/`hsing`. `descMap_strict` (uses `C_bot_eq_strBot_nil`).
- **`genKey`/`genKey0`/`genKeyBot`** — the one-step computation `k(T(g)(toCC(b·w))) = f_b(g w)` (and the
  `Λ̂`/`⊥` analogues) for an arbitrary `g`; `ccEquiv_symm_comp`/`ccEquiv_comp_symm` (iso cancellation).
- **`rec_determines`** (any `g` solving the recursion `g = (k⊚T(g))⊚ofIso ccEquiv` equals `descMap`, by
  induction on σ + `genKey` + `map_ext_C`), **`descMap_satisfiesRec`**, **`descComm`** (the square),
  **`descAlgHom`**, **`descAlgHom_uniq`**, and **`CisInitial`**.

**The algebras (answer to part 1):** a `Tc`-algebra `k:𝟙+E+E→E` is exactly a domain `E` with a point
`e` and two strict unary ops `f₀,f₁`; `C` is initial since every finite/infinite binary string is the
unique `f`-word, `desc(b₀b₁… ) = f_{b₀}(f_{b₁}(…))` over `e`/`⊥`.

**Axiom audit:** data is choice-free — `descMap`, `Calg`, `Tc`, `sumMap3`, `sinjᵢ` are
`[propext, Quot.sound]`. The Prop obligations `descComm`, `descAlgHom_uniq`, `CisInitial` are
`[propext, Classical.choice, Quot.sound]`; the choice comes **only** from the project's foundational
map-extensionality `ApproximableMap.ext_of_toElementMap`/`eq_of_toElementMap_principal` (choice-bound
because nbhd-membership is not decidable), shared by every map-equality result in the repo — genuinely
unavoidable, permitted by the choice rule for Prop-level results.

**Gotcha for future edits:** `rw` of lemmas whose statement carries explicit `sum3`/`sumMap3` nonempty
proof args (`genKey`, `ccEquiv_symm_comp`) often fails to match syntactically even when display-equal;
use `exact`/`erw` (defeq-aware) instead — see the `exact h.symm` / `erw [ccEquiv_symm_comp]` sites.

**Remaining (part 2):** generalization `Cₙ` (n-ary sequences `Cₙ ≅ 𝟙 + n·Cₙ`; algebras = point + `n`
strict unary ops). Conceptually answered; Lean formalization deferred pending a scope decision (it
duplicates the binary development for arbitrary `n`).

## Checkpoint — Exercise 6.17 part 2 (generalization to `Cₙ`) COMPLETE (2026-06-21)

`Exercise617Gen.lean` builds green (`lake build Domain` ✓, ≈3086 jobs), zero `sorry`. The binary
Example 6.2 development is generalized over an **arbitrary alphabet** `A : Type` `[DecidableEq A]`,
answering part 2 in full Lean.

**What was built (in `Exercise617Gen.lean`, namespace `Domain.Neighborhood.Exercise617Gen`):**
- **Generic domain.** `Strn A := List A`; cones `coneN`/`memCn`; `Cn A : NeighborhoodSystem (Strn A)`
  of finite-or-infinite `A`-sequences; `strBotN`/`strElemN` elements; `prependN`; and the prepend map
  `consMapN a : Cn A → Cn A`. (Direct generalization of Example 6.2's `Bool`-indexed `C`/`consMap`.)
- **`A`-indexed separated sum.** `SigTok A β := Option (Unit ⊕ A×β)` token type with injections
  `jU`/`jc a`, master `masterSig`, system **`sumSig A V h`** (`h : ∀ X, V.mem X → X.Nonempty`, since the
  separated sum needs `∅∉𝒟`), element-injections `sinjU`/`sinjC a`, and the functorial map
  **`sumMapSig f = id + Σ_a f`** with `isStrict_sumMapSig`, `sumMapSig_id`/`_comp`. This packages as the
  endofunctor **`Tsig(X) = 𝟙 + Σ_{a:A} X : Endofunctor StrictDomainObj`** on the same bespoke `∅`-free
  category reused from part 1.
- **Domain equation.** `embA a` (generic `embBit`), `toCC`/`fromCC`, and the order-iso
  **`ccEquiv : (Cn A).Element ≃o (CCn A).Element`** with `CCn A = sumSig A (Cn A) Cn_nonempty`; packaged
  as `Cn_domain_equation : Cn A ≅ᴰ CCn A` and the algebra `Cnalg = (Cnobj, cnStr)`,
  `cnStr = ofIso ccEquiv.symm`. `[Inhabited A]` supplies the non-emptiness witnesses
  (`singleton_nil_ne_univ`, `embA_ne`) that were concrete (`true ≠ false`) in the binary case.
- **Initiality.** Same recursion skeleton as part 1: `liftCn` (choice-free head-recursion
  `φ(Λ)=e`, `φ(a·x)=f_a(φ x)`, `f_a = k∘sinjC a`), `map_ext_Cn` (C-extensionality), one-step `genKey`,
  `rec_determines`, giving `descAlgHom : AlgHom Cnalg B` and `descAlgHom_uniq`, hence
  **`CnisInitial : IsInitial Cnalg`**.
- **Instantiation.** `A := Fin (n+1)` recovers Scott's `Cₙ`: `Cfin_domain_equation`
  (`Cn (Fin (n+1)) ≅ᴰ 𝟙 + (n+1)·Cₙ`) and `CfinIsInitial`. `n=1` (`Fin 2 ≃ Bool`) reproduces Example 6.2.

**The algebras (part-2 answer):** a `Tsig`-algebra `k : 𝟙 + Σ_a E → E` is a domain `E` with a
distinguished point `e = k(jU)` and **`A`-many strict unary operations** `f_a = k∘sinjC a`; `Cn A` is
initial because every finite/infinite `A`-sequence is the unique `f`-word over `e`/`⊥`.

**Axioms:** data (`Cn`, `sumSig`, `sumMapSig`, `Tsig`, `ccEquiv`, `Cnalg`, `Cn_domain_equation`) is
`[propext, Quot.sound]` (choice-free); the Prop-level `descAlgHom`/`CnisInitial`/`CfinIsInitial`
inherit `Classical.choice` only from the foundational map-extensionality, exactly as in part 1.

## Checkpoint — Exercise 6.18 (`𝒟^∞` as an initial algebra) COMPLETE (2026-06-21)

`Domain/Neighborhood/Exercise618.lean` builds green (`lake build Domain` ✓, 3087 jobs), zero `sorry`,
wired into `Domain.lean`. Exercise 6.18 asks to discuss `𝒟^∞` (Exercise 3.16) **as an initial algebra**
and **as a solution of the domain equation `𝒟^∞ ≅ 𝒟 × 𝒟^∞`**.

**Domain-equation half** is already Exercise 3.16 (`iter_isomorphic`, `iterProdIso`). This module
supplies the **initial-algebra half** for the product endofunctor `T(X) = 𝒟 × X` over a fixed `∅`-free
domain `𝒟`, in the bespoke `StrictDomainObj` category (Exercise 6.17), where `IsInitial` is Scott's
universal property among strict algebras. (Theorem 6.14's same-carrier colimit tower does **not**
apply: `T(X)=𝒟×X` grows the token set `ℕ×Δ`, so `𝒟^∞` is built directly à la Exercise 3.16.)

**What was built (namespace `Domain.Neighborhood.Exercise618`):**
- **Element helpers.** `prod_nonempty`/`iterSys_nonempty` (`∅`-freeness preserved); the head/tail
  reading `iterProdIso_apply` and its inverse "cons" `iterProdIso_symm_pair` (`consSeq`); bottom
  computations `iterBot_eq`, `component_bot`, `pair_bot`.
- **Structure maps.** `jmap = ofIso iterProdIso`, `imap = ofIso iterProdIso⁻¹` (the algebra map),
  `isStrict_imap`, `jmap_comp_imap : j∘i = I`.
- **Existence.** Operator `descOp k f = k∘(id×f)∘j`, descent chain `descSeq` (`h₀=⊥`,
  `hₙ₊₁=descOp k hₙ`), and **`descMap = iSupMap descSeq` (choice-free data)**. `descMap_fix`
  (`descMap = descOp descMap`, via continuity of `k` over directed unions), `descMap_strict`, and the
  homomorphism square **`descMap_comm : descMap∘i = k∘T(descMap)`** (from `descMap_fix` + `j∘i=I`).
- **Uniqueness.** Truncation chain `ρₙ = descSeq imap` with closed form
  `rho_apply : ρₙ(z) = ⟨z₀,…,z_{n-1},⊥,…⟩` and **`iSupRho_eq_id : ⋃ₙ ρₙ = I`** (cofinite-`Δ`
  structure of `𝒟^∞`). `g`-independence (`gcomp_rho_zero`, `gcomp_rho_succ`) gives
  **`comm_unique`**: any two strict homomorphisms into `(E,k)` agree on every truncation, hence are
  equal.
- **Categorical packaging.** `isStrict_prodMap`; `prodObj`/`prodMapHom`/**`prodFunctor Dom`** (the
  endofunctor `T(X)=𝒟×X`); `iterObj`/**`iterAlg Dom`** (`(𝒟^∞, i)`); `descAlgHom`; and
  **`iterIsInitial Dom : IsInitial (iterAlg Dom)`** — `𝒟^∞` is the initial `T`-algebra.

**Axioms:** the data map **`descMap` is choice-free `[propext, Quot.sound]`**; the Prop-level
`descMap_comm`/`comm_unique`/`iSupRho_eq_id`/`iterIsInitial` inherit `Classical.choice` only from the
foundational directed-suprema membership lemmas — exactly the same precedent as Exercise 6.17's
`CisInitial` (`#print axioms CisInitial = [propext, Classical.choice, Quot.sound]`).

---

## Checkpoint — 2026-06-21: Exercise 6.19 **Part A** COMPLETE (`Exercise619.lean`)

**Exercise 6.19** ("sum and product on the category of strict maps") asks to (A) define Scott's
*uniform* token-level sum/product on systems over `Δ ⊆ {0,1}*` (`Λ∈Δ`, `∅∉𝒟`) and answer *"Are these
correct up to isomorphism?"*, then (B) generate all `T(X)` from constants/identity/sum/product and show
they are functors, continuous on maps, monotone + continuous on domains. **Part A is done; Part B is
deferred** (it needs the Definition 6.8/6.10/6.13 notions re-expressed over this bespoke `{0,1}*` strict
category + closure-by-grammar-induction — a separate work item).

**What was built (namespace `Domain.Neighborhood.Exercise619`, `Str := List Bool`, `Λ = []`):**
- **Concrete sum `sumTok D₀ D₁ h₀ h₁`** over `Str`: `mem W := W = {Λ}∪0Δ₀∪1Δ₁ ∨ (∃X∈𝒟₀, W=0X) ∨
  (∃Y∈𝒟₁, W=1Y)`, with `0X = embBit false X`, `1Y = embBit true Y` (reusing Example 6.2's `embBit` and
  its disjointness/intersection algebra: `embBit_inter`, `embBit_inter_ne`, `embBit_subset`,
  `embBit_injective`, `embBit_nonempty`, `embBit_ne`). Master `sumTokMaster := insert [] (0Δ₀ ∪ 1Δ₁)`;
  closed under consistent `∩` exactly as the abstract `sum` (Exercise 3.18). `∅`-free via
  `sumTok_nonempty`.
- **`sumTok_iso_sum : sumTok D₀ D₁ h₀ h₁ ≅ᴰ sum D₀ D₁ h₀ h₁`** — the answer is **yes**. The order-iso
  `sumTokEquiv` is a *generalisation of `Example62.bbEquiv`* from `B` to arbitrary `∅`-free `D₀,D₁`:
  `toSum`/`fromSum` (mutually inverse `fromSum_toSum`/`toSum_fromSum`) with `@[simp]` bridges
  `toSum_mem_inj₀/₁`, `fromSum_mem_embF/T`. Generic inversion helpers `sum_mem_inj₀_inv`/`inj₁_inv`/
  `sum_mem_nonempty` and `sumTok_mem_embF_inv/embT_inv` carry the tag-disjointness through.
- **Concrete product `prodTok D₀ D₁`** over `Str`: `mem W := ∃ X∈𝒟₀ Y∈𝒟₁, W = {Λ}∪0X∪1Y`
  (`prodTokNbhd X Y := insert [] (0X ∪ 1Y)`). Membership simp lemmas `mem_prodTokNbhd_nil/false/true`
  reduce everything to coordinatewise facts: Scott's (2) `prodTokNbhd_inter`, (1)
  `prodTokNbhd_subset_iff`, uniqueness `prodTokNbhd_injective`. `∅`-free (`prodTok_nonempty`; every
  nbhd contains `Λ`). Note `prodTokNbhd D₀.master D₁.master = sumTokMaster` (same top as the sum).
- **`prodTok_iso_prod : prodTok D₀ D₁ ≅ᴰ prod D₀ D₁`** — yes. Built as
  `prodTokEquiv.trans (prodEquiv D₀ D₁).symm`, where `prodTokEquiv : |prodTok| ≃o |D₀|×|D₁|` mirrors
  Scott's Proposition 3.2 at the token level: components `fstTok`/`sndTok`, splitting `prodTok_mem_split`
  (Scott's (3)), pairing `pairTok`, with `pairTok_fstTok_sndTok`/`fstTok_pairTok`/`sndTok_pairTok`.
- **Axioms.** `sumTok`, `prodTok`, `sumTok_iso_sum`, `prodTok_iso_prod` all
  `#print axioms ⊆ {propext, Quot.sound}` (choice-free). Wired into `Domain.lean`; full `Domain` build
  green (3088 jobs).

**Next concrete target after 6.19A:** either **Exercise 6.19 Part B** (the functor algebra), or
**Exercise 6.20** (`tok(T({Γ}))` continuous on `{Γ ⊆ {0,1}* ∣ Λ∈Γ}` ⟹ a `Γ` with `Γ = tok(T({Γ}))`,
so `{Γ}◁T({Γ})` and 6.14 applies) — both build on this module's `sumTok`/`prodTok`.

## Checkpoint — 2026-06-21: Exercise 6.19 **Part B** COMPLETE (`Exercise619PartB.lean`)

Scott's ask: the constructs `T(X)` built from constants, identity, sum, and product are *"all
functors, continuous on maps, and monotone and continuous on domains."* All four properties are now
formalized and choice-free (`#print axioms ⊆ {propext, Quot.sound}`); wired into `Domain.lean`, full
`Domain` build green (3089 jobs).

**The category.** Rather than fight the universe-polymorphic `Endofunctor DomainObj` (Defs 6.8/6.13),
I work in the *concrete* category whose objects are `structure ScottSys` = `∅`-free neighbourhood
systems over the single token type `Str = {0,1}*` (Part A's setting). Because every object lives over
the same carrier, `◁` is a relation between systems on a common type and the domain conditions need
**no carrier transport**. Morphisms are `ApproximableMap`s between the underlying `.sys`.

**Object/map algebra (reusing Part A).**
- `ScottSys.sum`/`ScottSys.prod` repackage `sumTok`/`prodTok` so the result is again a `ScottSys`.
- `sumMapTok f₀ f₁ : (A₀+A₁) → (B₀+B₁)` and `prodMapTok f₀ f₁ : (A₀×A₁) → (B₀×B₁)` are the actions on
  maps, each a full `ApproximableMap` (the long cases: `rel_dom`/`rel_cod`/`master_rel`/`inter_right`/
  `mono`, all driven by `embBit` tag-disjointness via the new `embBit_not_subset_cross`).
- Strictness: `sumMapTok_isStrict` (always strict — `0X∪1Y` can only map nil to the master);
  `prodMapTok_isStrict` (strict iff both factors are).
- Bifunctor laws: `sumMapTok_id`/`sumMapTok_comp`, `prodMapTok_id`/`prodMapTok_comp`.

**The functor-expression grammar.** `inductive FExpr := const ScottSys | var | sum FExpr FExpr |
prod FExpr FExpr`; `FExpr.obj : FExpr → ScottSys → ScottSys`, `FExpr.map` on morphisms.

**The four properties (all by induction on `FExpr`).**
- *Functors:* `FExpr.map_id` (`T(I)=I`), `FExpr.map_comp` (`T(g∘f)=T(g)∘T(f)`), and
  `FExpr.map_isStrict` (so `T` restricts to the strict-map category of Def 6.8).
- *Continuous on maps:* `FExpr.map_mono` (`f ≤ f' ⟹ T(f) ≤ T(f')`) **and** `FExpr.map_continuous`
  (`λf. T(f)` sends `⨆` of a directed family of maps to `⨆` of the images). Monotone + preserves
  directed sups = approximable in the argument (Ex 2.13), which is Scott's "continuous on maps."
- *Monotone on domains:* `FExpr.obj_subsystem` (`X ◁ Y ⟹ T(X) ◁ T(Y)`), built on
  `sumTok_subsystem`/`prodTok_subsystem`.
- *Continuous on domains:* `FExpr.obj_continuous` (with forward half `obj_continuous_mp`):
  `λD. T(D)` preserves directed unions of subsystems — the form used in Theorem 6.14.

**Gotchas for the next session.** `DirectedOn` unfolds to an explicit `∀ x ∈ S, ∀ y ∈ S, …`, so feed
it as `hdir D₁ hD₁ D₂ hD₂` (not `hdir hD₁`). The `sumTok`/`prodTok` membership inversions need the
`∅`-freeness witnesses passed explicitly (`h₀ := B₀.ne`, etc.) since defeq won't surface them.

**Next concrete target after 6.19B:** **Exercise 6.20** (`tok(D)` on systems; the `Γ = tok(T({Γ}))`
fixed point feeding 6.14).

## Checkpoint — 2026-06-21: Exercise 6.20 COMPLETE (`Exercise619PartB.lean`)

Scott's ask: for the category of 6.19, show `λΓ. tok(T({Γ}))` is continuous on the domain
`{Γ ⊆ {0,1}* ∣ Λ∈Γ}` (`T` any functor from 6.19), and conclude there is a `Γ = tok(T({Γ}))`, so
`{Γ}◁T({Γ})` and Theorem 6.14 applies. All done choice-free (`⊆ {propext, Quot.sound}`); appended to
the existing 6.19B module, full `Domain` build green (3089 jobs).

**Setup.** `tok(𝒟) := 𝒟.master` (the master neighbourhood *is* the token set `Δ`, since `𝒟⊆𝒫(Δ)`);
`{Γ} := singletonSys Γ h` is the one-neighbourhood system (only nbhd `Γ`, master `Γ`, `∅`-free iff
`Γ` non-empty — supplied by `Λ∈Γ`).

**The crucial simplification.** Computing the whole system `T({Γ})` is unnecessary — only its master
is needed, and that obeys a tiny token-level recursion `mFun : FExpr → Set Str → Set Str` with **no**
neighbourhood data: `const C ↦ C.master`, `var ↦ Γ`, and *both* `sum`/`prod ↦ insert Λ (0·mFun T₀ Γ ∪
1·mFun T₁ Γ)` (recall `sumTokMaster = prodTokNbhd` agree on masters — same root `Λ`, same tags). The
bridge `mFun_eq_master : mFun T Γ = (T.obj (singletonSys Γ h)).sys.master` is by induction.

**Continuity on the domain.** `mFun_mono` (monotone) and `mFun_continuous` (preserves directed unions
— in fact *fully additive*: preserves arbitrary non-empty unions, so directedness is not even needed
at the master level, though the statement is the directed-sup form). Both go through the shared
tagged-union helpers `insertTag_mono`/`insertTag_continuous`.

**Fixed point = explicit Kleene union.** `mIter T 0 = {Λ}`, `mIter T (n+1) = mFun T (mIter T n)`;
`nil_mem_mIter` (`Λ∈` each), `mIter_mono_step`/`mIter_mono` (increasing chain) ⟹ `mFun_iter_fixed :
mFun T (⋃ₙ mIter T n) = ⋃ₙ mIter T n` (apply `mFun_continuous` to `Set.range (mIter T)`). Hence
`exists_tok_fixedPoint : ∃ Γ, Λ∈Γ ∧ mFun T Γ = Γ`, and the object-level capstone
`exists_singleton_subsystem : ∃ Γ h, (singletonSys Γ h).sys ◁ (T.obj (singletonSys Γ h)).sys` — the
6.14 hypothesis. `FExpr.RootedConst` (each constant `C` has `Λ∈C.master`; automatic for sum/prod)
keeps the bottom `{Λ}` and the whole chain inside `{Γ ∣ Λ∈Γ}`.

**Choice-discipline gotchas (important — these silently pull `Classical.choice`).** `Eq.le` on `Set`
(i.e. `(h : X = Y).le : X ⊆ Y`) and `monotone_nat_of_le_succ` both depend on `Classical.choice`.
Replaced the former with a `rw`-based `sub_master` in `singletonSys`, and the latter with a hand-rolled
`mIter_mono` (`induction hmn` on `m ≤ n`). Also hand-rolled `insertTag_mono` (the
`Set.insert_subset_insert`/`union_subset_union` combo was fine, but the by-hand `rintro` version is
clearly clean). Audit each new lemma with `#print axioms` — the whole 6.20 development is
`⊆ {propext, Quot.sound}`.

**Next concrete target:** **Exercise 6.21 is COMPLETE** (`Exercise621.lean`) — see the checkpoint
below. Next open Lecture VI items: **Exercise 6.22** (comment on the domain equations
`N ≅ {{0},{0,Λ}} ⊕ N`, `M ≅ {{Λ}} + M`, `N* ≅ N ⊕ (N ⊗ N*)`), **Exercise 6.23** (initial solution of
`Exp ≅ N ⊕ ((Exp×Exp)+(Exp×Exp))` as a syntactic domain + evaluation `val(s)`), **Exercise 6.24**
(simultaneous double fixed point `D ≅ D+(D×E)`, `E ≅ D+E`).

## Checkpoint — 2026-06-21: Exercise 6.21 COMPLETE (`Exercise621.lean`)

Scott's ask: *"do the same as 6.19 and 6.20"* for the **coalesced** sum `⊕` and **smash** product
`⊗` (p. 113), and *"generalize all of `+,×,⊕,⊗` to combinations of several terms."* All done
choice-free (`#print axioms ⊆ {propext, Quot.sound}`); wired into `Domain.lean`, full `Domain` build
green (3090 jobs). New module `Exercise621.lean` (namespace `Domain.Neighborhood.Exercise619`, so it
reuses Part A/B `sumTok`/`prodTok`/`embBit`/`ScottSys`/`sumMapTok`/`prodMapTok`/`singletonSys`/
`insertTag_*` directly).

**The operations.** `oplusTok D₀ D₁ h₀ h₁` is literally `sumTok` with the two improper copies `0Δ₀`,
`1Δ₁` deleted (proper rows now demand `X ≠ Δ₀`, `Y ≠ Δ₁`); `otimesTok D₀ D₁` is `prodTok` with proper
rectangles demanding `X ≠ Δ₀ ∧ Y ≠ Δ₁`, keeping only the full top `M = prodTokNbhd Δ₀ Δ₁` on the
boundary. Both keep the **same master** `M = {Λ}∪0Δ₀∪1Δ₁` as `+`/`×`. The domain meaning: `⊕`/`⊗`
**identify the two bottoms** (coalesced/smash), whereas `+`/`×` keep them apart. Closure is the
`sumTok`/`prodTok` proof + the helper `inter_ne_of_ne_left/right` (`X ⊆ Δ, X ≠ Δ ⟹ X∩X' ≠ Δ`).

**The map actions (the subtle part).** `oplusMapTok`/`otimesMapTok`'s relations add a
**master/collapse row** — *every* `W` in the domain relates to the top `M` — on top of the proper
rows (with `≠Δ` on both input and output components). The collapse row is what makes the map
total/approximable even when `f₀(X)` hits the top `Δ₀'` (which would land on the *deleted* copy
`0Δ₀'`): such a hit collapses to `M`, exactly the coalesced bottom. Both maps are **always strict**.
**Crucial gotcha:** the bifunctor *composition* laws `oplus/otimesMapTok_comp` need **`g₀,g₁`
strict** (`hg₀ : IsStrict g₀`, …). Reason: if the intermediate `f₀(X)=Δ₀'` (top) and `g₀` then
produces proper info from it, the RHS `(g⊕)∘(f⊕)` routes `X → M → M` (g⊕ sends the top only to the
top) while the LHS `(g∘f)⊕` would produce proper output — mismatch. Strictness of `g` forbids exactly
this (`g₀.rel Δ₀' Y → Y = Δ_C`). This is the formal reason Scott restricts to the **strict-map
category**, and it is why `GExpr.map_comp` (below) carries `IsStrict g` (whereas `FExpr.map_comp` for
`+`/`×` alone did not).

**The extended algebra `GExpr`** = `FExpr` + two constructors `oplus`/`otimes`. `GExpr.obj`,
`GExpr.map`, and the four properties all by induction over the **six** constructors, delegating
`sum`/`prod` to Part B's combinators and `oplus`/`otimes` to the new ones: functors
(`map_id`/`map_comp`/`map_isStrict`), continuous on maps (`map_mono`/`map_continuous`), monotone on
domains (`obj_subsystem`), continuous on domains (`obj_continuous`). The `obj_continuous_mp` and
`map_continuous_mp` forward inductions carry the `≠Δ` side-conditions across via the subsystem
`master_eq` (`fun heq => hXne (heq.trans (…).master_eq)`).

**6.20 for `GExpr`.** Because all four binary masters agree (`sumTokMaster = prodTokNbhd` on masters),
the token recursion `gFun` has the **same body** in all four binary cases, so `gFun_mono`/
`gFun_continuous` reuse Part B's generic `insertTag_mono`/`insertTag_continuous` verbatim. Capstones
`gExists_tok_fixedPoint` and `gExists_singleton_subsystem` (`{Γ} ◁ T({Γ})`, so Thm 6.14 applies).

**Several terms.** Key observation: `GExpr` is **closed** under the binary ops, so every finite
combination `T₀ ⋆ T₁ ⋆ ⋯ ⋆ Tₙ` (any `⋆`, any nesting) is *already* a `GExpr` and inherits every
result with zero extra work. `GExpr.naryOp op a l` packages the right-nested n-ary fold;
`narySum`/`naryProd`/`naryOplus`/`naryOtimes` are the four instances; `naryOp_rootedConst` preserves
the `Λ∈tok` side-condition; `{narySum,naryProd,naryOplus,naryOtimes}_singleton_subsystem` give each
n-ary construct a fixed point `Γ = tok(T({Γ}))`.

**Reusable gotchas for next session.** (1) `oplusTok_mem_embF`/`_embT`/`_inv` have **implicit**
`h₀ h₁` (the `∅`-freeness witnesses) that defeq won't surface — pass `(h₀ := B₀.ne) (h₁ := B₁.ne)`
explicitly (matches the Part-A gotcha). `otimesTok` takes **no** such args, so its helpers
(`otimesTok_mem_prod`/`_master`/`_prod_inv`) need none. (2) The collapse row's `W' = master` makes
`isStrict`/`id`/`comp` proofs hinge on `nil ∈ sumTokMaster` vs `nil ∉ embBit`; coerce the master
equality with `have heq' : sumTokMaster … = … := heq` before `▸` (defeq through `(A.oplus B).sys.master`
won't rewrite directly). (3) `prodTokNbhd_injective` needs its arg retyped to the literal
`prodTokNbhd …` shape (same coercion trick) before use on a `.sys.master`.

## Checkpoint — 2026-06-21: Exercise 6.22 COMPLETE (`Exercise622.lean`)

Scott's *"Comment on these domain equations"* — `N ≅ {{0},{0,Λ}} ⊕ N`, `M ≅ {{Λ}} + M`,
`N* ≅ N ⊕ (N ⊗ N*)`. This is a *comment-on* exercise, so the formal content is to recognise each RHS
as a construct `T(X)` of the **`GExpr`** algebra (Exercise 6.21) with **rooted** constants, hence
`gExists_singleton_subsystem` gives a solution `Γ = tok(T({Γ}))` with `{Γ} ◁ T({Γ})` and **Thm 6.14
applies**. Built green (full `Domain`, 3091 jobs), axiom audit `⊆ {propext, Quot.sound}`, wired into
`Domain.lean`. New module reuses everything from 6.21 (namespace `Domain.Neighborhood.Exercise619`).

**The two new constant domains.** `Cnat = {{0},{0,Λ}}` (`0 = [false]`, `Λ = []`): the **two-point
chain** `{0} ⊏ Δ={0,Λ}`. Built as a bare `NeighborhoodSystem` with the nested pair `{0} ⊆ {0,Λ}`;
`inter_mem`'s four cases discharge with `Set.inter_self` / `Set.inter_eq_self_of_subset_left` /
`…_right` off the single fact `hAB : {[false]} ⊆ {[false],[]}` (`Set.singleton_subset_iff.mpr
(Set.mem_insert ..)`). `∅`-free + rooted (`nil_mem_Cnat`, via `Set.mem_insert_iff.mpr (Or.inr rfl)`).
`Cone = singletonSys {Λ}` is the one-point `𝟙` (`nil_mem_Cone := rfl`).

**The three equations & their meaning (the "comment").** `NExpr = ⊕(const Cnat, var)` → `N` = the
**vertical naturals** (coalesced `⊕` *identifies* bottoms ⇒ a chain `⊥⊑0⊑1⊑⋯⊑∞`). `MExpr =
+(const Cone, var)` → `M` = the **lazy naturals** (separated `+` *keeps* the stop/continue choice
apart ⇒ branching). `NStarExpr N = ⊕(const N, ⊗(const N, var))` → `N*` = **strict streams over `N`**
(cons-cell functor `X ≅ N ⊕ (N ⊗ X)`, smash `⊗` = strict head/tail pair). The only `+`-vs-`⊕`
difference (coalesced vs separated) is *exactly* what distinguishes `N` from `M` — a nice payoff of
having both in `GExpr`.

**Theorems.** `N_eq_solution`, `M_eq_solution`, `NStar_eq_solution (N) (hN : Λ ∈ tok N)` — each is
`gExists_singleton_subsystem _ <rooted>`. `NStar_over_N_exists` **chains** them: eq-1's solution is a
rooted domain (its token set is the fixed point `Γ₁ ∋ Λ`, extracted via `gExists_tok_fixedPoint`), so
it is a legitimate datum domain for eq-3 — `N*` exists over the very `N` from eq-1.

**Gotchas / reuse for next session.** (1) `RootedConst` of these small expressions is just nested
`⟨…, trivial⟩` and elaborates fine without unfolding (`def`s are semireducible; `exact` unfolds
`NExpr`/`RootedConst` during defeq). (2) To get `Λ ∈ Γ` from a `GExpr` fixed point, use
`gExists_tok_fixedPoint` (exposes `hnil`), **not** `gExists_singleton_subsystem` (hides it). (3) Set
literals: `{[false],[]}` is `insert [false] {[]}`; `Λ ∈ master` is `Set.mem_insert_iff.mpr (Or.inr
rfl)`, and for a `singletonSys Γ` the master *is* `Γ` so `Λ ∈ {Λ}` is `rfl`. (4) `Cnat`/`Cone` are
the reusable "small constant domains" — `Cone` is the terminal object `𝟙`, handy for 6.23/6.24.

## Checkpoint — 2026-06-21: Exercise 6.23 **Phase 1** COMPLETE (`Exercise623.lean`)

Scott 6.23 asks to (a) *construe the initial solution of `Exp ≅ N ⊕ ((Exp×Exp)+(Exp×Exp))` as a
syntactic domain of expressions* (variables from `N`, two binary op-symbols `u,v`), and (b) show any
strict `s : N → D` + ops `u,v : D×D → D` determine a **unique** evaluation `val(s) : Exp → D`. User
chose the **full domain-theoretic initiality** route (à la Exercise 6.17), with `N` an **arbitrary
rooted `ScottSys`** parameter.

**Key architectural decision (important for whoever continues).** Theorem 6.14 (`Theorem614.lean`)
already builds the initial algebra abstractly as the colimit `⋃ₙ Tⁿ({Γ})` — *but* it is stated over
`Endofunctor DomainObj` with arbitrary carriers, so it is drowning in `HEq` carrier-transport, and
the `GExpr` operations `⊕,⊗,+,×` are **`Str`-specific** (not a total endofunctor of `DomainObj` — the
same obstruction `Exercise617` flagged). So we **cannot** instantiate the abstract Theorem 6.14. The
chosen path is to **re-derive Theorem 6.14 concretely in the `ScottSys` framework**, where the token
type is fixed at `Str` and every carrier equality is `rfl` (no `HEq`). The `GExpr` concrete
continuity lemmas (`obj_subsystem`, `obj_continuous`, `map_continuous`, `map_id`, `map_comp` [needs
`IsStrict g`], `map_isStrict`) are *exactly* the hypotheses needed and plug straight in.

**Phase 1 delivered (a generic, reusable colimit fixed point for ANY rooted `GExpr` — also the engine
for 6.24).** All choice-free; full `Domain` green (3092 jobs).
- `gFix T = ⋃ₙ gIter T n` — the 6.20/6.21 token fixed point `Γ=tok(T({Γ}))`, as **explicit data**
  (use this, not `gExists_*`, to stay choice-free when you need the witness).
- `gGen T = {Γ}` (`singletonSys`); `gBase : {Γ} ◁ T({Γ})` (inlined `gExists_singleton_subsystem` body
  at the explicit `Γ`).
- tower `gTower T n = Tⁿ({Γ})` (`gChain` base `gBase`, step `obj_subsystem`); `gTower_le`;
  `gTower_master` (all levels share master `Γ`).
- `gColim T hT = ⋃ₙ Tⁿ({Γ})` (∅-free `ScottSys` over `Str`; `inter_mem` via `gTower_le`+`max`);
  `gTower_sub_colim : Tⁿ({Γ}) ◁ 𝒟`.
- **`gColim_obj_eq : T(gColim)=gColim`** (`ScottSys` equality). Membership half from `obj_continuous`
  on the directed tower (`T(⋃Tⁿ)=⋃Tⁿ⁺¹`, and the `n=0` level is absorbed by one `gChain` step);
  master half from `obj_subsystem (gTower_sub_colim 0)`. Helper `ScottSys.ext` (sys-equality ⟹ object
  equality; `ne` is a `Prop`).
- Instantiation: `Texp N = .oplus (.const N) (.sum (.prod .var .var) (.prod .var .var))`;
  `Texp_rooted (hN:Λ∈tok N)`; `Exp N hN := gColim (Texp N) _`; **`Exp_structure_eq : Texp(Exp)=Exp`**
  — the domain-equation iso (structure map = `idMap`).

**Phases 2–4 remaining (the evaluation map + initiality). Recommended plan:**
- **Phase 2 — algebras & decomposition.** Build a `Category` of `ScottSys` + **strict** maps (mirror
  `Exercise617`'s `StrictDomainObj` instance but over fixed `Str`; `GExpr.map_comp` needs strict `g`,
  so the strict-map category is forced). Make `Texp N` an `Endofunctor` of it (reuse `GExpr.map_id`,
  `map_comp`, `map_isStrict`). A `Texp`-algebra `(D,k)` decomposes — via element-level injections of
  `⊕`/`+`/`×` — into `s:N→D` (strict), `u,v:D×D→D`. The project has the *map* actions
  `sumMapTok`/`prodMapTok`/`oplusMapTok`/`otimesMapTok` (6.21) already; element-level injections may
  need adding (cf. `Exercise617`'s `sinj0/1/2`).
- **Phase 3 — descent `val(s)`.** Mirror `Theorem614` lines ~285–362 concretely: `colimAlg` = `Exp`
  with structure map `idMap` (from `Exp_structure_eq`); existence of a strict hom via the project's
  concrete **Theorem 6.9** (`Theorem69.lean`, homomorphisms out of a fixed point `D ≅ T(D)`). `val(s)`
  is that hom for the algebra `(D,s,u,v)`.
- **Phase 4 — uniqueness ⟹ `IsInitial`.** Mirror `Theorem614` lines ~303–598 concretely: projections
  `ρₙ = iₙ∘jₙ` from `gTower_sub_colim n` (Prop 6.12), `T(ρₙ)=ρₙ₊₁` (here MUCH easier than the abstract
  `map_rho_heq`: no `HEq`, just `GExpr.map_comp`/`map_id`), `⋃ₙρₙ=I` (`iSupMap`), and `g∘ρₙ` is
  `g`-independent (base `ρ₀=⊥` since `{Γ}` is one-point; step: homomorphism square). Conclude
  uniqueness of strict homs ⟹ `IsInitial`.
- **Known gotcha:** `oplusMapTok_comp`/`otimesMapTok_comp` (so `GExpr.map_comp`) REQUIRE strict `g` —
  stay in the strict category; the `⊕` `N`-summand injection must respect the coalesced bottom
  (collapse row), cf. 6.21's `oplusMapTok`.

## Checkpoint — 2026-06-21: Exercise 6.23 **Phases 2–3 COMPLETE + Phase 4 partial** (`Exercise623.lean`)

Continuing 6.23. Everything choice-free (`#print axioms ⊆ {propext, Quot.sound}`); full `Domain`
green (3092 jobs). New content all in namespace `Domain.Neighborhood.Exercise619`; added
`import Domain.Neighborhood.Theorem69` and `open Domain.Neighborhood.Exercise510` (for `StrictMap`,
`IsStrict`, `isStrict_idMap`, `isStrict_constBot`, `isStrict_comp`).

**Phase 2 — the strict-map category, the endofunctor, the algebra.**
- `instance : Category ScottSys` — objects = `ScottSys` (∅-free systems over the *fixed* token type
  `Str`), morphisms = `StrictMap A.sys B.sys`; `id`/`comp`/laws from Theorem 2.5 (`idMap_comp`,
  `comp_idMap`, `comp_assoc`) + `isStrict_idMap`/`isStrict_comp`. The fixed carrier `Str` is exactly
  what removes the `HEq` carrier-transport that made the abstract `Endofunctor DomainObj` (Thm 6.14)
  unusable. Simp lemmas `ScottSys.id_val`/`ScottSys.comp_val` (both `rfl`).
- `gFunctor (T : GExpr) : Endofunctor ScottSys` — `obj := T.obj`, `map := gFunctorMap T` (a strict
  `f ↦ ⟨T.map f.1, T.map_isStrict …⟩`), functoriality from `GExpr.map_id`/`map_comp` (the latter's
  `IsStrict g` is automatic — every morphism here is strict). `TexpF N := gFunctor (Texp N)`.
- `isoOfObjEq` (identity iso from an object equality), `ExpIso : T(Exp)≅Exp` (= `isoOfObjEq
  Exp_structure_eq`), and `ExpAlg N hN : TAlgebra (TexpF N)` with structure map `ExpIso.hom` (the
  identity, since `T(Exp)=Exp`). This is the "construe the initial solution as a syntactic domain"
  half.

**Phase 3 — the evaluation homomorphism `val(s)` (existence).** Since the structure map `i` is the
**identity** (`Exp_structure_eq`), the homomorphism equation `val∘i = k∘T(val)` is the fixed-point
equation `val = k∘T(val)∘j`. Solved by **Kleene iteration directly** (no need to re-derive Thm 6.9's
`homOp`/`strictFun` machinery):
- raw helpers `algStr B := B.str.1`, `expHom`/`expInv` (the iso's `i`/`j` as raw maps, ascribed
  through `StrictMap`), with `expInv_comp_expHom`/`expHom_comp_expInv` from the iso laws.
- `descRel : ℕ → ApproximableMap Exp.sys D.sys` (`val₀ = constMap ⊥`,
  `valₙ₊₁ = (algStr B)∘(T(valₙ))∘expInv`); `descRel_isStrict`, `constBot_le` (the `⊥` map is least),
  `descRel_le_succ`/`descRel_mono` (increasing), `descDir`/`descDirLe`.
- `descMap := iSupMap descRel descDir` (= `⋃ₙ valₙ`), `descMap_isStrict`.
- `descMap_fix : descMap = (algStr B)∘(T(descMap))∘expInv` — the decisive step, via
  `GExpr.map_continuous` (`T(⋃valₙ)=⋃T(valₙ)`) and the index-shift `⋃valₙ₊₁=⋃valₙ`.
- `descComm : descMap∘expHom = (algStr B)∘T(descMap)` (conjugate `descMap_fix` by `i`, using
  `j∘i=I`), packaged as **`descAlgHom : AlgHom (ExpAlg N hN) B`** — Scott's evaluation map exists.

**Phase 4 (partial) — `descAlgHom` is the *least* homomorphism.**
- `algHom_fix (g)` : every hom `g` is itself a fixed point `g = (algStr B)∘T(g)∘expInv` (from
  `g.comm` rearranged by `i∘j=I`).
- `descRel_le_algHom`/`descMap_le_algHom` : `val ≤ g` for every hom `g` (the Kleene iterates lie
  below any fixed point; induction + monotonicity of `λh.k∘T(h)∘j`).

**Phase 4 remaining — the reverse `g ≤ val` ⟹ `IsInitial`. Precise roadmap:**
- Build `ρₙ = iₙ∘jₙ : Exp → Exp`, `iₙ = (gTower_sub_colim n).inj`, `jₙ = (gTower_sub_colim n).proj`
  (Prop 6.12, `Subsystem.inj`/`proj`; these depend only on the two systems, not the `◁` proof).
- **Crux lemma** `GExpr.map (h.inj) = (obj_subsystem h).inj` and the `proj` analogue, by induction
  over the 6 constructors (this is the *concrete* `MonotoneAt.inj_heq`/`proj_heq` of Def 6.13). The
  `const`/`var` cases are immediate (`idMap = refl.inj` by `idMap_rel`); the four binary cases need
  `sumMapTok hA.inj hB.inj = (sumTok_subsystem hA hB).inj` etc. (match the tagged-token relations;
  `⊕`/`⊗` carry the `≠Δ`/collapse-row conditions). From it, `GExpr.map ρₙ = ρₙ₊₁` (use
  `GExpr.map_comp` [needs `iₙ` strict] + the equality `T(Exp)=Exp` = `gColim_obj_eq` to retype the
  codomain; recall `gTower (n+1) = T.obj (gTower n)` is `rfl`).
- Then mirror `Theorem614` concretely: `key_rho` (`ρₙ₊₁ = expHom∘T(ρₙ)∘expInv`), `⋃ₙρₙ = I`
  (`iSupMap` + `rho_rel`-style description), `ρ₀ = ⊥` (since `{Γ}` is one-point), `g∘ρₙ`
  `g`-independent and `= descRel n` (homomorphism square + `algHom_fix`), hence `g = ⋃ g∘ρₙ = ⋃
  descRel n = descMap` ⟹ uniqueness ⟹ **`IsInitial (ExpAlg N hN)`**.
- Optional (Scott's "explain the algebras"): decompose a structure map `k : T(D)→D` into `s:N→D`
  (strict), `u,v:D×D→D` via element-level injections of `⊕`/`+`/`×` (cf. Ex 6.17's `sinj0/1/2`); then
  `descAlgHom` for `(D,s,u,v)` *is* `val(s)`.

**Lean gotchas this session (reuse next time).** (1) `f.1` on a `Category.Hom`-typed term often fails
to reduce through the class projection (`instCategoryScottSys.1 X Y` "not of the form `C …`"); fix by
**typing helpers with `StrictMap` directly** (defeq to `Hom`) or **ascribing** `(f : StrictMap _ _).1`.
The `ScottSys.id_val`/`comp_val`/`gFunctorMap_val` simp lemmas (all `rfl`) bridge `⊚`/`id`/`gFunctor`
to raw `.comp`/`idMap`/`GExpr.map`. (2) `congrArg Subtype.val g.comm` lands the categorical comm
square at the raw `.comp` level **by defeq** — use it (and `show …`) instead of fighting `simp`.
(3) `rw [hcomm]`/`rw [comp_assoc]` repeatedly failed with "pattern not found / unsolved `X=X`" on
defeq-but-not-syntactic implicits (the `↑g.hom` vs `g.hom.1` display is a tell) — switch to
**term-mode `calc` with `congrArg (fun m => m.comp …)`** and `(comp_assoc _ _ _).symm`, which bridge by
defeq. (4) `StrictMap`/`isStrict_idMap`/`isStrict_constBot` live in `Exercise510`; `isStrict_comp`/
`comp_mono_gen` in `Theorem69` — both imported/opened now.

## 2026-06-21 — Exercise 6.23 Phase 4 COMPLETE (`ExpInitial`), green, choice-free

`Exercise623.lean` builds green, **zero `sorry`**, wired in `Domain.lean`. Phase 4 (uniqueness ⟹
initiality) is done; `#print axioms ExpInitial = {propext, Quot.sound}` (and likewise
`descMap_eq_algHom`, `key_rho`, `GExpr.map_inj/map_proj`, `iSupRho_eq_id`, `gcomp_rho_eq`, and all 8
token `*MapTok_inj/proj` lemmas).

What landed (all in the `Uniqueness`/crux sections of `Exercise623.lean`):
- `Subsystem.inj_isStrict`/`proj_isStrict`/`self_inj`/`self_proj` (Prop 6.12 helpers).
- The **8 token lemmas** `sum/prod/oplus/otimesMapTok_inj` + `_proj`: the functor's token actions
  carry Prop-6.12 projection pairs, e.g. `otimesMapTok h0.inj h1.inj = (otimesTok_subsystem h0 h1).inj`.
- **Crux** `GExpr.map_inj : T.map h.inj = (T.obj_subsystem h).inj` and `GExpr.map_proj` (induction over
  the 6 constructors; `const/var` immediate, 4 binary cases discharged by the token lemmas).
- The projection chain `expSub n : (gTower (Texp N) n).sys ◁ (Exp N hN).sys`, `rho n = iₙ.comp jₙ`,
  `rho_rel`, `rho_mono`, `iSupRho`, **`iSupRho_eq_id : ⋃ₙ ρₙ = I_Exp`**, `rho_zero_rel` (`ρ₀ = ⊥`).
- `map_rho_eq : T(ρₙ) = i'ₙ∘j'ₙ` and **`key_rho : ρₙ₊₁ = expHom∘T(ρₙ)∘expInv`**.
- `gcomp_rho_zero/_succ/_eq` (`g∘ρₙ = descRel n`, `g`-independent), `descMap_eq_algHom`
  (`g.hom.1 = descMap`), `algHom_ext`, and **`ExpInitial : IsInitial (ExpAlg N hN)`**.

**Bug fixes this session (the build that was red on resume).** (a) `gTower` takes `(T : GExpr)` then
`(n : ℕ)` — it does **not** take the `RootedConst` proof; `expSub`/`rho_rel` had a stray
`(Texp_rooted hN)` arg (`gTower_sub_colim`/`gTower_le`/`gColim_master` *do* take it). (b) `key_rho`:
chained `rw [comp_rel, comp_rel, …]` is brittle on nested comps — use
`rw [map_rho_eq]; simp only [comp_rel, rho_rel, expInv_rel, expHom_rel, Subsystem.proj_rel,
Subsystem.inj_rel, hsyseq]`. (c) the `rw [hcomm]`/`rw [map_comp …]` calc steps: replace with
term-mode `congrArg (fun m => …) hcomm` / `…map_comp …).symm` (gotcha #3). (d) `descMap_eq_algHom`'s
final `rw [← comp_idMap, ← iSupRho_eq_id]` failed on `idMap (ExpAlg…).carrier.sys` vs `idMap (Exp…).sys`
(defeq, not syntactic) — replace with a `calc … := by rw [iSupRho_eq_id hN]; exact (comp_idMap _).symm`
that closes by **defeq via `exact`**.

**NEW gotcha — `Eq.le` on `Set` drags in `Classical.choice`.** `(h : s = t).le` to get `s ⊆ t`
silently depends on `Classical.choice` (the `Set` `Preorder`/`le_of_eq` path). This is what made the
sum/oplus/otimes token lemmas (and everything downstream incl. `ExpInitial`) non-choice-free. **Fix:
use `(h : s = t).subset`** (`Eq.subset`, choice-free) — or `subset_rfl`. `prodMapTok_*` was already
clean precisely because it had no master case and never used `.le`. Bisect choice provenance with
`#print axioms` + temporarily `sorry`-ing branches (setup vs. branch bodies).

---

## Checkpoint — Exercise 6.24 COMPLETE (double fixed point) — 2026-06-22

**Status:** `lake build Domain` green (3093 jobs), zero `sorry`. New module `Exercise624.lean`
(namespace `Domain.Neighborhood.Exercise624`), wired into `Domain.lean`. Axiom audit on
`exists_double_fixedPoint`, `exists_simultaneous_subsystems`, `Dsol_subsystem`, `Esol_subsystem`
all `⊆ {propext, Quot.sound}` (choice-free).

**What Exercise 6.24 asks.** Show there exist domains with `D ≅ D+(D×E)` and `E ≅ D+E` *by a double
fixed-point method*: decide the tokens, then define `D, E` by simultaneous fixed points. This is the
**simultaneous** analogue of 6.20/6.21 — those exercises deliver a single `Γ` with `{Γ} ◁ T({Γ})`
("so 6.14 applies"); 6.24 delivers a **pair** `(Γ_D, Γ_E)` solving two coupled token equations at
once, whence the two singleton systems are subsystems of the two right-hand sides simultaneously =
the joint hypothesis of the simultaneous Theorem 6.14.

**Design (concrete, no bivariate `FExpr` needed).** Both `D, E` are `∅`-free systems over the single
token type `Str = {0,1}*`. Over `{0,1}*` the sum `+` and product `×` share the master shape
`{Λ} ∪ 0·(…) ∪ 1·(…)`, so the two token recursions collapse to:
- `gTok p q = tok(D+E) = insert [] (embBit false p ∪ embBit true q)`;
- `fTok p q = tok(D+(D×E)) = gTok p (gTok p q)`  (the inner `gTok p q` is `tok(D×E)`).

**Key continuity insight.** `mem_gTok_iUnion`/`mem_fTok_iUnion`: every token of `*Tok (⋃ aₙ)(⋃ bₙ)`
lands in some *single* `*Tok aₙ bₙ`. Reason: each concrete token (`[]`, `0w'`, `1[]`, `1(0u')`,
`1(1u')`) references **at most one** of the two coordinates, even in `fTok`'s nested `true`-branch —
so **no directedness merge is needed** (unlike the abstract continuity-on-domains lemmas). This makes
the fixed point fall out from just monotonicity + this additivity; the chain need not even be proved
increasing.

**The double fixed point.** `pIter : ℕ → Set Str × Set Str`, `Φ(p,q) = (fTok p q, gTok p q)` from
`({Λ},{Λ})`; `GammaD = ⋃ₙ (pIter n).1`, `GammaE = ⋃ₙ (pIter n).2`. `fTok_GammaD_GammaE`,
`gTok_GammaD_GammaE` (⊇: `fTok_mono`/`gTok_mono` + `pIter_*_subset_*`; ⊆: additivity lemma landing at
stage `n+1`). Capstone `exists_double_fixedPoint`.

**Object level.** `Dsol = {Γ_D}`, `Esol = {Γ_E}` (`singletonSys`); `Fsol D E = D.sum (D.prod E)`,
`Gsol D E = D.sum E`. `master_Fsol`/`master_Gsol` are **`rfl`** (the sum/product masters defeq-expand to
`fTok`/`gTok`). `Dsol_subsystem : {Γ_D} ◁ D+(D×E)` and `Esol_subsystem : {Γ_E} ◁ D+E` by the
singleton-subsystem pattern (cf. `exists_singleton_subsystem`); `exists_simultaneous_subsystems`
packages both.

**Choice-discipline gotcha (reuse).** `Set.subset_iUnion` is **classical** (drags in
`Classical.choice`). For a choice-free `(s i) ⊆ ⋃ i, s i`, prove it by hand:
`fun _ hx => Set.mem_iUnion.mpr ⟨i, hx⟩` (here `pIter_fst_subset_GammaD`/`pIter_snd_subset_GammaE`).
`Set.mem_iUnion` itself is choice-free. (Also: `(pIter 0).1` does not match `{·}` for
`Set.mem_singleton_iff`; use `have hw0 : w = [] := hn` — singleton membership is defeq to `=`.)

**Next concrete target:** Exercise 6.25 (projection-pair `g,h` identities on elements:
`g(x) ⊑ y ↔ x ⊑ h(y)`, the Galois connection, and the two extremal formulas for `h`/`g`).

---

## Checkpoint 2026-06-22 — Exercise 6.25 COMPLETE (`Exercise625.lean`)

**Status:** `lake build Domain` green (3094 jobs), zero `sorry`. All 7 results choice-free
(`#print axioms ⊆ {propext, Quot.sound}`). Wired into `Domain.lean` after `Exercise624`.

**What it proves.** Exercise 6.25 is entirely *element-level* reasoning about an abstract projection
pair, so I reused `Subsystem.ProjectionPair D E` (from `Proposition612.lean`) directly — no new
domain construction. Scott's `g = P.inj`, `h = P.proj`. Namespace
`Domain.Neighborhood.Subsystem.ProjectionPair`.

- **Two laws on elements** (the only inputs to everything else):
  - `proj_inj_apply : h(g x) = x` — `rw [← toElementMap_comp, P.proj_comp_inj, toElementMap_idMap]`.
  - `inj_proj_apply_le : g(h y) ⊑ y` — `le_iff_toElementMap_le.mp P.inj_comp_proj_le` then
    `rw [toElementMap_comp, toElementMap_idMap]`.
- **`galois : g(x) ⊑ y ↔ x ⊑ h(y)`** — `→` apply monotone `h` then `h(g x)=x`; `←` apply monotone
  `g` then chain through `g(h y) ⊑ y`. (`toElementMap_mono` is Prop 2.2(iii).)
- **`proj_eq_sSup : h(y) = ⊔{x ∣ g(x) ⊑ y}`** — `lowerSet y := {x ∣ g(x)⊑y}`; by `galois` it is the
  down-set `{x ∣ x⊑h(y)}`, so `lowerSet_bounded` (bound `h(y)`) and `lowerSet_directed` (top `h(y)`,
  membership = `inj_proj_apply_le`). Equality by `le_antisymm` of `D.le_sSup`/`D.sSup_le`
  (Exercise 1.27's bounded `sSup`).
- **`inj_eq_sInf : g(x) = ⊓{y ∣ x ⊑ h(y)}`** — `upperSet x := {y ∣ x⊑h(y)}`; `upperSet_nonempty`
  contains `g(x)` (since `x ⊑ h(g x)=x`). Equality by `le_antisymm` of `E.le_sInf`/`E.sInf_le`
  (Exercise 1.18's `sInf`; needs only `Nonempty`, not bounded).
- **`inj_bounded`** — `g` maps consistent (=bounded, per Ex 1.27) sets to bounded sets: image of a
  set bounded by `b` is bounded by `g(b)` (monotone). True of any approximable map; the real content
  is the next one.
- **`inj_sSup : g(⊔S) = ⊔{g(s) ∣ s∈S}`** — `g` (lower adjoint) preserves **all** lubs, not just
  directed ones. `⊒` is monotonicity; `⊑` is the adjoint trick: `(galois ..).mpr` reduces to
  `⊔S ⊑ h(⊔{g s})`, then `sSup_le` reduces to each `s ⊑ h(⊔{g s})`, then `(galois ..).mp` reduces to
  `g(s) ⊑ ⊔{g s}` = `le_sSup`.

**Lessons / reusable facts.**
- `le_iff_toElementMap_le` (Thm 3.13(i), top-level in `Domain.Neighborhood`, *not* inside
  `ApproximableMap`) is the bridge from a `≤` between approximable *maps* to a `≤` between their
  element images — exactly what turns `inj_comp_proj_le : g∘h ≤ I` into `g(h y) ⊑ y`.
- Two bounded-sup APIs coexist: `sSupDirected` (`Approximable.lean`, directed families, the lub used
  by continuity) vs. `Bounded`/`sSup` (`Exercise127.lean`, *any* bounded set, built from `sInf` of
  upper bounds). Exercise 6.25's "not just directed unions" needs the **`Exercise127` `sSup`**.
- `ProjectionPair` lives over a *single* token type `α` (both `D E : NeighborhoodSystem α`), so
  `D.Bounded`/`D.sSup`/`E.sInf` all apply with no cross-type plumbing.

**Next concrete target:** Exercise 6.26 (`𝒟_⊥` lift, functoriality, `𝒟_⊥ ⊕ ℰ_⊥ ≅ 𝒟 + ℰ`).

---

## Checkpoint — Exercise 6.26 (the lifting `𝒟_⊥`) COMPLETE

`Domain/Neighborhood/Exercise626.lean`, namespace `Domain.Neighborhood.Exercise619` (reopened, as
`Exercise621` does, to reuse `sumTok`/`oplusTok`/`otimesTok`/`prodTokNbhd` + their membership lemmas).
Wired into `Domain.lean`; `lake build Domain` green.

**Object.** `liftTok D _hD` over `Str = {0,1}*` with master `liftTokMaster D = insert [] (embBit false D.master)`
(`= {Λ}∪0Δ`) and proper neighbourhoods `embBit false X = 0X` for every `X∈𝒟` (incl. `0Δ`, strictly above
the new bottom). `∅`-free (`liftTok_nonempty`); packaged as `ScottSys.lift`. (The nonempty hypothesis is
unused inside the system itself — hence the binder `_hD` — but carried for the `ScottSys` packaging.)

**Elements — `|𝒟_⊥| ≅ |𝒟|_⊥`.** `liftBot` (mem `W ↔ W = master`) is the fresh least element
(`liftBot_le`); `liftUp x = {master}∪{0X∣X∈x}` is an order embedding (`liftUp_le_liftUp_iff`) sitting
strictly above it (`liftBot_lt_liftUp`, via `embF_ne_liftTokMaster`). `unlift z hz = {X∣0X∈z}` (needs
`hz : z.mem 0Δ`) with `liftUp_unlift`, and the covering `eq_liftBot_or_exists_liftUp`. The covering is the
**only** non-`{propext,Quot.sound}` result: it case-splits on `z.mem 0Δ` (excluded middle), unavoidable.

**Functor — "is this a suitable functor?" yes (strict).** `liftMapTok f` (rel: a *collapse-to-master*
row `(W∈𝒟_⊥ ∧ W'=master)` ∨ a copy row `0X→0X'` from `f.rel X X'`), with `liftMapTok_isStrict` (for any
`f`), `liftMapTok_id`, `liftMapTok_comp` — the one-summand analogue of 6.19's `sumMapTok`.

**`𝒟_⊥ ⊕ ℰ_⊥ ≅ᴰ 𝒟 + ℰ`** (`lift_oplus_lift_iso_sum`). Element `OrderIso` `sumLiftEquiv` built from
`toSumLift`/`fromSumLift`: the `⊕` of the lifts has tokens `00X'` (`X'∈𝒟`) / `10Y'` (`Y'∈ℰ`) over the
shared bottom; the iso *deletes the inner `0`* (`00X'↔0X'`, `10Y'↔1Y'`). Cross-tag (`0`vs`1`) intersections
vanish by `∅`-freeness — structurally exactly 6.19's `toSum`/`fromSum` with one extra `embBit false`.

**`𝒟_⊥ ⊗ ℰ_⊥ ≅ᴰ (𝒟 × ℰ)_⊥`** (`lift_otimes_lift_iso_lift_prod`) — the answer to Scott's `??`. The smash
of the lifts has proper rectangles `prodTokNbhd (0X') (0Y')`; the lift of the product has `0(prodTokNbhd X' Y')`.
`liftProdEquiv` (`toLiftProd`/`fromLiftProd`) transports one to the other; purely rectangular (no
cross-empties), so cleaner than the sum.

**Gotcha for future work (recorded once).** The reused membership/closure lemmas for `oplusTok`/`sumTok`
(`oplusTok_mem_master`, `sumTok_mem_embF`, `*_mem_embF_inv`, `oplusTok_nonempty`, …) carry the `∅`-free
witnesses `h₀ h₁` as *implicit* arguments that appear **only under `.mem`** — which the unifier reduces
away — so they are **not** inferred from the goal/expected type. Pass them explicitly
(`(h₀ := D.ne) (h₁ := E.ne)`, or use the packaged `(D.lift.oplus E.lift).ne`), or just use `Or.inl rfl`
for master membership. Likewise pass `(D₀ := …) (D₁ := …)` to `sumTokMaster_inter_embF/T` when the goal
spells the system as a `.lift.sys` projection (folded) but the lemma would unfold it (`rw` needs a
syntactic match). This affected ~10 sites here.

**Axioms.** All of `liftTok`, `ScottSys.lift`, order facts, `liftMapTok*`, `lift_oplus_lift_iso_sum`,
`lift_otimes_lift_iso_lift_prod` audit to `{propext, Quot.sound}`; `eq_liftBot_or_exists_liftUp` additionally
uses `Classical.choice` (the lone, called-out excluded-middle split).

---

## Checkpoint — Exercise 6.27 COMPLETE (`Exercise627.lean`, ns `Exercise627`)

**Which subsystem relations `⊴` (Lemma 6.15 *embeds-as-subdomain*) hold.** Verdict: **the first five
hold for all `𝒟,ℰ`; the sixth `𝒟 ⊴ 𝒟⊗ℰ` is false in general.** Wired into `Domain.lean`; full
`Domain` green, zero `sorry`. Concrete `{0,1}*` constructors of Ex 6.19/6.21 + function spaces
(`FunctionSpace.lean`, Ex 5.10).

- **(1) `(𝒟⊗ℰ)◁(𝒟×ℰ)`** `otimesTok_subsystem_prodTok` ⟹ `otimes_trianglelefteq_prod` (`Subsystem.trianglelefteq`): smash is literally a subsystem of the product (same master, sub-family of proper rectangles, boundary-stable intersections).
- **(2) `𝒟 ⊴ 𝒟×ℰ`** `fst_trianglelefteq_prod` via projection pair `fstInj X↦(X,Δ₁)` / `fstProj`, `trianglelefteq_of_projectionPair`.
- **(3) `(𝒟⊕ℰ)◁(𝒟+ℰ)`** `oplusTok_subsystem_sumTok` ⟹ `oplus_trianglelefteq_sum`: coalesced sum drops `0Δ₀`,`1Δ₁`; cross-tag intersections empty.
- **(4) `𝒟 ⊴ 𝒟⊕ℰ`** `inl_trianglelefteq_oplus` via `inlInj`/`inlProj` with `leftN X` (`=0X` proper / `sumTokMaster` at `X=Δ₀`). **Only classical part:** `oplus_mem_leftN` decides the undecidable `X=Δ₀` ⟹ `Classical.choice` (genuinely unavoidable over arbitrary systems; flagged).
- **(5) `(𝒟→⊥ℰ)⊴(𝒟→ℰ)`** `strictFun_trianglelefteq_funSpace` — **general `V₀ V₁`, choice-free**. Inclusion `inclMap` + strictification retraction `strctMap`, built by `ofMono` from elementwise `incl=toFilter∘val∘toStrictMap`, `strct=toStrictFilter∘strictify∘toApproxMap`. New `strictifyMap` (force `Δ₀↦Δ₁`); `strictifyMap_le`, `strictifyMap_of_isStrict`. Crux union formulas `toElementMap_inclMap`/`toElementMap_strctMap` (via `mem_stepFun_iff`/`mem_sstepFun_iff`); then `strct_incl`/`incl_strct_le` collapse via the four equiv-inverse lemmas (`toApproxMap_toFilter`, `toStrictMap_toStrictFilter`, …). Comp laws use a **choice-free** local `ext_of_principal` (extracts `mem` from `rel_dom`, avoiding `ext_of_toElementMap`'s `by_cases` — which silently pulls in `Classical.choice`) and `le_iff_toElementMap_le`.
- **(6) `¬(𝒟 ⊴ 𝒟⊗ℰ)`** `not_trianglelefteq_otimes`: counterexample `ℰ=𝟙` (`unitPt`). `otimes_unitPt_collapse` ⟹ `twoPt⊗𝟙` has only its master ⟹ `subsingleton_element_of_only_master` (one-point lattice), but `twoPt` has two elements — contradicts iso injectivity.

**Axioms.** Parts 1–3, 5, 6 audit to `{propext, Quot.sound}`; part 4 (`inl_trianglelefteq_oplus`)
additionally uses `Classical.choice` (the single documented `X=Δ₀?` split). **Gotcha recorded:** the
standard extensionality `ext_of_toElementMap`/`eq_of_toElementMap_principal` do a `by_cases V₀.mem X`,
which brings in `Classical.choice`; when you need a *choice-free* map equality from agreement on
principals, use the `rel_dom`-based `ext_of_principal` pattern instead.

**Next concrete target:** Exercise 6.29 (infinitary `∑_n D_n`, `∏_n D_n`; `⊕`,`⊗`?).

---

## Checkpoint — Exercise 6.28 COMPLETE (`Exercise628.lean`, ns `Domain.Neighborhood`) — 2026-06-22

**Statement (Plotkin).** If `𝒟,ℰ` are *finite* systems and `𝒟 ⊴ ℰ ⊴ 𝒟`, then `𝒟 ≅ ℰ`. Need the
same for infinite systems? Wired into `Domain.lean`; full `Domain` green, zero `sorry`.

**The one idea.** `⊴` is *stronger* than a plain order embedding (it is a retract), but the proof
only needs the embedding. `Trianglelefteq.elementEmbedding : (D ⊴ E) → Nonempty (|D| ↪o |E|)`:
unfold `⊴` to `e : |D| ≅o |D'|` with `D' ◁ E`; Prop 6.12 turns `D' ◁ E` into the projection pair
`i = hsub.inj`, `j = hsub.proj` with `j ∘ i = I` (`proj_comp_inj`); then `projElementEmbedding i j hji`
is an order embedding `|D'| ↪o |E|` — built by `OrderEmbedding.ofMapLEIff i.toElementMap`, with `≤`
both ways: forward is `toElementMap_mono i`, backward applies the *monotone left inverse* `j`
(`toElementMap_mono j` to `i(a) ⊑ i(b)`, then rewrite by the round-trip
`j(i(x)) = (j∘i)(x) = I(x) = x` from `toElementMap_comp`/`hji`/`toElementMap_idMap`). Compose with
`e.toOrderEmbedding` (`RelEmbedding.trans`).

**Finite Schröder–Bernstein.** `orderIso_of_embeddings {P Q} [Finite P] [Finite Q] (f : P ↪o Q)
(g : Q ↪o P) : Nonempty (P ≃o Q)`: order embeddings are injective, so
`Fintype.card_le_of_injective` both ways gives equal card, `Fintype.bijective_iff_injective_and_card`
makes `f` bijective, and the `OrderIso` is `{ toEquiv := Equiv.ofBijective f hbij,
map_rel_iff' := f.map_rel_iff' }`.

**GOTCHA (recorded).** `StrictMono.orderIsoOfSurjective` needs `[LinearOrder]`; element domains are
only `PartialOrder`. A surjective *strictly monotone* map is **not** an order iso on partial orders
— but a surjective *order embedding* (which reflects `≤`) is. So build the iso from the bijective
embedding's `map_rel_iff'` directly, never via `orderIsoOfSurjective`.

**Finite system.** `NeighborhoodSystem.IsFinite D := Finite {X // D.mem X}` (finitely many
neighbourhoods). `finite_element_of_isFinite : D.IsFinite → Finite |D|`: a filter is pinned by which
neighbourhoods it contains, so `x ↦ {p | x.mem p.1}` injects `|D| ↪ Set {X // D.mem X}` (off-`D`
sets are in neither filter by `x.sub`); finite powerset of a finite type. Faithful theorem
`isomorphic_of_finite_system` just `haveI`s the two `Finite |·|` and calls the core.

**Need the same for infinite systems? No.** Plotkin's argument is a finite cardinality count with no
infinite analogue; the retraction preorder on infinite dcpos fails Cantor–Schröder–Bernstein
(Eilenberg-swindle obstruction). The infinite counterexample is recorded as prose only — out of this
file's scope (would require building two non-isomorphic infinite systems that are mutual retracts).

**Axioms.** `projElementEmbedding`, `Trianglelefteq.elementEmbedding` are choice-free
`{propext, Quot.sound}`. `orderIso_of_embeddings`, `finite_element_of_isFinite`, and both main
theorems add `Classical.choice` (extracting `Fintype` from `Finite` / a section of the surjection) —
genuinely unavoidable and confined to the finite count.

---

## Checkpoint — 2026-06-22 — Exercise 6.29 COMPLETE (infinitary `∑`, `∏`; `⊕` yes, `⊗` no)

`Exercise629.lean` (ns `Domain.Neighborhood.Exercise629`), wired into `Domain.lean`, full `Domain`
green, zero `sorry`. Index family `D : ∀ i, NeighborhoodSystem (α i)` over `α i` (`ℕ` intended).

**The four operations.**
- **`iprod` `∏_i D_i`** — cylinders `iprodNbhd X = {p | p.2 ∈ X p.1}`, `X i ∈ 𝒟ᵢ`, master off a finite
  support. Headline **infinitary Prop 3.2**: `iprodEquiv : |∏_i D_i| ≃o ∀ i, |D_i|` (pointwise order).
- **`isum` `∑_i D_i`** — separated sum over `Option (Σ i, α i)`: basepoint master `sumMasterI` or one
  tagged copy `injI i X`. `isum_trichotomy`, `isum_summand_unique`.
- **`ioplus` `⊕_i D_i`** — coalesced sum (as `∑`, improper copies deleted). Generalizes fine.
- **`iotimes` `⊗_i D_i`** — smash. Proper = every coordinate proper ⟹ over infinite `ι` clashes with
  finite support ⟹ `iotimes_only_master`/`iotimes_subsingleton`: a one-point domain. **`⊗` does not
  generalize.** Answer to Scott's question: `+`,`×`,`⊕` generalize; `⊗` degenerates.

**Choice discipline (the hard part — went from pervasive `Classical.choice` to clean).**
- Finite support is the **positive `List` form** `FinSupp D X := ∃ l, ∀ i, i ∉ l → X i = master`. The
  negative form (`X i ≠ master → i ∈ l`) forces double-negation elimination on undecidable set
  equality (`X i = master`) in `FinSupp.inter`/reconstruction ⟹ choice. The positive form makes both
  constructive (outside `l ++ l'`, `master ∩ master = master`; the support equality `restrictTo l X = X`
  is `(hl j h).symm`).
- `Function.update_eq_self` is **classical** — prove `updTuple D i master = (fun j => master)` by
  `funext` + `by_cases j = i` (`updTuple_apply_self`/`_ne`, both `propext`-only).
- In `injI`-intersection `inter_mem` proofs (`isum`/`ioplus`), do **not** `by_cases i = j` (classical,
  no `DecidableEq`): recover `i = j` constructively from the consistency witness `Z` via
  `index_of_some_mem_injI`. Same trick makes `isum_summand_unique` choice-free.
- Mathlib pitfalls pulling choice: `Set.Finite`, `Function.update_eq_self`, `List.mem_toFinset`,
  `Finite.of_fintype`, `not_forall`/`Infinite.exists_notMem_finset`.

**Axiom audit.** Data `iprod`, `isum`, `ioplus`, `iotimes`, `iprodEquiv`, plus `isum_summand_unique`,
`z_mem_of_slices`, `FinSupp.inter` — all `⊆ {propext, Quot.sound}`. Only `isum_trichotomy` (excluded
middle: does `z` reach a summand?) and `iotimes_subsingleton`/`iotimes_only_master` (cardinality via
classical `Set.Finite`) add `Classical.choice` — both Prop-level, genuinely classical, flagged in
their docstrings and the file header.

**Next concrete target:** Exercise 6.29 is **COMPLETE**; this finishes Lecture VI's formalization. The
next frontier is **Lecture VII** (Defn 7.1 *computable presentation* onward), transcribed/inventoried
but formalization-deferred.

---

## Checkpoint 2026-06-22 — Lecture VII opens: **Definition 7.1 COMPLETE** (`Definition71.lean`)

**Modeling decision (user-chosen).** Lecture VII's "recursive / recursively enumerable" is modeled
with **genuine mathlib recursion theory**: `ComputablePred` (a predicate with a `Decidable` instance
whose `decide` is `Computable`) and `REPred` (domain of a `Partrec` function), over the integer
indices (`ℕ`, `ℕ×ℕ`, `ℕ×ℕ×ℕ` are all `Primcodable`). Imports: `Mathlib.Computability.Partrec` +
`Mathlib.Computability.RE`.

**CHOICE NOTE (applies to *all* of Lecture VII).** mathlib's recursion theory is **classical at its
foundation** — `#print axioms Computable.const` already lists `Classical.choice`. Therefore every
Lecture-VII computability theorem audits as `{propext, Classical.choice, Quot.sound}`. This is
**unavoidable and expected** under the chosen modeling, *not* a discipline slip: the construction
*data* (the enumeration `X`, the index functions) is still explicit and constructive; only the
*computability witnesses* (the `ComputablePred`/`REPred` proofs) are classical. Flag it, don't fight
it.

**What's in `Definition71.lean`:**
- `ComputablePresentation V` (structure): `X : ℕ → Set α`, `mem_X : ∀ n, V.mem (X n)`,
  `surj : V.mem Y → ∃ n, X n = Y`, and Scott's two decidable relations
  `interEq_computable : ComputablePred (fun (t:ℕ×ℕ×ℕ) => X t.1 ∩ X t.2.1 = X t.2.2)` (7.1(i)) and
  `cons_computable : ComputablePred (fun (t:ℕ×ℕ) => ∃ k, X k ⊆ X t.1 ∩ X t.2)` (7.1(ii)).
- `ComputablePresentation.incl_computable` — Scott's biconditional `Xₙ⊆Xₘ ↔ Xₙ∩Xₘ=Xₙ`
  (`Set.inter_eq_left`); proved by reindexing `(n,m)↦(n,m,n)` into (i) via `ComputablePred.computable_iff`
  + `Computable.pair/fst/snd`/`Computable.comp`.
- `ComputablePresentation.eq_computable` — `Xₙ=Xₘ ↔ Xₙ⊆Xₘ ∧ Xₘ⊆Xₙ` (`Set.Subset.antisymm_iff`);
  decision Bool `cond (f (n,m)) (f (m,n)) false` from `incl_computable`'s `f` (used `show … = ((cond …
  : Bool) : Prop)` to force the projections to reduce, then `cases`+`simp`).
- `NeighborhoodSystem.IsEffectivelyGiven V := Nonempty (ComputablePresentation V)`.
- `unitPresentation : ComputablePresentation unitSys` + `unitSys_isEffectivelyGiven` — the constant
  enumeration `Xₙ=Δ=univ`; both relations are always-true (`ComputablePred.computable_iff.2 ⟨fun _ =>
  true, Computable.const true, by funext; simp⟩`).

**Useful mathlib API found.** `ComputablePred` & `REPred` live in `Mathlib.Computability.RE`.
`ComputablePred.computable_iff : ComputablePred p ↔ ∃ f:α→Bool, Computable f ∧ p = fun a => (f a:Prop)`
is the workhorse for building derived deciders. `Computable.find` (in RE) turns a `ComputablePred`
+ totality into a `Computable` `Nat.find` — will be handy for the intersection-index function and
later constructions. `Computable.fst/snd/pair/comp/cond/const` for index plumbing. The Bool→Prop
coercion is `(b : Prop) := (b = true)`.

**Next:** Definition 7.2 — a *computable map* `f : 𝒟 → E` is one whose neighbourhood relation
`Xₙ f Yₘ` is `REPred` in `(n,m)` (r.e., not merely recursive — the `𝒟 = {Δ}` degeneration gives the
*computable element* notion: `{m | Yₘ ∈ y}` is r.e.). Will need the approximable-map infrastructure
(`ApproximableMap`) to phrase `Xₙ f Yₘ`.

---

## Checkpoint — Jun 22, 2026: Definition 7.1 redone CHOICE-FREE (bespoke recursion theory)

**What changed.** Definition 7.1 was previously formalized on Mathlib's `ComputablePred` and audited
`{propext, Classical.choice, Quot.sound}`. Per the decision to keep the project choice-free, it has
been **rebuilt on a bespoke, choice-free recursion theory** and now audits `{propext, Quot.sound}`.

**Why we rejected Mathlib here.** We audited Mathlib `v4.30.0`'s recursion theory and found
`Classical.choice` is pervasive in its *correctness lemmas* (not the inductives themselves): the
tactics `grind` and `lia` both pull `Classical.choice` (whereas `omega` does not), and the `@[simp]`
lemma `Nat.unpair_pair` is classical, which in turn makes `Computable.const`, `Primrec.const`,
`Nat.Primrec.id/add/mul`, `Nat.sqrt_le`, `Nat.unpair_pair`, … all classical. Since these are exactly
the lemmas any `ComputablePred`/`REPred` development leans on, **we roll our own recursion theory and
reject Mathlib in this case because it opens Classical and we are trying to avoid that.**

**New file `Domain/Neighborhood/Recursive.lean`** (ns `Domain.Recursive`), all `⊆ {propext, Quot.sound}`:
- choice-free `Nat.sqrt` correctness — `amGM`, `iter_sq_le`, `lt_iter_succ_sq` (faithful ports of
  Mathlib's `Nat.sqrt.iter_sq_le`/`lt_iter_succ_sq` with `grind`/`lia`→`omega`, plus a choice-free
  `lt_of_mul_lt_mul_left'` replacing the classical `Nat.lt_of_mul_lt_mul_left`), `sqrt_le`,
  `lt_succ_sqrt`, `sqrt_eq_of` (the `q²≤m<(q+1)² → sqrt m = q` characterization), `sqrt_add_eq`;
- `Nat.pair`/`unpair` round-trips — `unpair_pair` (+ `unpair_pair_fst/snd`), `sqrt_le_add`,
  `pair_unpair`;
- primitive-recursive arithmetic — `primrec_id`, `primrec_add`, `primrec_mul` (built ONLY from the
  choice-free `Nat.Primrec` constructors `zero/succ/left/right/pair/comp/prec`, with the
  `unpair_pair`-noise discharged by my choice-free round-trips + `omega`, via helpers `rec_add`/`rec_mul`);
- the predicate API — `RecDecidable p := ∃ f, Nat.Primrec f ∧ ∀n, p n ↔ f n = 1`, `RecDecidable₂`,
  `RecDecidable₃`, and closure `RecDecidable.of_iff` / `.comp` (reindex by any `Nat.Primrec` map) /
  `.and` (multiply `{0,1}` deciders; uses choice-free `nat_mul_eq_one`), plus `recDecidable_of_forall`.

**`Definition71.lean`** now states (i)/(ii) as `RecDecidable₃`/`RecDecidable₂`, derives
`incl_computable` (reindex `(n,m)↦(n,m,n)` via `RecDecidable.comp` + `Set.inter_eq_left`) and
`eq_computable` (`RecDecidable.and` of `incl` with its `swapPair` reindex + `Set.Subset.antisymm_iff`),
and `unitPresentation` via the constant-`1` decider `recDecidable_of_forall`. Wired into `Domain.lean`.

**Audits** (`#print axioms`): `incl_computable`, `eq_computable`, `unitPresentation`,
`unitSys_isEffectivelyGiven`, and every lemma in `Recursive.lean` → `{propext, Quot.sound}`.
`lake build Domain` green.

**Next:** Definition 7.2 (computable map / element) on top of `Recursive.lean` — will need an r.e.
analogue. The natural choice-free move is `RecEnumerable p := ∃ f, Nat.Primrec f ∧ ∀n, p n ↔ ∃k, f (pair n k) = 1`
(domain of a `Nat.Primrec` predicate / projection), staying within the same constructor-only discipline.

---

## Checkpoint — 2026-06-22 — Definition 7.2 COMPLETE (computable maps & computable elements), choice-free

**`Definition72.lean`** (ns `Domain.Neighborhood`), wired into `Domain.lean` after `Definition71`.
Formalizes Scott's Definition 7.2: an approximable map `f : 𝒟 → ℰ` between recursively presented
domains is *computable* iff the neighbourhood relation `Xₙ f Yₘ` is **recursively enumerable** in
`n, m`.

- **`IsComputableMap P Q f := REPred₂ (fun n m ↦ f.rel (P.X n) (Q.X m))`** — Definition 7.2 proper,
  relative to computable presentations `P` of `V`, `Q` of `W` (Def 7.1) and an `ApproximableMap f`.
- **`IsComputableElement Q y := REPred (fun m ↦ y.mem (Q.X m))`** — Scott's *computable element*: the
  `𝒟 = {Δ}` degeneration of 7.2, where `f` collapses to a single `y ∈ |ℰ|` whose index set
  `{m ∣ Yₘ ∈ y}` must be r.e.
- **`idMap_isComputable P : IsComputableMap P P (idMap V)`** — identity is computable (the identity
  half of Prop 7.3). The relation `Xₙ I Xₘ` is `Xₙ ⊆ Xₘ` (`incl_computable`), recursively
  *decidable* hence r.e. via `RecDecidable.re` (after `RecDecidable.of_iff` strips the `idMap_rel`
  `V.mem`-conjuncts using `mem_X`).
- **`principal_isComputableElement P n : IsComputableElement P (V.principal (P.mem_X n))`** — every
  finite (principal) element `↑Xₙ` is computable (Scott: "if `y` were finite, the set of indices
  would be recursive"). Its index set `{m ∣ Xₙ ⊆ Xₘ}` is a recursive **slice** of `incl_computable`:
  fix the first index by the choice-free primrec reindex `m ↦ Nat.pair n m`
  (`(Nat.Primrec.const n).pair primrec_id |>.of_eq rfl`), `RecDecidable.comp`, then `.re`.

**New r.e. layer in `Recursive.lean`** (choice-free, after the `RecDecidable` section):
- `REPred p := ∃ q, RecDecidable q ∧ ∀ n, p n ↔ ∃ i, q (Nat.pair i n)` — "recursively enumerable" as
  the **projection of a recursively decidable relation**. Chosen over Scott's bare enumerator
  description (`y = {Y_{r(i)}}` for primrec `r`) because the projection form also represents the
  *empty* set (take `q ≡ false`), which r.e. requires; the two are standardly equivalent.
- `REPred₂ r := REPred (fun t ↦ r t.unpair.1 t.unpair.2)` — `Nat.pair`-coding (mirrors
  `RecDecidable₂`).
- `RecDecidable.re` / `RecDecidable₂.re` — every recursively decidable predicate is r.e. (use the
  decider as `q ⟨i,n⟩ := p n`, a reindex along `unpair.2` dropping the search variable; witness
  `i = 0`).
- `REPred.of_iff` — transfer across a pointwise `↔`. `rePred_of_forall` — always-true is r.e.

**Audits** (`#print axioms`): `IsComputableMap`, `IsComputableElement`, `REPred`, `REPred.of_iff`
depend on **no axioms**; `idMap_isComputable`, `principal_isComputableElement`, `RecDecidable.re`,
`rePred_of_forall` → `{propext, Quot.sound}`. **No `Classical.choice`** anywhere. `lake build Domain`
green (3101 jobs; the lone `Exercise617Gen` unused-variable warning is pre-existing).

**Next:** **Proposition 7.3** — composition of computable maps is computable (identity already done).
This needs `REPred` closed under **`∃` over ℕ** and **`∧`** (both hold for the projection-of-decidable
form: pair the search variables, use `RecDecidable.and`). Then **Theorem 7.4** (`D₀+D₁`, `D₀×D₁`
effectively given; the `inᵢ`/`outᵢ`/`projᵢ` combinators computable).

---

## Checkpoint — 2026-06-22 — Proposition 7.3 COMPLETE (identity + composition computable), choice-free

Added to **`Definition72.lean`** (ns `Domain.Neighborhood`), all `⊆ {propext, Quot.sound}`:

- **`comp_isComputable`** — `IsComputableMap P Q f → IsComputableMap Q R g → IsComputableMap P R
  (g.comp f)`. Scott's `X (g∘f) Z ↔ ∃ Y, X f Y ∧ Y g Z`; surjectivity `Q.surj` (with `g.rel_dom` to
  know `Y` is a `W`-neighbourhood) lets the witness `Y` range over **indices** `l` (`Y = Q.X l`), so
  the relation becomes `∃ l, Xₙ f Yₗ ∧ Yₗ g Zₖ`. Assembled as
  `((hf'.comp hgf).and (hg'.comp hgg)).proj` then `REPred.of_iff` (peeling `comp_rel`), where the
  primrec reindexers are `hgf : u ↦ ⟨u.2.1, u.1⟩` and `hgg : u ↦ ⟨u.1, u.2.2⟩` (`u` codes `(l, ⟨n,k⟩)`).
- **`apply_isComputableElement`** — the "immediate and useful consequence": `f` computable and `x`
  a computable element ⟹ `f(x)` computable. `f(x) = {Yₘ ∣ ∃ Xₙ ∈ x, Xₙ f Yₘ}` (`toElementMap`);
  `P.surj` (with `x.sub`) ranges `X` over `n`, giving `∃ n, Xₙ ∈ x ∧ Xₙ f Yₘ`, r.e. by the same
  closure lemmas.

**New choice-free r.e.-closure layer in `Recursive.lean`** (projection-of-`RecDecidable` form), the
reusable engine for 7.3 and 7.4:

- **`REPred.comp`** — reindex by a `Nat.Primrec g`: `p` r.e. ⟹ `fun n ↦ p (g n)` r.e. (absorb `g`
  into the decidable relation along `unpair.2`).
- **`REPred.and`** — `p, q` r.e. ⟹ `fun n ↦ p n ∧ q n` r.e. (pair the two search variables `i, j`
  into one `w`; the decider is `RecDecidable.and` of two reindexed copies).
- **`REPred.proj`** — `p` r.e. ⟹ `fun n ↦ ∃ i, p ⟨i, n⟩` r.e. (fold the existential variable into
  the search variable).

**Lean GOTCHA noted:** `IsComputableMap`/`IsComputableElement` are `def … : Prop := REPred …`, so
**dot notation** `hf.comp`/`hx.and` does *not* resolve (head symbol is `IsComputableMap`, not
`REPred`). Re-bind first: `have hf' : REPred (fun s ↦ f.rel (P.X s.unpair.1) (Q.X s.unpair.2)) := hf`
(defeq by `β`-reduction), then use dot notation on `hf'`.

**Audits** (`#print axioms`): `comp_isComputable`, `apply_isComputableElement`, `REPred.comp`,
`REPred.and`, `REPred.proj` → `{propext, Quot.sound}`. No `Classical.choice`. `lake build Domain`
green (3101 jobs; only the pre-existing `Exercise617Gen` unused-`F` warning).

**Next:** **Theorem 7.4** — `D₀+D₁`, `D₀×D₁` effectively given (build `ComputablePresentation`s of the
sum/product systems: enumerate the tagged/paired neighbourhoods, decide intersection & consistency
from the components' deciders) and the combinators `inᵢ`/`outᵢ`/`projᵢ`, `f+g`, `f×g` computable
(now straightforward given the `REPred` closure layer).

---

### Checkpoint — Theorem 7.4 (× half) COMPLETE & CHOICE-FREE; + half pending; new RT layer

`Theorem74.lean` (ns `Domain.Neighborhood`), wired into `Domain.lean`. Full `lake build` green; all
new decls audit `⊆ {propext, Quot.sound}`.

**Done (the `×` half of Theorem 7.4):**
- `prodPresentation P₀ P₁ : ComputablePresentation (prod V₀ V₁)` — `W_k = X⁰_{k.unpair.1} ∪ X¹_{k.unpair.2}`
  (Scott's one-one pairing `r=Nat.pair`, `p,q=unpair.1/2`), over `prod`/`prodNbhd` (`Product.lean`,
  tokens `α⊕β`). The product is **uniform** (no tag analysis), so 7.1(i) (`interEq`) and 7.1(ii)
  (`cons`) each decompose, via `prodNbhd_inter`/`prodNbhd_subset_iff`/`prodNbhd_eq_iff`, into a
  **conjunction** of the two factors' relations on reindexed indices — recursively decidable by the
  *existing* `RecDecidable.and`/`.comp`/`.of_iff` (no new recursion theory needed here).
- `prod_isEffectivelyGiven`.
- `proj₀_isComputable`/`proj₁_isComputable` — `(X⁰ₙ∪X¹ₘ) pᵢ Z ↔ (componentᵢ) ⊆ Z`, a recursive slice
  of `incl_computable` (Scott's worked `proj₁` example), so r.e. via `.re`.
- `paired_isComputable` — `Zₙ ⟨f,g⟩ (X⁰_k∪X¹_l) ↔ Zₙ f X⁰_k ∧ Zₙ g X¹_l`, conjunction of two r.e.
- `prodMap_isComputable` (`f×g`) — via `f×g = ⟨f∘p₀, g∘p₁⟩` (Ex 3.19) + `comp_isComputable` (Prop 7.3);
  no relation-bashing.

**New choice-free recursion theory in `Recursive.lean` (built for the `+` half, all audited clean):**
- `primrec_pred` / `primrec_sub` — truncated subtraction via the `prec` recursor (mathlib's
  `Nat.Primrec.sub`/`.pred` are classical).
- `RecDecidable.natEq` — equality of two primrec functions is recursively decidable (`{0,1}`-char
  `1-((a-b)+(b-a))`).
- `RecDecidable.not`, `RecDecidable.em` (an RD predicate is decidable; via `Nat.decEq`),
  `RecDecidable.or` (choice-free De Morgan `p∨q ↔ ¬(¬p∧¬q)`).
- `REPred.or` — disjunction of r.e. predicates is r.e. (the witness carries a `{0,1}` tag selecting
  which disjunct's search index to use); this is the last of Scott's listed closure properties
  ("conjunctions, disjunctions, substituting recursive functions, ∃ to the front").

**GOTCHA (important, cost me an axiom-audit failure):** `omega` on an **`↔` goal** pulls
`Classical.choice`, but on **implications** it is clean. Always prove biconditionals as
`constructor <;> intro h <;> omega`. Also `eq_or_ne` is classical — use `Nat.decEq`.

**Pending (the `+` / sum half of Theorem 7.4):** `sumPresentation` + `sum_isEffectivelyGiven`, then
`inMap₀/₁`/`outMap₀/₁`/`sumMap` computable. The plan + intersection-table case analysis is written
out in the "Next concrete target" section near the top of this file. The RT it needs is now in place.

---

## Checkpoint 2026-06-22 — Theorem 7.4 `+` (sum) half COMPLETE & CHOICE-FREE

`Theorem74.lean` now closes the sum half; `lake build Domain` is green, zero `sorry`, and every new
declaration audits `⊆ {propext, Quot.sound}` (verified `sumPresentation`, `sum_isEffectivelyGiven`,
`inMap₀/₁_isComputable`, `outMap₀/₁_isComputable`, `sumMap_isComputable`, plus the helpers
`sumEnum_eq_iff`/`eqSEdec`). What landed:

- **`sumEnum P₀ P₁ t`** — tag enumeration over `Option(α⊕β)`: `tag 0 ↦ inj₀ X⁰_{t.2}`,
  `tag 1 ↦ inj₁ X¹_{t.2}`, `tag ≥2 ↦ sumMaster` (`tag = t.unpair.1`, component `= t.unpair.2`);
  with `sumEnum_zero/one/master`, `sumEnum_mem`, `sumEnum_nonempty`, distinctness lemmas
  (`inj₀_eq_iff`, `inj₀_ne_sumMaster`, `inj₀_ne_inj₁_of_nonempty`, `inj₀_eq_inj₁_elim`), and the
  master-absorption lemmas (`sumEnum_subset_sumMaster`, `sum{Master_inter,_inter_sumMaster}`).
- **`sumEnum_eq_iff`** (equality of two sum-nbhds decoded into tag/component conditions) →
  **`eqSEdec`** (recursively decidable, via `recDec_setEq₀/₁` + `RecDecidable.or/.and/.not/.natEq`).
- **`sumPresentation`** / **`sum_isEffectivelyGiven`** — the `interEq`/`cons` deciders are a 9-branch
  `tag_a × tag_b` case split (with a further 3-way `tag_c` split where the result is a left/right
  copy), built from `eqSEdec`, `P₀/P₁.interEq/cons` slices, and the closure lemmas.
- Combinators **`inMap₀/₁_isComputable`**, **`outMap₀/₁_isComputable`** (`out` decoded via `leftPart`/
  `rightPart`, with `k₀/k₁` the surjective index of `Vᵢ.master`), **`sumMap_isComputable`** (`f+g`:
  relation tag-decodes to `(m master) ∨ (both-left ∧ f.rel) ∨ (both-right ∧ g.rel)`, r.e. by
  `REPred.or`/`.and`/`.comp`).

**Two choice traps fixed during the audit (see also the top-of-file note):**
1. `omega` closing a **non-arithmetic** goal (a `Set` equality) by contradiction pulls
   `Classical.choice` — prefix `exfalso` (all such call sites in `Theorem74.lean` now do).
2. `Set.Nonempty.ne_empty` is classical — replaced by `Set.notMem_empty` after `rw [← h]`.

**Next:** Theorem 7.5 — the function-space `(D₀→D₁)` is effectively given; `eval`/`curry` computable;
computable elements correspond to computable maps.

## Checkpoint 2026-06-22 — Theorem 7.5 scaffolding: Def 7.1 extended + primrec list-fold engine

Theorem 7.5 is a *major* multi-part theorem; building it incrementally in green, audited milestones.
Two foundational milestones landed (full `lake build` green, zero `sorry`, all new decls audit
`⊆ {propext, Quot.sound}` or no axioms):

- **Milestone 1 — `ComputablePresentation` extended (Def 7.1).** Scott's function-space deciders must
  *form* component intersections (locate the index `k` with `X_k = Xₙ ∩ Xₘ`), which the previous
  `RecDecidable` (primrec-only, no unbounded search) could not produce. Decision (user): add a
  **primitive-recursive intersection function** to the presentation rather than going general-recursive.
  `Definition71.lean`'s `ComputablePresentation` now carries:
  - `inter : ℕ → ℕ → ℕ`, `inter_primrec : Nat.Primrec (fun t => inter t.unpair.1 t.unpair.2)`,
    `inter_spec : (∃ k, X k ⊆ X n ∩ X m) → X (inter n m) = X n ∩ X m`;
  - `masterIdx : ℕ`, `masterIdx_spec : X masterIdx = V.master`.
  Re-greened all instances: `unitPresentation` (`Definition71.lean`), `prodPresentation` (componentwise
  `pair`), `sumPresentation` (tag-trichotomy via nested `selectFn`) in `Theorem74.lean`. New helpers in
  `Recursive.lean`: `primrec_add₂/_mul₂/_sub₂`, `selectFn` (+`primrec_selectFn`, `selectFn_one/zero/ite`,
  `geTwo_bit`, `eqZero_bit`).

- **Milestone 2 — choice-free primrec list-fold engine (`Recursive.lean`).** The reusable core every
  function-space decider will sit on. `Nat`-coded lists:
  - `encodeList : List ℕ → ℕ` (`[] ↦ 0`, `a::l ↦ pair a (encodeList l) + 1`); `encodeList_length_le`;
  - `decodeList : ℕ → List ℕ` (WF on the remaining code, `unpair_snd_le` the measure);
    `decodeList_succ`, `encodeList_decodeList` (`encode∘decode = id`), `decodeList_length_le`;
  - `foldStep`/`foldCode stp params z c` = `((foldStep stp params)^[c] (pair c z)).unpair.2`, i.e. fold
    the list coded by `c` threading accumulator `z` + fixed parameter `params`, step function `stp`;
  - **`foldCode_eq`** (`foldCode` on `encodeList l` = `List.foldl …`), **`foldCode_eq'`** (on an arbitrary
    code via `decodeList`), and **`primrec_foldCode`** (`foldCode` is primrec in all primrec inputs — via
    `rec_const_iterate` bridging `Nat.Primrec.prec`'s `Nat.rec` with the `Function.iterate` def, and
    `primrec_foldStepPacked`). `le_pair_right` proved choice-free (avoids mathlib's classical
    `Nat.right_le_pair`).

**Remaining for 7.5 (next sessions):** (a) `funSpace` neighborhoods as coded lists of step-pairs `[X,Y]`;
consistency decider (`stp` = component `cons`/`inter` over the entries, via `foldCode`) + inclusion
decider → `ComputablePresentation (funSpace …)` (`Theorem75.lean`); (b) `eval` computable; (c) computable
elements = computable maps; (d) `curry` (Scott defers fuller treatment to Ex 7.16); (e) wire into
`Domain.lean`, update `arxiv.md` row to Pass.

### Milestone 3 (2026-06-22) — bounded universal quantifier decider (`Recursive.lean`)

The funSpace consistency condition (Prop 3.9(i), and Scott's proof of 7.5, p.121–122) is a **bounded
universal**: a list of `q` step-pairs `[Xᵢ,Yᵢ]` is consistent in `(𝒟₀→𝒟₁)` iff **for every subset**
`I ⊆ {0,…,q-1}` (coded as a bitmask `b < 2^q`), `{Xᵢ : i∈I}` consistent in `𝒟₀` ⟹ `{Yᵢ : i∈I}`
consistent in `𝒟₁` (≤ `2·2^q` component checks). So the gateway primitive is bounded `∀`. Landed,
green, audited `⊆ {propext, Quot.sound}` (the `Fn`s are pure data, no axioms):

- `isOne v = 1 - ((v-1)+(1-v))` — the `{0,1}` indicator of `v = 1` (`isOne_eq_one_iff`, `isOne_le_one`,
  `primrec_isOne`); needed because `RecDecidable` char functions are only *guaranteed* `=1`/`≠1`, not
  literally `{0,1}`-valued, so folds must normalize each test.
- `bForallFn g n N` — `Nat.rec`-fold of `selectFn ih (isOne (g (pair i n))) 0`, staying in `{0,1}`
  (`bForallFn_le_one`), with `bForallFn_eq_one_iff : … = 1 ↔ ∀ i < N, g (pair i n) = 1`.
- **`RecDecidable.bForall`** — if `p` is `RecDecidable` and `bound` is `Nat.Primrec`, then
  `fun n => ∀ i < bound n, p (pair i n)` is `RecDecidable`. (The bounded-`∃` is not separately needed:
  unbounded `∃` is already `REPred.proj`, and consistency is the `∀` form.)

### Milestone 4 (2026-06-22) — primrec arithmetic for bit extraction (`Recursive.lean`)

All green, audited `⊆ {propext, Quot.sound}` (`recPow_eq` only `propext`):

- `primrec_pow : Nat.Primrec (unpaired fun b e => b ^ e)` (via `recPow_eq : Nat.rec 1 (·*b) e = b^e`,
  choice-free; mathlib's `^` `Primrec` lemmas route through classical `simp`), plus
  `primrec_two_pow : Nat.Primrec g → Nat.Primrec (fun n => 2 ^ g n)` for the `2^q` subset bound.
- **Halving** `halfParity n = pair (n/2) (n%2)` (structural recursion, step `(h,p) ↦ (h+p, 1-p)`;
  `halfParity_spec` proved with `omega`, which discharges `/2`,`%2` since the divisor is the literal
  `2`), giving `primrec_div2`/`primrec_mod2`. **No general `div`/`mod` is needed**: the consistency
  fold consumes the subset bitmask `b` one bit at a time via `b % 2` then `b / 2`.

**Next for 7.5 (`Theorem75.lean`):** build the per-subset fold over `decodeList code` (via `foldCode`,
param = bitmask `b` that is read `%2`/halved each entry; accumulator = running component-`inter` indices
in `𝒟₀` and `𝒟₁` + `{0,1}` consistency flags), and wrap in `RecDecidable.bForall` (bound `2 ^ len` via
`primrec_two_pow`) to obtain `funCons` (Prop 3.9(i)). Then the inclusion decider
(`⋂{Yₘᵢ : Xₖ⊆Xₙᵢ} ⊆ Yₗ` via a conditional `foldCode` + `inter` + `incl_computable`), assemble
`funPresentation : ComputablePresentation (funSpace …)` (junk-to-master on inconsistent codes, detected
by `funCons`, keeping the enumeration choice-free), then `eval`/elements=maps/`curry`.
All primrec building blocks (`foldCode`, `bForall`, `pow`, `div2`/`mod2`, `inter`/`masterIdx`) are now
in place — `Theorem75.lean` is unblocked.

## Checkpoint 2026-06-22 — Theorem 7.5: `Theorem75.lean` created; Prop 3.9(i) math core DONE (choice-free)

`Theorem75.lean` (ns `Domain.Neighborhood`) created and wired into `Domain.lean`. Full `lake build
Domain` green, **zero `sorry`**, every new declaration audits `⊆ {propext, Quot.sound}` (choice-free).
This lands the **mathematical heart** of Theorem 7.5 — Scott's Proposition 3.9(i), the function-space
consistency condition — in three reusable, choice-free milestones. (The remaining work is
recursion-theory *packaging* + assembly + the combinators; see "Remaining" below.)

**Choice subtlety discovered (important).** The "obvious" keystone `(stepFun L).Nonempty ↔ ∀X∈𝒟₀,
V₁.mem (interYs Δ₁ L X)` (routing through `leastMap`/`rel_interYs`) **pulls `Classical.choice`**,
because `FunctionSpace.rel_interYs` does a `by_cases X ⊆ p.1` on an *undecidable* set inclusion. The
fix that keeps everything `⊆ {propext, Quot.sound}`: phrase 3.9(i) over **explicit finite selections
(sublists)** — where no inclusion case-split is needed — and, for the reverse direction, single out
`{i ∣ X ⊆ Xᵢ}` using the **decidable `𝒟₀`-inclusion supplied by the presentation `P₀`** (`Nat.decEq`
on `incl_computable`'s char function), never `Classical.dec`.

**What landed in `Theorem75.lean` (all choice-free):**
- **Milestone 1 — 3.9(i) forward.** `interList base M` (intersection of a finite list of nbhds inside
  a base), `mem_interList`, `interList_subset_base`; `rel_interList_of_selection` (a witness map
  `f ∈ stepFun L` relates a common lower nbhd `Z` of the *selected* inputs to the intersection of the
  *selected* outputs — a finite `inter_right` fold over the explicit selection, **no `by_cases`**);
  `interList_mem_of_stepFun_nonempty` (non-empty ⟹ selected-output-intersection is a nbhd).
- **Milestone 2 — consistency characterization over coded entry-lists.** `funPair P₀ P₁ e =
  (X₀_{e.unpair.1}, Y₁_{e.unpair.2})`, `funListOf P₀ P₁ el = el.map (funPair …)`, `funListOf_valid`;
  **`stepFun_funListOf_nonempty_iff`** — `(stepFun (funListOf el)).Nonempty ↔ ∀ sub ⊑ el,
  (∃ Z∈𝒟₀, ∀ e∈sub, Z ⊆ X₀_{e.1}) → V₁.mem (interList Δ₁ (sub.map (Y₁_{·.2})))`. Reverse direction
  builds `leastMap`, discharging its `hcons` per-input by **filtering `el`** with the choice-free
  decidable `𝒟₀`-inclusion test (`List.filter` + `decidable_of_iff` off `P₀.incl_computable`), proving
  `interYs Δ₁ (funListOf el) X' = interList Δ₁ (filtered.map (Y₁_{·.2}))` by `Set.ext`.
- **Milestone 3a — choice-free consistency *decision principle* (`section ConsChain`, generic over one
  presentation `P : ComputablePresentation V`).** `interFrom P A js` (running left-accumulated
  intersection of `A` with `X_j`, `j∈js`), `mem_interFrom`, `interFrom_subset`,
  `interFrom_mem_of_witness` (a nbhd inside a finite running intersection makes it a nbhd);
  `interFrom_eq_of_foldl` / `idxchain P js = js.foldl (P.inter ·) masterIdx` / `idxchain_spec` (the
  `inter`-fold computes the genuine intersection *when consistent*, via `inter_spec` + prefix
  consistency); and the headline **`consChain_iff`**: `(∀ j∈js, X_{idxchain js} ⊆ X_j) ↔ V.mem
  (interFrom Δ js)`. **Key trick (avoids consistency-flag bookkeeping):** `X_{idxchain js}` is *always*
  a nbhd (`mem_X`), so if it sits inside every selected `X_j` it witnesses consistency; conversely
  `inter_spec` makes the chain exact when consistent. So consistency reduces to **one `inter`-fold +
  one bounded inclusion check** — both primitive-recursive-friendly.

**Remaining for Theorem 7.5 (precise plan; all the math is now in hand — what's left is recursion-theory
packaging + assembly):**
1. **`funCons` (consistency decider, `RecDecidable`).** Package the choice-free principles above into a
   `Nat.Primrec` char function of the code `c`: `(stepFun (funListOf (decodeList c))).Nonempty ↔
   ∀ b < 2^c, cons₀(selectMask b) → cons₁(selectMask b)` (`RecDecidable.bForall`, bound `2^c` via
   `primrec_two_pow primrec_id`; the over-count past `length` is harmless). Each `cons₀/cons₁` =
   `consChain_iff`: a first `foldCode` over `decodeList c` threading the bitmask `b` (read `%2`,
   halved each entry via `halfParity`) that applies `P.inter` to the selected component to compute
   `idxchain`, then a second `foldCode` AND-ing `isOne (incl-char (pair idxchain compIdx))` over the
   selected entries. Connect via `foldCode_eq'` (→ `List.foldl`) + a `selectMask`↔bitmask induction +
   `consChain_iff`/`stepFun_funListOf_nonempty_iff`. Relate `interList Δ (js.map X)` to
   `interFrom Δ js` by `Set.ext` (both = `⋂ ∩ master`).
2. **Inclusion decider (`RecDecidable₂ (Xₐ ⊆ X_b)` for funSpace).** `stepFun L ⊆ step Xk Yℓ ⟺
   interYs Δ₁ L Xk ⊆ Yℓ` (`FunctionSpace.stepFun_subset_step_iff`, needs `L` consistent). Decider:
   bounded-∀ over `L' = decodeList b` of `[interYs-fold over decodeList a selecting i with Xk⊆Xnᵢ
   (decidable incl), inter₁ their Ymᵢ → index] ⊆ Yℓ` (one conditional `foldCode` per `(k,ℓ)∈L'`, **no
   2^q**). `interEq` = inclusion both ways (`RecDecidable.and` + swap); `cons` = `funCons` of the append
   code.
3. **`funInter` (the presentation's primrec `inter`).** `X n ∩ X m = stepFun(L_n ++ L_m)`, so
   `funInter c₁ c₂` = code of `decodeList c₁ ++ decodeList c₂`; need a primrec `appendCode` (a fold).
   `masterIdx` = `0` (empty list ↦ `stepFun [] = univ` = `funSpace.master`). Junk-to-master enumeration:
   `Xenum c = if funCons c = 1 then stepFun (funListOf (decodeList c)) else univ`.
4. **Assemble `funPresentation : ComputablePresentation (funSpace V₀ V₁)`** + `funSpace_isEffectivelyGiven`
   (`mem_X` via consistency ⟹ nbhd / else master; `surj` via `funListOf` of `P₀.surj`/`P₁.surj`
   indices + forward consistency; `interEq`/`cons`/`inter`/`masterIdx` from 1–3).
5. **`eval` computable** — Scott: `eval` is a *recursive* (decidable) set, because the function-space
   nbhd has a minimal element `leastMap` (3.9(ii)) and `Xk eval Yℓ` reduces to `Xk f₀ Yℓ`, decidable.
6. **Computable elements = computable maps** — "easy consequence": `φ.mem (X c) ↔ ∀ entries,
   φ.mem (step …)`, so the element index set is r.e. iff the relation is (`toApproxMap`).
7. **`curry` computable** (Scott defers the full relation to Ex 7.16; `FunctionSpace.curry` is in place).
8. Update `arxiv.md` row for Theorem 7.5 to **Pass** once 1–7 land.

## Checkpoint 2026-06-23 — Theorem 7.5: consistency decider + appendCode + inclusion characterization DONE (choice-free)

Recovered the clean pre-cutover base (`Theorem75.lean` @ commit `863547b`, 301 lines, Milestones
1/2/3a) after a budget cutover to Composer left an **818-line, non-building, sorry-laden** working
tree (saved for reference at `/tmp/composer_t75_blueprint.lean`; its HANDOFF/arxiv "landed/zero sorry"
claims were false). Then built the next milestones for real — `lake build Domain` green, **zero
`sorry`**, every new decl audits `⊆ {propext, Quot.sound}`.

**What landed (on top of 1/2/3a):**
- **Milestone 3b — bitmask sublist selection.** `bitSelect L b` (low bit = head), `bitSelect_sublist`,
  `exists_bitSelect_lt` (every sublist is some `bitSelect L b`, `b < 2^len`),
  `forall_sublist_iff_forall_bitmask` (∀-over-sublists ⇔ bounded ∀-over-`b < 2^c`, via
  `decodeList_length_le`). Choice gotcha avoided: `0 < 2^n` via `rw [pow_zero]; exact Nat.one_pos`
  and `Nat.pow_le_pow_right (Nat.le_succ 1) …` (NOT `simp`/`decide`, which pull `Classical.choice`).
- **Milestone 3c — single-pass consistency fold (`section ConsFold`, generic `P`).** `consUpd` threads
  `pair b (pair idx flag)`; at a *selected* entry it `P.inter`s the running index with the entry's
  `projFn`-component and ANDs `flag` with the **binary** consistency test `isOne (fc …)`
  (`fc` = `P.cons_computable` char). `consUpd_eval` (clean β-reduced step), `consUpd_foldl_flag_zero`
  (0 persists), headline **`consUpd_foldl_spec`** (final flag = 1 ↔ `V.mem (interFrom P (X a) (selected
  projFn))`, by induction generalising the start index `a`: `inter_spec` keeps `X a` exact along the
  consistent prefix; `P.surj` turns a witnessing nbhd back into the `∃k` of `fc`). `consStp`/`consCharAt`
  wrap it through `foldCode`; `consCharAt_spec`; **`primrec_consStp`** (KEY: build the primrec term with
  *unannotated* `.comp`/`.pair` `have`s then one final `.of_eq … simp [unpair_pair_*]` — annotating the
  reduced form forces non-defeq `unpair (pair …)` unification → `whnf` heartbeat timeout, the bug that
  sank the Composer attempt); **`consFold_decidable`**.
- **Milestone 3d — `funCons_decidable`.** `interList_X_eq_interFrom`, `antecedent_cons_iff` (Prop
  3.9(i) antecedent ⇔ `interFrom` consistency in `𝒟₀`), `funConsequent_eq`; **`funCons_iff`**
  (`(stepFun (funListOf (decodeList c))).Nonempty ↔ ∀ b<2^c, cons₀(bitSelect)→cons₁(bitSelect)`) and
  **`funCons_decidable : RecDecidable (fun c ↦ (stepFun (funListOf (decodeList c))).Nonempty)`**
  (`consFold_decidable P₀ (·.unpair.1)` ⇒ `consFold_decidable P₁ (·.unpair.2)` via `.not`/`.or`/`.em`,
  wrapped in `RecDecidable.bForall (bound := fun n ↦ 2^n)`).
- **Milestone 4 — `appendCode`.** `appendStep`/`appendStp`/`appendCode` (foldCode prepend),
  `decodeList_appendCode` (codes `(decodeList b).reverse ++ decodeList a`), `primrec_appendCode`,
  `funListOf_append`, **`stepFun_funListOf_appendCode`** (= `stepFun(funListOf da) ∩ stepFun(funListOf db)`,
  via `ext` + `mem_stepFun`; reverse is harmless since `stepFun` is an intersection).
- **Milestone 5a — inclusion CHARACTERISATION (choice-free).** `funListOf_cons`; **`rel_interYs_funList`**
  — the *choice-free* re-proof of `FunctionSpace.rel_interYs` for a presented list (the library version
  `by_cases X ⊆ Xᵢ` ⇒ `Classical.choice`; here the split is `P₀.incl_computable.em (pair n' e.1)` then
  `simp [unpair_pair_*]`); `interYs_funList_mem_of_nonempty` (nonempty ⇒ the `leastMap` consistency
  hypothesis `hcons`); **`stepFun_funListOf_subset_iff`** (`stepFun(funListOf ea) ⊆ stepFun(funListOf eb)
  ↔ ∀ e'∈eb, interYs Δ₁ (funListOf ea) (X₀_{e'.1}) ⊆ X₁_{e'.2}`; forward tests `leastMap`, backward uses
  the choice-free `rel_interYs_funList`).

**REMAINING for 7.5 (precise; 5a's math is in hand, what's left is the primrec packaging + assembly):**
1. **Milestone 5b — `RecDecidable₂ (Xenum a ⊆ Xenum b)`.** Compute the index of `interYs Δ₁ (funListOf
   (decodeList a)) (X₀_{n'})` by a conditional-`inter` `foldCode` over `decodeList a` (select `e` with
   `isOne(fincl0 (pair n' e.1))`, `P₁.inter` the running idx with `e.2`); prove
   `foldl_cond_inter` (conditional fold = `idxchain` over the `filter`-`map`ped list), and
   `interYs_eq_interFrom_filter` (`Set.ext` via `mem_interYs`/`mem_interFrom` + `hincl0`), so when
   consistent (Milestone 1 forward gives the outputs are a nbhd) `P₁.X idx = interYs`. Then
   `stepFun ⊆ stepFun ⟺ ∀ e'∈decodeList b, incl₁(idx(e'.1,a), e'.2)` — a `foldCode`-AND over
   `decodeList b` (need a `bForallList`-style spec). Junk-handling: `Xenum c = if funCons c then
   stepFun(funListOf(decodeList c)) else univ`, so the full incl decider case-splits on `funCons a`,
   `funCons b` (both `RecDecidable`): `univ ⊆ Xb ⟺ funCons b ⇒ (db empty-ish)`… handle via the two
   `funCons` flags. `interEq` = incl both ways; `cons` = `funCons (appendCode a b)`.
2. **Milestone 6 — `funPresentation` + `funSpace_isEffectivelyGiven`.** `inter a b := selectFn
   (isOne(funCons a)) (selectFn (isOne(funCons b)) (appendCode a b) a) b`; `masterIdx = 0`
   (`Xenum 0 = univ`); `mem_X`/`surj` via `funListOf_valid`/`stepFun_funListOf_nonempty_iff` forward +
   `P₀.surj`/`P₁.surj`; `inter_spec` via `stepFun_funListOf_appendCode`.
3. **Milestone 7 — `eval` computable** (Scott: recursive set via `leastMap`/3.9(ii)).
4. **Milestone 8 — computable elements = computable maps.**
5. **Milestone 9 — `curry` computable** (Scott defers full relation to Ex 7.16).
6. Flip `arxiv.md` row to **Pass** once 1–5 land.

NOTE: `arxiv.md` row stays at its committed value (NOT Pass) until the theorem is fully complete.

## Checkpoint 2026-06-23 (later) — Theorem 7.5 COMPLETE & CHOICE-FREE (all four parts)

`Theorem75.lean` now lands **all four parts of Theorem 7.5**, full `lake build Domain` green, **zero
`sorry`**, zero warnings in `Theorem75.lean`/`Recursive.lean`, every new decl audits
`⊆{propext, Quot.sound}`. `arxiv.md` row flipped to **Pass** with a dense note. `Theorem75.lean` is
wired into `Domain.lean`. Recovered the pre-cutover Milestones 5b/6/8 base (`Eq.le`/`.ge`→
`Eq.subset`/`.superset` to kill `Classical.choice`; dropped an unused `hgN` from `mem_Xenum_iff`),
then built 7 and 9.

**What landed (on top of Milestones 1–6, 8):**
- **Milestone 7 — `evalMap_isComputable`** (`IsComputableMap (prodPresentation funPresentation P₀) P₁
  (evalMap V₀ V₁)`). `evalMap_rel_prodNbhd_iff`: `(F,X) eval Y ↔ F ⊆ [X,Y]` (every map in `F` relates
  `X→Y` ⟺ `F ⊆ step X Y = {f∣f X Y}`, via `mem_step`). `Xenum_singleton`: `[X₀ⱼ,Y₁ₘ] = Xenum(⟨⟨j,m⟩,0⟩+1)`
  (one-entry, always consistent — the step map witnesses). So eval reduces to the **decidable**
  function-space inclusion `funPresentation.incl_computable` (= `RecDecidable (Xenum a ⊆ Xenum b)`, read
  off by defeq since `funPresentation.X ≡ Xenum`) re-indexed by the primrec singleton-code map
  `t ↦ ⟨t.1.1, ⟨⟨t.1.2,t.2⟩,0⟩+1⟩`; `.re`. Scott's "`eval` is a recursive set".
- **Milestone 9 — `curry_isComputable`** (`IsComputableMap P₀ (funPresentation P₁ P₂ …) (curry g)` from
  `hg : IsComputableMap (prodPresentation P₀ P₁) P₂ g`). `mem_Xenum_iff_map` (single-map analogue of
  `mem_Xenum_iff`, via `mem_stepFun`) + `curry_rel`/`gSection_rel` give `curry_rel_Xenum_iff`:
  `(X₀ₙ) curry(g)(Xenum c) ↔ (gN c=1 → ∀⟨j,k⟩∈decodeList c, X₀ₙ∪X₁ⱼ g X₂ₖ)`. The body is r.e. in the
  **parameter** `n` and entry `e`, so this is r.e. by the new `REPred.forall_mem_decodeList₂`, guarded
  by decidable consistency (`Decidable.imp_iff_not_or`, as in Milestone 8). Required importing
  `Theorem74` (for `prodPresentation`).
- **New choice-free RT in `Recursive.lean`:** `REPred.forall_mem_decodeList₂` — parameterised bounded
  `∀`: `REPred₂ p → REPred (fun t ↦ ∀ e∈decodeList t.2, p t.1 e)`. Proof reduces to the existing
  unparameterised `forall_mem_decodeList` by primitively re-coding `decodeList c` into the pairs
  `⟨t.1,e⟩` (`mapPairCode`/`mapPairStp`/`mapPairStep`, a `foldCode` prepend threading the parameter via
  the `params` slot; `decodeList_mapPairCode = ((decodeList c).map ⟨n,·⟩).reverse`, order-irrelevant
  under `∀∈`), then `REPred.comp` + `REPred.of_iff` with `List.mem_reverse`/`List.mem_map`.

**Dot-notation gotcha:** `hS.forall_mem_decodeList₂` fails because `hS : REPred₂ …` (head `REPred₂`) but
the lemma lives in the `REPred` namespace — call `REPred.forall_mem_decodeList₂ hS` explicitly.

**Theorem 7.5 is DONE.** Next concrete target: **Theorem 7.6** (`fix:(D→D)→D` computable on effectively
given `D`) — `arxiv.md` line 4377.

## Checkpoint 2026-06-23 (later still) — Theorem 7.6 COMPLETE & CHOICE-FREE (`fix` computable)

`Theorem76.lean` (ns `Domain.Neighborhood`) created, wired into `Domain.lean`, full `lake build Domain`
green, **zero `sorry`**, zero warnings in `Theorem76.lean`; `#print axioms` of `fixMap_isComputable`,
`fixMap_rel_iff`, `fixElement_mem_iff_chain`, `fixChainChar_spec` all `{propext, Quot.sound}`
(choice-free). `arxiv.md` row flipped to **Pass** with a dense note. **No new recursion theory was
needed** — everything reuses Theorem 7.5's `Xenum`/`funPresentation`/`Xenum_singleton` and
`Recursive.lean`'s `foldCode`/`selectFn`/`isOne`/`RecDecidable.natEq`/`.and`/`decodeList`/`encodeList`.

**Headline:** `fixMap_isComputable (P : ComputablePresentation V) (gN incl eq …) : IsComputableMap
(funPresentation P P gN incl incl eq …) P (fixMap V)` — mirrors `evalMap_isComputable`'s signature
(takes the funSpace consistency char `gN` + `P`'s inclusion/equality chars `incl`/`eq` as hyps, the
form that composes; there is no "extract-from-`IsEffectivelyGiven`" wrapper, same as `eval`).

**Scott's proof structure** (line 4377): `⋂[X_{nᵢ},X_{mᵢ}] fix X_ℓ ↔ ∃` finite sequence
`Δ=X_{k₀},…,X_{k_p}=X_ℓ` with each `⋂{X_{mᵢ}∣X_{kⱼ}⊆X_{nᵢ}}⊆X_{kⱼ₊₁}` — an `∃`-of-decidable, hence
r.e. (genuinely r.e., **not** recursive — no bound on the sequence length).

**What landed (all choice-free):**
- **Math core — `fixMap_rel_iff`.** The funSpace nbhd `F=Xenum c` has least map
  `ĝ=toApproxMap((funSpace V V).principal (Xenum_mem … c))`; `rel_iff_mem_principal` +
  `fixMap_toElementMap` (Thm 4.2) + `mem_fixElement` (Thm 4.1) reduce `(fixMap V).rel (Xenum c)(P.X ℓ)`
  to `∃n, (ĝⁿ).rel Δ (P.X ℓ)`. **Key decidability** `leastMap_Xenum_rel`: `ĝ.rel (P.X a)(P.X b) ↔
  Xenum c ⊆ step (P.X a)(P.X b)` (via `toApproxMap_rel`+`mem_principal`; the funSpace-membership
  conjunct is discharged by `step_mem`), and `[X_a,X_b]=Xenum(codePair a b)` (`Xenum_codePair` =
  `Xenum_singleton` at the one-entry code `codePair a b = pair (pair a b) 0 + 1`), so the one-step test
  is the **decidable** funSpace inclusion `Xenum c ⊆ Xenum(codePair a b)`.
- **Chain over indices.** `gLastOf`/`gStepsOK g P a full` (consecutive `g.rel (P.X ·)(P.X ·)` along an
  index list); `gStepsOK_sound` (chain ⟹ `(g^len).rel`, induction on the list using the **`iter_comm`
  form** `g.iterMap (n+1) = (g.iterMap n).comp g` so the chain prepends), `gStepsOK_complete`
  (`(gⁿ).rel (P.X a)(P.X ℓ)` ⟹ chain, induction on `n`, naming the intermediate nbhd `Y` via `P.surj`
  as `P.X k`, prepending `k`); **`fixElement_mem_iff_chain`**: `ĝ.fixElement.mem (P.X ℓ) ↔ ∃full,
  gStepsOK ĝ P masterIdx full ∧ P.X(gLastOf masterIdx full) ⊆ P.X ℓ`. **Design note:** the endpoint is
  the *relaxed* `X_{last} ⊆ X_ℓ` (not `last = ℓ`) — this is what makes the `n=0` base of the
  strengthened (arbitrary-start) completeness induction go through (`(g⁰).rel=idMap` gives only
  `X_a ⊆ X_ℓ`), and soundness still closes via `(g^len).mono` widening the codomain.
- **r.e. packaging.** The `∃full` is realised directly as the `REPred` search `∃i, q(pair i n)`:
  `q` decodes `i`, runs one primrec `foldCode` `fixChainChar` (packed step `fixStp`, pure step
  `fixPStep`; state `pair prevIdx flag`, parameter `c`, seed `pair masterIdx 1`), and checks
  `flag=1 ∧ incl(pair lastIdx ℓ)=1`. `fixPStep_foldl_fst` (`.unpair.1` tracks `gLastOf`),
  `fixPStep_foldl_snd` (`.unpair.2=1 ↔ start-flag=1 ∧ chainDec`), `fixChainChar_spec` package the fold;
  `chainDec_iff_gStepsOK` bridges the `{0,1}`-flag chain `chainDec` (uses `fincl s=1`, the extracted
  char of `funPresentation.incl_computable`) to `gStepsOK ĝ`. The final `RecDecidable q` is
  `(RecDecidable.natEq … (const 1)).and (RecDecidable.natEq … (const 1))`; the `∃full ↔ ∃i` bijection is
  `decodeList`/`encodeList` (`decodeList_encodeList`).

**Gotcha (cost a rebuild):** declaring the fold helpers as `(fincl c i : ℕ)` instead of
`(fincl : ℕ → ℕ) (c i : ℕ)` makes Lean silently coerce `fincl`-as-`ℕ` applied-as-a-function into
`↑sorry` (a coercion `sorry`), which only surfaces as a downstream `assumption`/defeq failure with a
mysterious `(↑sorry)` in the goal — **not** as a sorry warning. Watch the argument types of higher-order
fold parameters. Also: list-recursive defs (`gLastOf`/`gStepsOK`/`chainDec`) reduce by defeq, so the
`gLastOf b rest = gLastOf prev (b::rest)` cons-equality needs an explicit trailing `rfl` after the `rw`
(rw's auto-`rfl` did not fire on the un-whnf'd RHS).

**Theorem 7.6 is DONE.** Next concrete target: **Proposition 7.7** (`D`<sup>§</sup> effectively given;
Example 6.1 combinators computable) — `arxiv.md` line 4399.

## Checkpoint 2026-06-23 (later still) — Proposition 7.7 FOUNDATIONAL LAYER done (Milestone 1)

`Proposition77.lean` (ns `Domain.Neighborhood.Proposition77`) created, wired into `Domain.lean`, full
`lake build Domain` green, **zero `sorry`**, zero warnings; `#print axioms` of `Vsharp`/`Vsharp_mem`/
`Vsharp_surj`/`Vsharp_nonempty` is `{propext, Quot.sound}` (choice-free). **`arxiv.md` row stays `—`
(NOT Pass) — the presentation is not yet built.** This is the math layer Scott waves at with "this
proof is essentially an exercise"; the real content is the recursive enumeration + the structural
intersection checks.

**What landed (Milestone 1, all choice-free math over `Example61`'s `Dsharp D hD` on `List Bool × α`):**
- **`Vsharp D P : ℕ → Set (List Bool × α)`** — Scott's enumeration `V₀=Γ`, `V_{2n+1}=embZero (P.X n)`,
  `V_{2n+2}=embPair (V_{n.unpair.1}) (V_{n.unpair.2})`. Defined by **well-founded recursion** with
  `termination_by k => k`; the children of `V_{2n+2}` are `V` at `(k-1)/2 = n`'s `unpair.1/.2`, both
  `≤ n < k`, so it terminates. Needed a local **`unpair_fst_le`** (`n.unpair.1 ≤ n`, via local
  `le_pair_left` — kept local, NOT in `Recursive.lean`, to avoid a full downstream rebuild).
- Unfolding lemmas `Vsharp_zero`, `Vsharp_succ` (`rw [Vsharp]` works for the WF def), and the clean
  `Vsharp_odd`/`Vsharp_even` (specialise via `omega` facts `(2n+1)%2=1`, `2n/2=n`, `(2n+2)=(2n+1)+1`).
- **`Vsharp_mem`** (`MemS D (Vsharp D P k)`, i.e. each `Vₖ ∈ 𝒟^§`): strong induction; **choice gotcha**
  — `Nat.even_or_odd` pulls `Classical.choice`! Replaced by a hand-rolled parity split
  `(∃n,k=2n+1)∨(∃n,k=2n+2)` whose disjunct is chosen by `Nat.lt_or_ge (k%2) 1` with explicit witnesses
  `⟨k/2-1, by omega⟩` / `⟨k/2, by omega⟩` (omega only proves the *arithmetic* equation, no choice).
- **`Vsharp_surj`** (every `MemS` nbhd is some `Vₖ`): induction on `MemS`; `gamma↦0`, `zero hX↦2n+1`
  (`P.surj hX` names `X=P.X n`), `pair↦2·(pair a b)+2` (`unpair_pair` recovers the two child indices).
- **`Vsharp_nonempty`** (`memS_nonempty hD ∘ Vsharp_mem`).
- **Per-parity intersection identities** (the actual 7.1(i)/(ii) "checks"): `Vsharp_zero_inter`/
  `Vsharp_inter_zero` (`V₀=Γ` is `∩`-identity, via `memS_subset_gamma`); `Vsharp_odd_inter_odd`
  (`= embZero (Xₐ∩X_b)`, throws the check back onto `D`); `Vsharp_odd_inter_even`/`Vsharp_even_inter_odd`
  (`= ∅`, inconsistent); `Vsharp_even_inter_even` (`= embPair (V_{a.1}∩V_{b.1}) (V_{a.2}∩V_{b.2})`,
  throws back to strictly-smaller subscripts). Straight from `Example61`'s `embZero_inter`/
  `embPair_inter`/`embZero_inter_embPair`.

**REMAINING for 7.7 (precise design — Milestones 2–5):**

The deciders `interEq_computable : RecDecidable₃`, `cons_computable : RecDecidable₂`, and the primrec
`inter` are **course-of-values recursive on the index trees**: e.g. `cons(2a+2,2b+2)=cons(a.1,b.1) ∧
cons(a.2,b.2)`, `inter(2a+2,2b+2)=2·pair(inter(a.1,b.1))(inter(a.2,b.2))+2`,
`inter(2a+1,2b+1)=2·(P.inter a b)+1`, leaf/node clashes inconsistent, `0` is `∩`-identity. The
combined measure `w = Nat.pair n m` **strictly decreases** on every recursive call (`a.1 ≤ a < n`,
`b.1 < m` ⟹ `pair(a.1,b.1) < pair(n,m)`), so this is a *unary* course-of-values on `w`.

- **Milestone 2a — generic primrec memo evaluator** (new RT in `Recursive.lean`):
  `rtbl step : ℕ → ℕ`, `rtbl 0 = 0`, `rtbl (t+1) = pair (step (pair t (rtbl t))) (rtbl t) + 1`
  (reverse table, so the prec-step is a *cons* — no `snoc` needed), built from `Nat.Primrec.prec`;
  `gOf step w := step (pair w (rtbl step w))`. To read `g v` (`v<w`) inside `step`, look up position
  `w-1-v` of the reverse table `[g(w-1),…,g 0]` via a new **`listGet c i := (decodeList c).getD i 0`**
  (primrec via a `foldCode` whose accumulator `pair countdown value` selects the `i`-th element). Prove
  `gOf step w = step (pair w (encodeList ((List.range w).reverse.map (gOf step))))` or, more usefully,
  `listGet (rtbl step w) (w-1-v) = gOf step v` for `v < w` (strong induction on `w`).
- **Milestone 2b — `cons`/`inter`/`eq` step functions** over `w = pair n m` (decode `n=w.1,m=w.2`,
  parity by `n%2`/`m%2`, leaf index `n/2`, node child-base `n/2-1`): instantiate `gOf` thrice. Leaf
  cases delegate to `P`'s extracted primrec chars (`P.cons_computable`/`P.eq_computable`/`P.inter`).
  Node cases AND/combine table lookups at `pair(a.1,b.1)`, `pair(a.2,b.2)`. Use `isOne`/`selectFn`/
  `RecDecidable.natEq`/`.and` etc. (all already in `Recursive.lean`).
- **Milestone 2c — correctness** by strong induction on `w`: `gCons (pair n m) = 1 ↔ ∃k, Vₖ⊆Vₙ∩Vₘ`
  (use the per-parity `Vsharp_*_inter_*` lemmas + `memS_*` inversion; leaf↔`D`-consistency); likewise
  `Vsharp (gInter (pair n m)) = Vₙ∩Vₘ` when consistent, and `gEq` for equality. Then
  `interEq(n,m,k) ↔ cons(n,m) ∧ gEq(gInter(pair n m)) k` (or `Vₙ∩Vₘ=Vₖ` directly via `gEq`).
- **Milestone 3 — `dsharpPresentation`/`dsharp_isEffectivelyGiven`**: assemble
  `ComputablePresentation (Dsharp D hD)` (`X=Vsharp D P`, `masterIdx=0` since `V₀=Γ=master`,
  `inter`/`inter_spec`/`interEq_computable`/`cons_computable` from 2c).
- **Milestone 4 — combinators**: Scott does "a selection": **`X_n (λx.x^§) V_k ↔ V_{2n+1}⊆V_k`**
  (`embZero(Xₙ)⊆`), recursively *decidable* (`incl` reindexed), hence r.e.; **`V_m proj₀ V_k ↔ k=0 ∨
  ∃n. m=2n+2 ∧ V_{p n}⊆V_k`**. NB Example 6.1's combinators are currently *element-level*
  (`inSharp`/`pairSharp`) — need their `ApproximableMap` forms (or read off the relation from the
  domain-equation iso `dsharpEquiv` composed with `sum`/`prod` projections) before stating
  `IsComputableMap`. Exercise 7.17 is the *full* finish (all 6.2 combinators + strict `g:D^§→E`).
- **Milestone 5 — flip `arxiv.md` row to Pass, axiom-audit all new decls, HANDOFF checkpoint.**

---

## Checkpoint — 2026-06-23 — Proposition 7.7 **Milestones 2+3 COMPLETE** (deciders + `dsharpPresentation`)

`Domain/Neighborhood/Proposition77.lean` is **green**, wired into `Domain.lean` (already imported),
zero `sorry`. The whole decider + presentation layer is built and `dsharp_isEffectivelyGiven` is
proven: **if `D` is effectively given, so is `D^§`.**

**Axiom audit (`#print axioms`):**
- **Data is choice-free `⊆ {propext, Quot.sound}`:** `Vsharp`, `Vsharp_mem`, `Vsharp_surj`,
  `Vsharp_zero`, `dsharpStep`, `gOf`, `intI` (and `listGet`/`rtbl` machinery).
- **`Prop`-level correctness uses `Classical.choice`** (`dsharp_decider_spec`, `dsharp_intI_correct`,
  `dsharp_interEq_iff`, and hence the bundled `dsharpPresentation`/`dsharp_isEffectivelyGiven`).
  This is **unavoidable & allowed**: the proofs reason about `Set` equality / subset over an arbitrary
  carrier `α` (no `DecidableEq`), so `Classical` enters via `omega`-on-`Set`-goals and friends. The
  *data fields* (`X`, `inter`, `masterIdx`) of `dsharpPresentation` are all choice-free as audited
  above; only the proof obligations pull choice.

**What got built (Milestone 2a–2d, all in `Proposition77.lean`):**
- **2a — generic primrec memo evaluator** (prototyped locally, not yet promoted to `Recursive.lean`):
  `listGet c i := (decodeList c).getD i 0` (primrec via `foldCode` w/ countdown accumulator);
  `rtbl step` reverse table (`rtbl 0 = 0`, `rtbl (w+1) = pair (step (pair w (rtbl step w))) (rtbl step w)+1`);
  `gOf step w := step (pair w (rtbl step w))`. Key lemma `listGet_rtbl : v < w → listGet (rtbl step w) (w-1-v) = gOf step v` (strong induction). All `primrec_*` lemmas present.
- **2b — combined `dsharpStep fcons feq finter`** computes a **packed triple** `packT e c ii` (eq-bit,
  cons-bit, inter-idx) in one course-of-values pass over `w = pair n m`; accessors `eqB/consB/intI`;
  9 parity cases via `selectFn` (no `if`). `primrec_dsharpStep` from `hfc_pr`/`hfe_pr`/`P.inter_primrec`.
- **2c — `dsharp_decider_spec`** (the heart): strong induction on `pair i j` proving simultaneously
  `consB = 1 ↔ ∃l, Vₗ⊆Vᵢ∩Vⱼ`, `Vsharp (intI …) = Vᵢ∩Vⱼ` (when consistent), `eqB = 1 ↔ Vᵢ=Vⱼ`. Needed
  `Nat.pair`-monotonicity (`pair_lt_pair_of_lt`) for well-foundedness and `memS_sub_embZero`/
  `memS_sub_embPair`/`Vsharp_eq_Gamma_iff` inversions.
- **2d/3 — assembly**: `dsharp_intI_correct` (intersection-index correctness, `fcons`/`feq` irrelevant,
  instantiated with `fun _ => 0`); `dsharp_interEq_iff` (7.1(i): `Vₙ∩Vₘ=Vₖ ↔ consB·eqB(intI,k)=1`);
  `dsharpPresentation P hD : ComputablePresentation (Dsharp D hD)` (`X=Vsharp D P`, `masterIdx=0`,
  `inter n m := intI (gOf (dsharpStep 0 0 P.inter) (pair n m))`); `dsharp_isEffectivelyGiven`.

**Gotcha reminders that bit this session:** the file's `variable {D} (P : ComputablePresentation D)`
makes **`P` the first explicit arg** of every helper that mentions it — call sites must pass it
(`dsharp_decider_spec P fcons feq finter …`, etc.). And a top-level theorem that uses `P` only in its
*body* (not its statement) must bind `P` **explicitly** in its own signature
(`dsharp_isEffectivelyGiven (P : ComputablePresentation D) (hD …)`), since `variable` auto-inclusion
keys off the **type**.

**Next concrete target: Milestone 4** — Example 6.1 combinators as `ApproximableMap`s + computability.
Scott does "a selection": `Xₙ (λx.x^§) Vₖ ↔ V_{2n+1} ⊆ Vₖ` (i.e. `embZero(Xₙ) ⊆ …`, recursively
decidable ⟹ r.e.); `Vₘ proj₀ Vₖ ↔ k=0 ∨ ∃n. m=2n+2 ∧ V_{p n} ⊆ Vₖ`. Need the `ApproximableMap` forms
(Example 6.1's `inSharp`/`pairSharp` are currently element-level) before stating `IsComputableMap`.
Then **Milestone 5** flips `arxiv.md` Prop 7.7 row to Pass.

---

## Checkpoint — 2026-06-23 — Proposition 7.7 **Milestone 4 COMPLETE → Prop 7.7 DONE / Pass** (`Combinators77.lean`)

New module `Domain/Neighborhood/Combinators77.lean` (green, wired into `Domain.lean`, zero `sorry`).
Both clauses of Prop 7.7 are now formalized: `D^§` effectively given (M1–3) **and** a selection of the
Example 6.1 combinators computable (M4). `arxiv.md` Prop 7.7 row flipped to **Pass**.

**`λx. x^§` (Scott's injection `inSharp`):** `inSharpMap : ApproximableMap D (Dsharp D hD)` with
relation `X (λx.x^§) W ↔ 0·X ⊆ W` (`embZero X ⊆ W`); `inSharpMap_toElementMap` proves its elementwise
action is Example 6.1's `inSharp` (so it genuinely is `λx.x^§`). **`inSharp_isComputable`**: the index
relation is `embZero (P.X n) ⊆ V_m ↔ V_{2n+1} ⊆ V_m`, i.e. `dsharpPresentation.incl_computable`
reindexed by the primrec `(n,m) ↦ (2n+1, m)`, hence (recursively decidable ⟹) r.e.

**`proj₀` (first projection of the pair part):** `proj0Map : ApproximableMap (Dsharp D hD) (Dsharp D hD)`
with relation `W proj₀ Z ↔ Z = Γ ∨ ∃ P Q, W = 1·P ∪ 2·Q ∧ P ⊆ Z`; `proj0_toElementMap_pairSharp`
proves `proj₀(⟨x,y⟩^§) = x`. **`proj0_isComputable`**: `proj0_rel_Vsharp_iff` reduces the index
relation to `k = 0 ∨ (m % 2 = 0 ∧ m ≠ 0 ∧ V_{(m/2-1).unpair.1} ⊆ V_k)` — a disjunction of the
equality decider (`k=0`), parity deciders (`%2`, `≠0`), and `incl_computable` reindexed by the primrec
left-child map `s ↦ pair ((s.1/2-1).unpair.1) s.2`; all recursively decidable, so `.re`.

**Axioms:** the `ApproximableMap` **data** (`inSharpMap`, `proj0Map`) and **both faithfulness
theorems** (`inSharpMap_toElementMap`, `proj0_toElementMap_pairSharp`) are choice-free
`⊆ {propext, Quot.sound}`. Only `inSharp_isComputable`/`proj0_isComputable` pull `Classical.choice`
(via `incl_computable` / `Set` reasoning over arbitrary `α`) — unavoidable, same as the M1–3 deciders.

**Reusable patterns:** to characterize an `ApproximableMap`'s relation against `Vsharp` and conclude
computability, mirror Theorem 7.4's `proj₀`/`in₀`: state the relation as a Boolean combination of
`incl_computable`/`natEq`/`%2` deciders (reindexed by primrec maps), then `RecDecidable.of_iff … |>.re`.
The `show REPred (fun s => f.rel (Vsharp … s.unpair.1) (Vsharp … s.unpair.2))` step relies on
`(dsharpPresentation P hD).X = Vsharp D P` *definitionally*; the `@[simp] dsharpPresentation_X` handle
normalizes the `incl_computable` predicate's `(dsharpPresentation …).X` to `Vsharp` so `simp` closes the
`of_iff` reindex goals. **`Element.ext` must be used `apply`-style** (`apply Element.ext; intro W`); as a
term `Element.ext (fun W => …)` mis-resolves its first explicit slot to a `NeighborhoodSystem`.

**Prop 7.7 is now fully Pass.** Optional follow-on: **Exercise 7.17** (the *full* finish — all Example
6.2 combinators + strict `g : D^§ → E`), which generalizes this selection.

---

## Checkpoint 2026-06-27 — Example 7.8 (`PN` effectively given) COMPLETE / Pass, fully choice-free

**What landed.** `Domain/Neighborhood/Example78.lean` (ns `Domain.Neighborhood.Example78`) +
a new choice-free primitive-recursive **bitwise OR** layer at the end of
`Domain/Neighborhood/Recursive.lean`. Wired into `Domain.lean`; `lake build Domain` green; **every
declaration — including the presentation *data* — audits `⊆ {propext, Quot.sound}`.**

**Math (the powerset domain `PN`).** Scott enumerates the finite subsets of `ℕ` by
`Eₙ = {k ∣ ∃ i,j. i<2ᵏ ∧ n=i+2ᵏ+j·2ᵏ⁺¹}`, which is just "`k` is a set bit of `n`" = `Nat.testBit n k`.
The neighbourhoods are the *cofinite* sets `nbhd n := {k ∣ n.testBit k = false} = ℕ ∖ Eₙ` (so
`nbhd 0 = ℕ = Δ`, `nbhd_zero`). Key facts:
- **`nbhd_inter n m : nbhd n ∩ nbhd m = nbhd (n ||| m)`** — Scott's `Eₙ ∪ Eₘ = E_k` with `k = n ||| m`
  (bitwise OR); proof is `Nat.testBit_lor` + `Bool.or_eq_false_iff` after `Set.ext`.
- **`nbhd_injective`** — `Nat.eq_of_testBit_eq` (the converse-inclusion ordering Scott mentions; we
  only need injectivity).
- **`PN : NeighborhoodSystem ℕ`** (`mem Y := ∃ n, Y = nbhd n`, master `ℕ`); closed under ∩ by
  `nbhd_inter`, so *any two neighbourhoods are consistent* (`PN_consistent`) — Scott's remark.
- **`PNpres : ComputablePresentation PN`**: enumeration `nbhd`; intersection function = `myLor`
  (below); 7.1(i) `nbhd n ∩ nbhd m = nbhd k ↔ (n ||| m) = k` is decided by `RecDecidable.natEq`
  (equality of two primrec functions, then `nbhd_injective`); 7.1(ii) is always-true
  (`recDecidable_of_forall`). **`PN_isEffectivelyGiven`** packages it.

**New recursion theory — choice-free primitive-recursive `n ||| m` (`Recursive.lean`).** mathlib's
`Nat.lor` is not exposed as a `Nat.Primrec`, so we build our own and bridge to `Nat.lor`:
- `lowOr x y := 1 - (1 - (x%2 + y%2))` (the `{0,1}` low-bit OR); `lowOr_eq_mod : lowOr x y = (x|||y)%2`
  via `Nat.testBit_lor`+`Nat.testBit_zero` and an **explicit `Nat.mod_two_eq_zero_or_one` case split**
  (NOT `omega` on the `↔` — that pulls `Classical.choice`, the documented gotcha).
- `lorStep` (packed state `pair (pair curA curB) (pair weight acc)`) strips the low bit of each arg,
  ORs them (`lowOr`), and accumulates with a doubling weight; `myLor a b` iterates it `a+b` times and
  reads `acc`.
- `lor_low_rec : x ||| y = 2·(x/2 ||| y/2) + lowOr x y` (one-step law, via `Nat.div_add_mod` and a
  `testBit` computation of `(x|||y)/2`).
- `lorStep_iter_spec` — the invariant `acc_k + 2ᵏ·(a/2ᵏ ||| b/2ᵏ) = a ||| b` (with `curA_k = a/2ᵏ`,
  weight `2ᵏ`); at `k = a+b` both args are `0` (since `a < 2^a ≤ 2^(a+b)`, `Nat.lt_two_pow_self`), giving
  **`myLor_eq_lor : myLor a b = a ||| b`**.
- **`primrec_myLor : Nat.Primrec (fun t => myLor t.unpair.1 t.unpair.2)`** — from `Nat.Primrec.prec`
  (base = init state, step = `lorStep`), bridged to `Function.iterate` by `rec_const_iterate`.
- All of `primrec_lowOr`, `primrec_lorStep`, `lowOr_eq_mod`, `myLor_eq_lor`, `primrec_myLor` audit
  `⊆ {propext, Quot.sound}`. Added imports to `Recursive.lean`: `Mathlib.Data.Nat.Bitwise`,
  `Mathlib.Tactic.Ring`.

**Reusable.** `Recursive.myLor`/`myLor_eq_lor`/`primrec_myLor` are a general choice-free
primitive-recursive bitwise-OR usable elsewhere. The set-theoretic neighbourhood `Example78.nbhd`
and `nbhd_inter`/`nbhd_injective` are the foundation for **Exercise 7.23** (combinators on `PN`).

**Gotcha reconfirmed:** `omega` fed an `↔` (or a goal/hyp whose decidability it can't see) silently
pulls `Classical.choice`; replace with an explicit finite case split (`Nat.mod_two_eq_zero_or_one`).
Also, on `Set`, `(h : A = B).ge` to get `B ⊆ A` pulls `Classical.choice` — use `h.symm.subset`
(`Eq.subset`) instead, which is axiom-free.

---

## Checkpoint 2026-06-27 — Definition 7.9 (Smyth power domain `ℙ𝒟` family) COMPLETE / Pass, choice-free

**What landed.** `Domain/Neighborhood/Definition79.lean` (ns `Domain.Neighborhood.NeighborhoodSystem`),
wired into `Domain.lean` (after `Example78`); `lake build Domain` green; **every declaration audits
`⊆ {propext, Quot.sound}`** (the whole file is choice-free, *data and proofs*).

**Math (Definition 7.9).** Scott's Smyth power domain `ℙ𝒟 = {⋃_{i<n}↓Xᵢ ∣ ∀i<n. Xᵢ∈𝒟}`, where the
**down-set** `↓X = {Y∈𝒟∣Y⊆X}`. The key reuse: **`↓X` of §7 is *exactly* Exercise 1.20's `upSet`**
(`Exercise120.lean`: `upSet X = {Y∈𝒟∣Y⊆X}`), and the **preparation `𝒟† = {↓X∣X∈𝒟}`** Scott uses to make
the construct iso-invariant is *exactly* Ex 1.20's `powerSystem` (the positive system over tokens `Δ†=𝒟`).
So Def 7.9 is "the closure of `𝒟†` under finite unions, including the empty union `∅` (`n=0`)".

**What got built (all in `Definition79.lean`):**
- **`dagger V := V.powerSystem`** (alias for `𝒟†`) + **`dagger_isomorphic : V ≅ᴰ V.dagger`** (reuses
  `isomorphic_powerSystem`).
- **`PDmem W := ∃ L:List(Set α), (∀X∈L, V.mem X) ∧ W=⋃_{X∈L} V.upSet X`** — the `ℙ𝒟` neighbourhood
  family. Lists model Scott's "finite sequences of integers"; `L=[]` realizes the empty union `∅`.
- **`mem_PDunion`** (`z∈⋃_{X∈L}↓X ↔ ∃X∈L, z∈↓X`, via `Set.mem_iUnion`+`exists_prop`), **`PDmem_empty`**,
  **`PDmem_upSet`** (`X∈𝒟 ⟹ ↓X∈ℙ𝒟`), **`PDmem_master`** (`↓Δ`), **`PDmem_union`** (binary—hence
  finite—union closure, list `++`).
- **`PDmem_iff_fin`** — same family with Scott's literal `⋃_{i<n}` (`Fin n → Set α`); `List`↔`Fin` via
  `List.ofFn`/`List.get`/`List.get_of_mem`/`List.mem_ofFn`+`Set.mem_range`.
- Two displayed remarks: **`upSet_inter_nonempty_iff`** (`(↓X∩↓Y).Nonempty ↔ ∃Z∈𝒟,Z⊆X∩Y`, i.e. `{X,Y}`
  consistent) and **`dagger_upSet_inter`** (consistent ⟹ `↓X∩↓Y=↓(X∩Y)∈𝒟†`). The unconditional set
  identity `↓X∩↓Y=↓(X∩Y)` is Ex 1.20's `upSet_inter`.

**Choice discipline (bit me once).** `simp` closing `∅=⋃_{X∈[]}↓X` and `↓X=⋃_{Y∈[X]}↓Y` silently pulls
`Classical.choice` here. Fixed with explicit choice-free proofs: **`cases hX`** on `hX : X∈([]:List _)`
(empty inductive, no constructors), `Set.notMem_empty`, `List.mem_singleton`. Also note `List.not_mem_nil`
in this toolchain is the *applied* form `(a∈[])→False` (use `cases`/`(… h).elim`, not `not_mem_nil a`),
and the term-mode `nomatch hX` mis-parsed inside an anonymous-constructor field — use tactic `cases hX`.

**Next concrete target: Proposition 7.10** — package `ℙ𝒟` as `PowerDomain : NeighborhoodSystem (Set α)`
(`mem := PDmem`, `master := upSet master`; `inter_mem` from distribution of `∩` over the finite union +
`upSet_inter`; `sub_master` since each `↓Xᵢ ⊆ ↓Δ`), then its `ComputablePresentation` (enumerate finite
sequences via `Nat.pair`/`decodeList`; intersection = the distributed double-union with empty terms
thrown out, each `X_{nᵢ}∩X_{mⱼ}=X_{kᵢⱼ}` from `𝒟.inter`; equality decided by
`↓X_k ⊆ ⋃_{i<q}↓X_{nᵢ} ↔ ∃i<q. X_k⊆X_{nᵢ}` — recursive by `𝒟.incl`). Reuse `Definition79.lean`'s
`PDmem_union`/`mem_PDunion`/`upSet_inter`/`upSet_inter_nonempty_iff`.

---

### Checkpoint — 2026-06-27 — **Proposition 7.10 COMPLETE / Pass** (`Proposition710.lean`, green, wired, audited)

`ℙ𝒟` is a neighbourhood system *and* effectively given whenever `𝒟` is. Built on `Definition79.lean`
(`PDmem`, `PDmem_union`, `PDmem_master`, `mem_PDunion`) + Ex 1.20 `upSet`/`upSet_inter` + the choice-free
recursion theory in `Recursive.lean`.

**Part A — `PowerDomain : NeighborhoodSystem (Set α)`** (`mem := PDmem`, `master := ↓Δ`):
- `upSetUnion_nil`/`upSetUnion_cons` (cons law for `⋃_{X∈L}↓X`).
- `PDmem_upSet_inter` (`↓X∩↓Y ∈ ℙ𝒟`): rewrite `↓X∩↓Y=↓(X∩Y)` (`upSet_inter`), then **`by_cases V.mem (X∩Y)`** —
  consistent ⟹ one down-set `PDmem_upSet`; else `↓(X∩Y)=∅` because `inter_mem` makes any `Z⊆X∩Y` force
  `X∩Y∈𝒟`. **This `by_cases` is the SOLE `Classical` step.** It is genuinely unavoidable (membership in an
  *arbitrary* system is not decidable) and lives only in the `inter_mem` **Prop** field — the data fields
  `mem`/`master` are choice-free.
- `PDmem_upSet_inter_biUnion` → `PDmem_biUnion_inter` → `PDmem_inter` (distribute `∩` over both finite
  unions via `Set.*_inter_distrib_*`, then term-by-term). `sub_master` since each `↓X_a ⊆ ↓Δ`.

**Part B — `PowerDomain_isEffectivelyGiven : V.IsEffectivelyGiven → V.PowerDomain.IsEffectivelyGiven`**,
via `PDPresentation P cons hconsp hcons` (parametrised on `𝒟`'s primrec consistency decider `cons`,
extracted **choice-free** from `P.cons_computable` inside the `Nonempty` proof — same pattern as
`Theorem75.lean`'s `funPresentation`).
- **Enumeration** `Ypd c := UPX (decodeList c) = ⋃_{a∈decodeList c} ↓X_a` (`Ypd 0=∅` via `decodeList_zero`;
  `Ypd ⟨v,acc⟩+1 = ↓X_v ∪ Ypd acc` via `decodeList_succ`). `mem_X`/`Ypd_isPDmem` (list `(dl c).map P.X`),
  `surj`/`PDmem_exists_Ypd`.
- **Relation (i) — equality.** `Ypd_subset_iff : Y_c⊆Y_k ↔ ∀a∈dl c,∃b∈dl k, X_a⊆X_b` (key step
  `upSet_subset_Ypd_iff`: a down-set lies in a finite union of down-sets iff its top is below one of them).
  `subCode_computable` is `RecDecidable₂` via the **NEW** choice-free combinators
  **`RecDecidable₂.bForallList`/`RecDecidable₂.bExistsList`** (bounded `∀/∃` over `decodeList`, added to
  `Recursive.lean`) applied to `P.incl_computable.swap`. `eqCode_computable` = `subCode ∧ subCode.swap`
  (`Ypd_eq_iff` = `Set.Subset.antisymm_iff`).
- **Intersection code** `interCode cons n m` — nested `foldCode`: outer over `dl n`, inner over `dl m`,
  prepending `P.inter a b` exactly on **consistent** pairs (`isOne (cons ⟨a,b⟩)` via `selectFn`). Step lemmas
  `innerInterStp`/`outerInterStp` + `*_eq` (via `foldCode_eq'`). Correctness `Ypd_interCode : Y_{interCode n m}
  = Y_n∩Y_m` via `Ypd_innerstep` (the `selectFn`/`isOne` `by_cases` is a **decidable ℕ-equality**, choice-free)
  → `Ypd_innerfoldl`/`Ypd_innerInterCode`/`Ypd_outerfoldl`. Primrec via `primrec_foldCode`/`primrec_selectFn`/
  `primrec_isOne`. `cons_computable` for `ℙ𝒟` is trivial (`∅∈ℙ𝒟` ⟹ every pair consistent; witness code `0`).

**Axiom audit.** Pure data/recursion is choice-free: `interCode` *no axioms*; `Ypd`, `primrec_interCode`,
`subCode_computable` `⊆{propext,Quot.sound}`. The bundled `def`s `PowerDomain`/`PDPresentation` and the
`Prop`-valued `eqCode_computable`/`Ypd_interEq_computable`/`PowerDomain_isEffectivelyGiven` carry
`Classical.choice`, confined to **Prop** obligations (the Part-A `inter_mem` split above + `RecDecidable`
existentials / mathlib set lemmas) — consistent with the choice discipline.

**Gotchas this session (all fixed).** (1) Auto-bound section vars: `P : ComputablePresentation V` pulls `V`
into every `def`/`theorem` that mentions `P`, so the intersection-code defs are `V.innerInterStp P …`,
`V.interCode P …` etc. — **must use `V.`-dot notation** at every call site (writing `interCode P …` feeds `P`
as the `V` argument). (2) `(cons n m : ℕ)` accidentally typed `cons : ℕ` — write `(cons : ℕ → ℕ) (n m : ℕ)`.
(3) `isOne_eq_one_iff` takes the value explicitly: `(isOne_eq_one_iff _).mpr h`. (4) The new bounded-quantifier
lemmas were originally in the `RecDecidable` namespace but operate on `RecDecidable₂`, breaking dot notation —
renamed to `RecDecidable₂.bForallList`/`bExistsList`.

**Next concrete target: Def 7.11 / Prop 7.12** (finite-element joins `{x₀,…,x_{n-1}}` in `ℙ𝒟`), building
directly on `Proposition710.lean`'s `Ypd`/`interCode`/`PowerDomain`.

---

### Checkpoint — 2026-06-27 — **Definition 7.11 COMPLETE / Pass** (`Definition711.lean`, green, wired, audited)

Scott's finite-element join in `|ℙ𝒟|` from PRG-19 p.129:

`{x₀,…,x_{n-1}} = { z ∈ |ℙ𝒟| ∣ ∃ X₀∈x₀ … ∃ X_{n-1}∈x_{n-1}. ⋃_{i<n}(↑X_i) ⊆ z }`

(with Scott's note `∀ i<n. X_i ∈ z` left as documentation — the formal membership uses the union of down-sets).

**Formalization (`Definition711.lean`, on `Proposition710.lean`'s `PowerDomain`).**
- **`PDmemFinJoin xs W`** — membership: `∃ (X : Fin n → Set α) (∀ i, xs i).mem (X i)) ∧ PD.mem W ∧ ∀ i, ↓X_i ⊆ W`.
- **`PDfinJoinZero = ⊥`** (`PDmem_finJoinZero`); **`PDfinJoinSucc xs`** packages the filter (filter axioms proved;
  `inter_mem` uses **`upSet_inter`** from Ex 1.20).
- **`PDfinJoin n xs`** — `n = 0` ⟹ `⊥`; else `PDfinJoinSucc`.
- **`PDmem_finJoin`**, **`PDmem_finJoin_iUnion`** (Scott's displayed `⋃_{i<n} ↓X_i ⊆ W` via `Set.iUnion_subset`).
- **`PDsingleton x = PDfinJoin 1 ![x]`** with **`PDmem_singleton`**.

**Choice discipline.** Filter proofs choice-free; bundled `def`s inherit `Classical.choice` from `PowerDomain`
(same Prop-level `inter_mem` pattern as Prop 7.10). Audited: `PDfinJoin`/`PDsingleton` `⊆{propext,Quot.sound,Classical.choice}`.

**Superseded by Prop 7.12 checkpoint below** (`{↑X}=↑(↓X)`, intersection law, approximability/computability).

---

### Checkpoint — 2026-06-27 — **Proposition 7.12 PARTIAL / Pass (A,B,D)** (`Proposition712.lean`, green, wired, audited)

Scott's PRG-19 p.129 Prop 7.12: the finite join map `λx₀,…,x_{n-1}.{x₀,…,x_{n-1}} : Dⁿ→ℙD` is approximable and computable when `D` is effectively given; `{x₀,…,x_{n-1}} = {x₀}∩…∩{x_{n-1}}`; and `λx.{x}` shows `D ⊴ ℙD`.

**Formalization (`Proposition712.lean`, on `Definition711.lean` + `Proposition710.lean`).**
- **Part A:** **`PDsingletonApproxMap`** via Ex 2.8 **`ofMono`** (`↑X↦{↑X}`); **`PDsingleton_mono`**; **`PDsingletonApproxMap_toElementMap`**; **`PDsingleton_principal`** (`{↑X}=↑(↓X)`).
- **Part B:** filter meet **`PDsingletonMeet`**; **`PDfinJoin_pair`** / **`PDfinJoin_inter_two`** (binary `{x,y}={x}∩{y}`); **`PDfinJoinApproxMap₂`** + **`finJoinMap_prod`** (`ofMap₂` on `D×D`).
- **Part C — DEFERRED:** `D ⊴ ℙD` (Lemma 6.15 projection pair). Naive token retraction `↓X↦↑X else ⊥` is not **`ofMono`**-monotone when `↓A∩↓B∈ℙ𝒟` but `A∩B∉𝒟`; `𝒟† ◁ ℙ𝒟` also fails **`inter_closed`**. Injection half is **`PDsingletonApproxMap`**.
- **Part D:** **`PDsingletonApproxMap_rel_Ypd_iff`** (`∃b∈dl k, X_n⊆X_b`); **`singleton_isComputable`**; **`PDfinJoinApproxMap₂_isComputable`** (two singleton tests, `proj₀`-style reindexing).

**Gotchas.** (1) Avoid `singletonMap`/`finJoinMap₂` names inside `namespace NeighborhoodSystem` with `(V := V)` — Lean parses as structure field projection. (2) Use **`PDext`** / `@Element.ext (Set α) V.PowerDomain` for `|ℙ𝒟|` extensionality. (3) **`RecDecidable₂.bExistsList.swap`** for correct pair-coding of bounded `∃` over decode lists in computability proofs.

**Choice discipline.** All proofs choice-free modulo inherited `PowerDomain.inter_mem` (`Classical.choice` in Prop fields only). Audited: main decls `⊆{propext,Quot.sound,Classical.choice}`.

**Next concrete target: Prop 7.12 Part C (`D ⊴ ℙD`).**

---

### Checkpoint — 2026-06-27 (later) — **Prop 7.12 Part C WIP / working tree RED** (`Proposition712.lean` does NOT build)

**Status: do not trust the working copy.** `Proposition712.lean` is uncommitted and **red**: `lake build Domain.Neighborhood.Proposition712` → **21 errors, 0 `sorry`**, file grew **~390 → 718 lines**. A subagent fix-loop on Part C was **interrupted mid-edit**. Parts A/B/D were green at the last *committed* `HEAD`; `git diff`/`git stash` recovers the green A/B/D file. Decide first: **(a) restart Part C from the committed green file, or (b) finish the lemmas below.**

**The route being attempted (sound on paper, Scott `D ≅ D† ⊴ ℙD`).** Build the retraction `j : ℙ𝒟 → 𝒟†` with Ex 2.8 **`ofMono`** from an *element-level* map `PDdaggerRetractElem W hW : |𝒟†|`, instead of a token relation (which we already know fails `inter_right`/`mono`, see the earlier checkpoint). The element value is the principal filter `↑(pdListSup L)` where `L` is a witness list for `W∈ℙ𝒟` and `pdListSup` (= `PDlistFoldSup V.master`) folds the generators with
`pdFoldSupStep master acc z := if z⊆acc then acc else if acc⊆z then z else master`
— i.e. it keeps the larger of `acc,z` under `⊆`, and **collapses to `master` (=⊥ in info order) when they are incomparable.** Intuition: the bluntest `Y∈𝒟` with `W ⊆ ↓Y`. The one case that matters for `j∘i=I` is a **single generator**: `pdListSup [X] = X` (`PDlistFoldSup_singleton`, *proved*), so `j(↓X)=↑X`.

**What compiles (and is reusable):** everything through `PDdaggerInj` (the injection `↓X↦↓X`, `S⊆W`) and `Isomorphic.trianglelefteq_trans` (transports `⊴` along `D≅D†`) — these are unchanged and fine. `pdFoldSupStep_ge_acc/_mem/_ge_z`, `PDlistFoldSup_mem`, `PDlistFoldSup_singleton` build.

**Where it's stuck (the 21 errors cluster in the multi-generator fold lemmas + `ofMono` plumbing):**
- `pdFoldSupStep_mono_acc` (line ~284): `simp` leaves unsolved goals on the 4-way `by_cases` over `z⊆acc/acc⊆z/z⊆acc'/acc'⊆z` (monotonicity of one fold step in `acc`).
- `pdFoldSup_foldl_ub` (~302–305): `List.mem_cons_self` arity / `Type mismatch` on the cons branch upper-bound recursion.
- `PDlistFoldSup_eq_of_upSet` (~446/466), `PDlistFoldSup_sup_sub_of_union` (~495–521), `PDlistFoldSup_upSet_mono` (~554/556): the `rewrite … upSet …` steps don't find the pattern; these are the **core monotonicity lemma** `W'⊆W → pdListSup uses … ⊆ …` feeding `PDdaggerRetractElem_mono`.
- `PDdaggerRetractElem_mono` (~575), `PDdaggerRetract_toElementMap_principal` (~592/594), `PDdaggerRetract_comp_inj` / `PDdaggerInj_comp_retract_le`, `dagger_trianglelefteq_powerDomain` (~634): downstream `ofMono` glue (`toElementMap_ofMono_principal`, `eq_of_toElementMap_principal`) — blocked until the fold lemmas land.

**⚠️ Choice-discipline regression to fix.** The current `PDdaggerRetractElem` uses **`Classical.choose hW`** to extract the witness list `L` from `W∈ℙ𝒟` (`∃ L, …`), so `PDdaggerRetract` is **`noncomputable` and pulls `Classical.choice` into *data*** — this violates `.cursor/rules/handoff-discipline.mdc` (data must be `⊆{propext,Quot.sound}`). Two ways out: (i) prove the fold value is **independent of the chosen list** (any two witness lists for the same `W` give the same `↓(pdListSup L)` because `↓(pdListSup L)` is determined by `W` as the least down-set ⊇ `W`), then phrase `PDdaggerRetractElem` via that canonical value; or (ii) accept choice here and **call it out** (Prop-level only) — but it's currently in `def`, not a proof, so (i) is preferred.

**Recommended restart (if not finishing the above):** keep `ofMono` + `pdListSup`, but (1) make `PDdaggerRetractElem` choice-free by defining the value as `↑(⋂{Y∈𝒟 ∣ W⊆↓Y})`-style canonical token or by `pdListSup`-of-`Classical.choose` *only inside `Prop`* via a `rel` characterization; (2) prove the single clean monotonicity lemma `W'⊆W → W ⊆ ↓(pdListSup L) → W' ⊆ ↓(pdListSup L')` first and derive `_mono` from it; (3) the two projection-pair laws then follow from `PDlistFoldSup_singleton` (`j∘i=I`) and `PDdaggerRetractElem_upSet_subset` (`i∘j⊑I`) — both already drafted near lines 532/596.

---

## Checkpoint 2026-06-27 (latest) — **Prop 7.12 Part C REFUTED** (`D ⊴ ℙD` is FALSE in general); `Proposition712.lean` GREEN again

**Resolution of the WIP above.** The `ofMono`/`pdListSup` projection-pair route was **not** stuck on
plumbing — it was attempting to prove a **false** theorem. `PDdaggerRetractElem_mono` is *genuinely
unprovable*: with `pdListSup [] = Δ` we get `j(∅)=↑Δ=⊥`, but `∅ ⊆ ↓X` forces `j(↓X)=↑X ≤ j(∅)=⊥`,
i.e. `↑X ≤ ⊥`, false unless `X=Δ`. The deeper reason: `∅` (the empty union, always in `ℙ𝒟` by
`PDmem_empty`) is the **top** `↑∅ = ⊤_{ℙ𝒟}` of `|ℙ𝒟|`, and any monotone (approximable) retraction
`ℙ𝒟→𝒟` must send `⊤_{ℙ𝒟}` to an upper bound of all of `|𝒟|` = a greatest element of `|𝒟|`, which a
general bounded-complete domain does **not** have.

**What landed (green, wired, zero `sorry`).** `Proposition712.lean` restored to the committed green
**Parts A/B/D** (verbatim) + a new **`namespace Counterexample712C`** formalizing the refutation. The
broken 718-line Part C WIP is gone. Added one import: `Domain.Neighborhood.Lemma615` (for `⊴`/`◁`).

**The counterexample (clean invariant: "has a greatest element").**
- **`HasTop E := ∃ t:E.Element, ∀ x, x ≤ t`.**
- **`improperTop` / `hasTop_of_inter_closed`** — an *unconditionally* ∩-closed system (∀XY,
  `mem X→mem Y→mem(X∩Y)`, **no** witness needed) has the improper filter (= all neighbourhoods) as a
  greatest element. (Data `improperTop` audits **no axioms**.)
- **`powerDomain_hasTop`** — `ℙ𝒟` is unconditionally ∩-closed (`PDmem_inter`; the empty union always
  supplies the missing witness), so `|ℙ𝒟|` *always* has a top.
- **`subsystem_inter_closed`** — `D'◁ℙ𝒟` inherits unconditional ∩-closure (Def 6.10 `inter_closed`,
  routed through the always-true `ℙ𝒟.mem(X∩Y)`).
- **`hasTop_of_iso`** — `≅ᴰ` is an order-iso of element lattices (`OrderIso.le_iff_le` +
  `apply_symm_apply`), so it transports `HasTop`.
- ⟹ **`hasTop_of_trianglelefteq_powerDomain : D ⊴ E.PowerDomain → HasTop D`** (destruct `⊴` into
  `D'◁ℙ𝒟 ∧ D≅ᴰD'`, chain the three facts).
- **`Vshape : NeighborhoodSystem Bool`** — the flat 2-point domain, `mem X := X=univ ∨ X={true} ∨
  X={false}`, master `univ`. `inter_mem` holds (the only non-trivial pair `{true}∩{false}=∅` has **no**
  neighbourhood witness `Z⊆∅`, so condition (ii) is vacuous there). **Data `Vshape` audits
  `⊆{propext,Quot.sound}`** (choice-free: the bad inter cases discharge via
  `obtain ⟨z,hz⟩ := hZne; exact absurd (hZsub hz) (Set.notMem_empty z)`, **not** `Set.Nonempty.ne_empty`).
- **`Vshape_not_hasTop`** — a top `t` would contain `{true}` and `{false}` (from `↑{true},↑{false} ≤ t`),
  hence `{true}∩{false}=∅ ∈ t` by `t.inter_mem`, but `∅∉Vshape` (`Vshape_not_mem_empty`).
- **`vshape_not_trianglelefteq_powerDomain : ¬(Vshape ⊴ Vshape.PowerDomain)`** — the headline.

**When Part C *does* hold.** `D ⊴ ℙ𝒟` is true exactly when `|𝒟|` has a greatest element, e.g. when
`∅∈𝒟` (then `↑∅=⊤_{|𝒟|}`). The surviving "half" of Scott's would-be projection pair is the singleton
**injection** `PDsingletonApproxMap` (Part A), which is fine for every `𝒟`.

**Faithfulness note.** This refutes Scott's *as-formalized* claim only because Definition 7.9 (this
project, faithful to Scott's text "the finite unions can be empty, `n=0`") puts `∅∈ℙ𝒟`. A variant
`ℙ𝒟` restricted to **non-empty** unions (`n≥1`) would not be unconditionally ∩-closed (`↓A∩↓B` can be
`∅∉ℙ𝒟`), removing the forced top — but that would break the committed-green Prop 7.10 / Def 7.11 and
deviate from the transcribed Definition 7.9. Left as-is; the counterexample is the correct outcome
under the present definitions.

**Axiom audit.** `Vshape ⊆{propext,Quot.sound}`, `improperTop` no axioms; the `Prop`-valued
counterexample lemmas + A/B/D maps `⊆{propext,Quot.sound,Classical.choice}` (choice inherited from
`PowerDomain.inter_mem`'s `by_cases`, Prop-level only). `lake build Domain` green.

---

## Checkpoint 2026-06-27 — **Exercise 7.13 — next target** (abstract `INCL` characterization of effectively given domains)

**Status: NOT STARTED.** This is the next concrete work item now that Prop 7.12 is resolved. No file
yet; suggested `Domain/Neighborhood/Exercise713.lean`, ns `Domain.Neighborhood.Exercise713`, wire into
`Domain.lean` after `Proposition712`.

**Scott's exact statement (PRG-19 p.130).** "Show that an effectively given domain can always be
identified with a relation `INCL(n,m)` on integers, where the two derived relations
- `CONS(n,m) :↔ ∃k. INCL(k,n) ∧ INCL(k,m)`  (consistency), and
- `MEET(n,m,k) :↔ ∀j. (INCL(j,k) ↔ INCL(j,n) ∧ INCL(j,m))`  (binary meet / intersection)

are both **recursively decidable**, and where the axioms hold:
- (i)   `∀n. INCL(n,n)`                                   (reflexive)
- (ii)  `∀n m k. INCL(n,m) ∧ INCL(m,k) → INCL(n,k)`        (transitive)
- (iii) `∃m ∀n. INCL(n,m)`                                 (a greatest code `m` — the master `Δ`)
- (iv)  `∀n m. CONS(n,m) → ∃k. MEET(n,m,k)`               (consistent pairs have a meet)

Hint: consider the neighbourhood system `𝒟 = { {m∈ℕ ∣ INCL(m,n)} ∣ n∈ℕ }`. Is this essentially any
effectively given system?"

**Reading / what to formalize.** `INCL(n,m)` is the integer image of `Xₙ ⊆ Xₘ`. The exercise is an
**equivalence (both directions)**:
- **(⇒)** From `P : ComputablePresentation V` (an effectively given `𝒟`) produce
  `INCL n m := P.X n ⊆ P.X m` and show it is recursively decidable (this is essentially
  `P.incl_computable` — already a `RecDecidable₂`), that `CONS`/`MEET` are recursively decidable
  (`CONS` = `P.cons`/consistency decider; `MEET` from the intersection function `P.inter` +
  `P.interEq`-style equality), and that axioms (i)–(iv) hold (refl/trans of `⊆`; master `P.masterIdx`
  for (iii); `inter` witness for (iv)).
- **(⇐)** From any `INCL` relation on `ℕ` with `CONS`/`MEET` recursively decidable and (i)–(iv), build
  the neighbourhood system `Sᵢ := {m ∣ INCL(m,n)}` (the hint's `𝒟`), show `Sₙ ⊆ Sₖ ↔ INCL(n,k)`
  (← by `INCL(m,n)→INCL(m,k)` via (ii); → because `n∈Sₙ` by (i)), that it is a genuine
  `NeighborhoodSystem` (master from (iii); conditional `inter_mem` from (iv)+`MEET`), and that it is
  **effectively given** (a `ComputablePresentation`) with enumeration `n ↦ Sₙ`, intersection from
  `MEET`, equality/inclusion from `INCL`/its decidability. Finally that the two passes are mutually
  inverse "up to effective isomorphism" (this is where **Exercise 7.18**'s notion of *effective
  isomorphism* would tighten "essentially the same"; for 7.13 a round-trip
  `INCL ↦ 𝒟 ↦ INCL` equality and a `𝒟 ≅ᴰ`-level statement should suffice).

**Infrastructure to reuse (all already in the repo).**
- `ComputablePresentation V` (`Definition71.lean`): fields `X : ℕ→Set α`, `mem_X`, `surj`,
  `incl_computable : RecDecidable₂ (fun n m ↦ X n ⊆ X m)` (i.e. `INCL`!), `cons_computable`,
  `inter`/`interEq`, `masterIdx`/`masterIdx_spec`. This is *literally* the data 7.13 abstracts.
- `Recursive.lean`: `RecDecidable`/`RecDecidable₂`/`REPred`, `.and`/`.of_iff`/`.comp`,
  `RecDecidable.natEq`, bounded `∀/∃` (`bForall`, `bForallList`/`bExistsList`), `recDecidable_of_forall`.
  `MEET` needs an **unbounded `∀j`** that is nonetheless decidable — handle it the way Prop 7.10's
  `interCode`/equality does: reduce `MEET(n,m,k)` to a *finite* check via the meet **witness/index**
  (the `inter` code) rather than a literal `∀j`, i.e. `MEET(n,m,k) ↔ Xₖ = Xₙ∩Xₘ` decided by the
  presentation's `interEq`. (Scott states `MEET` as `∀j[…]`, but on an effectively given system it is
  decidable precisely because the meet is computed by `inter`.)
- For the (⇐) construction, mirror `Definition71.lean`'s `unitSys_isEffectivelyGiven` /
  `Example78.lean`'s `PN` for how to assemble a `ComputablePresentation` from a primrec relation.

**Choice discipline.** The `INCL`/`CONS`/`MEET` deciders and the assembled presentation *data* should
stay `⊆{propext,Quot.sound}` (build on the choice-free `Recursive.lean` layer, **not** mathlib's
recursion theory). `Set`-equality/membership reasoning over an arbitrary carrier will pull
`Classical.choice` at the `Prop` level only (same pattern as 7.4/7.5/7.10). Watch the documented
traps: `omega` on an `↔`/`Set`-goal and `simp` closing `Set` identities both silently pull choice.

**Definition of done (per `.cursor/rules/handoff-discipline.mdc`).** `lake build` green, zero `sorry`,
axiom audit on the headline decls, append a dated checkpoint here, flip the `arxiv.md` 7.13 row to
**Pass** with a dense note, wire the new module into `Domain.lean`.

---

## Checkpoint 2026-06-27 (latest) — **Exercise 7.13 COMPLETE / Pass** (`Exercise713.lean`, green, wired, audited, **fully choice-free**)

The full equivalence "an effectively given domain ⇔ a recursive `INCL(n,m)` relation on `ℕ`", in
both directions plus both round-trips. **All declarations — data *and* Prop — audit
`⊆{propext,Quot.sound}`** (stronger than this target's plan anticipated; the only subtle step,
`toNbhd_inter_eq_iff`, uses `exact iff_comm` instead of `tauto` to avoid `Classical.choice`).

**The abstract data — `InclStructure`.** A relation `INCL : ℕ → ℕ → Prop` plus, following the project
convention that `ComputablePresentation` carries `inter` as *primrec data* (rather than recovering it
by an unbounded μ-search), the **witnesses** `meetIdx : ℕ→ℕ→ℕ` (primrec) and `topIdx : ℕ`. Fields:
`incl_dec`/`cons_dec`/`meet_dec` (`RecDecidable₂`/`RecDecidable₂`/`RecDecidable₃` of `INCL`, of
`CONS n m := ∃k,INCL k n∧INCL k m`, of `MEET n m k := ∀j,INCL j k↔(INCL j n∧INCL j m)`),
`meetIdx_primrec`, and Scott's axioms `incl_refl`/`incl_trans`/`topIdx_spec`/`meetIdx_spec`. The
literal existential axioms are re-derived as theorems `axiom_i`/`axiom_ii`/`axiom_iii`
(`⟨topIdx,topIdx_spec⟩`)/`axiom_iv` (`⟨meetIdx n m, meetIdx_spec h⟩`).

**(⇐) the hint system.** `toNbhd n := {m ∣ INCL m n}` (`Sₙ`). Crux **`toNbhd_subset_iff : Sₙ⊆Sₖ ↔
INCL n k`** (→ `n∈Sₙ` by reflexivity (i); ← transitivity (ii)). **`toSystem`** (`mem Y:=∃n,Y=Sₙ`,
master `Δ=Set.univ=S_{topIdx}` by `toNbhd_top`; `inter_mem` supplies `meetIdx n m` and uses (iv)
through **`toNbhd_inter_eq_iff : Sₙ∩Sₘ=Sₖ ↔ MEET n m k`**). **`toPresentation`**: rel 7.1(i) decided
by `meet_dec` via `toNbhd_inter_eq_iff`, rel 7.1(ii) by `cons_dec` via
**`toNbhd_subset_inter_iff : Sₖ⊆Sₙ∩Sₘ ↔ INCL k n∧INCL k m`** + `exists_congr`, `inter:=meetIdx`,
`masterIdx:=topIdx`. ⟹ **`toSystem_isEffectivelyGiven`**.

**(⇒) from a presentation.** **`ofPresentation P : InclStructure`** with `INCL n m := P.X n ⊆ P.X m`,
`meetIdx:=P.inter`, `topIdx:=P.masterIdx`. refl/trans of `⊆`; `topIdx_spec` is `V.sub_master`;
`incl_dec:=P.incl_computable`, `cons_dec` from `P.cons_computable` (`subset_inter_iff` per `k`). The
**only** nontrivial decider is `MEET`: lemma **`meet_iff_interEq : (∀j, Xⱼ⊆Xₖ↔(Xⱼ⊆Xₙ∧Xⱼ⊆Xₘ)) ↔
(Xₙ∩Xₘ=Xₖ)`** (⇒ `MEET` at `j=k` gives `Xₖ⊆Xₙ∩Xₘ`, a consistency witness ⟹ `Xₙ∩Xₘ∈𝒟` by
`V.inter_mem` ⟹ `surj` enumerates it as `Xₚ`, and `MEET` at `j=p` gives `Xₙ∩Xₘ=Xₚ⊆Xₖ`; ⇐
`subset_inter_iff`), composed with `P.interEq_computable` for `meet_dec`. (`meet_iff_interEq`
itself audits `⊆{propext,Quot.sound}` despite using `surj`/`inter_mem`.)

**Round-trip A.** **`ofPresentation_toPresentation_INCL I n m : (ofPresentation I.toPresentation).INCL
n m ↔ I.INCL n m`** — `INCL↦𝒟↦INCL` recovers `INCL` exactly (it is defeq `I.toNbhd n ⊆ I.toNbhd m`,
then `toNbhd_subset_iff`).

**Round-trip B (the headline "essentially any effectively given system?" — YES).**
**`reconstruct_isomorphic P : toSystem (ofPresentation P) ≅ᴰ V`**, where
`reconstruct P := (ofPresentation P).toSystem`. Built powerIso-style (cf. `Exercise120.lean`) from the
mutually inverse, order-(co)preserving **`reconElem P x := {Sₙ ∣ x.mem Xₙ}`** and
**`reconElemInv P y := {Xₙ ∣ y.mem Sₙ}`**, packaged as **`reconIso : |V| ≃o |reconstruct P|`**; the
theorem returns `reconIso.symm`. Glue lemma **`ofPresentation_toNbhd_eq_iff : Sₙ=Sₘ ↔ Xₙ=Xₘ`** (from
`toNbhd_subset_iff` + `Set.Subset.antisymm_iff`). Subtlety in `reconElemInv.inter_mem`: V-side
consistency of `(n,m)` is recovered from the *S*-side meet index `p` (`y.sub (y.inter_mem …)` gives
`Sₙ∩Sₘ=Sₚ`, and `p∈Sₚ` ⟹ `Xₚ⊆Xₙ` and `Xₚ⊆Xₘ`, the needed witness for `V.inter_mem`); then `surj`
gives the V-index. (Exercise 7.18's *effective* isomorphism would upgrade this `≅ᴰ` to an effective
iso, tightening Scott's "essentially".)

**Gotchas.** (1) `RecDecidable₃`'s coding order is `(n,m,k) ↦ pair n (pair m k)`; `MEET` and `interEq`
share it, so `RecDecidable.of_iff (fun t => lemma … t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2)
hp` lines up directly (beta-defeq). (2) Orientation of `toNbhd_inter_eq_iff.mpr`: it yields
`Sₙ∩Sₘ=S_{meetIdx}` (good for `inter_mem`'s `∃k,X∩Y=Sₖ`), so `inter_spec` (which wants
`X(inter)=Xₙ∩Xₘ`) needs `.symm`. (3) `tauto`/`simp`-closing-`Set`-identities and `omega`-on-`↔`
silently pull `Classical.choice`; `iff_comm`/explicit `subset_inter_iff` keep it clean.

**Axiom audit.** `toSystem`, `toPresentation`, `ofPresentation`, `reconElem`, `reconElemInv`,
`toSystem_isEffectivelyGiven`, `ofPresentation_toPresentation_INCL`, `reconstruct_isomorphic`,
`meet_iff_interEq` — **all** `⊆{propext,Quot.sound}`. `lake build Domain` green; zero `sorry`; wired
into `Domain.lean` after `Proposition712`.

---

## Checkpoint 2026-06-27 (latest) — **Exercise 7.14 COMPLETE / Pass** (`Exercise714.lean`, green, wired, audited, **fully choice-free**)

The two halves of the exercise: (1) the recursion-theory facts after Definition 7.2 about primitive
recursive functions witnessing r.e.-ness, and (2) every computable element as a *decreasing* union of
finite (principal) elements. **All four headline declarations audit `⊆{propext,Quot.sound}`** — Half 2
included (better than the plan anticipated). Wired into `Domain.lean` after `Exercise713`.

**Half 1 — "a non-empty set is r.e. iff it is the range of a primitive recursive function."** Stated
against the project's choice-free r.e. model `REPred p := ∃q, RecDecidable q ∧ ∀n, p n↔∃i,q⟨i,n⟩`:
- **`repred_range_primrec`** (⇐): the range `fun n => ∃i, r i=n` of a primrec `r` is r.e. — the
  relation `q t := r t.1 = t.2` is recursively decidable by `RecDecidable.natEq (hr.comp .left) .right`,
  and `∃i, r i=n` is its projection (defeq after `unpair_pair`).
- **`repred_exists_primrec_range`** (⇒): a *non-empty* `REPred p` with witness `a` (`p a`) is the
  range of the primrec **`r w := selectFn (isOne (qc w)) w.unpair.2 a`** (`qc` = the `{0,1}` decider
  of the underlying `q`, normalised by `isOne` so it is exactly `{0,1}`-valued). Key lemma
  `hrw_mem : ∀w, p (r w)` — on a code `w=⟨i,n⟩` with `qc w=1` it returns `n` (and `q w`⟹`p n` via
  `hqe`+`pair_unpair`), otherwise it returns the fall-back `a∈p`. The **fall-back is exactly why
  non-emptiness is required** (an empty r.e. set is not a range). Primrec via `primrec_selectFn`/
  `primrec_isOne`/`Nat.Primrec.const`.
- **`repred₂_exists_primrec_enum`** (the map form `f={(X_{s(i)},Y_{r(i)})}`): a non-empty `REPred₂ p`
  is enumerated by a *pair* of primrec functions, `p n m ↔ ∃i, s i=n ∧ r i=m`, by applying the ⇒
  direction to the `Nat.pair`-coded relation and splitting the range fn `pf` into `s i:=(pf i).1`,
  `r i:=(pf i).2` (round-trips by `pair_unpair`/`unpair_pair`).

**Half 2 — `computableElement_eq_decreasing_iUnion_principal`.** For a computable element `y` of an
effectively given `W` (`IsComputableElement Q y`, i.e. `{m∣Yₘ∈y}` r.e.), produces `t:ℕ→ℕ` with
`Nat.Primrec t`, **decreasing** `Q.X(t(i+1))⊆Q.X(t i)`, and the union law
`y.mem Z ↔ ∃i, (W.principal (Q.mem_X (t i))).mem Z` (Scott's `y=⋃{↑Y_{t(i)}}`, Factoid 1.7b form).
Construction: the index set is non-empty because every filter contains `Δ` (`y.master_mem` +
`Q.surj W.master_mem` ⟹ witness `m₀`), so Half 1 lists it as the range of primrec `r₀`. To force
decrease, take running intersections **`tFun Q r₀`** (`def` via `Nat.rec`: `t 0=r₀0`,
`t(i+1)=Q.inter (t i) (r₀(i+1))`), which is primrec by genuine **`Nat.Primrec.prec`** with a
counter-dependent step (`primrec_tFun`, mirroring `RecDecidable.bForall`'s `prec`+`simp;rfl` pattern;
the step `g` is `Q.inter_primrec.comp (proj_IH.pair (r₀∘succ∘proj_y))`). Each `Yₜ₍ᵢ₎` is the meet of
`Yᵣ₀₍₀₎..Yᵣ₀₍ᵢ₎` so (a) stays in `y` (`ht_mem`, by `y.inter_mem` + `Q.inter_spec`, the consistency
witness `hcons` being the meet itself via `y.sub (y.inter_mem ..)` + `Q.surj`), (b) decreases
(`ht_dec` from `ht_eq`+`Set.inter_subset_left`), (c) is cofinal `Q.X(t i)⊆Q.X(r₀ i)` (`ht_sub_r`).
Union (→): `Z∈y` ⟹ `Q.surj`/`r₀`-spec give `i` with `Q.X(r₀ i)=Z`, and `ht_sub_r i` ⟹ `Q.X(t i)⊆Z`;
(←) `y.up_mem (ht_mem i)`.

**Gotchas.** (1) Lambda witnesses `⟨i, by …⟩` for `∃i, s i=n` leave a **beta-redex**
`(fun i => (pf i).unpair.1) i = n`; `rw` won't fire — insert `show (pf i).unpair.1 = n` (goal) /
`change … at hs` (hyp) to beta-reduce first. Same for `selectFn`'s enumerator: `show selectFn … = n`
before `rw [hqc1, selectFn_one, unpair_pair_snd]`. (2) `Q.inter_spec` needs `∃k, Xₖ⊆Xₙ∩Xₘ`; supply it
from the meet being in `y` (`hk.subset` of `Q.surj (y.sub (y.inter_mem ..))`). (3) `tFun_zero`/
`tFun_succ` hold by `rfl` because `tFun` is a thin wrapper over `Nat.rec` (not `brecOn`).

**Axiom audit.** `repred_range_primrec`, `repred_exists_primrec_range`, `repred₂_exists_primrec_enum`,
`computableElement_eq_decreasing_iUnion_principal` — **all** `⊆{propext,Quot.sound}`. `lake build
Domain` green; zero `sorry`; wired into `Domain.lean` after `Exercise713`.

---

## 2026-06-28 — Exercise 7.15 COMPLETE (`⊗`, `⊕`, `D`<sup>∞</sup> effectively given) — `Exercise715.lean`

`lake build Domain` green, zero `sorry`, wired into `Domain.lean` after `Exercise714`. All three
remaining 7.4-style constructs are now effectively given.

**Scott's *bare* Definition 7.1 for `⊗`/`⊕`.** The smash/coalesced bottom-collapse makes a
**primitive-recursive `inter` function provably impossible** (a consistent `(a,b)` may need to detect
that `b` is *secretly* the master, i.e. decide `Xb=Δ₀`?, which is r.decidable but not primrec). So the
file introduces **`ScottPresentation`** = `ComputablePresentation` minus the `inter`/`masterIdx` data
fields (Scott's literal Def 7.1: just enumeration `X` + relations (i),(ii) recursively decidable), with
`IsEffectivelyGivenS`/`IsComputableMapS`. Results:
- **`smash_isEffectivelyGivenS`** (`smashEnum`/`smashPresentation`): (i),(ii) reduce to the components'
  deciders + properness tests; the *only* classical input is the enumeration `smashEnum` (branches on
  the set-equality properness test).
- **`osum_isEffectivelyGivenS`**: `osum : NeighborhoodSystem (Option (α⊕β))` (coalesced sum over the
  separated-sum machinery), `osumEnum`/`osumPresentation`; (i) reduces to `sumPresentation.interEq` via
  a primrec reindex `r`, (ii) by direct case analysis. Same choice localisation as smash.

**`D`<sup>∞</sup> `= iterSys V` (Ex 3.16) — full `ComputablePresentation`, FULLY CHOICE-FREE
`⊆{propext,Quot.sound}` (data *and* proofs).** It is *uniform* (every cylinder is a genuine member, no
deletion), so a primrec `inter` exists. **`iterSys_isEffectivelyGiven`** via **`iterPresentation P`**:
- **Coding.** A code `t` codes a finite fiber-index list (`Recursive.decodeList`); fiber `j` of the
  enumerated nbhd is `P.X (iterIdx P t j)`, where **`iterIdx P t j := nthCode t j P.masterIdx`** reads
  the `j`-th entry, defaulting to `masterIdx` (so all but finitely many fibers are `Δ`).
  `fiber (iterEnum P t) j = P.X (iterIdx P t j)` is **`rfl`** (key simp lemma `fiber_iterEnum`).
- **Relations (i),(ii)** reduce to **bounded coordinate checks** over `j < n+m(+k)`:
  `iterEnum_inter_eq_iff` / `iterEnum_cons_iff` (beyond the bound every fiber is `Δ`, handled by
  `iterIdx_ge`), fed to **`RecDecidable.bForall`** after reindexing into `P.interEq_computable` /
  `P.cons_computable` (the per-coordinate decider; reindex built from `primrec_nthCode`).
- **`inter` = `iterInter P n m`** tabulates `P.inter` coordinate-wise: `tabCode (interG P) ⟨n+m,⟨n,m⟩⟩
  (n+m)` (`interG P s = P.inter (iterIdx (s.2.1) s.1) (iterIdx (s.2.2) s.1)`). `tabCode_nth_lt`/`_ge`
  give `iterInter_idx_lt`/`_ge`; `inter_spec` via `P.inter_spec` at each consistent coordinate.
- **`masterIdx := 0`** (empty list ⟹ all-`Δ` ⟹ `iterSys` master). **`surj`** via **`exists_list_fiber`**
  (induction on `N` building `[idx of fiber 0,…,fiber N-1]`, `P.surj` per coordinate, choice-free).
- **Combinator `projN_isComputable`** — the coordinate projections `projN n` (Ex 3.16; `head=projN 0`)
  are `IsComputableMap (iterPresentation P) P (projN V n)`: relation `W (projN n) X ↔
  fiber W n ⊆ X ↔ X_{iterIdx t n} ⊆ X_b`, a slice of `incl_computable` (mirrors `proj₀_isComputable`).

**New choice-free infra in `Recursive.lean`** (all `⊆{propext,Quot.sound}`):
- **`nthCode c i d`** (i-th entry of list-code `c`, default `d`): `nthCode_eq` (= `(decodeList c).getD i d`)
  via `foldCode`/`nthCode_foldl`; `primrec_nthCode`.
- **`tabCode g a B`** (tabulate `[g⟨0,p⟩…g⟨B-1,p⟩]` for `a=⟨B,p⟩`) via genuine **`Nat.Primrec.prec`**
  step `tabStep`: `decodeList_tabCode`, `tabCode_nth_lt`/`tabCode_nth_ge`, `primrec_tabCode`.
- **⚠️ `Classical.choice` gotcha & fix.** Mathlib's `List.getD_eq_getElem`, `List.getD_eq_default`,
  `List.getD_append(_right)` are **`grind`-proved ⟹ pull `Classical.choice`**. They silently tainted
  `tabCode_nth_*` and the whole `D`<sup>∞</sup> presentation. **Fixed by re-proving the slice by
  structural induction** (only the clean `getD_nil`/`getD_cons_zero`/`getD_cons_succ`/`getElem_map`/
  `getElem_range`): `getD_eq_default_cf`, `getD_append_cf`, `getD_append_right_cf`, `getD_map_range_cf`,
  `getD_eq_getElem_cf`. Audit `nthCode_eq`/`decodeList_encodeList` were already clean; after the swap so
  are `tabCode_nth_*`, `iterPresentation`, `iterSys_isEffectivelyGiven`, `projN_isComputable`.

**Remaining for 7.15:** `⊗`/`⊕` combinators (smash strict-pair; `in`/`out` for coalesced `⊕`) — the
`D`<sup>∞</sup> combinator (`projN`) is done. These would use `IsComputableMapS` (the bare-presentation
analogue of `IsComputableMap`).

### Checkpoint 2026-06-28 — Exercise 7.15 combinators COMPLETE (full Theorem-7.4 parity)

`Exercise715.lean` green, wired, zero `sorry`. Closed the combinator gap flagged in the line above.

- **Coalesced `⊕` (mirrors `+`):** `osumInMap₀`/`osumInMap₁` (injections), `osumOutMap₀`/`osumOutMap₁`
  (projections via `leftPart`/`rightPart`), `osumMap` (`f⊕g`) — all `*_isComputable` via
  `IsComputableMapS`. `osumMap`'s `rel` branches: codomain master (collapse) ∨ proper `inj₀`-pair via
  `f.rel` ∨ proper `inj₁`-pair via `g.rel`; computability is a `RecDecidable` tag/properness skeleton
  `∨`-glued with `f`/`g`'s r.e. relations (`Hf`/`Hg`). New helper lemmas: `osum_eq_master_of_inj₀/₁master`,
  `osum_mem_subset_inj₀/₁`. (`inter_right`'s master branch wants `Set.inter_eq_self_of_subset_right` —
  `Set.inter_eq_right.mpr` mis-orients against `osum`'s `sumMaster` vs `.master`.)
- **Smash `⊗` (mirrors `×`):** `smashProj₀`/`smashProj₁` (projections; same `Sum.inl⁻¹'W⊆X'` relation as the
  product `proj`, valid since every smash member is a `prodNbhd`; computable via `smashEnum_eq_eff` +
  `incl_computable`), `smashPaired` (`⟨a,b⟩⊗`, strict pairing — proper image factors else master),
  `smashMap` (`f⊗g`). `smashPaired_isComputable` needs **no** effective-index bridge: the proper branch
  reads `smashEnum`'s *raw* factors, so it's `¬proper(m) ∨ (proper(m) ∧ a.rel(n,m₀) ∧ b.rel(n,m₁))`.
- **`D`<sup>∞</sup>:** `projN` (`head=projN 0`) — already done.
- **Axiom audit:** `projN_isComputable ⊆ {propext, Quot.sound}` (choice-free). The five `⊕` and three `⊗`
  combinators are `{propext, Classical.choice, Quot.sound}` — `Classical.choice` is Prop-level only,
  inherited from the classical `osumEnum`/`smashEnum` properness branch (the *data* — systems and
  presentations — stays choice-free; this is the documented `⊗`/`⊕` posture).

### Checkpoint 2026-06-28 — Exercise 7.16 COMPLETE (`curry` is a *recursive* set)

`Exercise716.lean` green, wired into `Domain.lean`, zero `sorry`, **fully choice-free
`⊆{propext,Quot.sound}` (data and proofs)**. Completes the proof of Theorem 7.5 by writing `curry` out
as a neighbourhood relation and settling Scott's question.

**Answer:** `curry` is a **recursive (recursively decidable) set**, not merely r.e. — exactly as Scott
shows for `eval`.

- **Reuse, not redefine.** The `curry` *combinator* already exists as `Table55.curryC V₀ V₁ V₂ =
  ofIso (curryIso V₀ V₁ V₂)` (Thm 2.7 on Thm 3.12's order-iso `curryIso`; faithfulness
  `curryC_toApproxMap`). `Exercise716.lean` imports `Table55` and reuses these. (Initial draft had
  duplicated `curryIso`/`curryComb` — caught by a whole-project name clash with `Table55`; removed.)
- **(1) `curry` as a relation between neighbourhoods — `curryComb_rel`:**
  `G curryC H ↔ mem G ∧ mem H ∧ ∀ g∈G, curry g∈H`. Key new lemma `toApproxMap_principal_mem`: the
  *least map* `toApproxMap ↑G` of a function-space neighbourhood `G` lies in `G`. Forward direction
  feeds that least map through `curryEquiv`'s monotonicity + up-closure of `H`; backward applies the
  ∀-hypothesis to it. This reduces the `∀ g∈G` to a single check on the least map.
- **(2) Recursive decidability — `curryComb_rel_recDecidable` / `curryComb_isComputable`:** relative
  to the Theorem-7.5 function-space presentations `PA=(𝒟₀×𝒟₁→𝒟₂)`, `PB=(𝒟₀→(𝒟₁→𝒟₂))`, inner
  `Pc=(𝒟₁→𝒟₂)` (all via `funPresentation`/`funConsChar`), the relation on codes unfolds to
  `X_PA n curryC X_PB m ↔ gNb m=1 → ∀ e∈⟦m⟧, gNc e₂=1 → ∀ e'∈⟦e₂⟧, X_PA n ⊆ X_PA (curryStepCode e₁ e')`.
  - Each `X_PA n ⊆ X_PA (curryStepCode …)` is product-function-space **inclusion** — recursively
    *decidable* via `PA.incl_computable` (this is the crux: decidable, not just r.e.).
  - `curryStepCode a e'` codes the one-entry step `[⟨X_a, Y_{e'₁}⟩, Z_{e'₂}]`, an `Xenum`-singleton
    over `prodPresentation P₀ P₁` (`Xenum_singleton` + `prodPresentation_X`); primrec via
    `primrec_curryStepCode`.
  - The two nested `∀`s are **bounded** over `decodeList` (`RecDecidable₂.bForallList`); the `gNb`/`gNc`
    consistency guards via `RecDecidable.natEq` + `Decidable.imp_iff_not_or`.
  - Reduction lemmas (from `Theorem75.lean`): `mem_Xenum_iff_map`, `curry_rel_Xenum_iff`,
    `Xenum_singleton`. Concludes `IsComputableMap PA PB (curryC …)` via `RecDecidable₂.re`.
- **Axiom audit:** `curryComb_rel`, `curryComb_rel_recDecidable`, `curryComb_isComputable` all
  `⊆ {propext, Quot.sound}` (choice-free — no `Classical.choice`).

---

## Checkpoint — 2026-06-28 — Exercise 7.17 **Part 1 COMPLETE** (all Example 6.1 combinators of `D^§`)

New module `Domain/Neighborhood/Exercise717.lean` (ns `Domain.Neighborhood.Proposition77`, green,
wired into `Domain.lean`, zero `sorry`). This is **clause 1 of Exercise 7.17** — "complete 7.7
including *all* the combinators of 6.1". (Scott's text prints "6.2"; the construct is Example **6.1**,
and 7.7 itself says "all the combinators of Example 6.1", so we read it as 6.1.) `Combinators77.lean`
had done the *selection* `inSharp`(`λx.x^§`) + `proj₀`; this finishes the set.

**What landed (continuing the `Proposition77` namespace, reusing `Vsharp`/`dsharpPresentation`):**
- **`proj1Map`** — pair-part *second* projection `D^§ → D^§`, the exact mirror of `Combinators77`'s
  `proj0Map` with the second `embPair` component: `W proj₁ Z ↔ Z=Γ ∨ ∃P Q, W=1·P∪2·Q ∧ Q⊆Z`.
  Faithfulness **`proj1_toElementMap_pairSharp : proj₁(⟨x,y⟩^§)=y`**. Computability
  **`proj1_isComputable`** via `proj1_rel_Vsharp_iff`: index rel `k=0 ∨ (m%2=0 ∧ m≠0 ∧
  V_{(m/2-1).unpair.2}⊆V_k)` — same shape as `proj0` but the **right** child (`.unpair.2`), so the
  primrec reindex uses `Nat.Primrec.right.comp …`. Disjunction of `natEq`/parity/`incl` deciders ⟹ `.re`.
- **`pairSharpMap`** — Scott's pairing constructor `pair : D^§ × D^§ → D^§` as a **joint** map out of
  `prod (Dsharp D hD) (Dsharp D hD)` (so over `α⊕α`, using `Product.lean`'s `prodNbhd`/`prod`/`pair`).
  Relation `rel V W ↔ (prod).mem V ∧ MemS W ∧ ∃A B, MemS A ∧ MemS B ∧ V=prodNbhd A B ∧ embPair A B⊆W`.
  `master_rel` works because `embPair Γ Γ ⊆ Γ` (`embPair_subset_Gamma`). Faithfulness
  **`pairSharpMap_toElementMap : pairSharpMap.toElementMap (pair x y) = pairSharp D hD x y`** (the
  product element pairing maps to Example 6.1's `pairSharp`; forward via up-closure of `pairSharp`,
  backward splits `W=Γ` / `W=embPair P Q`). Computability **`pairSharp_isComputable`** via
  `pairSharp_rel_Vsharp_iff`: on indices the relation collapses (by `prodNbhd_injective` +
  **`Vsharp_even`**: `embPair (V_{p t})(V_{q t}) = V_{2·t+2}`) to `V_{2·t+2} ⊆ V_k` — a slice of
  `dsharpPresentation.incl_computable` reindexed by primrec `s ↦ ⟨2·s.unpair.1+2, s.unpair.2⟩`, hence r.e.

With `inSharpMap`/`proj0Map` this is the **full** combinator set of the domain equation
`D^§ ≅ D + (D^§ × D^§)`: injections `in`,`pair` and pair-part projections `proj₀`,`proj₁`.

**Axiom audit (`#print axioms`):** `proj1Map`, `pairSharpMap`, and **both faithfulness theorems**
(`proj1_toElementMap_pairSharp`, `pairSharpMap_toElementMap`) are choice-free `⊆ {propext, Quot.sound}`.
The two `*_isComputable` proofs carry `Classical.choice` (Prop-level only — inherited from
`incl_computable` / `Set` reasoning over arbitrary `α`), exactly as in `Combinators77.lean`.

**Reusable patterns / gotchas:**
- For the joint pairing's index iff, `rw [pairSharpMap_rel, prodPresentation_X, Vsharp_even]` then the
  `∃A B, V=prodNbhd A B`-witness is pinned by `prodNbhd_injective`; the `(dsharpPresentation P hD).X k`
  vs `Vsharp D P k` mismatch is **defeq** (handled by `simp [dsharpPresentation_X]` / `rfl`).
- `obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq` eliminates the **later**-introduced pair `A B`
  (substituting them away), so refer to the **earlier** names (`A0 B0`) afterwards — this bit once
  (got "Unknown identifier `A`").

---

## Checkpoint 2026-06-28 — Exercise 7.17 **Part 2 DONE** (`Exercise717Part2.lean`); Ex 7.17 now **Pass**

`Exercise717Part2.lean` green, wired into `Domain.lean`, zero `sorry`, full `lake build Domain` green.
This completes **all of Exercise 7.17**.

**What it proves.** For `E` effectively given (presentation `Q`) with computable `u : D → E` and
`v : E×E → E`, the unique strict catamorphism `g : D^§ → E` (`g(in x)=u(x)`, `g(pair y z)=v(g y,g z)`)
is a computable map: `gMap_isComputable`.

**Construction.**
- **`GRel u v`** (inductive nbhd relation): `Γ ↦ Δ_E` / `0·X ↦ u.rel X` / `1·P∪2·Q ↦ ∃Z₁ Z₂,
  P g Z₁ ∧ Q g Z₂ ∧ ⟨Z₁,Z₂⟩ v Z`. No separate top-clause (`gRel_master = GRel.gamma rfl`).
- **`gMap`** : the `ApproximableMap` wrapping `GRel`; inversion lemmas `gRel_{gamma,embZero,embPair}_inv`
  (need `hD : ∀X,D.mem X→X.Nonempty` + `Classical`); faithfulness **`gMap_in`/`gMap_pair`** and
  **`gMap_strict`** (all choice-free `⊆{propext,Quot.sound}`).
- **Certificate evaluator** (computability): `gEval = gOf (gStep fe fU fV mIdx)`, a **fresh**
  course-of-values memo over `w = ⟨n, cert⟩` (NOT `dsharpStep`: the same sub-nbhd may fold to
  *different* outputs in different tree positions, so the certificate must mirror the derivation tree).
  `cert` decodes to `⟨out, wit, lcert, rcert⟩`; `gStep` branches on the `Vsharp` shape `n` (0 / 2a+1 /
  2a+2), the node case reading the two children's `⟨okBit,outIdx⟩` from the memo table via
  `listGet_rtbl`. `primrec_gStep` (primrec when `fe`/`fU`/`fV` are).
- **`Nat.pair` monotonicity** for the child-code `< w` measure: `pair_lt_pair_left`,
  `pair_le_pair_right`, `pair_lt_pair_of_lt_le` (in this file) + new **`le_pair_left`** in
  `Recursive.lean` (next to `le_pair_right`).
- **`gEval_sound`** (strong induction on `w`) / **`gEval_complete`** (strong induction on `n`,
  `maxHeartbeats 1000000` for the giant decoded-`cert` terms) ⟹
  `GRel(Vₙ)(Yₘ) ↔ ∃cert, gEval⟨n,cert⟩.ok=1 ∧ Y_{cert.out}=Yₘ`.
- **`gMap_isComputable`**: deciders `fe`/`fU`/`fV` read off `Q.eq_computable` and the r.e. relations
  of `u`/`v` (with `prodPresentation_X` aligning `v`'s domain `⟨k1,k2⟩ ↦ prodNbhd(Y_{k1})(Y_{k2})`);
  then `RecDecidable.and`/`.re` for the certificate body, `REPred.proj` for `∃cert`, `REPred.of_iff`
  bridged by sound+complete.

**Axiom audit (`#print axioms`):** `gMap_in`, `gMap_pair`, `gMap_strict` are choice-free
`⊆{propext,Quot.sound}`; `gMap_isComputable` carries `Classical.choice` (Prop-level only — inherited
from the `GRel` inversion lemmas' `Set` reasoning over arbitrary `α`,`β`), exactly as Part 1's
`*_isComputable`.

**Reusable patterns / gotchas:**
- `gEval`-form memo lookup: wrap `listGet_rtbl` as **`listGet_rtbl_gEval`** so the result is
  syntactically `gEval …` (not `gOf (gStep …)`), or `gEval_out`/`hok` rewrites won't match.
- `set_option … in` must precede the **docstring**, not sit between docstring and `theorem`.
- `unpair_snd_snd_fst_le _` can't unify against a literal `Nat.pair`-tower bound — prove `certL ≤ ⟨…⟩`
  directly by chaining `le_pair_left`/`le_pair_right`.
- After `rw [hokL, hokR]` the `1*1*fV` collapse: use `simp only [Nat.one_mul]` (a fixed count of
  `Nat.one_mul` rewrites is brittle because `1*1` reduces reducibly).

**Next concrete target:** ~~Exercise 7.18~~ DONE (see below) — continue VII/VIII (Exercise 7.19 `D↦PD`
functor; Exercise 7.23 finish `PN`).

---

## Checkpoint 2026-06-28 — Exercise 7.18 DONE (effective isomorphism; `D∞ ≅ (D∞)∞` effective)

`Exercise718.lean` (ns `Domain.Neighborhood.Exercise718`) green, wired into `Domain.lean`, zero
`sorry`, **fully choice-free `⊆{propext,Quot.sound}` — data AND every Prop, including computability.**
Axiom audit confirmed for all of `iterSys_effectivelyIsomorphic_iterIter`, `iterSys_isomorphic_iterIter`,
`Fmap_isComputable`, `Gmap_isComputable`, `Gmap_comp_Fmap`, `Fmap_comp_Gmap`,
`EffectivelyIsomorphic.isomorphic`.

**Part 1 — "complete the sentence".** `EffectiveIso P Q` = a pair of mutually inverse approximable
maps `toMap:D→E`, `invMap:E→D`, **both `IsComputableMap`** (Def 7.2), with `invMap.comp toMap = I_D`
and `toMap.comp invMap = I_E`. `EffectivelyIsomorphic P Q := Nonempty (EffectiveIso P Q)`. Derived
`EffectiveIso.toDomainIso : |D| ≃o |E|` (elementwise maps inverse via `← toElementMap_comp` +
`left_inv`/`right_inv` + `toElementMap_idMap`; monotone via `toElementMap_mono`; `map_rel_iff'`
needs a `show e.toMap.toElementMap x ≤ … ` to bridge the just-built structure's coe — defeq but not
syntactic) ⟹ `EffectivelyIsomorphic.isomorphic : D ≅ᴰ E`.

**Part 2 — `D∞ ≅ (D∞)∞` effective.** `D∞ = iterSys V` (tokens `ℕ×α`), `(D∞)∞ = iterSys (iterSys V)`
(tokens `ℕ×(ℕ×α)`). Iso = index reindexing along `Nat.pair`/`unpair`: `x_{i,j} = x_{pair i j}`.
- **`fiber2 S i j := fiber (fiber S i) j`** (double-indexed fiber; `fiber2_master`, `fiber2_inter`,
  `fiber2_mono`, `mem_fiber2_of_mem`).
- **`Fmap`** `W F S ↔ mem ∧ mem ∧ ∀ i j, fiber W (pair i j) ⊆ fiber2 S i j`;
  **`Gmap`** `S G W ↔ mem ∧ mem ∧ ∀ k, fiber2 S (unpair k).1 (unpair k).2 ⊆ fiber W k`.
  Full `ApproximableMap` structure; `inter_right` uses the reindex witness for the consistency
  `Z ⊆ X∩Y` (iterSys is NOT closed under arbitrary binary ∩, so the witness is essential).
- **Reindex constructions** `reindexF W` (`fiber2 = fiber W (pair i j)`) / `reindexG S`
  (`fiber = fiber2 S (unpair k)`), with `reindexF_subset_iff`/`reindexG_subset_iff` (the workhorses
  for `inter_right` + the inverse laws) and membership `reindexF_mem`/`reindexG_mem`.
- **Inverse laws** `Gmap_comp_Fmap`/`Fmap_comp_Gmap` (`ApproximableMap.ext` on the `comp` rels; `⇐`
  supplies `reindexF W` / `reindexG S` as the `∃` witness; key step `pair_unpair`/`unpair_pair`).
- **`reindexG` cofinite-`Δ` bound is CHOICE-FREE:** the uniform inner max over `i < No` is built by
  a `Prop`-level induction **`exists_inner_bound`** (`obtain ⟨Mn,_⟩ := (hS.1 n).2` per step, `max M Mn`
  — no `Exists.choose`!), plus a local strict-monotone **`pair_lt_pair_of_lt`** (copied from
  `Proposition77` to dodge that heavy import) so `i<No ∧ j<M ⟹ pair i j < pair No M`, hence
  `k ≥ pair No M ⟹` inactive.
- **Computability `Fmap_isComputable`/`Gmap_isComputable` (recursively DECIDABLE, so `.re`):** over
  `iterPresentation P` / `iterPresentation (iterPresentation P)`. `fiber2_iterEnum_iter` reads the
  double fiber as `P.X (iterIdx P (iterIdx (iterᴾ) m i) j)`. The relations reduce
  (`Fmap_rel_enum_iff`/`Gmap_rel_enum_iff`) to BOUNDED `incl_computable`: anything past the coded
  fiber length is `Δ` (`iterIdx_ge`, and `(iterPresentation P).masterIdx = 0` by `rfl` ⟹ inner code
  `0` ⟹ `iterIdx P 0 j = masterIdx` ⟹ `Δ`), so `LHS ⊆ Δ` trivially. `G` = one `RecDecidable.bForall`
  over `k < n`; `F` = a **nested** `bForall` (`hp₂.bForall hbound₂` for `j < iterIdx (iterᴾ) m i`,
  then `.bForall hbound₁` for `i < m`). Index funcs are `primrec_nthCode.comp (… .pair …)` +
  `of_eq` to fold `iterIdx`/`nthCode`.
- **Packaging:** `iterIterEffectiveIso P : EffectiveIso (iterPresentation P)
  (iterPresentation (iterPresentation P))` ⟹ `iterSys_effectivelyIsomorphic_iterIter` + corollary
  `iterSys_isomorphic_iterIter : iterSys V ≅ᴰ iterSys (iterSys V)`.

**Gotchas worth keeping:** (1) `ComputablePresentation` has **no** `sub_master` field — use
`V.sub_master (P.mem_X _)`. (2) `iterSys` is not ∩-closed without a consistency witness; every
`inter_right`/`inter_mem` here threads a `reindex*` witness. (3) For the `≃o` `map_rel_iff'`, the
freshly-constructed structure's function coe is only *defeq* to `e.toMap.toElementMap` — open with
`show … ≤ …` before `rw`.

---

## Checkpoint 2026-06-28 — Exercise 7.19 DONE (`D ↦ ℙD` is a functor; `Exercise719.lean`)

`Exercise719.lean` (ns `Domain.Neighborhood`) green, wired into `Domain.lean`, zero `sorry`, full
`lake build Domain` green.

**What it proves.** For `f : D → E` (approximable), the functorial action **`PFmap f : ℙD → ℙE`** on
the Smyth power domain (Def 7.9 / Prop 7.10), proved approximable, functorial, and computability-
preserving.

**Construction & key lemmas.**
- **`PFmap f`** : `ApproximableMap V.PowerDomain W.PowerDomain` with the *representation-independent*
  relation `rel A B := V.PDmem A ∧ W.PDmem B ∧ ∀ X ∈ A, ∃ Y ∈ B, f.rel X Y`. `@[simp] PFmap_rel`.
  - `master_rel`: from `f.master_rel` + `f.mono` (any `X ⊆ Δ_D` maps to `Δ_E`).
  - `inter_right`: witness `Y ∩ Y'` lands in `B ∩ B'` because the power domain is **downward closed**
    (new `NeighborhoodSystem.PDmem_down`); plus `f.inter_right`.
  - `mono`: trivial (body only quantifies over set membership; `B ⊆ B'`).
  - helpers `PDmem_mem` (members of a `ℙ𝒟`-nbhd are `𝒟`-nbhds), `PDmem_down` (downward closure).
- **Scott's display** `PFmap_rel_fin`: `(ℙf).rel (⋃_{X∈L₁}↓X)(⋃_{Y∈L₂}↓Y) ↔ ∀ X∈L₁, ∃ Y∈L₂, X f Y`
  (the `∀i<n∃j<m. Xᵢ f Yⱼ` of the exercise) — equiv by `mono` both ways + generators are members.
- **Functor laws**: `PFmap_idMap` (`ℙ I_D = I_{ℙD}`; body `∀X∈A,∃Y∈B,X⊆Y` ↔ `A⊆B` by `PDmem_down`),
  `PFmap_comp` (`ℙ(g∘f)=ℙg∘ℙf`). Fwd of `comp` builds the middle `ℙE`-nbhd `⋃_{Y∈M}↓Y` from a list
  `M` gathered by **choice-free** list recursion `comp_witness` (`obtain` per `cons`, Prop goal).
- **Computability (Scott's "if f computable, is ℙf?")**: **yes**. `PFmap_rel_Ypd_iff` reduces the
  relation on Prop-7.10 codes (`Y_c = ⋃_{a∈dl c}↓Xₐ`) to `∀ a∈dl c, ∃ b∈dl d, Xₐ f Y_b`. r.e. via the
  new **`bExists_decodeList_re`** (bounded `∃` over `decodeList` preserves r.e.: decidable
  list-membership `b ∈ decodeList d` ∧ r.e. body `R a b`, then `REPred.proj`) followed by
  `REPred.forall_mem_decodeList₂` (param bounded `∀`) + a `Nat.pair`-swap reindex. `PFmap_isComputable`
  packages it as `IsComputableMap (PDPresentation …)(PDPresentation …)(PFmap f)` (defeq: `PDPresentation.X = Ypd`).
- Discussion in docstring: `λf.ℙf` exists in spirit (monotone/continuous in `f`); `ℙf({x,y})={f x,f x'}`.

**Axiom audit (`#print axioms`):** ALL decls are `⊆ {propext, Classical.choice, Quot.sound}`. The
`Classical.choice` is **Prop-level and entirely inherited** from `ℙ𝒟`'s ∩-closure (Prop 7.10
`PDmem_upSet_inter`, the `by_cases V.mem (X∩Y)`); the new content of this file adds no further choice
(the `Recursive.lean` r.e. layer is choice-free, so `PFmap_isComputable*` add only `hf`'s axioms).

**Gotchas:** (1) `V.PowerDomain` itself carries `Classical.choice` (Prop 7.10), so anything over it
inherits it — don't claim choice-free for power-domain maps. (2) `REPred.forall_mem_decodeList₂` takes
`hp : REPred₂ p`; call it as `REPred.forall_mem_decodeList₂ hInner` (not dot notation — head is
`REPred₂`). (3) `mem_Ypd`/`mem_PDunion` destructure straight to `⟨a, ha, hmem, hsub⟩` (the `upSet`
membership is defeq to the `And`).

**Next concrete target:** Exercise 7.20 (`union : ℙ(ℙD)→ℙD` combinator; is it computable?
`ℙ(ℙD) ≅ ℙD`?), Exercise 7.21, or Exercise 7.23 (finish `PN`).

---

## Checkpoint — Sunday Jun 28, 2026 — Exercise 7.20 DONE (`union : ℙ(ℙD) → ℙD`)

`Exercise720.lean` green, wired into `Domain.lean`, zero `sorry`; full `lake build Domain` green.

**What it is:** the **multiplication `μ : ℙℙD → ℙD`** of the Smyth power-domain monad — the
*flattening* combinator. Builds directly on Definition 7.9 / Proposition 7.10 (`PowerDomain`, `Ypd`,
`PDPresentation`) and Exercise 7.19's lemmas (`PDmem_mem`, `PDmem_down`).

- **`unionMap (V) : ApproximableMap V.PowerDomain.PowerDomain V.PowerDomain`**, rep-independent
  relation `rel A B := ℙℙD.PDmem A ∧ ℙD.PDmem B ∧ ∀ S ∈ A, ∀ X ∈ S, ∃ Y ∈ B, X ⊆ Y`. Approximable:
  `master_rel` sends every `X` below `↓Δ` (witness `Δ`, `sub_master`); `inter_right` narrows the
  witness to `Y ∩ Y'` — a `D`-nbhd because `X ⊆ Y∩Y'` witnesses consistency (`V.inter_mem`), landing
  in `B ∩ B'` by `PDmem_down` (the Ex-7.19 downward-closure lemma); `mono` immediate.
- **Scott's display** `unionMap_rel_fin`: for nested lists `LS : List (List 𝒟)`, `LY : List 𝒟`,
  `union.rel (⋃_{l∈LS} ↓_{ℙD}(⋃_{X∈l}↓X)) (⋃_{Y∈LY}↓Y) ↔ ∀ l∈LS, ∀ X∈l, ∃ Y∈LY, X ⊆ Y` — exactly
  `∀ i<n ∀ j<m_i ∃ k<q. X_{ij} ⊆ Y_k`. (Two readings coincide by `PDmem_down` at *both* levels.)
- **Computable? YES — recursively decidable.** `unionMap_rel_Ypd_iff` reduces the relation on
  `ℙℙ𝒟`/`ℙ𝒟` codes to the nested bounded quantifier `∀ c∈dl n, ∀ a∈dl c, ∃ b∈dl m, Xₐ ⊆ X_b`, which
  is `RecDecidable₂` via `(V.subCode_computable P).bForallList` (one extra `bForallList` on top of
  Prop 7.10's `subCode_computable`), hence r.e. (`.re`). `unionMap_isComputable` packages it as
  `IsComputableMap (V.PowerDomain.PDPresentation (V.PDPresentation P consV …) (fun _=>1) …)
  (V.PDPresentation P consV …) (unionMap V)`. The **inner `cons` for `ℙ𝒟`** (needed to build the
  `ℙℙ𝒟` presentation) is the **constant `fun _ => 1`**, correct because the empty union (`code 0`,
  `Y₀ = ∅`) is below every `ℙ𝒟`-nbhd (witness `k = 0`, `Ypd_zero`).
- **Discussion answers (docstring):** `union({{x},{y,z}}) = {x,y,z}` (set-theoretic union of the
  member-sets); `ℙℙD ≇ ℙD` in general (`ℙ` not idempotent — `union` collapses `{{x},{y}}` and
  `{{x,y}}` to the same `{x,y}`, so it is not injective on elements).

**Axiom audit:** all four decls `⊆ {propext, Classical.choice, Quot.sound}`. `Classical.choice` is
Prop-level and **entirely inherited** from the power domain (`PowerDomain`/`PowerDomain.PowerDomain`
via Prop 7.10 `PDmem_upSet_inter`'s `by_cases`); this file adds **no** further choice, exactly as in
Exercise 7.19.

**Gotchas:** (1) the `ℙℙD` presentation is a *double* `PDPresentation`; supply the inner `ℙ𝒟`
consistency decider explicitly as `(fun _ => 1, Nat.Primrec.const 1, hspec)` with `hspec` proved via
`Ypd_zero` + `empty_subset` (`code 0` always below). (2) `unionMap_rel_Ypd_iff` is stated for a
*generic* `Q : ComputablePresentation V.PowerDomain` with `hQ : ∀ c, Q.X c = V.Ypd P c`, so the
final `IsComputableMap` passes `hQ := fun _ => rfl` (the `PDPresentation.X = Ypd` field is defeq).
(3) for the `PDmem A` obligation in `unionMap_rel_fin`, build the witness list as `LS.map (fun l =>
⋃ X∈l, ↓X)` and prove the union equality with `simp only [Set.mem_iUnion, List.mem_map, exists_prop]`
(a bare `rw [mem_PDunion]` mis-unifies on the nested `upSet (⋃…)` body).

**Next concrete target:** Exercise 7.20 is superseded by 7.21 below. Remaining §7 exercises:
Exercise 7.22 (algebraists' least-fixed-point domain over `{0,1}*`), Exercise 7.23 (finish `PN` of
Ex 7.8: `fun`/`graph` computable), Exercise 7.24 (LUCID stream operators).

---

## Checkpoint — Sunday Jun 28, 2026 — Exercise 7.21 DONE (`ℙ(D→E) → (ℙD → ℙE)` and friends)

`Exercise721.lean` (ns `Domain.Neighborhood`) green, wired into `Domain.lean`, zero `sorry`; full
`lake build Domain` green.

**What it is.** Scott's 7.21 is four open-ended questions. We formalize the **headline (Q1)** in full
and answer Q2–Q4 in the docstring.

**Q1 — `papply : ℙ(D→E) → (ℙD → ℙE)` (yes, non-trivial).** The **Smyth power-domain lift of
evaluation** (Thm 3.11 `eval : (D→E) × D → E`):
- **`papplyEval V W : ApproximableMap₂ (funSpace V W).PowerDomain V.PowerDomain W.PowerDomain`**,
  `rel Φ A B := ℙfun Φ ∧ ℙD A ∧ ℙE B ∧ ∀ G∈Φ, ∀ X∈A, ∃ Y∈B, (eval V W).rel G X Y`. Two-variable
  analogue of Ex 7.19's `ℙf` (one level: `∀X∈A,∃Y∈B, X f Y`). Approximable: `master_rel` (witness
  `Δ_E`, members extracted by `simp [PowerDomain_master, mem_upSet]`), `inter_right` (witness `Y∩Y'`
  via `eval.inter_right` + Ex-7.19 downward closure `PDmem_down`), `mono`.
- **`papplyB = ofMap₂ papplyEval`** (map out of `prod ℙfun ℙD → ℙE`), then **`papply = curry papplyB`**
  (Thm 3.12 `curry`) has the *exact* type `ApproximableMap (funSpace V W).PowerDomain
  (funSpace V.PowerDomain W.PowerDomain)` = `ℙ(D→E) → (ℙD→ℙE)`.
- **Non-trivial:** `papplyEval_step_witness` — for any `X₀∈D, Y₀∈E`,
  `(papplyEval).rel (↓[X₀,Y₀]) (↓X₀) (↓Y₀)` (the functions sending `X₀↦Y₀`, applied to `X₀`, give `Y₀`;
  uses `step_mem`, `mem_step`, `f.mono`).
- **Computable when `eval` is** (`papplyEval_isComputable`): `papplyEval_rel_Ypd_iff` reduces the
  relation on Prop-7.10 codes to `∀g∈dl Φc, ∀x∈dl Ac, ∃y∈dl Bc, eval(Pf.X g)(P.X x)(Q.X y)`, r.e. by
  the **new choice-free helper `re_forallG_forallX_existsY`** (`⊆{propext,Quot.sound}`): three nested
  bounded quantifiers over an r.e. body, built by `bExists_decodeList_re` (Ex 7.19) then
  `REPred.forall_mem_decodeList₂` twice, with four primrec re-indexings (`hm1`..`hm4`, each closed by
  `REPred.of_iff … ; simp only [unpair_pair_fst, unpair_pair_snd]`). Base predicate `heval` (eval
  r.e. on codes) **must be passed explicitly with `(R := …)`** — HOU can't infer it; `heval` itself is
  Thm 7.5's `evalMap_isComputable` transported through `funPresentation` to the ternary relation.

**Q2–Q4 (docstring discussion).** Q2: no isos among `D→ℙE`, `ℙ(D×E)`, `ℙD×ℙE` in general (Smyth `ℙ`
doesn't distribute over `×`; `⟨ℙp₀,ℙp₁⟩ : ℙ(D×E)→ℙD×ℙE` forgets correlation — `{(d₁,e₁),(d₂,e₂)}` and
`{(d₁,e₂),(d₂,e₁)}` share marginals). Q3: yes, relational composition `ℙ(D×E)×ℙ(E×F)→ℙ(D×F)` (Smyth
lift; middle witness gathered as Ex-7.19 `comp_witness`) — same recipe as `papply`. Q4: `ℙN⊴PN`
(finitely-generated/computable core; `PN` = ideal completion of Ex 7.8), not isomorphic.

**Gotchas worth keeping:** (1) `Y ∈ V.upSet X` is *defeq* to `V.mem Y ∧ Y ⊆ X` — `obtain ⟨_,_⟩ := h`
works directly; `mem_upSet.mp` does NOT resolve under `open NeighborhoodSystem` (it's `Exercise120`'s,
`V`-explicit). (2) `re_forallG_forallX_existsY heval` fails by higher-order unification — supply
`(R := fun g x y => …)`. (3) `REPred₂ X` is defeq to `REPred (fun t => X t.1 t.2)`; declare the
`hR2`/`hF`/`hG` steps with `show REPred …` then `REPred.of_iff`, and read `hE`/`hFfull`/`hGfull` back
as plain `REPred` so `.comp` (which is `REPred.comp`, not `REPred₂.comp`) resolves.

**Axiom audit (`#print axioms`):** `re_forallG_forallX_existsY ⊆ {propext, Quot.sound}` (fully
choice-free); `papplyEval`, `papply`, `papplyEval_step_witness`, `papplyEval_rel_Ypd_iff`,
`papplyEval_isComputable` all `= {propext, Classical.choice, Quot.sound}` — choice Prop-level and
**inherited** from the power domain (Prop 7.10 `PDmem_upSet_inter`'s `by_cases`), none added, exactly
as Exercises 7.19/7.20.

---

## Checkpoint 2026-06-28 — Exercise 7.22 algebraic core DONE (`Exercise722.lean`)

`Exercise722.lean` (ns `Domain.Neighborhood.Exercise722`) green, wired into `Domain.lean`, zero
`sorry`. **Every headline decl is fully choice-free `⊆{propext,Quot.sound}`** (axiom audit confirmed
for `Ssys`, `Ssys_isPositive`, `InS.nonempty` (no axioms), `mulElem`, `mulElem_assoc`, `emb`,
`emb_mul`, `emb_injective`). Imports just `Basic` + `Mathlib.Data.Set.Insert`.

**Scope decision (read before "finishing" 7.22).** Scott's Exercise 7.22 has four parts; this file
mechanises the **algebraic core** and *discusses* the other two (in the docstring, NOT as `sorry`):

1. **Least-fixed-point family `S`** — DONE as the inductive predicate `InS : Set (List Bool) → Prop`
   with constructors `univ` (`Σ=Set.univ`), `singleton σ` (`{σ}`), `mul` (`concat X Y`), `inter`
   (`X∩Y` *with a non-emptiness hypothesis*). Tokens `Σ={0,1}* = List Bool`.
2. **Positive neighbourhood system** — DONE. `InS.nonempty` (induction: `Σ`/`{σ}` non-empty, `concat`
   preserves it, `inter` carries it) is exactly what makes the system positive. `Ssys` built by
   `NeighborhoodSystem.ofPositive InS Set.univ InS.univ (fun {X} _ => Set.subset_univ X) (pos)` where
   `pos X Y hX hY = ⟨(·.nonempty), InS.inter hX hY⟩`. `Ssys_isPositive` proved *directly* by `intro`
   (NOT via `ofPositive_isPositive _ _ _ _ _` — those `_`s can't be inferred from the bare goal
   `Ssys.IsPositive` because `Ssys` is an opaque `def`).
3. **Multiplication / semigroup** — DONE. `mulElem x y` (mem `Z := InS Z ∧ ∃X, x.mem X ∧ ∃Y, y.mem Y
   ∧ concat X Y ⊆ Z`) is a filter; `master_mem` uses `X=Y=Σ`; `inter_mem` uses witnesses `X₁∩X₂∈x`,
   `Y₁∩Y₂∈y` (filter closure) + `concat_mono` + positivity (`Z₁∩Z₂∈S` because the non-empty
   `concat(X₁∩X₂)(Y₁∩Y₂)` sits inside it). `mulElem_assoc` via `concat_assoc` (`rw [← concat_assoc]` /
   `rw [concat_assoc]`) + `concat_mono`.
4. **Embedding homomorphism** — DONE. `emb σ` (mem `X := InS X ∧ σ∈X`); `emb_mul : emb(σ++τ) =
   mulElem (emb σ)(emb τ)` (fwd witnesses `{σ},{τ}` via `concat_singleton`; bwd `append_mem_concat`);
   `emb_injective` (`emb σ = emb τ ⟹ emb τ.mem {σ} ⟹ τ=σ`).

**NOT mechanised (genuine gaps, documented honestly — left for a future session):**
- **"Effectively given"** (Definition 7.1). The hint: each `S`-member is a *regular event*, and the
  set algebra of regular events is decidable. An enumeration would Gödel-number the finite syntax of
  `S`-terms; Scott's relations (i) `Xₙ∩Xₘ=X_k` and (ii) consistency `∃k.X_k⊆Xₙ∩Xₘ` (≡ non-emptiness
  of `Xₙ∩Xₘ` **by positivity**) are decidable via DFA emptiness/equivalence. Mechanising that inside
  the project's bespoke **choice-free** recursion theory (`Recursive.lean`) means rebuilding the
  automata decision procedures primitively — a large separate effort. mathlib's `Language.IsRegular`
  has `.inf`/`.add`/`.compl` but **no `.mul` (concatenation closure)** and no decidability, so even a
  classical regularity proof needs the regex↔DFA bridge. (cf. `Example62Regular.lean` for the
  Myhill–Nerode infra already present.)
- **Infinite-word equations** `σ⃗σ⃗=σ⃗?`, `σ⃗σ⃗σ⃗=σ⃗?`, `σ⃗1⃗σ⃗1⃗=σ⃗1⃗?`, `01⃗01⃗01⃗01⃗=01⃗01⃗?` —
  Scott poses these as open *investigations* (least-fixed-point/total elements under `mulElem`).

**Gotchas worth keeping:**
- `Set.mem_singleton_iff` lives in `Mathlib.Data.Set.Insert`, which `Basic`'s `Mathlib.Data.Set.Basic`
  does **not** transitively import — add `import Mathlib.Data.Set.Insert` explicitly.
- `Language α := Set (List α)` is a (non-`abbrev`) `def`, so the `Mul`/`Inter`/`Singleton` instance
  resolution does **not** see through it; rather than fight that, this file uses a bespoke `concat` on
  `Set (List Bool)` so `∩`/`univ`/`{σ}` stay the native `Set` ops the nbhd-system API expects.
- Proving `IsPositive` of an `ofPositive`-built system: go `by intro …` (defeq unfolds `Ssys.mem` to
  `InS`), don't try to back out the args of `ofPositive_isPositive`.

**Next concrete target:** Exercise 7.23 (finish `PN` of Example 7.8; `fun`/`graph` + `∩`/`∪`/`+`
computable) — see `Example78.lean`. Or the deferred 7.22 effectively-given decision procedure if the
choice-free automata layer is built out.

---

## Checkpoint 2026-06-28 — Exercise 7.22 regular-event layer (`Exercise722Regular.lean`)

`Exercise722Regular.lean` (ns `Domain.Neighborhood.Exercise722`, imports `Exercise722`) green, wired,
zero `sorry`, **fully choice-free `⊆{propext,Quot.sound}`** (audit: `matchesB_iff`,
`decidableMemDenote`, `inS_eq_range_denote` = `{propext,Quot.sound}`; `InS_denote_of_nonempty`,
`InS_exists_denote`, `inS_iff_exists_denote` depend on **no axioms**).

**What this adds toward "effectively given" (Scott's regular-event hint).**
- **`SExpr`** (`deriving DecidableEq`): the syntax of `S`-terms — `sigma` (`Σ`), `single σ` (`{σ}`),
  `cat` (`·`), `cap` (`∩`). A regex fragment with `·`,`∩`,`Σ` only (**no** `∪`/complement/`∗`).
- **`denote : SExpr → Set (List Bool)`** (`= univ`/`{σ}`/`concat`/`∩`), with `@[simp]` unfolds.
- **Decidable membership** (the computational core of "regular event"): `matchesB : SExpr → List Bool
  → Bool` (cat case = `(List.range (|w|+1)).any` over cut points; cap = `&&`), `matchesB_iff`
  (`mem_concat_iff_split` splits `w = w.take i ++ w.drop i` via `List.take_left`/`drop_left`/
  `take_append_drop`), ⟹ `instance decidableMemDenote : DecidablePred (·∈denote e)`.
- **Soundness/completeness**: `InS_denote_of_nonempty` (non-empty denotation ∈ `S`; non-emptiness
  propagates *down* to subterms, needed for the `cap`→`InS.inter` nonemptiness arg) and
  `InS_exists_denote` (every `S`-member is a denotation), giving **`inS_iff_exists_denote : InS X ↔
  ∃ e, denote e = X ∧ X.Nonempty`** and `inS_eq_range_denote : {X|InS X} = denote '' {e|nonempty}`.

**Why full Def-7.1 effective givenness is NOT here (the hard wall, documented).** `RecDecidable p =
∃ f, Nat.Primrec f ∧ ∀n, p n ↔ f n = 1` — needs a genuine **primitive-recursive** decider; classical
`Decidable` does NOT lift to it. The two index relations are automata-complete:
- **(ii) consistency** `∃k.X_k⊆Xₙ∩Xₘ` ≡ (positivity, `Ssys_isPositive`) **∩-non-emptiness** of
  `denote(cap eₙ eₘ)` — needs product-automaton reachability (no structural recursion: `Σ{0}Σ∩Σ{1}Σ`
  non-empty vs `{00}∩{11}` empty), and a bounded-`matchesB` search needs a *proven* DFA length bound.
- **(i)** `Xₙ∩Xₘ=X_k` is **language equivalence**, and is **NOT** reducible to ∩-emptiness because the
  class lacks complement/`\` (`L₁⊆L₂ ⟺ L₁\L₂=∅`). Needs a regular-equivalence procedure (minimal
  DFAs / Myhill–Nerode; `Example62Regular.lean` has the Myhill–Nerode infra).
Even building the *enumeration* `X:ℕ→Set` onto `S` needs decidable emptiness (to map empty syntax
denotations back into `S`). mathlib gaps: `Language.IsRegular` has `.inf`/`.add`/`.compl` but **no
`.mul`** (concat closure) and no decidability; `RegularExpression` has `·`/`∪`/`∗` but **no `∩`**.
So the remaining work = a choice-free primitive-recursive subset-construction + product + reachability
+ pumping bound in `Recursive.lean`, then `matchesB` over a bounded word set. Sizeable; left for later.

**Reusable gotchas:** `Set.mem_singleton_iff` needs `import Mathlib.Data.Set.Insert` (not pulled by
`Mathlib.Data.Set.Basic`); `deriving Encodable`/auto `Countable` for a custom inductive is NOT
available (dropped the instance — countability is a prose remark); `matchesB` recurses structurally on
the `SExpr` arg with the word generalized (`induction e generalizing w`).

**Update — emptiness vs. equivalence settled (does NOT complete 7.22).** Added to
`Exercise722Regular.lean` (all `⊆{propext,Quot.sound}`): `emptyExpr := cap {0} {1}` with
`denote_emptyExpr = ∅` (so `∅` is fragment-denotable though `∉ S`); `empty_iff_equiv_emptyExpr`
(relation (ii) = ¬(equivalence to `∅`)); `interEq_iff` (relation (i) = language equivalence
`denote(cap eₙ eₘ)=denote e_k`, no axioms); `denote_catSigmaSigma` (`Σ·Σ=Σ` — `denote` not injective,
so (i) is NOT syntactic code-equality); and the **decisive counterexample** `sigma_ne_containsZero`
(`Σ ≠ Σ{0}Σ`, witness `[1]`, proved by `decide` on `matchesB`). **Conclusion: an emptiness decider
does NOT complete 7.22.** Both relations reduce to *language equivalence on `SExpr`*; equivalence is
strictly stronger than fragment-emptiness because the fragment lacks complement/`\` (`L₁⊆L₂ ⟺
L₁\L₂=∅`): deciding `Σ = Σ{0}Σ` needs to detect a word in `Σ ∩ (Σ{0}Σ)ᶜ = {1}*`, and `{1}*` is not a
fragment expression. Scott's claim is **still true** (regex-with-`∩` equivalence IS decidable, and a
primrec `inter n m := code(cap eₙ eₘ)` exists trivially since `denote(cap a b)=denote a ∩ denote b`),
so 7.22 is not "asking too much" — but completing it needs a full choice-free regular-language
**equivalence** decider (product/complement DFA or a derivative bisimulation with a finiteness/termination
proof), not merely emptiness. That equivalence decider is the remaining (large) automata sub-project;
`decide`-by-`matchesB` already settles any *fixed* word, so it handles concrete instances.

---

## Checkpoint 2026-06-28 (PM) — Exercise 7.22 DFA layer (Route A leaf automata) — `Exercise722DFA.lean`

**New file `Domain/Neighborhood/Exercise722DFA.lean` — green, wired, zero `sorry`, fully choice-free
`⊆{propext,Quot.sound}`** (audited: `sigmaDFA_accepts`, `singleDFA_accepts`, `singleDFA_evalFrom`,
`interDFA_accepts`, `complDFA_accepts` all `[propext, Quot.sound]`).

**Why this file / what changed in the plan.** Investigating the choice-free decision procedure for the
two Definition-7.1 relations (both reduced in `Exercise722Regular.lean` to **language equivalence on
`SExpr`**), I scoped mathlib's automata library and found the difficulty is **not** distributed as a
tidy "steps 1–3 easy / step 4 = finiteness hard". Two decisive facts:
- With **explicit `Fintype` DFA states (Route A)**, state-space finiteness is *structural* (it is the
  `Fintype` instance) — there is **no separate Brzozowski/ACI finiteness theorem to prove**. So the
  "hard step 4" essentially disappears.
- mathlib gives intersection/complement **for free** (`DFA.inter`/`accepts_inter`, `DFA.compl`/
  `accepts_compl`), but has **no language-concatenation automaton** (no NFA/εNFA/regex concat→DFA).
  So the genuine crux migrates *into* steps 1–2: building an **εNFA concatenation** for `cat` and
  proving `accepts = denote a * denote b` (via `εNFA.IsPath`/`isPath_append`, mathlib has the path
  API). That is the large, high-compute proof.

**Delivered (Medium pass) — the tractable Route-A pieces, all proved choice-free:**
- `sigmaDFA : DFA Bool Unit`, `sigmaDFA_accepts : .accepts = Set.univ` (+ `…_denote = denote .sigma`).
- `singleDFA σ : DFA Bool (Option (Fin (|σ|+1)))` (`none` = dead sink; `some i` = "read the length-`i`
  prefix of `σ`"); key lemma `singleDFA_evalFrom` (from `some k`, reading `w` reaches `some (k+|w|)`
  **iff `w <+: σ.drop k`**, else dead — the `List.IsPrefix` phrasing avoids all in-type `Fin` index
  proofs; uses `List.drop_eq_getElem_cons`, `List.cons_prefix_cons`, `IsPrefix.eq_of_length`); hence
  **`singleDFA_accepts : .accepts = {σ}`** (+ `…_denote`). `singleDFA_evalFrom_none` = dead sink.
- `inter_eval` (product DFA evaluates componentwise — choice-free, avoids mathlib's classical
  `accepts_inter`) ⟹ **`interDFA_accepts`** (`(M₁.inter M₂).accepts = denote (.cap a b)` from
  component correctness). **`complDFA_accepts`** (`Mᶜ.accepts = (denote a)ᶜ`, choice-free, defeq).
- Sanity `example`s confirming the state types carry **`Fintype` *and* `DecidableEq`** (`Unit`,
  `Option (Fin _)`, products) — so the eventual emptiness/equivalence search is decidable data.

**Reusable gotchas (new):** (1) `DFA.accepts : Language`, but goals often pick `Set.instMembership`
not `Language.instMembershipList` — `rw [DFA.mem_accepts]`/`Set.mem_inter_iff` then fail to match;
work via `show … eval … ∈ … accept` + defeq `exact`/`Iff.rfl` instead. (2) `rw`'s trailing
reducible-transparency `rfl` won't close `Language`-vs-`Set` defeq goals (`{σ}={σ}`, `Xᶜ=Xᶜ`); an
**explicit `rfl`** tactic (default transparency) does. (3) Don't `rw` the `dite` *condition* when the
`then`-branch's value has a proof depending on it (motive failure) — instead prove a `condiff : cond₁ ↔
cond₂` and discharge each side with `dif_pos`/`dif_neg`, closing the index with `Fin.ext`+`omega`.
(4) `Fintype (Option (Fin _))` is not pulled by `Mathlib.Computability.DFA`; needs
`import Mathlib.Data.Fintype.Option`.

**Remaining for a high-compute session (the real crux + the bridge):**
1. **`cat` concatenation automaton** (εNFA with ε-links accept_a→start_b; `St (cat a b)=St a ⊕ St b`)
   + correctness `accepts = denote a * denote b` via `εNFA.mem_accepts_iff_exists_path`/`isPath_append`.
   This is the hard proof; everything else composes off it.
2. A **`Finset`-state subset construction** (mathlib's `NFA.n` determinizes to `Set σ`, which lacks
   `DecidableEq`) so the determinized `cat` DFA keeps `DecidableEq` states.
3. The uniform `toDFA : (e:SExpr) → DFA Bool (St e)` recursion + `denote e = (toDFA e).accepts`.
4. **Decision**: emptiness = "no accept state reachable" (finite search over `Fintype` states);
   equivalence via `inter`+`compl`+emptiness (symmetric difference). Then the **`RecDecidable`/`Nat.Primrec`
   bridge** (encode the finite automaton + reachability search as a primitive-recursive function in
   the bespoke `Recursive.lean` theory) — this, not finiteness, is now the last choice-discipline-
   sensitive obligation for true Def-7.1 effective givenness.

---

## Checkpoint 2026-06-28 (late) — Exercise 7.22 step 4: the concatenation automaton + `denote e = accepts`

**Two new files, green, wired, zero `sorry`, fully choice-free `⊆{propext,Quot.sound}`** (audited):
`Domain/Neighborhood/Exercise722Cat.lean` and `Domain/Neighborhood/Exercise722Decide.lean`.

This is the high-compute "step 4". After scoping mathlib I found the difficulty is **not** "leaves
easy / finiteness hard": with explicit **`Fintype`-state automata**, finiteness is structural (it's
the `Fintype` instance). The real crux is the **concatenation automaton**, which mathlib lacks
entirely (it has `DFA.inter`/`compl`, NFA/εNFA/DFA, εNFA `IsPath` API, but **no language-concat
construction**, and **no automata emptiness/equivalence decider**). Also note `DecidableEq (Set σ)` is
**not** choice-free, so mathlib's `NFA.n` determinization (to `Set σ`) is useless for a choice-free
decision — hence the **NFA-centric, decide-emptiness-by-reachability** architecture (determinization is
only needed for *equivalence*/relation (i), deferred).

**`Exercise722Cat.lean` — the concatenation automaton (CRUX):** `catEps M₁ M₂ : εNFA Bool (σ₁ ⊕ σ₂)`
= copy of `M₁` on `inl`, `M₂` on `inr`, with **ε-edges from every `M₁`-accept to every `M₂`-start**
(encoded as a set-builder `{t | s ∈ M₁.accept ∧ t ∈ inr '' M₂.start}` — **not** `if…then…else`, which
needs `Decidable (s ∈ M₁.accept)`). Proven:
- `catEps_mem_εClosure_iff` — the only ε-edges go `inl`-accept → `inr`-start, so `εClosure T` adds
  `inr '' M₂.start` exactly when `T` holds an `inl`-accept state.
- **`catEps_mem_eval_iff`** (the engine, ~90-line induction via `List.reverseRecOn` +
  `εNFA.mem_stepSet_iff`): the reachable `inl`-states mirror `M₁.eval x`; the reachable `inr`-states
  are exactly `⋃` over prefix-splits `x = u ++ v` with `u ∈ M₁.accepts` of `M₂.eval v`. (Avoids
  `IsPath` path-surgery; the only fiddly list step is `v = v' ++ [c] ⟹ c = a ∧ x = u ++ v'` via
  `List.append_inj'`.)
- **`catEps_accepts : (catEps M₁ M₂).accepts = concat M₁.accepts M₂.accepts`** (project's `concat`).

**`Exercise722Decide.lean` — assembly + reduction:**
- `NFAinter` (NFA product, mathlib has no NFA intersection) + `NFAinter_mem_eval_iff` /
  `NFAinter_mem_accepts_iff` (componentwise, ∩ of languages).
- `autState : SExpr → Type` (`Unit` / `Option (Fin (|σ|+1))` / `×` / `⊕`) with
  `instFintypeAutState` (recursive `Fintype` instance); **`toNFA : (e) → NFA Bool (autState e)`**
  (leaves = `DFA.toNFA` of `Exercise722DFA`'s `sigmaDFA`/`singleDFA`; `cap` = `NFAinter`;
  `cat` = `(catEps … ….).toNFA`).
- **`toNFA_accepts : (toNFA e).accepts = denote e`** — every fragment language is recognised by an
  explicit `Fintype` automaton (the constructive, choice-free form of Scott's "the sets in `S` are
  regular events"). Leaf cases use **`dfaToNFA_accepts`**, a hand-rolled **choice-free** replacement
  for mathlib's `DFA.toNFA_correct` (which pulls `Classical.choice`!), proved via
  `dfaToNFA_eval : M.toNFA.eval x = {M.eval x}`.
- **`denote_eq_empty_iff : denote e = ∅ ↔ ∀ s ∈ (toNFA e).accept, ∀ x, s ∉ (toNFA e).eval x`**
  (+ generic `nfa_accepts_nonempty_iff`). This **reduces Definition 7.1 relation (ii)** (consistency,
  ≡ `∩`-non-emptiness by positivity of `Ssys`) to **reachability over the finite state set
  `autState e`** — the only non-finite quantifier (`∀ x`) is what a reachability search eliminates.

**Reusable gotchas (new):** (1) `if s ∈ (someSet) then…` needs `Decidable` — use a set-builder
instead to stay choice-free. (2) **mathlib's `DFA.toNFA_correct`, `DFA.toNFA_evalFrom_match` pull
`Classical.choice`** — reprove choice-free via `eval = {det-eval}`. (3) For recursive `def f : SExpr →
NFA …`, `rw [f]`/`simp only [f]` is flaky and the `accepts` projection across `Language`/`Set` blocks
mathlib `accepts`-lemmas; use `change … = …` to the unfolded form then `rw` with **explicit args**
(`dfaToNFA_accepts (singleDFA σ)`) and finish defeq goals with an explicit term (`Iff.rfl`,
`(Set.mem_inter_iff …).symm`). (4) `Set.eq_empty_iff_forall_notMem` (not `…not_mem`). (5) recursive
`Fintype` instance: `instFintypeAutState | .cap a b => by letI := … a; letI := … b; exact inferInstance`.

**What remains for true Def-7.1 effective givenness (well-scoped, NOT a finiteness proof):**
1. Turn `denote_eq_empty_iff`'s `∀ x` into a **terminating decision**. Two clean routes:
   (a) **Finset reachability fixpoint** over `autState e` — needs `DecidablePred` for membership in
   `(toNFA e).step`/`.start` (decidable through `εNFA.toNFA`'s εClosure; provable by induction on `e`),
   then `reachable = closure` computed in `≤ card` iterations, giving `Decidable` emptiness directly;
   (b) **pigeonhole pump-down** (`M.accepts.Nonempty → ∃ x ∈ accepts, |x| < Fintype.card σ`, via
   `NFA.Path` loop-excision + `Fintype.exists_ne_map_eq_of_card_lt`) ⟹ emptiness = "no short word
   matches", decided by the **already-built `matchesB`** (`Exercise722Regular`) over the finite set of
   words of length `< card`. Route (b) reuses `matchesB`/`decidableMemDenote` and needs no new
   `DecidablePred` step instances.
2. Relation (i) `Xₙ ∩ Xₘ = X_k` (language **equivalence**) additionally needs determinization +
   complement: a **`Finset`-state subset construction** (mathlib's `NFA.n` → `Set σ` is choice-unsafe
   for `DecidableEq`), then `inter`+`compl`+emptiness on the symmetric difference.
3. The **`RecDecidable`/`Nat.Primrec` bridge** (encode the finite automaton + the reachability/bounded
   search as a primitive-recursive characteristic function in the bespoke `Recursive.lean`). This —
   not finiteness — is the last choice-discipline-sensitive obligation.

---

## Checkpoint 2026-06-28 — Exercise 7.22 Composer C1: `instDecidableEqAutState`

**Session C1** (`@Exercise722-Composer-Run.md`): added recursive **`instDecidableEqAutState :
(e : SExpr) → DecidableEq (autState e)`** in `Exercise722Decide.lean`, mirroring
`instFintypeAutState` (base cases via `inferInstanceAs`; `cap`/`cat` by recursive `letI` + product/sum
instances). Two sanity `example`s: `.sigma` and `.single [true, false]`. **`lake build
Domain.Neighborhood.Exercise722Decide`** green, zero `sorry`. No new theorems — axiom audit N/A.
**Next Composer session:** C2 (`autStateCard` + bound) or C3 (`wordsUpTo`) — both unblocked.

---

## Checkpoint 2026-06-28 — Exercise 7.22 Composer C2: `autStateCard` + bound

**Session C2** (`@Exercise722-Composer-Run.md`): added **`autStateCard : SExpr → ℕ`** (sigma→1,
single→|σ|+2, cap→product, cat→sum) and **`autStateCard_le_card : autStateCard e ≤ Fintype.card (autState
e)`** in `Exercise722Decide.lean`. Proof: sigma/single by simp+card lemmas; cap/cat by
`Nat.mul_le_mul`/`Nat.add_le_add` chained with `Fintype.card_prod`/`Fintype.card_sum`. **`lake build
Domain.Neighborhood.Exercise722Decide`** green, zero `sorry`. No new axioms beyond
`⊆{propext,Quot.sound}`. **Next Composer session:** C3 (`wordsUpTo`) — no prerequisites; C4 blocked
until C2+C3 both ☑ (C2 now done).

---

## Checkpoint 2026-06-28 — Exercise 7.22 Composer C3: `wordsUpTo` + `anyMatchesB`

**Session C3** (`@Exercise722-Composer-Run.md`): new **`Domain/Neighborhood/Exercise722Words.lean`**
with **`wordsUpTo n`** (all `List Bool` of length ≤ `n`), **`mem_wordsUpTo : w ∈ wordsUpTo n ↔ w.length
≤ n`** (induction on `n`; append/flatMap split), and **`anyMatchesB e ws := ws.any (matchesB e)`**.
`#eval anyMatchesB .sigma (wordsUpTo 0)` = `true`. Wired in `Domain.lean`. **`lake build
Domain.Neighborhood.Exercise722Words`** green, zero `sorry`. No new theorems beyond the characterisation
— axiom audit N/A (`mem_wordsUpTo` choice-free by construction). **Next Composer session:** C4
(short-word bound via pumping; needs C2 ☑ + C3 ☑).

---

## Checkpoint 2026-06-28 — Exercise 7.22 Composer C4 BLOCKED

**Session C4** (`@Exercise722-Composer-Run.md`): attempted **`exists_accepted_word_short` /
`nfa_accepts_nonempty_iff_short` / `denote_nonempty_iff_short`** in `Exercise722Decide.lean`. Partial
progress: **`mem_pumped_ac`** (extract `a++c` from `{a}{b}*{c}`) and pumping branch of
`accepts_shorter_word` type-check; **`autStateCard_eq_card`** (needed for `denote_nonempty_iff_short`
with `wordsUpTo (autStateCard e)`) also drafted. **Blocker:** mathlib **`NFA.pumping_lemma`** bounds
`|a|+|b|` by **`Fintype.card (Set σ)`** (2^|σ|), not **`|σ|`**; the playbook's tight bound needs a
**path/pigeonhole** shorten on **`NFA.Path`** (skip loop → `a++c` accepted). Custom helpers
(`statesList`, `appendPath`, `exists_split`, `statesList_get_append`) did not reach green after multiple
build-fix passes (appendPath typing, `Exists.choose` on nested `∃`, `statesList_get` induction).
**Reverted** `Exercise722Decide.lean` to pre-C4 (`git checkout --`). **`lake build
Domain.Neighborhood.Exercise722Decide`** green again. Progress tracker C4 stays ☐. **Retry:** finish
path helpers (see playbook § Skeleton C4) or re-@ for **C11** (infinite-word prose, no prerequisites).

---

## Checkpoint 2026-06-28 (retry) — Exercise 7.22 Composer C4 BLOCKED (path API)

**Session C4 retry:** built **`pathStateAt` / `pathAppend` / `pathAppend_take_drop`** (dependent
`∃ w hp ht, pathStateAt = w` — avoids `∧` on `Path` **Type**), **`mem_evalFrom_of_path`**, **`accepts_skip_loop`**
(via `take i ++ drop j`), **`accepts_shorten_step`** (pigeonhole on `pathStateAt`), **`exists_accepted_word_short`**
(`Nat.strongRecOn`), plus **`autStateCard_eq_card`** / **`denote_nonempty_iff_short`**. **Blockers:** (1)
`cases p with | cons … =>` — pattern binders not visible to subsequent `let`/`match` lines (persistent
`Unknown identifier` on `start`/`ys`/…); (2) **`hu.trans heqi.symm`** typing for skip-loop state equality;
(3) **`accepts_card_zero`** / **`mem_evalFrom`** `rw` alignment with `Language`/`Set.iUnion`. Reverted
again (`git checkout -- Domain/Neighborhood/Exercise722Decide.lean`); **`lake build
Domain.Neighborhood.Exercise722Decide`** green. C4 stays ☐. **Next:** fix `pathAppend_take_drop` with
`match p, n with | .cons …, 0 =>` in a single term (no `cases`+`let`), or use **`NFA.Path.rec`**;
alternatively `@` for **C11**.

---

**2025-06-28 — Exercise 7.22 Composer C11 PASS (infinite-word prose).** Expanded `Exercise722.lean`
docstring § *Infinite words*: define `σ⃗` as `{X ∈ S | ∀n, σⁿ ∈ X}` aligned with `mulElem`/`emb`; prose
verdicts on Scott's four equations — **`σ⃗ σ⃗ = σ⃗` YES**, **`σ⃗ σ⃗ σ⃗ = σ⃗` YES**, **`σ⃗ 1⃗ σ⃗ 1⃗ = σ⃗ 1⃗`
YES** (idempotency for single-letter / `σ1`-period streams), **`01⃗ 01⃗ 01⃗ 01⃗ = 01⃗ 01⃗` NO** (period-2
case: `τ⃗² ⊊ τ⃗⁴`; counterexample neighbourhood containing only `τ^{4k}`). Left/right fixed-point
symmetry noted. No Lean proofs added (docstring only). **`lake build Domain.Neighborhood.Exercise722`**
green. C11 ☑. **Next:** C4 retry (short-word bound) or C5 when C4 passes.

---

**2026-06-28 — Exercise 7.22 Composer C4 PASS (short-word bound).** Added `Exercise722Words` import +
**ShortWord** section in `Exercise722Decide.lean`: path-based pigeonhole (`pathStateAt`, `pathAppend`,
`PathSplit` / `pathAppend_take_drop`, `accepts_skip_loop`, `accepts_shorten_step`,
`exists_accepted_word_short`, `nfa_accepts_nonempty_iff_short`, `autStateCard_eq_card`,
`denote_nonempty_iff_short`). Bound is **`|w| < Fintype.card σ`** (tighter than mathlib
`NFA.pumping_lemma`'s `2^|σ|`). **`lake build Domain.Neighborhood.Exercise722Decide`** green, zero
`sorry`. Axiom audit: `denote_nonempty_iff_short` uses **`Classical.choice`** (via
`Fintype.exists_ne_map_eq_of_card_lt` / noncomputable path split) — acceptable for **Prop-level**
lemmas; **C5 `decideEmptyB` stays computable** via `matchesB`. C4 ☑. **Next:** C5 (`decideEmptyB`).

---

**2026-06-28 — Exercise 7.22 Composer C5 PASS (`decideEmptyB`).** Added **`decideNonemptyB`** /
**`decideEmptyB`** (`anyMatchesB e (wordsUpTo (autStateCard e))`), **`decideNonemptyB_iff`**, **`decideEmptyB_iff`**, and **`decidableEmptyDenote`** in `Exercise722Decide.lean`. `#eval decideEmptyB (.cap (.single [false]) (.single [true]))` = `true`. **`lake build Domain.Neighborhood.Exercise722Decide`** green, zero `sorry`. **Computational core is choice-free** (`matchesB`/`anyMatchesB`); iff lemmas inherit **`Classical.choice`** from C4's `denote_nonempty_iff_short` (Prop-level only — the **Bool function** does not invoke choice at runtime). C5 ☑. **Next:** C6 (`consistentB`).

---

**2026-06-28 — Exercise 7.22 Composer C6 PASS (`consistentB`).** Added **`consistentB a b := !decideEmptyB (.cap a b)`**, **`consistentB_iff`**, **`capNonempty_iff_consistent`**, and **`consistentB_iff_Ssys`** (links Bool decider to Def 7.1 (ii) via **`Ssys_isPositive`** / **`Ssys_mem`**). Fix: apply **`Ssys_isPositive`** with implicit `X,Y` — pass **`Ssys_mem.mpr ha`** not `(denote a)`. **`lake build Domain.Neighborhood.Exercise722Decide`** green, zero `sorry`. **`consistentB`** is computable; iff lemmas inherit **`Classical.choice`** from C5 (Prop-level). C6 ☑. **Next:** C7a (interEq docstring) or C8 (`SsysX` enumeration).

---

**2026-06-28 — Exercise 7.22 Composer C7a PASS (interEq gap documented).** Added § *Relation (i) `interEq`* docstring at end of `Exercise722Decide.lean`: (i) = language equivalence (`interEq_iff`); (ii) mechanised via `consistentB`; emptiness insufficient (`sigma_ne_containsZero` / complement not in fragment); full (i) decider deferred to C7b (compl + symmetric difference or bisimulation). Docstring only, no new proofs. **`lake build Domain.Neighborhood.Exercise722Decide`** green. C7a ☑. **Next:** C8 (`SsysX` enumeration) or C12 (arxiv, needs C6+).

---

**2026-06-28 — Exercise 7.22 Composer C8 PASS (`SsysX` enumeration).** New **`Exercise722Presentation.lean`**: Gödel **`SExpr.encode`**, fuelled **`decodeFuel`/`SExpr.decode`**, index **`SExpr.index = pair (encode e) (sexprDepth e)`**, **`SsysX n`** (non-empty `denote e` via `decideNonemptyB`, junk/empty → `Σ`), **`SsysX_mem`**, **`SsysX_surj`**. Wired in **`Domain.lean`**. **`lake build Domain.Neighborhood.Exercise722Presentation`** green, zero `sorry`. Axiom audit: **`SsysX_mem`/`SsysX_surj` ⊆ `{propext, Classical.choice, Quot.sound}`** (choice inherited from `decideNonemptyB_iff`). C8 ☑. **Next:** C9 (`RecDecidable₂` consistency) or C12.

---

**2026-06-28 — SESSION C9 BLOCKED (`RecDecidable₂` consistency).** Partial C9 in **`Exercise722Presentation.lean`**: **`ssysActive`**, **`safeDecodeActive`**, **`ssysConsistentB`**, **`ssys_cons_positivity`**, **`ssys_cons_iff`**, **`ssysConsistentB_iff`**, **`ssys_cons_char_iff`** (Scott (ii) ↔ `consistentB` on safe decode ↔ `ssysConsistentB`). **`lake build Domain.Neighborhood.Exercise722Presentation`** green, zero `sorry`. Axioms: **`ssys_cons_char_iff` ⊆ `{propext, Classical.choice, Quot.sound}`**. **Blocker:** `Ssys_cons_computable : RecDecidable₂ (fun n m => ∃ k, SsysX k ⊆ SsysX n ∩ SsysX m)` needs a **`Nat.Primrec` port** of `decideNonemptyB`/`consistentB` on Gödel-coded indices (`selectFn`/`isOne` char function + `primrec_Ssys_consChar`); same gap as `Exercise722DFA.lean` “decision bridge”. Attempted `Ssys_consChar`/`ssysActiveN`/`ssysCapConsistentN` proofs hit `simp` recursion / WHNF timeout on `selectFn_ite` linkage. C9 tracker stays ☐. **Retry:** add primrec emptiness/consistency on `(code,fuel)` in `Presentation.lean` (or shared `Recursive.lean` helper), then `RecDecidable.of_iff` + `Ssys_consChar`. **Next:** C9 retry or C12 (arxiv audit, needs C6+ only).

---

**2026-06-28 — Exercise 7.22 Composer C12 PASS (arxiv + audit).** Updated **`arxiv.md`** Exercise 7.22 row: Composer C1–C6/C7a/C8/C9-partial/C11 status; **`decideEmptyB_iff`/`consistentB_iff` axiom audit** (`⊆ {propext, Classical.choice, Quot.sound}`, choice inherited); **Still open** C9–C10/C7b. **`HANDOFF.md`** Resume Protocol Composer tracker line updated. **`lake build Domain`** green. C12 ☑. **Next:** C9 retry (`Nat.Primrec` bridge) or C10 (after C9).

---

**2026-06-29 — Exercise 7.22 C9: failed monolith removed; situation restated.** **Deleted** untracked **`Exercise722Primrec.lean`** (~840 lines, never green, ~88 errors): duplicated `SExpr` encode/decode from **`Exercise722Presentation.lean`**, attempted full **`matchesBCode`/`decideNonemptyBCode`** stack — blocked by `List.mapM` API drift, `Nat.pair` bounds, cascading `primrec_*` errors. **Not wired** into `Domain.lean`. **Kept (green):** **`Recursive.lean`** additions — **`isZero`/`primrec_isZero`**, **`primrec_le`**, **`primrec_max`**, **`primrec_ite`**, **`bExistsFn`** (+ lemmas); **`lake build Domain`** green. **Still green:** C1–C8, C11, C12; Presentation logical C9 layer (`ssys_cons_char_iff`). **Still open:** `Ssys_cons_computable`, C10, C7b. **Viable C9 retry:** small primrec char in/after **`Exercise722Presentation.lean`**, importing existing decode — not a monolith. C9/C10 tracker ☐.

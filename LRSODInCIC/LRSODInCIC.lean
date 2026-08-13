/- ================================================================
   L, R, S, O, D expressed in Lean 4's Calculus of Inductive
   Constructions.

   Standalone package (no Mathlib, no scott1972/1980/1982).

   Strategy: a DEEP EMBEDDING. Each layer is a `structure` whose
   fields are exactly the axioms of that layer, over an abstract
   carrier. Lean's ambient `Set`, `Classical.choice`, and unbounded
   `Type u` hierarchy are STRONGER than S was built to be (S has no
   Choice, no Replacement beyond ω, and exactly one Power Set
   application). Using them directly would silently smuggle in content
   S forbids. So: no `import Mathlib`, and `Classical.choice` is never
   invoked.
   ================================================================ -/

/- ----------------------------------------------------------------
   L, R — Logic and inference rules

   Inherent in CIC's kernel (typing rules K1–K7, definitional
   equality E1–E10) — EXCEPT L3 (classical contraposition), since bare
   CIC is intuitionistic. We add the minimum needed to recover L3:
   excluded middle as a single local axiom — NOT `Classical.choice`.
   ---------------------------------------------------------------- -/

axiom lem : ∀ (p : Prop), p ∨ ¬p

theorem L3 (p q : Prop) : (¬q → ¬p) → (p → q) := by
  intro h hp
  cases lem q with
  | inl hq  => exact hq
  | inr hnq => exact absurd hp (h hnq)

-- R1 (modus ponens) = function application; R2 (generalization) = λ-abstraction.


/- ----------------------------------------------------------------
   S — Set theory (Z minus Choice minus Replacement, V_{ω+2})
   ---------------------------------------------------------------- -/

structure SetTheory where
  V   : Type
  mem : V → V → Prop

  -- S1 Extensionality
  ext : ∀ x y : V, (∀ z, mem z x ↔ mem z y) → x = y

  -- S2 Pairing
  pair   : V → V → V
  pairAx : ∀ x y z : V, mem z (pair x y) ↔ (z = x ∨ z = y)

  -- S3 Union
  union   : V → V
  unionAx : ∀ x z : V, mem z (union x) ↔ ∃ y, mem y x ∧ mem z y

  -- S5 Separation (Δ₀-in-∈ schema, rendered as `V → Prop` on fixed V)
  sep   : (V → Prop) → V → V
  sepAx : ∀ (φ : V → Prop) (x z : V), mem z (sep φ x) ↔ (mem z x ∧ φ z)

  succ    : V → V
  succAx  : ∀ x z : V, mem z (succ x) ↔ (mem z x ∨ z = x)
  empty   : V
  emptyAx : ∀ z : V, ¬ mem z empty

  -- S4 Infinity
  omega0   : V
  infOmega : mem empty omega0 ∧ ∀ y, mem y omega0 → mem (succ y) omega0

  -- S6 Power Set — only 𝒫(ω₀)
  powOmega   : V
  powOmegaAx : ∀ y : V, mem y powOmega ↔ (∀ z, mem z y → mem z omega0)

namespace SetTheory
variable (T : SetTheory)

def sub (x y : T.V) : Prop := ∀ z, T.mem z x → T.mem z y

def isInductive (I : T.V) : Prop :=
  T.mem T.empty I ∧ ∀ y, T.mem y I → T.mem (T.succ y) I

def omega : T.V :=
  T.sep (fun z => ∀ I, T.sub I T.omega0 → T.isInductive I → T.mem z I) T.omega0

end SetTheory


/- ----------------------------------------------------------------
   O — Point-set topology, general, 3 axioms
   ---------------------------------------------------------------- -/

structure TopologicalSpace (D : Type) where
  isOpen : (D → Prop) → Prop

  openEmpty : isOpen (fun _ => False)
  openFull  : isOpen (fun _ => True)

  openUnion : ∀ {ι : Type} (U : ι → D → Prop),
                (∀ i, isOpen (U i)) → isOpen (fun x => ∃ i, U i x)

  openInter : ∀ (U W : D → Prop), isOpen U → isOpen W →
                isOpen (fun x => U x ∧ W x)


/- ----------------------------------------------------------------
   D — D∞-specific axioms, stated purely in O's vocabulary
   ---------------------------------------------------------------- -/

namespace TopologicalSpace
variable {D : Type} (T : TopologicalSpace D)

def leq (x y : D) : Prop := ∀ U, T.isOpen U → U x → U y

def isClosed (C : D → Prop) : Prop := T.isOpen (fun x => ¬ C x)

def clSingleton (y : D) : D → Prop := fun x => T.leq x y

def compact (K : D → Prop) : Prop :=
  ∀ {ι : Type} (U : ι → D → Prop),
    (∀ i, T.isOpen (U i)) →
    (∀ x, K x → ∃ i, U i x) →
    ∃ (n : Nat) (f : Fin n → ι), ∀ x, K x → ∃ j, U (f j) x

def irreducible (C : D → Prop) : Prop :=
  (∃ x, C x) ∧
  ¬ ∃ C1 C2,
      T.isClosed C1 ∧ T.isClosed C2 ∧
      (∀ x, C1 x → C x) ∧ (∀ x, C2 x → C x) ∧
      (∀ x, C x → C1 x ∨ C2 x) ∧
      (∃ x, C x ∧ ¬ C1 x) ∧ (∃ x, C x ∧ ¬ C2 x)

end TopologicalSpace

structure DInfinityFoundations (D : Type) extends TopologicalSpace D where
  t0 : ∀ x y : D, (∀ U, isOpen U → (U x ↔ U y)) → x = y

  sober : ∀ C : D → Prop,
            toTopologicalSpace.isClosed C →
            toTopologicalSpace.irreducible C →
            ∃ y, C = toTopologicalSpace.clSingleton y ∧
              ∀ y', C = toTopologicalSpace.clSingleton y' → y' = y

  basis     : Nat → (D → Prop)
  basisOpen : ∀ n, isOpen (basis n)
  basisCpt  : ∀ n, toTopologicalSpace.compact (basis n)
  basisGen  : ∀ U, isOpen U → ∀ x, U x → ∃ n, basis n x ∧ (∀ y, basis n y → U y)
  basisCap  : ∀ m n, ∃ k, ∀ x, (basis m x ∧ basis n x) ↔ basis k x

  bot   : D
  botAx : ∀ U, isOpen U → U bot → ∀ x, U x


/- ----------------------------------------------------------------
   A worked witness: the Sierpiński domain  ⊥ ⊑ ⊤

   `instance` is reserved for `class` declarations. `DInfinityFoundations`
   is a `structure`, so a witness is an ordinary value: `def` to name it
   and reuse it (as here), or `example` to check satisfiability without
   adding anything to the environment.

   Carrier `Bool`, with `false` as ⊥ and `true` as ⊤. The opens are the
   up-sets — ∅, {⊤}, {⊥,⊤} — which is exactly the condition
   `U ⊥ → U ⊤`. This is Sierpiński space, the smallest non-degenerate
   Scott domain, and it satisfies D1–D4 in full.

   Two things this witness makes concrete. First, D1–D4 axiomatize a
   *class* of spaces (pointed ω-algebraic domains) rather than pinning
   down D∞: reaching D∞ specifically needs the tower and the inverse
   limit, which are constructions on top of D1–D4, not consequences of
   them. Second, the axiom audit at the end localizes the classical
   frontier — sobriety (D2) is the only field whose proof reaches for
   `lem`; O, D1, D3 and D4 are verified constructively.
   ---------------------------------------------------------------- -/

def sierpTop : TopologicalSpace Bool where
  isOpen U  := U false → U true
  openEmpty := fun h => h
  openFull  := fun h => h
  openUnion := by
    intro _ U hU h
    obtain ⟨i, hi⟩ := h
    exact ⟨i, hU i hi⟩
  openInter := by
    intro U W hU hW h
    exact ⟨hU h.1, hW h.2⟩

/-- Every open containing ⊥ is the whole space: `botAx` in usable form. -/
theorem sierp_up {U : Bool → Prop} (hU : sierpTop.isOpen U) (h : U false) :
    ∀ x, U x := by
  intro x
  cases x
  · exact h
  · exact hU h

/-- `{⊤}` is open: the separating open witnessing T₀. -/
theorem sierp_isOpen_top : sierpTop.isOpen (fun b => b = true) := fun _ => rfl

/-- Everything is below ⊤. -/
theorem sierp_leq_top (x : Bool) : sierpTop.leq x true := by
  intro U hU h
  cases x
  · exact hU h
  · exact h

theorem sierp_leq_bot_bot : sierpTop.leq false false := fun _ _ h => h

/-- ⊤ is *not* below ⊥ — the order is non-trivial, unlike a T₁ space. -/
theorem sierp_not_leq_top_bot : ¬ sierpTop.leq true false := by
  intro h
  exact absurd (h _ sierp_isOpen_top rfl) (by decide)

def sierp : DInfinityFoundations Bool where
  toTopologicalSpace := sierpTop

  -- D1: the open `{⊤}` separates ⊥ from ⊤, so `leq` is antisymmetric.
  t0 := by
    intro x y h
    cases x <;> cases y
    · rfl
    · exact absurd ((h _ sierp_isOpen_top).mpr rfl) (by decide)
    · exact absurd ((h _ sierp_isOpen_top).mp rfl) (by decide)
    · rfl

  -- D2: the two irreducible closed sets are {⊥} and the whole space,
  -- with generic points ⊥ and ⊤ respectively.
  sober := by
    intro C hC hirr
    obtain ⟨w, hw⟩ := hirr.1
    cases lem (C true) with
    | inl hCt =>
        have hCf : C false := by
          cases lem (C false) with
          | inl h => exact h
          | inr h => exact absurd hCt (hC h)
        refine ⟨true, ?_, ?_⟩
        · funext x
          refine propext ⟨fun _ => sierp_leq_top x, fun _ => ?_⟩
          cases x
          · exact hCf
          · exact hCt
        · intro y' hy'
          cases y' with
          | false => exact absurd (cast (congrFun hy' true) hCt) sierp_not_leq_top_bot
          | true  => rfl
    | inr hCt =>
        have hCf : C false := by
          cases w
          · exact hw
          · exact absurd hw hCt
        refine ⟨false, ?_, ?_⟩
        · funext x
          cases x
          · exact propext ⟨fun _ => sierp_leq_bot_bot, fun _ => hCf⟩
          · exact propext ⟨fun h => absurd h hCt, fun h => absurd h sierp_not_leq_top_bot⟩
        · intro y' hy'
          cases y' with
          | false => rfl
          | true  => exact absurd (cast (congrFun hy' true).symm (sierp_leq_top true)) hCt

  -- D3: basis 0 = {⊥,⊤}, basis (n+1) = {⊤}. Both compact open, and the
  -- family is closed under intersection.
  basis := fun n =>
    match n with
    | 0     => fun _ => True
    | _ + 1 => fun b => b = true

  basisOpen := by
    intro n
    cases n
    · exact fun h => h
    · exact fun _ => rfl

  basisCpt := by
    intro n ι U hU hcov
    cases n with
    | zero =>
        -- one open suffices: whichever open covers ⊥ is already everything
        obtain ⟨i, hi⟩ := hcov false trivial
        exact ⟨1, fun _ => i, fun x _ => ⟨0, sierp_up (hU i) hi x⟩⟩
    | succ _ =>
        obtain ⟨i, hi⟩ := hcov true rfl
        refine ⟨1, fun _ => i, ?_⟩
        intro x hx
        cases x
        · exact Bool.noConfusion hx
        · exact ⟨0, hi⟩

  basisGen := by
    intro U hU x hx
    cases x with
    | false => exact ⟨0, trivial, fun y _ => sierp_up hU hx y⟩
    | true  =>
        refine ⟨1, rfl, ?_⟩
        intro y hy
        cases y
        · exact absurd hy (by decide)
        · exact hx

  basisCap := by
    intro m n
    cases m with
    | zero =>
        cases n with
        | zero   => exact ⟨0, fun _ => ⟨fun _ => trivial, fun _ => ⟨trivial, trivial⟩⟩⟩
        | succ k => exact ⟨k + 1, fun _ => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩⟩
    | succ k =>
        cases n with
        | zero   => exact ⟨k + 1, fun _ => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩⟩
        | succ _ => exact ⟨k + 1, fun _ => ⟨fun h => h.1, fun h => ⟨h, h⟩⟩⟩

  -- D4: ⊥ is the generic point.
  bot   := false
  botAx := fun _ hU h x => sierp_up hU h x

/-- The order is genuinely two-element: ⊥ ⊑ ⊤ but not conversely. -/
example : sierpTop.leq false true ∧ ¬ sierpTop.leq true false :=
  ⟨sierp_leq_top false, sierp_not_leq_top_bot⟩

-- Axiom audit. Layer O and the order facts are outright axiom-free; all
-- three axioms in the full witness enter through `sober` alone — `propext`
-- and `Quot.sound` via `funext`/`propext` on the closure equation, and `lem`
-- for the case split on `C ⊤`. D2 is the classical frontier here.
#print axioms sierpTop                -- does not depend on any axioms
#print axioms sierp_not_leq_top_bot   -- does not depend on any axioms
#print axioms sierp                   -- [lem, propext, Quot.sound]

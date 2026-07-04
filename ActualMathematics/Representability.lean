/-
  PrimitiveRecognitionCalculus/Representability.lean

  The definitional repair of the forced predicate: from a bare injection to a
  FINITE-CODE DECODER.

  The panel audit of the demarcation paper found the one real mismatch in the
  base development: the choice-free diagonal refutes an ENUMERATION (a
  surjection ℕ → (ℕ → Bool)), while `DeltaForced` demands an INJECTION X ↪ ℕ.
  Constructively these are not interchangeable (turning an injection into a
  surjection needs decidability of the image), which is exactly why
  `not_deltaForced_real` carries a classical tag. This module repairs the
  definition so the diagonal hits it directly:

    A REPRESENTATION of X is a decoder `ℕ → Option X` that covers X: every
    element has a code that decodes to it. The `Option` makes the domain of
    the partial decoding DECIDABLE (a protocol can recognize a valid code),
    which is precisely what separates this notion from the effective-topos
    subcountability of 2^ℕ (where the code domain is undecidable). With a
    decidable code domain, the bare diagonal refutes a representation of the
    binary sequences choice-free: `not_representable_cantor` has axiom
    profile ⊆ {propext, Quot.sound}. The boundary statement now lives AT the
    definition, not beside it.

  Contents:
  * `Representation`, `DeltaRepresentable`: the repaired certificate notion.
  * The forced tower ℕ, ℤ, ℚ with EXPLICIT decoders, all choice-free
    (`representable_nat/int/rat`, bundled in `representable_tower`).
  * Closure under the operations of distinction, choice-free: product
    (`Representation.prod`, via the local pairing `dpair` and the bounded
    search `findPair`), branch (`Representation.sum`, parity interleave), and
    DECIDABLE restriction (`Representation.subtype`). The decidability
    requirement on restriction is a feature, not a loss: distinction cuts
    along decidable predicates.
  * `not_representable_cantor`: the diagonal at the definition, choice-free.
  * `no_self_survey`: the generalized diagonal. For EVERY type X there is no
    surjection X → (X → Bool): closure under distinction never closes under
    self-description. Choice-free.
  * `deltaForced_of_representable`: for discrete types (decidable equality)
    the decoder yields the least-code injection via `Nat.find`, choice-free.
    So the repaired notion refines the original on the discrete fragment.
  * Classical bridges (tagged classical, kept separate): representable types
    are countable, ℝ is not representable, and classically representable =
    countable (the constructive separation between them is LEM/intensionality,
    not the axiom of choice).

  No project-local axioms. No sorry. Forced-side facts are
  `Classical.choice`-free; the classical bridges are quarantined at the end.
-/

import Mathlib
import ActualMathematics.DeltaForced

namespace ActualMathematics
namespace Forced

universe u v

/-! ### The repaired certificate: a covering decoder -/

/-- A **representation** of `X`: a decoder from finite codes with a decidable
domain (`Option` marks invalid codes), covering all of `X`. This is the
finite-code-representability repair of the forced predicate: the certificate is
the decoder one actually runs, and the diagonal refutes it directly. -/
structure Representation (X : Type u) where
  /-- The decoder: a total function from codes to `Option X`; `none` marks an
  invalid code, so the domain of definition is decidable. -/
  decode : ℕ → Option X
  /-- Covering: every element of `X` has a code. -/
  complete : ∀ x : X, ∃ n : ℕ, decode n = some x

/-- A type is **δ-representable** when it carries a representation. This is the
repaired forced predicate: forced = carries an explicit covering decoder. -/
def DeltaRepresentable (X : Type u) : Prop := Nonempty (Representation X)

/-! ### Decoding integers: the inverse of the parity certificate -/

/-- The decoding inverse of `intToNat`: even codes are nonnegative, odd codes
are negative. -/
def intFromNat (n : ℕ) : ℤ :=
  if n % 2 = 0 then ((n / 2 : ℕ) : ℤ) else -(((n / 2 : ℕ) : ℤ) + 1)

theorem intFromNat_intToNat (z : ℤ) : intFromNat (intToNat z) = z := by
  cases z with
  | ofNat k =>
      show intFromNat (2 * k) = Int.ofNat k
      unfold intFromNat
      have h1 : (2 * k) % 2 = 0 := by omega
      have h2 : (2 * k) / 2 = k := by omega
      rw [if_pos h1, h2]
      rfl
  | negSucc k =>
      show intFromNat (2 * k + 1) = Int.negSucc k
      unfold intFromNat
      have h1 : ¬ ((2 * k + 1) % 2 = 0) := by omega
      have h2 : (2 * k + 1) / 2 = k := by omega
      rw [if_neg h1, h2, Int.negSucc_eq]

/-! ### Decoding pairs: bounded search inverts `dpair`

`dpair` (DeltaForced.lean) is the choice-free Cantor-style pairing. Its
decoding needs no `Nat.sqrt` (whose Mathlib lemmas pull `Classical.choice`):
since `dpair a b ≥ a, b`, a bounded search over all pairs below the code finds
the unique preimage. -/

/-- Both coordinates of a `dpair` preimage are bounded by the code. (The two
conjuncts are discharged separately: `omega` on a conjunction goal routes
through `Classical.choice`, per-conjunct it stays choice-free.) -/
theorem dpair_le {a b m : ℕ} (h : dpair a b = m) : a ≤ m ∧ b ≤ m := by
  unfold dpair at h
  by_cases hab : a < b
  · rw [if_pos hab] at h
    have hb : 1 ≤ b := by omega
    have hbb : b * 1 ≤ b * b := Nat.mul_le_mul_left b hb
    have hb1 : b * 1 = b := Nat.mul_one b
    constructor
    · omega
    · omega
  · rw [if_neg hab] at h
    constructor
    · omega
    · omega

/-- The second coordinate is bounded by the code (standalone form). -/
theorem dpair_right_le (a b : ℕ) : b ≤ dpair a b :=
  (dpair_le rfl).2

/-- Bounded search for a `dpair` preimage of `m`: scan indices `i < fuel`,
reading `i` as the pair `(i / (m+1), i % (m+1))`. -/
def findPairAux (m : ℕ) : ℕ → Option (ℕ × ℕ)
  | 0 => none
  | i + 1 =>
      if dpair (i / (m + 1)) (i % (m + 1)) = m then
        some (i / (m + 1), i % (m + 1))
      else findPairAux m i

theorem findPairAux_sound (m : ℕ) :
    ∀ (fuel : ℕ) (a b : ℕ), findPairAux m fuel = some (a, b) → dpair a b = m := by
  intro fuel
  induction fuel with
  | zero =>
      intro a b h
      exact absurd h (by simp [findPairAux])
  | succ i ih =>
      intro a b h
      unfold findPairAux at h
      by_cases hc : dpair (i / (m + 1)) (i % (m + 1)) = m
      · rw [if_pos hc] at h
        have hab : i / (m + 1) = a ∧ i % (m + 1) = b := by
          have h' := Option.some.inj h
          exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
        rw [← hab.1, ← hab.2]
        exact hc
      · rw [if_neg hc] at h
        exact ih a b h

theorem findPairAux_isSome (m i : ℕ)
    (hhit : dpair (i / (m + 1)) (i % (m + 1)) = m) :
    ∀ fuel : ℕ, i < fuel → (findPairAux m fuel).isSome = true := by
  intro fuel
  induction fuel with
  | zero => intro h; omega
  | succ j ih =>
      intro hij
      unfold findPairAux
      by_cases hc : dpair (j / (m + 1)) (j % (m + 1)) = m
      · rw [if_pos hc]; rfl
      · rw [if_neg hc]
        have hne : i ≠ j := by
          intro hEq; rw [hEq] at hhit; exact hc hhit
        exact ih (by omega)

/-- The pair decoder: search all indices below `(m+1)²`. -/
def findPair (m : ℕ) : Option (ℕ × ℕ) := findPairAux m ((m + 1) * (m + 1))

/-- `findPair` inverts `dpair`: the bounded search finds the (unique, by
`dpair_inj2`) preimage. Choice-free. -/
theorem findPair_eq (a b : ℕ) : findPair (dpair a b) = some (a, b) := by
  set m := dpair a b with hm
  -- the witness index is `a * (m + 1) + b`
  have hbounds : a ≤ m ∧ b ≤ m := dpair_le hm.symm
  have hdiv : (a * (m + 1) + b) / (m + 1) = a := by
    have h4 : a * (m + 1) + b = (m + 1) * a + b := by ring
    have h2 : ((m + 1) * a + b) / (m + 1) = a + b / (m + 1) :=
      Nat.mul_add_div (by omega) a b
    have h3 : b / (m + 1) = 0 := Nat.div_eq_of_lt (by omega)
    rw [h4, h2]
    omega
  have hmod : (a * (m + 1) + b) % (m + 1) = b := by
    have h4 : a * (m + 1) + b = (m + 1) * a + b := by ring
    have h2 : ((m + 1) * a + b) % (m + 1) = b % (m + 1) := Nat.mul_add_mod _ _ _
    have h3 : b % (m + 1) = b := Nat.mod_eq_of_lt (by omega)
    rw [h4, h2]
    omega
  have hhit : dpair ((a * (m + 1) + b) / (m + 1)) ((a * (m + 1) + b) % (m + 1)) = m := by
    rw [hdiv, hmod]
  have hlt : a * (m + 1) + b < (m + 1) * (m + 1) := by
    have h1 : a * (m + 1) ≤ m * (m + 1) :=
      Nat.mul_le_mul_right (m + 1) hbounds.1
    have h2 : m * (m + 1) + (m + 1) = (m + 1) * (m + 1) := by ring
    omega
  have hsome := findPairAux_isSome m (a * (m + 1) + b) hhit ((m + 1) * (m + 1)) hlt
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hsome
  have hsound : dpair p.1 p.2 = m := findPairAux_sound m _ p.1 p.2 (by rw [hp])
  have hpe : p.1 = a ∧ p.2 = b := dpair_inj2 (by rw [hsound, hm])
  show findPairAux m ((m + 1) * (m + 1)) = some (a, b)
  rw [hp, ← hpe.1, ← hpe.2]

/-! ### The representable tower: explicit decoders for ℕ, ℤ, ℚ -/

/-- The identity decoder for ℕ. -/
def reprNat : Representation ℕ where
  decode n := some n
  complete x := ⟨x, rfl⟩

/-- The parity decoder for ℤ. -/
def reprInt : Representation ℤ where
  decode n := some (intFromNat n)
  complete z := ⟨intToNat z, by rw [intFromNat_intToNat]⟩

/-- The rational decoder: split the code into a numerator code and a
denominator, and accept exactly the reduced fractions. -/
def decodeRat (m : ℕ) : Option ℚ :=
  match findPair m with
  | some (a, b) =>
      if h : b ≠ 0 ∧ (intFromNat a).natAbs.Coprime b then
        some ⟨intFromNat a, b, h.1, h.2⟩
      else none
  | none => none

theorem decodeRat_complete (q : ℚ) :
    decodeRat (dpair (intToNat q.num) q.den) = some q := by
  obtain ⟨n, d, hd, hred⟩ := q
  show decodeRat (dpair (intToNat n) d) = some ⟨n, d, hd, hred⟩
  unfold decodeRat
  rw [findPair_eq]
  simp only [intFromNat_intToNat]
  rw [dif_pos ⟨hd, hred⟩]

/-- The reduced-fraction decoder for ℚ. -/
def reprRat : Representation ℚ where
  decode := decodeRat
  complete q := ⟨dpair (intToNat q.num) q.den, decodeRat_complete q⟩

theorem representable_nat : DeltaRepresentable ℕ := ⟨reprNat⟩
theorem representable_int : DeltaRepresentable ℤ := ⟨reprInt⟩
theorem representable_rat : DeltaRepresentable ℚ := ⟨reprRat⟩

/-- **The representable tower.** ℕ, ℤ, ℚ carry explicit covering decoders,
choice-free. This is the forced tower under the repaired definition. -/
theorem representable_tower :
    DeltaRepresentable ℕ ∧ DeltaRepresentable ℤ ∧ DeltaRepresentable ℚ :=
  ⟨representable_nat, representable_int, representable_rat⟩

/-! ### Closure under the operations of distinction (choice-free) -/

/-- Product of representations: decode the two halves of a paired code. -/
def Representation.prod {X : Type u} {Y : Type v}
    (rX : Representation X) (rY : Representation Y) : Representation (X × Y) where
  decode m :=
    match findPair m with
    | some (i, j) =>
        match rX.decode i, rY.decode j with
        | some x, some y => some (x, y)
        | _, _ => none
    | none => none
  complete := by
    rintro ⟨x, y⟩
    obtain ⟨i, hi⟩ := rX.complete x
    obtain ⟨j, hj⟩ := rY.complete y
    exact ⟨dpair i j, by simp [findPair_eq, hi, hj]⟩

/-- Sum of representations: parity interleave of the two decoders. -/
def Representation.sum {X : Type u} {Y : Type v}
    (rX : Representation X) (rY : Representation Y) : Representation (X ⊕ Y) where
  decode m :=
    if m % 2 = 0 then (rX.decode (m / 2)).map Sum.inl
    else (rY.decode (m / 2)).map Sum.inr
  complete := by
    rintro (x | y)
    · obtain ⟨i, hi⟩ := rX.complete x
      refine ⟨2 * i, ?_⟩
      rw [if_pos (by omega)]
      have h2 : 2 * i / 2 = i := by omega
      rw [h2, hi]
      rfl
    · obtain ⟨j, hj⟩ := rY.complete y
      refine ⟨2 * j + 1, ?_⟩
      rw [if_neg (by omega)]
      have h2 : (2 * j + 1) / 2 = j := by omega
      rw [h2, hj]
      rfl

/-- Decidable restriction of a representation: keep the codes whose decoding
satisfies the (decidable) predicate. Distinction cuts along decidable
predicates, and this is the closure that fact licenses. -/
def Representation.subtype {X : Type u}
    (rX : Representation X) (p : X → Prop) [DecidablePred p] :
    Representation {x : X // p x} where
  decode n :=
    match rX.decode n with
    | some x => if h : p x then some ⟨x, h⟩ else none
    | none => none
  complete := by
    rintro ⟨x, hx⟩
    obtain ⟨n, hn⟩ := rX.complete x
    exact ⟨n, by simp [hn, dif_pos hx]⟩

theorem representable_prod {X : Type u} {Y : Type v}
    (hX : DeltaRepresentable X) (hY : DeltaRepresentable Y) :
    DeltaRepresentable (X × Y) := by
  obtain ⟨rX⟩ := hX
  obtain ⟨rY⟩ := hY
  exact ⟨rX.prod rY⟩

theorem representable_sum {X : Type u} {Y : Type v}
    (hX : DeltaRepresentable X) (hY : DeltaRepresentable Y) :
    DeltaRepresentable (X ⊕ Y) := by
  obtain ⟨rX⟩ := hX
  obtain ⟨rY⟩ := hY
  exact ⟨rX.sum rY⟩

theorem representable_subtype {X : Type u}
    (hX : DeltaRepresentable X) (p : X → Prop) [DecidablePred p] :
    DeltaRepresentable {x : X // p x} := by
  obtain ⟨rX⟩ := hX
  exact ⟨rX.subtype p⟩

/-! ### The diagonal at the definition (choice-free) -/

/-- **The diagonal hits the repaired definition.** The binary sequences carry
no covering decoder: given one, complement it on the diagonal and ask for the
diagonal's own code. Uses no choice and no excluded middle; the only case
analyses are on `Option` and `Bool`. -/
theorem not_representable_cantor : ¬ DeltaRepresentable (ℕ → Bool) := by
  rintro ⟨r⟩
  let g : ℕ → Bool := fun n =>
    match r.decode n with
    | some f => !(f n)
    | none => false
  obtain ⟨m, hm⟩ := r.complete g
  have hg : g m = !(g m) := by
    show (match r.decode m with
          | some f => !(f m)
          | none => false) = !(g m)
    rw [hm]
  cases hgm : g m <;> rw [hgm] at hg <;> simp at hg

/-- **Generalized diagonal-boundedness.** No type surveys its own binary
predicates: for every `X` there is no surjection `X → (X → Bool)`. Closure
under distinction never closes under self-description. Choice-free. -/
theorem no_self_survey {X : Type u} :
    ¬ ∃ f : X → (X → Bool), Function.Surjective f := by
  rintro ⟨f, hf⟩
  obtain ⟨m, hm⟩ := hf (fun x => !(f x x))
  have h := congrFun hm m
  simp at h

/-! ### The discrete bridge: decoders refine injections -/

/-- For a discrete type (decidable equality), a covering decoder yields the
least-code injection, via the choice-free `Nat.find`. So on the discrete
fragment the repaired notion refines the original `DeltaForced`. -/
theorem deltaForced_of_representable {X : Type u} [DecidableEq X]
    (h : DeltaRepresentable X) : DeltaForced X := by
  obtain ⟨r⟩ := h
  refine ⟨⟨fun x => Nat.find (r.complete x), ?_⟩⟩
  intro x y hxy
  have hxy' : Nat.find (r.complete x) = Nat.find (r.complete y) := hxy
  have hx := Nat.find_spec (r.complete x)
  have hy := Nat.find_spec (r.complete y)
  rw [hxy'] at hx
  exact Option.some.inj (hx.symm.trans hy)

/-! ### Classical bridges (quarantined; each is tagged classical)

Classically, representable = countable, and ℝ is not representable. The
constructive separation between "countable" and "carries a decoder" is
excluded middle / intensionality, not the axiom of choice; these bridges make
that precise by showing where the classical reasoning enters. -/

/-- A representable type is countable. Classical (uses `isEmpty_or_nonempty`
and the surjection-to-countable bridge). -/
theorem countable_of_representable {X : Type u}
    (h : DeltaRepresentable X) : Countable X := by
  obtain ⟨r⟩ := h
  rcases isEmpty_or_nonempty X with hE | hN
  · infer_instance
  · obtain ⟨x₀⟩ := hN
    have hsurj : Function.Surjective (fun n => (r.decode n).getD x₀) := by
      intro x
      obtain ⟨n, hn⟩ := r.complete x
      refine ⟨n, ?_⟩
      show (r.decode n).getD x₀ = x
      rw [hn]
      rfl
    exact hsurj.countable

/-- A countable type is representable. Classical (the decoder is built by
choice from the bare injection). With `countable_of_representable` this shows
the two notions coincide classically; constructively they separate, and the
separator is excluded middle, not choice. -/
theorem representable_of_countable {X : Type u} [Countable X] :
    DeltaRepresentable X := by
  classical
  rcases isEmpty_or_nonempty X with hE | hN
  · exact ⟨⟨fun _ => none, fun x => (hE.false x).elim⟩⟩
  · obtain ⟨f, hf⟩ := (inferInstance : Countable X).exists_injective_nat'
    refine ⟨⟨fun n => if h : ∃ x : X, f x = n then some h.choose else none, ?_⟩⟩
    intro x
    have hex : ∃ y : X, f y = f x := ⟨x, rfl⟩
    refine ⟨f x, ?_⟩
    show (if h : ∃ y : X, f y = f x then some h.choose else none) = some x
    rw [dif_pos hex]
    exact congrArg some (hf hex.choose_spec)

/-- The classical continuum is not representable (classical, via
countability). The choice-free content of the boundary is
`not_representable_cantor`; this corollary transports it to the display-tier
ℝ through the classical cardinality bridge. -/
theorem not_representable_real : ¬ DeltaRepresentable ℝ := by
  intro h
  have hc : Countable ℝ := countable_of_representable h
  have hle : Cardinal.mk ℝ ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.mpr hc
  rw [Cardinal.mk_real] at hle
  exact absurd hle (not_le.mpr Cardinal.aleph0_lt_continuum)

end Forced
end ActualMathematics

/-
  PrimitiveRecognitionCalculus/BornRuleQuadratic.lean

  Schema A, second rung: Born predictions with IRRATIONAL probabilities are
  still δ-forced, and the instrument still decides them by finite integer
  arithmetic.

  The first rung (BornRuleForced.lean) covered rational-presented amplitudes:
  weights and totals in ℤ, decisions by integer comparison. Its stated scope
  boundary was the Hadamard gate: amplitudes in ℤ[1/√2] (and Clifford+T
  circuits generally) produce Born weights in ℤ[√2], and individual outcome
  probabilities can be genuinely irrational. Example: the circuit H·T·H on
  |0⟩ gives outcome probabilities (2+√2)/4 and (2−√2)/4.

  This module closes that rung. The carrier is the quadratic ring ℤ[√2],
  represented as integer pairs (a, b) meaning a + b√2:

  * Ring operations are integer formulas; the prediction space (ℤ[√2])² is
    δ-forced by an explicit certificate (parity code + Cantor pairing).
  * The SIGN of a + b√2 is decided by integer comparisons: the sign algorithm
    compares a² against 2b² with the sign pattern of (a, b). Its correctness
    needs exactly one fact: x² = 2y² has no nonzero integer solutions, the
    irrationality of √2, proved here by parity descent (strong induction),
    choice-free. This is the honest kernel: deciding order in ℚ(√2) IS the
    place where irrationality does work.
  * Born weights |c|² = re² + im² land in the DOMINATED cone (rational part
    ≥ √2·|irrational part|, expressed as 0 ≤ a ∧ 2b² ≤ a²): squares are
    dominated ((a²−2b²)² ≥ 0 in disguise), and dominated elements are closed
    under addition (a Cauchy–Schwarz-style integer inequality). This gives
    nonnegativity, single ≤ total, and total > 0 with no real numbers.
  * The zero test on a weight is decidable pair equality; comparisons of two
    predictions cross-multiply in ℤ[√2] and read the sign algorithm. Both are
    finite computations (`decide`-able), so the conservativity pairing of the
    first rung extends verbatim: the instrument decides, the display charges
    WLPO/LPO (CalibrationOmniscience).
  * The worked Hadamard–T example is included and computed by the kernel:
    weights 8±4√2 over total 16, the irrational parts nonzero, the comparison
    decided.
  * A quarantined classical bridge (`isPos_iff_real`) certifies that the sign
    algorithm agrees with the real sign of a + b√2 on the displayed line. The
    agreement with the display is classical; the instrument-side decision
    itself is choice-free. That division is the paper's point, made formal.

  Axiom discipline: everything up to the classical-bridge section has profile
  ⊆ {propext, Quot.sound}. No project-local axioms. No sorry.
-/

import Mathlib
import ActualMathematics.DeltaForced
import ActualMathematics.Representability
import ActualMathematics.BornRuleForced
import ActualMathematics.CalibrationOmniscience

namespace ActualMathematics
namespace Born
namespace Quadratic

open Forced

/-! ## The carrier: ℤ[√2] as integer pairs -/

/-- An element of ℤ[√2]: the pair `(a, b)` means `a + b√2`. -/
structure Zsqrt2 where
  a : ℤ
  b : ℤ
deriving DecidableEq

/-- Component extensionality. -/
theorem Zsqrt2.ext' {z w : Zsqrt2} (ha : z.a = w.a) (hb : z.b = w.b) : z = w := by
  cases z with
  | mk za zb =>
    cases w with
    | mk wa wb =>
      simp only at ha hb
      subst ha
      subst hb
      rfl

def zero : Zsqrt2 := ⟨0, 0⟩
def one : Zsqrt2 := ⟨1, 0⟩
def sqrt2 : Zsqrt2 := ⟨0, 1⟩

def add (z w : Zsqrt2) : Zsqrt2 := ⟨z.a + w.a, z.b + w.b⟩
def neg (z : Zsqrt2) : Zsqrt2 := ⟨-z.a, -z.b⟩
def sub (z w : Zsqrt2) : Zsqrt2 := ⟨z.a - w.a, z.b - w.b⟩
def mul (z w : Zsqrt2) : Zsqrt2 :=
  ⟨z.a * w.a + 2 * (z.b * w.b), z.a * w.b + z.b * w.a⟩

theorem zero_iff {z : Zsqrt2} : z = zero ↔ z.a = 0 ∧ z.b = 0 := by
  constructor
  · intro h
    rw [h]
    exact ⟨rfl, rfl⟩
  · intro ⟨h1, h2⟩
    exact Zsqrt2.ext' h1 h2

/-- The generator squares to 2: `√2 · √2 = 2`. -/
theorem sqrt2_mul_sqrt2 : mul sqrt2 sqrt2 = ⟨2, 0⟩ := rfl

/-! ## The kernel fact: √2 is irrational (parity descent, choice-free) -/

/-- No positive natural solution to `x² = 2y²`: parity descent by strong
induction. The only case analyses are on `x % 2` (decidable) and the descent
is structural. Choice-free. -/
theorem nat_descent : ∀ x : ℕ, ∀ y : ℕ, x * x = 2 * (y * y) → x = 0 := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro y hxy
    by_cases hx0 : x = 0
    · exact hx0
    · exfalso
      have hpar : x % 2 = 0 ∨ x % 2 = 1 := by omega
      rcases hpar with hev | hod
      · -- x = 2m: then y² = 2m² and y < x, descend
        obtain ⟨m, hm⟩ : ∃ m, x = 2 * m := ⟨x / 2, by omega⟩
        have hmpos : 0 < m := by omega
        have hm1 : 1 ≤ m := hmpos
        have hmm1 : 1 ≤ m * m := by
          have := Nat.mul_le_mul hm1 hm1
          omega
        have hx2 : x * x = 4 * (m * m) := by rw [hm]; ring
        have hy2 : y * y = 2 * (m * m) := by omega
        have hylt : y < x := by
          rcases Nat.lt_or_ge y x with h | h
          · exact h
          · exfalso
            have := Nat.mul_le_mul h h
            omega
        have hy0 : y = 0 := ih y hylt m hy2
        rw [hy0] at hy2
        omega
      · -- x odd: x² is odd, 2y² is even
        obtain ⟨m, hm⟩ : ∃ m, x = 2 * m + 1 := ⟨x / 2, by omega⟩
        have hx2 : x * x = 4 * (m * m) + 4 * m + 1 := by rw [hm]; ring
        omega

/-- The integer form: `x² = 2y²` forces `x = y = 0`. Choice-free. -/
theorem int_descent {x y : ℤ} (h : x * x = 2 * (y * y)) : x = 0 ∧ y = 0 := by
  have h1 : ((x.natAbs * x.natAbs : ℕ) : ℤ) = x * x := Int.natAbs_mul_self
  have h2 : ((y.natAbs * y.natAbs : ℕ) : ℤ) = y * y := Int.natAbs_mul_self
  have hnat : x.natAbs * x.natAbs = 2 * (y.natAbs * y.natAbs) := by omega
  have hx0 : x.natAbs = 0 := nat_descent x.natAbs y.natAbs hnat
  have hy0 : y.natAbs = 0 := by
    rw [hx0] at hnat
    rcases Nat.eq_zero_or_pos y.natAbs with h0 | hpos
    · exact h0
    · exfalso
      have h1' : 1 ≤ y.natAbs := hpos
      have := Nat.mul_le_mul h1' h1'
      omega
  omega

/-! ## The sign algorithm -/

/-- `0 < a + b√2`, decided by integer comparisons. The three disjuncts are the
sign patterns of `(a, b)`: both nonnegative (not both zero); positive rational
part beating a negative irrational part (`2b² < a²`); positive irrational part
beating a negative rational part (`a² < 2b²`). Correctness against the real
line is `isPos_iff_real` (classical bridge, end of file); the exhaustiveness
and exclusivity below are choice-free, with the descent lemma refuting the
boundary `a² = 2b²`. -/
def IsPos (z : Zsqrt2) : Prop :=
  (0 ≤ z.a ∧ 0 ≤ z.b ∧ ¬(z.a = 0 ∧ z.b = 0)) ∨
  (0 < z.a ∧ z.b < 0 ∧ 2 * (z.b * z.b) < z.a * z.a) ∨
  (z.a < 0 ∧ 0 < z.b ∧ z.a * z.a < 2 * (z.b * z.b))

instance isPos_decidable (z : Zsqrt2) : Decidable (IsPos z) := by
  unfold IsPos
  infer_instance

/-- `0 ≤ a + b√2`: positive or zero. -/
def IsNonneg (z : Zsqrt2) : Prop := IsPos z ∨ z = zero

theorem isPos_zero_false : ¬ IsPos zero := by decide

/-- **Sign trichotomy, decided.** Every element of ℤ[√2] is positive, zero, or
has positive negation, by integer computation. The boundary case `a² = 2b²`
with `(a,b) ≠ 0` is refuted by the descent lemma: this is exactly where the
irrationality of √2 enters the instrument's arithmetic. Choice-free. -/
theorem sign_trichotomy (z : Zsqrt2) : IsPos z ∨ z = zero ∨ IsPos (neg z) := by
  have ena : (-z.a) * (-z.a) = z.a * z.a := by ring
  have enb : (-z.b) * (-z.b) = z.b * z.b := by ring
  by_cases hb0 : z.b = 0
  · by_cases ha0 : z.a = 0
    · exact Or.inr (Or.inl (zero_iff.mpr ⟨ha0, hb0⟩))
    · by_cases hapos : 0 < z.a
      · exact Or.inl (Or.inl ⟨by omega, by omega, by omega⟩)
      · refine Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))
        · show (0 : ℤ) ≤ -z.a
          omega
        · show (0 : ℤ) ≤ -z.b
          omega
        · show ¬(-z.a = 0 ∧ -z.b = 0)
          omega
  · by_cases hbpos : 0 < z.b
    · by_cases ha : 0 ≤ z.a
      · exact Or.inl (Or.inl ⟨ha, by omega, by omega⟩)
      · -- a < 0, b > 0: compare a² with 2b²
        by_cases hlt : z.a * z.a < 2 * (z.b * z.b)
        · exact Or.inl (Or.inr (Or.inr ⟨by omega, hbpos, hlt⟩))
        · by_cases heq : z.a * z.a = 2 * (z.b * z.b)
          · exact absurd (int_descent heq).2 hb0
          · -- 2b² < a²: the negation is positive (second pattern)
            refine Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩)))
            · show (0 : ℤ) < -z.a
              omega
            · show -z.b < (0 : ℤ)
              omega
            · show 2 * ((-z.b) * (-z.b)) < (-z.a) * (-z.a)
              rw [ena, enb]
              omega
    · -- b < 0
      by_cases ha : z.a ≤ 0
      · refine Or.inr (Or.inr (Or.inl ⟨?_, ?_, ?_⟩))
        · show (0 : ℤ) ≤ -z.a
          omega
        · show (0 : ℤ) ≤ -z.b
          omega
        · show ¬(-z.a = 0 ∧ -z.b = 0)
          omega
      · -- a > 0, b < 0: compare 2b² with a²
        by_cases hlt : 2 * (z.b * z.b) < z.a * z.a
        · exact Or.inl (Or.inr (Or.inl ⟨by omega, by omega, hlt⟩))
        · by_cases heq : z.a * z.a = 2 * (z.b * z.b)
          · exact absurd (int_descent heq).1 (by omega)
          · -- a² < 2b²: the negation is positive (third pattern)
            refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, ?_, ?_⟩)))
            · show -z.a < (0 : ℤ)
              omega
            · show (0 : ℤ) < -z.b
              omega
            · show (-z.a) * (-z.a) < 2 * ((-z.b) * (-z.b))
              rw [ena, enb]
              omega

/-- Positivity excludes positive negation (the trichotomy is exact).
Choice-free. -/
theorem isPos_neg_exclusive (z : Zsqrt2) : IsPos z → IsPos (neg z) → False := by
  intro h1 h2
  have hna : (neg z).a = -z.a := rfl
  have hnb : (neg z).b = -z.b := rfl
  rw [IsPos, hna, hnb] at h2
  have ena : (-z.a) * (-z.a) = z.a * z.a := by ring
  have enb : (-z.b) * (-z.b) = z.b * z.b := by ring
  rw [ena, enb] at h2
  rcases h1 with ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ | ⟨p1, p2, p3⟩ <;>
    rcases h2 with ⟨q1, q2, q3⟩ | ⟨q1, q2, q3⟩ | ⟨q1, q2, q3⟩ <;> omega

/-! ## The dominated cone: where Born weights live -/

/-- The rational part dominates: `0 ≤ a` and `2b² ≤ a²` (i.e. `a ≥ √2·|b|`).
Every Born weight lands here; the cone is closed under addition and implies
nonnegativity. -/
def Dominates (z : Zsqrt2) : Prop :=
  0 ≤ z.a ∧ 2 * (z.b * z.b) ≤ z.a * z.a

theorem dominates_zero : Dominates zero := by
  constructor <;> simp [zero]

/-- Squares are dominated: `(a + b√2)²` has rational part `a² + 2b²` and
irrational part `2ab`, and `2(2ab)² ≤ (a² + 2b²)²` is `(a² − 2b²)² ≥ 0` in
disguise. Choice-free. -/
theorem sq_dominates (z : Zsqrt2) : Dominates (mul z z) := by
  have h1 : (mul z z).a = z.a * z.a + 2 * (z.b * z.b) := rfl
  have h2 : (mul z z).b = z.a * z.b + z.b * z.a := rfl
  constructor
  · rw [h1]
    have := sq_nonneg_int z.a
    have := sq_nonneg_int z.b
    omega
  · rw [h1, h2]
    have key : 0 ≤ (z.a * z.a - 2 * (z.b * z.b)) * (z.a * z.a - 2 * (z.b * z.b)) :=
      sq_nonneg_int _
    have e1 : (z.a * z.a + 2 * (z.b * z.b)) * (z.a * z.a + 2 * (z.b * z.b))
        = (z.a * z.a - 2 * (z.b * z.b)) * (z.a * z.a - 2 * (z.b * z.b))
          + 8 * ((z.a * z.b) * (z.a * z.b)) := by ring
    have e2 : 2 * ((z.a * z.b + z.b * z.a) * (z.a * z.b + z.b * z.a))
        = 8 * ((z.a * z.b) * (z.a * z.b)) := by ring
    omega

/-- From `q² ≤ p²` with `0 ≤ p` and `0 < q`, conclude `q ≤ p`. Choice-free
square-root comparison at the integer level. -/
theorem le_of_sq_le_sq {p q : ℤ} (hp : 0 ≤ p) (h : q * q ≤ p * p) (hq : 0 < q) :
    q ≤ p := by
  rcases Int.lt_or_le p q with hlt | hle
  · exfalso
    have h1 : p * p ≤ p * q := Int.mul_le_mul_of_nonneg_left (le_of_lt hlt) hp
    have h2 : p * q < q * q := Int.mul_lt_mul_of_pos_right hlt hq
    omega
  · exact hle

/-- The dominated cone is closed under addition. The cross-term estimate
`2·b₁b₂ ≤ a₁a₂` is the integer Cauchy–Schwarz step, derived from the two
dominance hypotheses by squaring. Choice-free. -/
theorem dominates_add {z w : Zsqrt2} (hz : Dominates z) (hw : Dominates w) :
    Dominates (add z w) := by
  obtain ⟨ha1, hd1⟩ := hz
  obtain ⟨ha2, hd2⟩ := hw
  have hadda : (add z w).a = z.a + w.a := rfl
  have haddb : (add z w).b = z.b + w.b := rfl
  have hb1 : 0 ≤ 2 * (z.b * z.b) := by
    have := sq_nonneg_int z.b
    omega
  have hbb2 : 0 ≤ 2 * (w.b * w.b) := by
    have := sq_nonneg_int w.b
    omega
  have haa1 : 0 ≤ z.a * z.a := sq_nonneg_int z.a
  -- (2 b₁b₂)² = (2b₁²)(2b₂²)·... ≤ (a₁²)(a₂²) = (a₁a₂)²
  have hsq : (2 * (z.b * w.b)) * (2 * (z.b * w.b)) ≤ (z.a * w.a) * (z.a * w.a) := by
    have hmul : (2 * (z.b * z.b)) * (2 * (w.b * w.b)) ≤ (z.a * z.a) * (w.a * w.a) :=
      Int.mul_le_mul hd1 hd2 hbb2 haa1
    have e1 : (2 * (z.b * w.b)) * (2 * (z.b * w.b))
        = (2 * (z.b * z.b)) * (2 * (w.b * w.b)) := by ring
    have e2 : (z.a * w.a) * (z.a * w.a) = (z.a * z.a) * (w.a * w.a) := by ring
    omega
  have hP : 0 ≤ z.a * w.a := Int.mul_nonneg ha1 ha2
  have hcross : 2 * (z.b * w.b) ≤ z.a * w.a := by
    rcases Int.lt_or_le 0 (2 * (z.b * w.b)) with hpos | hnonpos
    · exact le_of_sq_le_sq hP hsq hpos
    · omega
  constructor
  · rw [hadda]; omega
  · rw [hadda, haddb]
    have e3 : (z.a + w.a) * (z.a + w.a)
        = z.a * z.a + 2 * (z.a * w.a) + w.a * w.a := by ring
    have e4 : 2 * ((z.b + w.b) * (z.b + w.b))
        = 2 * (z.b * z.b) + 4 * (z.b * w.b) + 2 * (w.b * w.b) := by ring
    omega

/-- A dominated element and its negation are both dominated only at zero. -/
theorem eq_zero_of_dominates_both {z : Zsqrt2}
    (h1 : Dominates z) (h2 : Dominates (neg z)) : z = zero := by
  obtain ⟨ha1, _⟩ := h1
  obtain ⟨ha2, hd2⟩ := h2
  have hna : (neg z).a = -z.a := rfl
  have hnb : (neg z).b = -z.b := rfl
  have ha0 : z.a = 0 := by rw [hna] at ha2; omega
  have hbb : z.b * z.b = 0 := by
    have ena : (neg z).a * (neg z).a = z.a * z.a := by rw [hna]; ring
    have enb : (neg z).b * (neg z).b = z.b * z.b := by rw [hnb]; ring
    have := sq_nonneg_int z.b
    rw [ena, enb, ha0] at hd2
    omega
  exact zero_iff.mpr ⟨ha0, mul_self_eq_zero_int hbb⟩

/-- Nonzero dominated elements are positive. The strictness at the boundary
`2b² = a²` is refuted by the descent lemma. Choice-free. -/
theorem isPos_of_dominates_ne_zero {z : Zsqrt2}
    (h : Dominates z) (hz : z ≠ zero) : IsPos z := by
  obtain ⟨ha, hd⟩ := h
  by_cases ha0 : z.a = 0
  · exfalso
    have hbb : z.b * z.b = 0 := by
      have := sq_nonneg_int z.b
      rw [ha0] at hd
      omega
    exact hz (zero_iff.mpr ⟨ha0, mul_self_eq_zero_int hbb⟩)
  · by_cases hb : 0 ≤ z.b
    · exact Or.inl ⟨ha, hb, fun ⟨h1, _⟩ => ha0 h1⟩
    · -- b < 0: need strict 2b² < a²
      by_cases heq : z.a * z.a = 2 * (z.b * z.b)
      · exact absurd (int_descent heq).1 ha0
      · exact Or.inr (Or.inl ⟨by omega, by omega, by omega⟩)

theorem isNonneg_of_dominates {z : Zsqrt2} (h : Dominates z) : IsNonneg z := by
  by_cases hz : z = zero
  · exact Or.inr hz
  · exact Or.inl (isPos_of_dominates_ne_zero h hz)

/-! ## Amplitudes and weights over ℤ[√2] -/

/-- A Gaussian-ℤ[√2] amplitude: real and imaginary parts in ℤ[√2]. These are
the amplitude numerators of Clifford+T states over a common power-of-√2
denominator (which cancels in every probability). -/
structure QAmp where
  re : Zsqrt2
  im : Zsqrt2
deriving DecidableEq

/-- The Born weight `|c|² = re² + im²`, an exact element of ℤ[√2]. -/
def qnormSq (c : QAmp) : Zsqrt2 := add (mul c.re c.re) (mul c.im c.im)

/-- Weights are dominated: sum of two dominated squares. -/
theorem qnormSq_dominates (c : QAmp) : Dominates (qnormSq c) :=
  dominates_add (sq_dominates c.re) (sq_dominates c.im)

/-- The weight vanishes exactly when the amplitude does. Choice-free. -/
theorem qnormSq_eq_zero_iff (c : QAmp) :
    qnormSq c = zero ↔ c.re = zero ∧ c.im = zero := by
  constructor
  · intro h
    have hcomp := zero_iff.mp h
    have ha : (qnormSq c).a
        = c.re.a * c.re.a + 2 * (c.re.b * c.re.b)
          + (c.im.a * c.im.a + 2 * (c.im.b * c.im.b)) := rfl
    have h1 := sq_nonneg_int c.re.a
    have h2 := sq_nonneg_int c.re.b
    have h3 := sq_nonneg_int c.im.a
    have h4 := sq_nonneg_int c.im.b
    have hra : c.re.a * c.re.a = 0 := by omega
    have hrb : c.re.b * c.re.b = 0 := by omega
    have hia : c.im.a * c.im.a = 0 := by omega
    have hib : c.im.b * c.im.b = 0 := by omega
    exact ⟨zero_iff.mpr ⟨mul_self_eq_zero_int hra, mul_self_eq_zero_int hrb⟩,
           zero_iff.mpr ⟨mul_self_eq_zero_int hia, mul_self_eq_zero_int hib⟩⟩
  · intro ⟨h1, h2⟩
    have : c = ⟨zero, zero⟩ := by
      cases c with
      | mk re im =>
        simp only at h1 h2
        rw [h1, h2]
    rw [this]
    rfl

/-! ## Finite outcome sums (structural recursion, as in the first rung) -/

/-- The total of a finite family in ℤ[√2]. -/
def qtotal : (n : ℕ) → (Fin n → Zsqrt2) → Zsqrt2
  | 0, _ => zero
  | n + 1, w => add (w ⟨0, Nat.succ_pos n⟩) (qtotal n (fun i => w i.succ))

theorem qtotal_dominates :
    ∀ (n : ℕ) (w : Fin n → Zsqrt2), (∀ k, Dominates (w k)) →
      Dominates (qtotal n w) := by
  intro n
  induction n with
  | zero => intro w _; exact dominates_zero
  | succ m ih =>
      intro w hw
      exact dominates_add (hw ⟨0, Nat.succ_pos m⟩)
        (ih (fun i => w i.succ) (fun k => hw k.succ))

/-- Cancellation: `(z + w) − z = w`. -/
theorem sub_add_cancel_left (z w : Zsqrt2) : sub (add z w) z = w :=
  Zsqrt2.ext' (by show z.a + w.a - z.a = w.a; omega)
    (by show z.b + w.b - z.b = w.b; omega)

/-- Rearrangement: `(x + y) − z = x + (y − z)`. -/
theorem sub_add_comm (x y z : Zsqrt2) : sub (add x y) z = add x (sub y z) :=
  Zsqrt2.ext' (by show x.a + y.a - z.a = x.a + (y.a - z.a); omega)
    (by show x.b + y.b - z.b = x.b + (y.b - z.b); omega)

/-- `0 − z = −z`. -/
theorem sub_zero_left (z : Zsqrt2) : sub zero z = neg z :=
  Zsqrt2.ext' (by show (0 : ℤ) - z.a = -z.a; omega)
    (by show (0 : ℤ) - z.b = -z.b; omega)

/-- The total minus any single term is dominated (the sum of the remaining
dominated terms). This is `p_k ≤ 1` cross-multiplied, in cone form. -/
theorem qtotal_sub_dominates :
    ∀ (n : ℕ) (w : Fin n → Zsqrt2), (∀ k, Dominates (w k)) →
      ∀ k, Dominates (sub (qtotal n w) (w k)) := by
  intro n
  induction n with
  | zero => intro w _ k; exact absurd k.2 (by omega)
  | succ m ih =>
      intro w hw k
      rcases Nat.eq_zero_or_pos k.val with h0 | hpos
      · have hk : k = ⟨0, Nat.succ_pos m⟩ := Fin.ext h0
        subst hk
        show Dominates (sub (add (w ⟨0, Nat.succ_pos m⟩) (qtotal m fun i => w i.succ))
          (w ⟨0, Nat.succ_pos m⟩))
        rw [sub_add_cancel_left]
        exact qtotal_dominates m _ (fun j => hw j.succ)
      · have hj : k.val - 1 < m := by omega
        have hk : k = (⟨k.val - 1, hj⟩ : Fin m).succ := by
          apply Fin.ext
          show k.val = (k.val - 1) + 1
          omega
        rw [hk]
        show Dominates (sub (add (w ⟨0, Nat.succ_pos m⟩) (qtotal m fun i => w i.succ))
          (w (⟨k.val - 1, hj⟩ : Fin m).succ))
        rw [sub_add_comm]
        exact dominates_add (hw ⟨0, Nat.succ_pos m⟩)
          (ih (fun i => w i.succ) (fun j => hw j.succ) ⟨k.val - 1, hj⟩)

/-- A dominated family whose total vanishes has every term zero (used for
positivity of the total). -/
theorem term_eq_zero_of_qtotal_eq_zero {n : ℕ} {w : Fin n → Zsqrt2}
    (hw : ∀ k, Dominates (w k)) (h : qtotal n w = zero) (k : Fin n) :
    w k = zero := by
  have hd := qtotal_sub_dominates n w hw k
  rw [h, sub_zero_left] at hd
  exact eq_zero_of_dominates_both (hw k) hd

/-! ## The Born setup over ℤ[√2] -/

/-- A finite-dimensional Born measurement with ℤ[√2]-presented data (the
Clifford+T amplitude ring over a cancelled power-of-√2 denominator), with at
least one nonzero amplitude. -/
structure Setup (n : ℕ) where
  amp : Fin n → QAmp
  witness : Fin n
  nondegenerate : qnormSq (amp witness) ≠ zero

def weight {n : ℕ} (s : Setup n) (k : Fin n) : Zsqrt2 := qnormSq (s.amp k)

def totalWeight {n : ℕ} (s : Setup n) : Zsqrt2 := qtotal n (weight s)

/-- The Born prediction for outcome `k`: the exact pair `(w_k, T)` in ℤ[√2],
representing the (possibly irrational) probability `w_k / T`. -/
def prediction {n : ℕ} (s : Setup n) (k : Fin n) : Zsqrt2 × Zsqrt2 :=
  (weight s k, totalWeight s)

theorem weight_dominates {n : ℕ} (s : Setup n) (k : Fin n) :
    Dominates (weight s k) :=
  qnormSq_dominates (s.amp k)

theorem weight_nonneg {n : ℕ} (s : Setup n) (k : Fin n) : IsNonneg (weight s k) :=
  isNonneg_of_dominates (weight_dominates s k)

/-- Cross-multiplied `p_k ≤ 1`: the total minus any weight is nonnegative. -/
theorem weight_le_total {n : ℕ} (s : Setup n) (k : Fin n) :
    IsNonneg (sub (totalWeight s) (weight s k)) :=
  isNonneg_of_dominates
    (qtotal_sub_dominates n (weight s) (fun j => weight_dominates s j) k)

/-- The state has positive squared norm: `0 < T` in ℤ[√2], decided by the
sign algorithm. -/
theorem total_pos {n : ℕ} (s : Setup n) : IsPos (totalWeight s) := by
  refine isPos_of_dominates_ne_zero
    (qtotal_dominates n (weight s) (fun j => weight_dominates s j)) ?_
  intro h
  exact s.nondegenerate
    (term_eq_zero_of_qtotal_eq_zero (fun j => weight_dominates s j) h s.witness)

/-- **Exact normalization**: `Σ_k w_k = T` by definition, an identity of
ℤ[√2] bookkeeping, not a limit. -/
theorem sum_exact {n : ℕ} (s : Setup n) : qtotal n (weight s) = totalWeight s := rfl

/-! ## The prediction space is forced -/

/-- Certificate for ℤ[√2]: parity-code each integer component, pair. -/
def zsqrt2ToNat (z : Zsqrt2) : ℕ := dpair (intToNat z.a) (intToNat z.b)

theorem zsqrt2ToNat_inj : Function.Injective zsqrt2ToNat := by
  intro z w h
  obtain ⟨h1, h2⟩ := dpair_inj2 h
  exact Zsqrt2.ext' (intToNat_inj h1) (intToNat_inj h2)

/-- Certificate for prediction pairs. -/
def qpredToNat (p : Zsqrt2 × Zsqrt2) : ℕ := dpair (zsqrt2ToNat p.1) (zsqrt2ToNat p.2)

theorem qpredToNat_inj : Function.Injective qpredToNat := by
  rintro ⟨x1, y1⟩ ⟨x2, y2⟩ h
  obtain ⟨h1, h2⟩ := dpair_inj2 h
  have e1 : x1 = x2 := zsqrt2ToNat_inj h1
  have e2 : y1 = y2 := zsqrt2ToNat_inj h2
  rw [e1, e2]

/-- **The quadratic Born prediction space is δ-forced** by an explicit
choice-free certificate: irrational Born probabilities are still forced
objects. -/
theorem quadPrediction_forced : DeltaForced (Zsqrt2 × Zsqrt2) :=
  ⟨⟨qpredToNat, qpredToNat_inj⟩⟩

/-! ## Instrument decisions are finite computations -/

/-- **The exact-zero test on a quadratic Born prediction is decided** by pair
equality on ℤ (kernel-computable). -/
theorem zero_test_decided {n : ℕ} (s : Setup n) (k : Fin n) :
    weight s k = zero ∨ weight s k ≠ zero := by
  rcases instDecidableEqZsqrt2 (weight s k) zero with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- The zero test reads the recorded amplitude exactly. -/
theorem zero_iff_amp_zero {n : ℕ} (s : Setup n) (k : Fin n) :
    weight s k = zero ↔ (s.amp k).re = zero ∧ (s.amp k).im = zero :=
  qnormSq_eq_zero_iff (s.amp k)

/-- **Comparison of two quadratic Born predictions is decided.** Cross-multiply
in ℤ[√2] and read the sign algorithm; the descent lemma guarantees the three
cases are exhaustive. A finite computation on integers, though the compared
probabilities are irrational reals on the display. -/
theorem comparison_decided {n m : ℕ} (s : Setup n) (t : Setup m)
    (k : Fin n) (l : Fin m) :
    IsPos (sub (mul (weight s k) (totalWeight t)) (mul (weight t l) (totalWeight s)))
      ∨ sub (mul (weight s k) (totalWeight t)) (mul (weight t l) (totalWeight s)) = zero
      ∨ IsPos (neg (sub (mul (weight s k) (totalWeight t))
          (mul (weight t l) (totalWeight s)))) :=
  sign_trichotomy _

/-! ## The worked instance: the Hadamard–T circuit -/

/-- The state `H·T·H|0⟩`: amplitude numerators `(2+√2) + √2·i` and
`(2−√2) − √2·i` over the common denominator 4. Its Born probabilities are
`(2+√2)/4` and `(2−√2)/4`, both irrational. -/
def hadamardT : Setup 2 where
  amp := fun k =>
    if k.val = 0 then ⟨⟨2, 1⟩, ⟨0, 1⟩⟩ else ⟨⟨2, -1⟩, ⟨0, -1⟩⟩
  witness := ⟨0, by omega⟩
  nondegenerate := by decide

/-- The weights compute to `8 + 4√2` and `8 − 4√2` over total `16`: exact
ℤ[√2] bookkeeping, kernel-checked. -/
theorem hadamardT_weights :
    weight hadamardT ⟨0, by omega⟩ = ⟨8, 4⟩
      ∧ weight hadamardT ⟨1, by omega⟩ = ⟨8, -4⟩
      ∧ totalWeight hadamardT = ⟨16, 0⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The irrational parts of the weights are nonzero: these Born probabilities
are genuinely outside the first rung's rational scope. -/
theorem hadamardT_irrational_parts :
    (weight hadamardT ⟨0, by omega⟩).b ≠ 0
      ∧ (weight hadamardT ⟨1, by omega⟩).b ≠ 0 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- The instrument decides the comparison `p₀ > p₁` by integer arithmetic:
the cross-multiplied difference is `128·√2`, and the sign algorithm reads it
positive. Kernel-checked. -/
theorem hadamardT_comparison_decided :
    IsPos (sub (mul (weight hadamardT ⟨0, by omega⟩) (totalWeight hadamardT))
      (mul (weight hadamardT ⟨1, by omega⟩) (totalWeight hadamardT))) := by
  decide

/-! ## The conservativity certificate, second rung -/

/-- **Operational δ-conservativity, quadratic instance.** Born predictions
over the Clifford+T amplitude ring: the prediction space is δ-forced; the
predictions form an exact probability vector in ℤ[√2]; zero tests and
comparisons are decided by finite integer computation (with the √2 descent
supplying exactness of the sign trichotomy); and the same decisions referred
to the displayed continuum charge WLPO and LPO. Irrationality of the
displayed probability does not move the boundary: the instrument still never
pays. -/
structure QuadConservativityCert : Prop where
  prediction_space_forced : DeltaForced (Zsqrt2 × Zsqrt2)
  nonneg : ∀ {n : ℕ} (s : Setup n) (k : Fin n), IsNonneg (weight s k)
  le_one : ∀ {n : ℕ} (s : Setup n) (k : Fin n),
    IsNonneg (sub (totalWeight s) (weight s k))
  total_pos : ∀ {n : ℕ} (s : Setup n), IsPos (totalWeight s)
  sum_exact : ∀ {n : ℕ} (s : Setup n), qtotal n (weight s) = totalWeight s
  zero_test_decided : ∀ {n : ℕ} (s : Setup n) (k : Fin n),
    weight s k = zero ∨ weight s k ≠ zero
  comparison_decided : ∀ {n m : ℕ} (s : Setup n) (t : Setup m) (k : Fin n) (l : Fin m),
    IsPos (sub (mul (weight s k) (totalWeight t)) (mul (weight t l) (totalWeight s)))
      ∨ sub (mul (weight s k) (totalWeight t)) (mul (weight t l) (totalWeight s)) = zero
      ∨ IsPos (neg (sub (mul (weight s k) (totalWeight t))
          (mul (weight t l) (totalWeight s))))
  display_zero_test_wlpo :
    (∀ x : Calibration.CReal, Calibration.EqZero x ∨ ¬ Calibration.EqZero x) →
      Omniscience.WLPO
  display_trichotomy_lpo :
    (∀ x : Calibration.CReal,
        Calibration.Pos x ∨ Calibration.EqZero x ∨ Calibration.Neg x) →
      Omniscience.LPO

/-- The certificate holds, choice-free. -/
theorem quadConservativityCert_holds : QuadConservativityCert where
  prediction_space_forced := quadPrediction_forced
  nonneg := fun s k => weight_nonneg s k
  le_one := fun s k => weight_le_total s k
  total_pos := fun s => total_pos s
  sum_exact := fun s => sum_exact s
  zero_test_decided := fun s k => zero_test_decided s k
  comparison_decided := fun s t k l => comparison_decided s t k l
  display_zero_test_wlpo := Calibration.calib_exact_zero_imp_wlpo
  display_trichotomy_lpo := Calibration.calib_trichotomy_imp_lpo

/-! ## Classical bridge (quarantined): the sign algorithm reads the real sign

Everything above decides sign by integer arithmetic. This section certifies,
classically, that the algorithm agrees with the order of the displayed real
number `a + b√2`. The agreement with the DISPLAY is classical (it mentions ℝ);
the instrument-side decision itself is choice-free. That division of labor is
the paper's demarcation, made formal inside one file. -/

/-- The displayed real value of `z`. Classical (mentions `ℝ`). -/
noncomputable def toReal (z : Zsqrt2) : ℝ := (z.a : ℝ) + (z.b : ℝ) * Real.sqrt 2

/-- Forward half of the bridge: the algorithm's yes is the real line's yes. -/
theorem toReal_pos_of_isPos {z : Zsqrt2} (h : IsPos z) : 0 < toReal z := by
  have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have hspos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · -- both nonnegative, not both zero
    unfold toReal
    by_cases ha0 : z.a = 0
    · have hb : 0 < z.b := by
        rcases Int.lt_or_le 0 z.b with h | h
        · exact h
        · exact absurd ⟨ha0, by omega⟩ h3
      have hbr : (0 : ℝ) < (z.b : ℝ) := by exact_mod_cast hb
      have := mul_pos hbr hspos
      have har : ((z.a : ℤ) : ℝ) = 0 := by exact_mod_cast ha0
      rw [har]
      linarith
    · have ha : 0 < z.a := by omega
      have har : (0 : ℝ) < (z.a : ℝ) := by exact_mod_cast ha
      have hbr : (0 : ℝ) ≤ (z.b : ℝ) := by exact_mod_cast h2
      have := mul_nonneg hbr hs0
      linarith
  · -- a > 0, b < 0, 2b² < a²
    unfold toReal
    have har : (0 : ℝ) < (z.a : ℝ) := by exact_mod_cast h1
    have hbr : (z.b : ℝ) < 0 := by exact_mod_cast h2
    have hlt : 2 * ((z.b : ℝ) * (z.b : ℝ)) < (z.a : ℝ) * (z.a : ℝ) := by
      exact_mod_cast h3
    by_contra hle
    push_neg at hle
    -- a ≤ −b√2, both nonneg; square
    have hnb : (0 : ℝ) < -(z.b : ℝ) * Real.sqrt 2 := by
      have : (0 : ℝ) < -(z.b : ℝ) := by linarith
      exact mul_pos this hspos
    have hcmp : (z.a : ℝ) ≤ -(z.b : ℝ) * Real.sqrt 2 := by linarith
    have hsq : (z.a : ℝ) * (z.a : ℝ)
        ≤ (-(z.b : ℝ) * Real.sqrt 2) * (-(z.b : ℝ) * Real.sqrt 2) :=
      mul_self_le_mul_self (le_of_lt har) hcmp
    have hexp : (-(z.b : ℝ) * Real.sqrt 2) * (-(z.b : ℝ) * Real.sqrt 2)
        = 2 * ((z.b : ℝ) * (z.b : ℝ)) := by
      have : (-(z.b : ℝ) * Real.sqrt 2) * (-(z.b : ℝ) * Real.sqrt 2)
          = ((z.b : ℝ) * (z.b : ℝ)) * (Real.sqrt 2 * Real.sqrt 2) := by ring
      rw [this, hs2]
      ring
    rw [hexp] at hsq
    linarith
  · -- a < 0, b > 0, a² < 2b²
    unfold toReal
    have har : (z.a : ℝ) < 0 := by exact_mod_cast h1
    have hbr : (0 : ℝ) < (z.b : ℝ) := by exact_mod_cast h2
    have hlt : (z.a : ℝ) * (z.a : ℝ) < 2 * ((z.b : ℝ) * (z.b : ℝ)) := by
      exact_mod_cast h3
    by_contra hle
    push_neg at hle
    -- b√2 ≤ −a, both nonneg; square
    have hbs : (0 : ℝ) < (z.b : ℝ) * Real.sqrt 2 := mul_pos hbr hspos
    have hcmp : (z.b : ℝ) * Real.sqrt 2 ≤ -(z.a : ℝ) := by linarith
    have hsq : ((z.b : ℝ) * Real.sqrt 2) * ((z.b : ℝ) * Real.sqrt 2)
        ≤ (-(z.a : ℝ)) * (-(z.a : ℝ)) :=
      mul_self_le_mul_self (le_of_lt hbs) hcmp
    have hexp : ((z.b : ℝ) * Real.sqrt 2) * ((z.b : ℝ) * Real.sqrt 2)
        = 2 * ((z.b : ℝ) * (z.b : ℝ)) := by
      have : ((z.b : ℝ) * Real.sqrt 2) * ((z.b : ℝ) * Real.sqrt 2)
          = ((z.b : ℝ) * (z.b : ℝ)) * (Real.sqrt 2 * Real.sqrt 2) := by ring
      rw [this, hs2]
      ring
    have hexp2 : (-(z.a : ℝ)) * (-(z.a : ℝ)) = (z.a : ℝ) * (z.a : ℝ) := by ring
    rw [hexp, hexp2] at hsq
    linarith

/-- The displayed value of the negation is the negated value. -/
theorem toReal_neg (z : Zsqrt2) : toReal (neg z) = -(toReal z) := by
  unfold toReal
  have hna : ((neg z).a : ℝ) = -(z.a : ℝ) := by
    show ((-z.a : ℤ) : ℝ) = -(z.a : ℝ)
    push_cast
    ring
  have hnb : ((neg z).b : ℝ) = -(z.b : ℝ) := by
    show ((-z.b : ℤ) : ℝ) = -(z.b : ℝ)
    push_cast
    ring
  rw [hna, hnb]
  ring

/-- The sign algorithm agrees with the real sign. Classical bridge. -/
theorem isPos_iff_real (z : Zsqrt2) : IsPos z ↔ 0 < toReal z := by
  constructor
  · exact toReal_pos_of_isPos
  · intro hval
    rcases sign_trichotomy z with hp | h0 | hn
    · exact hp
    · exfalso
      rw [h0] at hval
      have hz : toReal zero = 0 := by
        show ((0 : ℤ) : ℝ) + ((0 : ℤ) : ℝ) * Real.sqrt 2 = 0
        norm_num
      rw [hz] at hval
      exact lt_irrefl 0 hval
    · exfalso
      have hnegpos : 0 < toReal (neg z) := toReal_pos_of_isPos hn
      rw [toReal_neg] at hnegpos
      linarith

end Quadratic
end Born
end ActualMathematics

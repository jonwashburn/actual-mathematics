/-
  PrimitiveRecognitionCalculus/BornRuleForced.lean

  The first worked instance of the OPERATIONAL δ-CONSERVATIVITY converse:
  finite-dimensional Born-rule predictions are δ-forced, choice-free.

  The demarcation program prices the continuum: its order decisions each cost
  an omniscience principle (CalibrationOmniscience: exact-zero test = WLPO,
  trichotomy = LPO, dichotomy = LLPO). That is the FORWARD direction: the
  model layer is expensive. The converse direction, the one that turns the
  demarcation from a definition into physics, is that the INSTRUMENT layer
  never pays: every finite instrumented prediction is δ-forced, and the
  decisions physics actually performs on predictions (is this probability
  zero? which of two probabilities is larger?) are finite computations, not
  omniscience. This module proves the first schema instance.

  The setup. A finite-dimensional quantum measurement with rational-presented
  data: amplitudes are Gaussian rationals presented as Gaussian-integer
  numerators over a common denominator (the denominator cancels in every
  probability, so it never appears). The Born weight of outcome k is
  |c_k|^2 = re^2 + im^2, an integer; the total weight T is their sum; the
  Born probability of outcome k is the exact rational pair (w_k, T). This
  covers any state reachable from rational data by Gaussian-rational gates
  (X, CNOT, S, rational rotations); amplitudes with irrational entries (e.g.
  a bare 1/sqrt(2) from a Hadamard) enter this schema instance only when
  their weights are rational, and the general algebraic-amplitude case is the
  next rung of the schema, not this one.

  What is proved, all choice-free (axiom profiles ⊆ {propext, Quot.sound}):

  * `bornPrediction_forced` : the prediction space ℤ × ℤ carries an explicit
     choice-free certificate (parity code + local Cantor pairing), so every
     Born prediction is a δ-forced object.
  * `bornWeight_nonneg`, `bornWeight_le_total`, `bornTotal_pos`,
    `born_sum_exact` : the predictions form an exact probability vector
    (0 <= p_k <= 1, Σ p_k = 1, cross-multiplied), with the normalization an
    exact bookkeeping identity, not a limit.
  * `born_zero_test_decided` : the exact-zero test on a Born prediction is
     DECIDED by a finite computation. The same test on the displayed
     continuum is WLPO (`calib_exact_zero_imp_wlpo`).
  * `born_trichotomy_decided` : comparison of two Born predictions is
     DECIDED (cross-multiplied integer trichotomy). The same comparison on
     the displayed continuum is LPO (`calib_trichotomy_imp_lpo`).
  * `bornConservativityCert_holds` : the certificate bundling instrument-side
     decidability against the display-side omniscience prices. This is the
     worked converse pair: physics computes its predictions in the forced
     tower and never performs the omniscient step; only the completed display
     charges LPO/WLPO.

  No project-local axioms. No sorry.
-/

import Mathlib
import ActualMathematics.DeltaForced
import ActualMathematics.CalibrationOmniscience

namespace ActualMathematics
namespace Born

open Forced

/-! ## Gaussian-integer amplitudes and Born weights -/

/-- A Gaussian-integer amplitude: the numerator data of a Gaussian-rational
amplitude over a common denominator (which cancels in every probability). -/
structure Amp where
  re : ℤ
  im : ℤ

/-- The Born weight `|c|^2 = re^2 + im^2` of an amplitude: an exact integer. -/
def normSq (z : Amp) : ℤ := z.re * z.re + z.im * z.im

/-- Squares of integers are nonnegative, choice-free (sign split on `Int.le_total`,
then `Int.mul_nonneg` on the matching orientation). -/
theorem sq_nonneg_int (a : ℤ) : 0 ≤ a * a := by
  rcases Int.le_total 0 a with h | h
  · exact Int.mul_nonneg h h
  · have hneg : 0 ≤ -a := by omega
    have := Int.mul_nonneg hneg hneg
    have hrw : (-a) * (-a) = a * a := by ring
    omega

/-- An integer whose square vanishes is zero, choice-free (trichotomy, then
`Int.mul_pos` on either strict side). -/
theorem mul_self_eq_zero_int {a : ℤ} (h : a * a = 0) : a = 0 := by
  rcases Int.lt_trichotomy a 0 with hlt | heq | hgt
  · have hpos : 0 < -a := by omega
    have hp := Int.mul_pos hpos hpos
    have hrw : (-a) * (-a) = a * a := by ring
    omega
  · exact heq
  · have hp := Int.mul_pos hgt hgt
    omega

theorem normSq_nonneg (z : Amp) : 0 ≤ normSq z := by
  unfold normSq
  have h1 := sq_nonneg_int z.re
  have h2 := sq_nonneg_int z.im
  omega

/-- The weight is zero exactly when the amplitude is zero: `|c|^2 = 0 ↔ c = 0`.
Choice-free (squares are nonnegative and their sum vanishes only term-wise). -/
theorem normSq_eq_zero_iff (z : Amp) : normSq z = 0 ↔ z.re = 0 ∧ z.im = 0 := by
  constructor
  · intro h
    unfold normSq at h
    have h1 := sq_nonneg_int z.re
    have h2 := sq_nonneg_int z.im
    have hre : z.re * z.re = 0 := by omega
    have him : z.im * z.im = 0 := by omega
    exact ⟨mul_self_eq_zero_int hre, mul_self_eq_zero_int him⟩
  · rintro ⟨h1, h2⟩
    unfold normSq
    rw [h1, h2]
    rfl

/-! ## Finite outcome sums (structural recursion; no `Finset`, whose sum
lemmas route through `Classical.choice`) -/

/-- The total of a finite family of integers, by structural recursion. -/
def total : (n : ℕ) → (Fin n → ℤ) → ℤ
  | 0, _ => 0
  | n + 1, w => w ⟨0, Nat.succ_pos n⟩ + total n (fun i => w i.succ)

theorem total_nonneg : ∀ (n : ℕ) (w : Fin n → ℤ), (∀ k, 0 ≤ w k) → 0 ≤ total n w := by
  intro n
  induction n with
  | zero => intro w _; exact Int.le_refl 0
  | succ m ih =>
      intro w hw
      have h0 := hw ⟨0, Nat.succ_pos m⟩
      have hrest := ih (fun i => w i.succ) (fun k => hw k.succ)
      show 0 ≤ w ⟨0, Nat.succ_pos m⟩ + total m (fun i => w i.succ)
      omega

/-- Each term of a nonnegative family is bounded by the total. -/
theorem single_le_total :
    ∀ (n : ℕ) (w : Fin n → ℤ), (∀ k, 0 ≤ w k) → ∀ k, w k ≤ total n w := by
  intro n
  induction n with
  | zero => intro w _ k; exact absurd k.2 (by omega)
  | succ m ih =>
      intro w hw k
      have hrest_nonneg : 0 ≤ total m (fun i => w i.succ) :=
        total_nonneg m _ (fun j => hw j.succ)
      rcases Nat.eq_zero_or_pos k.val with h0 | hpos
      · have hk : k = ⟨0, Nat.succ_pos m⟩ := Fin.ext h0
        subst hk
        show w ⟨0, Nat.succ_pos m⟩ ≤ w ⟨0, Nat.succ_pos m⟩ + total m (fun i => w i.succ)
        omega
      · -- k = j.succ for j := k - 1
        have hj : k.val - 1 < m := by omega
        have hk : k = (⟨k.val - 1, hj⟩ : Fin m).succ := by
          apply Fin.ext
          show k.val = (k.val - 1) + 1
          omega
        have hstep := ih (fun i => w i.succ) (fun j => hw j.succ) ⟨k.val - 1, hj⟩
        have h0 := hw ⟨0, Nat.succ_pos m⟩
        rw [hk]
        show w (⟨k.val - 1, hj⟩ : Fin m).succ
            ≤ w ⟨0, Nat.succ_pos m⟩ + total m (fun i => w i.succ)
        omega

/-- A nonnegative family with a nonzero term has positive total. -/
theorem total_pos :
    ∀ (n : ℕ) (w : Fin n → ℤ), (∀ k, 0 ≤ w k) → ∀ k, w k ≠ 0 → 0 < total n w := by
  intro n w hw k hk
  have h1 := single_le_total n w hw k
  have h2 := hw k
  omega

/-! ## The Born setup and its predictions -/

/-- A finite-dimensional Born measurement with rational-presented data: a
state given by Gaussian-integer amplitude numerators, with at least one
nonzero amplitude. -/
structure Setup (n : ℕ) where
  amp : Fin n → Amp
  witness : Fin n
  nondegenerate : normSq (amp witness) ≠ 0

/-- The Born weight of outcome `k`. -/
def weight {n : ℕ} (s : Setup n) (k : Fin n) : ℤ := normSq (s.amp k)

/-- The total weight (the squared norm of the state). -/
def totalWeight {n : ℕ} (s : Setup n) : ℤ := total n (weight s)

/-- The Born prediction for outcome `k`: the exact rational probability
`w_k / T`, presented as the forced pair `(w_k, T)`. -/
def bornPrediction {n : ℕ} (s : Setup n) (k : Fin n) : ℤ × ℤ :=
  (weight s k, totalWeight s)

theorem bornWeight_nonneg {n : ℕ} (s : Setup n) (k : Fin n) : 0 ≤ weight s k :=
  normSq_nonneg (s.amp k)

theorem bornTotal_pos {n : ℕ} (s : Setup n) : 0 < totalWeight s :=
  total_pos n (weight s) (fun j => bornWeight_nonneg s j) s.witness s.nondegenerate

/-- Cross-multiplied `p_k <= 1`: each weight is bounded by the total. -/
theorem bornWeight_le_total {n : ℕ} (s : Setup n) (k : Fin n) :
    weight s k ≤ totalWeight s :=
  single_le_total n (weight s) (fun j => bornWeight_nonneg s j) k

/-- **Exact normalization.** The Born weights sum to the total EXACTLY, by
definition: `Σ_k p_k = 1` cross-multiplied is a bookkeeping identity, not a
limit. There is no analytic step and hence no omniscience in normalizing a
finite-dimensional Born distribution. -/
theorem born_sum_exact {n : ℕ} (s : Setup n) :
    total n (weight s) = totalWeight s := rfl

/-! ## The prediction space is forced -/

/-- The explicit certificate for a pair of integers: parity-code each side,
then the local Cantor pairing. -/
def intPairToNat (p : ℤ × ℤ) : ℕ := dpair (intToNat p.1) (intToNat p.2)

theorem intPairToNat_inj : Function.Injective intPairToNat := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
  obtain ⟨h1, h2⟩ := dpair_inj2 h
  have ha : a₁ = a₂ := intToNat_inj h1
  have hb : b₁ = b₂ := intToNat_inj h2
  rw [ha, hb]

/-- **The Born prediction space is δ-forced**, by an explicit choice-free
certificate. Every finite-dimensional Born prediction is a forced object. -/
theorem bornPrediction_forced : DeltaForced (ℤ × ℤ) :=
  ⟨⟨intPairToNat, intPairToNat_inj⟩⟩

/-! ## Instrument-side decisions are finite computations -/

/-- **The exact-zero test on a Born prediction is decided.** `p_k = 0` holds
or fails by a finite integer computation; no omniscience is consulted. (The
same test on a displayed constructive real is WLPO:
`Calibration.calib_exact_zero_imp_wlpo`.) -/
theorem born_zero_test_decided {n : ℕ} (s : Setup n) (k : Fin n) :
    weight s k = 0 ∨ weight s k ≠ 0 := by
  rcases Int.decEq (weight s k) 0 with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- **Comparison of Born predictions is decided.** For two rational-presented
setups, `p < q ∨ p = q ∨ q < p` holds by cross-multiplied integer trichotomy,
a finite computation. (The same trichotomy on the displayed continuum is LPO:
`Calibration.calib_trichotomy_imp_lpo`.) -/
theorem born_trichotomy_decided {n m : ℕ} (s : Setup n) (t : Setup m)
    (k : Fin n) (l : Fin m) :
    weight s k * totalWeight t < weight t l * totalWeight s
      ∨ weight s k * totalWeight t = weight t l * totalWeight s
      ∨ weight t l * totalWeight s < weight s k * totalWeight t := by
  omega

/-- The zero test agrees with the amplitude test: `p_k = 0` iff the amplitude
vanishes. The instrument-level decision is about the recorded data, and it is
exact. -/
theorem born_zero_iff_amp_zero {n : ℕ} (s : Setup n) (k : Fin n) :
    weight s k = 0 ↔ (s.amp k).re = 0 ∧ (s.amp k).im = 0 :=
  normSq_eq_zero_iff (s.amp k)

/-! ## The conservativity certificate: the converse pair -/

/-- **Operational δ-conservativity, first instance.** Finite-dimensional
Born predictions from rational-presented data: the prediction space is
δ-forced with an explicit choice-free certificate; the predictions form an
exact probability vector; and the decisions physics performs on them (zero
test, comparison) are finite computations. Against this, the SAME decisions
made on the displayed continuum each cost an omniscience principle. The
instrument never pays the omniscience tax; only the display charges it. -/
structure ConservativityCert : Prop where
  /-- The prediction space carries a choice-free certificate. -/
  prediction_space_forced : DeltaForced (ℤ × ℤ)
  /-- Born weights are nonnegative. -/
  nonneg : ∀ {n : ℕ} (s : Setup n) (k : Fin n), 0 ≤ weight s k
  /-- Cross-multiplied `p_k <= 1`. -/
  le_one : ∀ {n : ℕ} (s : Setup n) (k : Fin n), weight s k ≤ totalWeight s
  /-- The state has positive squared norm. -/
  total_pos : ∀ {n : ℕ} (s : Setup n), 0 < totalWeight s
  /-- Exact normalization: `Σ p = 1` is bookkeeping, not a limit. -/
  sum_exact : ∀ {n : ℕ} (s : Setup n), total n (weight s) = totalWeight s
  /-- The instrument decides the zero test by finite computation. -/
  zero_test_decided :
    ∀ {n : ℕ} (s : Setup n) (k : Fin n), weight s k = 0 ∨ weight s k ≠ 0
  /-- The instrument decides comparisons by finite computation. -/
  trichotomy_decided :
    ∀ {n m : ℕ} (s : Setup n) (t : Setup m) (k : Fin n) (l : Fin m),
      weight s k * totalWeight t < weight t l * totalWeight s
        ∨ weight s k * totalWeight t = weight t l * totalWeight s
        ∨ weight t l * totalWeight s < weight s k * totalWeight t
  /-- The display charges WLPO for the same zero test. -/
  display_zero_test_wlpo :
    (∀ x : Calibration.CReal, Calibration.EqZero x ∨ ¬ Calibration.EqZero x) →
      Omniscience.WLPO
  /-- The display charges LPO for the same trichotomy. -/
  display_trichotomy_lpo :
    (∀ x : Calibration.CReal,
        Calibration.Pos x ∨ Calibration.EqZero x ∨ Calibration.Neg x) →
      Omniscience.LPO

/-- The certificate holds, choice-free. -/
theorem bornConservativityCert_holds : ConservativityCert where
  prediction_space_forced := bornPrediction_forced
  nonneg := fun s k => bornWeight_nonneg s k
  le_one := fun s k => bornWeight_le_total s k
  total_pos := fun s => bornTotal_pos s
  sum_exact := fun s => born_sum_exact s
  zero_test_decided := fun s k => born_zero_test_decided s k
  trichotomy_decided := fun s t k l => born_trichotomy_decided s t k l
  display_zero_test_wlpo := Calibration.calib_exact_zero_imp_wlpo
  display_trichotomy_lpo := Calibration.calib_trichotomy_imp_lpo

end Born
end ActualMathematics

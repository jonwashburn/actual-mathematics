/-
  PrimitiveRecognitionCalculus/CalibrationOmniscience.lean

  The forward calibrations, mechanized: the continuum's order behavior charges
  omniscience, proved over a constructive carrier, choice-free.

  The demarcation paper prices the Q-to-R step in the currency of constructive
  reverse mathematics: real trichotomy is LPO, the order dichotomy is LLPO, and
  the exact-zero test is WLPO. `Omniscience.lean` proved the hierarchy among
  the principles; this module proves the CALIBRATIONS, the direction that says
  the continuum's sharp decisions FORCE omniscience. These were the "stated,
  mechanization in progress" rows of the paper's appendix; this module closes
  them.

  The carrier. A constructive real is a regular sequence of dyadic stages: at
  precision n the stage is `num n / 2^n` with `num n : ℤ`, and regularity is
  the Bishop bound `|x_m - x_n| <= 1/(m+1) + 1/(n+1)`, written entirely at the
  integer cross-multiplication level (no rational display: Mathlib's Q lemmas
  route through `Classical.choice`, and the point of this module is the
  choice-free axiom profile). The order predicates use the standard Bishop
  thresholds, also cross-multiplied:

    EqZero x  :  ∀ n, |num n| * (n+1) <= 2 * 2^n        (x ≈ 0)
    Pos x     :  ∃ n, 2 * 2^n < num n * (n+1)           (0 < x)
    Neg x     :  ∃ n, num n * (n+1) < -(2 * 2^n)        (x < 0)
    NonNeg x  :  ∀ n, -(2 * 2^n) <= num n * (n+1)       (0 <= x)
    NonPos x  :  ∀ n, num n * (n+1) <= 2 * 2^n          (x <= 0)

  The engine is one encoding: a binary sequence α becomes the real `jumpSeq σ α`
  whose stages are 0 until the first `true` of α at index N, and `σ(N) / 2^N`
  from then on (a single jump of dyadic size, sign supplied by σ). Deciding the
  order of that real against 0 decides the Σ⁰₁/Π⁰₁ data of α:

  * `calib_exact_zero_imp_wlpo` : deciding `x ≈ 0 ∨ ¬(x ≈ 0)` for every x
     decides `∀ n, α n = false` for every α: the exact-zero test is WLPO.
  * `calib_trichotomy_imp_lpo`  : trichotomy `0<x ∨ x≈0 ∨ x<0` yields LPO.
  * `calib_dichotomy_imp_llpo`  : dichotomy `0<=x ∨ x<=0` yields LLPO
     (via the parity-signed jump on an at-most-one-true sequence).

  Together with `Omniscience.lean` (LPO ⇔ WLPO ∧ MP) this prices the boundary:
  the forced tower's order is decidable by finite computation
  (`Grow/ForcedTrichotomy`: axiom profile EMPTY), while the completed line's
  order decisions each cost a named omniscience principle.

  Everything here is choice-free: axiom profiles are ⊆ {propext, Quot.sound}.
  No project-local axioms. No sorry.
-/

import Mathlib
import ActualMathematics.Omniscience

namespace ActualMathematics
namespace Calibration

/-! ## The carrier: dyadic-stage constructive reals -/

/-- A constructive real: dyadic stages `num n / 2^n` satisfying the Bishop
regularity bound `|x_m - x_n| <= 1/(m+1) + 1/(n+1)`, cross-multiplied to the
integer level:
`|num m * 2^n - num n * 2^m| * (m+1) * (n+1) <= 2^(m+n) * (m+n+2)`. -/
structure CReal where
  num : ℕ → ℤ
  regular : ∀ m n : ℕ,
    (num m * 2 ^ n - num n * 2 ^ m).natAbs * ((m + 1) * (n + 1)) ≤
      2 ^ (m + n) * (m + n + 2)

/-- `x ≈ 0`: every stage is within the Bishop tolerance of zero,
`|x_n| <= 2/(n+1)`, cross-multiplied. -/
def EqZero (x : CReal) : Prop :=
  ∀ n : ℕ, (x.num n).natAbs * (n + 1) ≤ 2 * 2 ^ n

/-- `0 < x`: some stage exceeds the tolerance, `x_n > 2/(n+1)`. -/
def Pos (x : CReal) : Prop :=
  ∃ n : ℕ, ((2 * 2 ^ n : ℕ) : ℤ) < x.num n * ((n + 1 : ℕ) : ℤ)

/-- `x < 0`: some stage falls below minus the tolerance. -/
def Neg (x : CReal) : Prop :=
  ∃ n : ℕ, x.num n * ((n + 1 : ℕ) : ℤ) < -((2 * 2 ^ n : ℕ) : ℤ)

/-- `0 <= x`: no stage falls below minus the tolerance. -/
def NonNeg (x : CReal) : Prop :=
  ∀ n : ℕ, -((2 * 2 ^ n : ℕ) : ℤ) ≤ x.num n * ((n + 1 : ℕ) : ℤ)

/-- `x <= 0`: no stage exceeds the tolerance. -/
def NonPos (x : CReal) : Prop :=
  ∀ n : ℕ, x.num n * ((n + 1 : ℕ) : ℤ) ≤ ((2 * 2 ^ n : ℕ) : ℤ)

/-- The zero real: every stage is 0. -/
def zero : CReal where
  num _ := 0
  regular m n := by
    rw [Int.zero_mul, Int.zero_mul, sub_self, Int.natAbs_zero, Nat.zero_mul]
    exact Nat.zero_le _

/-! ## First-true search on a binary sequence -/

/-- The least index `<= n` at which `α` is `true`, if any. Structural
recursion; no choice. -/
def firstTrue (α : ℕ → Bool) : ℕ → Option ℕ
  | 0 => if α 0 = true then some 0 else none
  | n + 1 =>
      match firstTrue α n with
      | some N => some N
      | none => if α (n + 1) = true then some (n + 1) else none

theorem firstTrue_none {α : ℕ → Bool} :
    ∀ {n : ℕ}, firstTrue α n = none → ∀ k, k ≤ n → α k = false := by
  intro n
  induction n with
  | zero =>
      intro h k hk
      have hk0 : k = 0 := Nat.le_zero.mp hk
      subst hk0
      by_cases h0 : α 0 = true
      · rw [firstTrue, if_pos h0] at h
        exact absurd h (by simp)
      · exact Bool.eq_false_iff.mpr h0
  | succ n ih =>
      intro h k hk
      rw [firstTrue] at h
      cases hft : firstTrue α n with
      | some N => rw [hft] at h; exact absurd h (by simp)
      | none =>
          rw [hft] at h
          by_cases hs : α (n + 1) = true
          · rw [if_pos hs] at h; exact absurd h (by simp)
          · rcases Nat.lt_or_ge k (n + 1) with hlt | hge
            · exact ih hft k (by omega)
            · have : k = n + 1 := by omega
              subst this
              exact Bool.eq_false_iff.mpr hs

theorem firstTrue_some {α : ℕ → Bool} :
    ∀ {n N : ℕ}, firstTrue α n = some N →
      α N = true ∧ N ≤ n ∧ ∀ j, j < N → α j = false := by
  intro n
  induction n with
  | zero =>
      intro N h
      by_cases h0 : α 0 = true
      · rw [firstTrue, if_pos h0] at h
        have hN : N = 0 := (Option.some.inj h).symm
        subst hN
        exact ⟨h0, Nat.le_refl 0, fun j hj => absurd hj (by omega)⟩
      · rw [firstTrue, if_neg h0] at h
        exact absurd h (by simp)
  | succ n ih =>
      intro N h
      rw [firstTrue] at h
      cases hft : firstTrue α n with
      | some M =>
          rw [hft] at h
          have hM : M = N := Option.some.inj h
          subst hM
          obtain ⟨h1, h2, h3⟩ := ih hft
          exact ⟨h1, by omega, h3⟩
      | none =>
          rw [hft] at h
          by_cases hs : α (n + 1) = true
          · rw [if_pos hs] at h
            have hN : N = n + 1 := (Option.some.inj h).symm
            subst hN
            exact ⟨hs, Nat.le_refl _, fun j hj => firstTrue_none hft j (by omega)⟩
          · rw [if_neg hs] at h
            exact absurd h (by simp)

/-- If `α` is true at `N` and false strictly below, then the search settles on
`N` from index `N` onward. -/
theorem firstTrue_stable {α : ℕ → Bool} {N : ℕ}
    (hN : α N = true) (hmin : ∀ j, j < N → α j = false) :
    ∀ n, N ≤ n → firstTrue α n = some N := by
  intro n
  induction n with
  | zero =>
      intro h
      have : N = 0 := by omega
      subst this
      rw [firstTrue, if_pos hN]
  | succ n ih =>
      intro h
      rcases Nat.lt_or_ge n N with hlt | hge
      · -- N = n + 1
        have hEq : N = n + 1 := by omega
        subst hEq
        have hnone : firstTrue α n = none := by
          cases hft : firstTrue α n with
          | none => rfl
          | some M =>
              obtain ⟨hMt, hMle, _⟩ := firstTrue_some hft
              have : α M = false := hmin M (by omega)
              rw [hMt] at this
              exact absurd this (by simp)
        rw [firstTrue, hnone, if_pos hN]
      · have := ih hge
        rw [firstTrue, this]

/-- Two settled values of the search agree (each is THE least true index). -/
theorem firstTrue_unique {α : ℕ → Bool} {m n N₁ N₂ : ℕ}
    (h₁ : firstTrue α m = some N₁) (h₂ : firstTrue α n = some N₂) : N₁ = N₂ := by
  obtain ⟨ht₁, _, hmin₁⟩ := firstTrue_some h₁
  obtain ⟨ht₂, _, hmin₂⟩ := firstTrue_some h₂
  rcases Nat.lt_trichotomy N₁ N₂ with h | h | h
  · have := hmin₂ N₁ h
    rw [ht₁] at this
    exact absurd this (by simp)
  · exact h
  · have := hmin₁ N₂ h
    rw [ht₂] at this
    exact absurd this (by simp)

/-- A true value of `α` guarantees the search settles: there is a least true
index `N <= k`, located by the bounded search (no choice). -/
theorem firstTrue_of_true {α : ℕ → Bool} {k : ℕ} (hk : α k = true) :
    ∃ N, N ≤ k ∧ α N = true ∧ ∀ j, j < N → α j = false := by
  cases hft : firstTrue α k with
  | some N =>
      obtain ⟨h1, h2, h3⟩ := firstTrue_some hft
      exact ⟨N, h2, h1, h3⟩
  | none =>
      have := firstTrue_none hft k (Nat.le_refl k)
      rw [hk] at this
      exact absurd this (by simp)

/-! ## The jump encoding -/

/-- The stage numerators of the jump real of `α` with sign `σ`: stage `n` is
`0` if `α` has no true value `<= n`, and `σ(N) * 2^(n-N)` (i.e. the dyadic
value `σ(N)/2^N`) once the first true index `N` is in view. -/
def jumpNum (σ : ℕ → ℤ) (α : ℕ → Bool) (n : ℕ) : ℤ :=
  match firstTrue α n with
  | some N => σ N * 2 ^ (n - N)
  | none => 0

theorem jumpNum_of_none {σ : ℕ → ℤ} {α : ℕ → Bool} {n : ℕ}
    (h : firstTrue α n = none) : jumpNum σ α n = 0 := by
  unfold jumpNum
  rw [h]

theorem jumpNum_of_some {σ : ℕ → ℤ} {α : ℕ → Bool} {n N : ℕ}
    (h : firstTrue α n = some N) : jumpNum σ α n = σ N * 2 ^ (n - N) := by
  unfold jumpNum
  rw [h]

/-- Powers of two cast from ℕ to ℤ. -/
theorem cast_two_pow (k : ℕ) : (((2 : ℕ) ^ k : ℕ) : ℤ) = (2 : ℤ) ^ k := by
  induction k with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, pow_succ, Int.natCast_mul, ih]
      rfl

/-- `m + 1 < 2 ^ N` whenever `m < N`. -/
theorem succ_lt_two_pow {m N : ℕ} (h : m < N) : m + 1 < 2 ^ N := by
  have h1 : m + 1 < 2 ^ (m + 1) := Nat.lt_two_pow_self
  have h2 : 2 ^ (m + 1) ≤ 2 ^ N := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- The regularity bound for the jump numerators, one-sided case: no true in
view at `m`, first true `N` in view at `n` (so `m < N <= n`). -/
theorem jump_bound_none_some {σ : ℕ → ℤ} (hσ : ∀ N, (σ N).natAbs = 1)
    {α : ℕ → Bool} {m n N : ℕ}
    (hm : firstTrue α m = none) (hn : firstTrue α n = some N) :
    (jumpNum σ α m * 2 ^ n - jumpNum σ α n * 2 ^ m).natAbs * ((m + 1) * (n + 1)) ≤
      2 ^ (m + n) * (m + n + 2) := by
  obtain ⟨hNt, hNn, _⟩ := firstTrue_some hn
  have hmN : m < N := by
    rcases Nat.lt_or_ge m N with h | h
    · exact h
    · have := firstTrue_none hm N h
      rw [hNt] at this
      exact absurd this (by simp)
  -- reduce the numerator difference to a pure power of two
  rw [jumpNum_of_none hm, jumpNum_of_some hn, Int.zero_mul, zero_sub, Int.natAbs_neg,
    Int.natAbs_mul, Int.natAbs_mul, hσ, Int.natAbs_pow, Int.natAbs_pow]
  show 1 * (2 : ℕ) ^ (n - N) * 2 ^ m * ((m + 1) * (n + 1)) ≤ 2 ^ (m + n) * (m + n + 2)
  obtain ⟨d, rfl⟩ : ∃ d, n = N + d := ⟨n - N, by omega⟩
  have hsub : N + d - N = d := by omega
  rw [hsub, Nat.one_mul]
  -- core comparison, then multiply by the common positive factor 2^(d+m)
  have hcore : (m + 1) * (N + d + 1) ≤ 2 ^ N * (m + (N + d) + 2) :=
    Nat.mul_le_mul (Nat.le_of_lt (succ_lt_two_pow hmN)) (by omega)
  have hmul := Nat.mul_le_mul_left (2 ^ d * 2 ^ m) hcore
  have lhs_eq : 2 ^ d * 2 ^ m * ((m + 1) * (N + d + 1))
      = 2 ^ d * 2 ^ m * ((m + 1) * (N + d + 1)) := rfl
  have rhs_eq : 2 ^ d * 2 ^ m * (2 ^ N * (m + (N + d) + 2))
      = 2 ^ (m + (N + d)) * (m + (N + d) + 2) := by
    have hp : (2 : ℕ) ^ (m + (N + d)) = 2 ^ d * 2 ^ m * 2 ^ N := by
      rw [← Nat.pow_add, ← Nat.pow_add]
      congr 1
      omega
    rw [hp]
    ring
  calc 2 ^ d * 2 ^ m * ((m + 1) * (N + d + 1))
      ≤ 2 ^ d * 2 ^ m * (2 ^ N * (m + (N + d) + 2)) := hmul
    _ = 2 ^ (m + (N + d)) * (m + (N + d) + 2) := rhs_eq

/-- The jump numerators are regular: `jumpSeq` is a well-formed constructive
real. -/
theorem jump_regular {σ : ℕ → ℤ} (hσ : ∀ N, (σ N).natAbs = 1)
    (α : ℕ → Bool) (m n : ℕ) :
    (jumpNum σ α m * 2 ^ n - jumpNum σ α n * 2 ^ m).natAbs * ((m + 1) * (n + 1)) ≤
      2 ^ (m + n) * (m + n + 2) := by
  cases hm : firstTrue α m with
  | none =>
      cases hn : firstTrue α n with
      | none =>
          rw [jumpNum_of_none hm, jumpNum_of_none hn, Int.zero_mul, Int.zero_mul,
            sub_self, Int.natAbs_zero, Nat.zero_mul]
          exact Nat.zero_le _
      | some N => exact jump_bound_none_some hσ hm hn
  | some N₁ =>
      cases hn : firstTrue α n with
      | none =>
          -- swap the roles of m and n
          have h := jump_bound_none_some hσ hn hm
          have habs : (jumpNum σ α m * 2 ^ n - jumpNum σ α n * 2 ^ m).natAbs
              = (jumpNum σ α n * 2 ^ m - jumpNum σ α m * 2 ^ n).natAbs := by
            omega
          rw [habs, Nat.mul_comm (m + 1) (n + 1)]
          have hpow : (2 : ℕ) ^ (m + n) = 2 ^ (n + m) := by rw [Nat.add_comm]
          have hcnt : m + n + 2 = n + m + 2 := by omega
          rw [hpow, hcnt]
          exact h
      | some N₂ =>
          -- same first-true index: the two stages agree exactly
          have hN : N₁ = N₂ := firstTrue_unique hm hn
          subst hN
          obtain ⟨_, hN₁m, _⟩ := firstTrue_some hm
          obtain ⟨_, hN₁n, _⟩ := firstTrue_some hn
          rw [jumpNum_of_some hm, jumpNum_of_some hn]
          obtain ⟨d₁, rfl⟩ : ∃ d, m = N₁ + d := ⟨m - N₁, by omega⟩
          obtain ⟨d₂, rfl⟩ : ∃ d, n = N₁ + d := ⟨n - N₁, by omega⟩
          have hs₁ : N₁ + d₁ - N₁ = d₁ := by omega
          have hs₂ : N₁ + d₂ - N₁ = d₂ := by omega
          rw [hs₁, hs₂]
          have hzero : σ N₁ * 2 ^ d₁ * 2 ^ (N₁ + d₂)
              - σ N₁ * 2 ^ d₂ * 2 ^ (N₁ + d₁) = 0 := by
            rw [pow_add, pow_add]
            ring
          rw [hzero, Int.natAbs_zero, Nat.zero_mul]
          exact Nat.zero_le _

/-- The jump real of `α` with unit sign data `σ`. -/
def jumpSeq (σ : ℕ → ℤ) (hσ : ∀ N, (σ N).natAbs = 1) (α : ℕ → Bool) : CReal where
  num := jumpNum σ α
  regular := jump_regular hσ α

/-! ## Bridge lemmas: order of the jump real decides the sequence -/

/-- If `α` is everywhere false, the jump real is (exactly) zero at every
stage. -/
theorem eqZero_of_allFalse {σ : ℕ → ℤ} {hσ : ∀ N, (σ N).natAbs = 1}
    {α : ℕ → Bool} (h : ∀ k, α k = false) : EqZero (jumpSeq σ hσ α) := by
  intro n
  have hnone : firstTrue α n = none := by
    cases hft : firstTrue α n with
    | none => rfl
    | some N =>
        obtain ⟨hNt, _, _⟩ := firstTrue_some hft
        rw [h N] at hNt
        exact absurd hNt (by simp)
  show (jumpNum σ α n).natAbs * (n + 1) ≤ 2 * 2 ^ n
  rw [jumpNum_of_none hnone, Int.natAbs_zero, Nat.zero_mul]
  exact Nat.zero_le _

/-- The witness precision at which a jump at `N` violates every zero
tolerance: `n₀ = 2^(N+1)`. At that stage the inequality
`2^(n₀-N) * (n₀+1) <= 2*2^n₀` would force `n₀ + 1 <= 2^(N+1) = n₀`. -/
theorem jump_stage_violation {N : ℕ} :
    ¬ (2 ^ (2 ^ (N + 1) - N) * (2 ^ (N + 1) + 1) ≤ 2 * 2 ^ (2 ^ (N + 1))) := by
  intro hcon
  set n₀ := 2 ^ (N + 1) with hn₀
  have hNn : N < n₀ := by
    have := succ_lt_two_pow (Nat.lt_succ_self N)
    omega
  obtain ⟨d, hd⟩ : ∃ d, n₀ = N + d := ⟨n₀ - N, by omega⟩
  have hsub : n₀ - N = d := by omega
  rw [hsub] at hcon
  -- 2 * 2^n₀ = 2^(N+1) * 2^d
  have hsplit : 2 * 2 ^ n₀ = 2 ^ (N + 1) * 2 ^ d := by
    rw [hd, ← Nat.pow_add, ← Nat.pow_succ']
    congr 1
    omega
  rw [hsplit] at hcon
  -- cancel the positive factor 2^d
  have hpos : 0 < 2 ^ d := Nat.two_pow_pos d
  have hle : n₀ + 1 ≤ 2 ^ (N + 1) := by
    have h1 : (n₀ + 1) * 2 ^ d ≤ 2 ^ (N + 1) * 2 ^ d := by
      calc (n₀ + 1) * 2 ^ d = 2 ^ d * (n₀ + 1) := by ring
        _ ≤ 2 ^ (N + 1) * 2 ^ d := hcon
        _ = 2 ^ (N + 1) * 2 ^ d := rfl
    exact Nat.le_of_mul_le_mul_right h1 hpos
  omega

/-- If `α` is true somewhere, the jump real fails the zero tolerance at the
witness stage `n₀ = 2^(N+1)` (for the first true index `N`). -/
theorem not_eqZero_of_true {σ : ℕ → ℤ} {hσ : ∀ N, (σ N).natAbs = 1}
    {α : ℕ → Bool} {k : ℕ} (hk : α k = true) : ¬ EqZero (jumpSeq σ hσ α) := by
  intro hzero
  obtain ⟨N, _, hNt, hNmin⟩ := firstTrue_of_true hk
  set n₀ := 2 ^ (N + 1) with hn₀
  have hNn : N ≤ n₀ := by
    have := succ_lt_two_pow (Nat.lt_succ_self N)
    omega
  have hft : firstTrue α n₀ = some N := firstTrue_stable hNt hNmin n₀ hNn
  have hstage := hzero n₀
  rw [show (jumpSeq σ hσ α).num n₀ = jumpNum σ α n₀ from rfl,
    jumpNum_of_some hft, Int.natAbs_mul, hσ, Int.natAbs_pow] at hstage
  show False
  exact jump_stage_violation (by
    have : (1 : ℕ) * ((2 : ℤ).natAbs ^ (n₀ - N)) * (n₀ + 1) ≤ 2 * 2 ^ n₀ := hstage
    simpa using this)

/-- `EqZero` of the jump real decides `∀ k, α k = false` (both directions,
choice-free). This is the engine of all three calibrations. -/
theorem eqZero_iff_allFalse {σ : ℕ → ℤ} {hσ : ∀ N, (σ N).natAbs = 1}
    (α : ℕ → Bool) : EqZero (jumpSeq σ hσ α) ↔ ∀ k, α k = false := by
  constructor
  · intro hzero k
    by_cases hk : α k = true
    · exact absurd hzero (not_eqZero_of_true (hσ := hσ) hk)
    · exact Bool.eq_false_iff.mpr hk
  · exact eqZero_of_allFalse

/-! ## Calibration 1: the exact-zero test is WLPO -/

/-- **The exact-zero test forces WLPO.** If every constructive real can be
decided `x ≈ 0` or `¬(x ≈ 0)`, then every binary sequence can be decided
everywhere-false or not: the sharp zero test on the continuum is exactly the
weak limited principle of omniscience. Choice-free. -/
theorem calib_exact_zero_imp_wlpo
    (h : ∀ x : CReal, EqZero x ∨ ¬ EqZero x) : Omniscience.WLPO := by
  intro α
  have hσ : ∀ _ : ℕ, ((1 : ℤ)).natAbs = 1 := fun _ => rfl
  rcases h (jumpSeq (fun _ => (1 : ℤ)) hσ α) with hz | hnz
  · exact Or.inl ((eqZero_iff_allFalse α).mp hz)
  · exact Or.inr (fun hall => hnz (eqZero_of_allFalse hall))

/-! ## Calibration 2: trichotomy is LPO -/

/-- A positive stage of the unit-sign jump real locates a true value of `α`. -/
theorem true_of_pos {α : ℕ → Bool}
    {hσ : ∀ _ : ℕ, ((1 : ℤ)).natAbs = 1}
    (h : Pos (jumpSeq (fun _ => (1 : ℤ)) hσ α)) : ∃ k, α k = true := by
  obtain ⟨n, hn⟩ := h
  cases hft : firstTrue α n with
  | some N =>
      obtain ⟨hNt, _, _⟩ := firstTrue_some hft
      exact ⟨N, hNt⟩
  | none =>
      rw [show (jumpSeq (fun _ => (1 : ℤ)) hσ α).num n = jumpNum (fun _ => (1 : ℤ)) α n
          from rfl, jumpNum_of_none hft, Int.zero_mul] at hn
      -- 2 * 2^n < 0 is absurd
      exact absurd hn (by
        have : (0 : ℤ) ≤ ((2 * 2 ^ n : ℕ) : ℤ) := Int.natCast_nonneg _
        omega)

/-- The unit-sign jump real is nowhere negative. -/
theorem not_neg_jump {α : ℕ → Bool} {hσ : ∀ _ : ℕ, ((1 : ℤ)).natAbs = 1} :
    ¬ Neg (jumpSeq (fun _ => (1 : ℤ)) hσ α) := by
  rintro ⟨n, hn⟩
  have hnum : (0 : ℤ) ≤ (jumpSeq (fun _ => (1 : ℤ)) hσ α).num n := by
    show (0 : ℤ) ≤ jumpNum (fun _ => (1 : ℤ)) α n
    cases hft : firstTrue α n with
    | some N =>
        rw [jumpNum_of_some hft, one_mul, ← cast_two_pow]
        exact Int.natCast_nonneg _
    | none =>
        exact (jumpNum_of_none hft (σ := fun _ => (1 : ℤ))) ▸ Int.le_refl 0
  have hprod : (0 : ℤ) ≤ (jumpSeq (fun _ => (1 : ℤ)) hσ α).num n * ((n + 1 : ℕ) : ℤ) :=
    Int.mul_nonneg hnum (Int.natCast_nonneg _)
  have hcast : (0 : ℤ) ≤ ((2 * 2 ^ n : ℕ) : ℤ) := Int.natCast_nonneg _
  omega

/-- **Trichotomy forces LPO.** If every constructive real satisfies
`0 < x ∨ x ≈ 0 ∨ x < 0`, then every binary sequence is decidably
everywhere-false or somewhere-true. Choice-free. -/
theorem calib_trichotomy_imp_lpo
    (h : ∀ x : CReal, Pos x ∨ EqZero x ∨ Neg x) : Omniscience.LPO := by
  intro α
  have hσ : ∀ _ : ℕ, ((1 : ℤ)).natAbs = 1 := fun _ => rfl
  rcases h (jumpSeq (fun _ => (1 : ℤ)) hσ α) with hp | hz | hneg
  · exact Or.inr (true_of_pos hp)
  · exact Or.inl ((eqZero_iff_allFalse α).mp hz)
  · exact absurd hneg not_neg_jump

/-! ## Calibration 3: dichotomy is LLPO -/

/-- The parity sign: `+1` at even indices, `-1` at odd ones. -/
def paritySign (N : ℕ) : ℤ := if N % 2 = 0 then 1 else -1

theorem paritySign_natAbs (N : ℕ) : (paritySign N).natAbs = 1 := by
  unfold paritySign
  by_cases h : N % 2 = 0
  · rw [if_pos h]; rfl
  · rw [if_neg h]; rfl

/-- The stage inequality refuted at the witness precision, signed version:
`0 <= x` fails against a NEGATIVE jump, `x <= 0` fails against a POSITIVE
one. Shared arithmetic core. -/
theorem jump_stage_signed_violation {N : ℕ} :
    ¬ ((2 : ℤ) ^ (2 ^ (N + 1) - N) * ((2 ^ (N + 1) + 1 : ℕ) : ℤ) ≤
        ((2 * 2 ^ (2 ^ (N + 1)) : ℕ) : ℤ)) := by
  intro hcon
  set n₀ := 2 ^ (N + 1) with hn₀
  -- move to ℕ through the explicit (choice-free) cast lemmas
  have hcast : ((2 ^ (n₀ - N) * (n₀ + 1) : ℕ) : ℤ) ≤ ((2 * 2 ^ n₀ : ℕ) : ℤ) := by
    rw [Int.natCast_mul, cast_two_pow]
    exact hcon
  have hnat : 2 ^ (n₀ - N) * (n₀ + 1) ≤ 2 * 2 ^ n₀ := Int.ofNat_le.mp hcast
  exact jump_stage_violation hnat

/-- If `β` has its unique true value at an ODD index, the parity jump real is
not nonnegative... contrapositive form: `0 <= y_β` forces every odd index of
`β` to be false. -/
theorem odd_false_of_nonNeg {β : ℕ → Bool}
    (hone : ∀ m n, β m = true → β n = true → m = n)
    (h : NonNeg (jumpSeq paritySign paritySign_natAbs β)) :
    ∀ k, β (2 * k + 1) = false := by
  intro k
  by_cases hk : β (2 * k + 1) = true
  · exfalso
    set N := 2 * k + 1 with hN
    -- N is the unique true index, hence the first
    have hmin : ∀ j, j < N → β j = false := by
      intro j hj
      by_cases hj' : β j = true
      · have := hone j N hj' hk
        omega
      · exact Bool.eq_false_iff.mpr hj'
    set n₀ := 2 ^ (N + 1) with hn₀
    have hNn : N ≤ n₀ := by
      have := succ_lt_two_pow (Nat.lt_succ_self N)
      omega
    have hft : firstTrue β n₀ = some N := firstTrue_stable hk hmin n₀ hNn
    have hodd : paritySign N = -1 := by
      unfold paritySign
      rw [if_neg (by omega)]
    have hstage := h n₀
    rw [show (jumpSeq paritySign paritySign_natAbs β).num n₀ = jumpNum paritySign β n₀
        from rfl, jumpNum_of_some hft, hodd] at hstage
    -- -(2^(n₀-N)) * (n₀+1) >= -(2*2^n₀)  ⟹  2^(n₀-N) * (n₀+1) <= 2*2^n₀
    have hflip : (2 : ℤ) ^ (n₀ - N) * ((n₀ + 1 : ℕ) : ℤ) ≤ ((2 * 2 ^ n₀ : ℕ) : ℤ) := by
      have hexp : (-1 : ℤ) * 2 ^ (n₀ - N) * ((n₀ + 1 : ℕ) : ℤ)
          = -((2 : ℤ) ^ (n₀ - N) * ((n₀ + 1 : ℕ) : ℤ)) := by ring
      rw [hexp] at hstage
      omega
    exact jump_stage_signed_violation hflip
  · exact Bool.eq_false_iff.mpr hk

/-- Symmetrically: `y_β <= 0` forces every even index of `β` to be false. -/
theorem even_false_of_nonPos {β : ℕ → Bool}
    (hone : ∀ m n, β m = true → β n = true → m = n)
    (h : NonPos (jumpSeq paritySign paritySign_natAbs β)) :
    ∀ k, β (2 * k) = false := by
  intro k
  by_cases hk : β (2 * k) = true
  · exfalso
    set N := 2 * k with hN
    have hmin : ∀ j, j < N → β j = false := by
      intro j hj
      by_cases hj' : β j = true
      · have := hone j N hj' hk
        omega
      · exact Bool.eq_false_iff.mpr hj'
    set n₀ := 2 ^ (N + 1) with hn₀
    have hNn : N ≤ n₀ := by
      have := succ_lt_two_pow (Nat.lt_succ_self N)
      omega
    have hft : firstTrue β n₀ = some N := firstTrue_stable hk hmin n₀ hNn
    have heven : paritySign N = 1 := by
      unfold paritySign
      rw [if_pos (by omega)]
    have hstage := h n₀
    rw [show (jumpSeq paritySign paritySign_natAbs β).num n₀ = jumpNum paritySign β n₀
        from rfl, jumpNum_of_some hft, heven, one_mul] at hstage
    exact jump_stage_signed_violation hstage
  · exact Bool.eq_false_iff.mpr hk

/-- **Dichotomy forces LLPO.** If every constructive real satisfies
`0 <= x ∨ x <= 0`, then for every binary sequence with at most one true value,
either the even or the odd indices are all false. Choice-free. -/
theorem calib_dichotomy_imp_llpo
    (h : ∀ x : CReal, NonNeg x ∨ NonPos x) : Omniscience.LLPO := by
  intro β hone
  have hone' : ∀ m n, β m = true → β n = true → m = n := hone
  rcases h (jumpSeq paritySign paritySign_natAbs β) with hnn | hnp
  · exact Or.inr (odd_false_of_nonNeg hone' hnn)
  · exact Or.inl (even_false_of_nonPos hone' hnp)

/-! ## The calibration certificate -/

/-- **Forward calibration certificate.** Over the dyadic constructive carrier:
the exact-zero test yields WLPO, trichotomy yields LPO, dichotomy yields LLPO.
Together with the hierarchy (`Omniscience.lean`: LPO ⇔ WLPO ∧ MP) this is the
priced boundary of the demarcation paper, all choice-free. -/
structure CalibrationCert : Prop where
  exact_zero_wlpo :
    (∀ x : CReal, EqZero x ∨ ¬ EqZero x) → Omniscience.WLPO
  trichotomy_lpo :
    (∀ x : CReal, Pos x ∨ EqZero x ∨ Neg x) → Omniscience.LPO
  dichotomy_llpo :
    (∀ x : CReal, NonNeg x ∨ NonPos x) → Omniscience.LLPO
  hierarchy_lpo_wlpo : Omniscience.LPO → Omniscience.WLPO
  hierarchy_lpo_llpo : Omniscience.LPO → Omniscience.LLPO
  hierarchy_lpo_markov : Omniscience.LPO → Omniscience.MarkovPrinciple
  location_lpo :
    Omniscience.WLPO → Omniscience.MarkovPrinciple → Omniscience.LPO

/-- The certificate holds, choice-free. -/
theorem calibrationCert_holds : CalibrationCert where
  exact_zero_wlpo := calib_exact_zero_imp_wlpo
  trichotomy_lpo := calib_trichotomy_imp_lpo
  dichotomy_llpo := calib_dichotomy_imp_llpo
  hierarchy_lpo_wlpo := Omniscience.lpo_imp_wlpo
  hierarchy_lpo_llpo := Omniscience.lpo_imp_llpo
  hierarchy_lpo_markov := Omniscience.lpo_imp_markov
  location_lpo := Omniscience.wlpo_and_markov_imp_lpo

end Calibration
end ActualMathematics

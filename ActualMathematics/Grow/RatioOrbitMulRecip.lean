import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder

namespace ActualMathematics.PRCGrow.RatioOrbitMulRecip

open ActualMathematics

theorem mul_recipNonzero_crossEq_one (p : RatioOrbit)
    (h : ¬ SignedOrbit.balanced p.num SignedOrbit.zero) :
    RatioOrbit.crossEq (RatioOrbit.mul p (RatioOrbit.recipNonzero p h)) RatioOrbit.one := by
  rw [RatioOrbit.crossEq_iff_toIntCross]
  have hod : (RatioOrbit.one).den.toNat = 1 := rfl
  have hon : (RatioOrbit.one).num.toInt = 1 := rfl
  rw [hod, hon]
  by_cases hn : p.num.nonnegFlag = true
  · -- nonneg branch: recip.num = ofOrbit p.den, recip.den = |p.num|
    have hni : 0 ≤ p.num.toInt := (SignedOrbit.nonnegFlag_eq_true_iff p.num).mp hn
    have habs : (Int.natAbs p.num.toInt : ℤ) = p.num.toInt := by omega
    simp only [RatioOrbit.recipNonzero, RatioOrbit.mul, if_pos hn,
               SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt, SignedOrbit.abs_toNat,
               DistinctionNat.toNat_mul, Nat.cast_mul, Nat.cast_one, one_mul, mul_one]
    rw [habs]
    ring
  · -- neg branch: recip.num = -(ofOrbit p.den), recip.den = |p.num|
    have hnn : ¬ (0 ≤ p.num.toInt) :=
      fun hc => hn ((SignedOrbit.nonnegFlag_eq_true_iff p.num).mpr hc)
    have hni : p.num.toInt < 0 := by omega
    have habs : (Int.natAbs p.num.toInt : ℤ) = -p.num.toInt := by omega
    simp only [RatioOrbit.recipNonzero, RatioOrbit.mul, if_neg hn,
               SignedOrbit.mul_toInt, SignedOrbit.negate_toInt, SignedOrbit.ofOrbit_toInt,
               SignedOrbit.abs_toNat, DistinctionNat.toNat_mul, Nat.cast_mul, Nat.cast_one,
               one_mul, mul_one]
    rw [habs]
    ring

end ActualMathematics.PRCGrow.RatioOrbitMulRecip

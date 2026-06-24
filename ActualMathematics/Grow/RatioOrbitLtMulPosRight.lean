import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.RatioOrbitLeReflTotal
import ActualMathematics.Grow.RatioOrbitLtTrichotomy
import ActualMathematics.Grow.RatioOrbitOrderMulNonneg

namespace ActualMathematics.PRCGrow.RatioOrbitLtMulPosRight

open ActualMathematics
open ActualMathematics.PRCGrow.RatioOrbitLeReflTotal
open ActualMathematics.PRCGrow.RatioOrbitLtTrichotomy
open ActualMathematics.PRCGrow.RatioOrbitOrderMulNonneg

theorem ltQ_mul_pos_right (p q r : RatioOrbit)
    (hr : ltQ RatioOrbit.zero r) (hpq : ltQ p q) :
    ltQ (RatioOrbit.mul p r) (RatioOrbit.mul q r) := by
  unfold ltQ at hr hpq ⊢
  refine ⟨?_, ?_⟩
  · exact leQ_mul_nonneg_right p q r hr.1 hpq.1
  · intro hcross
    apply hpq.2
    have hncross_r : ¬ RatioOrbit.crossEq RatioOrbit.zero r := hr.2
    rw [RatioOrbit.crossEq_iff_toIntCross] at hncross_r
    have hzero_num_toInt : RatioOrbit.zero.num.toInt = 0 := by
      have hzero_num : RatioOrbit.zero.num = SignedOrbit.zero := rfl
      rw [hzero_num]; exact SignedOrbit.zero_toInt
    have hr_num_ne : r.num.toInt ≠ 0 := by
      intro h
      apply hncross_r
      rw [hzero_num_toInt, h]
      ring
    have hr_den_ne : (r.den.toNat : ℤ) ≠ 0 := by
      have := RatioOrbit.den_toNat_ne_zero r; omega
    rw [RatioOrbit.crossEq_iff_toIntCross] at hcross ⊢
    have hmul_pr_num : (RatioOrbit.mul p r).num = SignedOrbit.mul p.num r.num := rfl
    have hmul_qr_num : (RatioOrbit.mul q r).num = SignedOrbit.mul q.num r.num := rfl
    have hmul_pr_den : (RatioOrbit.mul p r).den = p.den * r.den := rfl
    have hmul_qr_den : (RatioOrbit.mul q r).den = q.den * r.den := rfl
    rw [hmul_pr_num, hmul_qr_num, hmul_pr_den, hmul_qr_den,
        SignedOrbit.mul_toInt, SignedOrbit.mul_toInt,
        DistinctionNat.toNat_mul, DistinctionNat.toNat_mul] at hcross
    push_cast at hcross
    push_cast
    have hstep1 : p.num.toInt * ((q.den.toNat : ℤ) * (r.den.toNat : ℤ)) =
                  q.num.toInt * ((p.den.toNat : ℤ) * (r.den.toNat : ℤ)) := by
      apply Int.eq_of_mul_eq_mul_right hr_num_ne
      push_cast
      linear_combination hcross
    apply Int.eq_of_mul_eq_mul_right hr_den_ne
    push_cast
    linear_combination hstep1

end ActualMathematics.PRCGrow.RatioOrbitLtMulPosRight

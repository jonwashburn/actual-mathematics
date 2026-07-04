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

theorem crossEq_mul_pos_right_cancel (p q r : RatioOrbit)
    (hr_ne : ¬ RatioOrbit.crossEq RatioOrbit.zero r)
    (h : RatioOrbit.crossEq (RatioOrbit.mul p r) (RatioOrbit.mul q r)) :
    RatioOrbit.crossEq p q := by
  rw [RatioOrbit.crossEq_iff_toIntCross] at hr_ne h ⊢
  have hz_num : RatioOrbit.zero.num.toInt = 0 := SignedOrbit.zero_toInt
  have hz_den : RatioOrbit.zero.den.toNat = 1 := by
    show (DistinctionNat.succ DistinctionNat.zero).toNat = 1
    rw [DistinctionNat.toNat_succ, DistinctionNat.toNat_zero]
  rw [hz_num, hz_den] at hr_ne
  have hrn_ne : r.num.toInt ≠ 0 := by
    intro hc; apply hr_ne; rw [hc]; ring
  have hrd_ne : (r.den.toNat : ℤ) ≠ 0 := by
    have := r.den_toNat_ne_zero; omega
  have hmpr_num : (RatioOrbit.mul p r).num = SignedOrbit.mul p.num r.num := rfl
  have hmpr_den : (RatioOrbit.mul p r).den = p.den * r.den := rfl
  have hmqr_num : (RatioOrbit.mul q r).num = SignedOrbit.mul q.num r.num := rfl
  have hmqr_den : (RatioOrbit.mul q r).den = q.den * r.den := rfl
  rw [hmpr_num, hmpr_den, hmqr_num, hmqr_den] at h
  rw [SignedOrbit.mul_toInt, SignedOrbit.mul_toInt] at h
  rw [DistinctionNat.toNat_mul, DistinctionNat.toNat_mul] at h
  rw [Int.natCast_mul, Int.natCast_mul] at h
  apply Int.eq_of_mul_eq_mul_right hrd_ne
  apply Int.eq_of_mul_eq_mul_right hrn_ne
  linear_combination h

theorem ltQ_mul_pos_right (p q r : RatioOrbit) (hr : ltQ RatioOrbit.zero r)
    (hpq : ltQ p q) :
    ltQ (RatioOrbit.mul p r) (RatioOrbit.mul q r) :=
  ⟨leQ_mul_nonneg_right p q r hr.1 hpq.1,
   fun hce => hpq.2 (crossEq_mul_pos_right_cancel p q r hr.2 hce)⟩

end ActualMathematics.PRCGrow.RatioOrbitLtMulPosRight

import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.RatioOrbitLeReflTotal

namespace ActualMathematics.PRCGrow.RatioOrbitOrderMulNonneg

open ActualMathematics
open ActualMathematics.PRCGrow.RatioOrbitLeReflTotal

theorem leQ_mul_nonneg_right (p q r : RatioOrbit)
    (hr : leQ RatioOrbit.zero r) (hpq : leQ p q) :
    leQ (RatioOrbit.mul p r) (RatioOrbit.mul q r) := by
  unfold leQ at hpq hr ⊢
  rw [SignedOrbit.le_iff_toInt_le] at hpq hr ⊢
  simp only [SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt] at hpq hr ⊢
  have hpr_num : (RatioOrbit.mul p r).num = SignedOrbit.mul p.num r.num := rfl
  have hpr_den : (RatioOrbit.mul p r).den = p.den * r.den := rfl
  have hqr_num : (RatioOrbit.mul q r).num = SignedOrbit.mul q.num r.num := rfl
  have hqr_den : (RatioOrbit.mul q r).den = q.den * r.den := rfl
  rw [hpr_num, hpr_den, hqr_num, hqr_den]
  simp only [SignedOrbit.mul_toInt]
  rw [DistinctionNat.toNat_mul, DistinctionNat.toNat_mul]
  have hzero_num : RatioOrbit.zero.num = SignedOrbit.zero := rfl
  rw [hzero_num] at hr
  simp only [SignedOrbit.zero_toInt] at hr
  rw [Int.zero_mul] at hr
  have hz : (0 : ℤ) < RatioOrbit.zero.den.toNat := by
    have := RatioOrbit.den_toNat_ne_zero RatioOrbit.zero
    omega
  have hr_nonneg : 0 ≤ r.num.toInt := by
    by_contra h
    push_neg at h
    have hneg : r.num.toInt * (RatioOrbit.zero.den.toNat : ℤ) < 0 :=
      Int.mul_neg_of_neg_of_pos h hz
    omega
  have hrf : 0 ≤ r.num.toInt * (r.den.toNat : ℤ) := by
    apply Int.mul_nonneg hr_nonneg
    have := RatioOrbit.den_toNat_ne_zero r
    omega
  have h : p.num.toInt * (q.den.toNat : ℤ) * (r.num.toInt * (r.den.toNat : ℤ)) ≤
            q.num.toInt * (p.den.toNat : ℤ) * (r.num.toInt * (r.den.toNat : ℤ)) :=
    Int.mul_le_mul_of_nonneg_right hpq hrf
  simp only [Nat.cast_mul]
  have hdiff : (q.num.toInt * r.num.toInt * ((p.den.toNat : ℤ) * (r.den.toNat : ℤ))) -
               (p.num.toInt * r.num.toInt * ((q.den.toNat : ℤ) * (r.den.toNat : ℤ))) =
               (q.num.toInt * (p.den.toNat : ℤ) * (r.num.toInt * (r.den.toNat : ℤ))) -
               (p.num.toInt * (q.den.toNat : ℤ) * (r.num.toInt * (r.den.toNat : ℤ))) := by ring
  have hsub : 0 ≤ (q.num.toInt * r.num.toInt * ((p.den.toNat : ℤ) * (r.den.toNat : ℤ))) -
                   (p.num.toInt * r.num.toInt * ((q.den.toNat : ℤ) * (r.den.toNat : ℤ))) := by
    rw [hdiff]
    exact Int.sub_nonneg.mpr h
  exact Int.sub_nonneg.mp hsub

end ActualMathematics.PRCGrow.RatioOrbitOrderMulNonneg

import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.RatioOrbitLeReflTotal
import ActualMathematics.Grow.SignedOrbitNonnegFlagMulOfOrbitRightOfNeZeroChoiceFree
import ActualMathematics.Grow.SignedOrbitLeProductRightFactorIffOfBalancedChoiceFree
import ActualMathematics.Grow.SignedOrbitLeOfProductRightFactorIffOfBalancedChoiceFree
import ActualMathematics.Grow.SignedOrbitLeCongrOfBalancedChoiceFree
import ActualMathematics.Grow.SignedOrbitMulBalancedZeroOfBalancedZeroRightChoiceFree
import ActualMathematics.Grow.SignedOrbitZeroLeIffNonnegFlagChoiceFree
import ActualMathematics.Grow.SignedOrbitLeMulRightIffOfNonnegFlagOfNotBalancedZeroChoiceFree

namespace ActualMathematics.PRCGrow.RatioOrbitOrderMulNonneg

open ActualMathematics
open ActualMathematics.PRCGrow.RatioOrbitLeReflTotal

theorem leQ_mul_nonneg_right : ∀ p q r, leQ RatioOrbit.zero r → leQ p q → leQ (RatioOrbit.mul p r) (RatioOrbit.mul q r) := by
  intro p q r hr0 hpq
  unfold leQ at hr0 hpq ⊢
  unfold RatioOrbit.mul at ⊢
  rw [SignedOrbit.le_iff_toInt_le] at hr0 hpq ⊢
  simp only [SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt, DistinctionNat.toNat_mul] at hr0 hpq ⊢
  have h0num : RatioOrbit.zero.num.toInt = 0 := by
    unfold RatioOrbit.zero
    simp only [SignedOrbit.zero_toInt]
  have h0den : RatioOrbit.zero.den.toNat = 1 := by
    unfold RatioOrbit.zero
    rfl
  rw [h0num, h0den] at hr0
  push_cast at hr0 hpq ⊢
  have h_rn : 0 ≤ r.num.toInt := by omega
  have h_rd : 0 ≤ (r.den.toNat : ℤ) := by omega
  have h_coeff : 0 ≤ r.num.toInt * (r.den.toNat : ℤ) := Int.mul_nonneg h_rn h_rd
  have h_diff : 0 ≤ q.num.toInt * (p.den.toNat : ℤ) - p.num.toInt * (q.den.toNat : ℤ) := by omega
  have h_prod : 0 ≤ r.num.toInt * (r.den.toNat : ℤ) * (q.num.toInt * (p.den.toNat : ℤ) - p.num.toInt * (q.den.toNat : ℤ)) :=
    Int.mul_nonneg h_coeff h_diff
  have h_identity : q.num.toInt * r.num.toInt * ((p.den.toNat : ℤ) * (r.den.toNat : ℤ))
                    - p.num.toInt * r.num.toInt * ((q.den.toNat : ℤ) * (r.den.toNat : ℤ))
      = r.num.toInt * (r.den.toNat : ℤ) * (q.num.toInt * (p.den.toNat : ℤ) - p.num.toInt * (q.den.toNat : ℤ)) := by
    ring
  rw [← h_identity] at h_prod
  omega

end ActualMathematics.PRCGrow.RatioOrbitOrderMulNonneg

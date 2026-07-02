import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.RatioOrbitLeReflTotal
import ActualMathematics.Orbit

namespace ActualMathematics.PRCGrow.SignedOrbitMulBalancedZeroOfBalancedZeroRightChoiceFree

open ActualMathematics

theorem mul_balanced_zero_of_balanced_zero_right_cf
    (z w : SignedOrbit)
    (hw : w.balanced SignedOrbit.zero) :
    (z.mul w).balanced SignedOrbit.zero := by
  rw [SignedOrbit.balanced_iff_toNat_eq] at hw ⊢
  simp only [SignedOrbit.mul_pos, SignedOrbit.mul_neg, SignedOrbit.zero,
    DistinctionNat.toNat_add, DistinctionNat.toNat_mul, DistinctionNat.toNat_zero,
    Nat.add_zero, Nat.zero_add] at hw ⊢
  rw [hw]

end ActualMathematics.PRCGrow.SignedOrbitMulBalancedZeroOfBalancedZeroRightChoiceFree

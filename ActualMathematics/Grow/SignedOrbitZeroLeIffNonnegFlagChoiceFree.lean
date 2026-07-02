import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.RatioOrbitLeReflTotal
import ActualMathematics.Orbit
import ActualMathematics.OrbitArithmetic
import ActualMathematics.Grow.SignedOrbitOrderChoiceFree

namespace ActualMathematics.PRCGrow.SignedOrbitZeroLeIffNonnegFlagChoiceFree

open ActualMathematics
open ActualMathematics.PRCGrow.SignedOrbitOrderChoiceFree

theorem zero_le_iff_nonnegFlag_cf (z : SignedOrbit) :
    SignedOrbit.le SignedOrbit.zero z ↔ z.nonnegFlag = true := by
  rw [le_iff_nonnegFlag_sub_cf]
  unfold SignedOrbit.nonnegFlag
  rw [leq_eq_true_iff_cf, leq_eq_true_iff_cf]
  have hp : (SignedOrbit.sub z SignedOrbit.zero).pos = z.pos + DistinctionNat.zero := rfl
  have hn : (SignedOrbit.sub z SignedOrbit.zero).neg = z.neg + DistinctionNat.zero := rfl
  rw [hp, hn, DistinctionNat.toNat_add, DistinctionNat.toNat_add,
      DistinctionNat.toNat_zero, Nat.add_zero, Nat.add_zero]

end ActualMathematics.PRCGrow.SignedOrbitZeroLeIffNonnegFlagChoiceFree

import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.SignedOrbitZeroLeIffNonnegFlagChoiceFree
import ActualMathematics.Orbit

namespace ActualMathematics.PRCGrow.SignedOrbitNonnegFlagSubIffLeChoiceFree

open ActualMathematics
open ActualMathematics.PRCGrow.SignedOrbitZeroLeIffNonnegFlagChoiceFree
open SignedOrbit

theorem nonnegFlag_sub_iff_le_cf (a b : SignedOrbit) :
    (a.sub b).nonnegFlag = true ↔ b.le a := by
  rw [← zero_le_iff_nonnegFlag_cf]
  unfold le
  exact nonneg_iff_of_balanced (sub_zero_balanced _)

end ActualMathematics.PRCGrow.SignedOrbitNonnegFlagSubIffLeChoiceFree

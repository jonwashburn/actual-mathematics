import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.RatioOrbitLeReflTotal
import ActualMathematics.Orbit
import ActualMathematics.Grow.SignedOrbitLeCongrRightOfBalancedChoiceFree
import ActualMathematics.Grow.SignedOrbitLeCongrLeftOfBalancedChoiceFree

namespace ActualMathematics.PRCGrow.SignedOrbitLeCongrOfBalancedChoiceFree

open ActualMathematics
open ActualMathematics.PRCGrow.SignedOrbitLeCongrRightOfBalancedChoiceFree
open ActualMathematics.PRCGrow.SignedOrbitLeCongrLeftOfBalancedChoiceFree

theorem le_congr_of_balanced_cf {a a' b b' : SignedOrbit}
    (ha : SignedOrbit.balanced a a') (hb : SignedOrbit.balanced b b') :
    SignedOrbit.le a b ↔ SignedOrbit.le a' b' :=
  (le_congr_left_of_balanced_cf ha).trans (le_congr_right_of_balanced_cf hb)

end ActualMathematics.PRCGrow.SignedOrbitLeCongrOfBalancedChoiceFree

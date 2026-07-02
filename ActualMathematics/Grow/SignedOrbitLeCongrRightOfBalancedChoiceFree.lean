import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.RatioOrbitLeReflTotal
import ActualMathematics.Orbit
import ActualMathematics.Grow.SignedOrbitOrderChoiceFree

namespace ActualMathematics.PRCGrow.SignedOrbitLeCongrRightOfBalancedChoiceFree

open ActualMathematics
open ActualMathematics.PRCGrow.SignedOrbitOrderChoiceFree

theorem le_congr_right_of_balanced_cf {a b b' : SignedOrbit}
    (h : b.balanced b') :
    a.le b ↔ a.le b' := by
  rw [SignedOrbit.balanced_iff_toNat_eq] at h
  constructor
  · intro hle
    rw [le_iff_toNat_cf] at hle ⊢
    omega
  · intro hle
    rw [le_iff_toNat_cf] at hle ⊢
    omega

end ActualMathematics.PRCGrow.SignedOrbitLeCongrRightOfBalancedChoiceFree

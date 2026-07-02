import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.RatioOrbitLeReflTotal
import ActualMathematics.Orbit
import ActualMathematics.Grow.SignedOrbitOrderChoiceFree

namespace ActualMathematics.PRCGrow.SignedOrbitLeCongrLeftOfBalancedChoiceFree

open ActualMathematics
open ActualMathematics.PRCGrow.SignedOrbitOrderChoiceFree

theorem le_congr_left_of_balanced_cf {a a' b : SignedOrbit}
    (h : SignedOrbit.balanced a a') :
    SignedOrbit.le a b ↔ SignedOrbit.le a' b := by
  rw [SignedOrbit.balanced_iff_toNat_eq] at h
  constructor
  · intro hle
    rw [le_iff_toNat_cf] at hle ⊢
    omega
  · intro hle
    rw [le_iff_toNat_cf] at hle ⊢
    omega

end ActualMathematics.PRCGrow.SignedOrbitLeCongrLeftOfBalancedChoiceFree

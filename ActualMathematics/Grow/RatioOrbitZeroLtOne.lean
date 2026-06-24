import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.RatioOrbitLeReflTotal
import ActualMathematics.Grow.RatioOrbitLtTrichotomy

namespace ActualMathematics.PRCGrow.RatioOrbitZeroLtOne

open ActualMathematics
open ActualMathematics.PRCGrow.RatioOrbitLeReflTotal
open ActualMathematics.PRCGrow.RatioOrbitLtTrichotomy

/-- The delta-native rational order has `0 < 1`: the unit is strictly positive.
`ltQ` unfolds to `leQ ∧ ¬ crossEq`.  The `leQ` part reduces, via
`SignedOrbit.le_iff_toInt_le` and the toInt computation, to `0 ≤ 1` on the
integer display of the cross product; the `¬ crossEq` part reduces, via
`RatioOrbit.crossEq_iff_toIntCross`, to the atomic disequality `0 ≠ 1`.
Each leaf is an ATOMIC decidable (in)equality, closed choice-free by `decide`. -/
theorem zero_ltQ_one : ltQ RatioOrbit.zero RatioOrbit.one := by
  unfold ltQ
  constructor
  · -- leQ part: cross-product inequality reduces to `0 ≤ 1` on `toInt`.
    unfold leQ
    rw [SignedOrbit.le_iff_toInt_le]
    decide
  · -- ¬ crossEq part: integer cross bridge gives the atomic `0 ≠ 1`.
    rw [RatioOrbit.crossEq_iff_toIntCross]
    decide

end ActualMathematics.PRCGrow.RatioOrbitZeroLtOne

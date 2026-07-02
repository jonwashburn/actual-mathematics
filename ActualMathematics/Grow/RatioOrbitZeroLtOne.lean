import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.RatioOrbitLeReflTotal
import ActualMathematics.Grow.RatioOrbitLtTrichotomy
import ActualMathematics.Grow.SignedOrbitOrderChoiceFree

namespace ActualMathematics.PRCGrow.RatioOrbitZeroLtOne

open ActualMathematics.PRCGrow.RatioOrbitLeReflTotal
open ActualMathematics.PRCGrow.RatioOrbitLtTrichotomy
open ActualMathematics.PRCGrow.SignedOrbitOrderChoiceFree
open ActualMathematics

theorem zero_ltQ_one : ltQ RatioOrbit.zero RatioOrbit.one := by
  unfold ltQ
  refine ⟨?_, ?_⟩
  · unfold leQ
    rw [le_iff_toNat_cf]
    decide
  · intro h
    have hf : ¬ RatioOrbit.crossEq RatioOrbit.zero RatioOrbit.one := by decide
    exact hf h

end ActualMathematics.PRCGrow.RatioOrbitZeroLtOne

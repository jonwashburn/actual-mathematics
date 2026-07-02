import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Orbit
import ActualMathematics.Grow.SignedOrbitOrderChoiceFree

namespace ActualMathematics.PRCGrow.RatioOrbitLeReflTotal

open ActualMathematics
open ActualMathematics.PRCGrow.SignedOrbitOrderChoiceFree

/-- Cross-multiplication order on `RatioOrbit`: `leQ p q` iff the signed orbit
    `p.num * q.den` is `≤` the signed orbit `q.num * p.den`, where the positive
    distinctions (dens) are cast in via `SignedOrbit.ofOrbit`. -/
def leQ (p q : RatioOrbit) : Prop :=
  SignedOrbit.le
    (SignedOrbit.mul p.num (SignedOrbit.ofOrbit q.den))
    (SignedOrbit.mul q.num (SignedOrbit.ofOrbit p.den))

/-- Reflexivity of `leQ`: every rational is ≤ itself. Proved by `le_refl_cf`
    at the cross-product, which is literally the same signed orbit on both sides. -/
theorem leQ_refl (p : RatioOrbit) : leQ p p := by
  unfold leQ
  exact le_refl_cf _

/-- Totality of `leQ`: for any two rationals, one is ≤ the other. Proved by
    `le_total_cf` at the two cross-products. -/
theorem leQ_total (p q : RatioOrbit) : leQ p q ∨ leQ q p := by
  unfold leQ
  exact le_total_cf _ _

end ActualMathematics.PRCGrow.RatioOrbitLeReflTotal

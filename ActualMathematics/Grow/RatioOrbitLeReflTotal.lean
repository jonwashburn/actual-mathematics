import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Orbit

namespace ActualMathematics.PRCGrow.RatioOrbitLeReflTotal

open ActualMathematics

/-- Cross-multiplication order on `RatioOrbit` via the internal `SignedOrbit.le`. -/
def leQ (p q : RatioOrbit) : Prop :=
  SignedOrbit.le (SignedOrbit.mul p.num (SignedOrbit.ofOrbit q.den))
                 (SignedOrbit.mul q.num (SignedOrbit.ofOrbit p.den))

theorem leQ_refl (p : RatioOrbit) : leQ p p :=
  SignedOrbit.le_refl _

theorem leQ_total (p q : RatioOrbit) : leQ p q ∨ leQ q p :=
  SignedOrbit.le_total _ _

end ActualMathematics.PRCGrow.RatioOrbitLeReflTotal

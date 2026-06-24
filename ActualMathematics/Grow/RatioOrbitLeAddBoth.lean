import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.RatioOrbitLeReflTotal
import ActualMathematics.Grow.RatioOrbitLeTransAntisymm
import ActualMathematics.Grow.RatioOrbitOrderAddMono
import ActualMathematics.Grow.RatioOrbitLeWellDef

namespace ActualMathematics.PRCGrow.RatioOrbitLeAddBoth

open ActualMathematics
open ActualMathematics.PRCGrow.RatioOrbitLeReflTotal
open ActualMathematics.PRCGrow.RatioOrbitLeTransAntisymm
open ActualMathematics.PRCGrow.RatioOrbitOrderAddMono
open ActualMathematics.PRCGrow.RatioOrbitLeWellDef

/-- Addition on `RatioOrbit` is commutative up to cross-equality. -/
theorem crossEq_add_comm (x y : RatioOrbit) :
    RatioOrbit.crossEq (RatioOrbit.add x y) (RatioOrbit.add y x) := by
  rw [RatioOrbit.crossEq_iff_toIntCross]
  simp only [RatioOrbit.add, SignedOrbit.add_toInt, SignedOrbit.scaleByNat_toInt,
    SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt, DistinctionNat.toNat_mul]
  push_cast
  ring

/-- Two-sided additive monotonicity of the delta-native rational order. -/
theorem leQ_add (a b c d : RatioOrbit) (hab : leQ a b) (hcd : leQ c d) :
    leQ (RatioOrbit.add a c) (RatioOrbit.add b d) := by
  -- Add `c` on the right of `a ≤ b`.
  have h1 : leQ (RatioOrbit.add a c) (RatioOrbit.add b c) := leQ_add_right a b c hab
  -- Add `b` on the right of `c ≤ d`.
  have h2 : leQ (RatioOrbit.add c b) (RatioOrbit.add d b) := leQ_add_right c d b hcd
  -- Commutativity (up to crossEq) of the involved sums.
  have hcb : RatioOrbit.crossEq (RatioOrbit.add c b) (RatioOrbit.add b c) :=
    crossEq_add_comm c b
  have hdb : RatioOrbit.crossEq (RatioOrbit.add d b) (RatioOrbit.add b d) :=
    crossEq_add_comm d b
  -- Transport `h2` along the cross-equalities to obtain `leQ (b+c) (b+d)`.
  have step1 : leQ (RatioOrbit.add b c) (RatioOrbit.add d b) :=
    (leQ_congr_left (RatioOrbit.add c b) (RatioOrbit.add b c) (RatioOrbit.add d b) hcb).mp h2
  have step2 : leQ (RatioOrbit.add b c) (RatioOrbit.add b d) :=
    (leQ_congr_right (RatioOrbit.add b c) (RatioOrbit.add d b) (RatioOrbit.add b d) hdb).mp step1
  -- Chain with transitivity.
  exact leQ_trans (RatioOrbit.add a c) (RatioOrbit.add b c) (RatioOrbit.add b d) h1 step2

end ActualMathematics.PRCGrow.RatioOrbitLeAddBoth

import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.RatioOrbitLeReflTotal

namespace ActualMathematics.PRCGrow.RatioOrbitOrderAddMono

open ActualMathematics
open ActualMathematics.PRCGrow.RatioOrbitLeReflTotal

theorem leQ_add_right (p q r : RatioOrbit) (h : leQ p q) :
    leQ (RatioOrbit.add p r) (RatioOrbit.add q r) := by
  unfold leQ at h ⊢
  rw [SignedOrbit.le_iff_toInt_le] at h ⊢
  simp only [SignedOrbit.scaleByNat_toInt, SignedOrbit.mul_toInt,
             SignedOrbit.ofOrbit_toInt] at h
  unfold RatioOrbit.add
  simp only [SignedOrbit.scaleByNat_toInt, SignedOrbit.mul_toInt,
             SignedOrbit.ofOrbit_toInt, SignedOrbit.add_toInt,
             DistinctionNat.toNat_mul]
  push_cast
  rw [← Int.sub_nonneg]
  have key : (q.num.toInt * ↑(r.den.toNat) + r.num.toInt * ↑(q.den.toNat)) * (↑(p.den.toNat) * ↑(r.den.toNat)) -
      (p.num.toInt * ↑(r.den.toNat) + r.num.toInt * ↑(p.den.toNat)) * (↑(q.den.toNat) * ↑(r.den.toNat)) =
      (q.num.toInt * ↑(p.den.toNat) - p.num.toInt * ↑(q.den.toNat)) * (↑(r.den.toNat) * ↑(r.den.toNat)) := by
    ring
  rw [key]
  exact Int.mul_nonneg (by rw [Int.sub_nonneg]; exact h)
    (Int.mul_nonneg (by omega) (by omega))

end ActualMathematics.PRCGrow.RatioOrbitOrderAddMono

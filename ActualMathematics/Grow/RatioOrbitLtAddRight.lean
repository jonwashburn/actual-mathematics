import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.RatioOrbitLeReflTotal
import ActualMathematics.Grow.RatioOrbitLtTrichotomy
import ActualMathematics.Grow.RatioOrbitOrderAddMono

namespace ActualMathematics.PRCGrow.RatioOrbitLtAddRight

open ActualMathematics
open ActualMathematics.PRCGrow.RatioOrbitLeReflTotal
open ActualMathematics.PRCGrow.RatioOrbitLtTrichotomy
open ActualMathematics.PRCGrow.RatioOrbitOrderAddMono

theorem ltQ_add_right (p q r : RatioOrbit) (h : ltQ p q) :
    ltQ (RatioOrbit.add p r) (RatioOrbit.add q r) := by
  unfold ltQ at h ⊢
  refine ⟨leQ_add_right p q r h.1, ?_⟩
  intro hce
  apply h.2
  rw [RatioOrbit.crossEq_iff_toIntCross] at hce ⊢
  unfold RatioOrbit.add at hce
  simp only [SignedOrbit.add_toInt, SignedOrbit.mul_toInt,
             SignedOrbit.scaleByNat_toInt, SignedOrbit.ofOrbit_toInt,
             DistinctionNat.toNat_mul] at hce
  push_cast at hce
  have hf : (r.den.toNat : ℤ) ≠ 0 := by
    have := r.den_toNat_ne_zero
    omega
  have key : (r.den.toNat : ℤ) * ((r.den.toNat : ℤ) *
            (p.num.toInt * (q.den.toNat : ℤ) - q.num.toInt * (p.den.toNat : ℤ))) = 0 := by
    linear_combination hce
  have key2 : (r.den.toNat : ℤ) *
            (p.num.toInt * (q.den.toNat : ℤ) - q.num.toInt * (p.den.toNat : ℤ)) = 0 := by
    apply Int.eq_of_mul_eq_mul_right hf
    linear_combination key
  have key3 : p.num.toInt * (q.den.toNat : ℤ) - q.num.toInt * (p.den.toNat : ℤ) = 0 := by
    apply Int.eq_of_mul_eq_mul_right hf
    linear_combination key2
  omega

end ActualMathematics.PRCGrow.RatioOrbitLtAddRight

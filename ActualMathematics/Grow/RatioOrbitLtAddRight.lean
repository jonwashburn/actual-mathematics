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

theorem crossEq_add_right_cancel (p q r : RatioOrbit)
    (h : RatioOrbit.crossEq (RatioOrbit.add p r) (RatioOrbit.add q r)) :
    RatioOrbit.crossEq p q := by
  unfold RatioOrbit.crossEq at h ⊢
  simp only [RatioOrbit.add] at h
  rw [SignedOrbit.balanced_iff_toNat_eq] at h ⊢
  simp only [SignedOrbit.scaleByNat_pos, SignedOrbit.scaleByNat_neg,
             SignedOrbit.add_pos, SignedOrbit.add_neg,
             DistinctionNat.toNat_add, DistinctionNat.toNat_mul] at h ⊢
  have hdr : 0 < r.den.toNat := Nat.pos_of_ne_zero (RatioOrbit.den_toNat_ne_zero r)
  apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hdr hdr)
  ring_nf at h ⊢
  omega

theorem ltQ_add_right (p q r : RatioOrbit) (h : ltQ p q) :
    ltQ (RatioOrbit.add p r) (RatioOrbit.add q r) :=
  ⟨leQ_add_right p q r h.1, fun hce => h.2 (crossEq_add_right_cancel p q r hce)⟩

end ActualMathematics.PRCGrow.RatioOrbitLtAddRight

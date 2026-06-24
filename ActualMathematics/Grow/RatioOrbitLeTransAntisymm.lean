import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.RatioOrbitLeReflTotal

namespace ActualMathematics.PRCGrow.RatioOrbitLeTransAntisymm

open ActualMathematics
open ActualMathematics.PRCGrow.RatioOrbitLeReflTotal

theorem leQ_trans (p q r : RatioOrbit) (hpq : leQ p q) (hqr : leQ q r) : leQ p r := by
  unfold leQ at hpq hqr ⊢
  rw [SignedOrbit.le_iff_toInt_le] at hpq hqr ⊢
  simp only [SignedOrbit.scaleByNat_toInt, SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt] at hpq hqr ⊢
  have hp0 : (0 : ℤ) ≤ (p.den.toNat : ℤ) := by have := RatioOrbit.den_toNat_ne_zero p; omega
  have hr0 : (0 : ℤ) ≤ (r.den.toNat : ℤ) := by have := RatioOrbit.den_toNat_ne_zero r; omega
  have hqpos : (0 : ℤ) < (q.den.toNat : ℤ) := by have := RatioOrbit.den_toNat_ne_zero q; omega
  have hpq' : 0 ≤ q.num.toInt * (p.den.toNat : ℤ) - p.num.toInt * (q.den.toNat : ℤ) := by omega
  have hqr' : 0 ≤ r.num.toInt * (q.den.toNat : ℤ) - q.num.toInt * (r.den.toNat : ℤ) := by omega
  have e1 := Int.mul_nonneg hpq' hr0
  have e2 := Int.mul_nonneg hqr' hp0
  have key : 0 ≤ r.num.toInt * (q.den.toNat : ℤ) * (p.den.toNat : ℤ)
              - p.num.toInt * (q.den.toNat : ℤ) * (r.den.toNat : ℤ) := by
    have hrw : r.num.toInt * (q.den.toNat : ℤ) * (p.den.toNat : ℤ)
                - p.num.toInt * (q.den.toNat : ℤ) * (r.den.toNat : ℤ)
        = (q.num.toInt * (p.den.toNat : ℤ) - p.num.toInt * (q.den.toNat : ℤ)) * (r.den.toNat : ℤ)
          + (r.num.toInt * (q.den.toNat : ℤ) - q.num.toInt * (r.den.toNat : ℤ)) * (p.den.toNat : ℤ) := by
      ring
    rw [hrw]; exact Int.add_nonneg e1 e2
  have key2 : p.num.toInt * (r.den.toNat : ℤ) * (q.den.toNat : ℤ)
              ≤ r.num.toInt * (p.den.toNat : ℤ) * (q.den.toNat : ℤ) := by
    have hl : p.num.toInt * (r.den.toNat : ℤ) * (q.den.toNat : ℤ)
        = p.num.toInt * (q.den.toNat : ℤ) * (r.den.toNat : ℤ) := by ring
    have hr : r.num.toInt * (p.den.toNat : ℤ) * (q.den.toNat : ℤ)
        = r.num.toInt * (q.den.toNat : ℤ) * (p.den.toNat : ℤ) := by ring
    rw [hl, hr]; omega
  exact Int.le_of_mul_le_mul_right key2 hqpos

theorem leQ_antisymm (p q : RatioOrbit) (hpq : leQ p q) (hqp : leQ q p) : RatioOrbit.crossEq p q := by
  unfold leQ at hpq hqp
  have h := SignedOrbit.le_antisymm_balanced hpq hqp
  rw [RatioOrbit.crossEq_iff_toIntCross]
  rw [SignedOrbit.balanced_iff_toInt_eq] at h
  simp only [SignedOrbit.scaleByNat_toInt, SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt] at h
  exact h

end ActualMathematics.PRCGrow.RatioOrbitLeTransAntisymm

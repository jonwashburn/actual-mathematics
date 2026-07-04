import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.RatioOrbitLeReflTotal
import ActualMathematics.Grow.SignedOrbitOrderChoiceFree

namespace ActualMathematics.PRCGrow.RatioOrbitLeWellDef

open ActualMathematics
open ActualMathematics.PRCGrow.RatioOrbitLeReflTotal
open ActualMathematics.PRCGrow.SignedOrbitOrderChoiceFree

theorem leQ_congr_left (p p' q : RatioOrbit) (h : RatioOrbit.crossEq p p') :
    (leQ p q ↔ leQ p' q) := by
  unfold RatioOrbit.crossEq at h
  rw [SignedOrbit.balanced_iff_toNat_eq] at h
  simp only [SignedOrbit.scaleByNat_pos, SignedOrbit.scaleByNat_neg,
             DistinctionNat.toNat_mul] at h
  unfold leQ
  simp only [le_iff_toNat_cf]
  simp only [SignedOrbit.mul_pos, SignedOrbit.mul_neg, SignedOrbit.ofOrbit,
             DistinctionNat.toNat_add, DistinctionNat.toNat_mul,
             DistinctionNat.toNat_zero, Nat.mul_zero, Nat.add_zero]
  have hx : 0 < p.den.toNat := Nat.pos_of_ne_zero (RatioOrbit.den_toNat_ne_zero p)
  have hx' : 0 < p'.den.toNat := Nat.pos_of_ne_zero (RatioOrbit.den_toNat_ne_zero p')
  have hy : (p.num.pos.toNat * p'.den.toNat + p'.num.neg.toNat * p.den.toNat) * q.den.toNat
      = (p'.num.pos.toNat * p.den.toNat + p.num.neg.toNat * p'.den.toNat) * q.den.toNat := by
    rw [h]
  constructor
  · intro h1
    refine Nat.le_of_mul_le_mul_left ?_ hx
    have h1x := Nat.mul_le_mul (Nat.le_refl p'.den.toNat) h1
    ring_nf at h1x hy ⊢
    omega
  · intro h1
    refine Nat.le_of_mul_le_mul_left ?_ hx'
    have h1x := Nat.mul_le_mul (Nat.le_refl p.den.toNat) h1
    ring_nf at h1x hy ⊢
    omega

theorem leQ_congr_right (p q q' : RatioOrbit) (h : RatioOrbit.crossEq q q') :
    (leQ p q ↔ leQ p q') := by
  unfold RatioOrbit.crossEq at h
  rw [SignedOrbit.balanced_iff_toNat_eq] at h
  simp only [SignedOrbit.scaleByNat_pos, SignedOrbit.scaleByNat_neg,
             DistinctionNat.toNat_mul] at h
  unfold leQ
  simp only [le_iff_toNat_cf]
  simp only [SignedOrbit.mul_pos, SignedOrbit.mul_neg, SignedOrbit.ofOrbit,
             DistinctionNat.toNat_add, DistinctionNat.toNat_mul,
             DistinctionNat.toNat_zero, Nat.mul_zero, Nat.add_zero]
  have hy : 0 < q.den.toNat := Nat.pos_of_ne_zero (RatioOrbit.den_toNat_ne_zero q)
  have hy' : 0 < q'.den.toNat := Nat.pos_of_ne_zero (RatioOrbit.den_toNat_ne_zero q')
  have hx : (q.num.pos.toNat * q'.den.toNat + q'.num.neg.toNat * q.den.toNat) * p.den.toNat
      = (q'.num.pos.toNat * q.den.toNat + q.num.neg.toNat * q'.den.toNat) * p.den.toNat := by
    rw [h]
  constructor
  · intro h1
    refine Nat.le_of_mul_le_mul_left ?_ hy
    have h1y := Nat.mul_le_mul (Nat.le_refl q'.den.toNat) h1
    ring_nf at h1y hx ⊢
    omega
  · intro h1
    refine Nat.le_of_mul_le_mul_left ?_ hy'
    have h1y := Nat.mul_le_mul (Nat.le_refl q.den.toNat) h1
    ring_nf at h1y hx ⊢
    omega

end ActualMathematics.PRCGrow.RatioOrbitLeWellDef

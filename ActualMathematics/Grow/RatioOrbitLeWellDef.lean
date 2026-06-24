import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.RatioOrbitLeReflTotal

namespace ActualMathematics.PRCGrow.RatioOrbitLeWellDef

open ActualMathematics
open ActualMathematics.PRCGrow.RatioOrbitLeReflTotal

theorem leQ_congr_left (p p' q : RatioOrbit) (h : RatioOrbit.crossEq p p') :
    leQ p q ↔ leQ p' q := by
  unfold leQ
  rw [RatioOrbit.crossEq_iff_toIntCross] at h
  have hp'den_pos : (SignedOrbit.ofOrbit p'.den).nonnegFlag = true := by
    rw [SignedOrbit.nonnegFlag_eq_true_iff, SignedOrbit.ofOrbit_toInt]
    omega
  have hp'den_nz : ¬ SignedOrbit.balanced (SignedOrbit.ofOrbit p'.den) SignedOrbit.zero := by
    rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt, SignedOrbit.ofOrbit_toInt]
    have := p'.den_toNat_ne_zero
    omega
  have hpden_pos : (SignedOrbit.ofOrbit p.den).nonnegFlag = true := by
    rw [SignedOrbit.nonnegFlag_eq_true_iff, SignedOrbit.ofOrbit_toInt]
    omega
  have hpden_nz : ¬ SignedOrbit.balanced (SignedOrbit.ofOrbit p.den) SignedOrbit.zero := by
    rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt, SignedOrbit.ofOrbit_toInt]
    have := p.den_toNat_ne_zero
    omega
  constructor
  · intro hle
    apply (SignedOrbit.le_mul_left_iff_of_nonnegFlag_of_not_balanced_zero
      (SignedOrbit.ofOrbit p.den) _ _ hpden_pos hpden_nz).mp
    have hle' := (SignedOrbit.le_mul_left_iff_of_nonnegFlag_of_not_balanced_zero
      (SignedOrbit.ofOrbit p'.den) _ _ hp'den_pos hp'den_nz).mpr hle
    rw [SignedOrbit.le_iff_toInt_le] at hle'
    rw [SignedOrbit.le_iff_toInt_le]
    simp only [SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt] at hle' ⊢
    have hL : (p'.den.toNat : ℤ) * (p.num.toInt * (q.den.toNat : ℤ)) =
              (p.den.toNat : ℤ) * (p'.num.toInt * (q.den.toNat : ℤ)) := by
      linear_combination (q.den.toNat : ℤ) * h
    have hR : (p'.den.toNat : ℤ) * (q.num.toInt * (p.den.toNat : ℤ)) =
              (p.den.toNat : ℤ) * (q.num.toInt * (p'.den.toNat : ℤ)) := by
      ring
    rw [hL, hR] at hle'
    exact hle'
  · intro hle
    apply (SignedOrbit.le_mul_left_iff_of_nonnegFlag_of_not_balanced_zero
      (SignedOrbit.ofOrbit p'.den) _ _ hp'den_pos hp'den_nz).mp
    have hle' := (SignedOrbit.le_mul_left_iff_of_nonnegFlag_of_not_balanced_zero
      (SignedOrbit.ofOrbit p.den) _ _ hpden_pos hpden_nz).mpr hle
    rw [SignedOrbit.le_iff_toInt_le] at hle'
    rw [SignedOrbit.le_iff_toInt_le]
    simp only [SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt] at hle' ⊢
    have hL : (p.den.toNat : ℤ) * (p'.num.toInt * (q.den.toNat : ℤ)) =
              (p'.den.toNat : ℤ) * (p.num.toInt * (q.den.toNat : ℤ)) := by
      linear_combination -(q.den.toNat : ℤ) * h
    have hR : (p.den.toNat : ℤ) * (q.num.toInt * (p'.den.toNat : ℤ)) =
              (p'.den.toNat : ℤ) * (q.num.toInt * (p.den.toNat : ℤ)) := by
      ring
    rw [hL, hR] at hle'
    exact hle'

theorem leQ_congr_right (p q q' : RatioOrbit) (h : RatioOrbit.crossEq q q') :
    leQ p q ↔ leQ p q' := by
  unfold leQ
  rw [RatioOrbit.crossEq_iff_toIntCross] at h
  have hq'den_pos : (SignedOrbit.ofOrbit q'.den).nonnegFlag = true := by
    rw [SignedOrbit.nonnegFlag_eq_true_iff, SignedOrbit.ofOrbit_toInt]
    omega
  have hq'den_nz : ¬ SignedOrbit.balanced (SignedOrbit.ofOrbit q'.den) SignedOrbit.zero := by
    rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt, SignedOrbit.ofOrbit_toInt]
    have := q'.den_toNat_ne_zero
    omega
  have hqden_pos : (SignedOrbit.ofOrbit q.den).nonnegFlag = true := by
    rw [SignedOrbit.nonnegFlag_eq_true_iff, SignedOrbit.ofOrbit_toInt]
    omega
  have hqden_nz : ¬ SignedOrbit.balanced (SignedOrbit.ofOrbit q.den) SignedOrbit.zero := by
    rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt, SignedOrbit.ofOrbit_toInt]
    have := q.den_toNat_ne_zero
    omega
  constructor
  · intro hle
    apply (SignedOrbit.le_mul_right_iff_of_nonnegFlag_of_not_balanced_zero
      (SignedOrbit.ofOrbit q.den) _ _ hqden_pos hqden_nz).mp
    have hle' := (SignedOrbit.le_mul_right_iff_of_nonnegFlag_of_not_balanced_zero
      (SignedOrbit.ofOrbit q'.den) _ _ hq'den_pos hq'den_nz).mpr hle
    rw [SignedOrbit.le_iff_toInt_le] at hle'
    rw [SignedOrbit.le_iff_toInt_le]
    simp only [SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt] at hle' ⊢
    have hL : (p.num.toInt * (q.den.toNat : ℤ)) * (q'.den.toNat : ℤ) =
              (p.num.toInt * (q'.den.toNat : ℤ)) * (q.den.toNat : ℤ) := by
      ring
    have hR : (q.num.toInt * (p.den.toNat : ℤ)) * (q'.den.toNat : ℤ) =
              (q'.num.toInt * (p.den.toNat : ℤ)) * (q.den.toNat : ℤ) := by
      linear_combination (p.den.toNat : ℤ) * h
    rw [hL, hR] at hle'
    exact hle'
  · intro hle
    apply (SignedOrbit.le_mul_right_iff_of_nonnegFlag_of_not_balanced_zero
      (SignedOrbit.ofOrbit q'.den) _ _ hq'den_pos hq'den_nz).mp
    have hle' := (SignedOrbit.le_mul_right_iff_of_nonnegFlag_of_not_balanced_zero
      (SignedOrbit.ofOrbit q.den) _ _ hqden_pos hqden_nz).mpr hle
    rw [SignedOrbit.le_iff_toInt_le] at hle'
    rw [SignedOrbit.le_iff_toInt_le]
    simp only [SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt] at hle' ⊢
    have hL : (p.num.toInt * (q'.den.toNat : ℤ)) * (q.den.toNat : ℤ) =
              (p.num.toInt * (q.den.toNat : ℤ)) * (q'.den.toNat : ℤ) := by
      ring
    have hR : (q'.num.toInt * (p.den.toNat : ℤ)) * (q.den.toNat : ℤ) =
              (q.num.toInt * (p.den.toNat : ℤ)) * (q'.den.toNat : ℤ) := by
      linear_combination -(p.den.toNat : ℤ) * h
    rw [hL, hR] at hle'
    exact hle'

end ActualMathematics.PRCGrow.RatioOrbitLeWellDef

import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.RatioOrbitLeReflTotal
import ActualMathematics.Grow.RatioOrbitLtTrichotomy

namespace ActualMathematics.PRCGrow.RatioOrbitRecipPos

open ActualMathematics
open ActualMathematics.PRCGrow.RatioOrbitLeReflTotal
open ActualMathematics.PRCGrow.RatioOrbitLtTrichotomy

theorem ltQ_recipNonzero_pos (p : RatioOrbit)
    (h : ¬ SignedOrbit.balanced p.num SignedOrbit.zero) :
    ltQ RatioOrbit.zero p → ltQ RatioOrbit.zero (RatioOrbit.recipNonzero p h) := by
  intro hlt
  unfold ltQ at hlt ⊢
  obtain ⟨hle, hne⟩ := hlt

  -- Basic facts
  have hzero_num : RatioOrbit.zero.num = SignedOrbit.zero := rfl
  have hzero_den_ne : RatioOrbit.zero.den ≠ DistinctionNat.zero := by
    intro hc
    have hh := RatioOrbit.den_toNat_ne_zero RatioOrbit.zero
    rw [hc] at hh
    exact hh rfl
  have hzc : (RatioOrbit.zero.den.toNat : ℤ) ≠ 0 := by
    have := RatioOrbit.den_toNat_ne_zero RatioOrbit.zero; omega

  -- p.num.toInt ≠ 0 directly from h
  have hne_num : p.num.toInt ≠ 0 := by
    intro hz
    apply h
    rw [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.zero_toInt]
    exact hz

  -- p.num.nonnegFlag = true, hence 0 ≤ p.num.toInt
  unfold leQ at hle
  have hbalzero : SignedOrbit.balanced
      (SignedOrbit.mul RatioOrbit.zero.num (SignedOrbit.ofOrbit p.den)) SignedOrbit.zero := by
    apply SignedOrbit.mul_balanced_zero_of_balanced_zero_left
    exact (SignedOrbit.balanced_iff_toInt_eq RatioOrbit.zero.num SignedOrbit.zero).mpr
      (by rw [hzero_num])
  have hle2 := (SignedOrbit.le_congr_left_of_balanced hbalzero).mp hle
  have hflagY : (SignedOrbit.mul p.num (SignedOrbit.ofOrbit RatioOrbit.zero.den)).nonnegFlag = true :=
    (SignedOrbit.zero_le_iff_nonnegFlag _).mp hle2
  have hflag : p.num.nonnegFlag = true := by
    rw [SignedOrbit.nonnegFlag_mul_ofOrbit_right_of_ne_zero p.num RatioOrbit.zero.den hzero_den_ne]
      at hflagY
    exact hflagY
  have hnonneg : 0 ≤ p.num.toInt := (SignedOrbit.nonnegFlag_eq_true_iff p.num).mp hflag
  have hpos : 0 < p.num.toInt := by omega

  -- recip.num = ofOrbit p.den
  have hrecip_num : (RatioOrbit.recipNonzero p h).num = SignedOrbit.ofOrbit p.den := by
    unfold RatioOrbit.recipNonzero
    exact if_pos hflag
  have hrecip_toInt : (RatioOrbit.recipNonzero p h).num.toInt = (p.den.toNat : ℤ) := by
    rw [hrecip_num, SignedOrbit.ofOrbit_toInt]

  refine ⟨?_, ?_⟩

  -- Goal 1 : leQ 0 recip
  · unfold leQ
    have hbalzero1 : SignedOrbit.balanced
        (SignedOrbit.mul RatioOrbit.zero.num
          (SignedOrbit.ofOrbit (RatioOrbit.recipNonzero p h).den)) SignedOrbit.zero := by
      apply SignedOrbit.mul_balanced_zero_of_balanced_zero_left
      exact (SignedOrbit.balanced_iff_toInt_eq RatioOrbit.zero.num SignedOrbit.zero).mpr
        (by rw [hzero_num])
    apply (SignedOrbit.le_congr_left_of_balanced hbalzero1).mpr
    apply (SignedOrbit.zero_le_iff_nonnegFlag _).mpr
    rw [SignedOrbit.nonnegFlag_mul_ofOrbit_right_of_ne_zero _ RatioOrbit.zero.den hzero_den_ne]
    rw [hrecip_num]
    apply (SignedOrbit.nonnegFlag_eq_true_iff _).mpr
    rw [SignedOrbit.ofOrbit_toInt]
    omega

  -- Goal 2 : ¬ crossEq 0 recip
  · rw [RatioOrbit.crossEq_iff_toIntCross]
    rw [hzero_num, SignedOrbit.zero_toInt]
    simp only [Int.zero_mul]
    rw [hrecip_toInt]
    intro hcontra
    have hmul : (0 : ℤ) * (RatioOrbit.zero.den.toNat : ℤ)
        = (p.den.toNat : ℤ) * (RatioOrbit.zero.den.toNat : ℤ) := by
      rw [Int.zero_mul]; exact hcontra
    have heq := Int.eq_of_mul_eq_mul_right hzc hmul
    have := RatioOrbit.den_toNat_ne_zero p
    omega

end ActualMathematics.PRCGrow.RatioOrbitRecipPos

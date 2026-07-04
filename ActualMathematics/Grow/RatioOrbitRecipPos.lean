import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.RatioOrbitLeReflTotal
import ActualMathematics.Grow.RatioOrbitLtTrichotomy

namespace ActualMathematics.PRCGrow.RatioOrbitRecipPos

open ActualMathematics
open ActualMathematics.PRCGrow.RatioOrbitLeReflTotal
open ActualMathematics.PRCGrow.RatioOrbitLtTrichotomy

theorem ltQ_recipNonzero_pos (p : RatioOrbit)
    (h : ¬ SignedOrbit.balanced p.num SignedOrbit.zero)
    (hlt : ltQ RatioOrbit.zero p) :
    ltQ RatioOrbit.zero (RatioOrbit.recipNonzero p h) := by
  -- Destructure hlt : ltQ 0 p into leQ 0 p and ¬ crossEq 0 p
  unfold ltQ at hlt
  obtain ⟨hle, hne⟩ := hlt
  -- Facts about RatioOrbit.zero
  have h0num : (RatioOrbit.zero).num.toInt = 0 := by
    show SignedOrbit.zero.toInt = 0
    exact SignedOrbit.zero_toInt
  have h0den : (RatioOrbit.zero).den.toNat = 1 := by decide
  -- From hle : leQ 0 p, derive 0 ≤ p.num.toInt via the integer bridge
  unfold leQ at hle
  rw [SignedOrbit.le_iff_toInt_le] at hle
  first
  | rw [SignedOrbit.scaleByNat_toInt, SignedOrbit.scaleByNat_toInt] at hle
  | rw [SignedOrbit.mul_toInt, SignedOrbit.mul_toInt,
        SignedOrbit.ofOrbit_toInt, SignedOrbit.ofOrbit_toInt] at hle
  rw [h0num, h0den] at hle
  -- From hne : ¬ crossEq 0 p, derive p.num.toInt ≠ 0 via the integer cross bridge
  rw [RatioOrbit.crossEq_iff_toIntCross] at hne
  rw [h0num, h0den] at hne
  -- Combine to get 0 < p.num.toInt
  have hpos : 0 < p.num.toInt := by omega
  -- Hence p.num.nonnegFlag = true
  have hflag : p.num.nonnegFlag = true :=
    (SignedOrbit.nonnegFlag_eq_true_iff p.num).mpr (by omega)
  -- Rewrite the if in recipNonzero to get (recipNonzero p h).num = ofOrbit p.den
  -- whose toInt = p.den.toNat, which is > 0
  have hrecip_toInt : (RatioOrbit.recipNonzero p h).num.toInt = (p.den.toNat : ℤ) := by
    unfold RatioOrbit.recipNonzero
    first
    | rw [if_pos hflag, SignedOrbit.ofOrbit_toInt]
    | (simp only [if_pos hflag]; rw [SignedOrbit.ofOrbit_toInt])
  have hden_pos : (p.den.toNat : ℤ) > 0 := by
    have := RatioOrbit.den_toNat_ne_zero p
    omega
  -- Prove ltQ 0 recip = leQ 0 recip ∧ ¬ crossEq 0 recip
  unfold ltQ
  refine ⟨?_, ?_⟩
  -- leQ 0 recip via le_iff_toInt_le: reduces to 0 ≤ p.den.toNat
  · unfold leQ
    rw [SignedOrbit.le_iff_toInt_le]
    first
    | rw [SignedOrbit.scaleByNat_toInt, SignedOrbit.scaleByNat_toInt]
    | rw [SignedOrbit.mul_toInt, SignedOrbit.mul_toInt,
          SignedOrbit.ofOrbit_toInt, SignedOrbit.ofOrbit_toInt]
    rw [h0num, h0den, hrecip_toInt]
    omega
  -- ¬ crossEq 0 recip via crossEq_iff_toIntCross: reduces to p.den.toNat ≠ 0
  · rw [RatioOrbit.crossEq_iff_toIntCross]
    rw [h0num, h0den, hrecip_toInt]
    omega

end ActualMathematics.PRCGrow.RatioOrbitRecipPos

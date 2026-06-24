import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.RatioOrbitLeReflTotal
import ActualMathematics.Grow.RatioOrbitLtTrichotomy

namespace ActualMathematics.PRCGrow.RatioOrbitMulPos

open ActualMathematics
open ActualMathematics.PRCGrow.RatioOrbitLeReflTotal
open ActualMathematics.PRCGrow.RatioOrbitLtTrichotomy

theorem ltQ_mul_pos (p q : RatioOrbit)
    (hp : ltQ RatioOrbit.zero p) (hq : ltQ RatioOrbit.zero q) :
    ltQ RatioOrbit.zero (RatioOrbit.mul p q) := by
  unfold ltQ at hp hq
  obtain ⟨hp_le, hp_ne⟩ := hp
  obtain ⟨hq_le, hq_ne⟩ := hq
  have hz_num : RatioOrbit.zero.num.toInt = 0 := SignedOrbit.zero_toInt
  have hz_den : RatioOrbit.zero.den.toNat = 1 := by decide
  unfold leQ at hp_le hq_le
  rw [SignedOrbit.le_iff_toInt_le] at hp_le hq_le
  simp only [SignedOrbit.mul_toInt, SignedOrbit.scaleByNat_toInt, SignedOrbit.ofOrbit_toInt] at hp_le hq_le
  rw [hz_num, hz_den] at hp_le hq_le
  rw [RatioOrbit.crossEq_iff_toIntCross] at hp_ne hq_ne
  rw [hz_num, hz_den] at hp_ne hq_ne
  have hp_pos : 0 < p.num.toInt := by omega
  have hq_pos : 0 < q.num.toInt := by omega
  have hmul_pos : 0 < p.num.toInt * q.num.toInt := Int.mul_pos hp_pos hq_pos
  have hmul_toInt : (RatioOrbit.mul p q).num.toInt = p.num.toInt * q.num.toInt :=
    SignedOrbit.mul_toInt p.num q.num
  have hmul_den : (RatioOrbit.mul p q).den.toNat = p.den.toNat * q.den.toNat :=
    DistinctionNat.toNat_mul p.den q.den
  unfold ltQ
  refine ⟨?_, ?_⟩
  · unfold leQ
    rw [SignedOrbit.le_iff_toInt_le]
    simp only [SignedOrbit.mul_toInt, SignedOrbit.scaleByNat_toInt, SignedOrbit.ofOrbit_toInt,
               hmul_toInt, hmul_den, hz_num, hz_den]
    omega
  · rw [RatioOrbit.crossEq_iff_toIntCross]
    simp only [hmul_toInt, hmul_den, hz_num, hz_den]
    omega

end ActualMathematics.PRCGrow.RatioOrbitMulPos

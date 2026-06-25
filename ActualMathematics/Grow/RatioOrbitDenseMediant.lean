import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.RatioOrbitLeReflTotal
import ActualMathematics.Grow.RatioOrbitLtTrichotomy

namespace ActualMathematics.PRCGrow.RatioOrbitDenseMediant

open ActualMathematics
open ActualMathematics.PRCGrow.RatioOrbitLeReflTotal
open ActualMathematics.PRCGrow.RatioOrbitLtTrichotomy

def mediant (p q : RatioOrbit) : RatioOrbit where
  num := SignedOrbit.add p.num q.num
  den := p.den + q.den
  den_ne_zero := by
    have hp := RatioOrbit.den_toNat_ne_zero p
    have hq := RatioOrbit.den_toNat_ne_zero q
    intro heq
    have h := DistinctionNat.toNat_add p.den q.den
    have hzero : DistinctionNat.zero.toNat = 0 := rfl
    rw [heq, hzero] at h
    omega

theorem ltQ_mediant : ∀ p q, ltQ p q → ltQ p (mediant p q) ∧ ltQ (mediant p q) q := by
  intro p q h
  unfold ltQ at h
  obtain ⟨hle, hne⟩ := h
  unfold leQ at hle
  rw [SignedOrbit.le_iff_toInt_le] at hle
  simp only [SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt] at hle
  rw [RatioOrbit.crossEq_iff_toIntCross] at hne
  have hmed_num : (mediant p q).num = SignedOrbit.add p.num q.num := rfl
  have hmed_den : (mediant p q).den = p.den + q.den := rfl
  refine ⟨?_, ?_⟩
  · -- ltQ p (mediant p q)
    unfold ltQ
    refine ⟨?_, ?_⟩
    · -- leQ p (mediant p q) : a*(b+d) ≤ (a+c)*b
      unfold leQ
      rw [SignedOrbit.le_iff_toInt_le, hmed_num, hmed_den]
      simp only [SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt,
                 SignedOrbit.add_toInt, DistinctionNat.toNat_add]
      push_cast
      set a := p.num.toInt with ha
      set c := q.num.toInt with hc
      set b := (p.den.toNat : ℤ) with hb
      set d := (q.den.toNat : ℤ) with hd
      have e1 : a * (b + d) = a * b + a * d := by ring
      have e2 : (a + c) * b = a * b + c * b := by ring
      rw [e1, e2]
      omega
    · -- ¬ crossEq p (mediant p q)
      rw [RatioOrbit.crossEq_iff_toIntCross, hmed_num, hmed_den]
      simp only [SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt,
                 SignedOrbit.add_toInt, DistinctionNat.toNat_add]
      push_cast
      set a := p.num.toInt with ha
      set c := q.num.toInt with hc
      set b := (p.den.toNat : ℤ) with hb
      set d := (q.den.toNat : ℤ) with hd
      have e1 : a * (b + d) = a * b + a * d := by ring
      have e2 : (a + c) * b = a * b + c * b := by ring
      intro heq
      rw [e1, e2] at heq
      apply hne
      omega
  · -- ltQ (mediant p q) q
    unfold ltQ
    refine ⟨?_, ?_⟩
    · -- leQ (mediant p q) q : (a+c)*d ≤ c*(b+d)
      unfold leQ
      rw [SignedOrbit.le_iff_toInt_le, hmed_num, hmed_den]
      simp only [SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt,
                 SignedOrbit.add_toInt, DistinctionNat.toNat_add]
      push_cast
      set a := p.num.toInt with ha
      set c := q.num.toInt with hc
      set b := (p.den.toNat : ℤ) with hb
      set d := (q.den.toNat : ℤ) with hd
      have e3 : (a + c) * d = a * d + c * d := by ring
      have e4 : c * (b + d) = c * b + c * d := by ring
      rw [e3, e4]
      omega
    · -- ¬ crossEq (mediant p q) q
      rw [RatioOrbit.crossEq_iff_toIntCross, hmed_num, hmed_den]
      simp only [SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt,
                 SignedOrbit.add_toInt, DistinctionNat.toNat_add]
      push_cast
      set a := p.num.toInt with ha
      set c := q.num.toInt with hc
      set b := (p.den.toNat : ℤ) with hb
      set d := (q.den.toNat : ℤ) with hd
      have e3 : (a + c) * d = a * d + c * d := by ring
      have e4 : c * (b + d) = c * b + c * d := by ring
      intro heq
      rw [e3, e4] at heq
      apply hne
      omega

end ActualMathematics.PRCGrow.RatioOrbitDenseMediant

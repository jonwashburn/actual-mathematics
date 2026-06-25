import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.RatioOrbitLeReflTotal
import ActualMathematics.Grow.RatioOrbitLtTrichotomy

namespace ActualMathematics.PRCGrow.RatioOrbitDensity

open ActualMathematics
open ActualMathematics.PRCGrow.RatioOrbitLeReflTotal
open ActualMathematics.PRCGrow.RatioOrbitLtTrichotomy

def mediant (p q : RatioOrbit) : RatioOrbit where
  num := SignedOrbit.add p.num q.num
  den := p.den + q.den
  den_ne_zero := by
    intro h
    have hp := RatioOrbit.den_toNat_ne_zero p
    have hq := RatioOrbit.den_toNat_ne_zero q
    have h1 : (p.den + q.den).toNat = 0 := by rw [h]; rfl
    rw [DistinctionNat.toNat_add] at h1
    omega

theorem ltQ_dense_mediant : ∀ p q, ltQ p q → ltQ p (mediant p q) ∧ ltQ (mediant p q) q := by
  intro p q h
  unfold ltQ at h
  obtain ⟨hle, hne⟩ := h
  unfold leQ at hle
  rw [SignedOrbit.le_iff_toInt_le] at hle
  simp only [SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt,
              SignedOrbit.scaleByNat_toInt] at hle
  rw [RatioOrbit.crossEq_iff_toIntCross] at hne
  -- hle : p.num.toInt * ↑q.den.toNat ≤ q.num.toInt * ↑p.den.toNat
  -- hne : ¬ (p.num.toInt * ↑q.den.toNat = q.num.toInt * ↑p.den.toNat)
  constructor
  · -- ltQ p (mediant p q)
    unfold ltQ
    constructor
    · -- leQ p (mediant p q)
      unfold leQ
      rw [SignedOrbit.le_iff_toInt_le]
      simp only [SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt,
                  SignedOrbit.scaleByNat_toInt, mediant,
                  SignedOrbit.add_toInt, DistinctionNat.toNat_add]
      push_cast
      have hid :
          (p.num.toInt + q.num.toInt) * (p.den.toNat : ℤ)
            - p.num.toInt * ((p.den.toNat : ℤ) + (q.den.toNat : ℤ))
          = q.num.toInt * (p.den.toNat : ℤ) - p.num.toInt * (q.den.toNat : ℤ) := by
        ring
      omega
    · -- ¬ crossEq p (mediant p q)
      rw [RatioOrbit.crossEq_iff_toIntCross]
      simp only [mediant, SignedOrbit.add_toInt, DistinctionNat.toNat_add]
      push_cast
      intro hh
      apply hne
      linear_combination hh
  · -- ltQ (mediant p q) q
    unfold ltQ
    constructor
    · -- leQ (mediant p q) q
      unfold leQ
      rw [SignedOrbit.le_iff_toInt_le]
      simp only [SignedOrbit.mul_toInt, SignedOrbit.ofOrbit_toInt,
                  SignedOrbit.scaleByNat_toInt, mediant,
                  SignedOrbit.add_toInt, DistinctionNat.toNat_add]
      push_cast
      have hid :
          q.num.toInt * ((p.den.toNat : ℤ) + (q.den.toNat : ℤ))
            - (p.num.toInt + q.num.toInt) * (q.den.toNat : ℤ)
          = q.num.toInt * (p.den.toNat : ℤ) - p.num.toInt * (q.den.toNat : ℤ) := by
        ring
      omega
    · -- ¬ crossEq (mediant p q) q
      rw [RatioOrbit.crossEq_iff_toIntCross]
      simp only [mediant, SignedOrbit.add_toInt, DistinctionNat.toNat_add]
      push_cast
      intro hh
      apply hne
      linear_combination hh

end ActualMathematics.PRCGrow.RatioOrbitDensity

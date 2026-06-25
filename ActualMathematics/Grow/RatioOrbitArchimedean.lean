import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.RatioOrbitLeReflTotal

namespace ActualMathematics.PRCGrow.RatioOrbitArchimedean

open ActualMathematics
open ActualMathematics.PRCGrow.RatioOrbitLeReflTotal

def ofNat : ℕ → RatioOrbit
  | 0 => RatioOrbit.zero
  | n+1 => RatioOrbit.add (ofNat n) RatioOrbit.one

theorem one_num_toInt : RatioOrbit.one.num.toInt = 1 := by decide

theorem one_den_toNat : RatioOrbit.one.den.toNat = 1 := by decide

theorem ofNat_den_toNat (n : ℕ) : (ofNat n).den.toNat = 1 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    unfold ofNat RatioOrbit.add
    simp only [DistinctionNat.toNat_mul, ih]
    rfl

theorem ofNat_num_toInt (n : ℕ) : (ofNat n).num.toInt = (n : ℤ) := by
  induction n with
  | zero => decide
  | succ k ih =>
    unfold ofNat RatioOrbit.add
    simp only [SignedOrbit.add_toInt, SignedOrbit.mul_toInt, SignedOrbit.scaleByNat_toInt,
               SignedOrbit.ofOrbit_toInt, one_num_toInt, one_den_toNat, ofNat_den_toNat, ih,
               Nat.cast_one, mul_one, one_mul]
    omega

theorem leQ_archimedean : ∀ p : RatioOrbit, ∃ n : ℕ, leQ p (ofNat n) := by
  intro p
  refine ⟨p.num.toInt.toNat + 1, ?_⟩
  unfold leQ
  rw [SignedOrbit.le_iff_toInt_le]
  simp only [SignedOrbit.mul_toInt, SignedOrbit.scaleByNat_toInt, SignedOrbit.ofOrbit_toInt,
             ofNat_num_toInt, ofNat_den_toNat, Nat.cast_one, mul_one]
  have hd1 : 1 ≤ p.den.toNat := Nat.pos_of_ne_zero (RatioOrbit.den_toNat_ne_zero p)
  have hnat : p.num.toInt.toNat + 1 ≤ (p.num.toInt.toNat + 1) * p.den.toNat := by
    calc p.num.toInt.toNat + 1
        = (p.num.toInt.toNat + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ (p.num.toInt.toNat + 1) * p.den.toNat := Nat.mul_le_mul (Nat.le_refl _) hd1
  rw [← Nat.cast_mul]
  omega

end ActualMathematics.PRCGrow.RatioOrbitArchimedean

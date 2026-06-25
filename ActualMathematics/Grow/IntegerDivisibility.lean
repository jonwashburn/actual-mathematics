import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder

namespace ActualMathematics.PRCGrow.IntegerDivisibility

open ActualMathematics

def dvdZ (a b : SignedOrbit) : Prop :=
  ∃ c : SignedOrbit, SignedOrbit.balanced (SignedOrbit.mul a c) b

theorem dvdZ_refl (a : SignedOrbit) : dvdZ a a := by
  refine ⟨SignedOrbit.one, ?_⟩
  simp only [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.mul_toInt, SignedOrbit.one_toInt]
  ring

theorem dvdZ_trans (a b c : SignedOrbit) (hab : dvdZ a b) (hbc : dvdZ b c) : dvdZ a c := by
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hbc
  refine ⟨SignedOrbit.mul x y, ?_⟩
  have hx' := (SignedOrbit.balanced_iff_toInt_eq _ _).mp hx
  have hy' := (SignedOrbit.balanced_iff_toInt_eq _ _).mp hy
  simp only [SignedOrbit.mul_toInt] at hx' hy'
  simp only [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.mul_toInt]
  linear_combination y.toInt * hx' + hy'

theorem dvdZ_add (a b c : SignedOrbit) (hab : dvdZ a b) (hac : dvdZ a c) :
    dvdZ a (SignedOrbit.add b c) := by
  obtain ⟨x, hx⟩ := hab
  obtain ⟨y, hy⟩ := hac
  refine ⟨SignedOrbit.add x y, ?_⟩
  have hx' := (SignedOrbit.balanced_iff_toInt_eq _ _).mp hx
  have hy' := (SignedOrbit.balanced_iff_toInt_eq _ _).mp hy
  simp only [SignedOrbit.mul_toInt] at hx' hy'
  simp only [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.mul_toInt, SignedOrbit.add_toInt]
  linear_combination hx' + hy'

theorem one_dvdZ (a : SignedOrbit) : dvdZ SignedOrbit.one a := by
  refine ⟨a, ?_⟩
  simp only [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.mul_toInt, SignedOrbit.one_toInt]
  ring

theorem dvdZ_zero (a : SignedOrbit) : dvdZ a SignedOrbit.zero := by
  refine ⟨SignedOrbit.zero, ?_⟩
  simp only [SignedOrbit.balanced_iff_toInt_eq, SignedOrbit.mul_toInt, SignedOrbit.zero_toInt]
  ring

end ActualMathematics.PRCGrow.IntegerDivisibility

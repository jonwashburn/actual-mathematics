import ActualMathematics.DeltaKernel.BootstrapInitiality
import ActualMathematics.DeltaKernel.Examples
import ActualMathematics.IntegerRational
import ActualMathematics.OrbitArithmetic

/-!
# Bootstrap B2: internal arithmetic from the licensed δ signature

From the frozen syntax and its initiality, the recursion equations for `+`
and `·` hold in the canonical model, numerals evaluate correctly, and the
kernel exports concrete arithmetic theorems with empty ledger.  The existing
δ-orbit constructions then supply quotient-derived integers and rationals.

Metatheory remains Lean. Object-level arithmetic is the content of the
checked derivations and their canonical evaluation, not a second copy of
`Nat` smuggled into the object language.

Classification:
* `0` and `S` are licensed primitive term constructors.
* `+` and `·` are licensed recursion operations whose equations are checked.
* `DistinctionNat` is the initial orbit carrier, defined in the metatheory.
* `PRCInt` is quotient-derived from pairs of orbit naturals.
* `PRCRat` is quotient-derived from nonzero-denominator pairs of PRC integers.
-/

namespace ActualMathematics.DeltaKernel.Bootstrap

open ActualMathematics.DeltaKernel
open ActualMathematics
open DTerm DFormula

/-! ## Numeral evaluation -/

theorem eval_ofNat (n : Nat) (ρ : Env) : (DTerm.ofNat n).eval ρ = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [DTerm.ofNat, DTerm.eval, ih]

theorem eval_ofNat_closed (n : Nat) :
    (DTerm.ofNat n).eval (fun _ => 0) = n :=
  eval_ofNat n _

/-! ## Recursion equations in the canonical model -/

theorem eval_add_zero (t : DTerm) (ρ : Env) :
    (DTerm.add t .zero).eval ρ = t.eval ρ := by
  simp [DTerm.eval]

theorem eval_add_succ (t s : DTerm) (ρ : Env) :
    (DTerm.add t (.succ s)).eval ρ = (DTerm.succ (DTerm.add t s)).eval ρ := by
  simp only [DTerm.eval]
  exact (Nat.add_assoc (t.eval ρ) (s.eval ρ) 1).symm

theorem eval_mul_zero (t : DTerm) (ρ : Env) :
    (DTerm.mul t .zero).eval ρ = 0 := by
  simp [DTerm.eval]

theorem eval_mul_succ (t s : DTerm) (ρ : Env) :
    (DTerm.mul t (.succ s)).eval ρ =
      (DTerm.add (DTerm.mul t s) t).eval ρ := by
  simp [DTerm.eval, Nat.mul_succ]

/-! ## Kernel-certified arithmetic exports -/

theorem one_plus_one_internal :
    check [] Examples.onePlusOne =
      some (.eq (.add Examples.one Examples.one) Examples.two, .empty) :=
  Examples.onePlusOne_forced

theorem one_plus_one_exported : 1 + 1 = 2 :=
  Examples.one_plus_one_certified

theorem zero_add_forced :
    check [] Examples.zeroAdd =
      some (.all (.eq (.add .zero (.var 0)) (.var 0)), .empty) :=
  Examples.zeroAdd_forced

/-! ## Quotient-derived integer and rational carriers -/

theorem prcInt_display_injective :
    Function.Injective PRCInt.toInt :=
  PRCInt.toInt_injective

theorem prcInt_add_display (a b : PRCInt) :
    PRCInt.toInt (PRCInt.add a b) =
      PRCInt.toInt a + PRCInt.toInt b :=
  PRCInt.toInt_add a b

theorem prcInt_mul_display (a b : PRCInt) :
    PRCInt.toInt (PRCInt.mul a b) =
      PRCInt.toInt a * PRCInt.toInt b :=
  PRCInt.toInt_mul a b

theorem prcRat_add_comm (a b : PRCRat) :
    PRCRat.add a b = PRCRat.add b a :=
  PRCRat.add_comm a b

theorem prcRat_left_distrib (a b c : PRCRat) :
    PRCRat.mul a (PRCRat.add b c) =
      PRCRat.add (PRCRat.mul a b) (PRCRat.mul a c) :=
  PRCRat.left_distrib a b c

theorem prcRat_mul_recip_cancel {a : PRCRat}
    (h : a ≠ PRCRat.zero) :
    PRCRat.mul a (PRCRat.recip a) = PRCRat.one :=
  PRCRat.mul_recip_cancel₀ h

/-- B2 package: numerals, recursion equations, forced kernel exports, and
the quotient-derived integer/rational tower. -/
def BootstrapArithmeticSpec : Prop :=
  (∀ n ρ, (DTerm.ofNat n).eval ρ = n) ∧
  (∀ t ρ, (DTerm.add t .zero).eval ρ = t.eval ρ) ∧
  (∀ t s ρ,
      (DTerm.add t (.succ s)).eval ρ =
        (DTerm.succ (DTerm.add t s)).eval ρ) ∧
  (∀ t ρ, (DTerm.mul t .zero).eval ρ = 0) ∧
  (∀ t s ρ,
      (DTerm.mul t (.succ s)).eval ρ =
        (DTerm.add (DTerm.mul t s) t).eval ρ) ∧
  check [] Examples.onePlusOne =
      some (.eq (.add Examples.one Examples.one) Examples.two, .empty) ∧
  (1 + 1 = 2) ∧
  Function.Injective PRCInt.toInt ∧
  (∀ a b : PRCInt,
    PRCInt.toInt (PRCInt.add a b) =
      PRCInt.toInt a + PRCInt.toInt b) ∧
  (∀ a b : PRCInt,
    PRCInt.toInt (PRCInt.mul a b) =
      PRCInt.toInt a * PRCInt.toInt b) ∧
  (∀ a b : PRCRat,
    PRCRat.add a b = PRCRat.add b a) ∧
  (∀ a b c : PRCRat,
    PRCRat.mul a (PRCRat.add b c) =
      PRCRat.add (PRCRat.mul a b) (PRCRat.mul a c)) ∧
  (∀ a : PRCRat, a ≠ PRCRat.zero →
    PRCRat.mul a (PRCRat.recip a) = PRCRat.one)

theorem bootstrap_arithmetic : BootstrapArithmeticSpec :=
  ⟨eval_ofNat, eval_add_zero, eval_add_succ, eval_mul_zero, eval_mul_succ,
   one_plus_one_internal,
   one_plus_one_exported,
   prcInt_display_injective,
   prcInt_add_display,
   prcInt_mul_display,
   prcRat_add_comm,
   prcRat_left_distrib,
   fun a h => prcRat_mul_recip_cancel (a := a) h⟩

#print axioms prcInt_display_injective
#print axioms prcRat_mul_recip_cancel
#print axioms bootstrap_arithmetic

end ActualMathematics.DeltaKernel.Bootstrap

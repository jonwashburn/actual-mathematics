import ActualMathematics.DeltaKernel.BootstrapInitiality
import ActualMathematics.DeltaKernel.Examples

/-!
# Bootstrap B2: internal arithmetic from the licensed δ signature

From the frozen syntax and its initiality, the recursion equations for `+`
and `·` hold in the canonical model, numerals evaluate correctly, and the
kernel exports concrete arithmetic theorems with empty ledger.

Metatheory remains Lean. Object-level arithmetic is the content of the
checked derivations and their canonical evaluation, not a second copy of
`Nat` smuggled into the object language.
-/

namespace ActualMathematics.DeltaKernel.Bootstrap

open ActualMathematics.DeltaKernel
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

/-- B2 package: numerals, recursion equations, and forced kernel exports. -/
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
  (1 + 1 = 2)

theorem bootstrap_arithmetic : BootstrapArithmeticSpec :=
  ⟨eval_ofNat, eval_add_zero, eval_add_succ, eval_mul_zero, eval_mul_succ,
   one_plus_one_internal, one_plus_one_exported⟩

#print axioms bootstrap_arithmetic

end ActualMathematics.DeltaKernel.Bootstrap

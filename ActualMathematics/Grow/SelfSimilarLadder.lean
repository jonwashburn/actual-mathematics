import ActualMathematics.DeltaSpine.GoldenInt
import ActualMathematics.DeltaSpine.CostUniqueness
import ActualMathematics.Grow.PhiUniquePosRoot

namespace ActualMathematics.PRCGrow.SelfSimilarLadder

open ActualMathematics.DeltaSpine
open ActualMathematics.DeltaSpine.GoldenInt

theorem phiZpow_fib : ∀ n : Int, phiZpow (n + 2) = phiZpow (n + 1) + phiZpow n := by
  intro n
  have h2 : phiZpow (n + 2) = phiZpow n * (phi * phi) := by
    have e : n + 2 = n + 1 + 1 := by ring
    rw [e, phiZpow_add, phiZpow_add, phiZpow_one]
    ring
  have h1 : phiZpow (n + 1) = phiZpow n * phi := by
    rw [phiZpow_add, phiZpow_one]
  rw [h2, h1, phi_sq]
  ring

theorem phiZpow_fib_neg (n : Int) :
    phiZpow (-n) = phiZpow (-(n + 1)) + phiZpow (-(n + 2)) := by
  have h := phiZpow_fib (-(n + 2))
  rw [show -(n + 2) + 2 = -n by ring, show -(n + 2) + 1 = -(n + 1) by ring] at h
  exact h

theorem traceZ_fib_defect : ∀ n : Int,
    traceZ (n + 1) + traceZ n = traceZ (n + 2) + 2 * phiZpow (-(n + 1)) := by
  intro n
  have hpos := phiZpow_fib n
  have hneg := phiZpow_fib_neg n
  unfold traceZ
  linear_combination hneg - hpos

theorem traceZ_not_fib :
    ¬ (∀ n : Int, traceZ (n + 2) = traceZ (n + 1) + traceZ n) := by
  intro h
  have h0 := h 0
  revert h0
  decide

theorem phiZpow_fib_coords : ∀ n : Nat,
    phiZpow ((n : Int) + 1) = GoldenInt.mk (Nat.fib n : Int) (Nat.fib (n + 1) : Int) := by
  intro n
  induction n with
  | zero =>
      rw [show ((0 : Nat) : Int) + 1 = 1 by decide, phiZpow_one]
      rfl
  | succ k ihk =>
      have e : ((k + 1 : Nat) : Int) + 1 = ((k : Int) + 1) + 1 := by
        rw [Int.natCast_add, Int.natCast_one]
      rw [e, phiZpow_add, phiZpow_one, ihk]
      ext
      · show (Nat.fib k : Int) * phi.a + (Nat.fib (k + 1) : Int) * phi.b = (Nat.fib (k + 1) : Int)
        simp only [phi_a, phi_b]
        ring
      · show (Nat.fib k : Int) * phi.b + (Nat.fib (k + 1) : Int) * phi.a + (Nat.fib (k + 1) : Int) * phi.b = (Nat.fib (k + 1 + 1) : Int)
        have hf : Nat.fib (k + 1 + 1) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two (n := k)
        simp only [phi_a, phi_b]
        rw [hf, Int.natCast_add]
        ring

theorem bridge_inhabited :
    traceZ 0 = 2 ∧ traceZ 1 = sqrtFive ∧ SatisfiesDAlembert traceZ :=
  ⟨traceZ_zero, traceZ_one, traceZ_dAlembert⟩

theorem t5_to_t6_delta :
    (∀ h : Int → GoldenInt, h 0 = 2 → h 1 = sqrtFive → SatisfiesDAlembert h →
        (∀ n : Int, h n = traceZ n) ∧ (∀ n : Int, h (n + 2) = sqrtFive * h (n + 1) - h n)) ∧
      ((∀ n : Int, phiZpow (n + 2) = phiZpow (n + 1) + phiZpow n) ∧
        (∀ n : Nat, phiZpow ((n : Int) + 1) = GoldenInt.mk (Nat.fib n : Int) (Nat.fib (n + 1) : Int)) ∧
        (∀ n : Int, traceZ (n + 1) + traceZ n = traceZ (n + 2) + 2 * phiZpow (-(n + 1))) ∧
        ¬ (∀ n : Int, traceZ (n + 2) = traceZ (n + 1) + traceZ n)) ∧
      (∀ x : GoldenInt, x * x = x + 1 → IsPos x → x = phi) :=
  ⟨fun h h0 h1 hd => ⟨dAlembert_unique h h0 h1 hd, fun n => dAlembert_step h h1 hd n⟩,
    ⟨phiZpow_fib, phiZpow_fib_coords, traceZ_fib_defect, traceZ_not_fib⟩,
    fun x hx hp => ActualMathematics.PRCGrow.PhiUniquePosRoot.phi_unique x hx hp⟩

end ActualMathematics.PRCGrow.SelfSimilarLadder

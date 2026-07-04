import ActualMathematics.DeltaSpine.GoldenInt

namespace ActualMathematics.PRCGrow.PhiUniquePosRoot

open ActualMathematics.DeltaSpine
open ActualMathematics.DeltaSpine.GoldenInt

theorem phi_unique : ∀ x : GoldenInt, x * x = x + 1 → IsPos x → x = phi := by
  intro x hx hpos
  have h := golden_roots hx
  cases h with
  | inl h => exact h
  | inr h =>
    rw [h] at hpos
    exact absurd hpos psi_not_isPos

theorem t6_delta_forced :
    (phi * phi = phi + 1 ∧ IsPos phi) ∧
    (∀ x : GoldenInt, x * x = x + 1 → IsPos x → x = phi) := by
  exact ⟨⟨phi_sq, phi_isPos⟩, phi_unique⟩

end ActualMathematics.PRCGrow.PhiUniquePosRoot

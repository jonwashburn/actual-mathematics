/-
  ActualMathematics/MeasureForcing.lean

  The forced per-rung weight `rho = 1/phi` and the partition identity it carries,
  used by `ContinuumTax` to make the phi-native mode sum converge to `c * phi^2`.

  Provenance note. In the parent Recognition Science library `rho = phi^(-1)` is
  the T9-forced measure weight on the rung ladder, and `sum_n rho^n = phi^2` is
  the forced partition function `Z = phi^2`. That forcing derivation is a large
  dependency tree. Here we only need `rho = 1/phi`, that it lies in `[0,1)`, and
  the closed form `1 - rho = 1/phi^2` (which gives `(1 - rho)^{-1} = phi^2`), so
  this module provides exactly those from `ActualMathematics.Constants` and
  Mathlib. Self-contained PROVIDER for the demarcation results, not the forcing
  derivation.

  No project-local axioms. No sorry.
-/

import Mathlib
import ActualMathematics.Constants

namespace ActualMathematics
namespace MeasureForcing

/-- The forced per-rung weight `rho = phi^(-1)`. -/
noncomputable def rho : ℝ := 1 / Constants.phi

theorem rho_pos : 0 < rho := by
  unfold rho
  exact div_pos one_pos Constants.phi_pos

theorem rho_nonneg : 0 ≤ rho := rho_pos.le

theorem rho_lt_one : rho < 1 := by
  unfold rho
  rw [div_lt_one Constants.phi_pos]
  exact Constants.one_lt_phi

/-- `1 - rho = 1/phi^2`. With `rho = 1/phi` and `phi^2 = phi + 1`, the geometric
sum `(1 - rho)^{-1}` is exactly the partition function `Z = phi^2`. -/
theorem one_sub_rho : 1 - rho = 1 / Constants.phi ^ 2 := by
  unfold rho
  have hphi : Constants.phi ≠ 0 := Constants.phi_ne_zero
  have hsq : Constants.phi ^ 2 = Constants.phi + 1 := Constants.phi_sq
  field_simp
  nlinarith [hsq, Constants.phi_pos]

end MeasureForcing
end ActualMathematics

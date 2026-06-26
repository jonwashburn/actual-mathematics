/-
  ActualMathematics/Constants.lean

  The single forced constant this framework's analysis layer needs: the golden
  ratio phi, with the arithmetic facts (positivity, phi > 1, phi^2 = phi + 1)
  used downstream by `MeasureForcing` and `ContinuumTax`.

  Provenance note. In the parent Recognition Science library phi is forced by
  the self-similarity fixed point of the recognition cost (T6 of the forcing
  chain). That derivation is a large dependency tree. Here we only need phi's
  closed form and its three arithmetic consequences, so this module gives the
  closed form `(1 + sqrt 5) / 2` directly and proves the needed facts from
  Mathlib alone. This is a self-contained PROVIDER for the demarcation results,
  not the forcing derivation; the forcing derivation lives in the parent library.

  No project-local axioms. No sorry.
-/

import Mathlib

namespace ActualMathematics
namespace Constants

/-- The golden ratio. In the parent library this is forced; here it is given in
closed form so the analysis layer is self-contained. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

theorem phi_pos : 0 < phi := by
  unfold phi
  have := Real.sqrt_nonneg 5
  linarith

theorem phi_ne_zero : phi ≠ 0 := ne_of_gt phi_pos

theorem one_lt_phi : 1 < phi := by
  unfold phi
  have h5 : (1 : ℝ) < Real.sqrt 5 := by
    have : Real.sqrt 1 < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    simpa using this
  linarith

/-- The defining quadratic identity: `phi^2 = phi + 1`. -/
theorem phi_sq : phi ^ 2 = phi + 1 := by
  have h : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold phi
  field_simp
  nlinarith [h]

end Constants
end ActualMathematics

/-
  PrimitiveRecognitionCalculus/PRCCostOnField.lean

  Items 1 + 3 of the δ frontier, unified: the cost function and every physics
  constant share ONE countable field.

  Two strands had been proved separately:

  * `PRCExpLogField`: a single countable subfield `T ⊂ ℝ`, closed under field
    operations and `exp`/`log`, containing π, φ, e, and α⁻¹. The CONSTANTS live there.
  * `PRCChainBridge`: the RS chain's cost entry is the calibrated δ cost
    `Cost.Jcost`. The COST FORM is fixed.

  What was missing is the weld between them: that the canonical cost function itself
  maps the countable field into the countable field, so the cost SIDE and the
  constant SIDE are not two different carriers but one. This module supplies it.

  `Cost.Jcost x = (x + x⁻¹)/2 − 1` is a field expression, so on any subfield it is
  closed:

  * `jcost_mem_T`: `x ∈ T → Cost.Jcost x ∈ T`.
  * `jcost_iterate_mem_T`: the entire forward orbit of a `T`-point under repeated
    cost evaluation stays in `T`. The recognition COST DYNAMICS never leave the
    countable field.
  * `cost_and_constants_share_one_countable_field`: ONE countable field `T`, strictly
    below the continuum, that is closed under field operations, `exp`, `log`, AND the
    canonical cost `Jcost`, and already contains π, φ, e, and α⁻¹.

  This is the end-to-end form of Item 3 ("the RS chain running on the countable field
  fed by the δ cost"): the cost function, the operations the constants are built
  from, and the constants themselves all live on a single countable carrier. The
  continuum is required nowhere in the loop, only (at most) as the ambient where the
  standard `exp`/`log` are written down.

  No project-local axioms. No sorry.
-/

import ActualMathematics.Cost
import ActualMathematics.PRCExpLogField

namespace ActualMathematics
namespace CostOnField

open ExpLogField

/-- The canonical cost `Cost.Jcost x = (x + x⁻¹)/2 − 1` maps the countable field `T`
into itself: it is a field expression, and `T` is a subfield (closed under `+`, `⁻¹`,
`/`, `−`, and containing `1` and `2`). No positivity or nonzero hypothesis is needed,
because `Subfield` inversion is total (`0⁻¹ = 0`). -/
theorem jcost_mem_T {x : ℝ} (hx : x ∈ T) : Cost.Jcost x ∈ T := by
  have h2 : (2 : ℝ) ∈ T := by exact_mod_cast natCast_mem T 2
  unfold Cost.Jcost
  exact sub_mem (div_mem (add_mem hx (inv_mem hx)) h2) (one_mem _)

/-- **The cost dynamics stay countable.** The entire forward orbit of any
`T`-element under repeated application of the cost function remains in `T`. Iterating
recognition cost never escapes the countable field. -/
theorem jcost_iterate_mem_T {x : ℝ} (hx : x ∈ T) (n : ℕ) :
    (Cost.Jcost^[n] x) ∈ T := by
  induction n with
  | zero => simpa using hx
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact jcost_mem_T ih

/-- The cost of every named constant is itself a `T`-element. -/
theorem jcost_pi_mem_T : Cost.Jcost Real.pi ∈ T := jcost_mem_T pi_mem_T
theorem jcost_phi_mem_T : Cost.Jcost Real.goldenRatio ∈ T := jcost_mem_T phi_mem_T
theorem jcost_alphaInv_mem_T : Cost.Jcost MinimalField.alphaInv ∈ T :=
  jcost_mem_T alphaInv_mem_T

/-- **The unified headline (Items 1 + 3).** There is ONE countable subfield `T` of ℝ,
strictly below the continuum, that simultaneously
  * is closed under field operations, `exp`, and `log`;
  * is closed under the canonical recognition cost `Cost.Jcost`;
  * contains the seeds π and φ and the derived constants `e` and `α⁻¹`.
The cost function, the operations the constants are built from, and the constants
themselves therefore share a single countable carrier. "A single primitive for
physics runs on the countable field fed by the δ cost" is literally true: nowhere in
the cost-and-constants loop is the uncountable continuum required. -/
theorem cost_and_constants_share_one_countable_field :
    ∃ K : Subfield ℝ,
      (K : Set ℝ).Countable
        ∧ (∀ x ∈ K, Real.exp x ∈ K)
        ∧ (∀ x ∈ K, Real.log x ∈ K)
        ∧ (∀ x ∈ K, Cost.Jcost x ∈ K)
        ∧ Real.pi ∈ K
        ∧ Real.goldenRatio ∈ K
        ∧ Real.exp 1 ∈ K
        ∧ MinimalField.alphaInv ∈ K
        ∧ (K : Set ℝ) ≠ Set.univ :=
  ⟨T, T_countable,
    fun _ hx => T_exp_closed hx,
    fun _ hx => T_log_closed hx,
    fun _ hx => jcost_mem_T hx,
    pi_mem_T, phi_mem_T, e_mem_T, alphaInv_mem_T, T_proper⟩

end CostOnField
end ActualMathematics

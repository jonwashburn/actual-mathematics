/-
  ActualMathematics/Physicality/RSNilCapacityAttack.lean

  Attack on the OPEN capacity clause proposed to force generator 2.

  The surviving residual after the generator-gauge no-go was
  `NilCapacityClauseTarget`: RecognitionSurface g → ¬ ExceedsFloorCapacity g.
  That only says surface charts refuse gains strictly above floor card 2,
  i.e. at most g ≤ 2. It does not force the mixed-type identification
  `g = |DerivedTwo|`.

  CLAIM: CLOSED negative FOR "NilCapacityClauseTarget forces g = 2".
  CONSTRAINT: a capacity ceiling alone is the wrong shape; exact floor
    saturation (`ExactFloorCapacity` / `CardinalCoordinateIdentification`)
    remains the residual that forces 2.
  SURVIVOR: `ExactFloorCapacityClause` as the strengthened OPEN target.
  DECOYS: base 3 kills the global NIL target; base 3/2 kills
    ceiling-to-binary-gain inference.

  does NOT license: that δ/J already forces g = 2; that ExactFloorCapacity
  is derived from current NIL or RecognitionSurface.

  No project-local axioms. No sorry.
-/

import ActualMathematics.Physicality.RSGainCalibration

namespace ActualMathematics
namespace Physicality
namespace RSNilCapacityAttack

open RSGainCalibration
open RSDeltaBaseCountermodel
open DeltaKernel
open DeltaKernel.Bootstrap

/-! ## What the proposed NIL capacity clause actually says -/

theorem nil_target_only_ceiling_at_surface
    (h : NilCapacityClauseTarget) {g : ℝ}
    (S : RecognitionSurface g) :
    ¬ ExceedsFloorCapacity g :=
  h g S

theorem exceeds_floor_iff_gt_two (g : ℝ) :
    ExceedsFloorCapacity g ↔ (2 : ℝ) < g := by
  unfold ExceedsFloorCapacity
  simp [derivedTwo_card]

theorem nil_target_only_g_le_two
    (h : NilCapacityClauseTarget) {g : ℝ}
    (S : RecognitionSurface g) :
    g ≤ 2 := by
  have hceil := nil_target_only_ceiling_at_surface h S
  have : ¬ (2 : ℝ) < g := by
    intro hgt
    exact hceil ((exceeds_floor_iff_gt_two g).mpr hgt)
  exact not_lt.mp this

/-! ## Decoy: base 3/2 obeys the ceiling and still fails binary gain -/

theorem base_three_halves_capacity_ceiling_decoy :
    RecognitionSurface (3 / 2 : ℝ) ∧
      ¬ ExceedsFloorCapacity (3 / 2 : ℝ) ∧
      ¬ RSBinaryGainBridge (3 / 2 : ℝ) := by
  refine ⟨recognitionSurface_of_one_lt (by norm_num), ?_,
    baseThreeHalves_fails_binary_gain_bridge⟩
  unfold ExceedsFloorCapacity
  simp [derivedTwo_card]
  norm_num

/-- Local kill: imposing the capacity ceiling on surface models still does
not force the binary-gain / saturation residual. -/
theorem capacity_ceiling_does_not_force_binary_gain :
    ¬ (∀ g : ℝ,
        RecognitionSurface g →
        ¬ ExceedsFloorCapacity g →
        RSBinaryGainBridge g) := by
  intro h
  have decoy := base_three_halves_capacity_ceiling_decoy
  exact decoy.2.2 (h (3 / 2) decoy.1 decoy.2.1)

/-- Same kill in generator-two form. -/
theorem capacity_ceiling_does_not_force_two :
    ¬ (∀ g : ℝ,
        RecognitionSurface g →
        ¬ ExceedsFloorCapacity g →
        g = 2) := by
  intro h
  have decoy := base_three_halves_capacity_ceiling_decoy
  have h2 := h (3 / 2) decoy.1 decoy.2.1
  norm_num at h2

/-! ## Exact residual that does force 2 -/

/-- Exact floor capacity: multiplicative gain equals forced outcome card.
This is the mixed-type residual, stronger than a one-sided ceiling. -/
def ExactFloorCapacity (g : ℝ) : Prop :=
  g = (Fintype.card DerivedTwo : ℝ)

theorem exact_floor_iff_binary_gain (g : ℝ) :
    ExactFloorCapacity g ↔ RSBinaryGainBridge g := by
  unfold ExactFloorCapacity RSBinaryGainBridge
  simp [derivedTwo_card]

/-- Exact floor capacity forces generator 2. -/
theorem exact_floor_eq_two {g : ℝ} (h : ExactFloorCapacity g) : g = 2 := by
  simpa [ExactFloorCapacity, derivedTwo_card] using h

/-- Strengthened OPEN target: every surface chart saturates exactly to floor
capacity. This, not the one-sided ceiling, is the residual that forces 2. -/
def ExactFloorCapacityClause : Prop :=
  ∀ g : ℝ, RecognitionSurface g → ExactFloorCapacity g

theorem exact_floor_clause_forces_two
    (h : ExactFloorCapacityClause) {g : ℝ}
    (S : RecognitionSurface g) :
    g = 2 :=
  exact_floor_eq_two (h g S)

/-- The strengthened clause is currently unforced: base 3/2 is a surface
model that fails exact floor capacity. -/
theorem exact_floor_clause_not_forced_by_recognition_surface :
    ¬ ExactFloorCapacityClause := by
  intro h
  have S := recognitionSurface_of_one_lt (g := (3 / 2 : ℝ)) (by norm_num)
  have hex : ExactFloorCapacity (3 / 2 : ℝ) := h (3 / 2) S
  have h2 : (3 / 2 : ℝ) = 2 := exact_floor_eq_two hex
  norm_num at h2

/-- Headline: the proposed NIL capacity ceiling is the wrong shape for forcing
generator 2. Exact floor saturation remains the residual. -/
theorem nil_capacity_attack_headline :
    (¬ NilCapacityClauseTarget) ∧
      (¬ (∀ g : ℝ, RecognitionSurface g → ¬ ExceedsFloorCapacity g →
          RSBinaryGainBridge g)) ∧
      (∀ g : ℝ, ExactFloorCapacity g ↔ RSBinaryGainBridge g) ∧
      (∀ g : ℝ, ExactFloorCapacity g → g = 2) ∧
      (¬ ExactFloorCapacityClause) :=
  ⟨nil_capacity_clause_not_forced_by_recognition_surface,
   capacity_ceiling_does_not_force_binary_gain,
   exact_floor_iff_binary_gain,
   fun _ => exact_floor_eq_two,
   exact_floor_clause_not_forced_by_recognition_surface⟩

#print axioms base_three_halves_capacity_ceiling_decoy
#print axioms capacity_ceiling_does_not_force_binary_gain
#print axioms exact_floor_iff_binary_gain
#print axioms exact_floor_clause_not_forced_by_recognition_surface
#print axioms nil_capacity_attack_headline

end RSNilCapacityAttack
end Physicality
end ActualMathematics

/-
  ActualMathematics/Physicality/RSGainCalibration.lean

  Capacity saturation and its independence from the current recognition surface.

  Two "2"s live in different categories:
  * Count-side 2: `Side` / `DerivedTwo` have cardinality 2 (THEOREM from δ).
  * Magnitude-side g: multiplicative recognition step on ℝ₊ (free for all g > 1
    under Peano + J-zero + δ-transport).

  Attempted derivation of capacity saturation (`gain = |DerivedTwo|`) from the
  currently formalized recognition principles fails. Lean now proves the
  independence: floor card, OneAct cost-unit calibration, and generator-neutral
  process laws can all hold at base 3, which is unsaturated.

  CLAIM: CLOSED negative FOR deriving capacity saturation from the current
    recognition surface (neutral process + forced floor card + OneAct unit).
  CONSTRAINT extracted: a mixed-type cardinal↔coordinate identification law
    (`CardinalCoordinateIdentification`) is required; it is not a δ/J theorem
    and not an OneAct theorem.
  SURVIVOR: `GainInstrument` / `CardinalCoordinateIdentification` as the named
    residual of the same species as `OneActInstrument` for the cost unit.
  OPEN (expected closure): strengthen no-information-loss with an explicit
    capacity clause that rejects charts whose one-step gain exceeds floor
    capacity; until that predicate exists in Lean, saturation stays residual.

  Under the residual, `gain = 2` is THEOREM. Without it, the generator-gauge
  no-go stands.

  No project-local axioms. No sorry.
-/

import ActualMathematics.Physicality.RSDeltaBaseCountermodel
import ActualMathematics.PhysicalOneActCalibration
import ActualMathematics.Basic

namespace ActualMathematics
namespace Physicality
namespace RSGainCalibration

open DeltaKernel
open DeltaKernel.Bootstrap
open RSDeltaBaseCountermodel
open PhysicalOneActCalibration

noncomputable section

/-! ## Forced count side of the dial -/

/-- The primitive δ side type is exactly Boolean. -/
def sideEquivBool : Side ≃ Bool where
  toFun
    | .left => false
    | .right => true
  invFun
    | false => .left
    | true => .right
  left_inv := by
    intro s
    cases s <;> rfl
  right_inv := by
    intro b
    cases b <;> rfl

noncomputable instance : Fintype Side :=
  Fintype.ofEquiv Bool sideEquivBool.symm

/-- One primitive distinction has exactly two sides. THEOREM from δ syntax. -/
@[simp] theorem side_card : Fintype.card Side = 2 := by
  rw [Fintype.card_congr sideEquivBool]
  decide

/-- The side floor and the derived-two floor have the same cardinality. -/
theorem side_card_eq_derivedTwo_card :
    Fintype.card Side = Fintype.card DerivedTwo := by
  simp

/-! ## Current recognition surface (does not force saturation) -/

/-- The currently formalized recognition surface relevant to the dial:
generator-neutral process laws, forced floor cardinalities, and OneAct
cost-unit forcing. None of these fields mentions a cardinal↔real identification. -/
structure RecognitionSurface (g : ℝ) : Prop where
  neutral : GeneratorNeutralModel g
  floor_derived : Fintype.card DerivedTwo = 2
  floor_side : Fintype.card Side = 2
  one_act_forces_unit : ∀ I : OneActInstrument, I.unit = 1

theorem recognitionSurface_of_one_lt {g : ℝ} (hg : 1 < g) :
    RecognitionSurface g where
  neutral := generatorNeutralModel_of_one_lt hg
  floor_derived := derivedTwo_card
  floor_side := side_card
  one_act_forces_unit := instrument_forces_canonical_unit

/-- Base 3 satisfies the entire current recognition surface and fails
capacity saturation. This is the discriminating decoy. -/
theorem unsaturated_recognition_surface :
    RecognitionSurface 3 ∧ ¬ RSBinaryGainBridge 3 :=
  ⟨recognitionSurface_of_one_lt (by norm_num), base3_fails_binary_gain_bridge⟩

/-- φ also saturates the surface without saturating capacity. -/
theorem unsaturated_phi_recognition_surface :
    RecognitionSurface Real.goldenRatio ∧
      ¬ RSBinaryGainBridge Real.goldenRatio :=
  ⟨recognitionSurface_of_one_lt Real.one_lt_goldenRatio,
   basePhi_fails_binary_gain_bridge⟩

/-- **No-go.** Capacity saturation is not a theorem of the current recognition
surface. Floor card and OneAct are present in the antecedent and still fail to
force the binary-gain bridge. -/
theorem saturation_not_forced_by_recognition_surface :
    ¬ (∀ g : ℝ, RecognitionSurface g → RSBinaryGainBridge g) := by
  intro h
  exact (unsaturated_recognition_surface.2) (h 3 unsaturated_recognition_surface.1)

/-- Same no-go in generator-two form: the surface does not force `g = 2`. -/
theorem generator_two_not_forced_by_recognition_surface :
    ¬ (∀ g : ℝ, RecognitionSurface g → g = 2) := by
  intro h
  have h3 := h 3 unsaturated_recognition_surface.1
  norm_num at h3

/-! ## Extracted mixed-type residual -/

/-- The irreducible mixed-type law extracted by the no-go: real one-step
multiplicative gain equals the forced outcome cardinality of one distinction.
This is exactly `RSBinaryGainBridge`, renamed to record its logical role. -/
abbrev CardinalCoordinateIdentification (g : ℝ) : Prop :=
  RSBinaryGainBridge g

theorem cardinal_coordinate_iff_binary_gain (g : ℝ) :
    CardinalCoordinateIdentification g ↔ RSBinaryGainBridge g :=
  Iff.rfl

/-- A chart whose gain strictly exceeds forced floor capacity. Such charts are
the natural targets of a future no-information-loss capacity clause. -/
def ExceedsFloorCapacity (g : ℝ) : Prop :=
  (Fintype.card DerivedTwo : ℝ) < g

theorem base3_exceeds_floor_capacity :
    ExceedsFloorCapacity 3 := by
  unfold ExceedsFloorCapacity
  simp [derivedTwo_card]
  norm_num

/-- OPEN target (not yet forced): every recognition chart compatible with a
completed no-information-loss capacity clause refuses gains that exceed floor
capacity. Formalizing and forcing that clause would discharge saturation.
Until then, this is a named goal, not a theorem. -/
def NilCapacityClauseTarget : Prop :=
  ∀ g : ℝ, RecognitionSurface g → ¬ ExceedsFloorCapacity g

/-- The current surface does not imply the NIL capacity target: base 3 is a
surface model that exceeds floor capacity. -/
theorem nil_capacity_clause_not_forced_by_recognition_surface :
    ¬ NilCapacityClauseTarget := by
  intro h
  exact h 3 unsaturated_recognition_surface.1 base3_exceeds_floor_capacity

/-! ## Capacity-saturating gain instrument (residual twin of OneAct) -/

/-- A capacity-saturating gain instrument: a candidate multiplicative step,
a natural readout of free one-act capacity, a proof that the readout equals
the forced outcome count of one primitive distinction, and saturation of the
real step to that count.

This is the generator-side twin of `PhysicalOneActCalibration.OneActInstrument`.
It does not construct laboratory hardware. It isolates the exact logical role
of the mixed-type residual. -/
structure GainInstrument where
  gain : ℝ
  one_lt : 1 < gain
  readout : ℕ
  reads_capacity : readout = Fintype.card DerivedTwo
  saturating : gain = readout

/-- Side-based capacity reading is equivalent: the instrument may cite either
forced two-outcome floor. -/
theorem GainInstrument.reads_side_capacity (I : GainInstrument) :
    I.readout = Fintype.card Side := by
  rw [I.reads_capacity, side_card_eq_derivedTwo_card]

/-- Saturation is exactly the named cardinal↔coordinate identification. -/
theorem GainInstrument.toBinaryGainBridge (I : GainInstrument) :
    RSBinaryGainBridge I.gain := by
  unfold RSBinaryGainBridge
  refine I.saturating.trans ?_
  simp [I.reads_capacity]

theorem GainInstrument.toCardinalCoordinate (I : GainInstrument) :
    CardinalCoordinateIdentification I.gain :=
  I.toBinaryGainBridge

/-- Any capacity-saturating gain instrument forces generator 2. -/
theorem gainInstrument_forces_two (I : GainInstrument) :
    I.gain = 2 :=
  generator_two_of_binary_gain_bridge I.toBinaryGainBridge

/-- Canonical consistency witness at gain 2. Not a lab construction. -/
def canonicalGainInstrument : GainInstrument where
  gain := 2
  one_lt := by norm_num
  readout := Fintype.card DerivedTwo
  reads_capacity := rfl
  saturating := by
    simp [derivedTwo_card]

/-- Under saturation, the instrument's gain is a generator-neutral model base
that is forced to equal 2. -/
theorem canonical_gain_is_neutral_two :
    GeneratorNeutralModel canonicalGainInstrument.gain ∧
      canonicalGainInstrument.gain = 2 := by
  refine ⟨generatorNeutralModel_of_one_lt canonicalGainInstrument.one_lt, ?_⟩
  exact gainInstrument_forces_two canonicalGainInstrument

/-- Building a gain instrument from the binary-gain bridge. -/
def GainInstrument.ofBinaryGainBridge {g : ℝ} (hg : 1 < g)
    (h : RSBinaryGainBridge g) : GainInstrument where
  gain := g
  one_lt := hg
  readout := Fintype.card DerivedTwo
  reads_capacity := rfl
  saturating := by
    unfold RSBinaryGainBridge at h
    exact_mod_cast h

theorem binary_gain_bridge_iff_gainInstrument (g : ℝ) (hg : 1 < g) :
    RSBinaryGainBridge g ↔ ∃ I : GainInstrument, I.gain = g := by
  constructor
  · intro h
    exact ⟨GainInstrument.ofBinaryGainBridge hg h, rfl⟩
  · intro ⟨I, hI⟩
    subst hI
    exact I.toBinaryGainBridge

/-- **Headline.** Attempted derivation of saturation from the current recognition
surface fails (no-go). The extracted residual is cardinal↔coordinate
identification, equivalent to `GainInstrument` saturation. Under that residual,
gain 2 is forced; without it, unsaturated surface models survive. -/
theorem physical_gain_calibration_headline :
    (¬ ∀ g : ℝ, RecognitionSurface g → RSBinaryGainBridge g) ∧
      (∀ I : GainInstrument, I.gain = 2) ∧
      (∃ I : GainInstrument, I.gain = 2) ∧
      (∀ I : GainInstrument, CardinalCoordinateIdentification I.gain) ∧
      (¬ NilCapacityClauseTarget) :=
  ⟨saturation_not_forced_by_recognition_surface,
   gainInstrument_forces_two,
   ⟨canonicalGainInstrument, gainInstrument_forces_two canonicalGainInstrument⟩,
   fun I => I.toCardinalCoordinate,
   nil_capacity_clause_not_forced_by_recognition_surface⟩

/-! ## Axiom audits -/

#print axioms side_card
#print axioms unsaturated_recognition_surface
#print axioms saturation_not_forced_by_recognition_surface
#print axioms generator_two_not_forced_by_recognition_surface
#print axioms nil_capacity_clause_not_forced_by_recognition_surface
#print axioms gainInstrument_forces_two
#print axioms canonicalGainInstrument
#print axioms physical_gain_calibration_headline

end
end RSGainCalibration
end Physicality
end ActualMathematics

/-
  ActualMathematics/Physicality/RSGainCalibration.lean

  Capacity-saturation calibration for the multiplicative recognition dial.

  The generator-gauge no-go (`RSDeltaBaseCountermodel`) proves that Peano
  generation, forced J, J-zero separation, and δ-transport do not force the
  multiplicative step `g = 2`. Separately, δ forces a two-outcome absolute
  floor (`Side`, `DerivedTwo`). Those live in different categories: a cardinal
  and a real process coordinate.

  This module does not pretend the categories are already identified. It names
  the residual physical datum in the same species as `OneActInstrument`:
  a gain instrument that reads the free-outcome capacity of one primitive
  distinction and saturates its multiplicative step to that capacity.

  CLAIM: CLOSED positive FOR `gain = 2` UNDER capacity saturation.
  DOMAIN: multiplicative recognition charts with `gain > 1`.
  PREMISES: `derivedTwo_card` / `side_card`; the named saturation interface.
  REACH: any saturating gain instrument forces generator 2; the canonical
    witness exists; saturation is equivalent to `RSBinaryGainBridge`.
  does NOT license: discharge of saturation from δ/J alone (the no-go stands);
    uniqueness of saturation among all conceivable physical bridges.

  No project-local axioms. No sorry.
-/

import ActualMathematics.Physicality.RSDeltaBaseCountermodel
import ActualMathematics.Basic

namespace ActualMathematics
namespace Physicality
namespace RSGainCalibration

open DeltaKernel
open DeltaKernel.Bootstrap
open RSDeltaBaseCountermodel

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

/-! ## Capacity-saturating gain instrument -/

/-- A capacity-saturating gain instrument: a candidate multiplicative step,
a natural readout of free one-act capacity, a proof that the readout equals
the forced outcome count of one primitive distinction, and saturation of the
real step to that count.

This is the generator-side twin of `PhysicalOneActCalibration.OneActInstrument`.
It does not construct laboratory hardware. It isolates the exact logical role
of capacity saturation. -/
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

/-- Saturation is exactly the named binary-gain bridge. -/
theorem GainInstrument.toBinaryGainBridge (I : GainInstrument) :
    RSBinaryGainBridge I.gain := by
  unfold RSBinaryGainBridge
  refine I.saturating.trans ?_
  simp [I.reads_capacity]

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

/-- **Physical gain-calibration headline.** Capacity saturation is the residual
datum that forces the multiplicative dial to 2. It is equivalent to the binary
gain bridge, admits a canonical witness, and does not discharge the
generator-gauge no-go on unsaturated charts. -/
theorem physical_gain_calibration_headline :
    (∀ I : GainInstrument, I.gain = 2) ∧
      (∃ I : GainInstrument, I.gain = 2) ∧
      (∀ I : GainInstrument, RSBinaryGainBridge I.gain) ∧
      (¬ ∀ g : ℝ, GeneratorNeutralModel g → g = 2) :=
  ⟨gainInstrument_forces_two,
   ⟨canonicalGainInstrument, gainInstrument_forces_two canonicalGainInstrument⟩,
   fun I => I.toBinaryGainBridge,
   generator_two_not_derivable⟩

/-! ## Axiom audits -/

#print axioms side_card
#print axioms side_card_eq_derivedTwo_card
#print axioms gainInstrument_forces_two
#print axioms canonicalGainInstrument
#print axioms physical_gain_calibration_headline

end
end RSGainCalibration
end Physicality
end ActualMathematics

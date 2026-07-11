import ActualMathematics.CalibrationOmniscience
import ActualMathematics.Omniscience
import ActualMathematics.Strength
import ActualMathematics.DeltaKernel.BootstrapDemarcation

/-!
# Bootstrap F3: continuum tax (omniscience prices past ℚ)

Extensions past ℚ are named purchases. Exact-zero testing costs WLPO;
trichotomy costs LPO; order dichotomy costs LLPO. Continuum completeness
is not a δ failure; it is a priced classical / omniscience extension.
-/

namespace ActualMathematics.DeltaKernel.Bootstrap

open ActualMathematics
open ActualMathematics.Calibration

/-- F3 package: wire the existing calibration certificate into the bootstrap. -/
structure BootstrapContinuumTaxSpec : Prop where
  /-- Exact-zero on constructive reals prices WLPO. -/
  exact_zero_wlpo :
    (∀ x : CReal, EqZero x ∨ ¬ EqZero x) → Omniscience.WLPO
  /-- Trichotomy prices LPO. -/
  trichotomy_lpo :
    (∀ x : CReal, Pos x ∨ EqZero x ∨ Neg x) → Omniscience.LPO
  /-- Dichotomy prices LLPO. -/
  dichotomy_llpo :
    (∀ x : CReal, NonNeg x ∨ NonPos x) → Omniscience.LLPO
  /-- Hierarchy: LPO ⇒ WLPO. -/
  hierarchy_lpo_wlpo : Omniscience.LPO → Omniscience.WLPO
  /-- Hierarchy: LPO ⇒ LLPO. -/
  hierarchy_lpo_llpo : Omniscience.LPO → Omniscience.LLPO
  /-- Exact location: LPO ⇔ WLPO ∧ Markov. -/
  location_lpo :
    Omniscience.WLPO → Omniscience.MarkovPrinciple → Omniscience.LPO
  /-- Continuum completeness is tagged as a purchase, not δ-only. -/
  continuum_is_purchase_tag :
      Tagged StrengthTag.classicalExtension (¬ Forced.DeltaForced ℝ)

theorem bootstrap_continuum_tax : BootstrapContinuumTaxSpec where
  exact_zero_wlpo := calib_exact_zero_imp_wlpo
  trichotomy_lpo := calib_trichotomy_imp_lpo
  dichotomy_llpo := calib_dichotomy_imp_llpo
  hierarchy_lpo_wlpo := Omniscience.lpo_imp_wlpo
  hierarchy_lpo_llpo := Omniscience.lpo_imp_llpo
  location_lpo := Omniscience.wlpo_and_markov_imp_lpo
  continuum_is_purchase_tag := bootstrap_continuum_purchase

/-- Transparent packaging of the choice-free calibration certificate. -/
theorem bootstrap_calibration_cert : CalibrationCert :=
  calibrationCert_holds

#print axioms bootstrap_continuum_tax
#print axioms bootstrap_calibration_cert

end ActualMathematics.DeltaKernel.Bootstrap

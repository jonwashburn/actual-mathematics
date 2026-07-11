import ActualMathematics.DeltaKernel.BootstrapCapstone
import ActualMathematics.DeltaKernel.BootstrapDemarcation
import ActualMathematics.DeltaKernel.BootstrapTowerExport
import ActualMathematics.DeltaKernel.BootstrapContinuumTax
import ActualMathematics.DeltaKernel.BootstrapChoiceFreeHost
import ActualMathematics.DeltaKernel.BootstrapPublicSpineBridge

/-!
# Bootstrap F-ladder capstone: forcing / physically-real verdict

The B-ladder (`BootstrapCapstone`) closed the mechanism: licensed syntax,
initiality, arithmetic export, foundation, host invariance. This capstone
closes the F-ladder: what the mechanism FORCES, and the exact price of
everything beyond.

CLAIM: CLOSED positive for the δ bootstrap forcing verdict.
DOMAIN: ActualMathematics Forced / Representability / Calibration predicates,
        plus the PublicSpine bridge claim block (textual receipt:
        reality repo `δ/check_delta_publicspine_bridge.sh`).
PREMISES:
  A1. `DeltaForced X := Nonempty (X ↪ ℕ)`; `PhysicallyReal := DeltaForced`
      (definitional demarcation thesis, F1).
  A2. ℕδ/ℤδ/ℚδ are the orbit carriers of `IntegerRational.lean` (F2).
  A3. Omniscience calibrations are the constructive-reverse-mathematics
      readings of WLPO/LPO/LLPO (F3).
  A4. `List Unit` host receipts are the `Rigidity` Peano-model certificates
      (F4).
  A5. ¬`DeltaForced ℝ` uses classical uncountability of ℝ; every conjunct
      touching ℝ is tagged `classicalExtension`.
REACH: max licensed:
  * choice-free core ({propext, Quot.sound}): the δ-native tower
    ℕδ/ℤδ/ℚδ is forced with exact free-vs-constructed provenance;
    the omniscience calibration certificate holds; an independent
    choice-free second host realizes the same validity;
  * classical demarcation layer (+Classical.choice, entering only through
    ℝ facts): ℕ,ℤ,ℚ physically real, ℝ a named purchase, continuum
    extensions priced at WLPO/LPO/LLPO, and the same claim stated by the
    IndisputableMonolith PublicSpine.
does NOT license:
  * ZFC / CIC reconstruction;
  * the claim that every Lean type is physically real
    (`not_all_types_physically_real` proves the exact negative);
  * the stronger claim that the countability cut alone rules out coded
    interpretations of formal set theories;
  * a choice-free proof of ¬`DeltaForced ℝ`;
  * absolute consistency of the host;
  * any physical claim beyond the demarcation predicate itself.
-/

namespace ActualMathematics.DeltaKernel.Bootstrap

open ActualMathematics
open ActualMathematics.Forced
open ActualMathematics.Calibration

/-- Choice-free forcing core: everything here prints {propext, Quot.sound}.
Each conjunct is separately proved in its own module; no field assumes the
conclusion it establishes. -/
def BootstrapForcingCore : Prop :=
  BootstrapTowerExportSpec ∧
  Tagged StrengthTag.deltaOnly
    (Forced.DeltaForced NatDelta ∧ Forced.DeltaForced IntDelta ∧
      Forced.DeltaForced RatDelta) ∧
  CalibrationCert ∧
  BootstrapChoiceFreeHostSpec

theorem bootstrap_forcing_core : BootstrapForcingCore :=
  ⟨bootstrap_tower_export,
   bootstrap_tower_export_deltaOnly,
   bootstrap_calibration_cert,
   bootstrap_choice_free_host⟩

/-- Classical demarcation layer: `Classical.choice` enters only through the
ℝ conjuncts (uncountability of the continuum), exactly as the
`classicalExtension` tags state. -/
def BootstrapForcingDemarcation : Prop :=
  BootstrapDemarcationSpec ∧
  BootstrapContinuumTaxSpec ∧
  BootstrapPublicSpineBridgeSpec

theorem bootstrap_forcing_demarcation : BootstrapForcingDemarcation :=
  ⟨bootstrap_demarcation_spec,
   bootstrap_continuum_tax,
   bootstrap_public_spine_bridge⟩

/-- The δ Bootstrap Forcing Theorem: mechanism (B-ladder) + forced tower with
provenance + omniscience prices + independent host + demarcation + bridge. -/
def DeltaBootstrapForcing : Prop :=
  BootstrapSpec ∧ BootstrapForcingCore ∧ BootstrapForcingDemarcation

theorem delta_bootstrap_forcing : DeltaBootstrapForcing :=
  ⟨delta_bootstrap, bootstrap_forcing_core, bootstrap_forcing_demarcation⟩

#print axioms bootstrap_forcing_core
#print axioms bootstrap_forcing_demarcation
#print axioms delta_bootstrap_forcing

end ActualMathematics.DeltaKernel.Bootstrap

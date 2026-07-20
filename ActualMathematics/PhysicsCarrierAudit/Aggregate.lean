/-
  PhysicsCarrierAudit/Aggregate.lean

  Extraction-side carrier audit aggregate: Core gate + classification-level
  continuum consumers + negative controls + SelfContainedAudit restriction.
  Named `ExtractionCarrierAudit` so it is not confused with the parent
  `FullPhysicsCarrierAudit` (which packages the Skeleton physics-value registry).
  Weakest-link tag is classicalExtension.
-/

import ActualMathematics.PhysicsCarrierAudit.Core
import ActualMathematics.PhysicsCarrierAudit.Manifest
import ActualMathematics.PhysicsCarrierAudit.Migration

namespace ActualMathematics
namespace PhysicsCarrierAudit

open CountableCarrierDemarcation
open ActualMathematics.DeltaKernel.Bootstrap

/-! ## Named statement-level continuum consumers (semantic, non-duplicate) -/

/-- The eight semantic Skeleton endpoints whose statements consume continuum
structure (`statementConsumes` / `continuumConsuming` in the frozen manifest).
Classification-level register; does not import Skeleton. -/
inductive NamedContinuumConsumer where
  | t9_forced_measure_mean
  | t9_forced_measure_normalized
  | public_continuum_purchase
  | public_floor_demarcation
  | public_cost_selection
  | cost_is_unique
  | rcl_is_forced
  | einstein_from_action
  deriving DecidableEq, Repr

def NamedContinuumConsumer.continuumRole : NamedContinuumConsumer → ContinuumRole
  | _ => .statementConsumes

def NamedContinuumConsumer.verdict : NamedContinuumConsumer → AuditVerdict
  | _ => .continuumConsuming

def NamedContinuumConsumer.guidepostName : NamedContinuumConsumer → String
  | .t9_forced_measure_mean => "guidepost_T9_forced_measure_mean"
  | .t9_forced_measure_normalized => "guidepost_T9_forced_measure_normalized"
  | .public_continuum_purchase => "guidepost_public_continuum_purchase"
  | .public_floor_demarcation => "guidepost_public_floor_demarcation"
  | .public_cost_selection => "guidepost_public_cost_selection"
  | .cost_is_unique => "guidepost_cost_is_unique"
  | .rcl_is_forced => "guidepost_rcl_is_forced"
  | .einstein_from_action => "guidepost_einstein_from_action"

theorem named_continuum_consumer_role
    (c : NamedContinuumConsumer) :
    NamedContinuumConsumer.continuumRole c = ContinuumRole.statementConsumes :=
  rfl

theorem named_continuum_consumer_verdict
    (c : NamedContinuumConsumer) :
    NamedContinuumConsumer.verdict c = AuditVerdict.continuumConsuming :=
  rfl

/-- Cost-selection continuum role (definitional classification). -/
theorem neg_cost_selection_not_unconditional_carrier :
    publicCostSelectionContinuumRole = ContinuumRole.statementConsumes :=
  rfl

/-- Friedmann ξ decimal certificate is not an integral identification. -/
theorem xi_decimal_not_integral_id : ¬ XiIntegralIdentification :=
  fun h => h

/-- guidepost_conformal_horizon_xi is model-tier (decimal bounds), not theorem-tier
integral ID. -/
def conformalHorizonXiVerdict : AuditVerdict := .model

theorem guidepost_conformal_horizon_xi_is_model :
    conformalHorizonXiVerdict = AuditVerdict.model :=
  rfl

/-! ## Aggregate corollaries -/

/-- Classification-level: the full registry is not an all-PASS carrier audit. -/
theorem not_all_carrier_expressible :
    ∃ c : NamedContinuumConsumer,
      NamedContinuumConsumer.verdict c = AuditVerdict.continuumConsuming :=
  ⟨NamedContinuumConsumer.public_cost_selection, rfl⟩

theorem not_all_pass : ¬ (∀ _c : NamedContinuumConsumer,
    NamedContinuumConsumer.verdict _c = AuditVerdict.carrierExpressible) := by
  intro h
  have := h NamedContinuumConsumer.public_cost_selection
  simp [NamedContinuumConsumer.verdict] at this

/-- Every theorem-tier SelfContainedAudit scalar seed is carrierExpressible. -/
theorem every_theorem_finite_audit_scalar_seed_carrier_expressible :
    ∀ id : FiniteAuditSeedId,
      FiniteAuditSeedId.kind id = AuditKind.scalar →
      (PhysicsAuditId.row (.seed id)).honesty = HonestyTier.theorem ∧
        (PhysicsAuditId.row (.seed id)).expectedVerdict =
          AuditVerdict.carrierExpressible := by
  intro id hkind
  cases id with
  | hbarNative | coherenceEnergy | newtonG | einsteinKappa | darkEnergyTheta =>
      simp [PhysicsAuditId.row, FiniteAuditSeedId.kind]

/-- All negative-control receipts inhabit. -/
theorem negative_controls_hold :
    ∀ id : NegativeControlId, Nonempty (NegativeControlId.ReceiptType id) :=
  fun id => ⟨NegativeControlId.receipt id⟩

/-- Plan-mandated negatives specifically. -/
theorem neg_publicSpine_cost_selection_receipt :
    Nonempty (NegativeControlId.ReceiptType
      .publicSpineCostSelectionNotUnconditional) :=
  ⟨NegativeControlId.receipt .publicSpineCostSelectionNotUnconditional⟩

theorem neg_friedmann_xi_receipt :
    Nonempty (NegativeControlId.ReceiptType .friedmannXiDecimalNotIntegral) :=
  ⟨NegativeControlId.receipt .friedmannXiDecimalNotIntegral⟩

/-! ## Extraction aggregate (not the parent FullPhysicsCarrierAudit) -/

/-- Extraction-side bundle of what this library proves: Core gate, continuum
consumers that are not all carrier-expressible, negatives, SelfContainedAudit,
and the parent freeze cardinalities. Distinct from the parent
`FullPhysicsCarrierAudit`, which also packages Skeleton physics-value receipts. -/
structure ExtractionCarrierAudit : Prop where
  core : CorePhysicsCarrierAudit
  not_all_pass :
    ∃ c : NamedContinuumConsumer,
      NamedContinuumConsumer.verdict c = AuditVerdict.continuumConsuming
  negatives :
    ∀ id : NegativeControlId, Nonempty (NegativeControlId.ReceiptType id)
  self_contained_audit_restriction : SelfContainedAudit
  expected_raw : expectedRawCount = 136
  expected_semantic : expectedSemanticCount = 130

theorem extraction_carrier_audit_holds : ExtractionCarrierAudit where
  core := core_physics_carrier_audit_holds
  not_all_pass := not_all_carrier_expressible
  negatives := negative_controls_hold
  self_contained_audit_restriction := self_contained_audit_of_core_holds
  expected_raw := rfl
  expected_semantic := rfl

theorem extraction_carrier_audit_tagged :
    Tagged StrengthTag.classicalExtension ExtractionCarrierAudit where
  holds := extraction_carrier_audit_holds

end PhysicsCarrierAudit
end ActualMathematics

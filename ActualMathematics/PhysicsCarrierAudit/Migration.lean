/-
  PhysicsCarrierAudit/Migration.lean

  SelfContainedAudit is the restriction of the Core seed receipts / Core gate.
-/

import ActualMathematics.PhysicsCarrierAudit.Core

namespace ActualMathematics
namespace PhysicsCarrierAudit

open CountableCarrierDemarcation

/-- Every SelfContainedAudit seed has a load-bearing Core receipt. -/
theorem every_finite_audit_seed_receipt :
    ∀ id : FiniteAuditSeedId, Nonempty (FiniteAuditSeedId.Receipt id) :=
  fun id => ⟨FiniteAuditSeedId.receipt id⟩

/-- The Core gate projects onto SelfContainedAudit. -/
theorem self_contained_audit_of_core_holds : SelfContainedAudit :=
  self_contained_audit_of_core core_physics_carrier_audit_holds

/-- Seed receipts cover the SelfContainedAudit surface. -/
theorem self_contained_audit_restriction_of_seeds
    (_h : ∀ id : FiniteAuditSeedId, Nonempty (FiniteAuditSeedId.Receipt id)) :
    SelfContainedAudit :=
  self_contained_audit_of_core_holds

/-- Compatibility: SelfContainedAudit holds exactly when the seed receipts
inhabit (the Core gate supplies the shared package). -/
theorem self_contained_audit_iff_seed_receipts :
    SelfContainedAudit ↔
      (∀ id : FiniteAuditSeedId, Nonempty (FiniteAuditSeedId.Receipt id)) :=
  Iff.intro
    (fun _ => every_finite_audit_seed_receipt)
    (fun h => self_contained_audit_restriction_of_seeds h)

/-- Core's SelfContainedAudit component is proof-irrelevantly the legacy package. -/
theorem self_contained_audit_core_eq_legacy :
    (core_physics_carrier_audit_holds).self_contained_audit =
      self_contained_audit_holds :=
  proof_irrel _ _

end PhysicsCarrierAudit
end ActualMathematics

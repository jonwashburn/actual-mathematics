/-
  PhysicsCarrierAudit/Core.lean

  Typed scaffold for the physics-carrier audit vocabulary, extracted from
  IndisputableMonolith.Foundation.PrimitiveRecognitionCalculus.PhysicsCarrierAudit.

  This extraction keeps the tag vocabulary, evidence structures, negative
  controls, and closed-form seed receipts. Parent physics theorems
  (GapDerivation, MassLaw, EMAlphaCert, DarkEnergyPhiDilutionLaw band proofs,
  Skeleton registry) are replaced by SelfContainedAudit closed-form receipts
  from CountableCarrierDemarcation. The full parent physics-value audit lives in
  the parent PhysicsCarrierAudit modules.

  `ConditionalSlot` is vendored locally (parent:
  IndisputableMonolith.Gravity.ConditionalSlot).

  No project-local axioms. No sorry.
-/

import ActualMathematics.Constants
import ActualMathematics.CountableCarrierDemarcation
import ActualMathematics.DeltaForced
import ActualMathematics.DeltaKernel.BootstrapDemarcation
import ActualMathematics.PRCCompletenessIndependence
import ActualMathematics.Strength

namespace ActualMathematics
namespace PhysicsCarrierAudit

open CountableCarrierDemarcation
open ActualMathematics.Constants
open ActualMathematics.Forced
open ActualMathematics.CompletenessIndependence
open ActualMathematics.DeltaKernel.Bootstrap

/-! ## Local ConditionalSlot (vendored)

Parent: `IndisputableMonolith.Gravity.ConditionalSlot.ConditionalSlot`.
Tiny proof carrier so ScalarEvidence / NegativeEvidence stay typed. -/

/-- A named Prop together with a proof that it holds. -/
structure ConditionalSlot (P : Prop) where
  holds : P

/-! ## §1. Tag vocabulary -/

/-- The twelve Skeleton public physics chapters in the freeze. -/
inductive PhysicsChapter where
  | foundation
  | publicSpine
  | cost
  | constants
  | quantum
  | electromagnetism
  | standardModel
  | masses
  | gravity
  | cosmology
  | matter
  | holography
  deriving DecidableEq, Repr

/-- How a row is evidenced. -/
inductive AuditKind where
  | scalar
  | structural
  | openTarget
  | negativeControl
  deriving DecidableEq, Repr

/-- Soul-facing honesty (Skeleton docstring tier), independent of `StrengthTag`. -/
inductive HonestyTier where
  | theorem
  | forcedConditional
  | model
  | open
  | hypothesis
  deriving DecidableEq, Repr

/-- Statement-level continuum role (not proof technique). -/
inductive ContinuumRole where
  | noneInStatement
  | ambientDisplayOnly
  | statementConsumes
  deriving DecidableEq, Repr

/-- Dispositional verdict for one audited claim. -/
inductive AuditVerdict where
  | carrierExpressible
  | continuumConsuming
  | conditional
  | model
  | open
  | refuted
  deriving DecidableEq, Repr

/-! ## §2. Metadata row (computable; not a receipt) -/

structure DeclNames where
  guidepost : String
  source : String
  deriving DecidableEq, Repr

structure AuditRow where
  chapter : PhysicsChapter
  kind : AuditKind
  honesty : HonestyTier
  continuum : ContinuumRole
  expectedVerdict : AuditVerdict
  strength : StrengthTag
  names : DeclNames
  deriving Repr

/-! ## §3. Load-bearing evidence -/

structure ScalarEvidence (values : List ℝ) (P : Prop) where
  mem : ∀ x ∈ values, x ∈ carrier
  statement : ConditionalSlot P

structure StructuralEvidence (P : Prop) where
  statement : ConditionalSlot P

structure ConditionalEvidence (Assumptions Conclusion : Prop) where
  premises : ConditionalSlot Assumptions
  conclusion : ConditionalSlot Conclusion

structure OpenEvidence (P : Prop) where
  continuum : ContinuumRole
  names : DeclNames

structure NegativeEvidence (P : Prop) where
  statement : ConditionalSlot P

structure ProvenMeta where
  honesty : HonestyTier
  continuum : ContinuumRole
  strength : StrengthTag
  names : DeclNames
  deriving Repr

structure ScalarReceipt (values : List ℝ) (P : Prop) extends ProvenMeta where
  evidence : ScalarEvidence values P

structure StructuralReceipt (P : Prop) extends ProvenMeta where
  evidence : StructuralEvidence P

structure ConditionalReceipt (Assumptions Conclusion : Prop) extends ProvenMeta where
  evidence : ConditionalEvidence Assumptions Conclusion

structure OpenReceipt (P : Prop) where
  honesty : HonestyTier := .open
  continuum : ContinuumRole
  names : DeclNames

structure NegativeReceipt (P : Prop) where
  names : DeclNames
  strength : StrengthTag
  evidence : NegativeEvidence P

/-! ## §4. Negative-control classification helpers -/

/-- PublicSpine cost selection is a continuum-consuming package at the
statement level (quantifies over `F : ℝ → ℝ` with continuity), not an
unconditional carrier-membership closure. -/
def publicCostSelectionContinuumRole : ContinuumRole := .statementConsumes

/-- Unevaluated integral identification of Friedmann ξ is not established;
`xi_RS_bounds` is a decimal/model certificate only. -/
def XiIntegralIdentification : Prop := False

/-- ξ is not among the SelfContainedAudit seed statements. -/
def XiInFiniteAudit : Prop := False

/-! ## §5. Negative-control IDs -/

inductive NegativeControlId where
  | rationalMissesPhi
  | carrierProper
  | carrierNotOrderComplete
  | realNotDeltaForced
  | publicSpineCostSelectionNotUnconditional
  | friedmannXiDecimalNotIntegral
  deriving DecidableEq, Repr

def NegativeControlId.row : NegativeControlId → AuditRow
  | .rationalMissesPhi =>
    { chapter := .constants
      kind := .negativeControl
      honesty := .theorem
      continuum := .noneInStatement
      expectedVerdict := .carrierExpressible
      strength := .deltaOnly
      names := {
        guidepost := "PhysicsCarrierAudit.neg_rationalMissesPhi"
        source := "CountableCarrierDemarcation.rationalCandidate_lt_carrier" } }
  | .carrierProper =>
    { chapter := .foundation
      kind := .negativeControl
      honesty := .theorem
      continuum := .noneInStatement
      expectedVerdict := .carrierExpressible
      strength := .deltaOnly
      names := {
        guidepost := "PhysicsCarrierAudit.neg_carrierProper"
        source := "CountableCarrierDemarcation.carrier_proper" } }
  | .carrierNotOrderComplete =>
    { chapter := .foundation
      kind := .negativeControl
      honesty := .theorem
      continuum := .noneInStatement
      expectedVerdict := .carrierExpressible
      strength := .classicalExtension
      names := {
        guidepost := "PhysicsCarrierAudit.neg_carrierNotOrderComplete"
        source := "CountableCarrierDemarcation.carrier_not_order_complete" } }
  | .realNotDeltaForced =>
    { chapter := .publicSpine
      kind := .negativeControl
      honesty := .theorem
      continuum := .statementConsumes
      expectedVerdict := .continuumConsuming
      strength := .classicalExtension
      names := {
        guidepost := "PhysicsCarrierAudit.neg_realNotDeltaForced"
        source := "Forced.not_deltaForced_real" } }
  | .publicSpineCostSelectionNotUnconditional =>
    { chapter := .publicSpine
      kind := .negativeControl
      honesty := .theorem
      continuum := .statementConsumes
      expectedVerdict := .continuumConsuming
      strength := .classicalExtension
      names := {
        guidepost := "PhysicsCarrierAudit.neg_publicSpine_cost_selection_not_unconditional"
        source := "classification: publicCostSelectionContinuumRole" } }
  | .friedmannXiDecimalNotIntegral =>
    { chapter := .cosmology
      kind := .negativeControl
      honesty := .model
      continuum := .ambientDisplayOnly
      expectedVerdict := .model
      strength := .classicalExtension
      names := {
        guidepost := "PhysicsCarrierAudit.neg_friedmann_xi_decimal_not_integral"
        source := "classification: XiIntegralIdentification := False" } }

/-- Exact Props audited by negative controls. -/
def NegativeControlId.statementProp : NegativeControlId → Prop
  | .rationalMissesPhi => rationalCandidate < carrier
  | .carrierProper => (carrier : Set ℝ) ≠ Set.univ
  | .carrierNotOrderComplete =>
      ∃ S : Set ℝ,
        (∀ x ∈ S, x ∈ carrier)
          ∧ S.Nonempty
          ∧ (∃ b ∈ carrier, ∀ x ∈ S, x ≤ b)
          ∧ ¬ ∃ s, IsLUBIn carrier S s
  | .realNotDeltaForced => ¬ DeltaForced ℝ
  | .publicSpineCostSelectionNotUnconditional =>
      publicCostSelectionContinuumRole = ContinuumRole.statementConsumes
        ∧ (carrier : Set ℝ) ≠ Set.univ
  | .friedmannXiDecimalNotIntegral =>
      ¬ XiIntegralIdentification ∧ ¬ XiInFiniteAudit

def NegativeControlId.ReceiptType : NegativeControlId → Type
  | id => NegativeReceipt (NegativeControlId.statementProp id)

def NegativeControlId.receipt :
    (id : NegativeControlId) → NegativeControlId.ReceiptType id
  | .rationalMissesPhi =>
    { names := (NegativeControlId.row .rationalMissesPhi).names
      strength := .deltaOnly
      evidence := ⟨⟨rationalCandidate_lt_carrier⟩⟩ }
  | .carrierProper =>
    { names := (NegativeControlId.row .carrierProper).names
      strength := .deltaOnly
      evidence := ⟨⟨carrier_proper⟩⟩ }
  | .carrierNotOrderComplete =>
    { names := (NegativeControlId.row .carrierNotOrderComplete).names
      strength := .classicalExtension
      evidence := ⟨⟨carrier_not_order_complete⟩⟩ }
  | .realNotDeltaForced =>
    { names := (NegativeControlId.row .realNotDeltaForced).names
      strength := .classicalExtension
      evidence := ⟨⟨not_deltaForced_real⟩⟩ }
  | .publicSpineCostSelectionNotUnconditional =>
    { names := (NegativeControlId.row .publicSpineCostSelectionNotUnconditional).names
      strength := .classicalExtension
      evidence := ⟨⟨⟨rfl, carrier_proper⟩⟩⟩ }
  | .friedmannXiDecimalNotIntegral =>
    { names := (NegativeControlId.row .friedmannXiDecimalNotIntegral).names
      strength := .classicalExtension
      evidence := ⟨⟨⟨fun h => h, fun h => h⟩⟩⟩ }

/-! ## §6. SelfContainedAudit migration seeds

Parent FiniteAuditSeedId mass/alpha/GapDerivation rows are omitted; closed-form
native constants from CountableCarrierDemarcation replace them. -/

inductive FiniteAuditSeedId where
  | hbarNative
  | coherenceEnergy
  | newtonG
  | einsteinKappa
  | darkEnergyTheta
  deriving DecidableEq, Repr

def FiniteAuditSeedId.kind : FiniteAuditSeedId → AuditKind
  | .hbarNative | .coherenceEnergy | .newtonG | .einsteinKappa
  | .darkEnergyTheta => .scalar

def FiniteAuditSeedId.chapter : FiniteAuditSeedId → PhysicsChapter
  | .hbarNative | .coherenceEnergy | .newtonG | .einsteinKappa => .constants
  | .darkEnergyTheta => .cosmology

def FiniteAuditSeedId.names : FiniteAuditSeedId → DeclNames
  | .hbarNative =>
    { guidepost := "ActualMathematics.CountableCarrierDemarcation.hbarNative"
      source := "IndisputableMonolith.Constants.hbar_eq_phi_inv_fifth" }
  | .coherenceEnergy =>
    { guidepost := "ActualMathematics.CountableCarrierDemarcation.EcohNative"
      source :=
        "IndisputableMonolith.Foundation.CoherenceExponent.coherence_energy_forced" }
  | .newtonG =>
    { guidepost := "ActualMathematics.CountableCarrierDemarcation.GNative"
      source := "IndisputableMonolith.Foundation.MaximalForcing.G_eq_phi5_div_pi" }
  | .einsteinKappa =>
    { guidepost := "ActualMathematics.CountableCarrierDemarcation.kappaNative"
      source := "IndisputableMonolith.Constants.kappa_einstein_eq" }
  | .darkEnergyTheta =>
    { guidepost :=
        "ActualMathematics.CountableCarrierDemarcation.darkEnergyThetaNative"
      source :=
        "IndisputableMonolith.Cosmology.DarkEnergyPhiDilutionLaw.darkEnergyThetaFromDimension_eq_phiFour" }

noncomputable def FiniteAuditSeedId.realizedValues : FiniteAuditSeedId → List ℝ
  | .hbarNative => [CountableCarrierDemarcation.hbarNative]
  | .coherenceEnergy => [CountableCarrierDemarcation.EcohNative]
  | .newtonG => [CountableCarrierDemarcation.GNative]
  | .einsteinKappa => [CountableCarrierDemarcation.kappaNative]
  | .darkEnergyTheta => [CountableCarrierDemarcation.darkEnergyThetaNative]

def FiniteAuditSeedId.statementProp : FiniteAuditSeedId → Prop
  | .hbarNative =>
      CountableCarrierDemarcation.hbarNative = Constants.phi ^ (-(5 : ℝ))
  | .coherenceEnergy =>
      CountableCarrierDemarcation.EcohNative = Constants.phi ^ (-(5 : ℝ))
  | .newtonG =>
      CountableCarrierDemarcation.GNative = Constants.phi ^ (5 : ℝ) / Real.pi
  | .einsteinKappa =>
      CountableCarrierDemarcation.kappaNative = 8 * Constants.phi ^ (5 : ℝ)
  | .darkEnergyTheta =>
      CountableCarrierDemarcation.darkEnergyThetaNative =
        Constants.phi ^ (-(4 : ℝ))

def FiniteAuditSeedId.Receipt : FiniteAuditSeedId → Type
  | id =>
    match FiniteAuditSeedId.kind id with
    | .scalar =>
        ScalarReceipt (FiniteAuditSeedId.realizedValues id)
          (FiniteAuditSeedId.statementProp id)
    | .structural | .openTarget | .negativeControl =>
        PEmpty

private def seedMeta (id : FiniteAuditSeedId) (honesty : HonestyTier)
    (continuum : ContinuumRole) (strength : StrengthTag) : ProvenMeta where
  honesty := honesty
  continuum := continuum
  strength := strength
  names := FiniteAuditSeedId.names id

noncomputable section

/-- Hand-written receipts; bodies cite SelfContainedAudit / carrier theorems. -/
noncomputable def FiniteAuditSeedId.receipt :
    (id : FiniteAuditSeedId) → FiniteAuditSeedId.Receipt id
  | .hbarNative =>
    { seedMeta .hbarNative .theorem .ambientDisplayOnly .traceClosure with
      evidence := {
        mem := by
          intro x hx
          simp only [FiniteAuditSeedId.realizedValues, List.mem_cons,
            List.mem_nil_iff] at hx
          rcases hx with rfl | h
          · exact CountableCarrierDemarcation.hbarNative_mem_carrier
          · exact False.elim h
        statement := ⟨rfl⟩ } }
  | .coherenceEnergy =>
    { seedMeta .coherenceEnergy .theorem .ambientDisplayOnly .traceClosure with
      evidence := {
        mem := by
          intro x hx
          simp only [FiniteAuditSeedId.realizedValues, List.mem_cons,
            List.mem_nil_iff] at hx
          rcases hx with rfl | h
          · exact CountableCarrierDemarcation.EcohNative_mem_carrier
          · exact False.elim h
        statement := ⟨rfl⟩ } }
  | .newtonG =>
    { seedMeta .newtonG .theorem .ambientDisplayOnly .traceClosure with
      evidence := {
        mem := by
          intro x hx
          simp only [FiniteAuditSeedId.realizedValues, List.mem_cons,
            List.mem_nil_iff] at hx
          rcases hx with rfl | h
          · exact CountableCarrierDemarcation.GNative_mem_carrier
          · exact False.elim h
        statement := ⟨rfl⟩ } }
  | .einsteinKappa =>
    { seedMeta .einsteinKappa .theorem .ambientDisplayOnly .traceClosure with
      evidence := {
        mem := by
          intro x hx
          simp only [FiniteAuditSeedId.realizedValues, List.mem_cons,
            List.mem_nil_iff] at hx
          rcases hx with rfl | h
          · exact CountableCarrierDemarcation.kappaNative_mem_carrier
          · exact False.elim h
        statement := ⟨rfl⟩ } }
  | .darkEnergyTheta =>
    { seedMeta .darkEnergyTheta .theorem .ambientDisplayOnly .traceClosure with
      evidence := {
        mem := by
          intro x hx
          simp only [FiniteAuditSeedId.realizedValues, List.mem_cons,
            List.mem_nil_iff] at hx
          rcases hx with rfl | h
          · exact CountableCarrierDemarcation.darkEnergyThetaNative_mem_carrier
          · exact False.elim h
        statement := ⟨rfl⟩ } }

/-! ## §7. Core corpus id (seeds ⊕ negatives) -/

inductive PhysicsAuditId where
  | neg : NegativeControlId → PhysicsAuditId
  | seed : FiniteAuditSeedId → PhysicsAuditId
  deriving DecidableEq, Repr

def PhysicsAuditId.kind : PhysicsAuditId → AuditKind
  | .neg _ => .negativeControl
  | .seed id => FiniteAuditSeedId.kind id

def PhysicsAuditId.chapter : PhysicsAuditId → PhysicsChapter
  | .neg id => (NegativeControlId.row id).chapter
  | .seed id => FiniteAuditSeedId.chapter id

def FiniteAuditSeedId.continuum : FiniteAuditSeedId → ContinuumRole
  | _ => .ambientDisplayOnly

def FiniteAuditSeedId.strength : FiniteAuditSeedId → StrengthTag
  | _ => .traceClosure

def PhysicsAuditId.row : PhysicsAuditId → AuditRow
  | .neg id => NegativeControlId.row id
  | .seed id =>
    { chapter := FiniteAuditSeedId.chapter id
      kind := FiniteAuditSeedId.kind id
      honesty := .theorem
      continuum := FiniteAuditSeedId.continuum id
      expectedVerdict := .carrierExpressible
      strength := FiniteAuditSeedId.strength id
      names := FiniteAuditSeedId.names id }

def PhysicsAuditId.statementProp : PhysicsAuditId → Prop
  | .neg id => NegativeControlId.statementProp id
  | .seed id => FiniteAuditSeedId.statementProp id

def PhysicsAuditId.Receipt : PhysicsAuditId → Type
  | .neg id => NegativeControlId.ReceiptType id
  | .seed id => FiniteAuditSeedId.Receipt id

noncomputable def PhysicsAuditId.receipt :
    (id : PhysicsAuditId) → PhysicsAuditId.Receipt id
  | .neg id => NegativeControlId.receipt id
  | .seed id => FiniteAuditSeedId.receipt id

theorem physicsAuditId_receipts_total :
    ∀ id : PhysicsAuditId, Nonempty (PhysicsAuditId.Receipt id) :=
  fun id => ⟨PhysicsAuditId.receipt id⟩

/-! ## §8. Core aggregate -/

structure CorePhysicsCarrierAudit : Prop where
  carrier_deltaForced : DeltaForced carrier
  carrier_proper : (carrier : Set ℝ) ≠ Set.univ
  carrier_incomplete :
    ∃ S : Set ℝ,
      (∀ x ∈ S, x ∈ carrier)
        ∧ S.Nonempty
        ∧ (∃ b ∈ carrier, ∀ x ∈ S, x ≤ b)
        ∧ ¬ ∃ s, IsLUBIn carrier S s
  self_contained_audit : SelfContainedAudit
  every_core_id : ∀ id : PhysicsAuditId, Nonempty (PhysicsAuditId.Receipt id)
  theorem_core_excludes_statementConsumes :
    ∀ id : PhysicsAuditId,
      (PhysicsAuditId.row id).honesty = .theorem →
      (PhysicsAuditId.row id).kind ≠ .negativeControl →
      (PhysicsAuditId.row id).continuum ≠ .statementConsumes

theorem core_physics_carrier_audit_holds : CorePhysicsCarrierAudit where
  carrier_deltaForced := carrier_deltaForced
  carrier_proper := carrier_proper
  carrier_incomplete := carrier_not_order_complete
  self_contained_audit := self_contained_audit_holds
  every_core_id := physicsAuditId_receipts_total
  theorem_core_excludes_statementConsumes := by
    intro id _hHon hKind
    cases id with
    | neg n =>
        have hk : (PhysicsAuditId.row (.neg n)).kind = AuditKind.negativeControl := by
          cases n <;> rfl
        exact (hKind hk).elim
    | seed s =>
        have hc : (PhysicsAuditId.row (.seed s)).continuum ≠
            ContinuumRole.statementConsumes := by
          cases s <;> intro h <;> cases h
        exact hc

theorem core_physics_carrier_audit_tagged :
    Tagged StrengthTag.classicalExtension CorePhysicsCarrierAudit where
  holds := core_physics_carrier_audit_holds

/-- Migration projection: Core gate implies SelfContainedAudit. -/
theorem self_contained_audit_of_core (H : CorePhysicsCarrierAudit) :
    SelfContainedAudit :=
  H.self_contained_audit

end

end PhysicsCarrierAudit
end ActualMathematics

import ActualMathematics.DeltaKernel.BootstrapDemarcation

/-!
# Bootstrap F5: PublicSpine bridge (actual-mathematics side)

`IndisputableMonolith.Foundation.PublicSpine` and the δ bootstrap state the
same forcing / physically-real verdict. Lean cannot import across the two
repositories, so the bridge is three receipts:

1. **Shared definitions.** `DeltaForced.lean` and `Strength.lean` are
   byte-identical between the repos modulo namespace prefix
   (`δ/check_delta_publicspine_bridge.sh` in the reality repo verifies this
   deterministically and fails on drift).
2. **Shared claim block.** The region between the `BRIDGE_CLAIM_BLOCK`
   markers below is byte-identical to the corresponding region of
   `IndisputableMonolith/Foundation/PublicSpineBootstrapBridge.lean`
   (same script verifies).
3. **Both sides prove it.** This file inhabits the claim from the bootstrap
   F1 certificates; the IM file inhabits the same formulas from
   `PublicSpine.forced_tower_holds` / `floor_demarcation_holds`, with `rfl`
   pins to `PublicSpine.ForcedTower` / `Floor_Demarcation`.

Strength tags match by construction: `deltaOnly` on the tower,
`classicalExtension` on every conjunct that touches ℝ.
-/

namespace ActualMathematics.DeltaKernel.Bootstrap

open ActualMathematics
open ActualMathematics.Forced

-- BRIDGE_CLAIM_BLOCK_BEGIN
/-- Forced tower formula shared with the PublicSpine bridge. -/
def BridgeForcedTower : Prop :=
  PhysicallyReal ℕ ∧ PhysicallyReal ℤ ∧ PhysicallyReal ℚ

/-- Continuum purchase formula shared with the PublicSpine bridge. -/
def BridgeContinuumPurchase : Prop :=
  ¬ DeltaForced ℝ

/-- Demarcation formula shared with the PublicSpine bridge. -/
def BridgeDemarcation : Prop :=
  PhysicallyReal ℕ ∧ PhysicallyReal ℤ ∧ PhysicallyReal ℚ ∧ ¬ PhysicallyReal ℝ

/-- The one claim both repositories state: the δ tower is physically real at
the `deltaOnly` stratum, the continuum is a `classicalExtension` purchase, and
physical reality is definitionally the δ-forced certificate. -/
structure DeltaBootstrapPublicSpineClaim : Prop where
  forced_tower : Tagged StrengthTag.deltaOnly BridgeForcedTower
  continuum_purchase :
      Tagged StrengthTag.classicalExtension BridgeContinuumPurchase
  demarcation : Tagged StrengthTag.classicalExtension BridgeDemarcation
  physically_real_is_deltaForced :
      ∀ X : Type, PhysicallyReal X ↔ DeltaForced X
-- BRIDGE_CLAIM_BLOCK_END

/-- The bootstrap side of the bridge, from the F1 certificates. -/
theorem deltaBootstrapPublicSpineClaim_holds : DeltaBootstrapPublicSpineClaim where
  forced_tower := bootstrap_forced_tower
  continuum_purchase := bootstrap_continuum_purchase
  demarcation := bootstrap_demarcation
  physically_real_is_deltaForced := fun X => physicallyReal_iff_deltaForced X

/-- Statement pin: the bridge tower formula is the F1 tower formula. -/
theorem bridge_forced_tower_pin :
    BridgeForcedTower =
      (PhysicallyReal ℕ ∧ PhysicallyReal ℤ ∧ PhysicallyReal ℚ) := rfl

/-- Statement pin: the bridge demarcation formula is the F1 demarcation. -/
theorem bridge_demarcation_pin :
    BridgeDemarcation =
      (PhysicallyReal ℕ ∧ PhysicallyReal ℤ ∧ PhysicallyReal ℚ ∧
        ¬ PhysicallyReal ℝ) := rfl

/-- F5 package (this side). The cross-repo textual receipt is
`δ/check_delta_publicspine_bridge.sh`. -/
structure BootstrapPublicSpineBridgeSpec : Prop where
  claim : DeltaBootstrapPublicSpineClaim
  tower_pin : BridgeForcedTower =
      (PhysicallyReal ℕ ∧ PhysicallyReal ℤ ∧ PhysicallyReal ℚ)
  demarcation_pin : BridgeDemarcation =
      (PhysicallyReal ℕ ∧ PhysicallyReal ℤ ∧ PhysicallyReal ℚ ∧
        ¬ PhysicallyReal ℝ)

theorem bootstrap_public_spine_bridge : BootstrapPublicSpineBridgeSpec where
  claim := deltaBootstrapPublicSpineClaim_holds
  tower_pin := bridge_forced_tower_pin
  demarcation_pin := bridge_demarcation_pin

#print axioms deltaBootstrapPublicSpineClaim_holds
#print axioms bootstrap_public_spine_bridge

end ActualMathematics.DeltaKernel.Bootstrap

/-
  PhysicsCarrierAudit/Manifest.lean

  Thin count surface synced to the parent freeze
  (δ/audits/full_physics_carrier_manifest.json in the reality repo). Completeness
  of that registry is owned by the parent scripts; this module only records the
  expected raw/semantic cardinalities for Lean-side documentation and Aggregate
  cross-checks.
-/

namespace ActualMathematics
namespace PhysicsCarrierAudit

/-- Raw `guidepost_*` / `target_*` endpoints in the twelve-chapter freeze. -/
def expectedRawCount : Nat := 136

/-- Semantic (deduplicated canonical) claims in the freeze. -/
def expectedSemanticCount : Nat := 130

theorem expectedRawCount_eq : expectedRawCount = 136 := rfl
theorem expectedSemanticCount_eq : expectedSemanticCount = 130 := rfl

end PhysicsCarrierAudit
end ActualMathematics

import ActualMathematics.DeltaForced
import ActualMathematics.Representability
import ActualMathematics.Strength

/-!
# Bootstrap F1: demarcation pin (forcing-chain scope)

Physically real = δ-forced = representable tower under the forcing cut.
ℕ, ℤ, ℚ are forced. ℝ is a classical purchase. This module does **not**
license reconstructing ZFC or “deriving all sets.”

CLAIM: CLOSED positive for the bootstrap demarcation verdict.
DOMAIN: ActualMathematics Forced / Representability predicates.
PREMISES:
  A1. `DeltaForced X := Nonempty (X ↪ ℕ)` (countable certificate).
  A2. `PhysicallyReal := DeltaForced` (definitional thesis).
  A3. Representability supplies covering decoders for the same tower.
  A4. ¬`DeltaForced ℝ` uses classical uncountability of ℝ.
REACH: max licensed:
  * ℕ, ℤ, ℚ are physically real / δ-forced / representable;
  * ℝ is not δ-forced (classicalExtension tag);
  * bootstrap refuses the claim that every type is forced.
does NOT license:
  * ZFC / CIC reconstruction;
  * that every countable type is ontologically forced by a bare act;
  * EXCLUSIVITY: the demarcation predicate is a countability CUT, deliberately
    coarse. Every subtype of ℕ passes it (witnesses below). Passing the cut
    does not assert δ-generation; the positive δ-generation content lives in
    the explicit tower constructions (F2), not in this predicate;
  * absolute consistency of the host.
-/

namespace ActualMathematics.DeltaKernel.Bootstrap

open ActualMathematics
open ActualMathematics.Forced

/-- Audit label matching `IndisputableMonolith.Foundation.PublicSpine.Tagged`. -/
structure Tagged (tag : StrengthTag) (P : Prop) : Prop where
  holds : P

/-- F1 core: physical reality coincides with the δ-forced certificate. -/
theorem physicallyReal_eq_deltaForced (X : Type) :
    PhysicallyReal X ↔ DeltaForced X :=
  physicallyReal_iff_deltaForced X

/-- Forced tower under StrengthTag.deltaOnly (choice-free certificates). -/
theorem bootstrap_forced_tower :
    Tagged StrengthTag.deltaOnly
      (PhysicallyReal ℕ ∧ PhysicallyReal ℤ ∧ PhysicallyReal ℚ) where
  holds := forcedTower

/-- Representable tower: explicit covering decoders for ℕ, ℤ, ℚ. -/
theorem bootstrap_representable_tower :
    Tagged StrengthTag.deltaOnly
      (DeltaRepresentable ℕ ∧ DeltaRepresentable ℤ ∧ DeltaRepresentable ℚ) where
  holds := representable_tower

/-- Continuum purchase: ℝ is not δ-forced. Classical uncountability lives here. -/
theorem bootstrap_continuum_purchase :
    Tagged StrengthTag.classicalExtension (¬ DeltaForced ℝ) where
  holds := not_deltaForced_real

/-- Full demarcation (tower + continuum cut). Classical tag because of ℝ. -/
theorem bootstrap_demarcation :
    Tagged StrengthTag.classicalExtension
      (PhysicallyReal ℕ ∧ PhysicallyReal ℤ ∧ PhysicallyReal ℚ ∧ ¬ PhysicallyReal ℝ) where
  holds := demarcation

/-- Exact negative boundary: the certificate class does not contain every Lean type.
This does not by itself rule out a coded interpretation of a formal set theory. -/
def NotAllTypesPhysicallyReal : Prop :=
  ¬ (∀ (X : Type), PhysicallyReal X)

/-- The classical real line witnesses the exact boundary above. -/
theorem not_all_types_physically_real : NotAllTypesPhysicallyReal := by
  intro h
  exact not_deltaForced_real (h ℝ)

/-- F1 package. -/
structure BootstrapDemarcationSpec : Prop where
  physically_real_iff : ∀ X : Type, PhysicallyReal X ↔ DeltaForced X
  forced_tower :
      Tagged StrengthTag.deltaOnly
        (PhysicallyReal ℕ ∧ PhysicallyReal ℤ ∧ PhysicallyReal ℚ)
  representable_tower :
      Tagged StrengthTag.deltaOnly
        (DeltaRepresentable ℕ ∧ DeltaRepresentable ℤ ∧ DeltaRepresentable ℚ)
  continuum_purchase :
      Tagged StrengthTag.classicalExtension (¬ DeltaForced ℝ)
  demarcation :
      Tagged StrengthTag.classicalExtension
        (PhysicallyReal ℕ ∧ PhysicallyReal ℤ ∧ PhysicallyReal ℚ ∧ ¬ PhysicallyReal ℝ)
  not_all_types_physically_real : NotAllTypesPhysicallyReal

theorem bootstrap_demarcation_spec : BootstrapDemarcationSpec where
  physically_real_iff := physicallyReal_eq_deltaForced
  forced_tower := bootstrap_forced_tower
  representable_tower := bootstrap_representable_tower
  continuum_purchase := bootstrap_continuum_purchase
  demarcation := bootstrap_demarcation
  not_all_types_physically_real := not_all_types_physically_real

#print axioms bootstrap_forced_tower
#print axioms bootstrap_representable_tower
#print axioms bootstrap_continuum_purchase
#print axioms bootstrap_demarcation_spec

end ActualMathematics.DeltaKernel.Bootstrap

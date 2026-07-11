import ActualMathematics.DeltaKernel.BootstrapFoundation
import ActualMathematics.PRCSetTheoryParse

/-!
# Bootstrap B4: derived set / type objects

Object syntax still has no set former or type former
(`object_primitive_audit`). Finite sets and the two-element type appear only
as constructions on the forced arithmetic carrier.

- Hereditarily finite sets = Ackermann codes on `Nat` (= eval of δ numerals).
- The two-element type = the Boolean shadow of absence vs presence of a
  distinction step.

Neither is an object-language primitive. Both are derived carriers with
explicit membership / canonicity theorems.
-/

namespace ActualMathematics.DeltaKernel.Bootstrap

open ActualMathematics.DeltaKernel
open ActualMathematics
open SetTheoryParse

/-! ## Finite sets from δ numerals -/

/-- A δ-derived finite set is an Ackermann code: a natural number obtained as
the value of a closed δ numeral. -/
structure DerivedHF where
  code : Nat
  witness : DTerm
  closed_eval : witness.eval (fun _ => 0) = code

/-- Empty set from the zero numeral. -/
def emptyHF : DerivedHF where
  code := 0
  witness := .zero
  closed_eval := rfl

/-- Singleton `{∅}` from the one-step numeral. -/
def singletonEmptyHF : DerivedHF where
  code := 1
  witness := .succ .zero
  closed_eval := rfl

theorem empty_ne_singletonEmpty :
    emptyHF.code ≠ singletonEmptyHF.code := by
  decide

theorem derived_extensionality (m n : Nat) :
    m = n ↔ ∀ i, (Mem i m ↔ Mem i n) :=
  ext_iff m n

/-! ## Two-element type from presence / absence -/

/-- Derived two-point carrier: silence vs a completed distinction. -/
inductive DerivedTwo where
  | absent
  | present
  deriving DecidableEq, Repr

def ofBool : Bool → DerivedTwo
  | false => .absent
  | true => .present

def toBool : DerivedTwo → Bool
  | .absent => false
  | .present => true

theorem derivedTwo_canonicity (x : DerivedTwo) :
    x = .absent ∨ x = .present := by
  cases x <;> simp

theorem derivedTwo_no_confusion : DerivedTwo.absent ≠ .present := by
  intro h
  cases h

theorem derivedTwo_roundtrip (x : DerivedTwo) : ofBool (toBool x) = x := by
  cases x <;> rfl

/-- B4 package: sets and the two-point type are constructions, not primitives. -/
def BootstrapDerivedSpec : Prop :=
  ObjectPrimitiveAudit ∧
  emptyHF.code ≠ singletonEmptyHF.code ∧
  (∀ m n : Nat, m = n ↔ ∀ i, (Mem i m ↔ Mem i n)) ∧
  (∀ x : DerivedTwo, x = .absent ∨ x = .present) ∧
  DerivedTwo.absent ≠ .present

theorem bootstrap_derived : BootstrapDerivedSpec :=
  ⟨object_primitive_audit, empty_ne_singletonEmpty, derived_extensionality,
   derivedTwo_canonicity, derivedTwo_no_confusion⟩

#print axioms bootstrap_derived

end ActualMathematics.DeltaKernel.Bootstrap

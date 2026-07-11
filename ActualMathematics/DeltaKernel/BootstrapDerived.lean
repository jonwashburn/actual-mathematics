import ActualMathematics.DeltaKernel.BootstrapFoundation
import ActualMathematics.PRCSetTheoryParse

/-!
# Bootstrap B4: derived set / type objects

Object syntax still has no set former or type former
(`object_primitive_audit`). Finite sets and the two-element type appear only
as constructions on the forced arithmetic carrier.

- Hereditarily finite sets are Ackermann codes denoted by closed δ numerals.
  Empty and adjunction provide formation; membership characterizations provide
  elimination; extensionality provides equality.
- The two-element object is a quotient of existing δ terms by their
  zero/nonzero observation.  It is not a fresh inductive object-language type.

Neither is an object-language primitive. Both are derived carriers with
explicit formation, equality, substitution, and elimination theorems.  Lean's
`Type`, subtype construction, and `Prop` remain part of the outside metatheory.
-/

namespace ActualMathematics.DeltaKernel.Bootstrap

open ActualMathematics.DeltaKernel
open ActualMathematics
open SetTheoryParse

/-! ## Finite sets from δ numerals -/

/-- A derived HF object is a code in the δ natural carrier.  `abbrev` makes
clear that no new carrier is postulated. -/
abbrev DerivedHF := Nat

/-- Canonical δ term denoting an HF code. -/
def denoteHF (n : DerivedHF) : DTerm := DTerm.ofNat n

def memHF (x a : DerivedHF) : Prop := Mem x a

def emptyHF : DerivedHF := 0

def adjHF (a b : DerivedHF) : DerivedHF := hfAdj a b

/-- Formation: every HF object is denoted by a closed δ term. -/
theorem derivedHF_formation (n : DerivedHF) :
    (denoteHF n).eval (fun _ => 0) = n :=
  eval_ofNat_closed n

/-- Equality law: two derived sets are equal exactly when membership agrees. -/
theorem derivedHF_extensionality (m n : DerivedHF) :
    m = n ↔ ∀ i, (memHF i m ↔ memHF i n) :=
  ext_iff m n

/-- Empty elimination law. -/
theorem derivedHF_empty_elim (i : DerivedHF) :
    ¬ memHF i emptyHF :=
  not_mem_empty i

/-- Adjunction elimination law. -/
theorem derivedHF_adj_elim (i a b : DerivedHF) :
    memHF i (adjHF a b) ↔ memHF i a ∨ i = b :=
  mem_hfAdj i a b

theorem empty_ne_singletonEmpty :
    emptyHF ≠ adjHF emptyHF emptyHF := by
  intro h
  have hm := derivedHF_adj_elim emptyHF emptyHF emptyHF
  have hadj : memHF emptyHF (adjHF emptyHF emptyHF) := hm.mpr (Or.inr rfl)
  rw [← h] at hadj
  exact derivedHF_empty_elim emptyHF hadj

/-! ## Two-element quotient of existing δ terms -/

/-- The sole observation retained by the two-point quotient. -/
def twoObservation (t : DTerm) : Bool :=
  if t.eval (fun _ => 0) = 0 then false else true

/-- Terms are identified when their zero/nonzero observations agree. -/
def twoEquivalent (t u : DTerm) : Prop :=
  twoObservation t = twoObservation u

theorem twoEquivalent_equivalence : Equivalence twoEquivalent where
  refl := fun _ => rfl
  symm := fun h => h.symm
  trans := fun h₁ h₂ => h₁.trans h₂

def derivedTwoSetoid : Setoid DTerm where
  r := twoEquivalent
  iseqv := twoEquivalent_equivalence

/-- Quotient-derived two-element carrier.  No field assumes canonicity. -/
def DerivedTwo : Type := Quot derivedTwoSetoid

namespace DerivedTwo

def absent : DerivedTwo := Quot.mk derivedTwoSetoid DTerm.zero

def present : DerivedTwo := Quot.mk derivedTwoSetoid (DTerm.succ DTerm.zero)

end DerivedTwo

def ofBool : Bool → DerivedTwo
  | false => DerivedTwo.absent
  | true => DerivedTwo.present

def toBool : DerivedTwo → Bool :=
  Quot.lift twoObservation (fun _ _ h => h)

/-- Canonical forms, proved by quotient induction and Boolean case analysis. -/
theorem derivedTwo_canonicity (x : DerivedTwo) :
    x = DerivedTwo.absent ∨ x = DerivedTwo.present := by
  induction x using Quot.ind with
  | _ t =>
      cases h : twoObservation t with
      | false =>
          left
          apply Quot.sound
          exact h
      | true =>
          right
          apply Quot.sound
          exact h

theorem derivedTwo_no_confusion :
    DerivedTwo.absent ≠ DerivedTwo.present := by
  intro h
  have hv := congrArg toBool h
  cases hv

/-- Equality substitution law for predicates on the derived object. -/
theorem derivedTwo_substitution {x y : DerivedTwo} (h : x = y)
    (P : DerivedTwo → Prop) :
    P x ↔ P y := by
  cases h
  rfl

/-- Elimination law from the two proved canonical forms. -/
theorem derivedTwo_elimination (P : DerivedTwo → Prop)
    (hAbsent : P DerivedTwo.absent)
    (hPresent : P DerivedTwo.present) :
    ∀ x : DerivedTwo, P x := by
  intro x
  rcases derivedTwo_canonicity x with h | h
  · rwa [h]
  · rwa [h]

theorem derivedTwo_roundtrip (x : DerivedTwo) : ofBool (toBool x) = x := by
  rcases derivedTwo_canonicity x with h | h
  · subst x
    rfl
  · subst x
    rfl

/-- B4 package: set and type objects are code constructions with their laws,
not additions to `DTerm` or `DFormula`. -/
def BootstrapDerivedSpec : Prop :=
  ObjectPrimitiveAudit ∧
  (∀ n : DerivedHF, (denoteHF n).eval (fun _ => 0) = n) ∧
  (∀ m n : DerivedHF, m = n ↔ ∀ i, (memHF i m ↔ memHF i n)) ∧
  (∀ i : DerivedHF, ¬ memHF i emptyHF) ∧
  (∀ i a b : DerivedHF, memHF i (adjHF a b) ↔ memHF i a ∨ i = b) ∧
  emptyHF ≠ adjHF emptyHF emptyHF ∧
  (∀ x : DerivedTwo,
    x = DerivedTwo.absent ∨ x = DerivedTwo.present) ∧
  DerivedTwo.absent ≠ DerivedTwo.present ∧
  (∀ (P : DerivedTwo → Prop),
    P DerivedTwo.absent → P DerivedTwo.present → ∀ x, P x)

theorem bootstrap_derived : BootstrapDerivedSpec :=
  ⟨object_primitive_audit,
   derivedHF_formation,
   derivedHF_extensionality,
   derivedHF_empty_elim,
   derivedHF_adj_elim,
   empty_ne_singletonEmpty,
   derivedTwo_canonicity,
   derivedTwo_no_confusion,
   derivedTwo_elimination⟩

#print axioms derivedHF_extensionality
#print axioms derivedHF_adj_elim
#print axioms derivedTwo_elimination
#print axioms bootstrap_derived

end ActualMathematics.DeltaKernel.Bootstrap

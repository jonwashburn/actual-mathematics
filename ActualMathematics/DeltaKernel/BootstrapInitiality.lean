import ActualMathematics.DeltaKernel.Examples

/-!
# The δ bootstrap: primitive audit and syntax initiality

This is the first rung of the bootstrap theorem.  The outside verifier is Lean:
`Type`, `Prop`, inductive definitions, functions, equality, `Nat`, and structural
recursion belong to the metatheory.  The object calculus is the data in
`Syntax.lean` and `Check.lean`.

The theorem in this file is deliberately narrower than "the language is forced
by a bare distinction."  It proves two exact facts.

1. The frozen object syntax has no set former, membership symbol, type former,
   universe, comprehension rule, or propositions-as-types constructor.
2. Once the displayed term signature is licensed, `DTerm` is its initial
   algebra: every interpretation is the unique structure-preserving fold.

`zero` and `succ` are the δ carrier operations.  `add` and `mul` are named
recursion-licensed extensions.  The logical constructors and proof rules are
also part of the licensed calculus.  No theorem below promotes those licensed
rules into consequences of an unstructured act.
-/

namespace ActualMathematics.DeltaKernel.Bootstrap

open ActualMathematics.DeltaKernel

/-! ## Exact object-level primitive audit -/

/-- Metatheoretic classes used only to audit the roots of object-language data. -/
inductive OntologyClass where
  | distinction
  | arithmetic
  | logic
  | proof
  | set
  | type
  deriving DecidableEq, Repr

/-- Root classification of every term constructor in the frozen δ syntax. -/
def termClass : DTerm → OntologyClass
  | .var _ => .logic
  | .zero => .distinction
  | .succ _ => .distinction
  | .add _ _ => .arithmetic
  | .mul _ _ => .arithmetic

/-- Root classification of every formula constructor in the frozen δ syntax. -/
def formulaClass : DFormula → OntologyClass
  | .eq _ _ => .logic
  | .fls => .logic
  | .conj _ _ => .logic
  | .disj _ _ => .logic
  | .impl _ _ => .logic
  | .all _ => .logic
  | .ex _ => .logic

/-- Derivation constructors are proof rules, including the separately ledgered
posit rules.  None is an object constructor. -/
def derivClass (_ : Deriv) : OntologyClass := .proof

theorem term_has_no_set_or_type_primitive (t : DTerm) :
    termClass t ≠ .set ∧ termClass t ≠ .type := by
  cases t <;> simp [termClass]

theorem formula_has_no_set_or_type_primitive (φ : DFormula) :
    formulaClass φ ≠ .set ∧ formulaClass φ ≠ .type := by
  cases φ <;> simp [formulaClass]

theorem deriv_has_no_set_or_type_primitive (d : Deriv) :
    derivClass d ≠ .set ∧ derivClass d ≠ .type := by
  simp [derivClass]

/-- The exact primitive-budget receipt.  This is a statement about the frozen
constructor inventory, not a claim that the inventory exists without a
metatheory. -/
def ObjectPrimitiveAudit : Prop :=
  (∀ t : DTerm, termClass t ≠ .set ∧ termClass t ≠ .type) ∧
  (∀ φ : DFormula, formulaClass φ ≠ .set ∧ formulaClass φ ≠ .type) ∧
  (∀ d : Deriv, derivClass d ≠ .set ∧ derivClass d ≠ .type)

theorem object_primitive_audit : ObjectPrimitiveAudit :=
  ⟨term_has_no_set_or_type_primitive,
   formula_has_no_set_or_type_primitive,
   deriv_has_no_set_or_type_primitive⟩

/-! ## Initiality of the licensed term signature -/

/-- A realization of the displayed term signature.  This is a metatheoretic
interface used to state initiality.  It assumes operations, never their laws. -/
structure TermAlgebra where
  carrier : Type
  var : Nat → carrier
  zero : carrier
  succ : carrier → carrier
  add : carrier → carrier → carrier
  mul : carrier → carrier → carrier

/-- A map of term algebras preserves every constructor of the displayed
signature. -/
structure TermHom (A B : TermAlgebra) where
  map : A.carrier → B.carrier
  map_var : ∀ n, map (A.var n) = B.var n
  map_zero : map A.zero = B.zero
  map_succ : ∀ x, map (A.succ x) = B.succ (map x)
  map_add : ∀ x y, map (A.add x y) = B.add (map x) (map y)
  map_mul : ∀ x y, map (A.mul x y) = B.mul (map x) (map y)

theorem TermHom.ext {A B : TermAlgebra} {f g : TermHom A B}
    (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The syntax itself as an algebra. -/
def termSyntax : TermAlgebra where
  carrier := DTerm
  var := DTerm.var
  zero := DTerm.zero
  succ := DTerm.succ
  add := DTerm.add
  mul := DTerm.mul

/-- Structural interpretation of a δ term in any realization. -/
def foldTerm (A : TermAlgebra) : DTerm → A.carrier
  | .var n => A.var n
  | .zero => A.zero
  | .succ t => A.succ (foldTerm A t)
  | .add t u => A.add (foldTerm A t) (foldTerm A u)
  | .mul t u => A.mul (foldTerm A t) (foldTerm A u)

/-- The structural fold packaged as a homomorphism. -/
def foldHom (A : TermAlgebra) : TermHom termSyntax A where
  map := foldTerm A
  map_var := fun _ => rfl
  map_zero := rfl
  map_succ := fun _ => rfl
  map_add := fun _ _ => rfl
  map_mul := fun _ _ => rfl

/-- Every homomorphism out of the syntax is the structural fold. -/
theorem hom_eq_fold (A : TermAlgebra) (f : TermHom termSyntax A) :
    ∀ t, f.map t = foldTerm A t := by
  intro t
  induction t with
  | var n => exact f.map_var n
  | zero => exact f.map_zero
  | succ t ih =>
      calc
        f.map (.succ t) = A.succ (f.map t) := f.map_succ t
        _ = A.succ (foldTerm A t) := by rw [ih]
  | add t u iht ihu =>
      calc
        f.map (.add t u) = A.add (f.map t) (f.map u) := f.map_add t u
        _ = A.add (foldTerm A t) (foldTerm A u) := by rw [iht, ihu]
  | mul t u iht ihu =>
      calc
        f.map (.mul t u) = A.mul (f.map t) (f.map u) := f.map_mul t u
        _ = A.mul (foldTerm A t) (foldTerm A u) := by rw [iht, ihu]

/-- Initiality for each target realization: one homomorphism exists and every
homomorphism is equal to it. -/
def termInitial (A : TermAlgebra) :
    ∃ f : TermHom termSyntax A, ∀ g : TermHom termSyntax A, g = f :=
  ⟨foldHom A, fun g => TermHom.ext (funext (fun t => by
    rw [hom_eq_fold A g t]
    rfl))⟩

/-- The initiality target as a transparent proposition. -/
def TermSyntaxInitial : Prop :=
  ∀ A : TermAlgebra,
    ∃ f : TermHom termSyntax A, ∀ g : TermHom termSyntax A, g = f

theorem term_syntax_initial : TermSyntaxInitial :=
  termInitial

/-! ## The checker is executable and non-vacuous -/

/-- Every checker run returns either one audited result or rejection. -/
theorem check_decides (Γ : Ctx) (d : Deriv) :
    (∃ φ O, check Γ d = some (φ, O)) ∨ check Γ d = none := by
  cases h : check Γ d with
  | none => exact Or.inr rfl
  | some result =>
      obtain ⟨φ, O⟩ := result
      exact Or.inl ⟨φ, O, rfl⟩

/-- Hostile witness: an out-of-range hypothesis is rejected. -/
theorem checker_rejects_bad_hyp :
    check [] (.hyp 0) = none := by
  rfl

/-- Positive and negative witnesses together bar the vacuous checker model. -/
theorem checker_nonvacuous :
    check [] Examples.onePlusOne =
        some (.eq (.add Examples.one Examples.one) Examples.two, .empty) ∧
      check [] (.hyp 0) = none :=
  ⟨Examples.onePlusOne_forced, checker_rejects_bad_hyp⟩

/-! ## First-rung capstone -/

def BootstrapInitialitySpec : Prop :=
  ObjectPrimitiveAudit ∧
  TermSyntaxInitial ∧
  (check [] Examples.onePlusOne =
      some (.eq (.add Examples.one Examples.one) Examples.two, .empty) ∧
    check [] (.hyp 0) = none)

theorem bootstrap_initiality : BootstrapInitialitySpec :=
  ⟨object_primitive_audit, term_syntax_initial, checker_nonvacuous⟩

#print axioms object_primitive_audit
#print axioms term_syntax_initial
#print axioms checker_nonvacuous
#print axioms bootstrap_initiality

end ActualMathematics.DeltaKernel.Bootstrap

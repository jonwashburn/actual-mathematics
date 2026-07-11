/-
  ActualMathematics/Physicality/DeltaTransport.lean

  The concrete Physicality Translation Theorem for the δ arithmetic language.

  THEOREM:
  * every empty-ledger checker theorem paired with an explicit δ construction
    is true in every Peano realization;
  * the target semantics is satisfaction-equivalent to the canonical source;
  * the source checker equation is carried unchanged;
  * model expansion makes the translation semantically conservative.

  CONDITIONAL:
  Calling the transported truth physical additionally consumes an empirical
  receipt supplied by an external authority.

  OPEN:
  This module provides no empirical authority and proves no physical
  realization exists.

  No project-local axioms. No sorry.
-/

import ActualMathematics.DeltaKernel.BootstrapRealizations
import ActualMathematics.Physicality.Conservativity
import ActualMathematics.Physicality.Receipts
import ActualMathematics.Rigidity.LedgerTransport

namespace ActualMathematics
namespace Physicality

open DeltaKernel
open DeltaKernel.Bootstrap
open Rigidity

/-- Canonical δ semantics: formulas are read in natural-number environments. -/
def deltaSource : Institution where
  Sentence := DFormula
  Model := Env
  sat := DFormula.sat

/-- One admissible target world: a δ-algebra, proof that it is a Peano
realization, and the source environment used to name quantified witnesses. -/
structure PeanoWorld where
  algebra : DeltaAlgebra
  peano : IsPeanoModel algebra
  env : Env

/-- Transported semantics. The satisfaction relation is the existing `msat`;
it is not supplied by a caller. -/
def deltaTarget : Institution where
  Sentence := DFormula
  Model := PeanoWorld
  sat := fun W φ => msat W.algebra W.env φ

/-- The fixed-signature δ translation. Sentences are unchanged, models reduce
to their natural witness environments, and `msat_iff_sat` supplies both
directions of the satisfaction law. -/
def deltaTranslation : Translation deltaSource deltaTarget where
  sentence := id
  reduct := PeanoWorld.env
  satisfaction := fun W φ => msat_iff_sat W.algebra W.peano φ W.env

/-- The δ translation is literally fixed-signature. -/
theorem delta_sentence_map_identity :
    deltaTranslation.sentence = (id : DFormula → DFormula) :=
  rfl

/-- No two source sentences are identified by the fixed sentence map. -/
theorem delta_sentence_faithful :
    Function.Injective deltaTranslation.sentence :=
  Translation.identity_sentence_faithful

/-- Formula-by-formula satisfaction preservation and reflection. -/
theorem delta_satisfaction_equivalence (W : PeanoWorld) (φ : DFormula) :
    deltaTarget.sat W φ ↔ deltaSource.sat W.env φ :=
  deltaTranslation.satisfaction W φ

/-- Every source environment expands to the canonical natural Peano world. -/
def deltaCanonicalExpansion : ModelExpansion deltaTranslation where
  expand := fun ρ =>
    { algebra := Rigidity.natAlgebra
      peano := Rigidity.natAlgebra_peano
      env := ρ }
  reduct_expand := fun _ => rfl

/-- Target validity reflects to source validity. -/
theorem delta_semantically_conservative :
    SemanticallyConservative deltaTranslation :=
  modelExpansion_implies_conservative deltaTranslation deltaCanonicalExpansion

/-- Source validity and validity in every Peano target are equivalent. -/
theorem delta_validity_iff (φ : DFormula) :
    deltaTarget.Valid φ ↔ deltaSource.Valid φ :=
  validity_iff_of_modelExpansion deltaTranslation deltaCanonicalExpansion φ

/-- Empty-ledger transport for a theorem carrying explicit construction data.
The construction receipt is not erased or reconstructed; the theorem consumes
only its checker certificate. -/
theorem transport_generated_forced (G : GeneratedTheorem) (W : PeanoWorld) :
    deltaTarget.sat W G.certificate.sentence :=
  transport_forced G.certificate.forced W.algebra W.peano W.env

/-- Graded transport for a computed purchase receipt. The target consumes
exactly the source ledger gates and adds none. -/
theorem transport_computed_purchase {Γ : Ctx}
    (C : ComputedPurchaseReceipt Γ) (hG : Gated C.ledger)
    (W : PeanoWorld) (hΓ : CtxSat W.env Γ) :
    deltaTarget.sat W C.sentence :=
  transport_graded C.checked hG W.algebra W.peano W.env hΓ

/-- A transported theorem together with the empirical target receipt and the
literal source checker equation. This is the proof-relevant transport result. -/
structure PhysicalizedTheorem
    (A : EmpiricalAuthority deltaTarget)
    (G : GeneratedTheorem) (W : PeanoWorld) : Prop where
  empirical : Nonempty (EmpiricalReceipt A W)
  targetTruth : deltaTarget.sat W G.certificate.sentence
  checkerReceipt :
    check [] G.certificate.derivation =
      some (G.certificate.sentence, Ledger.empty)

/-- **Physicality Translation Theorem.**

Every empty-ledger theorem paired with an inspectable δ construction transports
into every member of a nonempty empirically receipted Peano family. The target
truth uses the fixed `msat` semantics, and the original checker equation is
retained verbatim. -/
theorem universal_physicality_transport
    {A : EmpiricalAuthority deltaTarget}
    (G : GeneratedTheorem) (F : EmpiricalFamily A) :
    ∀ i : F.Index, PhysicalizedTheorem A G (F.realization i) := by
  intro i
  exact
    { empirical := ⟨F.receipt i⟩
      targetTruth := transport_generated_forced G (F.realization i)
      checkerReceipt := G.certificate.checked }

/-- Nonemptiness is operational: every empirical family yields at least one
physicalized theorem. -/
theorem exists_physicality_transport
    {A : EmpiricalAuthority deltaTarget}
    (G : GeneratedTheorem) (F : EmpiricalFamily A) :
    ∃ i : F.Index, PhysicalizedTheorem A G (F.realization i) :=
  ⟨F.witness, universal_physicality_transport G F F.witness⟩

/-! ## Concrete regression: forced addition commutativity in two realizations -/

/-- The real kernel certificate used as the regression witness. -/
def addCommGenerated : GeneratedTheorem where
  generated := generatedNatObject
  certificate :=
    { derivation := GodelTest.addComm
      sentence := .all (.all GodelTest.commFormula)
      checked := GodelTest.addComm_forced }

/-- Natural-number carrier as an admissible Peano target. -/
def natPeanoWorld (ρ : Env) : PeanoWorld where
  algebra := natDeltaAlgebra
  peano := natDeltaAlgebra_peano
  env := ρ

/-- Independently written `List Unit` carrier as an admissible Peano target. -/
def listPeanoWorld (ρ : Env) : PeanoWorld where
  algebra := listDeltaAlgebra
  peano := listDeltaAlgebra_peano
  env := ρ

/-- Forced addition commutativity transports to both independent Peano
carriers under the generic target semantics. -/
theorem addComm_two_independent_realizations (ρ : Env) :
    deltaTarget.sat (natPeanoWorld ρ) addCommGenerated.certificate.sentence ∧
      deltaTarget.sat (listPeanoWorld ρ) addCommGenerated.certificate.sentence :=
  ⟨transport_generated_forced addCommGenerated (natPeanoWorld ρ),
   transport_generated_forced addCommGenerated (listPeanoWorld ρ)⟩

/-- The same certificate also holds in the independently written direct list
evaluator, rather than only through generic `msat`. -/
theorem addComm_direct_list_realization (ρ : ListEnv) :
    listSat ρ addCommGenerated.certificate.sentence :=
  sound_forced_list GodelTest.addComm_forced ρ

/-! ## Axiom audits -/

#print axioms delta_satisfaction_equivalence
#print axioms delta_semantically_conservative
#print axioms transport_generated_forced
#print axioms transport_computed_purchase
#print axioms universal_physicality_transport
#print axioms addComm_two_independent_realizations
#print axioms addComm_direct_list_realization

end Physicality
end ActualMathematics

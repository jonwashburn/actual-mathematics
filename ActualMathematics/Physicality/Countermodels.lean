/-
  ActualMathematics/Physicality/Countermodels.lean

  Adversarial controls for the Physicality Translation Theorem.

  Each tempting overreach is assigned a named failure:
  * map every sentence to truth: satisfaction reflection fails;
  * empty realization family: the family witness cannot exist;
  * one-point carrier: the Peano laws fail;
  * bare equivalence / EvenNat: carrier equivalence loses inherited operations;
  * countability / Fin n: countability does not supply generation;
  * self-issued token: an authority acceptance proof is still missing;
  * constant-trace PRC embedding: weak embedding does not imply faithfulness.

  No project-local axioms. No sorry.
-/

import ActualMathematics.Physicality.DeltaTransport
import ActualMathematics.PRCDistinctionDichotomy

namespace ActualMathematics
namespace Physicality
namespace Countermodels

open DeltaKernel
open DeltaKernel.Bootstrap
open Rigidity

/-! ## Truth collapse -/

/-- Hostile target semantics: every sentence is declared true. -/
def alwaysTrueTarget : Institution where
  Sentence := DFormula
  Model := Unit
  sat := fun _ _ => True

/-- Mapping into an always-true semantics cannot satisfy the required
preservation-and-reflection equivalence: source falsity is a witness. -/
theorem no_map_everything_to_true :
    ¬ Nonempty (Translation deltaSource alwaysTrueTarget) := by
  rintro ⟨T⟩
  have hFalse : deltaSource.sat (T.reduct ()) DFormula.fls :=
    (T.satisfaction () DFormula.fls).mp trivial
  exact hFalse

/-! ## Empty realization family -/

/-- Every empirical family has an inhabited index type by construction. -/
theorem empirical_family_index_nonempty
    {I : Institution} {A : EmpiricalAuthority I}
    (F : EmpiricalFamily A) :
    Nonempty F.Index :=
  ⟨F.witness⟩

/-- No empirical family can expose `Empty` as its index type. -/
theorem no_empty_empirical_family
    {I : Institution} {A : EmpiricalAuthority I} :
    ¬ ∃ F : EmpiricalFamily A, F.Index = Empty := by
  rintro ⟨F, hEmpty⟩
  have x : Empty := hEmpty ▸ F.witness
  exact nomatch x

/-! ## One-point collapse -/

/-- The concrete singleton algebra is rejected at the `peano` field. -/
theorem one_point_collapse_rejected :
    ¬ IsPeanoModel singletonDeltaAlgebra :=
  singletonDeltaAlgebra_not_peano

/-! ## Bare carrier equivalence and EvenNat -/

abbrev EvenNat := {n : ℕ // Even n}

/-- Even naturals are equivalent to the δ naturals and therefore satisfy the
equivalence-invariant `TowerGen` predicate, but the inherited natural successor
leaves the subtype immediately. Bare equivalence is not construction or
operation provenance. -/
theorem evenNat_exposes_bare_equivalence_overreach :
    Nonempty (ℕ ≃ EvenNat) ∧
      TowerGen EvenNat ∧
      ¬ (∀ n : EvenNat, Even (n.1 + 1)) := by
  refine ⟨⟨natEquivEvenNat⟩,
    towerGen_evenNat, ?_⟩
  intro hClosed
  have hOne := hClosed (⟨0, by simp⟩ : EvenNat)
  change Even 1 at hOne
  rcases hOne with ⟨r, hr⟩
  cases r with
  | zero => simp at hr
  | succ r => omega

/-! ## Countability is not generation -/

/-- `Fin 17` is countable, but countability supplies no tower receipt. -/
theorem fin17_countable_but_not_generated :
    Countable (Fin 17) ∧ ¬ TowerGen (Fin 17) :=
  ⟨by infer_instance, not_towerGen_fin17⟩

/-! ## Self-issued evidence -/

/-- A hostile authority whose evidence tokens are internal strings but whose
acceptance relation rejects every token. -/
def rejectingAuthority : EmpiricalAuthority deltaTarget where
  Evidence := fun _ => SelfIssuedCertificate
  accepts := fun _ _ => False

/-- A self-issued token cannot become an empirical receipt without an
authority acceptance proof. -/
theorem self_issued_certificate_is_not_empirical (W : PeanoWorld) :
    IsEmpty (EmpiricalReceipt rejectingAuthority W) :=
  ⟨fun R => R.accepted⟩

/-- Consequently the rejecting authority admits no empirical realization
family. -/
theorem rejecting_authority_has_no_family :
    ¬ EmpiricallyRealized rejectingAuthority := by
  rintro ⟨F⟩
  exact
    (self_issued_certificate_is_not_empirical (F.realization F.witness)).false
      (F.receipt F.witness)

/-! ## Constant-trace weak embedding -/

/-- A two-token formal system whose expression carrier has only one point. -/
def constantTraceSystem : FormalSystem where
  Token := Bool
  Expr := Unit
  distinguishes := fun a b => a ≠ b
  exprExtends := fun _ _ => True
  endpointToken := fun e =>
    match e.side with
    | Side.left => false
    | Side.right => true
  traceExpr := fun _ => ()
  traceExpr_extends := by
    intro _ _ _
    trivial

theorem constantTraceSystem_expressive :
    constantTraceSystem.Expressive := by
  change false ≠ true
  decide

/-- The same weak embedding shape used by the generic distinction dichotomy:
the endpoints are distinguished while every trace is collapsed. -/
def constantTraceEmbedding : PRCEmbeddingInto constantTraceSystem :=
  PRCEmbeddingInto.ofExpressive constantTraceSystem constantTraceSystem_expressive

/-- Faithfulness requires the trace map itself to be injective. -/
def TraceFaithful {F : FormalSystem} (E : PRCEmbeddingInto F) : Prop :=
  Function.Injective E.traceMap

/-- A weak PRC embedding exists, but it is not faithful. This is why
`PRCDistinctionDichotomy` alone cannot discharge the translation contract. -/
theorem constant_trace_embedding_not_faithful :
    Nonempty (PRCEmbeddingInto constantTraceSystem) ∧
      ¬ TraceFaithful constantTraceEmbedding := by
  constructor
  · exact ⟨constantTraceEmbedding⟩
  · intro hInjective
    have hEq : Trace.empty = Trace.step Trace.empty :=
      hInjective rfl
    have hNe : Trace.empty ≠ Trace.step Trace.empty := by
      decide
    exact hNe hEq

/-! ## Axiom audits -/

#print axioms no_map_everything_to_true
#print axioms no_empty_empirical_family
#print axioms one_point_collapse_rejected
#print axioms evenNat_exposes_bare_equivalence_overreach
#print axioms fin17_countable_but_not_generated
#print axioms self_issued_certificate_is_not_empirical
#print axioms rejecting_authority_has_no_family
#print axioms constant_trace_embedding_not_faithful

end Countermodels
end Physicality
end ActualMathematics

/-
  ActualMathematics/PRCSyntacticArithmeticQ.lean

  Syntactic (proof-theoretic) parse of Robinson arithmetic Q into the δ
  `FormalSystem` interface, under the frozen prereg
  δ/plans/Delta_Inevitability_Corpus_Campaign_Prereg_20260717.html.

  The prior arithmetic leg (`PRCInevitabilityInstances.peanoSystem`) discriminated
  SEMANTICALLY: 0 ≠ 1 in the standard model ℕ. This module upgrades the arithmetic
  parse to a SYNTACTIC one, in the deep-embedding style of `DeltaKernel/Syntax.lean`
  and `DeltaKernel/Check.lean` (the pattern is imitated, not imported):

  * The language of Q is deep-embedded: `QTerm` (closed terms over {0, S}) and
    `QFormula` (equality atoms and negation).
  * Derivations are POSITIVE DATA: `QDeriv : QFormula → Type` is an inductive
    family whose constructors are the standard Q axioms and equality rules:
    `ax_succ_ne_zero` (Q1, the axiom S t ≠ 0, at closed terms), `ax_succ_inj`
    (Q2, injectivity of S), `eq_refl`, `eq_symm`, `eq_trans`, `eq_congr_succ`,
    and `neg_symm` (the modus-tollens composite of `eq_symm`; derivable in any
    Hilbert calculus for Q with the propositional axioms, taken here as a
    primitive rule so the fragment needs no propositional connectives).
  * `deriv_one_ne_zero` is an EXPLICIT derivation term (one axiom instance, not a
    tactic-produced proof) deriving S 0 ≠ 0 inside Q.
  * FRAGMENT SOUNDNESS is proved: `QTerm.eval` / `QFormula.holds` give the
    standard interpretation in ℕ and `qderiv_sound` shows every derivable formula
    holds there, by induction on the derivation. `model_separates` extracts
    (1 : ℕ) ≠ 0 through `holds` from the explicit derivation.
  * NON-VACUITY GUARD: `qderiv_no_eq_one_zero` shows the calculus does NOT derive
    S 0 = 0 (via soundness: such a derivation would force 1 = 0 in ℕ). So the
    discrimination below is not a relabelled Boolean: the derivability relation
    genuinely separates the derivable from the underivable. This is the honest
    bounded substitute for a consistency proof.

  The parse: `qSyntacticSystem` has tokens the closed Q terms, and
  `distinguishes a b := Nonempty (QDeriv (neg (eq a b)))`, i.e. two tokens are
  distinguished exactly when Q DERIVES their inequation. The endpoints are the
  numerals 0 and S 0; expressivity is witnessed by the explicit derivation term.
  The system realizes the δ core (`qSyntacticSystem_embeds_delta`) and falls on
  the δ side of the distinction dichotomy (`qSyntacticSystem_not_degenerate`).

  HONEST BOUNDARY. Only the fragment of Q needed for the endpoint discrimination
  is embedded: closed terms over {0, S} (no variables, no + or ·), formulas built
  from equality and negation, and the axioms Q1, Q2 plus equality rules listed
  above. Full Q (Q3-Q7, quantifiers, open terms) is not claimed. Soundness is
  proved for exactly this fragment; the non-vacuity guard is soundness-based and
  is weaker than a syntactic consistency proof for full Q.

  No project-local axioms. No sorry.
-/

import ActualMathematics.PRCDistinctionDichotomy

namespace ActualMathematics
namespace SyntacticArithmeticQ

open FormalSystem

/-! ### The language of Q (closed-term fragment) -/

/-- Closed terms of Q over the signature {0, S}. Closed terms suffice for the
endpoint discrimination; open terms, + and · are outside this fragment. -/
inductive QTerm : Type where
  | zero : QTerm
  | succ : QTerm → QTerm
deriving Repr, DecidableEq

/-- Formulas of the embedded fragment: equality atoms and negation. -/
inductive QFormula : Type where
  | eq : QTerm → QTerm → QFormula
  | neg : QFormula → QFormula
deriving Repr, DecidableEq

/-! ### Hilbert-style derivations as positive data -/

/-- Derivations in the Q fragment, as an inductive family of DATA (a derivation
is a tree, not a `Prop`). Constructors are the standard axioms and rules:

* `ax_succ_ne_zero` is Q1 (`S t ≠ 0`), instantiated at closed terms;
* `ax_succ_inj` is Q2 (injectivity of `S`), as a rule;
* `eq_refl`, `eq_symm`, `eq_trans`, `eq_congr_succ` are the equality rules;
* `neg_symm` is the contrapositive of `eq_symm` (from ⊢ ¬(s = t) infer
  ⊢ ¬(t = s)); in a full Hilbert calculus for Q it is derivable from `eq_symm`
  and modus tollens, and it is taken as a primitive rule here so the fragment
  needs no propositional connectives beyond negation. -/
inductive QDeriv : QFormula → Type where
  /-- Q1 at closed terms: `⊢ ¬(S t = 0)`. -/
  | ax_succ_ne_zero (t : QTerm) : QDeriv (.neg (.eq (.succ t) .zero))
  /-- Q2 as a rule: from `⊢ S s = S t` infer `⊢ s = t`. -/
  | ax_succ_inj {s t : QTerm} : QDeriv (.eq (.succ s) (.succ t)) → QDeriv (.eq s t)
  /-- `⊢ t = t`. -/
  | eq_refl (t : QTerm) : QDeriv (.eq t t)
  /-- From `⊢ s = t` infer `⊢ t = s`. -/
  | eq_symm {s t : QTerm} : QDeriv (.eq s t) → QDeriv (.eq t s)
  /-- From `⊢ s = t` and `⊢ t = u` infer `⊢ s = u`. -/
  | eq_trans {s t u : QTerm} :
      QDeriv (.eq s t) → QDeriv (.eq t u) → QDeriv (.eq s u)
  /-- Congruence of `S`: from `⊢ s = t` infer `⊢ S s = S t`. -/
  | eq_congr_succ {s t : QTerm} : QDeriv (.eq s t) → QDeriv (.eq (.succ s) (.succ t))
  /-- Contrapositive of `eq_symm`: from `⊢ ¬(s = t)` infer `⊢ ¬(t = s)`. -/
  | neg_symm {s t : QTerm} : QDeriv (.neg (.eq s t)) → QDeriv (.neg (.eq t s))

/-- **The explicit derivation term for S 0 ≠ 0.** One instance of Q1; a closed
term of the derivation family, not a tactic-produced opaque proof. -/
def deriv_one_ne_zero : QDeriv (.neg (.eq (.succ .zero) .zero)) :=
  QDeriv.ax_succ_ne_zero .zero

/-- The endpoint-oriented companion: `⊢ ¬(0 = S 0)`, by `neg_symm` on the Q1
instance. Also an explicit derivation term. -/
def deriv_zero_ne_one : QDeriv (.neg (.eq .zero (.succ .zero))) :=
  QDeriv.neg_symm deriv_one_ne_zero

/-! ### Fragment soundness in the standard model ℕ -/

/-- Standard interpretation of closed Q terms in ℕ. -/
def QTerm.eval : QTerm → ℕ
  | .zero => 0
  | .succ t => Nat.succ t.eval

/-- Standard interpretation of fragment formulas in ℕ. -/
def QFormula.holds : QFormula → Prop
  | .eq s t => s.eval = t.eval
  | .neg φ => ¬ φ.holds

/-- **Fragment soundness.** Every formula derivable in the Q fragment holds in
the standard model ℕ. Induction on the derivation tree; each axiom and rule maps
to the corresponding fact about ℕ. -/
theorem qderiv_sound : ∀ {φ : QFormula}, QDeriv φ → φ.holds
  | _, .ax_succ_ne_zero t => Nat.succ_ne_zero t.eval
  | _, .ax_succ_inj d => Nat.succ.inj (qderiv_sound d)
  | _, .eq_refl _ => rfl
  | _, .eq_symm d => (qderiv_sound d).symm
  | _, .eq_trans d₁ d₂ => (qderiv_sound d₁).trans (qderiv_sound d₂)
  | _, .eq_congr_succ d => congrArg Nat.succ (qderiv_sound d)
  | _, .neg_symm d => fun h => qderiv_sound d h.symm

/-- **Model separation, wired through `holds`.** The soundness image of the
explicit derivation `deriv_one_ne_zero` is exactly (1 : ℕ) ≠ 0. -/
theorem model_separates : (1 : ℕ) ≠ 0 :=
  fun h => qderiv_sound deriv_one_ne_zero h

/-- **Non-vacuity guard.** The calculus does NOT derive S 0 = 0: any such
derivation would be sound, forcing 1 = 0 in ℕ. So the derivability relation
genuinely separates formulas; the discrimination below is not a relabelled
Boolean. Honest bounded substitute for consistency of the fragment. -/
theorem qderiv_no_eq_one_zero : QDeriv (.eq (.succ .zero) .zero) → False :=
  fun d => Nat.succ_ne_zero 0 (qderiv_sound d)

/-! ### The parse into the FormalSystem interface -/

/-- Robinson arithmetic Q (the embedded fragment) parsed SYNTACTICALLY into the
`FormalSystem` interface. Tokens are the closed Q terms; two tokens are
distinguished exactly when Q DERIVES their inequation (a positive derivation
tree exists), not merely when they differ in a model. The endpoints are the
numerals 0 and S 0; the expression order is the derivation-length order. -/
def qSyntacticSystem : FormalSystem where
  Token := QTerm
  Expr := ℕ
  distinguishes := fun a b => Nonempty (QDeriv (.neg (.eq a b)))
  exprExtends := fun m n => m ≤ n
  endpointToken := fun e =>
    match e.side with
    | Side.left => QTerm.zero
    | Side.right => QTerm.succ QTerm.zero
  traceExpr := Trace.length
  traceExpr_extends := fun h => InevitabilityInstances.length_le_of_extends h

/-- `qSyntacticSystem` distinguishes its endpoints: Q derives ¬(0 = S 0), by the
explicit derivation term (Q1 instance plus `neg_symm`). -/
theorem qSyntacticSystem_expressive : qSyntacticSystem.Expressive :=
  ⟨deriv_zero_ne_one⟩

/-- **Syntactic Q contains the δ core.** -/
theorem qSyntacticSystem_embeds_delta : Nonempty (PRCEmbeddingInto qSyntacticSystem) :=
  FormalSystemEmbeddingTarget_proved qSyntacticSystem qSyntacticSystem_expressive

theorem qSyntacticSystem_exprReflexive :
    DistinctionDichotomy.ExprReflexive qSyntacticSystem :=
  fun n => Nat.le_refl n

/-- Syntactic Q falls on the δ side of the distinction dichotomy: it is
non-degenerate, hence realizes δ. -/
theorem qSyntacticSystem_not_degenerate :
    ¬ DistinctionDichotomy.Degenerate qSyntacticSystem :=
  DistinctionDichotomy.not_degenerate_of_realizesDelta
    qSyntacticSystem qSyntacticSystem_embeds_delta

/-- **The syntactic parse, packaged.** Robinson arithmetic Q (embedded fragment):
(i) is sound for the standard model ℕ, (ii) derives S 0 ≠ 0 by an explicit
derivation term, (iii) separates 1 from 0 in the model through soundness,
(iv) does NOT derive S 0 = 0 (non-vacuity guard), and (v) realizes the δ core. -/
theorem syntactic_q_realizes_delta :
    (∀ φ : QFormula, QDeriv φ → φ.holds)
      ∧ Nonempty (QDeriv (.neg (.eq (.succ .zero) .zero)))
      ∧ ((1 : ℕ) ≠ 0)
      ∧ (QDeriv (.eq (.succ .zero) .zero) → False)
      ∧ Nonempty (PRCEmbeddingInto qSyntacticSystem) :=
  ⟨fun _ d => qderiv_sound d, ⟨deriv_one_ne_zero⟩, model_separates,
    qderiv_no_eq_one_zero, qSyntacticSystem_embeds_delta⟩

end SyntacticArithmeticQ
end ActualMathematics

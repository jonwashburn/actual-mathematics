/-
  ActualMathematics/PRCSyntacticFoundations.lean

  Capstone of the 2026-07-17 corpus campaign: the SYNTACTIC upgrade of the
  inevitability corpus (prereg: δ/plans/Delta_Inevitability_Corpus_Campaign_
  Prereg_20260717.html).

  The prior corpus parses (`PRCFoundationsParsed`) were semantic: ZFC was
  distinguished by extensional inequality in Mathlib's `ZFSet` model, type theory
  by Lean's own `Bool`. The panel review of 2026-07-17 identified the gap: since
  the embedding theorem is near interface-projection, all content must live in the
  FAITHFULNESS of the parses, and a semantic parse leaves the "you relabeled
  booleans" objection open.

  This capstone collects the four syntactic parses that close it. In each, the
  foundation's language and deduction system are deep-embedded, tokens are closed
  terms of that language, derivations are positive data (an inductive `Type`, not
  a bare `Prop`), and the δ distinction is DERIVED inside the foundation's own
  calculus by an explicit finite derivation term:

  * ROBINSON ARITHMETIC Q (`PRCSyntacticArithmeticQ`): the calculus derives
    S 0 ≠ 0 from the Q1 axiom; sound for ℕ; does not derive S 0 = 0.
  * ZF SET THEORY (`PRCSyntacticZF`): in the standard definitional extension by
    e (empty set) and s (its singleton), the calculus derives ¬(e = s) from the
    Empty and Singleton defining axioms plus the equality rules; sound for
    `ZFSet`; does not derive e = s.
  * TYPE THEORY (`PRCSyntacticSTLC`): a deep-embedded simply-typed lambda
    calculus with Bool whose own judgmental conversion provably cannot identify
    tt and ff (deterministic weak-head reduction, values normal, no-confusion);
    canonicity for closed well-typed normal booleans; evaluation separates the
    endpoints.
  * HOL (`PRCSyntacticHOL`): a Gordon-style propositional HOL kernel (TRUTH,
    ASSUME, REFL, EQ_MP, MP, DISCH, NOT_INTRO, NOT_ELIM) derives ⊢ ¬(T = F) as a
    five-node proof tree; sound for the standard model; does not derive T = F.

  Each parse carries the four-part fidelity bar frozen in the prereg:
  rule-faithful embedding, constructive Expressive (an explicit derivation term),
  fragment soundness into a standard model, and the model-separation witness that
  makes the parse non-vacuous (if the calculus derived the endpoint equality it
  would be unsound; this is the honest substitute for a consistency assumption).

  SCOPED HEADLINE (frozen wording, per the adversarial review). What is proved: a
  dichotomy for the fixed formal-system interface (any instance with reflexive
  expression-extension is degenerate or realizes the δ core), instantiated by
  deep syntactic embeddings of Q, ZF, an MLTT fragment, and HOL, where tokens are
  closed terms and distinction is derivability of inequality in the foundation's
  own calculus. It is NOT the claim that every conceivable foundation under every
  encoding contains the core independent of parse choices.

  No project-local axioms. No sorry.
-/

import ActualMathematics.PRCSyntacticArithmeticQ
import ActualMathematics.PRCSyntacticZF
import ActualMathematics.PRCSyntacticSTLC
import ActualMathematics.PRCSyntacticHOL

namespace ActualMathematics
namespace SyntacticFoundations

/-- **The four foundations, syntactically parsed, each realize the δ core.**
Robinson arithmetic, ZF set theory, the STLC type-theory fragment, and HOL, each
deep-embedded with its own deduction system and parsed into the `FormalSystem`
interface with distinction = derivability of the endpoint inequality in the
foundation's own calculus, each admit a PRC embedding. -/
theorem four_syntactic_foundations_realize_delta :
    Nonempty (PRCEmbeddingInto SyntacticArithmeticQ.qSyntacticSystem)
      ∧ Nonempty (PRCEmbeddingInto SyntacticZFParse.zfSyntacticSystem)
      ∧ Nonempty (PRCEmbeddingInto SyntacticSTLC.stlcSystem)
      ∧ Nonempty (PRCEmbeddingInto SyntacticHOL.holSystem) :=
  ⟨SyntacticArithmeticQ.qSyntacticSystem_embeds_delta,
    SyntacticZFParse.zfSyntacticSystem_embeds_delta,
    SyntacticSTLC.stlcSystem_embeds_delta,
    SyntacticHOL.holSystem_embeds_delta⟩

/-- The four syntactic systems all fall on the δ side of the distinction
dichotomy: none is degenerate. -/
theorem four_syntactic_foundations_not_degenerate :
    ¬ DistinctionDichotomy.Degenerate SyntacticArithmeticQ.qSyntacticSystem
      ∧ ¬ DistinctionDichotomy.Degenerate SyntacticZFParse.zfSyntacticSystem
      ∧ ¬ DistinctionDichotomy.Degenerate SyntacticSTLC.stlcSystem
      ∧ ¬ DistinctionDichotomy.Degenerate SyntacticHOL.holSystem :=
  ⟨SyntacticArithmeticQ.qSyntacticSystem_not_degenerate,
    SyntacticZFParse.zfSyntacticSystem_not_degenerate,
    SyntacticSTLC.stlcSystem_not_degenerate,
    SyntacticHOL.holSystem_not_degenerate⟩

/-- **Each foundation derives the δ distinction in its own calculus.** The
Expressive witness of each parse is an explicit finite derivation object of the
foundation's own deduction system (for the type-theory fragment, the constructive
refutation of convertibility, which is the type theory's own verdict of
distinctness for canonical forms). Nothing is assumed: each component is
inhabited by a concrete derivation term. -/
theorem four_foundations_derive_distinction :
    Nonempty (SyntacticArithmeticQ.QDeriv (.neg (.eq (.succ .zero) .zero)))
      ∧ Nonempty (SyntacticZFParse.ZFDeriv [] (.neg (.eq .const_e .const_s)))
      ∧ (SyntacticSTLC.Conv SyntacticSTLC.Tm.tt SyntacticSTLC.Tm.ff → False)
      ∧ Nonempty (SyntacticHOL.HOLThm
          (SyntacticHOL.HOLTerm.not
            (SyntacticHOL.HOLTerm.eq SyntacticHOL.HOLTerm.trueC SyntacticHOL.HOLTerm.falseC))) :=
  ⟨⟨SyntacticArithmeticQ.deriv_one_ne_zero⟩,
    ⟨SyntacticZFParse.deriv_e_ne_s⟩,
    SyntacticSTLC.tt_ff_not_conv,
    ⟨SyntacticHOL.deriv_T_ne_F⟩⟩

/-- **Non-vacuity, jointly.** None of the four calculi derives the endpoint
EQUALITY: each is sound for a standard model that separates the endpoints, so a
derivation of the equality would contradict soundness. This is the pre-registered
guard against the relabeled-booleans objection, and the honest substitute for a
consistency assumption (derivations are positive finite objects; no Con(T) is
assumed anywhere). -/
theorem four_foundations_non_vacuous :
    (SyntacticArithmeticQ.QDeriv (.eq (.succ .zero) .zero) → False)
      ∧ (SyntacticZFParse.ZFDeriv [] (.eq .const_e .const_s) → False)
      ∧ (SyntacticSTLC.evalNF SyntacticSTLC.Tm.tt ≠ SyntacticSTLC.evalNF SyntacticSTLC.Tm.ff)
      ∧ (SyntacticHOL.HOLThm
          (SyntacticHOL.HOLTerm.eq SyntacticHOL.HOLTerm.trueC SyntacticHOL.HOLTerm.falseC) → False) :=
  ⟨SyntacticArithmeticQ.qderiv_no_eq_one_zero,
    SyntacticZFParse.zfderiv_no_eq,
    SyntacticSTLC.model_separates,
    SyntacticHOL.holderiv_no_eq⟩

/-- **The corpus campaign capstone.** The four syntactic parses, jointly: each
foundation derives the δ distinction inside its own deep-embedded calculus, each
parse is non-vacuous (sound for a separating model), and each realizes the δ
core, falling on the δ side of the dichotomy. Together with the generic dichotomy
(`PRCDistinctionDichotomy.distinction_not_optional`), this is the scoped
inevitability claim: the named foundations, parsed at proof-theoretic
faithfulness, each contain the δ core through their own deductive machinery. -/
theorem syntactic_corpus_capstone :
    (Nonempty (SyntacticArithmeticQ.QDeriv (.neg (.eq (.succ .zero) .zero)))
        ∧ Nonempty (SyntacticZFParse.ZFDeriv [] (.neg (.eq .const_e .const_s)))
        ∧ (SyntacticSTLC.Conv SyntacticSTLC.Tm.tt SyntacticSTLC.Tm.ff → False)
        ∧ Nonempty (SyntacticHOL.HOLThm
            (SyntacticHOL.HOLTerm.not
              (SyntacticHOL.HOLTerm.eq SyntacticHOL.HOLTerm.trueC SyntacticHOL.HOLTerm.falseC))))
      ∧ (Nonempty (PRCEmbeddingInto SyntacticArithmeticQ.qSyntacticSystem)
          ∧ Nonempty (PRCEmbeddingInto SyntacticZFParse.zfSyntacticSystem)
          ∧ Nonempty (PRCEmbeddingInto SyntacticSTLC.stlcSystem)
          ∧ Nonempty (PRCEmbeddingInto SyntacticHOL.holSystem))
      ∧ (¬ DistinctionDichotomy.Degenerate SyntacticArithmeticQ.qSyntacticSystem
          ∧ ¬ DistinctionDichotomy.Degenerate SyntacticZFParse.zfSyntacticSystem
          ∧ ¬ DistinctionDichotomy.Degenerate SyntacticSTLC.stlcSystem
          ∧ ¬ DistinctionDichotomy.Degenerate SyntacticHOL.holSystem) :=
  ⟨four_foundations_derive_distinction,
    four_syntactic_foundations_realize_delta,
    four_syntactic_foundations_not_degenerate⟩

end SyntacticFoundations
end ActualMathematics

/-
  ActualMathematics/Physicality/Conservativity.lean

  Semantic conservativity for institution translations.

  A translation is conservative when validity of the translated sentence in
  every target model reflects to validity in every source model. A model
  expansion proves conservativity by supplying, for each source model, one
  target model whose reduct is exactly the source.

  No project-local axioms. No sorry.
-/

import ActualMathematics.Physicality.Institution

namespace ActualMathematics
namespace Physicality

universe uSrcSentence uSrcModel uTgtSentence uTgtModel

/-- Target validity reflects to source validity. -/
def SemanticallyConservative
    {Src : Institution.{uSrcSentence, uSrcModel}}
    {Tgt : Institution.{uTgtSentence, uTgtModel}}
    (T : Translation Src Tgt) : Prop :=
  ∀ φ : Src.Sentence,
    Tgt.Valid (T.sentence φ) → Src.Valid φ

/-- Every source model has a target expansion whose reduct is the original
source model. -/
structure ModelExpansion
    {Src : Institution.{uSrcSentence, uSrcModel}}
    {Tgt : Institution.{uTgtSentence, uTgtModel}}
    (T : Translation Src Tgt) where
  expand : Src.Model → Tgt.Model
  reduct_expand : ∀ M : Src.Model, T.reduct (expand M) = M

/-- Model expansion implies semantic conservativity. -/
theorem modelExpansion_implies_conservative
    {Src : Institution.{uSrcSentence, uSrcModel}}
    {Tgt : Institution.{uTgtSentence, uTgtModel}}
    (T : Translation Src Tgt)
    (E : ModelExpansion T) :
    SemanticallyConservative T := by
  intro φ hTarget M
  have hExpanded : Tgt.sat (E.expand M) (T.sentence φ) :=
    hTarget (E.expand M)
  have hReduced : Src.sat (T.reduct (E.expand M)) φ :=
    T.reflect_at (E.expand M) φ hExpanded
  rw [E.reduct_expand M] at hReduced
  exact hReduced

/-- Under model expansion, source validity and translated target validity are
equivalent. -/
theorem validity_iff_of_modelExpansion
    {Src : Institution.{uSrcSentence, uSrcModel}}
    {Tgt : Institution.{uTgtSentence, uTgtModel}}
    (T : Translation Src Tgt)
    (E : ModelExpansion T) (φ : Src.Sentence) :
    Tgt.Valid (T.sentence φ) ↔ Src.Valid φ := by
  constructor
  · exact modelExpansion_implies_conservative T E φ
  · exact T.transport_valid φ

end Physicality
end ActualMathematics

/-
  ActualMathematics/Physicality/Institution.lean

  Minimal institution-style semantics for the Physicality Translation Theorem.

  The load-bearing field is `satisfaction`: target truth is equivalent to source
  truth in the reduced model. Preservation alone would admit a translator that
  sends every sentence to `True`; the reverse implication blocks that collapse.

  No project-local axioms. No sorry.
-/

import Mathlib

namespace ActualMathematics
namespace Physicality

universe uSentence uModel

/-- A fixed mathematical language together with its models and satisfaction
relation. Sentence and model universes are independent because a model may
package a `Type`-valued carrier. -/
structure Institution where
  Sentence : Type uSentence
  Model : Type uModel
  sat : Model → Sentence → Prop

namespace Institution

/-- A sentence is valid when every model of the institution satisfies it. -/
def Valid (I : Institution) (φ : I.Sentence) : Prop :=
  ∀ M : I.Model, I.sat M φ

end Institution

universe uSrcSentence uSrcModel uTgtSentence uTgtModel

/-- A sentence translation and model reduct that preserve and reflect
satisfaction. The equivalence is the semantic anti-vacuity gate. -/
structure Translation
    (Src : Institution.{uSrcSentence, uSrcModel})
    (Tgt : Institution.{uTgtSentence, uTgtModel}) where
  sentence : Src.Sentence → Tgt.Sentence
  reduct : Tgt.Model → Src.Model
  satisfaction :
    ∀ (M : Tgt.Model) (φ : Src.Sentence),
      Tgt.sat M (sentence φ) ↔ Src.sat (reduct M) φ

namespace Translation

/-- Source truth transports to target truth at a particular target model. -/
theorem preserve_at
    {Src : Institution.{uSrcSentence, uSrcModel}}
    {Tgt : Institution.{uTgtSentence, uTgtModel}}
    (T : Translation Src Tgt)
    (M : Tgt.Model) (φ : Src.Sentence)
    (h : Src.sat (T.reduct M) φ) :
    Tgt.sat M (T.sentence φ) :=
  (T.satisfaction M φ).mpr h

/-- Target truth reflects to source truth in the reduced model. -/
theorem reflect_at
    {Src : Institution.{uSrcSentence, uSrcModel}}
    {Tgt : Institution.{uTgtSentence, uTgtModel}}
    (T : Translation Src Tgt)
    (M : Tgt.Model) (φ : Src.Sentence)
    (h : Tgt.sat M (T.sentence φ)) :
    Src.sat (T.reduct M) φ :=
  (T.satisfaction M φ).mp h

/-- Every source-valid sentence is valid after translation. -/
theorem transport_valid
    {Src : Institution.{uSrcSentence, uSrcModel}}
    {Tgt : Institution.{uTgtSentence, uTgtModel}}
    (T : Translation Src Tgt)
    (φ : Src.Sentence) (h : Src.Valid φ) :
    Tgt.Valid (T.sentence φ) := by
  intro M
  exact T.preserve_at M φ (h (T.reduct M))

/-- The identity sentence map is injective. Concrete fixed-signature
translations cite this rather than adding faithfulness as an assumption. -/
theorem identity_sentence_faithful {S : Type} :
    Function.Injective (id : S → S) :=
  fun _ _ h => h

end Translation

end Physicality
end ActualMathematics

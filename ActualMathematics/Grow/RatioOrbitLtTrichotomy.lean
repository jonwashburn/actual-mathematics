import ActualMathematics.IntegerRational
import ActualMathematics.IntegerOrder
import ActualMathematics.Grow.RatioOrbitLeReflTotal

namespace ActualMathematics.PRCGrow.RatioOrbitLtTrichotomy

open ActualMathematics
open ActualMathematics.PRCGrow.RatioOrbitLeReflTotal

def ltQ (p q : RatioOrbit) : Prop := leQ p q ∧ ¬ RatioOrbit.crossEq p q

theorem ltQ_irrefl (p : RatioOrbit) : ¬ ltQ p p := by
  intro h
  exact h.2 (RatioOrbit.crossEq_refl p)

instance crossEq_decidable (a b : RatioOrbit) : Decidable (RatioOrbit.crossEq a b) := by
  unfold RatioOrbit.crossEq
  infer_instance

theorem ltQ_trichotomy (p q : RatioOrbit) :
    ltQ p q ∨ RatioOrbit.crossEq p q ∨ ltQ q p := by
  cases' leQ_total p q with hpq hqp
  · by_cases heq : RatioOrbit.crossEq p q
    · exact Or.inr (Or.inl heq)
    · exact Or.inl ⟨hpq, heq⟩
  · by_cases heq : RatioOrbit.crossEq q p
    · exact Or.inr (Or.inl (RatioOrbit.crossEq_symm heq))
    · exact Or.inr (Or.inr ⟨hqp, heq⟩)

end ActualMathematics.PRCGrow.RatioOrbitLtTrichotomy

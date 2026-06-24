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

theorem ltQ_trichotomy (p q : RatioOrbit) :
    ltQ p q ∨ RatioOrbit.crossEq p q ∨ ltQ q p := by
  have hpq := RatioOrbit.crossEq_iff_toIntCross p q
  have hqp := RatioOrbit.crossEq_iff_toIntCross q p
  cases Int.decEq (p.num.toInt * (q.den.toNat : ℤ)) (q.num.toInt * (p.den.toNat : ℤ)) with
  | isTrue heq =>
      exact Or.inr (Or.inl (hpq.mpr heq))
  | isFalse hne =>
      rcases leQ_total p q with hle | hle
      · refine Or.inl ⟨hle, ?_⟩
        intro hc
        exact hne (hpq.mp hc)
      · refine Or.inr (Or.inr ⟨hle, ?_⟩)
        intro hc
        exact hne ((hqp.mp hc).symm)

end ActualMathematics.PRCGrow.RatioOrbitLtTrichotomy

import ActualMathematics.DeltaKernel.BootstrapRealizations
import ActualMathematics.DeltaKernel.BootstrapHostInvariance

/-!
# Bootstrap F4: choice-free second host receipt

The List Unit Peano realization and the Nat/List host-invariance package
are already choice-free (`0f4cfc8`). This module pins that receipt into the
forcing ladder so the capstone cannot silently reintroduce Classical.choice.
-/

namespace ActualMathematics.DeltaKernel.Bootstrap

open ActualMathematics.Rigidity

/-- F4 package: independent second host with printed choice-free basis. -/
structure BootstrapChoiceFreeHostSpec : Prop where
  independent : IndependentRealizationSpec
  host_validity : ∀ φ : DFormula, NatValid φ ↔ ListValid φ
  list_peano : IsPeanoModel listDeltaAlgebra
  nat_peano : IsPeanoModel natDeltaAlgebra
  hostile_nonmodel : ¬ IsPeanoModel singletonDeltaAlgebra

theorem bootstrap_choice_free_host : BootstrapChoiceFreeHostSpec where
  independent := independent_realizations
  host_validity := host_validity_iff
  list_peano := listDeltaAlgebra_peano
  nat_peano := natDeltaAlgebra_peano
  hostile_nonmodel := singletonDeltaAlgebra_not_peano

/-- Alias documenting the F4 closure date and intended axiom footprint. -/
theorem f4_independent_realizations_choice_free :
    IndependentRealizationSpec :=
  independent_realizations

#print axioms listDeltaAlgebra_peano
#print axioms independent_realizations
#print axioms bootstrap_choice_free_host
#print axioms f4_independent_realizations_choice_free

end ActualMathematics.DeltaKernel.Bootstrap

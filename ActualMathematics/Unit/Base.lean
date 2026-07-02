import Mathlib
import ActualMathematics.RationalField
import ActualMathematics.IntegerOrder

/-!
# The cocompletion-unit milestone: a named countable-choice carrier

This is the scaffold for the FIRST milestone of the new crown (the Forced ⊣
Classical adjunction): construct the reflection unit `η : ℚδ → ℝδ` (Cauchy plus
modulus) and confirm by `#print axioms` that the construction's choice cost is
EXACTLY the named countable choice `AC_omega` the demarcation predicts, and never
smuggled full `Classical.choice`.

The loop that grows the unit (carrier `RealDelta`, the map `η`, the unit laws, and
the completeness/universal-property statement) lives in `glm/delta_unit_loop.py`.
Its acceptance gate permits this one named axiom (matched by the final component
`AC_omega`) and forbids `Classical.choice`/`Classical.em`/`sorryAx`.

`ℚδ` is `PRCRat` (the quotient of `RatioOrbit` by cross-multiplication), with field
operations already in scope from `RationalField` / `IntegerRational`. The δ-native
real `ℝδ` is to be built as Cauchy sequences of `PRCRat` carrying an explicit
modulus of convergence (the modulus is what keeps the construction choice-free; the
only place a choice may enter is aligning moduli across a sequence of reals, and
there it must be exactly `AC_omega`).
-/

universe u

namespace ActualMathematics
namespace Unit

/-- **Named countable choice (AC_ω).**

This is the EXACT axiom the demarcation predicts the classical completion of `ℚδ`
costs: dependent choice over a countable index. It is strictly weaker than
`Classical.choice` (it ranges only over an `ℕ`-indexed family and requires the
witness-existence hypothesis), and it is the ONLY non-`{propext, Quot.sound}` axiom
the completion-unit gate permits.

The milestone is precisely the test that the modulus completion `η : ℚδ → ℝδ` can
be built so that:
* the carrier `ℝδ`, the map `η`, and the unit laws (`η 0 = 0`, `η 1 = 1`,
  `η (a+b) = η a + η b`, `η (a*b) = η a * η b`, `η` injective) are CHOICE-FREE,
  i.e. `#print axioms` ⊆ `{propext, Quot.sound}`; and
* the completeness / universal property of the completion costs at most this named
  `AC_omega`, i.e. `#print axioms` ⊆ `{propext, Quot.sound, AC_omega}`,
never `Classical.choice`. -/
axiom AC_omega {β : ℕ → Sort u} (R : ∀ n, β n → Prop) :
    (∀ n, ∃ x, R n x) → ∃ f : ∀ n, β n, ∀ n, R n (f n)

end Unit
end ActualMathematics

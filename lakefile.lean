import Lake
open Lake DSL

package actualMathematics where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

/-- The forced-mathematics framework: distinction → ℕ → ℤ → ℚ → constructive reals,
    factorization, the recognition cost (`ActualMathematics.Cost`, with the uniqueness
    theorem `law_of_logic_forces_jcost`), and the forced/posited demarcation.
    Choice-free where tagged (`#print axioms` ⊆ {propext, Quot.sound}). -/
@[default_target]
lean_lib ActualMathematics where
  globs := #[.andSubmodules `ActualMathematics]

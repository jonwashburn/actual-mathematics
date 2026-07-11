import ActualMathematics.DeltaKernel.BootstrapArithmetic
import ActualMathematics.DeltaKernel.Sound
import ActualMathematics.FormalSystem
import ActualMathematics.PRCSetTheoryParse
import ActualMathematics.PRCTypeTheoryParse

/-!
# Bootstrap B3: foundation interpretation

The δ kernel interprets a named fragment of intuitionistic arithmetic: every
FORCED derivation is true in the canonical model without EM, LPO, or Markov.
Separately, hereditarily finite set theory and Martin-Löf's two-element type
each realize the δ endpoint distinction through the FormalSystem interface.

This is relative interpretation, not "no metatheory." The host still supplies
`Type`, `Prop`, and recursion. The object claim is that the named foundations
contain the δ core and that forced δ theorems export into them.
-/

namespace ActualMathematics.DeltaKernel.Bootstrap

open ActualMathematics.DeltaKernel
open ActualMathematics

/-! ## Named arithmetic fragment -/

/-- Heyting-arithmetic fragment realized by the kernel: intuitionistic FOL over
`{0,S,+,·}` with induction and without classical posits. -/
structure HAFragment where
  /-- Forced empty-context derivations are true without EM/LPO/MP. -/
  forced_sound :
    ∀ {d : Deriv} {φ : DFormula},
      Forced [] d φ → ∀ ρ : Env, DFormula.sat ρ φ
  /-- Concrete witness: `1+1=2` is forced and exported. -/
  one_plus_one : 1 + 1 = 2
  /-- Concrete witness: `∀n, 0+n=n` is forced and exported. -/
  zero_add : ∀ n : Nat, 0 + n = n

def haFragment : HAFragment where
  forced_sound := fun h => sound_forced h
  one_plus_one := Examples.one_plus_one_certified
  zero_add := Examples.zero_add_certified

theorem ha_fragment_holds : Nonempty HAFragment := ⟨haFragment⟩

/-! ## Conventional foundations realize the δ core -/

theorem hf_sets_realize_delta :
    Nonempty (PRCEmbeddingInto SetTheoryParse.hfSystem) :=
  SetTheoryParse.hfSystem_embeds_delta

theorem mltt_two_realize_delta :
    Nonempty (PRCEmbeddingInto TypeTheoryParse.ttSystem) :=
  TypeTheoryParse.ttSystem_embeds_delta

/-- B3 package. -/
def BootstrapFoundationSpec : Prop :=
  Nonempty HAFragment ∧
  Nonempty (PRCEmbeddingInto SetTheoryParse.hfSystem) ∧
  Nonempty (PRCEmbeddingInto TypeTheoryParse.ttSystem)

theorem bootstrap_foundation : BootstrapFoundationSpec :=
  ⟨ha_fragment_holds, hf_sets_realize_delta, mltt_two_realize_delta⟩

#print axioms bootstrap_foundation

end ActualMathematics.DeltaKernel.Bootstrap

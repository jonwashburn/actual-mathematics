import ActualMathematics.DeltaKernel.BootstrapArithmetic
import ActualMathematics.DeltaKernel.Sound
import ActualMathematics.FormalSystem
import ActualMathematics.PRCSetTheoryParse
import ActualMathematics.PRCTypeTheoryParse
import Mathlib.Data.Nat.Bitwise

/-!
# Bootstrap B3: foundation interpretation

The first exact conventional foundation is the empty-ledger fragment of
Heyting arithmetic over `{0,S,+,·}`.  Its syntax and proof rules are the
licensed δ kernel, and `sound_forced` gives its interpretation in the
δ-derived natural carrier without EM, LPO, or Markov.

The first set foundation is Adjunctive Set Theory with Extensionality
(AST+Ext).  Its three axioms are extensionality, empty set, and adjunction
`x ∪ {y}`.  Ackermann codes on the δ arithmetic carrier form a model.  Every
code is denoted by a closed δ numeral, so this is a definable model
construction, not an object-language set primitive.

This is relative interpretation, not "no metatheory." The host still supplies
`Type`, `Prop`, and recursion. The object claim is that the named foundations
are represented by constructions over δ arithmetic.  The final section also
records the converse, weaker fact already proved elsewhere: conventional HF
set theory and a two-element MLTT fragment each contain the δ endpoint core.
-/

namespace ActualMathematics.DeltaKernel.Bootstrap

open ActualMathematics.DeltaKernel
open ActualMathematics
open SetTheoryParse

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

/-! ## AST+Ext interpreted by δ arithmetic -/

/-- The exact three-axiom theory interpreted first on the set side:
Adjunctive Set Theory with Extensionality.  `C : Type` and `Prop` belong to
the outside Lean metatheory. -/
def ASTExtAxioms {C : Type} (mem : C → C → Prop)
    (empty : C) (adj : C → C → C) : Prop :=
  (∀ a b, (∀ x, mem x a ↔ mem x b) → a = b) ∧
  (∀ x, ¬ mem x empty) ∧
  (∀ x a b, mem x (adj a b) ↔ mem x a ∨ x = b)

/-- Ackermann adjunction: set the bit indexed by the adjoined code. -/
def hfAdj (a b : Nat) : Nat := a ||| 2 ^ b

theorem mem_hfAdj (x a b : Nat) :
    Mem x (hfAdj a b) ↔ Mem x a ∨ x = b := by
  change Nat.testBit (a ||| 2 ^ b) x = true ↔
    Nat.testBit a x = true ∨ x = b
  rw [Nat.testBit_lor, Bool.or_eq_true, Nat.testBit_two_pow]
  simp only [decide_eq_true_eq]
  exact or_congr Iff.rfl eq_comm

/-- The Ackermann carrier satisfies AST+Ext. -/
theorem hf_satisfies_ASTExt :
    ASTExtAxioms Mem 0 hfAdj := by
  refine ⟨?_, not_mem_empty, mem_hfAdj⟩
  intro a b h
  exact (ext_iff a b).mpr h

/-- Every HF carrier code is the value of a closed δ term. -/
theorem hf_code_delta_denoted (n : Nat) :
    ∃ t : DTerm, t.eval (fun _ => 0) = n :=
  ⟨DTerm.ofNat n, eval_ofNat_closed n⟩

/-- Exact semantic interpretation receipt for AST+Ext inside δ arithmetic. -/
def HFModelDefinableInDelta : Prop :=
  ASTExtAxioms Mem 0 hfAdj ∧
  ∀ n : Nat, ∃ t : DTerm, t.eval (fun _ => 0) = n

theorem hf_model_definable_in_delta : HFModelDefinableInDelta :=
  ⟨hf_satisfies_ASTExt, hf_code_delta_denoted⟩

/-- Extensional observation both preserves and reflects equality of the
interpreted set codes. -/
theorem hf_observation_iff_code_eq (m n : Nat) :
    (∀ i, Mem i m ↔ Mem i n) ↔ m = n :=
  (ext_iff m n).symm

/-- Nontrivial AST+Ext probe: the singleton of the empty code is distinct
from the empty code.  Its δ certificate uses no classical posit. -/
def astSeparationProbe : Deriv :=
  Deriv.succNeZero DTerm.zero

theorem ast_separation_probe_forced :
    check [] astSeparationProbe =
      some (.neg (.eq (.succ .zero) .zero), .empty) :=
  rfl

/-! ## Converse endpoint embeddings -/

theorem hf_sets_realize_delta :
    Nonempty (PRCEmbeddingInto SetTheoryParse.hfSystem) :=
  SetTheoryParse.hfSystem_embeds_delta

theorem mltt_two_realize_delta :
    Nonempty (PRCEmbeddingInto TypeTheoryParse.ttSystem) :=
  TypeTheoryParse.ttSystem_embeds_delta

/-- B3 package. -/
def BootstrapFoundationSpec : Prop :=
  Nonempty HAFragment ∧
  HFModelDefinableInDelta ∧
  (∀ m n : Nat, (∀ i, Mem i m ↔ Mem i n) ↔ m = n) ∧
  check [] astSeparationProbe =
    some (.neg (.eq (.succ .zero) .zero), .empty) ∧
  Nonempty (PRCEmbeddingInto SetTheoryParse.hfSystem) ∧
  Nonempty (PRCEmbeddingInto TypeTheoryParse.ttSystem)

theorem bootstrap_foundation : BootstrapFoundationSpec :=
  ⟨ha_fragment_holds,
   hf_model_definable_in_delta,
   hf_observation_iff_code_eq,
   ast_separation_probe_forced,
   hf_sets_realize_delta,
   mltt_two_realize_delta⟩

#print axioms hf_satisfies_ASTExt
#print axioms hf_model_definable_in_delta
#print axioms ast_separation_probe_forced
#print axioms bootstrap_foundation

end ActualMathematics.DeltaKernel.Bootstrap

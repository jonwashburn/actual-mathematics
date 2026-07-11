import ActualMathematics.DeltaKernel.BootstrapDerived
import ActualMathematics.DeltaKernel.BootstrapRealizations
import ActualMathematics.Orbit

/-!
# Bootstrap B5: host invariance

Initiality supplies a unique structure map out of `DTerm` into every
`TermAlgebra`. Instantiating two independent carriers, Lean's `Nat` and
the directly implemented `List Unit` arithmetic, gives a canonical
length/replication isomorphism. `host_validity_iff` proves that translation
preserves and reflects satisfaction of every δ formula. Empty-ledger
certificates are sound in both.

`DistinctionNat` is retained below as the internal orbit realization of closed
numerals. It is not counted as the independent host because it shares the Lean
implementation and uses the same structural fold.

A second-host executable checker (Python) lives beside this module and
must agree on the forced `1+1=2` tree; that agreement is an empirical
receipt for checker portability, not a Lean theorem and not a proof of full
checker equivalence.
-/

namespace ActualMathematics.DeltaKernel.Bootstrap

open ActualMathematics.DeltaKernel
open ActualMathematics

/-! ## Two independent term algebras -/

/-- Host realization A: Lean `Nat`. Variables are ignored for closed-term
comparison by reading them as `0`. -/
def natAlgebra : TermAlgebra where
  carrier := Nat
  var := fun _ => 0
  zero := 0
  succ := Nat.succ
  add := Nat.add
  mul := Nat.mul

/-- Host realization B: the δ-orbit carrier. -/
def distinctionAlgebra : TermAlgebra where
  carrier := DistinctionNat
  var := fun _ => .zero
  zero := .zero
  succ := DistinctionNat.succ
  add := fun a b => DistinctionNat.ofNat (a.toNat + b.toNat)
  mul := fun a b => DistinctionNat.ofNat (a.toNat * b.toNat)

/-- Unique interpretation of syntax into `Nat`. -/
def interpretNat : TermHom termSyntax natAlgebra :=
  foldHom natAlgebra

/-- Unique interpretation of syntax into `DistinctionNat`. -/
def interpretDist : TermHom termSyntax distinctionAlgebra :=
  foldHom distinctionAlgebra

theorem interpretNat_unique (g : TermHom termSyntax natAlgebra) :
    g = interpretNat :=
  TermHom.ext (funext (fun t => by
    rw [hom_eq_fold natAlgebra g t]
    rfl))

theorem interpretDist_unique (g : TermHom termSyntax distinctionAlgebra) :
    g = interpretDist :=
  TermHom.ext (funext (fun t => by
    rw [hom_eq_fold distinctionAlgebra g t]
    rfl))

/-! ## Closed-term transport -/

def transportClosed (n : Nat) : DistinctionNat :=
  DistinctionNat.ofNat n

theorem transportClosed_toNat (n : Nat) :
    (transportClosed n).toNat = n :=
  DistinctionNat.toNat_ofNat n

theorem fold_nat_ofNat (n : Nat) :
    foldTerm natAlgebra (DTerm.ofNat n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Nat.succ (foldTerm natAlgebra (DTerm.ofNat n)) = Nat.succ n
      exact congrArg Nat.succ ih

theorem fold_dist_ofNat (n : Nat) :
    foldTerm distinctionAlgebra (DTerm.ofNat n) = DistinctionNat.ofNat n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change DistinctionNat.succ (foldTerm distinctionAlgebra (DTerm.ofNat n)) =
        DistinctionNat.succ (DistinctionNat.ofNat n)
      exact congrArg DistinctionNat.succ ih

/-- Host invariance for numerals: both realizations agree after transport. -/
theorem host_invariance_numerals (n : Nat) :
    transportClosed (foldTerm natAlgebra (DTerm.ofNat n)) =
      foldTerm distinctionAlgebra (DTerm.ofNat n) := by
  rw [fold_nat_ofNat, fold_dist_ofNat]
  rfl

/-- Any two homs into the same algebra agree, so representation changes that
preserve the licensed signature cannot alter interpretation. -/
theorem host_invariance_unique_nat
    (f g : TermHom termSyntax natAlgebra) : f = g := by
  rw [interpretNat_unique f, interpretNat_unique g]

theorem host_invariance_unique_dist
    (f g : TermHom termSyntax distinctionAlgebra) : f = g := by
  rw [interpretDist_unique f, interpretDist_unique g]

/-- B5 package. -/
def BootstrapHostInvarianceSpec : Prop :=
  TermSyntaxInitial ∧
  IndependentRealizationSpec ∧
  (∀ φ : DFormula, NatValid φ ↔ ListValid φ) ∧
  (∀ n, transportClosed (foldTerm natAlgebra (DTerm.ofNat n)) =
      foldTerm distinctionAlgebra (DTerm.ofNat n)) ∧
  (∀ f g : TermHom termSyntax natAlgebra, f = g) ∧
  (∀ f g : TermHom termSyntax distinctionAlgebra, f = g)

theorem bootstrap_host_invariance : BootstrapHostInvarianceSpec :=
  ⟨term_syntax_initial,
   independent_realizations,
   host_validity_iff,
   host_invariance_numerals,
   host_invariance_unique_nat, host_invariance_unique_dist⟩

#print axioms host_validity_iff
#print axioms bootstrap_host_invariance

end ActualMathematics.DeltaKernel.Bootstrap

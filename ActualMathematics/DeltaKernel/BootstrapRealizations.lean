import Mathlib
import ActualMathematics.DeltaKernel.BootstrapInitiality
import ActualMathematics.Rigidity.BaseInitiality

/-!
# The δ bootstrap: independent carrier realizations

The canonical semantics in `Semantics.lean` evaluates terms in `Nat`.  This file
adds a second realization written independently on `List Unit`.  Its evaluator
does not call the `Nat` evaluator, `foldTerm`, `natRec`, or `msat`.

The two carriers are compared only after both definitions exist.  Length and
replication give the unique δ-isomorphism, and a formula-induction theorem proves
that the two semantics have the same truth values under related environments.
A singleton algebra is included as a hostile non-model: the hypotheses used by
host invariance reject a realization that collapses zero and successor.
-/

namespace ActualMathematics.DeltaKernel.Bootstrap

open ActualMathematics
open ActualMathematics.DeltaKernel
open ActualMathematics.Rigidity

/-! ## Two separately written arithmetic carriers -/

abbrev ListNat := List Unit

def listZero : ListNat := []

def listSucc (x : ListNat) : ListNat := () :: x

def listAdd (x y : ListNat) : ListNat := x ++ y

/-- Multiplication by structural iteration on the second list. -/
def listMul : ListNat → ListNat → ListNat
  | _, [] => []
  | x, _ :: y => listAdd (listMul x y) x

@[simp] theorem length_listZero : listZero.length = 0 := rfl

@[simp] theorem length_listSucc (x : ListNat) :
    (listSucc x).length = x.length + 1 := rfl

@[simp] theorem length_listAdd (x y : ListNat) :
    (listAdd x y).length = x.length + y.length := by
  simp [listAdd]

@[simp] theorem length_listMul (x y : ListNat) :
    (listMul x y).length = x.length * y.length := by
  induction y with
  | nil => rfl
  | cons _ y ih =>
      simp [listMul, listAdd, ih, Nat.mul_succ]

/-- Every list of `Unit` is the canonical repetition of its sole inhabitant. -/
theorem listUnit_eq_replicate_length (x : ListNat) :
    x = List.replicate x.length () := by
  induction x with
  | nil => rfl
  | cons a x ih =>
      cases a
      exact congrArg (fun z : List Unit => () :: z) ih

/-- Lists of `Unit` are determined by their length. -/
theorem listUnit_eq_of_length_eq {x y : ListNat} (h : x.length = y.length) :
    x = y := by
  calc
    x = List.replicate x.length () := listUnit_eq_replicate_length x
    _ = List.replicate y.length () := congrArg (fun n => List.replicate n ()) h
    _ = y := (listUnit_eq_replicate_length y).symm

theorem listUnit_length_injective :
    Function.Injective (List.length : ListNat → Nat) :=
  fun _ _ => listUnit_eq_of_length_eq

/-- The explicit carrier equivalence.  It is data, with no choice of inverse. -/
def listNatEquiv : ListNat ≃ Nat where
  toFun := List.length
  invFun := fun n => List.replicate n ()
  left_inv := fun x => listUnit_eq_of_length_eq (by simp)
  right_inv := fun n => by simp

def natDeltaAlgebra : DeltaAlgebra where
  carrier := Nat
  zero := 0
  succ := Nat.succ

def listDeltaAlgebra : DeltaAlgebra where
  carrier := ListNat
  zero := listZero
  succ := listSucc

theorem natDeltaAlgebra_peano : IsPeanoModel natDeltaAlgebra where
  succ_injective := by
    intro a b h
    exact Nat.succ.inj h
  zero_not_succ := Nat.succ_ne_zero
  induction := fun P h0 hs n => Nat.rec h0 (fun k ih => hs k ih) n

theorem listDeltaAlgebra_peano : IsPeanoModel listDeltaAlgebra where
  succ_injective := by
    intro a b h
    exact List.cons.inj h |>.2
  zero_not_succ := by
    intro x h
    cases h
  induction := by
    intro P h0 hs x
    induction x with
    | nil => exact h0
    | cons a x ih =>
        cases a
        exact hs x ih

/-- The collapsed carrier is a concrete non-model. -/
def singletonDeltaAlgebra : DeltaAlgebra where
  carrier := Unit
  zero := ()
  succ := fun _ => ()

theorem singletonDeltaAlgebra_not_peano :
    ¬ IsPeanoModel singletonDeltaAlgebra := by
  intro h
  exact h.zero_not_succ () rfl

private theorem replicate_succ_unit (n : Nat) :
    List.replicate (Nat.succ n) () = () :: List.replicate n () := by
  rw [Nat.succ_eq_add_one, List.replicate_succ]

/-- The explicit hom from the `Nat` realization to the list realization. -/
def natToListHom : DeltaHom natDeltaAlgebra listDeltaAlgebra where
  map := fun n => List.replicate n ()
  map_zero := rfl
  map_succ := replicate_succ_unit

theorem natToListHom_bijective : Function.Bijective natToListHom.map := by
  constructor
  · intro m n h
    have := congrArg List.length h
    simpa [natToListHom] using this
  · intro x
    exact ⟨x.length, listUnit_eq_of_length_eq (by simp [natToListHom])⟩

def natListDeltaIso : DeltaIso natDeltaAlgebra listDeltaAlgebra :=
  ⟨natToListHom, natToListHom_bijective⟩

/-! ## Independent term evaluators -/

def ListEnv : Type := Nat → ListNat

namespace ListEnv

def cons (v : ListNat) (ρ : ListEnv) : ListEnv
  | 0 => v
  | n + 1 => ρ n

@[simp] theorem cons_zero (v : ListNat) (ρ : ListEnv) :
    cons v ρ 0 = v := rfl

@[simp] theorem cons_succ (v : ListNat) (ρ : ListEnv) (n : Nat) :
    cons v ρ (n + 1) = ρ n := rfl

end ListEnv

/-- Direct list evaluator.  This definition is independent of the generic fold
and of `DTerm.eval`. -/
def evalList (ρ : ListEnv) : DTerm → ListNat
  | .var n => ρ n
  | .zero => listZero
  | .succ t => listSucc (evalList ρ t)
  | .add t u => listAdd (evalList ρ t) (evalList ρ u)
  | .mul t u => listMul (evalList ρ t) (evalList ρ u)

def natTermAlgebra (ρ : Env) : TermAlgebra where
  carrier := Nat
  var := ρ
  zero := 0
  succ := Nat.succ
  add := Nat.add
  mul := Nat.mul

def listTermAlgebra (ρ : ListEnv) : TermAlgebra where
  carrier := ListNat
  var := ρ
  zero := listZero
  succ := listSucc
  add := listAdd
  mul := listMul

theorem foldTerm_nat_eq_eval (ρ : Env) :
    ∀ t, foldTerm (natTermAlgebra ρ) t = DTerm.eval ρ t := by
  intro t
  induction t with
  | var n => rfl
  | zero => rfl
  | succ t ih =>
      exact congrArg Nat.succ ih
  | add t u iht ihu =>
      exact congrArg₂ Nat.add iht ihu
  | mul t u iht ihu =>
      exact congrArg₂ Nat.mul iht ihu

theorem foldTerm_list_eq_evalList (ρ : ListEnv) :
    ∀ t, foldTerm (listTermAlgebra ρ) t = evalList ρ t := by
  intro t
  induction t with
  | var n => rfl
  | zero => rfl
  | succ t ih =>
      exact congrArg listSucc ih
  | add t u iht ihu =>
      exact congrArg₂ listAdd iht ihu
  | mul t u iht ihu =>
      exact congrArg₂ listMul iht ihu

/-- Environments name the same variables when each list has the corresponding
natural length. -/
def EnvRelated (ρN : Env) (ρL : ListEnv) : Prop :=
  ∀ i, (ρL i).length = ρN i

theorem EnvRelated.cons {ρN : Env} {ρL : ListEnv}
    (h : EnvRelated ρN ρL) (n : Nat) (x : ListNat)
    (hx : x.length = n) :
    EnvRelated (Env.cons n ρN) (ListEnv.cons x ρL) := by
  intro i
  cases i with
  | zero => exact hx
  | succ i => exact h i

theorem evalList_length {ρN : Env} {ρL : ListEnv}
    (h : EnvRelated ρN ρL) :
    ∀ t, (evalList ρL t).length = DTerm.eval ρN t := by
  intro t
  induction t with
  | var n => exact h n
  | zero => rfl
  | succ t ih => simp [evalList, DTerm.eval, ih]
  | add t u iht ihu => simp [evalList, DTerm.eval, iht, ihu]
  | mul t u iht ihu => simp [evalList, DTerm.eval, iht, ihu]

/-! ## Independent formula semantics and invariance -/

/-- Formula semantics written directly on the list carrier. -/
def listSat (ρ : ListEnv) : DFormula → Prop
  | .eq t u => evalList ρ t = evalList ρ u
  | .fls => False
  | .conj a b => listSat ρ a ∧ listSat ρ b
  | .disj a b => listSat ρ a ∨ listSat ρ b
  | .impl a b => listSat ρ a → listSat ρ b
  | .all a => ∀ x : ListNat, listSat (ListEnv.cons x ρ) a
  | .ex a => ∃ x : ListNat, listSat (ListEnv.cons x ρ) a

/-- Related environments give identical truth values in the direct `Nat` and
direct `List Unit` semantics. -/
theorem listSat_iff_sat :
    ∀ (φ : DFormula) {ρN : Env} {ρL : ListEnv},
      EnvRelated ρN ρL → (listSat ρL φ ↔ DFormula.sat ρN φ) := by
  intro φ
  induction φ with
  | eq t u =>
      intro ρN ρL hρ
      simp only [listSat, DFormula.sat]
      constructor
      · intro h
        have hl := congrArg List.length h
        simpa [evalList_length hρ t, evalList_length hρ u] using hl
      · intro h
        apply listUnit_eq_of_length_eq
        rw [evalList_length hρ t, evalList_length hρ u, h]
  | fls =>
      intro ρN ρL hρ
      exact Iff.rfl
  | conj a b iha ihb =>
      intro ρN ρL hρ
      exact and_congr (iha hρ) (ihb hρ)
  | disj a b iha ihb =>
      intro ρN ρL hρ
      exact or_congr (iha hρ) (ihb hρ)
  | impl a b iha ihb =>
      intro ρN ρL hρ
      exact imp_congr (iha hρ) (ihb hρ)
  | all a ih =>
      intro ρN ρL hρ
      simp only [listSat, DFormula.sat]
      constructor
      · intro hL n
        let x : ListNat := List.replicate n ()
        have hx : x.length = n := by simp [x]
        exact (ih (hρ.cons n x hx)).mp (hL x)
      · intro hN x
        exact (ih (hρ.cons x.length x rfl)).mpr (hN x.length)
  | ex a ih =>
      intro ρN ρL hρ
      simp only [listSat, DFormula.sat]
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x.length, (ih (hρ.cons x.length x rfl)).mp hx⟩
      · rintro ⟨n, hn⟩
        let x : ListNat := List.replicate n ()
        have hx : x.length = n := by simp [x]
        exact ⟨x, (ih (hρ.cons n x hx)).mpr hn⟩

/-- Closed observational truth in the direct natural semantics. -/
def NatValid (φ : DFormula) : Prop :=
  ∀ ρN : Env, DFormula.sat ρN φ

/-- Closed observational truth in the independently written list semantics. -/
def ListValid (φ : DFormula) : Prop :=
  ∀ ρL : ListEnv, listSat ρL φ

/-- Canonical host translation preserves and reflects truth of every formula.
This is the observational equivalence used by the bootstrap theorem. -/
theorem host_validity_iff (φ : DFormula) :
    NatValid φ ↔ ListValid φ := by
  constructor
  · intro hN ρL
    let ρN : Env := fun i => (ρL i).length
    have hρ : EnvRelated ρN ρL := fun _ => rfl
    exact (listSat_iff_sat φ hρ).mpr (hN ρN)
  · intro hL ρN
    let ρL : ListEnv := fun i => List.replicate (ρN i) ()
    have hρ : EnvRelated ρN ρL := by
      intro i
      simp [ρL]
    exact (listSat_iff_sat φ hρ).mp (hL ρL)

/-- Every empty-ledger certificate is true in the independently written list
semantics. -/
theorem sound_forced_list {d : Deriv} {φ : DFormula}
    (h : Forced [] d φ) :
    ∀ ρL : ListEnv, listSat ρL φ := by
  intro ρL
  let ρN : Env := fun i => (ρL i).length
  have hρ : EnvRelated ρN ρL := fun _ => rfl
  exact (listSat_iff_sat φ hρ).mpr (sound_forced h ρN)

/-- A forced certificate has the same semantic force in both concrete hosts. -/
theorem forced_true_in_both {d : Deriv} {φ : DFormula}
    (h : Forced [] d φ) :
    (∀ ρN : Env, DFormula.sat ρN φ) ∧
      (∀ ρL : ListEnv, listSat ρL φ) :=
  ⟨sound_forced h, sound_forced_list h⟩

/-! ## Second-rung capstone -/

def IndependentRealizationSpec : Prop :=
  IsPeanoModel natDeltaAlgebra ∧
  IsPeanoModel listDeltaAlgebra ∧
  ¬ IsPeanoModel singletonDeltaAlgebra ∧
  Function.Bijective natToListHom.map ∧
  (∀ (φ : DFormula) (ρN : Env) (ρL : ListEnv),
    EnvRelated ρN ρL → (listSat ρL φ ↔ DFormula.sat ρN φ)) ∧
  (∀ φ : DFormula, NatValid φ ↔ ListValid φ) ∧
  (∀ (d : Deriv) (φ : DFormula), Forced [] d φ →
    (∀ ρN : Env, DFormula.sat ρN φ) ∧
      (∀ ρL : ListEnv, listSat ρL φ))

theorem independent_realizations : IndependentRealizationSpec :=
  ⟨natDeltaAlgebra_peano,
   listDeltaAlgebra_peano,
   singletonDeltaAlgebra_not_peano,
   natToListHom_bijective,
   fun φ _ _ hρ => listSat_iff_sat φ hρ,
   host_validity_iff,
   fun _ _ h => forced_true_in_both h⟩

#print axioms listDeltaAlgebra_peano
#print axioms singletonDeltaAlgebra_not_peano
#print axioms length_listMul
#print axioms listUnit_eq_of_length_eq
#print axioms listNatEquiv
#print axioms natToListHom
#print axioms evalList_length
#print axioms natToListHom_bijective
#print axioms listSat_iff_sat
#print axioms host_validity_iff
#print axioms sound_forced_list
#print axioms independent_realizations

end ActualMathematics.DeltaKernel.Bootstrap

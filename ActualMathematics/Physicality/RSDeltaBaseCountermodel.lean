/- 
  ActualMathematics/Physicality/RSDeltaBaseCountermodel.lean

  Generator-gauge no-go theorem for intrinsic δ/J physicality.

  The existing δ language observes equality through the zero locus of J. It
  cannot observe the magnitude of a positive multiplicative generator. For
  every real `g > 1`, this file constructs:

      1, g, g², g³, ...

  as a Peano-shaped orbit, proves J separates its stages, and proves every δ
  formula has exactly its canonical satisfaction value on that orbit.

  CLAIM: CLOSED negative FOR uniqueness of generator 2 from the current
    Peano-generation, forced-J, J-zero-separation, and δ-transport premises.
  DOMAIN: positive real power orbits with generator `g > 1`.
  PREMISES: the existing δ checker soundness and canonical J zero-locus facts.
  REACH: base 3, base 3/2, and base φ satisfy the same current semantic premises
    as base 2; no δ formula can distinguish them.
  does NOT license: rejection of generator 2, or rejection of a physical bridge
    that identifies one-step gain with the two outcomes of `DerivedTwo`.

  `RSBinaryGainBridge` names that missing physical interpretation. Under it,
  and only under it among the surfaces formalized here, generator 2 and
  first-step cost 1/4 are forced.

  No project-local axioms. Every declaration is fully proved.
-/

import ActualMathematics.Physicality.RSDeltaClosure
import ActualMathematics.DeltaKernel.BootstrapDerived

namespace ActualMathematics
namespace Physicality
namespace RSDeltaBaseCountermodel

open DeltaKernel
open DeltaKernel.Bootstrap
open Rigidity
open RSDeltaClosure

noncomputable section

/-! ## A neutral positive-real generator orbit -/

def baseGTrace (g : ℝ) (n : DistinctionNat) : ℝ :=
  g ^ n.toNat

@[simp] theorem baseGTrace_zero (g : ℝ) :
    baseGTrace g DistinctionNat.zero = 1 := by
  rfl

@[simp] theorem baseGTrace_succ (g : ℝ) (n : DistinctionNat) :
    baseGTrace g (DistinctionNat.succ n) = g * baseGTrace g n := by
  rw [baseGTrace, baseGTrace, DistinctionNat.toNat_succ, pow_succ]
  ring

theorem baseGTrace_positive {g : ℝ} (hg : 1 < g) (n : DistinctionNat) :
    0 < baseGTrace g n := by
  unfold baseGTrace
  positivity

theorem baseGTrace_one_le {g : ℝ} (hg : 1 < g) (n : DistinctionNat) :
    1 ≤ baseGTrace g n := by
  induction n with
  | zero =>
      rw [baseGTrace_zero]
  | succ n ih =>
      rw [baseGTrace_succ]
      nlinarith

theorem baseGTrace_injective {g : ℝ} (hg : 1 < g) :
    Function.Injective (baseGTrace g) := by
  intro m n h
  change g ^ m.toNat = g ^ n.toNat at h
  have hg0 : 0 < g := lt_trans (by norm_num) hg
  have hnat : m.toNat = n.toNat :=
    pow_right_injective₀ hg0 (ne_of_gt hg) h
  exact DistinctionNat.toNat_inj hnat

def BaseGOrbit (g : ℝ) : Type :=
  Set.range (baseGTrace g)

namespace BaseGOrbit

theorem positive {g : ℝ} (hg : 1 < g) (x : BaseGOrbit g) :
    0 < x.1 := by
  rcases x with ⟨_, ⟨n, rfl⟩⟩
  exact baseGTrace_positive hg n

theorem one_le {g : ℝ} (hg : 1 < g) (x : BaseGOrbit g) :
    1 ≤ x.1 := by
  rcases x with ⟨_, ⟨n, rfl⟩⟩
  exact baseGTrace_one_le hg n

end BaseGOrbit

def baseGZero (g : ℝ) : BaseGOrbit g :=
  ⟨1, ⟨DistinctionNat.zero, baseGTrace_zero g⟩⟩

def baseGSucc (g : ℝ) (x : BaseGOrbit g) : BaseGOrbit g :=
  ⟨g * x.1, by
    rcases x with ⟨x, ⟨n, hn⟩⟩
    refine ⟨DistinctionNat.succ n, ?_⟩
    rw [baseGTrace_succ, hn]⟩

@[simp] theorem baseG_succ_native (g : ℝ) (x : BaseGOrbit g) :
    (baseGSucc g x).1 = g * x.1 :=
  rfl

def baseGAlgebra (g : ℝ) : DeltaAlgebra where
  carrier := BaseGOrbit g
  zero := baseGZero g
  succ := baseGSucc g

theorem baseGAlgebra_peano {g : ℝ} (hg : 1 < g) :
    IsPeanoModel (baseGAlgebra g) where
  succ_injective := by
    intro x y h
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    change g * x.1 = g * y.1 at hv
    have hg0 : 0 < g := lt_trans (by norm_num) hg
    nlinarith
  zero_not_succ := by
    intro x h
    have hv := congrArg Subtype.val h
    change g * x.1 = 1 at hv
    have hx := BaseGOrbit.one_le hg x
    nlinarith
  induction := by
    intro P h0 hs x
    rcases x with ⟨_, ⟨n, rfl⟩⟩
    induction n with
    | zero =>
        simpa [baseGAlgebra, baseGZero] using h0
    | succ n ih =>
        have hstep :=
          hs (⟨baseGTrace g n, ⟨n, rfl⟩⟩ : BaseGOrbit g) ih
        simpa [baseGAlgebra, baseGSucc, baseGTrace_succ] using hstep

noncomputable def baseGCompare (g : ℝ) (x y : BaseGOrbit g) : ℝ :=
  Cost.Jcost (x.1 / y.1)

theorem baseG_compare_eq_zero_iff {g : ℝ} (hg : 1 < g)
    (x y : BaseGOrbit g) :
    baseGCompare g x y = 0 ↔ x = y := by
  constructor
  · intro h
    have hratio : x.1 / y.1 = 1 :=
      (jcost_eq_zero_iff_one
        (div_pos (BaseGOrbit.positive hg x) (BaseGOrbit.positive hg y))).mp h
    have hy : y.1 ≠ 0 := (BaseGOrbit.positive hg y).ne'
    field_simp [hy] at hratio
    exact Subtype.ext hratio
  · rintro rfl
    simpa [baseGCompare, (BaseGOrbit.positive hg x).ne'] using Cost.Jcost_unit0

theorem baseG_first_step_formula {g : ℝ} (hg : 1 < g) :
    baseGCompare g (baseGZero g) (baseGSucc g (baseGZero g)) =
      Cost.Jcost g := by
  have hg0 : 0 < g := lt_trans (by norm_num) hg
  simpa [baseGCompare, baseGZero, baseGSucc, div_eq_mul_inv] using
    (Cost.Jcost_symm hg0).symm

/-! ## Native recursive arithmetic on the neutral orbit -/

noncomputable def baseGNatEquiv (g : ℝ) (hg : 1 < g) :
    ℕ ≃ BaseGOrbit g :=
  Equiv.ofBijective (natRec (baseGAlgebra g))
    ⟨natRec_injective (baseGAlgebra g) (baseGAlgebra_peano hg),
     natRec_surjective (baseGAlgebra g) (baseGAlgebra_peano hg)⟩

@[simp] theorem baseGNatEquiv_apply (g : ℝ) (hg : 1 < g) (n : ℕ) :
    baseGNatEquiv g hg n = natRec (baseGAlgebra g) n :=
  rfl

@[simp] theorem baseGNatEquiv_zero (g : ℝ) (hg : 1 < g) :
    baseGNatEquiv g hg 0 = baseGZero g :=
  rfl

@[simp] theorem baseGNatEquiv_succ (g : ℝ) (hg : 1 < g) (n : ℕ) :
    baseGNatEquiv g hg (Nat.succ n) =
      baseGSucc g (baseGNatEquiv g hg n) :=
  rfl

@[simp] theorem baseGNatEquiv_symm_zero (g : ℝ) (hg : 1 < g) :
    (baseGNatEquiv g hg).symm (baseGZero g) = 0 := by
  rw [← baseGNatEquiv_zero g hg]
  exact Equiv.symm_apply_apply (baseGNatEquiv g hg) 0

@[simp] theorem baseGNatEquiv_symm_succ (g : ℝ) (hg : 1 < g)
    (x : BaseGOrbit g) :
    (baseGNatEquiv g hg).symm (baseGSucc g x) =
      Nat.succ ((baseGNatEquiv g hg).symm x) := by
  apply (baseGNatEquiv g hg).injective
  rw [Equiv.apply_symm_apply]
  simpa using
    (baseGNatEquiv_succ g hg ((baseGNatEquiv g hg).symm x)).symm

@[simp] theorem baseGNatEquiv_symm_natRec (g : ℝ) (hg : 1 < g) (n : ℕ) :
    (baseGNatEquiv g hg).symm (natRec (baseGAlgebra g) n) = n := by
  simpa using Equiv.symm_apply_apply (baseGNatEquiv g hg) n

noncomputable def baseGAdd (g : ℝ) (hg : 1 < g)
    (x y : BaseGOrbit g) : BaseGOrbit g :=
  baseGNatEquiv g hg
    ((baseGNatEquiv g hg).symm x + (baseGNatEquiv g hg).symm y)

noncomputable def baseGMul (g : ℝ) (hg : 1 < g)
    (x y : BaseGOrbit g) : BaseGOrbit g :=
  baseGNatEquiv g hg
    ((baseGNatEquiv g hg).symm x * (baseGNatEquiv g hg).symm y)

@[simp] theorem baseGAdd_zero (g : ℝ) (hg : 1 < g) (x : BaseGOrbit g) :
    baseGAdd g hg x (baseGZero g) = x := by
  unfold baseGAdd
  rw [baseGNatEquiv_symm_zero, Nat.add_zero, Equiv.apply_symm_apply]

@[simp] theorem baseGAdd_succ (g : ℝ) (hg : 1 < g)
    (x y : BaseGOrbit g) :
    baseGAdd g hg x (baseGSucc g y) =
      baseGSucc g (baseGAdd g hg x y) := by
  unfold baseGAdd
  rw [baseGNatEquiv_symm_succ, Nat.add_succ, baseGNatEquiv_succ]

@[simp] theorem baseGMul_zero (g : ℝ) (hg : 1 < g) (x : BaseGOrbit g) :
    baseGMul g hg x (baseGZero g) = baseGZero g := by
  unfold baseGMul
  rw [baseGNatEquiv_symm_zero, Nat.mul_zero, baseGNatEquiv_zero]

@[simp] theorem baseGMul_succ (g : ℝ) (hg : 1 < g)
    (x y : BaseGOrbit g) :
    baseGMul g hg x (baseGSucc g y) =
      baseGAdd g hg (baseGMul g hg x y) x := by
  unfold baseGMul baseGAdd
  rw [baseGNatEquiv_symm_succ, Nat.mul_succ]
  simp only [Equiv.symm_apply_apply]

theorem baseG_natRec_add (g : ℝ) (hg : 1 < g) (m n : ℕ) :
    natRec (baseGAlgebra g) (m + n) =
      baseGAdd g hg (natRec (baseGAlgebra g) m)
        (natRec (baseGAlgebra g) n) := by
  change baseGNatEquiv g hg (m + n) =
    baseGAdd g hg (baseGNatEquiv g hg m) (baseGNatEquiv g hg n)
  simp [baseGAdd, baseGNatEquiv_symm_natRec]

theorem baseG_natRec_mul (g : ℝ) (hg : 1 < g) (m n : ℕ) :
    natRec (baseGAlgebra g) (m * n) =
      baseGMul g hg (natRec (baseGAlgebra g) m)
        (natRec (baseGAlgebra g) n) := by
  change baseGNatEquiv g hg (m * n) =
    baseGMul g hg (baseGNatEquiv g hg m) (baseGNatEquiv g hg n)
  simp [baseGMul, baseGNatEquiv_symm_natRec]

noncomputable def evalBaseGNative (g : ℝ) (hg : 1 < g)
    (ρ : Env) : DTerm → BaseGOrbit g
  | .var n => natRec (baseGAlgebra g) (ρ n)
  | .zero => baseGZero g
  | .succ t => baseGSucc g (evalBaseGNative g hg ρ t)
  | .add t s => baseGAdd g hg
      (evalBaseGNative g hg ρ t) (evalBaseGNative g hg ρ s)
  | .mul t s => baseGMul g hg
      (evalBaseGNative g hg ρ t) (evalBaseGNative g hg ρ s)

theorem evalBaseGNative_eq_natRec_eval (g : ℝ) (hg : 1 < g) (ρ : Env) :
    ∀ t : DTerm,
      evalBaseGNative g hg ρ t = natRec (baseGAlgebra g) (t.eval ρ)
  | .var _ => rfl
  | .zero => rfl
  | .succ t => by
      rw [evalBaseGNative, evalBaseGNative_eq_natRec_eval g hg ρ t]
      rfl
  | .add t s => by
      rw [evalBaseGNative, evalBaseGNative_eq_natRec_eval g hg ρ t,
        evalBaseGNative_eq_natRec_eval g hg ρ s]
      exact (baseG_natRec_add g hg (t.eval ρ) (s.eval ρ)).symm
  | .mul t s => by
      rw [evalBaseGNative, evalBaseGNative_eq_natRec_eval g hg ρ t,
        evalBaseGNative_eq_natRec_eval g hg ρ s]
      exact (baseG_natRec_mul g hg (t.eval ρ) (s.eval ρ)).symm

/-! ## The full δ language is generator-blind -/

def evalBaseG (g : ℝ) (ρ : Env) (t : DTerm) : BaseGOrbit g :=
  natRec (baseGAlgebra g) (t.eval ρ)

def msatBaseGJ (g : ℝ) : Env → DFormula → Prop
  | ρ, .eq t s =>
      baseGCompare g (evalBaseG g ρ t) (evalBaseG g ρ s) = 0
  | _, .fls => False
  | ρ, .conj a b => msatBaseGJ g ρ a ∧ msatBaseGJ g ρ b
  | ρ, .disj a b => msatBaseGJ g ρ a ∨ msatBaseGJ g ρ b
  | ρ, .impl a b => msatBaseGJ g ρ a → msatBaseGJ g ρ b
  | ρ, .all a =>
      ∀ x : BaseGOrbit g, ∀ n : ℕ,
        natRec (baseGAlgebra g) n = x → msatBaseGJ g (Env.cons n ρ) a
  | ρ, .ex a =>
      ∃ x : BaseGOrbit g, ∃ n : ℕ,
        natRec (baseGAlgebra g) n = x ∧ msatBaseGJ g (Env.cons n ρ) a

theorem msatBaseGJ_iff_msat {g : ℝ} (hg : 1 < g) (ρ : Env) :
    ∀ φ : DFormula,
      msatBaseGJ g ρ φ ↔ msat (baseGAlgebra g) ρ φ
  | .eq t s => by
      rw [msatBaseGJ, msat]
      exact baseG_compare_eq_zero_iff hg _ _
  | .fls => Iff.rfl
  | .conj a b => by
      simp only [msatBaseGJ, msat]
      exact and_congr (msatBaseGJ_iff_msat hg ρ a) (msatBaseGJ_iff_msat hg ρ b)
  | .disj a b => by
      simp only [msatBaseGJ, msat]
      exact or_congr (msatBaseGJ_iff_msat hg ρ a) (msatBaseGJ_iff_msat hg ρ b)
  | .impl a b => by
      simp only [msatBaseGJ, msat]
      exact imp_congr (msatBaseGJ_iff_msat hg ρ a) (msatBaseGJ_iff_msat hg ρ b)
  | .all a => by
      simp only [msatBaseGJ, msat]
      constructor
      · intro h x n hn
        exact (msatBaseGJ_iff_msat hg (Env.cons n ρ) a).mp (h x n hn)
      · intro h x n hn
        exact (msatBaseGJ_iff_msat hg (Env.cons n ρ) a).mpr (h x n hn)
  | .ex a => by
      simp only [msatBaseGJ, msat]
      constructor
      · rintro ⟨x, n, hn, h⟩
        exact ⟨x, n, hn, (msatBaseGJ_iff_msat hg (Env.cons n ρ) a).mp h⟩
      · rintro ⟨x, n, hn, h⟩
        exact ⟨x, n, hn, (msatBaseGJ_iff_msat hg (Env.cons n ρ) a).mpr h⟩

theorem msatBaseGJ_iff_sat {g : ℝ} (hg : 1 < g)
    (ρ : Env) (φ : DFormula) :
    msatBaseGJ g ρ φ ↔ DFormula.sat ρ φ :=
  (msatBaseGJ_iff_msat hg ρ φ).trans
    (msat_iff_sat (baseGAlgebra g) (baseGAlgebra_peano hg) φ ρ)

/-- The formula semantics can be read directly through the orbit's own
recursive term operations. The source-Nat evaluator is an extensionally equal
normal form, not a weaker semantic path. -/
theorem msatBaseGJ_atom_via_native {g : ℝ} (hg : 1 < g)
    (ρ : Env) (t s : DTerm) :
    msatBaseGJ g ρ (.eq t s) ↔
      baseGCompare g
        (evalBaseGNative g hg ρ t) (evalBaseGNative g hg ρ s) = 0 := by
  rw [msatBaseGJ, evalBaseGNative_eq_natRec_eval,
    evalBaseGNative_eq_natRec_eval]
  rfl

theorem msatBaseGJ_generator_invariant
    {g k : ℝ} (hg : 1 < g) (hk : 1 < k)
    (ρ : Env) (φ : DFormula) :
    msatBaseGJ g ρ φ ↔ msatBaseGJ k ρ φ :=
  (msatBaseGJ_iff_sat hg ρ φ).trans
    (msatBaseGJ_iff_sat hk ρ φ).symm

theorem generated_executes_baseG {g : ℝ} (hg : 1 < g)
    (G : GeneratedTheorem) (ρ : Env) :
    msatBaseGJ g ρ G.certificate.sentence := by
  apply (msatBaseGJ_iff_msat hg ρ G.certificate.sentence).mpr
  exact transport_forced G.certificate.forced
    (baseGAlgebra g) (baseGAlgebra_peano hg) ρ

structure GeneratorNeutralModel (g : ℝ) : Prop where
  one_lt : 1 < g
  peano : IsPeanoModel (baseGAlgebra g)
  cost_instance : JCostLawWitness
  cost_forced :
    ∀ (F : ℝ → ℝ),
      Cost.FunctionalEquation.IsReciprocalCost F →
      Cost.FunctionalEquation.IsNormalized F →
      Cost.FunctionalEquation.SatisfiesCompositionLaw F →
      MonotoneOn (Cost.FunctionalEquation.H F) (Set.Ici (0 : ℝ)) →
      Cost.FunctionalEquation.IsCalibrated F →
      ∀ x : ℝ, 0 < x → F x = Cost.Jcost x
  cost_separates : ∀ x y, baseGCompare g x y = 0 ↔ x = y
  all_formulas :
    ∀ ρ φ, msatBaseGJ g ρ φ ↔ DFormula.sat ρ φ
  atom_is_native_zero_cost :
    ∀ ρ t s, msatBaseGJ g ρ (.eq t s) ↔
      baseGCompare g
        (evalBaseGNative g one_lt ρ t)
        (evalBaseGNative g one_lt ρ s) = 0
  term_evaluation_is_native :
    ∀ ρ t,
      evalBaseGNative g one_lt ρ t =
        natRec (baseGAlgebra g) (t.eval ρ)
  add_zero : ∀ x, baseGAdd g one_lt x (baseGZero g) = x
  add_succ :
    ∀ x y, baseGAdd g one_lt x (baseGSucc g y) =
      baseGSucc g (baseGAdd g one_lt x y)
  mul_zero :
    ∀ x, baseGMul g one_lt x (baseGZero g) = baseGZero g
  mul_succ :
    ∀ x y, baseGMul g one_lt x (baseGSucc g y) =
      baseGAdd g one_lt (baseGMul g one_lt x y) x
  first_step_formula :
    baseGCompare g (baseGZero g) (baseGSucc g (baseGZero g)) =
      Cost.Jcost g

theorem generatorNeutralModel_of_one_lt {g : ℝ} (hg : 1 < g) :
    GeneratorNeutralModel g where
  one_lt := hg
  peano := baseGAlgebra_peano hg
  cost_instance := jcost_law_witness
  cost_forced := rs_jcost_forced
  cost_separates := baseG_compare_eq_zero_iff hg
  all_formulas := msatBaseGJ_iff_sat hg
  atom_is_native_zero_cost := msatBaseGJ_atom_via_native hg
  term_evaluation_is_native := evalBaseGNative_eq_natRec_eval g hg
  add_zero := baseGAdd_zero g hg
  add_succ := baseGAdd_succ g hg
  mul_zero := baseGMul_zero g hg
  mul_succ := baseGMul_succ g hg
  first_step_formula := baseG_first_step_formula hg

/-- The neutral-model family has exactly one parameter restriction: `g > 1`.
This is the moduli-space form of the no-go theorem. -/
theorem generatorNeutralModel_iff_one_lt (g : ℝ) :
    GeneratorNeutralModel g ↔ 1 < g :=
  ⟨fun M => M.one_lt, generatorNeutralModel_of_one_lt⟩

/-- Every neutral model executes every empty-ledger theorem checked by δ. -/
theorem GeneratorNeutralModel.executes_generated {g : ℝ}
    (M : GeneratorNeutralModel g) (G : GeneratedTheorem) (ρ : Env) :
    msatBaseGJ g ρ G.certificate.sentence :=
  generated_executes_baseG M.one_lt G ρ

theorem base3_countermodel :
    GeneratorNeutralModel 3 :=
  generatorNeutralModel_of_one_lt (by norm_num)

theorem baseThreeHalves_countermodel :
    GeneratorNeutralModel (3 / 2 : ℝ) :=
  generatorNeutralModel_of_one_lt (by norm_num)

theorem basePhi_countermodel :
    GeneratorNeutralModel Real.goldenRatio :=
  generatorNeutralModel_of_one_lt Real.one_lt_goldenRatio

/-- **No-go theorem.** The current generator-neutral process premises do not
force base two: base three satisfies all of them. -/
theorem generator_two_not_derivable :
    ¬ (∀ g : ℝ, GeneratorNeutralModel g → g = 2) := by
  intro h
  have h3 := h 3 base3_countermodel
  norm_num at h3

/-! ## One explicit generator-fixing physical bridge -/

/-- PHYSICAL INTERPRETATION: one multiplicative recognition step has gain equal
to the number of outcomes in the quotient-derived distinction carrier.

This proposition is deliberately named as a bridge. `derivedTwo_card` proves
the outcome count; it does not prove that a positive-real process coordinate
must equal that count. -/
def RSBinaryGainBridge (g : ℝ) : Prop :=
  g = Fintype.card DerivedTwo

theorem binary_gain_bridge_iff_two (g : ℝ) :
    RSBinaryGainBridge g ↔ g = 2 := by
  simp [RSBinaryGainBridge]

theorem generator_two_of_binary_gain_bridge {g : ℝ}
    (h : RSBinaryGainBridge g) :
    g = 2 :=
  (binary_gain_bridge_iff_two g).mp h

def RealizesFreeHistoryCardinality (g : ℝ) : Prop :=
  ∀ n : ℕ, g ^ n = Fintype.card (FreeDistinctionHistory n)

/-- The free-history realization and the one-step binary-gain bridge are the
same premise in two forms. They must not be counted as independent evidence. -/
theorem free_history_realization_iff_binary_gain_bridge (g : ℝ) :
    RealizesFreeHistoryCardinality g ↔ RSBinaryGainBridge g := by
  constructor
  · intro h
    have h1 := h 1
    simpa [RSBinaryGainBridge] using h1
  · intro h n
    have hg : g = 2 := generator_two_of_binary_gain_bridge h
    subst g
    simp

theorem jcost_eq_quarter_iff_two {g : ℝ} (hg : 1 < g) :
    Cost.Jcost g = 1 / 4 ↔ g = 2 := by
  have hg0 : 0 < g := lt_trans (by norm_num) hg
  constructor
  · intro h
    have hpoly : 2 * g ^ 2 - 5 * g + 2 = 0 := by
      unfold Cost.Jcost at h
      field_simp [hg0.ne'] at h
      nlinarith
    have hfactor : (2 * g - 1) * (g - 2) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfactor with hleft | hright
    · nlinarith
    · nlinarith
  · rintro rfl
    norm_num [Cost.Jcost]

/-- The bridge and the quarter-cost condition are the same generator-fixing
gate on positive orbits. J does not supply this gate by itself. -/
theorem binary_gain_bridge_iff_quarter_cost {g : ℝ} (hg : 1 < g) :
    RSBinaryGainBridge g ↔ Cost.Jcost g = 1 / 4 :=
  (binary_gain_bridge_iff_two g).trans (jcost_eq_quarter_iff_two hg).symm

theorem base3_fails_binary_gain_bridge :
    ¬ RSBinaryGainBridge 3 := by
  simp [RSBinaryGainBridge]

theorem baseThreeHalves_fails_binary_gain_bridge :
    ¬ RSBinaryGainBridge (3 / 2 : ℝ) := by
  norm_num [RSBinaryGainBridge]

theorem basePhi_fails_binary_gain_bridge :
    ¬ RSBinaryGainBridge Real.goldenRatio := by
  rw [binary_gain_bridge_iff_two]
  exact ne_of_lt Real.goldenRatio_lt_two

/-- Receipt preventing double counting: history cardinality, binary gain, and
quarter first-step cost are equivalent faces of one extra bridge. -/
theorem history_gain_quarter_triangle {g : ℝ} (hg : 1 < g) :
    (RealizesFreeHistoryCardinality g ↔ RSBinaryGainBridge g) ∧
    (RSBinaryGainBridge g ↔ Cost.Jcost g = 1 / 4) :=
  ⟨free_history_realization_iff_binary_gain_bridge g,
   binary_gain_bridge_iff_quarter_cost hg⟩

/-! ## Axiom audits -/

#print axioms baseGAlgebra_peano
#print axioms msatBaseGJ_iff_sat
#print axioms msatBaseGJ_generator_invariant
#print axioms generated_executes_baseG
#print axioms generatorNeutralModel_iff_one_lt
#print axioms GeneratorNeutralModel.executes_generated
#print axioms base3_countermodel
#print axioms baseThreeHalves_countermodel
#print axioms basePhi_countermodel
#print axioms generator_two_not_derivable
#print axioms free_history_realization_iff_binary_gain_bridge
#print axioms jcost_eq_quarter_iff_two
#print axioms history_gain_quarter_triangle

end
end RSDeltaBaseCountermodel
end Physicality
end ActualMathematics

/-
  PrimitiveRecognitionCalculus/Rigidity/LedgerTransport.lean

  THE TRANSPORT LEMMA (the panel's kill test for the Universal Ledger route):
  moving a kernel-certified theorem along the unique isomorphism from the δ-base
  to ANY Peano model costs ZERO posits. If this had failed (if re-expressing a
  FORCED theorem in an isomorphic carrier had required EM/LPO/MP or choice at
  the meta level), the forcing spectrum σ would have been encoding-relative and
  the absoluteness program dead on arrival. It passes.

  What is proved, concretely:

  * The δ-kernel's canonical model ℕ is itself a Peano δ-algebra, and the map
    from the δ-base `DistinctionNat` to ℕ is bijective (`base_to_nat_bijective`):
    the kernel's choice of ℕ as its semantic carrier is an instance of the
    rigidity theorem, not an encoding commitment.
  * For any δ-algebra M, `natRec M : ℕ → M.carrier` is the transport map; it is
    injective and surjective whenever M is Peano, choice-free, and it commutes
    with the base recursor (`natRec_baseRec`: the coherence triangle, an instance
    of initiality's uniqueness).
  * `msat M` re-reads every kernel formula IN M: atomic equalities become
    equalities of M-elements, quantifiers range over M.carrier (certified by
    ℕ-witnesses through the transport map; for Peano M the witnesses cover all
    of M, `msat_all_covers`, so nothing is vacuous).
  * `transport_forced`: a FORCED derivation (empty ledger) is true in the
    M-semantics of EVERY Peano model, with no metatheoretic principle beyond the
    forced fragment. `transport_graded`: the graded version — an accepted
    derivation with ledger O is true in every Peano model under EXACTLY the
    gates `Gated O`, no more. The ledger is untouched by transport.
  * Instance: the Gödel-test theorem (`∀x∀y, x+y=y+x`, FORCED @ QF-IND) holds in
    every Peano model, transported at zero cost (`addComm_transported`).

  STATUS: THEOREM. Axiom audits at the bottom; expected footprint is a subset of
  {propext, Quot.sound}, with no Classical.choice. The design point that makes
  this choice-free: `msat` never inverts the transport map (an inverse
  M.carrier → ℕ cannot be extracted choice-free in general); quantifier
  witnesses travel FORWARD along `natRec` only.

  No project-local axioms. No sorry.
-/

import Mathlib
import ActualMathematics.DeltaKernel.GodelTest
import ActualMathematics.Rigidity.BaseInitiality

namespace ActualMathematics
namespace Rigidity

open ActualMathematics.DeltaKernel

/-! ## ℕ as a δ-algebra, and the transport map -/

/-- The kernel's canonical semantic carrier ℕ, as a δ-algebra. -/
def natAlgebra : DeltaAlgebra where
  carrier := Nat
  zero := 0
  succ := Nat.succ

/-- ℕ is a Peano model of distinction. -/
theorem natAlgebra_peano : IsPeanoModel natAlgebra where
  succ_injective := fun _ _ h => Nat.succ.inj h
  zero_not_succ := fun x h => Nat.succ_ne_zero x h
  induction := fun _ h0 hs x => Nat.rec h0 (fun n ih => hs n ih) x

/-- The kernel's canonical model IS the δ-base up to the (unique) iso: the base
recursor into ℕ is bijective. Reading ℕ as "the" model is licensed by rigidity,
not by an encoding choice. -/
theorem base_to_nat_bijective : Function.Bijective (baseRec natAlgebra) :=
  ⟨baseRec_injective natAlgebra natAlgebra_peano,
   baseRec_surjective natAlgebra natAlgebra_peano⟩

/-- The transport map from the canonical model into any δ-algebra: unroll `n`
distinction steps in `M`. -/
def natRec (M : DeltaAlgebra) : Nat → M.carrier
  | 0 => M.zero
  | n + 1 => M.succ (natRec M n)

/-- Coherence triangle (initiality's uniqueness in action): transporting the
δ-base through ℕ agrees with the direct base recursor. -/
theorem natRec_baseRec (M : DeltaAlgebra) :
    ∀ n : DistinctionNat, natRec M (baseRec natAlgebra n) = baseRec M n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg M.succ ih

/-- The transport map into a Peano model is injective. Choice-free. -/
theorem natRec_injective (M : DeltaAlgebra) (h : IsPeanoModel M) :
    Function.Injective (natRec M) := by
  intro a
  induction a with
  | zero =>
      intro b he
      cases b with
      | zero => rfl
      | succ b => exact absurd he.symm (h.zero_not_succ (natRec M b))
  | succ a ih =>
      intro b he
      cases b with
      | zero => exact absurd he (h.zero_not_succ (natRec M a))
      | succ b => exact congrArg Nat.succ (ih (h.succ_injective he))

/-- The transport map into a Peano model is surjective (the model's own
induction schema). Choice-free. -/
theorem natRec_surjective (M : DeltaAlgebra) (h : IsPeanoModel M) :
    Function.Surjective (natRec M) := by
  intro y
  refine h.induction (fun y => ∃ n, natRec M n = y) ⟨0, rfl⟩ ?_ y
  rintro x ⟨n, rfl⟩
  exact ⟨n + 1, rfl⟩

/-! ## Kernel satisfaction transported into M

`msat M ρ φ` re-reads the kernel formula `φ` in the carrier of `M`: atomic
equalities are equalities of M-elements (through the transport map), and
quantifiers range over `M.carrier`, certified by ℕ-witnesses. Witnesses only
ever travel FORWARD along `natRec M`; no inverse is used anywhere, which is what
keeps the whole construction choice-free. -/
def msat (M : DeltaAlgebra) : Env → DFormula → Prop
  | ρ, .eq t s => natRec M (t.eval ρ) = natRec M (s.eval ρ)
  | _, .fls => False
  | ρ, .conj a b => msat M ρ a ∧ msat M ρ b
  | ρ, .disj a b => msat M ρ a ∨ msat M ρ b
  | ρ, .impl a b => msat M ρ a → msat M ρ b
  | ρ, .all a => ∀ x : M.carrier, ∀ n : Nat, natRec M n = x → msat M (Env.cons n ρ) a
  | ρ, .ex a => ∃ x : M.carrier, ∃ n : Nat, natRec M n = x ∧ msat M (Env.cons n ρ) a

/-- **The Transport Lemma.** For a Peano model M, satisfaction transported into
M coincides with satisfaction in the canonical model, formula by formula.
Injectivity of the transport map handles the atoms; quantifier witnesses travel
forward. Choice-free. -/
theorem msat_iff_sat (M : DeltaAlgebra) (hM : IsPeanoModel M) :
    ∀ (φ : DFormula) (ρ : Env), msat M ρ φ ↔ DFormula.sat ρ φ := by
  intro φ
  induction φ with
  | eq t s =>
      intro ρ
      simp only [msat, DFormula.sat]
      exact ⟨fun h => natRec_injective M hM h, fun h => congrArg (natRec M) h⟩
  | fls => intro ρ; exact Iff.rfl
  | conj a b iha ihb =>
      intro ρ
      simp only [msat, DFormula.sat]
      exact and_congr (iha ρ) (ihb ρ)
  | disj a b iha ihb =>
      intro ρ
      simp only [msat, DFormula.sat]
      exact or_congr (iha ρ) (ihb ρ)
  | impl a b iha ihb =>
      intro ρ
      simp only [msat, DFormula.sat]
      exact imp_congr (iha ρ) (ihb ρ)
  | all a ih =>
      intro ρ
      simp only [msat, DFormula.sat]
      constructor
      · intro h n
        exact (ih (Env.cons n ρ)).mp (h (natRec M n) n rfl)
      · intro h x n _
        exact (ih (Env.cons n ρ)).mpr (h n)
  | ex a ih =>
      intro ρ
      simp only [msat, DFormula.sat]
      constructor
      · rintro ⟨_, n, _, h⟩
        exact ⟨n, (ih (Env.cons n ρ)).mp h⟩
      · rintro ⟨n, h⟩
        exact ⟨natRec M n, n, rfl, (ih (Env.cons n ρ)).mpr h⟩

/-- Non-vacuity of the transported universal: in a Peano model, EVERY element of
the carrier is reached by a witness, so `msat`'s guarded ∀ genuinely constrains
all of M. (Surjectivity is exactly what a Peano model adds here.) -/
theorem msat_all_covers (M : DeltaAlgebra) (hM : IsPeanoModel M)
    {a : DFormula} {ρ : Env} (h : msat M ρ (.all a)) (x : M.carrier) :
    ∃ n, natRec M n = x ∧ msat M (Env.cons n ρ) a := by
  obtain ⟨n, rfl⟩ := natRec_surjective M hM x
  exact ⟨n, rfl, h (natRec M n) n rfl⟩

/-! ## Zero-cost transport of kernel certificates -/

/-- **Kill test, FORCED case: PASS.** A derivation the kernel accepts with the
EMPTY ledger is true in the transported semantics of EVERY Peano model, with no
metatheoretic principle beyond the forced fragment. Transport along the unique
iso costs zero posits. -/
theorem transport_forced {d : Deriv} {φ : DFormula} (h : Forced [] d φ)
    (M : DeltaAlgebra) (hM : IsPeanoModel M) (ρ : Env) : msat M ρ φ :=
  (msat_iff_sat M hM φ ρ).mpr (sound_forced h ρ)

/-- **Kill test, graded case: PASS.** An accepted derivation with ledger `O` is
true in every Peano model under EXACTLY the gates `Gated O` the canonical
soundness theorem already demanded. Transport adds no gate: the ledger is
invariant under change of carrier. -/
theorem transport_graded {Γ : Ctx} {d : Deriv} {φ : DFormula} {O : Ledger}
    (h : check Γ d = some (φ, O)) (hG : Gated O)
    (M : DeltaAlgebra) (hM : IsPeanoModel M) (ρ : Env) (hΓ : CtxSat ρ Γ) :
    msat M ρ φ :=
  (msat_iff_sat M hM φ ρ).mpr (sound_cond d Γ φ O h hG ρ hΓ)

/-- Instance: the Gödel-test theorem (commutativity of distinction-composition,
FORCED @ QF-IND) holds in every Peano model, at zero transported cost. -/
theorem addComm_transported (M : DeltaAlgebra) (hM : IsPeanoModel M) (ρ : Env) :
    msat M ρ (.all (.all GodelTest.commFormula)) :=
  transport_forced GodelTest.addComm_forced M hM ρ

/-! ## Choice-freeness audits

The verdict of the kill test is the axiom footprint: transport must consume
NOTHING beyond the forced fragment's own basis (⊆ {propext, Quot.sound}; in
particular no `Classical.choice`). -/

#print axioms msat_iff_sat
#print axioms transport_forced
#print axioms transport_graded
#print axioms addComm_transported

end Rigidity
end ActualMathematics

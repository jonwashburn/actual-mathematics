/-
  PrimitiveRecognitionCalculus/Rigidity/ChainWitnesses.lean

  THE FIRST INTERDERIVABILITY EDGE, DERIVED BY THE KERNEL ITSELF:
  every instance of LPO's conclusion schema is derivable consuming ONLY the EM
  posit — `ReducesTo {em} lpo`, uniformly in the matrix formula φ.

  This is the first half of `target_kernel_realizes_chain`
  (LedgerInitiality.lean). It is not a metatheoretic remark that "classically
  EM implies LPO": it is an explicit derivation-tree family `lpoFromEM φ` in
  the object calculus, accepted by `check` in the empty context with ledger
  exactly `ofEM`, for EVERY φ. The tree:

    implIntro (∀x (φ ∨ ¬φ))                 -- antecedent taken, never used
      disjElim (emPosit (∃x φ))             -- EM on ∃xφ: the ONE posit
        left  (∃x φ):   disjIntro1 — done
        right (¬∃x φ):  disjIntro2 (allIntro (implIntro φ
                          (implElim (hyp ¬∃xφ)
                            (exIntro φ↑ (var 0) (hyp φ)))))
                        -- from φ at the eigenvariable, witness ∃xφ,
                        -- contradict ¬∃xφ: so ¬φ everywhere.

  Note the EM instance is applied to `∃x φ`, NOT to the matrix φ the LPO
  instance is indexed by — exactly the cross-matrix freedom the panel confirmed
  `ReducesTo` must allow (it constrains posit KINDS via the ledger, not
  matrices). At instance grain (InstanceLedger.lean) the consumed instance is
  `(em, ∃x φ)`, which is precisely the information the instance-level Universal
  Ledger keeps and the Boolean chart forgets.

  The only non-computational checker condition is the binder-instantiation
  identity `(φ.lift 1 1).subst 0 (var 0) = φ` (introduce a fresh eigenvariable
  and immediately use it as the witness), proved here by structural induction
  (`term_subst_lift_self`, `formula_subst_lift_self`).

  The second half (MP-from-LPO) is deliberately NOT here: it needs the HA
  theorem `∀x (φ ∨ ¬φ)` for quantifier-free φ, whose minimal induction tier is
  the t₀ probe (panel LIVE BET 1) — loop-grade work, queued.

  STATUS: THEOREM (`lpo_reduces_to_em`, audited below; expected footprint ⊆
  {propext, Quot.sound}).

  No project-local axioms. No sorry.
-/

import Mathlib
import ActualMathematics.Rigidity.GraftCut

namespace ActualMathematics
namespace Rigidity

open ActualMathematics.DeltaKernel

/-! ## The binder-instantiation identity -/

/-- Lifting a term over a fresh variable at cutoff `k+1` and then substituting
`var k` back at `k` is the identity. -/
theorem term_subst_lift_self (k : Nat) :
    ∀ t : DTerm, DTerm.subst k (.var k) (t.lift 1 (k + 1)) = t
  | .var n => by
      by_cases h : n < k + 1
      · simp only [DTerm.lift, if_pos h, DTerm.subst]
        by_cases he : n = k
        · rw [if_pos he, he]
        · rw [if_neg he, if_neg (by omega : ¬ k < n)]
      · simp only [DTerm.lift, if_neg h, DTerm.subst]
        rw [if_neg (by omega : ¬ (n + 1 = k)),
          if_pos (by omega : k < n + 1), Nat.add_sub_cancel]
  | .zero => rfl
  | .succ t => by
      simp only [DTerm.lift, DTerm.subst, term_subst_lift_self k t]
  | .add t s => by
      simp only [DTerm.lift, DTerm.subst,
        term_subst_lift_self k t, term_subst_lift_self k s]
  | .mul t s => by
      simp only [DTerm.lift, DTerm.subst,
        term_subst_lift_self k t, term_subst_lift_self k s]

/-- Formula version: `(φ.lift 1 (k+1)).subst k (var k) = φ`. At `k = 0` this
is the eigenvariable-as-witness identity the LPO derivation needs. -/
theorem formula_subst_lift_self :
    ∀ (φ : DFormula) (k : Nat),
      DFormula.subst k (.var k) (φ.lift 1 (k + 1)) = φ
  | .eq t s, k => by
      simp only [DFormula.lift, DFormula.subst, term_subst_lift_self]
  | .fls, _ => rfl
  | .conj a b, k => by
      simp only [DFormula.lift, DFormula.subst,
        formula_subst_lift_self a k, formula_subst_lift_self b k]
  | .disj a b, k => by
      simp only [DFormula.lift, DFormula.subst,
        formula_subst_lift_self a k, formula_subst_lift_self b k]
  | .impl a b, k => by
      simp only [DFormula.lift, DFormula.subst,
        formula_subst_lift_self a k, formula_subst_lift_self b k]
  | .all a, k => by
      simp only [DFormula.lift, DFormula.subst]
      have hv : (DTerm.var k).lift 1 0 = .var (k + 1) := by
        simp only [DTerm.lift, if_neg (Nat.not_lt_zero k)]
      rw [hv, formula_subst_lift_self a (k + 1)]
  | .ex a, k => by
      simp only [DFormula.lift, DFormula.subst]
      have hv : (DTerm.var k).lift 1 0 = .var (k + 1) := by
        simp only [DTerm.lift, if_neg (Nat.not_lt_zero k)]
      rw [hv, formula_subst_lift_self a (k + 1)]

/-- The instance the checker meets: introduce a fresh eigenvariable, use it as
the existential witness. -/
theorem subst0_lift11 (φ : DFormula) :
    DFormula.subst 0 (.var 0) (φ.lift 1 1) = φ :=
  formula_subst_lift_self φ 0

/-! ## The derivation family -/

/-- The LPO instance at matrix `φ`, derived from ONE EM posit (on `∃x φ`). -/
def lpoFromEM (φ : DFormula) : Deriv :=
  .implIntro (.all (.disj φ φ.neg))
    (.disjElim (.emPosit (.ex φ))
      (.disjIntro1 (.all φ.neg) (.hyp 0))
      (.disjIntro2 (.ex φ)
        (.allIntro
          (.implIntro φ
            (.implElim (.hyp 1)
              (.exIntro (φ.lift 1 1) (.var 0) (.hyp 0)))))))

/-- The kernel accepts `lpoFromEM φ` in the empty context, concluding exactly
the LPO schema at `φ`, with ledger exactly `ofEM`: one EM posit, nothing else. -/
theorem lpoFromEM_check (φ : DFormula) :
    check [] (lpoFromEM φ) =
      some (.impl (.all (.disj φ φ.neg)) (.disj (.ex φ) (.all φ.neg)),
        Ledger.ofEM) := by
  simp only [lpoFromEM, check, DFormula.neg, DFormula.lift, DTerm.lift,
    List.map_cons, List.map_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    subst0_lift11, eq_self_iff_true, if_true,
    Ledger.union, Ledger.ofEM, Ledger.empty,
    Bool.or_false, Bool.false_or, Bool.true_or, Bool.or_true]

/-- **The first chain edge, kernel-derived.** Every LPO instance reduces to the
EM posit alone: `ReducesTo {em} lpo`. First half of
`target_kernel_realizes_chain`. -/
theorem lpo_reduces_to_em :
    ReducesTo (fun Q => decide (Q = Posit.em)) Posit.lpo := by
  intro φ ψ h
  simp only [Posit.concl, Option.some.injEq] at h
  subst h
  refine ⟨lpoFromEM φ, Ledger.ofEM, lpoFromEM_check φ, ?_⟩
  intro Q hQ
  revert hQ
  cases Q <;> decide

/-- Corollary via graft/cut: anything reducible to `{em, lpo}` is already
reducible to `{em}` — the LPO generator is redundant in the presence of EM. -/
theorem reduces_em_lpo_to_em {P : Posit}
    (h : ReducesTo (fun Q => decide (Q = Posit.em ∨ Q = Posit.lpo)) P) :
    ReducesTo (fun Q => decide (Q = Posit.em)) P := by
  refine reducesTo_trans h ?_
  intro Q hQ
  cases Q with
  | em => exact reducesTo_self Posit.em
  | lpo => exact lpo_reduces_to_em
  | mp => exact absurd hQ (by decide)

/-! ## Audits -/

#print axioms lpoFromEM_check
#print axioms lpo_reduces_to_em
#print axioms reduces_em_lpo_to_em

end Rigidity
end ActualMathematics

/-
  PrimitiveRecognitionCalculus/Rigidity/InstanceLedger.lean

  THE INSTANCE-LEVEL UNIVERSAL LEDGER, LATENT FORM (panel-greenlit 2026-07-04).

  The panel's ruling on the Universal Ledger program: the schema-level chain
  (LedgerInitiality.lean) can never be the canonical codomain of σ, because a
  free object on posit NAMES is functorial in the alphabet — extend the
  alphabet by LLPO and the 4-chain provably shifts to a non-chain lattice,
  failing the program's own falsifier. The canonical codomain must have
  FORMULAS as elements, not posit names: grade each certificate by the class
  of the actual posit INSTANCES it consumed. Then alphabet extension adds
  nothing (LLPO instances are already formulas), and the Boolean ledger and
  the 4-chain are demoted to charts.

  The decisive observation (the "latent architecture" repair): the kernel
  already carries the instance data. A `Deriv` tree records every posit leaf
  together with its matrix formula; only `check`'s Boolean ledger forgets the
  matrices. So the instance ledger needs NO kernel surgery — it is a fold over
  the same tree the kernel already audits:

    `usedInstances : Deriv → Multiset (Posit × DFormula)`

  This file delivers the panel's confirm-or-kill, both halves:

  * THEOREM `check_support` (the coherence lemma): if `check Γ d = some (φ, O)`
    then the Boolean ledger `O` is EXACTLY the support projection of
    `usedInstances d` — a posit flag is set iff some instance of that posit
    occurs in the multiset. The Boolean ledger is tree-local; the instance
    ledger refines it conservatively. Had this failed, the instance route
    would have required real kernel surgery.
  * THEOREM `emTriv_two_price` (the two-price certificate): the theorem
    `0=0 ∨ ¬(0=0)` has an accepted certificate whose Boolean chart says `em`
    (one EM instance consumed, on the decidable matrix `0=0`) AND an accepted
    certificate with the EMPTY ledger. So the instance consumed by the first
    certificate is dischargeable at zero cost, and any grading that prices the
    theorem by the Boolean chart of a single certificate overstates. σ at the
    instance level (min over certificates, instances weighed by their own
    dischargeability) sees ⊥ where the chart says `em`. This is the LLPO
    overstatement reproduced inside the current alphabet, at instance grain —
    the motivating defect, now a machine-checked example instead of an
    informal complaint.

  Multiplicity note: `usedInstances` is a MULTISET, so consuming EM twice is
  recorded twice. The idempotent Boolean ledger is its support quotient
  (`check_support`); pricing-by-support vs pricing-by-multiplicity becomes a
  choice of chart on one latent object, not a design commitment (the panel's
  resolution of the idempotence dispute).

  OPEN (next in queue, per panel sequencing): the graft/cut lemma making
  `ReducesTo` transitive (splice a derivation of a posit instance for its
  leaf, ledgers union, `check` stable); then the LPO-from-EM witness; then
  MP-from-LPO with the QF-decidability helper (whose minimal induction tier
  is the t₀ probe for the tier-indexed free object).

  No project-local axioms. No sorry.
-/

import Mathlib
import ActualMathematics.Rigidity.LedgerInitiality

namespace ActualMathematics
namespace Rigidity

open ActualMathematics.DeltaKernel

/-! ## The instance fold (latent in every derivation tree) -/

/-- The multiset of posit INSTANCES a derivation consumes: each posit leaf
contributes its posit name paired with the matrix formula it was applied to.
This is the data the Boolean ledger forgets. No kernel change: a fold over the
same tree `check` audits. -/
def usedInstances : Deriv → Multiset (Posit × DFormula)
  | .hyp _ => 0
  | .eqRefl _ => 0
  | .eqSubst _ _ _ d₁ d₂ => usedInstances d₁ + usedInstances d₂
  | .succNeZero _ => 0
  | .succInj d => usedInstances d
  | .addZero _ => 0
  | .addSucc _ _ => 0
  | .mulZero _ => 0
  | .mulSucc _ _ => 0
  | .ind _ d₀ dS => usedInstances d₀ + usedInstances dS
  | .implIntro _ d => usedInstances d
  | .implElim d₁ d₂ => usedInstances d₁ + usedInstances d₂
  | .conjIntro d₁ d₂ => usedInstances d₁ + usedInstances d₂
  | .conjElim1 d => usedInstances d
  | .conjElim2 d => usedInstances d
  | .disjIntro1 _ d => usedInstances d
  | .disjIntro2 _ d => usedInstances d
  | .disjElim d dL dR => usedInstances d + usedInstances dL + usedInstances dR
  | .flsElim _ d => usedInstances d
  | .allIntro d => usedInstances d
  | .allElim _ d => usedInstances d
  | .exIntro _ _ d => usedInstances d
  | .exElim _ d dBody => usedInstances d + usedInstances dBody
  | .emPosit φ => {(Posit.em, φ)}
  | .lpoPosit φ => {(Posit.lpo, φ)}
  | .mpPosit φ => {(Posit.mp, φ)}

/-- A posit name occurs in an instance multiset. -/
def HasPosit (m : Multiset (Posit × DFormula)) (P : Posit) : Prop :=
  ∃ ψ : DFormula, (P, ψ) ∈ m

@[simp] theorem hasPosit_zero (P : Posit) : HasPosit 0 P ↔ False := by
  simp [HasPosit]

@[simp] theorem hasPosit_add (m n : Multiset (Posit × DFormula)) (P : Posit) :
    HasPosit (m + n) P ↔ HasPosit m P ∨ HasPosit n P := by
  simp [HasPosit, Multiset.mem_add, exists_or]

@[simp] theorem hasPosit_singleton (Q : Posit) (χ : DFormula) (P : Posit) :
    HasPosit {(Q, χ)} P ↔ P = Q := by
  simp [HasPosit, Prod.ext_iff]

/-! ## Ledger support algebra -/

@[simp] theorem ledgerUses_empty (P : Posit) :
    ledgerUses Ledger.empty P = false := by
  cases P <;> rfl

@[simp] theorem ledgerUses_union (a b : Ledger) (P : Posit) :
    ledgerUses (a.union b) P = (ledgerUses a P || ledgerUses b P) := by
  cases P <;> rfl

/-- The induction-tier branch of `check`'s `ind` rule never touches the posit
flags: either way the posit support is the union of the sub-supports. -/
theorem ledgerUses_indTier (o₁ o₂ : Ledger) (b : Bool) (P : Posit) :
    ledgerUses (if b then o₁.union o₂ else (o₁.union o₂).union Ledger.ofIndFull) P
      = (ledgerUses o₁ P || ledgerUses o₂ P) := by
  cases b <;> cases P <;> simp [Ledger.union, Ledger.ofIndFull, ledgerUses]

/-! ## The coherence lemma (confirm half of the confirm-or-kill) -/

/-- **Support agreement.** The Boolean ledger `check` co-computes is exactly
the support projection of the instance multiset: a posit flag is set iff some
instance of that posit occurs in the tree. So the instance ledger is a
conservative refinement of the kernel's ledger — no kernel surgery needed for
the instance-level Universal Ledger. -/
theorem check_support (d : Deriv) : ∀ (Γ : Ctx) (φ : DFormula) (O : Ledger),
    check Γ d = some (φ, O) →
    ∀ P : Posit, (ledgerUses O P = true ↔ HasPosit (usedInstances d) P) := by
  induction d with
  | hyp i =>
      intro Γ φ O h P
      simp only [check] at h
      split at h
      next ψ heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simp [usedInstances]
      all_goals nomatch h
  | eqRefl t =>
      intro Γ φ O h P
      simp only [check, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp [usedInstances]
  | eqSubst φf t s d₁ d₂ ih₁ ih₂ =>
      intro Γ φ O h P
      simp only [check] at h
      split at h
      next cEq o₁ cT o₂ heq₁ heq₂ =>
        split at h
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            simp only [usedInstances, ledgerUses_union, Bool.or_eq_true, hasPosit_add]
            exact or_congr (ih₁ _ _ _ heq₁ P) (ih₂ _ _ _ heq₂ P)
          · nomatch h
        · nomatch h
      all_goals nomatch h
  | succNeZero t =>
      intro Γ φ O h P
      simp only [check, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp [usedInstances]
  | succInj d ih =>
      intro Γ φ O h P
      simp only [check] at h
      split at h
      next t s o heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simpa [usedInstances] using ih _ _ _ heq P
      all_goals nomatch h
  | addZero t =>
      intro Γ φ O h P
      simp only [check, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp [usedInstances]
  | addSucc t s =>
      intro Γ φ O h P
      simp only [check, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp [usedInstances]
  | mulZero t =>
      intro Γ φ O h P
      simp only [check, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp [usedInstances]
  | mulSucc t s =>
      intro Γ φ O h P
      simp only [check, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp [usedInstances]
  | ind φf d₀ dS ih₀ ihS =>
      intro Γ φ O h P
      simp only [check] at h
      split at h
      next c₀ o₁ cS o₂ heq₀ heqS =>
        split at h
        · split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            rw [ledgerUses_indTier]
            simp only [usedInstances, Bool.or_eq_true, hasPosit_add]
            exact or_congr (ih₀ _ _ _ heq₀ P) (ihS _ _ _ heqS P)
          · nomatch h
        · nomatch h
      all_goals nomatch h
  | implIntro φf d ih =>
      intro Γ φ O h P
      simp only [check] at h
      split at h
      next ψ o heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simpa [usedInstances] using ih _ _ _ heq P
      all_goals nomatch h
  | implElim d₁ d₂ ih₁ ih₂ =>
      intro Γ φ O h P
      simp only [check] at h
      split at h
      next φf ψ o₁ φ' o₂ heq₁ heq₂ =>
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          simp only [usedInstances, ledgerUses_union, Bool.or_eq_true, hasPosit_add]
          exact or_congr (ih₁ _ _ _ heq₁ P) (ih₂ _ _ _ heq₂ P)
        · nomatch h
      all_goals nomatch h
  | conjIntro d₁ d₂ ih₁ ih₂ =>
      intro Γ φ O h P
      simp only [check] at h
      split at h
      next φf o₁ ψ o₂ heq₁ heq₂ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simp only [usedInstances, ledgerUses_union, Bool.or_eq_true, hasPosit_add]
        exact or_congr (ih₁ _ _ _ heq₁ P) (ih₂ _ _ _ heq₂ P)
      all_goals nomatch h
  | conjElim1 d ih =>
      intro Γ φ O h P
      simp only [check] at h
      split at h
      next φf ψ o heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simpa [usedInstances] using ih _ _ _ heq P
      all_goals nomatch h
  | conjElim2 d ih =>
      intro Γ φ O h P
      simp only [check] at h
      split at h
      next φf ψ o heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simpa [usedInstances] using ih _ _ _ heq P
      all_goals nomatch h
  | disjIntro1 ψ d ih =>
      intro Γ φ O h P
      simp only [check] at h
      split at h
      next φf o heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simpa [usedInstances] using ih _ _ _ heq P
      all_goals nomatch h
  | disjIntro2 φf d ih =>
      intro Γ φ O h P
      simp only [check] at h
      split at h
      next ψ o heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simpa [usedInstances] using ih _ _ _ heq P
      all_goals nomatch h
  | disjElim d dL dR ih ihL ihR =>
      intro Γ φ O h P
      simp only [check] at h
      split at h
      next φf ψf o heq =>
        split at h
        next χ₁ o₁ χ₂ o₂ heqL heqR =>
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            simp only [usedInstances, ledgerUses_union, Bool.or_eq_true, hasPosit_add]
            exact or_congr (or_congr (ih _ _ _ heq P) (ihL _ _ _ heqL P)) (ihR _ _ _ heqR P)
          · nomatch h
        all_goals nomatch h
      all_goals nomatch h
  | flsElim φf d ih =>
      intro Γ φ O h P
      simp only [check] at h
      split at h
      next o heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simpa [usedInstances] using ih _ _ _ heq P
      all_goals nomatch h
  | allIntro d ih =>
      intro Γ φ O h P
      simp only [check] at h
      split at h
      next φf o heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simpa [usedInstances] using ih _ _ _ heq P
      all_goals nomatch h
  | allElim t d ih =>
      intro Γ φ O h P
      simp only [check] at h
      split at h
      next φf o heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simpa [usedInstances] using ih _ _ _ heq P
      all_goals nomatch h
  | exIntro φf t d ih =>
      intro Γ φ O h P
      simp only [check] at h
      split at h
      next c o heq =>
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          simpa [usedInstances] using ih _ _ _ heq P
        · nomatch h
      all_goals nomatch h
  | exElim ψ d dBody ih ihBody =>
      intro Γ φ O h P
      simp only [check] at h
      split at h
      next φf o heq =>
        split at h
        next ψ' o₂ heqB =>
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨-, rfl⟩ := h
            simp only [usedInstances, ledgerUses_union, Bool.or_eq_true, hasPosit_add]
            exact or_congr (ih _ _ _ heq P) (ihBody _ _ _ heqB P)
          · nomatch h
        all_goals nomatch h
      all_goals nomatch h
  | emPosit φf =>
      intro Γ φ O h P
      simp only [check, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      cases P <;> simp [usedInstances, ledgerUses, Ledger.ofEM]
  | lpoPosit φf =>
      intro Γ φ O h P
      simp only [check, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      cases P <;> simp [usedInstances, ledgerUses, Ledger.ofLPO]
  | mpPosit φf =>
      intro Γ φ O h P
      simp only [check] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        cases P <;> simp [usedInstances, ledgerUses, Ledger.ofMP]
      · nomatch h

/-! ## The two-price certificate (kill half of the confirm-or-kill: the chart
overstates, machine-checked) -/

/-- The decidable tautology `0 = 0 ∨ ¬(0 = 0)`. -/
def emTrivFormula : DFormula :=
  .disj (.eq .zero .zero) ((DFormula.eq .zero .zero).neg)

/-- Certificate 1: conclude it by POSITING excluded middle on `0 = 0`. -/
def emTrivPosited : Deriv := .emPosit (.eq .zero .zero)

/-- Certificate 2: conclude it FORCED — left injection of reflexivity. -/
def emTrivForced : Deriv :=
  .disjIntro1 ((DFormula.eq .zero .zero).neg) (.eqRefl .zero)

/-- **Two prices for one theorem.** The posited certificate is accepted with
Boolean chart `em`; the forced certificate is accepted with the EMPTY ledger.
So the single instance `(em, 0=0)` consumed by certificate 1 is dischargeable
at zero cost, and a σ that reads one certificate's Boolean chart overstates
the theorem's price. The instance-level ledger sees this; the Boolean chart
cannot. -/
theorem emTriv_two_price :
    check [] emTrivPosited = some (emTrivFormula, Ledger.ofEM) ∧
    check [] emTrivForced = some (emTrivFormula, Ledger.empty) :=
  ⟨rfl, rfl⟩

/-- The instance content of the posited certificate, explicitly: exactly one
EM instance, on the matrix `0 = 0`. -/
theorem emTrivPosited_instances :
    usedInstances emTrivPosited = {(Posit.em, .eq .zero .zero)} := rfl

/-- The forced certificate consumes no instances at all. -/
theorem emTrivForced_instances : usedInstances emTrivForced = 0 := rfl

/-! ## Audits -/

#print axioms check_support
#print axioms emTriv_two_price

end Rigidity
end ActualMathematics

/-
  PrimitiveRecognitionCalculus/Rigidity/GraftCut.lean

  THE GRAFT/CUT LEMMA: `ReducesTo` is transitive, so it is a genuine preorder.

  The panel's honesty flag on the Universal Ledger scaffold (2026-07-04): only
  reflexivity of `ReducesTo` was proved, so calling it a "preorder" and talking
  about quotients was unlicensed. This file discharges the flag with the two
  metatheorems the splice argument needs:

  * `check_append` (weakening): a derivation accepted in context `Γ` is
    accepted, with the SAME formula and the SAME ledger, in `Γ ++ Δ`. In
    particular a closed certificate is accepted in every context
    (`check_closed_any`). Ledger-invariance matters: weakening is free.
  * `splice` (graft/cut): if a derivation is accepted with a ledger inside
    posit set `S`, and every posit of `S` reduces to posit set `T`, then the
    SAME formula has a derivation accepted with a ledger inside `T` — replace
    each posit leaf by a `T`-certificate of its instance (weakened into the
    leaf's context) and rebuild the tree rule by rule. The construction is
    existence-style (the grafted tree is assembled inside the proof), so no
    choice principle is consumed extracting certificates from `ReducesTo`.
  * `reducesTo_trans`: transitivity, directly from `splice` at the empty
    context. With `reducesTo_self` (LedgerInitiality.lean) the
    kernel-interderivability relation is now a PREORDER, THEOREM-grade.

  STATUS: THEOREM. Audits at the bottom; expected footprint ⊆
  {propext, Quot.sound}, no Classical.choice.

  No project-local axioms. No sorry.
-/

import Mathlib
import ActualMathematics.Rigidity.InstanceLedger

namespace ActualMathematics
namespace Rigidity

open ActualMathematics.DeltaKernel

/-! ## Ledger `within` algebra -/

theorem ledgerWithin_empty (S : PositSet) : ledgerWithin Ledger.empty S := by
  intro P hP
  rw [ledgerUses_empty] at hP
  exact absurd hP (by decide)

theorem ledgerWithin_or {a b : Ledger} {S : PositSet} :
    ledgerWithin (a.union b) S ↔ (ledgerWithin a S ∧ ledgerWithin b S) := by
  constructor
  · intro h
    refine ⟨fun P hP => h P ?_, fun P hP => h P ?_⟩ <;>
      simp [ledgerUses_union, hP]
  · rintro ⟨h₁, h₂⟩ P hP
    rw [ledgerUses_union] at hP
    rcases (Bool.or_eq_true _ _).mp hP with h | h
    · exact h₁ P h
    · exact h₂ P h

theorem ledgerWithin_ofIndFull (S : PositSet) :
    ledgerWithin Ledger.ofIndFull S := by
  intro P hP
  cases P <;> exact absurd hP (by decide)

/-- The induction-tier branch is transparent to `within`: posit content is the
two sub-ledgers either way. -/
theorem ledgerWithin_indTier {o₁ o₂ : Ledger} (b : Bool) {S : PositSet} :
    ledgerWithin (if b then o₁.union o₂ else (o₁.union o₂).union Ledger.ofIndFull) S ↔
      (ledgerWithin o₁ S ∧ ledgerWithin o₂ S) := by
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [ledgerWithin_or, ledgerWithin_or]
    exact ⟨fun h => h.1, fun h => ⟨h, ledgerWithin_ofIndFull S⟩⟩
  · simp only [if_true]
    exact ledgerWithin_or

/-! ## Weakening -/

/-- **Weakening.** A derivation accepted in `Γ` is accepted in `Γ ++ Δ`, same
formula, same ledger. Hypothesis indices are untouched (appending extends the
context on the far side); every other rule is context-functorial. -/
theorem check_append (d : Deriv) : ∀ (Γ Δ : Ctx) (φ : DFormula) (O : Ledger),
    check Γ d = some (φ, O) → check (Γ ++ Δ) d = some (φ, O) := by
  induction d with
  | hyp i =>
      intro Γ Δ φ O h
      simp only [check] at h ⊢
      split at h
      next ψ heq =>
        have hlt : i < Γ.length := by
          rcases List.getElem?_eq_some_iff.mp heq with ⟨hl, -⟩
          exact hl
        rw [List.getElem?_append_left hlt, heq]
        exact h
      all_goals nomatch h
  | eqRefl t => intro Γ Δ φ O h; exact h
  | eqSubst φf t s d₁ d₂ ih₁ ih₂ =>
      intro Γ Δ φ O h
      simp only [check] at h ⊢
      split at h
      next cEq o₁ cT o₂ heq₁ heq₂ =>
        rw [ih₁ Γ Δ _ _ heq₁, ih₂ Γ Δ _ _ heq₂]
        exact h
      all_goals nomatch h
  | succNeZero t => intro Γ Δ φ O h; exact h
  | succInj d ih =>
      intro Γ Δ φ O h
      simp only [check] at h ⊢
      split at h
      next t s o heq =>
        rw [ih Γ Δ _ _ heq]
        exact h
      all_goals nomatch h
  | addZero t => intro Γ Δ φ O h; exact h
  | addSucc t s => intro Γ Δ φ O h; exact h
  | mulZero t => intro Γ Δ φ O h; exact h
  | mulSucc t s => intro Γ Δ φ O h; exact h
  | ind φf d₀ dS ih₀ ihS =>
      intro Γ Δ φ O h
      simp only [check] at h ⊢
      split at h
      next c₀ o₁ cS o₂ heq₀ heqS =>
        rw [ih₀ Γ Δ _ _ heq₀, ihS Γ Δ _ _ heqS]
        exact h
      all_goals nomatch h
  | implIntro φf d ih =>
      intro Γ Δ φ O h
      simp only [check] at h ⊢
      split at h
      next ψ o heq =>
        have := ih (φf :: Γ) Δ _ _ heq
        rw [List.cons_append] at this
        rw [this]
        exact h
      all_goals nomatch h
  | implElim d₁ d₂ ih₁ ih₂ =>
      intro Γ Δ φ O h
      simp only [check] at h ⊢
      split at h
      next φf ψ o₁ φ' o₂ heq₁ heq₂ =>
        rw [ih₁ Γ Δ _ _ heq₁, ih₂ Γ Δ _ _ heq₂]
        exact h
      all_goals nomatch h
  | conjIntro d₁ d₂ ih₁ ih₂ =>
      intro Γ Δ φ O h
      simp only [check] at h ⊢
      split at h
      next φf o₁ ψ o₂ heq₁ heq₂ =>
        rw [ih₁ Γ Δ _ _ heq₁, ih₂ Γ Δ _ _ heq₂]
        exact h
      all_goals nomatch h
  | conjElim1 d ih =>
      intro Γ Δ φ O h
      simp only [check] at h ⊢
      split at h
      next φf ψ o heq =>
        rw [ih Γ Δ _ _ heq]
        exact h
      all_goals nomatch h
  | conjElim2 d ih =>
      intro Γ Δ φ O h
      simp only [check] at h ⊢
      split at h
      next φf ψ o heq =>
        rw [ih Γ Δ _ _ heq]
        exact h
      all_goals nomatch h
  | disjIntro1 ψ d ih =>
      intro Γ Δ φ O h
      simp only [check] at h ⊢
      split at h
      next φf o heq =>
        rw [ih Γ Δ _ _ heq]
        exact h
      all_goals nomatch h
  | disjIntro2 φf d ih =>
      intro Γ Δ φ O h
      simp only [check] at h ⊢
      split at h
      next ψ o heq =>
        rw [ih Γ Δ _ _ heq]
        exact h
      all_goals nomatch h
  | disjElim d dL dR ih ihL ihR =>
      intro Γ Δ φ O h
      simp only [check] at h ⊢
      split at h
      next φf ψf o heq =>
        split at h
        next χ₁ o₁ χ₂ o₂ heqL heqR =>
          have hL := ihL (φf :: Γ) Δ _ _ heqL
          have hR := ihR (ψf :: Γ) Δ _ _ heqR
          rw [List.cons_append] at hL hR
          simp only [check, ih Γ Δ _ _ heq, hL, hR]
          exact h
        all_goals nomatch h
      all_goals nomatch h
  | flsElim φf d ih =>
      intro Γ Δ φ O h
      simp only [check] at h ⊢
      split at h
      next o heq =>
        rw [ih Γ Δ _ _ heq]
        exact h
      all_goals nomatch h
  | allIntro d ih =>
      intro Γ Δ φ O h
      simp only [check] at h ⊢
      split at h
      next φf o heq =>
        have := ih (Γ.map (DFormula.lift 1 0)) (Δ.map (DFormula.lift 1 0)) _ _ heq
        rw [← List.map_append] at this
        simp only [check, this]
        exact h
      all_goals nomatch h
  | allElim t d ih =>
      intro Γ Δ φ O h
      simp only [check] at h ⊢
      split at h
      next φf o heq =>
        rw [ih Γ Δ _ _ heq]
        exact h
      all_goals nomatch h
  | exIntro φf t d ih =>
      intro Γ Δ φ O h
      simp only [check] at h ⊢
      split at h
      next c o heq =>
        rw [ih Γ Δ _ _ heq]
        exact h
      all_goals nomatch h
  | exElim ψ d dBody ih ihBody =>
      intro Γ Δ φ O h
      simp only [check] at h ⊢
      split at h
      next φf o heq =>
        split at h
        next ψ' o₂ heqB =>
          have hB := ihBody (φf :: Γ.map (DFormula.lift 1 0))
            (Δ.map (DFormula.lift 1 0)) _ _ heqB
          rw [List.cons_append, ← List.map_append] at hB
          simp only [check, ih Γ Δ _ _ heq, hB]
          exact h
        all_goals nomatch h
      all_goals nomatch h
  | emPosit φf => intro Γ Δ φ O h; exact h
  | lpoPosit φf => intro Γ Δ φ O h; exact h
  | mpPosit φf => intro Γ Δ φ O h; exact h

/-- A closed certificate is accepted in every context, same ledger. -/
theorem check_closed_any {d : Deriv} {φ : DFormula} {O : Ledger}
    (h : check [] d = some (φ, O)) (Γ : Ctx) : check Γ d = some (φ, O) :=
  check_append d [] Γ φ O h

/-! ## The splice (graft/cut) -/

/-- **Graft/cut.** If `d` is accepted in `Γ` with a ledger inside `S`, and
every posit of `S` reduces to `T`, then the same formula is derivable in `Γ`
with a ledger inside `T`: replace every posit leaf by a `T`-certificate of its
instance (weakened into place) and rebuild. Existence-style, so no choice. -/
theorem splice {S T : PositSet} (hRep : ∀ Q : Posit, S Q = true → ReducesTo T Q) :
    ∀ (d : Deriv) (Γ : Ctx) (φ : DFormula) (O : Ledger),
      check Γ d = some (φ, O) → ledgerWithin O S →
      ∃ (d' : Deriv) (O' : Ledger), check Γ d' = some (φ, O') ∧ ledgerWithin O' T := by
  intro d
  induction d with
  | hyp i =>
      intro Γ φ O h _
      refine ⟨.hyp i, Ledger.empty, ?_, ledgerWithin_empty T⟩
      simp only [check] at h ⊢
      split at h
      next ψ heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        simp only [heq, h.1]
      all_goals nomatch h
  | eqRefl t =>
      intro Γ φ O h _
      simp only [check, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨.eqRefl t, Ledger.empty, rfl, ledgerWithin_empty T⟩
  | eqSubst φf t s d₁ d₂ ih₁ ih₂ =>
      intro Γ φ O h hin
      simp only [check] at h
      split at h
      next cEq o₁ cT o₂ heq₁ heq₂ =>
        split at h
        · split at h
          · rename_i hc₁ hc₂
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hin₁, hin₂⟩ := ledgerWithin_or.mp hin
            obtain ⟨d₁', o₁', h₁', hT₁⟩ := ih₁ Γ _ _ heq₁ hin₁
            obtain ⟨d₂', o₂', h₂', hT₂⟩ := ih₂ Γ _ _ heq₂ hin₂
            refine ⟨.eqSubst φf t s d₁' d₂', o₁'.union o₂', ?_,
              ledgerWithin_or.mpr ⟨hT₁, hT₂⟩⟩
            simp only [check, h₁', h₂', hc₁, hc₂, if_true]
          · nomatch h
        · nomatch h
      all_goals nomatch h
  | succNeZero t =>
      intro Γ φ O h _
      simp only [check, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨.succNeZero t, Ledger.empty, rfl, ledgerWithin_empty T⟩
  | succInj d ih =>
      intro Γ φ O h hin
      simp only [check] at h
      split at h
      next t s o heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨d', o', h', hT⟩ := ih Γ _ _ heq hin
        exact ⟨.succInj d', o', by simp only [check, h'], hT⟩
      all_goals nomatch h
  | addZero t =>
      intro Γ φ O h _
      simp only [check, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨.addZero t, Ledger.empty, rfl, ledgerWithin_empty T⟩
  | addSucc t s =>
      intro Γ φ O h _
      simp only [check, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨.addSucc t s, Ledger.empty, rfl, ledgerWithin_empty T⟩
  | mulZero t =>
      intro Γ φ O h _
      simp only [check, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨.mulZero t, Ledger.empty, rfl, ledgerWithin_empty T⟩
  | mulSucc t s =>
      intro Γ φ O h _
      simp only [check, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨.mulSucc t s, Ledger.empty, rfl, ledgerWithin_empty T⟩
  | ind φf d₀ dS ih₀ ihS =>
      intro Γ φ O h hin
      simp only [check] at h
      split at h
      next c₀ o₁ cS o₂ heq₀ heqS =>
        split at h
        · split at h
          · rename_i hc₀ hcS
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hin₀, hinS⟩ := (ledgerWithin_indTier φf.isQF).mp hin
            obtain ⟨d₀', o₁', h₀', hT₀⟩ := ih₀ Γ _ _ heq₀ hin₀
            obtain ⟨dS', o₂', hS', hTS⟩ := ihS Γ _ _ heqS hinS
            refine ⟨.ind φf d₀' dS',
              if φf.isQF then o₁'.union o₂' else (o₁'.union o₂').union Ledger.ofIndFull,
              ?_, (ledgerWithin_indTier φf.isQF).mpr ⟨hT₀, hTS⟩⟩
            simp only [check, h₀', hS', hc₀, hcS, if_true]
          · nomatch h
        · nomatch h
      all_goals nomatch h
  | implIntro φf d ih =>
      intro Γ φ O h hin
      simp only [check] at h
      split at h
      next ψ o heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨d', o', h', hT⟩ := ih (φf :: Γ) _ _ heq hin
        exact ⟨.implIntro φf d', o', by simp only [check, h'], hT⟩
      all_goals nomatch h
  | implElim d₁ d₂ ih₁ ih₂ =>
      intro Γ φ O h hin
      simp only [check] at h
      split at h
      next φf ψ o₁ φ' o₂ heq₁ heq₂ =>
        split at h
        · rename_i hc
          subst hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨hin₁, hin₂⟩ := ledgerWithin_or.mp hin
          obtain ⟨d₁', o₁', h₁', hT₁⟩ := ih₁ Γ _ _ heq₁ hin₁
          obtain ⟨d₂', o₂', h₂', hT₂⟩ := ih₂ Γ _ _ heq₂ hin₂
          exact ⟨.implElim d₁' d₂', o₁'.union o₂',
            by simp only [check, h₁', h₂', if_true],
            ledgerWithin_or.mpr ⟨hT₁, hT₂⟩⟩
        · nomatch h
      all_goals nomatch h
  | conjIntro d₁ d₂ ih₁ ih₂ =>
      intro Γ φ O h hin
      simp only [check] at h
      split at h
      next φf o₁ ψ o₂ heq₁ heq₂ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hin₁, hin₂⟩ := ledgerWithin_or.mp hin
        obtain ⟨d₁', o₁', h₁', hT₁⟩ := ih₁ Γ _ _ heq₁ hin₁
        obtain ⟨d₂', o₂', h₂', hT₂⟩ := ih₂ Γ _ _ heq₂ hin₂
        exact ⟨.conjIntro d₁' d₂', o₁'.union o₂',
          by simp only [check, h₁', h₂'],
          ledgerWithin_or.mpr ⟨hT₁, hT₂⟩⟩
      all_goals nomatch h
  | conjElim1 d ih =>
      intro Γ φ O h hin
      simp only [check] at h
      split at h
      next φf ψ o heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨d', o', h', hT⟩ := ih Γ _ _ heq hin
        exact ⟨.conjElim1 d', o', by simp only [check, h'], hT⟩
      all_goals nomatch h
  | conjElim2 d ih =>
      intro Γ φ O h hin
      simp only [check] at h
      split at h
      next φf ψ o heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨d', o', h', hT⟩ := ih Γ _ _ heq hin
        exact ⟨.conjElim2 d', o', by simp only [check, h'], hT⟩
      all_goals nomatch h
  | disjIntro1 ψ d ih =>
      intro Γ φ O h hin
      simp only [check] at h
      split at h
      next φf o heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨d', o', h', hT⟩ := ih Γ _ _ heq hin
        exact ⟨.disjIntro1 ψ d', o', by simp only [check, h'], hT⟩
      all_goals nomatch h
  | disjIntro2 φf d ih =>
      intro Γ φ O h hin
      simp only [check] at h
      split at h
      next ψ o heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨d', o', h', hT⟩ := ih Γ _ _ heq hin
        exact ⟨.disjIntro2 φf d', o', by simp only [check, h'], hT⟩
      all_goals nomatch h
  | disjElim d dL dR ih ihL ihR =>
      intro Γ φ O h hin
      simp only [check] at h
      split at h
      next φf ψf o heq =>
        split at h
        next χ₁ o₁ χ₂ o₂ heqL heqR =>
          split at h
          · rename_i hc
            subst hc
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hin', hinR⟩ := ledgerWithin_or.mp hin
            obtain ⟨hin₀, hinL⟩ := ledgerWithin_or.mp hin'
            obtain ⟨d', o', h', hT⟩ := ih Γ _ _ heq hin₀
            obtain ⟨dL', oL', hL', hTL⟩ := ihL (φf :: Γ) _ _ heqL hinL
            obtain ⟨dR', oR', hR', hTR⟩ := ihR (ψf :: Γ) _ _ heqR hinR
            exact ⟨.disjElim d' dL' dR', (o'.union oL').union oR',
              by simp only [check, h', hL', hR', if_true],
              ledgerWithin_or.mpr ⟨ledgerWithin_or.mpr ⟨hT, hTL⟩, hTR⟩⟩
          · nomatch h
        all_goals nomatch h
      all_goals nomatch h
  | flsElim φf d ih =>
      intro Γ φ O h hin
      simp only [check] at h
      split at h
      next o heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨d', o', h', hT⟩ := ih Γ _ _ heq hin
        exact ⟨.flsElim φf d', o', by simp only [check, h'], hT⟩
      all_goals nomatch h
  | allIntro d ih =>
      intro Γ φ O h hin
      simp only [check] at h
      split at h
      next φf o heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨d', o', h', hT⟩ := ih (Γ.map (DFormula.lift 1 0)) _ _ heq hin
        exact ⟨.allIntro d', o', by simp only [check, h'], hT⟩
      all_goals nomatch h
  | allElim t d ih =>
      intro Γ φ O h hin
      simp only [check] at h
      split at h
      next φf o heq =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨d', o', h', hT⟩ := ih Γ _ _ heq hin
        exact ⟨.allElim t d', o', by simp only [check, h'], hT⟩
      all_goals nomatch h
  | exIntro φf t d ih =>
      intro Γ φ O h hin
      simp only [check] at h
      split at h
      next c o heq =>
        split at h
        · rename_i hc
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨d', o', h', hT⟩ := ih Γ _ _ heq hin
          exact ⟨.exIntro φf t d', o',
            by simp only [check, h', hc, if_true], hT⟩
        · nomatch h
      all_goals nomatch h
  | exElim ψ d dBody ih ihBody =>
      intro Γ φ O h hin
      simp only [check] at h
      split at h
      next φf o heq =>
        split at h
        next ψ' o₂ heqB =>
          split at h
          · rename_i hc
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hin₁, hin₂⟩ := ledgerWithin_or.mp hin
            obtain ⟨d', o', h', hT⟩ := ih Γ _ _ heq hin₁
            obtain ⟨dB', oB', hB', hTB⟩ :=
              ihBody (φf :: Γ.map (DFormula.lift 1 0)) _ _ heqB hin₂
            exact ⟨.exElim ψ d' dB', o'.union oB',
              by simp only [check, h', hB', hc, if_true],
              ledgerWithin_or.mpr ⟨hT, hTB⟩⟩
          · nomatch h
        all_goals nomatch h
      all_goals nomatch h
  | emPosit φf =>
      intro Γ φ O h hin
      simp only [check, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hS : S Posit.em = true := hin Posit.em rfl
      obtain ⟨d', O', hchk, hT⟩ :=
        hRep Posit.em hS φf (.disj φf φf.neg) rfl
      exact ⟨d', O', check_closed_any hchk Γ, hT⟩
  | lpoPosit φf =>
      intro Γ φ O h hin
      simp only [check, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hS : S Posit.lpo = true := hin Posit.lpo rfl
      obtain ⟨d', O', hchk, hT⟩ :=
        hRep Posit.lpo hS φf
          (.impl (.all (.disj φf φf.neg)) (.disj (.ex φf) (.all φf.neg))) rfl
      exact ⟨d', O', check_closed_any hchk Γ, hT⟩
  | mpPosit φf =>
      intro Γ φ O h hin
      simp only [check] at h
      split at h
      · rename_i hqf
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hS : S Posit.mp = true := hin Posit.mp rfl
        obtain ⟨d', O', hchk, hT⟩ :=
          hRep Posit.mp hS φf (.impl (.neg (.neg (.ex φf))) (.ex φf))
            (by simp [Posit.concl, hqf])
        exact ⟨d', O', check_closed_any hchk Γ, hT⟩
      · nomatch h

/-! ## Transitivity: `ReducesTo` is a preorder -/

/-- **Cut.** If `P` reduces to `S` and every posit of `S` reduces to `T`, then
`P` reduces to `T`. With `reducesTo_self` this makes kernel-interderivability
a genuine preorder — the panel's "unlicensed preorder" flag is discharged. -/
theorem reducesTo_trans {S T : PositSet} {P : Posit}
    (hSP : ReducesTo S P) (hTS : ∀ Q : Posit, S Q = true → ReducesTo T Q) :
    ReducesTo T P := by
  intro φ ψ h
  obtain ⟨d, O, hchk, hin⟩ := hSP φ ψ h
  exact splice hTS d [] ψ O hchk hin

/-! ## Audits -/

#print axioms check_append
#print axioms splice
#print axioms reducesTo_trans

end Rigidity
end ActualMathematics

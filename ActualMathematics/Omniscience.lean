/-
  ActualMathematics/Omniscience.lean

  The omniscience principles, as the UNITS in which the strength of a non-forced
  posit is measured.

  Milan's companion paper (`Distinction, Initiality, and Recognition Quotients`)
  closes the CARDINALITY wall: a finite presentation generates a countable carrier,
  so the order-completion of ℚ (the continuum) is not finitely generated. That is a
  statement about SIZE. `PRCCompletenessIndependence` closes the MODEL-THEORETIC
  wall: order-completeness holds in ℝ and fails in a countable cost-closed field, so
  completeness is not ENTAILED by the cost/field axioms.

  This module opens the third, sharper wall, which neither of those touches: the
  PROOF-THEORETIC strength of completeness. The question is not "is the completed
  object too big?" nor "is completeness independent?" but "exactly HOW MUCH logical
  omniscience does a completeness principle smuggle in?". The answer is read in the
  classical reverse-mathematics / constructive-reverse-mathematics currency: the
  Limited Principle of Omniscience and its relatives. Real-number trichotomy is
  analytic `LPO`; the order dichotomy `0 ≤ x ∨ x ≤ 0` is analytic `LLPO`; monotone
  convergence carries `LPO`. These principles are decisions about Σ⁰₁ data that
  distinction does not force (you cannot, from a finite certificate, decide whether a
  countable search halts), so a posit that entails one of them is exactly that much
  stronger than the δ base.

  Here we fix the vocabulary and prove the part that is purely arithmetical and
  choice-free: the omniscience hierarchy itself (`LPO ⇒ WLPO`, `LPO ⇒ LLPO`,
  `LPO ⇒ Markov`, and `WLPO ∧ Markov ⇒ LPO`). The forward CALIBRATIONS that connect
  these to completeness (`trichotomy ⇒ LPO`, `dichotomy ⇒ LLPO`, `MCT ⇒ LPO`) live
  on a constructive real carrier and are grown as the next ladder rungs.

  The principles are stated over `ℕ → Bool` (binary sequences = decidable Σ⁰₁
  predicates). As `Prop`s they are choice-free; the point is precisely that they are
  NOT provable from the δ base, while classically (with `Classical.em`) they are all
  true. We never invoke `Classical` here, so the hierarchy lemmas are constructively
  valid implications.

  No project-local axioms. No sorry.
-/

import Mathlib

namespace ActualMathematics
namespace Omniscience

/-- **LPO**, the Limited Principle of Omniscience. For every binary sequence, either
it is identically `false`, or it is `true` somewhere. Equivalently: every Σ⁰₁
predicate over ℕ is decidable. Constructively unprovable; classically trivial. This
is the omniscience content of real-number trichotomy. -/
def LPO : Prop := ∀ α : ℕ → Bool, (∀ n, α n = false) ∨ (∃ n, α n = true)

/-- **WLPO**, the Weak Limited Principle of Omniscience. For every binary sequence,
either it is identically `false`, or it is not. This is `LPO` with the positive
existential weakened to a double negation: it decides the Π⁰₁ statement, not its Σ⁰₁
witness. -/
def WLPO : Prop := ∀ α : ℕ → Bool, (∀ n, α n = false) ∨ ¬ (∀ n, α n = false)

/-- **Markov's Principle**. If a binary sequence is not identically `false`, then it
is `true` somewhere. The constructive "unbounded search that is known to succeed does
succeed" principle. -/
def MarkovPrinciple : Prop := ∀ α : ℕ → Bool, ¬ (∀ n, α n = false) → ∃ n, α n = true

/-- **LLPO**, the Lesser Limited Principle of Omniscience. For a binary sequence with
at most one `true` term, either all even-indexed terms are `false`, or all
odd-indexed terms are `false`. This is the omniscience content of the order dichotomy
`0 ≤ x ∨ x ≤ 0` and of the (exact) intermediate value theorem. Strictly weaker than
`LPO`. -/
def LLPO : Prop :=
  ∀ α : ℕ → Bool,
    (∀ m n, α m = true → α n = true → m = n) →
    ((∀ k, α (2 * k) = false) ∨ (∀ k, α (2 * k + 1) = false))

/-- `LPO ⇒ WLPO`: deciding the Σ⁰₁ witness in particular decides its Π⁰₁ negation.
Choice-free. -/
theorem lpo_imp_wlpo (h : LPO) : WLPO := by
  intro α
  rcases h α with hall | ⟨n, hn⟩
  · exact Or.inl hall
  · exact Or.inr (fun hall => Bool.noConfusion ((hall n).symm.trans hn))

/-- `LPO ⇒ Markov`: full omniscience subsumes the known-to-halt search. Choice-free. -/
theorem lpo_imp_markov (h : LPO) : MarkovPrinciple := by
  intro α hne
  rcases h α with hall | hex
  · exact absurd hall hne
  · exact hex

/-- `LPO ⇒ LLPO`. Given the witness located by `LPO` and the at-most-one-true
hypothesis, every index of the other parity must be `false`. The parity split is the
omega-produced disjunction `n % 2 = 0 ∨ n % 2 = 1`, so the proof avoids the classical
`Nat.even_or_odd` and stays choice-free. -/
theorem lpo_imp_llpo (h : LPO) : LLPO := by
  intro α hone
  rcases h α with hall | ⟨n, hn⟩
  · exact Or.inl (fun k => hall (2 * k))
  · have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hmod with hpar | hpar
    · refine Or.inr (fun k => ?_)
      cases hb : α (2 * k + 1) with
      | false => rfl
      | true => exfalso; have := hone n (2 * k + 1) hn hb; omega
    · refine Or.inl (fun k => ?_)
      cases hb : α (2 * k) with
      | false => rfl
      | true => exfalso; have := hone n (2 * k) hn hb; omega

/-- `WLPO ∧ Markov ⇒ LPO`: deciding the Π⁰₁ statement, plus the known-to-halt search,
recovers full omniscience. Choice-free. This pins `LPO` exactly between the two
weaker principles. -/
theorem wlpo_and_markov_imp_lpo (hw : WLPO) (hm : MarkovPrinciple) : LPO := by
  intro α
  rcases hw α with hall | hne
  · exact Or.inl hall
  · exact Or.inr (hm α hne)

end Omniscience
end ActualMathematics

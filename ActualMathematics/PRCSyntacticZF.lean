/-
  ActualMathematics/PRCSyntacticZF.lean

  A SYNTACTIC (proof-theoretic) parse of ZF set theory into the δ `FormalSystem`
  interface, upgrading the semantic parse of `PRCFullZFCParse.lean`. There, the
  discrimination relation was genuine ZF extensional difference of the represented
  sets (a MODEL-side fact). Here the discrimination relation is DERIVABILITY: two
  tokens are distinguished exactly when the deep-embedded proof calculus derives
  their non-equality. The δ distinction is exhibited as an explicit finite
  derivation term (`deriv_e_ne_s`), not as a semantic observation.

  WHAT IS EMBEDDED. The language is first-order logic with equality over the
  signature {∈}, in the standard DEFINITIONAL EXTENSION of ZF by two constants:
  `e` (the empty set) and `s` (its singleton {e}), each carrying its standard
  defining axiom as a schema over closed terms:

    Empty(e)        :  ∀ z, ¬ z ∈ e          (constructor `ax_empty`)
    Singleton(s, e) :  ∀ z, z ∈ s ↔ z = e    (constructors `ax_singleton_mp`,
                                              `ax_singleton_mpr`, the two rule
                                              directions of the biconditional)

  The constants are justified by ZF's Empty Set and Pairing axioms: ZF proves
  ∃!x Empty(x) and ∃!y Singleton(y, e), so extending the language with e and s and
  their defining axioms is the standard conservative definitional extension.
  Embedding those existence axioms themselves and performing existential
  elimination inside the calculus is DELIBERATELY AVOIDED: it would force a full
  quantifier calculus with binder plumbing, and the point of this module is a
  finite, readable, rule-faithful derivation of the δ distinction.

  To avoid binder plumbing we deep-embed a propositional-plus-instantiation
  fragment: only the closed formulas needed (membership atoms and equality atoms
  between closed terms, and negation), with the universally quantified defining
  axioms embedded as axiom SCHEMAS over closed terms (each axiom constructor takes
  a closed term z and yields the instance at z). That is a standard Hilbert-style
  schema presentation and is rule-faithful.

  DERIVATIONS. `ZFDeriv Γ φ` is a natural-deduction derivation of φ from the
  finite hypothesis context Γ, as an inductive Type in the repo's `Deriv` pattern
  (`DeltaKernel/Check.lean`): the rules are the axiom schemas above, the equality
  rules `eq_refl`, `eq_symm`, and `eq_subst` (Leibniz substitution restricted to
  the membership context, the only congruence shape the fragment needs; symmetry
  is primitive because the restricted substitution cannot derive it), the
  hypothesis rule `hyp`, and negation introduction `neg_intro` (from derivations
  of ψ and ¬ψ under hypothesis φ, conclude ¬φ, discharging φ). DESIGN NOTE: a
  context-free reductio constructor with function-valued premises
  (`(ZFDeriv φ → ZFDeriv ψ) → ...`) is not admissible in Lean (strict positivity),
  and as an admissibility-style rule its soundness would need fragment
  completeness; explicit hypothesis contexts are the standard natural-deduction
  encoding and make soundness a direct structural induction.

  WHAT IS PROVED.
  * `deriv_e_ne_s` : the explicit closed derivation of ¬(e = s). The informal
    proof it encodes: e = e by reflexivity, so e ∈ s by Singleton; if e = s then
    substituting along s = e (symmetry) gives e ∈ e; but Empty gives ¬ e ∈ e;
    contradiction, hence ¬(e = s).
  * `zfderiv_sound` : fragment soundness. Interpreting e ↦ ∅ and s ↦ {∅} in
    Mathlib's `ZFSet`, every formula derivable from true hypotheses holds.
  * `model_separates` : (∅ : ZFSet) ≠ {∅}, the model-side separation.
  * `zfderiv_no_eq` : non-vacuity guard. The calculus does NOT derive e = s
    (soundness + model separation), so the discrimination relation below is not
    inhabited by an inconsistent calculus that derives everything.
  * `zfSyntacticSystem` : the parse. Tokens are the closed terms, and
    `distinguishes a b := Nonempty (ZFDeriv [] (¬ a = b))` is DERIVABILITY of
    non-equality; the expression order is the derivation-length order on traces.
    `zfSyntacticSystem_expressive`, `zfSyntacticSystem_embeds_delta`,
    `zfSyntacticSystem_not_degenerate`, and the packaged capstone
    `syntactic_zf_realizes_delta` follow.

  WHAT IS NOT EMBEDDED, AND WHY THAT DOES NOT WEAKEN THE δ CONCLUSION. The full
  separation and replacement schemas, unrestricted quantifier rules, and
  existential elimination are not embedded. The δ conclusion needs exactly (i) one
  derivable distinction between the two endpoint tokens and (ii) a reflexive
  expression order; both live in this fragment. Every rule here is a derived or
  primitive rule of full ZF (under the definitional extension), so the fragment's
  derivations are ZF derivations verbatim; enlarging the calculus toward full ZF
  only ADDS derivations, so the discrimination relation only grows and
  expressiveness is preserved. Non-vacuity in the enlargement is inherited from
  the same model: ZF does not derive e = s as long as ZF has the `ZFSet` model.

  No project-local axioms. No sorry.
-/

import Mathlib.SetTheory.ZFC.Basic
import ActualMathematics.PRCDistinctionDichotomy

namespace ActualMathematics
namespace SyntacticZFParse

open FormalSystem

/-- The ZF universe, pinned to universe 0 (the `FormalSystem` interface is
`Type`-0). -/
abbrev ZF := ZFSet.{0}

/-! ### Syntax: closed terms and the closed-formula fragment -/

/-- Closed terms of the definitional extension of ZF by the empty-set constant
`e` and the singleton constant `s`. Nothing else is needed: the δ distinction is
between these two. -/
inductive ZFTerm where
  | const_e
  | const_s
  deriving DecidableEq, Repr

/-- The closed-formula fragment: membership atoms and equality atoms between
closed terms, and negation. Exactly what the rules below need. -/
inductive ZFFormula where
  | mem : ZFTerm → ZFTerm → ZFFormula
  | eq : ZFTerm → ZFTerm → ZFFormula
  | neg : ZFFormula → ZFFormula
  deriving DecidableEq, Repr

/-! ### The proof calculus -/

/-- Natural-deduction derivations of the fragment from a finite hypothesis
context, following the repo's `Deriv` pattern (`DeltaKernel/Check.lean`):
derivations are an inductive Type, one constructor per named standard rule.

* `hyp`: hypothesis from the context.
* `ax_empty`: the Empty(e) defining axiom, as a schema over closed terms z:
  ¬ z ∈ e.
* `ax_singleton_mp` / `ax_singleton_mpr`: the two rule directions of the
  Singleton(s, e) defining axiom instance z ∈ s ↔ z = e.
* `eq_refl`, `eq_symm`, `eq_subst`: the equality rules the fragment needs.
  `eq_subst` is Leibniz substitution restricted to the membership context
  (from a = b and c ∈ a conclude c ∈ b); symmetry is primitive because the
  restricted substitution cannot derive it.
* `neg_intro`: negation introduction, discharging the hypothesis: from
  derivations of ψ and ¬ψ under hypothesis φ, conclude ¬φ. -/
inductive ZFDeriv : List ZFFormula → ZFFormula → Type where
  /-- Hypothesis: any formula in the context. -/
  | hyp {Γ : List ZFFormula} {φ : ZFFormula} :
      φ ∈ Γ → ZFDeriv Γ φ
  /-- Empty(e) schema instance at the closed term z: ⊢ ¬ z ∈ e. -/
  | ax_empty {Γ : List ZFFormula} (z : ZFTerm) :
      ZFDeriv Γ (.neg (.mem z .const_e))
  /-- Singleton(s, e) instance at z, forward direction: from z ∈ s conclude
  z = e. -/
  | ax_singleton_mp {Γ : List ZFFormula} {z : ZFTerm} :
      ZFDeriv Γ (.mem z .const_s) → ZFDeriv Γ (.eq z .const_e)
  /-- Singleton(s, e) instance at z, reverse direction: from z = e conclude
  z ∈ s. -/
  | ax_singleton_mpr {Γ : List ZFFormula} {z : ZFTerm} :
      ZFDeriv Γ (.eq z .const_e) → ZFDeriv Γ (.mem z .const_s)
  /-- Reflexivity: ⊢ t = t. -/
  | eq_refl {Γ : List ZFFormula} (t : ZFTerm) :
      ZFDeriv Γ (.eq t t)
  /-- Symmetry: from a = b conclude b = a. -/
  | eq_symm {Γ : List ZFFormula} {a b : ZFTerm} :
      ZFDeriv Γ (.eq a b) → ZFDeriv Γ (.eq b a)
  /-- Leibniz substitution in the membership context: from a = b and c ∈ a
  conclude c ∈ b. -/
  | eq_subst {Γ : List ZFFormula} {a b c : ZFTerm} :
      ZFDeriv Γ (.eq a b) → ZFDeriv Γ (.mem c a) → ZFDeriv Γ (.mem c b)
  /-- Negation introduction: from ψ and ¬ψ each derived under the extra
  hypothesis φ, conclude ¬φ, discharging φ. -/
  | neg_intro {Γ : List ZFFormula} {φ ψ : ZFFormula} :
      ZFDeriv (φ :: Γ) ψ → ZFDeriv (φ :: Γ) (.neg ψ) → ZFDeriv Γ (.neg φ)

/-! ### The explicit derivation of the δ distinction -/

/-- **The δ distinction, derived syntactically.** The explicit closed derivation
term for ¬(e = s). Reading the term bottom-up under the discharged hypothesis
e = s:

1. `eq_refl e`                 :  e = e
2. `ax_singleton_mpr` of 1     :  e ∈ s
3. `eq_symm` of the hypothesis :  s = e
4. `eq_subst` of 3 into 2      :  e ∈ e
5. `ax_empty e`                :  ¬ e ∈ e

`neg_intro` discharges the hypothesis: ⊢ ¬(e = s). -/
def deriv_e_ne_s : ZFDeriv [] (.neg (.eq .const_e .const_s)) :=
  .neg_intro
    (.eq_subst
      (.eq_symm (.hyp (List.Mem.head _)))
      (.ax_singleton_mpr (.eq_refl .const_e)))
    (.ax_empty .const_e)

/-! ### Fragment soundness in Mathlib's ZF universe -/

/-- Interpretation of the closed terms: e ↦ ∅ and s ↦ {∅}, the sets whose
existence and uniqueness justify the definitional extension. -/
noncomputable def ZFTerm.interp : ZFTerm → ZF
  | .const_e => ∅
  | .const_s => {∅}

/-- Truth of a fragment formula in the `ZFSet` model. -/
def ZFFormula.holds : ZFFormula → Prop
  | .mem a b => a.interp ∈ b.interp
  | .eq a b => a.interp = b.interp
  | .neg φ => ¬ φ.holds

/-- **Fragment soundness.** Every formula derivable from true hypotheses holds
in the `ZFSet` model. Direct structural induction over derivations; the
`neg_intro` case extends the hypothesis interpretation across the discharge. -/
theorem zfderiv_sound :
    ∀ {Γ : List ZFFormula} {φ : ZFFormula},
      ZFDeriv Γ φ → (∀ χ ∈ Γ, χ.holds) → φ.holds := by
  intro Γ φ d
  induction d with
  | hyp h =>
      intro hΓ
      exact hΓ _ h
  | ax_empty z =>
      intro _
      simp only [ZFFormula.holds, ZFTerm.interp]
      exact ZFSet.notMem_empty _
  | ax_singleton_mp _ ih =>
      intro hΓ
      have h := ih hΓ
      simp only [ZFFormula.holds, ZFTerm.interp] at h ⊢
      exact ZFSet.mem_singleton.mp h
  | ax_singleton_mpr _ ih =>
      intro hΓ
      have h := ih hΓ
      simp only [ZFFormula.holds, ZFTerm.interp] at h ⊢
      exact ZFSet.mem_singleton.mpr h
  | eq_refl t =>
      intro _
      simp only [ZFFormula.holds]
  | eq_symm _ ih =>
      intro hΓ
      have h := ih hΓ
      simp only [ZFFormula.holds] at h ⊢
      exact h.symm
  | eq_subst _ _ ih₁ ih₂ =>
      intro hΓ
      have h₁ := ih₁ hΓ
      have h₂ := ih₂ hΓ
      simp only [ZFFormula.holds] at h₁ h₂ ⊢
      exact h₁ ▸ h₂
  | @neg_intro Γ' φ' ψ' _ _ ih₁ ih₂ =>
      intro hΓ
      simp only [ZFFormula.holds]
      intro hφ
      have hΓ' : ∀ χ ∈ φ' :: Γ', χ.holds := by
        intro χ hχ
        cases hχ with
        | head => exact hφ
        | tail _ h => exact hΓ χ h
      have hψ := ih₁ hΓ'
      have hnψ := ih₂ hΓ'
      simp only [ZFFormula.holds] at hnψ
      exact hnψ hψ

/-- Soundness for closed derivations (empty context). -/
theorem zfderiv_sound_closed {φ : ZFFormula} (d : ZFDeriv [] φ) : φ.holds :=
  zfderiv_sound d (fun _ h => nomatch h)

/-- **Model separation.** ∅ and {∅} are distinct sets: ∅ ∈ {∅} but ∅ ∉ ∅. -/
theorem model_separates : (∅ : ZF) ≠ ({∅} : ZF) := by
  intro h
  have h1 : (∅ : ZF) ∈ ({∅} : ZF) := ZFSet.mem_singleton.mpr rfl
  rw [← h] at h1
  exact ZFSet.notMem_empty ∅ h1

/-- **Non-vacuity guard.** The calculus does NOT derive e = s: a derivation
would be sound, hence ∅ = {∅} in the model, contradicting `model_separates`.
So the discrimination relation below is not fed by an inconsistent calculus. -/
theorem zfderiv_no_eq (d : ZFDeriv [] (.eq .const_e .const_s)) : False := by
  have h := zfderiv_sound_closed d
  simp only [ZFFormula.holds, ZFTerm.interp] at h
  exact model_separates h

/-! ### The parse into the FormalSystem interface -/

/-- Syntactic ZF parsed into the `FormalSystem` interface. Tokens are the closed
terms; the discrimination relation is DERIVABILITY of non-equality in the proof
calculus (not a model-side observation); the endpoints are e and s; the
expression order is the derivation-length order on traces. -/
def zfSyntacticSystem : FormalSystem where
  Token := ZFTerm
  Expr := ℕ
  distinguishes := fun a b => Nonempty (ZFDeriv [] (.neg (.eq a b)))
  exprExtends := fun m n => m ≤ n
  endpointToken := fun e =>
    match e.side with
    | Side.left => ZFTerm.const_e
    | Side.right => ZFTerm.const_s
  traceExpr := Trace.length
  traceExpr_extends := fun h => InevitabilityInstances.length_le_of_extends h

/-- `zfSyntacticSystem` distinguishes its endpoints: the explicit derivation
`deriv_e_ne_s` witnesses ⊢ ¬(e = s). -/
theorem zfSyntacticSystem_expressive : zfSyntacticSystem.Expressive := by
  show Nonempty (ZFDeriv [] (.neg (.eq .const_e .const_s)))
  exact ⟨deriv_e_ne_s⟩

/-- **Syntactic ZF contains the δ core.** -/
theorem zfSyntacticSystem_embeds_delta :
    Nonempty (PRCEmbeddingInto zfSyntacticSystem) :=
  FormalSystemEmbeddingTarget_proved zfSyntacticSystem zfSyntacticSystem_expressive

theorem zfSyntacticSystem_exprReflexive :
    DistinctionDichotomy.ExprReflexive zfSyntacticSystem :=
  fun n => Nat.le_refl n

/-- Syntactic ZF falls on the δ side of the distinction dichotomy: it is
non-degenerate, hence realizes δ. -/
theorem zfSyntacticSystem_not_degenerate :
    ¬ DistinctionDichotomy.Degenerate zfSyntacticSystem :=
  DistinctionDichotomy.not_degenerate_of_realizesDelta zfSyntacticSystem
    zfSyntacticSystem_embeds_delta

/-- **The syntactic parse, packaged.** ZF's proof calculus (in the definitional
extension by e and s, on the deep-embedded closed fragment): (i) is sound for the
`ZFSet` model, (ii) DERIVES the δ distinction ¬(e = s) by an explicit finite
derivation term, (iii) the model separates the endpoints (∅ ≠ {∅}), (iv) the
calculus does not derive e = s (non-vacuity), and (v) the parsed system realizes
the δ core. -/
theorem syntactic_zf_realizes_delta :
    (∀ φ : ZFFormula, ZFDeriv [] φ → φ.holds)
      ∧ Nonempty (ZFDeriv [] (.neg (.eq .const_e .const_s)))
      ∧ ((∅ : ZF) ≠ ({∅} : ZF))
      ∧ (ZFDeriv [] (.eq .const_e .const_s) → False)
      ∧ Nonempty (PRCEmbeddingInto zfSyntacticSystem) :=
  ⟨fun _ d => zfderiv_sound_closed d, ⟨deriv_e_ne_s⟩, model_separates,
    zfderiv_no_eq, zfSyntacticSystem_embeds_delta⟩

end SyntacticZFParse
end ActualMathematics

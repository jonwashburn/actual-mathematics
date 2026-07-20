/-
  ActualMathematics/PRCSyntacticHOL.lean

  Corpus campaign (frozen prereg:
  δ/plans/Delta_Inevitability_Corpus_Campaign_Prereg_20260717.html): the
  SYNTACTIC (proof-theoretic) parse of a HOL / simple-type-theory kernel into
  the δ `FormalSystem` interface. HOL is the fourth corpus member: the main
  implemented foundation besides set theory and dependent type theory
  (HOL Light, HOL4, Isabelle/HOL).

  WHAT IS EMBEDDED. A Gordon-style HOL kernel, minimized to its propositional
  core, as POSITIVE DATA: sequents `Γ ⊢ t` are an inductive family
  `HOLDeriv : List HOLTerm → HOLTerm → Type`, so a derivation is a finite
  tree the kernel checks, never a host-level assumption. The embedded rules,
  named against the standard HOL Light / HOL4 kernel rule list:

    * `assum`     = ASSUME   (HOL Light primitive rule; `{t} ⊢ t`, here with
                              the usual context weakening built in)
    * `refl`      = REFL     (HOL Light primitive rule 1; `⊢ t = t`)
    * `eq_mp`     = EQ_MP    (HOL Light primitive rule; from `Γ ⊢ a = b` and
                              `Γ ⊢ a` conclude `Γ ⊢ b`)
    * `mp`        = MP       (HOL4 primitive; HOL Light derives it from
                              EQ_MP + DEDUCT_ANTISYM_RULE)
    * `disch`     = DISCH    (HOL4 primitive; HOL Light derives it; discharge
                              a hypothesis into an implication)
    * `truth`     = TRUTH    (bool.ml derived rule; `⊢ T`)
    * `not_intro` = NOT_INTRO (bool.ml derived rule; from `Γ ⊢ a ⟹ F`
                              conclude `Γ ⊢ ¬a`)
    * `not_elim`  = NOT_ELIM (bool.ml derived rule; the converse)

  TRUTH / NOT_INTRO / NOT_ELIM are derived rules in HOL Light only because
  its kernel defines T, F, ¬, ⟹ as lambda terms; since this fragment omits
  the lambda layer (see the honest boundary below), those constants are taken
  as primitive and their defining rules become kernel rules, exactly as in a
  Hilbert-style presentation of the same logic.

  THE TARGET DERIVATION. `deriv_T_ne_F : ⊢ ¬(T = F)` is a readable five-node
  tree: ASSUME `T = F`, TRUTH gives `⊢ T`, EQ_MP rewrites it to `F` under the
  assumption, DISCH discharges to `⊢ (T = F) ⟹ F`, NOT_INTRO closes. This is
  the standard HOL proof of `BOOL_EQ_DISTINCT` (HOL Light `bool.ml`),
  reproduced rule for rule.

  SPELLING OF THE DISTINCTION. We use boolean EQUALITY literally:
  `distinguishes a b := Nonempty (⊢ ¬(a = b))`. The denotation sends `Eq` at
  bool to `Iff`, which is exactly HOL's semantics of `=` at type `:bool` in
  the standard two-element model: in HOL, boolean equality and bi-implication
  coincide (boolean extensionality / `EQ_IFF`), so `Iff` is the faithful
  meta-level reading, not a substitute.

  FRAGMENT SOUNDNESS AND NON-VACUITY. `HOLTerm.denote` interprets the
  fragment in the standard model (`T ↦ True`, `F ↦ False`, `¬ ↦ Not`,
  `⟹ ↦ →`, `= ↦ Iff`); `holderiv_sound` proves every derivable sequent true
  in the model by induction on the derivation tree; `model_separates` shows
  the model itself separates the endpoints; `holderiv_no_eq` combines them:
  the kernel does NOT derive `T = F`, so `distinguishes` is not the total
  relation (`holSystem_not_total` exhibits an undistinguished pair). The
  distinction is earned by a derivation and blocked from vacuity by
  soundness.

  HONEST BOUNDARY. This is the propositional core of HOL: no lambda calculus
  (no MK_COMB / ABS / BETA / INST), no polymorphism (no INST_TYPE), no
  Hilbert choice (ε, SELECT_AX), no axiom of infinity, and `=` only at the
  bool type. The boundary does not weaken the δ conclusion: δ needs exactly
  the endpoint distinction `⊢ ¬(T = F)` and a monotone expression order, and
  every rule here is a rule of full HOL, so any extension of this kernel to
  full HOL still derives `deriv_T_ne_F` verbatim (adding rules can only
  enlarge the set of derivable sequents, and full HOL is consistent, so the
  non-vacuity guard survives extension as well). The omitted machinery buys
  expressivity beyond the distinction; it cannot remove the distinction.

  No project-local axioms. No sorry.
-/

import ActualMathematics.PRCDistinctionDichotomy

namespace ActualMathematics
namespace SyntacticHOL

open FormalSystem

/-! ### The HOL term fragment -/

/-- Propositional HOL terms at the bool type: the constants `T` and `F`,
negation, implication, and boolean equality. In full HOL these are lambda
terms over `=` and `⟹`; here they are primitive constructors (see the module
header for the boundary). -/
inductive HOLTerm : Type where
  /-- The HOL constant `T` (truth). -/
  | trueC : HOLTerm
  /-- The HOL constant `F` (falsity). -/
  | falseC : HOLTerm
  /-- HOL negation `¬`. -/
  | not : HOLTerm → HOLTerm
  /-- HOL implication `⟹`. -/
  | imp : HOLTerm → HOLTerm → HOLTerm
  /-- HOL equality `=` at the bool type. -/
  | eq : HOLTerm → HOLTerm → HOLTerm
  deriving DecidableEq, Repr

/-! ### The HOL derivation kernel (sequents as positive data) -/

/-- HOL sequents `Γ ⊢ t` as a derivation KERNEL: an inductive family of
finite trees, one constructor per kernel rule (names against the HOL Light /
HOL4 rule list; see the module header). A derivation is data, not a host
proposition; there is no rule that closes a goal without a complete
sub-tree. -/
inductive HOLDeriv : List HOLTerm → HOLTerm → Type where
  /-- TRUTH: `Γ ⊢ T`. -/
  | truth {Γ : List HOLTerm} : HOLDeriv Γ HOLTerm.trueC
  /-- ASSUME (with weakening): a hypothesis of the context is derivable. -/
  | assum {Γ : List HOLTerm} {t : HOLTerm} (h : t ∈ Γ) : HOLDeriv Γ t
  /-- REFL: `Γ ⊢ t = t`. -/
  | refl {Γ : List HOLTerm} (t : HOLTerm) : HOLDeriv Γ (HOLTerm.eq t t)
  /-- EQ_MP: from `Γ ⊢ a = b` and `Γ ⊢ a` conclude `Γ ⊢ b`. -/
  | eq_mp {Γ : List HOLTerm} {a b : HOLTerm}
      (dab : HOLDeriv Γ (HOLTerm.eq a b)) (da : HOLDeriv Γ a) : HOLDeriv Γ b
  /-- MP: from `Γ ⊢ a ⟹ b` and `Γ ⊢ a` conclude `Γ ⊢ b`. -/
  | mp {Γ : List HOLTerm} {a b : HOLTerm}
      (dab : HOLDeriv Γ (HOLTerm.imp a b)) (da : HOLDeriv Γ a) : HOLDeriv Γ b
  /-- DISCH: discharge the head hypothesis into an implication. -/
  | disch {Γ : List HOLTerm} {b : HOLTerm} (a : HOLTerm)
      (d : HOLDeriv (a :: Γ) b) : HOLDeriv Γ (HOLTerm.imp a b)
  /-- NOT_INTRO: from `Γ ⊢ a ⟹ F` conclude `Γ ⊢ ¬a`. -/
  | not_intro {Γ : List HOLTerm} {a : HOLTerm}
      (d : HOLDeriv Γ (HOLTerm.imp a HOLTerm.falseC)) : HOLDeriv Γ (HOLTerm.not a)
  /-- NOT_ELIM: from `Γ ⊢ ¬a` conclude `Γ ⊢ a ⟹ F`. -/
  | not_elim {Γ : List HOLTerm} {a : HOLTerm}
      (d : HOLDeriv Γ (HOLTerm.not a)) : HOLDeriv Γ (HOLTerm.imp a HOLTerm.falseC)

/-- A HOL theorem is a sequent with the empty context: `⊢ t`. -/
abbrev HOLThm (t : HOLTerm) : Type := HOLDeriv [] t

/-! ### The target derivation: `⊢ ¬(T = F)` -/

/-- **The endpoint separation, derived inside the HOL kernel.** The standard
HOL proof of `BOOL_EQ_DISTINCT`, rule for rule: ASSUME `T = F`; TRUTH gives
`⊢ T`; EQ_MP rewrites it to `F` under the assumption; DISCH discharges to
`⊢ (T = F) ⟹ F`; NOT_INTRO closes `⊢ ¬(T = F)`. A five-node finite tree. -/
def deriv_T_ne_F : HOLThm (HOLTerm.not (HOLTerm.eq HOLTerm.trueC HOLTerm.falseC)) :=
  HOLDeriv.not_intro
    (HOLDeriv.disch (HOLTerm.eq HOLTerm.trueC HOLTerm.falseC)
      (HOLDeriv.eq_mp
        (HOLDeriv.assum (List.Mem.head _))
        HOLDeriv.truth))

/-! ### Fragment soundness in the standard model -/

/-- The standard two-element model of the fragment: `T ↦ True`, `F ↦ False`,
`¬ ↦ Not`, `⟹ ↦ →`, and `=` at bool `↦ Iff` (HOL's boolean equality and
bi-implication coincide by boolean extensionality). -/
def HOLTerm.denote : HOLTerm → Prop
  | HOLTerm.trueC => True
  | HOLTerm.falseC => False
  | HOLTerm.not t => ¬ t.denote
  | HOLTerm.imp a b => a.denote → b.denote
  | HOLTerm.eq a b => a.denote ↔ b.denote

/-- A context holds in the model when every hypothesis does. -/
def CtxDenote (Γ : List HOLTerm) : Prop := ∀ t, t ∈ Γ → t.denote

/-- **Fragment soundness.** Every kernel-derivable sequent is true in the
standard model, by induction on the derivation tree. -/
theorem holderiv_sound : ∀ {Γ : List HOLTerm} {t : HOLTerm},
    HOLDeriv Γ t → CtxDenote Γ → t.denote
  | _, _, HOLDeriv.truth, _ => True.intro
  | _, _, HOLDeriv.assum h, hΓ => hΓ _ h
  | _, _, HOLDeriv.refl _, _ => Iff.rfl
  | _, _, HOLDeriv.eq_mp dab da, hΓ =>
      (holderiv_sound dab hΓ).mp (holderiv_sound da hΓ)
  | _, _, HOLDeriv.mp dab da, hΓ =>
      (holderiv_sound dab hΓ) (holderiv_sound da hΓ)
  | _, _, HOLDeriv.disch a d, hΓ => fun ha =>
      holderiv_sound d (fun u hu => by
        cases hu with
        | head => exact ha
        | tail _ hu' => exact hΓ u hu')
  | _, _, HOLDeriv.not_intro d, hΓ => fun ha => holderiv_sound d hΓ ha
  | _, _, HOLDeriv.not_elim d, hΓ => fun ha => holderiv_sound d hΓ ha

/-- Soundness for theorems: the empty context holds vacuously. -/
theorem holthm_sound {t : HOLTerm} (d : HOLThm t) : t.denote :=
  holderiv_sound d (fun _ hu => nomatch hu)

/-- **Model separation.** The standard model tells the two endpoints apart. -/
theorem model_separates : ¬ (True ↔ False) :=
  fun h => h.mp True.intro

/-! ### Non-vacuity guards -/

/-- **Non-vacuity.** The kernel does NOT derive `T = F`: soundness would put
`True ↔ False` in the model, against `model_separates`. -/
theorem holderiv_no_eq
    (d : HOLThm (HOLTerm.eq HOLTerm.trueC HOLTerm.falseC)) : False :=
  model_separates (holthm_sound d)

/-- Consistency of the fragment: the kernel does not derive `F`. -/
theorem holderiv_consistent (d : HOLThm HOLTerm.falseC) : False :=
  holthm_sound d

/-! ### The parse into the δ interface -/

/-- The HOL kernel parsed into the `FormalSystem` interface. Tokens are HOL
terms; the discrimination relation is PROOF-THEORETIC: two terms are
distinguished exactly when the kernel DERIVES their negated boolean equation
`⊢ ¬(a = b)`. The endpoints are the genuine HOL constants `T` and `F`; the
expression order is the derivation-length order. -/
def holSystem : FormalSystem where
  Token := HOLTerm
  Expr := ℕ
  distinguishes := fun a b => Nonempty (HOLThm (HOLTerm.not (HOLTerm.eq a b)))
  exprExtends := fun m n => m ≤ n
  endpointToken := fun e =>
    match e.side with
    | Side.left => HOLTerm.trueC
    | Side.right => HOLTerm.falseC
  traceExpr := Trace.length
  traceExpr_extends := fun h => InevitabilityInstances.length_le_of_extends h

/-- `holSystem` distinguishes its endpoints: the kernel derivation
`deriv_T_ne_F` is the witness. The distinction is a finite proof tree, not a
semantic relabelling. -/
theorem holSystem_expressive : holSystem.Expressive :=
  ⟨deriv_T_ne_F⟩

/-- **The HOL kernel contains the δ core.** -/
theorem holSystem_embeds_delta : Nonempty (PRCEmbeddingInto holSystem) :=
  FormalSystemEmbeddingTarget_proved holSystem holSystem_expressive

theorem holSystem_exprReflexive : DistinctionDichotomy.ExprReflexive holSystem :=
  fun n => Nat.le_refl n

/-- The HOL kernel falls on the δ side of the distinction dichotomy: it is
non-degenerate, hence realizes δ. -/
theorem holSystem_not_degenerate : ¬ DistinctionDichotomy.Degenerate holSystem :=
  DistinctionDichotomy.not_degenerate_of_realizesDelta holSystem holSystem_embeds_delta

/-- The discrimination relation is not the total relation: the kernel cannot
distinguish `T` from itself (soundness would refute `True ↔ True`). Together
with `holderiv_no_eq`, this shows `distinguishes` is earned derivation by
derivation, not vacuously true or vacuously symmetric. -/
theorem holSystem_not_total :
    ¬ holSystem.distinguishes HOLTerm.trueC HOLTerm.trueC := by
  rintro ⟨d⟩
  exact (holthm_sound d) Iff.rfl

/-! ### Capstone -/

/-- **The syntactic HOL parse, packaged.** The propositional HOL kernel:
(i) is sound for the standard model, (ii) DERIVES the endpoint separation
`⊢ ¬(T = F)` as a finite proof tree, (iii) has a model that separates the
endpoints, (iv) does not derive `T = F` (non-vacuity), and (v) realizes the
δ core. -/
theorem syntactic_hol_realizes_delta :
    (∀ (Γ : List HOLTerm) (t : HOLTerm), HOLDeriv Γ t → CtxDenote Γ → t.denote)
      ∧ Nonempty (HOLThm (HOLTerm.not (HOLTerm.eq HOLTerm.trueC HOLTerm.falseC)))
      ∧ (¬ (True ↔ False))
      ∧ (HOLThm (HOLTerm.eq HOLTerm.trueC HOLTerm.falseC) → False)
      ∧ Nonempty (PRCEmbeddingInto holSystem) :=
  ⟨fun _ _ d hΓ => holderiv_sound d hΓ, ⟨deriv_T_ne_F⟩, model_separates,
    holderiv_no_eq, holSystem_embeds_delta⟩

end SyntacticHOL
end ActualMathematics

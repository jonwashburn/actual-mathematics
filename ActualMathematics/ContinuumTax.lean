/-
  ActualMathematics/ContinuumTax.lean

  THE CONTINUUM TAX: renormalization as interest on the continuum purchase.

  ## The claim being formalized

  Article IV of the delta program (`RealLineNonNativity`) proves the real
  continuum is a purchase, not forced by distinction. Article IX bets that
  some classical hardness is encoding overhead. This module turns that bet
  on physics: the ultraviolet divergences of continuum field theory are
  exactly UNCERTIFIED DISPLAY ARTIFACTS in the sense of
  `CompletionConservativity`, and renormalization is the bookkeeping
  procedure that pays the tax: it splits a divergent display into a
  divergent counterterm (the interest on the continuum purchase) plus a
  certified finite residue (the physics).

  ## What is THEOREM here (the accounting layer, all proved, no sorry)

  1. `diverges_uncertified` / `continuum_creates_artifacts` /
     `divergence_not_conservative`: a UV-divergent cutoff display carries
     no finite certificate. The bare quantity has no value; it exists only
     as display. Divergent displays are artifacts, so the cutoff completion
     is non-conservative for divergence: the purchase creates artifacts.
  2. `residue_certificate` / `counterterm_diverges`: in any renormalization
     scheme for a divergent display, the residue is certified and the
     counterterm is itself divergent. The interest is unbounded; only the
     residue is physics.
  3. `scheme_ambiguity_finite` / `value_unique_of_counterterm_agree`: any
     two schemes for the same display differ by a CERTIFIED (finite)
     amount. Scheme dependence is finite renormalization, never a second
     divergence. This is the formal content of "the physics does not
     depend on how you pay the tax, only on having paid it."
  4. The phi-native ledger pays no tax (`native_certified`,
     `flat_diverges`, `tax_diverges`, `canonicalScheme`,
     `renormalized_value_eq_native`): weighting the rung ladder with the
     T9-forced measure phi^(-n) (`MeasureForcing.weight_forced`) makes the
     mode sum converge to c * phi^2 (the partition identity Z = phi^2,
     `MeasureForcing.partitionZ_eq_phi_sq`). Weighting the same ladder
     flat, which is what the unforced continuum bookkeeping does, diverges.
     The difference between the two bookkeepings, `continuumTax`, grows
     without bound, and the canonical renormalization scheme for the flat
     sum has counterterm exactly the tax and renormalized value exactly
     the native total. Renormalization recovers the number the forced
     measure assigned from the start.

  ## What is HYPOTHESIS (the physical bet, named, falsifiable)

  That the counterterms of actual renormalizable QFT are continuum-tax
  terms in the above sense: that a delta-native presentation of a
  renormalizable theory (countably generated carrier, phi-forced measure
  on modes) has finite bare quantities, with the subtraction step absent
  rather than performed. Falsifier: a delta-native rewrite of a concrete
  renormalizable observable (e.g. a one-loop QED quantity) that still
  requires a divergent subtraction; or a measured observable that tracks
  the flat-weighted display where the phi-native sum predicts otherwise.
  Precedent: ILG replaced the dark-matter fit with a weighted kernel; this
  module states the analogous accounting for UV divergences.

  This module proves the accounting layer only. It does not derive QFT.

  No project-local axioms. No sorry.
-/

import Mathlib
import ActualMathematics.MeasureForcing
import ActualMathematics.CompletionConservativity
import ActualMathematics.RealLineNonNativity

namespace ActualMathematics
namespace ContinuumTax

open Filter Topology
open CompletionConservativity

noncomputable section

/-! ## §0. Cutoff displays and divergence -/

/-- A cutoff display: a physical quantity presented as a function of the rung
cutoff. This is the regulated object of continuum field theory; the "bare
quantity at infinite cutoff" is whatever the display does as the cutoff is
removed. -/
abbrev CutoffDisplay := ℕ → ℝ

/-- UV divergence: the display grows without bound as the cutoff is removed. -/
def Diverges (A : CutoffDisplay) : Prop := Tendsto A atTop atTop

/-- A finite certificate for a cutoff display: a value the display settles on
as the cutoff is removed. This is the only sense in which a regulated quantity
HAS a value. -/
def CertifiedAt (L : ℝ) (A : CutoffDisplay) : Prop := Tendsto A atTop (nhds L)

/-- **A divergent display carries no finite certificate.** The bare quantity of
a UV-divergent theory does not have a value; it exists only as display. -/
theorem diverges_uncertified {A : CutoffDisplay} (hA : Diverges A) :
    ¬ ∃ L : ℝ, CertifiedAt L A := by
  rintro ⟨L, hL⟩
  exact not_tendsto_nhds_of_tendsto_atTop hA L hL

/-! ## §1. The completion interface: divergences are artifacts -/

/-- The cutoff completion: native data are the displays that settle (carry a
limit), the display type is all cutoff families, and a certificate is a claimed
limit value. This is the `CompletionConservativity` interface for removing a
regulator. -/
def cutoffCompletion :
    Completion {f : CutoffDisplay // ∃ L : ℝ, CertifiedAt L f} CutoffDisplay ℝ where
  display := Subtype.val
  certifies := CertifiedAt

/-- **The continuum purchase creates artifacts.** There is a divergent display
(witness: the linear divergence `n`) satisfying the divergence predicate yet
carrying no certificate. In the doctrine's vocabulary: UV divergences are
uncertified display witnesses. -/
theorem continuum_creates_artifacts :
    ArtifactFor cutoffCompletion Diverges := by
  refine ⟨fun n => (n : ℝ), tendsto_natCast_atTop_atTop, ?_⟩
  exact diverges_uncertified tendsto_natCast_atTop_atTop

/-- The cutoff completion is NOT conservative for divergence: divergent
displays never descend to native certificates. This is the formal statement
that the divergence lives in the purchased layer, not in the native ontology. -/
theorem divergence_not_conservative :
    ¬ ConservativeFor cutoffCompletion Diverges := fun h =>
  (conservative_iff_no_artifact cutoffCompletion Diverges).mp h continuum_creates_artifacts

/-! ## §2. Renormalization schemes: paying the tax -/

/-- A renormalization scheme for a cutoff display: a decomposition into a
counterterm (the subtraction) and a residue that settles on a finite
renormalized value. This is the shape of every regulator-and-subtract
procedure. -/
structure Scheme (A : CutoffDisplay) where
  /-- The subtracted part (the counterterm). -/
  counterterm : CutoffDisplay
  /-- The retained part (the renormalized, cutoff-dependent quantity). -/
  residue : CutoffDisplay
  /-- The scheme is exact bookkeeping: nothing is discarded, only split. -/
  split : ∀ n, A n = counterterm n + residue n
  /-- The renormalized value. -/
  value : ℝ
  /-- The residue is certified at the renormalized value. -/
  residue_certified : CertifiedAt value residue

/-- The residue of any scheme carries a certificate in the cutoff completion:
renormalization is exactly the construction of a certified quantity from an
uncertified display. -/
theorem residue_certificate {A : CutoffDisplay} (S : Scheme A) :
    ∃ c : ℝ, cutoffCompletion.certifies c S.residue :=
  ⟨S.value, S.residue_certified⟩

/-- **The interest is unbounded.** For a divergent display, the counterterm of
ANY scheme is itself divergent: the entire divergence is paid by the
subtraction, never absorbed into the residue. The tax cannot be made finite by
clever bookkeeping; it can only be isolated. -/
theorem counterterm_diverges {A : CutoffDisplay} (hA : Diverges A) (S : Scheme A) :
    Diverges S.counterterm := by
  have hbound : ∀ᶠ n in atTop, S.residue n ≤ S.value + 1 :=
    S.residue_certified.eventually (eventually_le_nhds (lt_add_one S.value))
  have hmono : (fun n => A n + -(S.value + 1)) ≤ᶠ[atTop] S.counterterm := by
    filter_upwards [hbound] with n hn
    have hsplit := S.split n
    linarith
  have hdiv : Tendsto (fun n => A n + -(S.value + 1)) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-(S.value + 1)) hA
  exact tendsto_atTop_mono' atTop hmono hdiv

/-- **Scheme dependence is finite.** Any two schemes for the same display have
counterterms whose difference is certified at the (finite) difference of the
renormalized values. Two ways of paying the tax differ by a finite
renormalization, never by a second divergence. -/
theorem scheme_ambiguity_finite {A : CutoffDisplay} (S T : Scheme A) :
    CertifiedAt (T.value - S.value) (fun n => S.counterterm n - T.counterterm n) := by
  have h : ∀ n, T.residue n - S.residue n = S.counterterm n - T.counterterm n := by
    intro n
    have hS := S.split n
    have hT := T.split n
    linarith
  exact (T.residue_certified.sub S.residue_certified).congr h

/-- Schemes with (eventually) the same counterterm assign the same renormalized
value: once the tax payment is fixed, the physics is unique. -/
theorem value_unique_of_counterterm_agree {A : CutoffDisplay} (S T : Scheme A)
    (h : ∀ᶠ n in atTop, S.counterterm n = T.counterterm n) :
    S.value = T.value := by
  have hres : S.residue =ᶠ[atTop] T.residue := by
    filter_upwards [h] with n hn
    have hS := S.split n
    have hT := T.split n
    linarith
  exact tendsto_nhds_unique (S.residue_certified.congr' hres) T.residue_certified

/-! ## §3. The phi-native ledger pays no tax

The teeth. The T9 forced measure (`MeasureForcing`) weights rung `n` by
`phi^(-n)`; the unforced continuum bookkeeping weights every rung flat. With
per-rung content `c > 0`: the native sum converges to `c * phi^2` (the
partition identity `Z = phi^2`), the flat sum diverges, and their gap, the
continuum tax, grows without bound. -/

/-- Flat partial mode sum: every rung weighted 1. This is the unforced
(continuum-display) bookkeeping of a mode sum with per-rung content `c`. -/
def flatPartial (c : ℝ) (N : ℕ) : ℝ := ∑ _n ∈ Finset.range N, c

/-- Phi-native partial mode sum: rung `n` weighted by the T9-forced measure
`rho^n = phi^(-n)` (`MeasureForcing.weight_forced`). -/
def nativePartial (c : ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.range N, c * MeasureForcing.rho ^ n

/-- The phi-native total: `c * phi^2`, the per-rung content times the partition
function `Z = phi^2` of the forced measure. -/
def nativeTotal (c : ℝ) : ℝ := c * Constants.phi ^ 2

theorem flatPartial_eq (c : ℝ) (N : ℕ) : flatPartial c N = (N : ℝ) * c := by
  unfold flatPartial
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **The flat bookkeeping diverges.** Any positive per-rung content, summed
with the unforced flat weights, is UV-divergent. -/
theorem flat_diverges {c : ℝ} (hc : 0 < c) : Diverges (flatPartial c) := by
  have h : Tendsto (fun N : ℕ => (N : ℝ) * c) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hc
  exact h.congr fun N => (flatPartial_eq c N).symm

/-- The phi-native mode sum converges, with total `c * phi^2`. The value is the
partition identity `Z = phi^2` of the forced measure
(`MeasureForcing.partitionZ_eq_phi_sq`), scaled by the per-rung content. -/
theorem native_hasSum (c : ℝ) :
    HasSum (fun n : ℕ => c * MeasureForcing.rho ^ n) (nativeTotal c) := by
  have hgeom : HasSum (fun n : ℕ => MeasureForcing.rho ^ n) (1 - MeasureForcing.rho)⁻¹ :=
    hasSum_geometric_of_lt_one MeasureForcing.rho_nonneg MeasureForcing.rho_lt_one
  have hval : (1 - MeasureForcing.rho)⁻¹ = Constants.phi ^ 2 := by
    rw [MeasureForcing.one_sub_rho, one_div, inv_inv]
  have h := hgeom.mul_left c
  rw [hval] at h
  exact h

/-- **The phi-native ledger is certified.** The native partial sums settle on
the native total: under the forced measure there is no divergence to subtract,
hence no tax to pay. -/
theorem native_certified (c : ℝ) : CertifiedAt (nativeTotal c) (nativePartial c) :=
  (native_hasSum c).tendsto_sum_nat

/-- The continuum tax at cutoff `N`: what the flat bookkeeping owes beyond the
phi-native sum at the same cutoff. -/
def continuumTax (c : ℝ) (N : ℕ) : ℝ := flatPartial c N - nativePartial c N

/-- **The canonical renormalization scheme for the flat mode sum.** Counterterm
= the continuum tax; residue = the phi-native partial sum; renormalized value =
the phi-native total. Renormalizing the flat display recovers exactly the
number the forced measure assigned from the start. -/
def canonicalScheme (c : ℝ) : Scheme (flatPartial c) where
  counterterm := continuumTax c
  residue := nativePartial c
  split := fun n => by unfold continuumTax; ring
  value := nativeTotal c
  residue_certified := native_certified c

/-- **The tax is unbounded.** The gap between the flat and the phi-native
bookkeepings diverges as the cutoff is removed: the interest on the continuum
purchase grows without bound. -/
theorem tax_diverges {c : ℝ} (hc : 0 < c) : Diverges (continuumTax c) :=
  counterterm_diverges (flat_diverges hc) (canonicalScheme c)

/-- Any scheme for the flat mode sum whose counterterm eventually agrees with
the continuum tax assigns the phi-native total as its renormalized value: the
renormalized physics IS the native sum. -/
theorem renormalized_value_eq_native {c : ℝ} (S : Scheme (flatPartial c))
    (h : ∀ᶠ n in atTop, S.counterterm n = continuumTax c n) :
    S.value = nativeTotal c :=
  value_unique_of_counterterm_agree S (canonicalScheme c) h

/-! ## §4. Certificate -/

/-- **Continuum Tax Certificate.** Bundles the accounting layer: the continuum
purchase is non-native (cardinality teeth from `RealLineNonNativity`),
divergent displays are uncertified artifacts, every scheme's counterterm
inherits the full divergence while its residue is certified, scheme ambiguity
is finite, and the phi-native ledger converges where the flat ledger diverges,
with the canonical scheme's renormalized value equal to the native total. -/
structure ContinuumTaxCert : Prop where
  /-- The purchase: no countable certificate system faithfully covers ℝ. -/
  purchase_nonnative :
    ∀ {Cert : Type} [Countable Cert] (assign : ℝ → Cert),
      ¬ RealLineNonNativity.Faithful assign
  /-- Divergent displays are uncertified artifacts of the cutoff completion. -/
  artifact : ArtifactFor cutoffCompletion Diverges
  /-- The cutoff completion is not conservative for divergence. -/
  not_conservative : ¬ ConservativeFor cutoffCompletion Diverges
  /-- No divergent display carries a finite certificate: bare values of
  UV-divergent quantities do not exist. -/
  no_bare_value : ∀ A : CutoffDisplay, Diverges A → ¬ ∃ L : ℝ, CertifiedAt L A
  /-- Every scheme for a divergent display has a divergent counterterm. -/
  interest_unbounded :
    ∀ (A : CutoffDisplay) (S : Scheme A), Diverges A → Diverges S.counterterm
  /-- Any two schemes differ by a certified finite renormalization. -/
  ambiguity_finite :
    ∀ (A : CutoffDisplay) (S T : Scheme A),
      CertifiedAt (T.value - S.value) (fun n => S.counterterm n - T.counterterm n)
  /-- The phi-native mode sum is certified at `c * phi^2`. -/
  native_pays_no_tax : ∀ c : ℝ, CertifiedAt (nativeTotal c) (nativePartial c)
  /-- The flat (continuum) mode sum diverges for positive content. -/
  flat_owes : ∀ c : ℝ, 0 < c → Diverges (flatPartial c)
  /-- The continuum tax grows without bound. -/
  tax_unbounded : ∀ c : ℝ, 0 < c → Diverges (continuumTax c)
  /-- Renormalizing the flat display recovers the native total. -/
  renormalization_recovers_native :
    ∀ c : ℝ, (canonicalScheme c).value = nativeTotal c

/-- The certificate holds. -/
theorem continuumTaxCert_holds : ContinuumTaxCert where
  purchase_nonnative := fun assign => RealLineNonNativity.real_not_faithfully_certifiable assign
  artifact := continuum_creates_artifacts
  not_conservative := divergence_not_conservative
  no_bare_value := fun _A hA => diverges_uncertified hA
  interest_unbounded := fun _A S hA => counterterm_diverges hA S
  ambiguity_finite := fun _A S T => scheme_ambiguity_finite S T
  native_pays_no_tax := native_certified
  flat_owes := fun _c hc => flat_diverges hc
  tax_unbounded := fun _c hc => tax_diverges hc
  renormalization_recovers_native := fun _c => rfl

end

end ContinuumTax
end ActualMathematics

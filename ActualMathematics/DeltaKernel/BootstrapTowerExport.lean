import ActualMathematics.IntegerRational
import ActualMathematics.Orbit
import ActualMathematics.DeltaForced
import ActualMathematics.Representability
import ActualMathematics.Strength
import ActualMathematics.DeltaKernel.BootstrapDemarcation

/-!
# Bootstrap F2: tower export ℤδ / ℚδ

Export the forced constructions above the free orbit carrier, with exact
free-versus-constructed tags.

* `DistinctionNat` (ℕδ): **free** / initial unary orbit.
* `PRCInt` (ℤδ): **constructed** by group completion (balanced signed orbits).
* `PRCRat` (ℚδ): **constructed** by field-of-fractions (ratio orbits).

Every certificate here is choice-free ({propext, Quot.sound} at most), so the
whole export carries `StrengthTag.deltaOnly`:

* ℕδ injects into ℕ by the `toNat` display; injectivity is the `ofNat`
  retraction (no simp, no classical decidability).
* ℤδ injects by composing the choice-free even/odd certificate with the
  quotient display `PRCInt.toInt` (injective by `Quot.sound`).
* ℚδ does **not** route through the classical ℚ display
  (`crossEq_iff_toRat_eq` consumes `Classical.choice` via Mathlib's rational
  field). Instead we give a covering decoder (`Forced.Representation`) built
  from the choice-free `findPair`, derive decidable equality on the quotient
  from decidable cross-multiplication, and extract the least-code injection
  via `Forced.deltaForced_of_representable` (`Nat.find`, choice-free).

These are δ-forced carriers under the F1 certificate reading. They are not
primitive set-theoretic objects.
-/

namespace ActualMathematics.DeltaKernel.Bootstrap

open ActualMathematics
open ActualMathematics.Forced

/-- Construction provenance for tower objects. -/
inductive TowerProvenance where
  | freeInitial
  | constructedGroupCompletion
  | constructedFractions
  deriving DecidableEq, Repr

/-- Named tower export with provenance tag. -/
structure TowerExport (X : Type) where
  provenance : TowerProvenance
  deltaForced : Forced.DeltaForced X
  displayName : String

/-- ℕδ: the free / initial orbit of repeated distinction. -/
abbrev NatDelta := DistinctionNat

/-- ℤδ: group completion of the orbit (signed balanced quotient). -/
abbrev IntDelta := PRCInt

/-- ℚδ: fractions of ℤδ (ratio-orbit quotient). -/
abbrev RatDelta := PRCRat

/-- Explicit certificate for ℕδ. Injectivity of the `toNat` display is the
`ofNat` retraction; no classical decidability enters. -/
theorem deltaForced_natDelta : Forced.DeltaForced NatDelta :=
  ⟨⟨DistinctionNat.toNat, fun a b h => by
      rw [← DistinctionNat.ofNat_toNat a, ← DistinctionNat.ofNat_toNat b, h]⟩⟩

/-- ℤδ is δ-forced: even/odd certificate after the injective quotient
display. Choice-free. -/
theorem deltaForced_intDelta : Forced.DeltaForced IntDelta :=
  ⟨⟨fun z => intToNat (PRCInt.toInt z), fun a b h =>
      PRCInt.toInt_injective (intToNat_inj h)⟩⟩

/-! ### A choice-free certificate for ℚδ

The quotient `PRCRat` is identified by cross-multiplication, which is
decidable (`SignedOrbit.balanced` is). A covering decoder plus decidable
equality yields the least-code injection without ever touching the classical
ℚ display. -/

instance instDecidableCrossEq (a b : RatioOrbit) :
    Decidable (RatioOrbit.crossEq a b) :=
  inferInstanceAs (Decidable (SignedOrbit.balanced _ _))

/-- Signed orbit displaying a given verifier integer (positive part minus
negative part). -/
def signedOfInt (n : ℤ) : SignedOrbit :=
  ⟨DistinctionNat.ofNat n.toNat, DistinctionNat.ofNat (-n).toNat⟩

theorem signedOfInt_toInt (n : ℤ) : (signedOfInt n).toInt = n := by
  show ((DistinctionNat.ofNat n.toNat).toNat : ℤ) -
      ((DistinctionNat.ofNat (-n).toNat).toNat : ℤ) = n
  rw [DistinctionNat.toNat_ofNat, DistinctionNat.toNat_ofNat]
  omega

/-- Ratio orbit decoded from a numerator code and a nonzero denominator. -/
def ratioOrbitOfCode (a b : ℕ) (hb : b ≠ 0) : RatioOrbit where
  num := signedOfInt (intFromNat a)
  den := DistinctionNat.ofNat b
  den_ne_zero := fun h => hb (by
    have h' := congrArg DistinctionNat.toNat h
    rwa [DistinctionNat.toNat_ofNat, DistinctionNat.toNat_zero] at h')

/-- The canonical code of a ratio orbit: paired numerator and denominator
displays, via the choice-free local pairing. -/
def codeOfRatioOrbit (q : RatioOrbit) : ℕ :=
  dpair (intToNat q.num.toInt) q.den.toNat

/-- Covering decoder for ℚδ: split the code, rebuild the ratio orbit, take the
quotient class. Never routes through the classical ℚ display. -/
def decodeRatDelta (m : ℕ) : Option RatDelta :=
  (findPair m).bind fun p =>
    if hb : p.2 ≠ 0 then some (PRCRat.mk (ratioOrbitOfCode p.1 p.2 hb)) else none

theorem decodeRatDelta_complete (x : RatDelta) :
    ∃ n : ℕ, decodeRatDelta n = some x := by
  refine Quot.induction_on x (fun q => ?_)
  refine ⟨codeOfRatioOrbit q, ?_⟩
  unfold decodeRatDelta codeOfRatioOrbit
  rw [findPair_eq]
  show (if hb : q.den.toNat ≠ 0 then
      some (PRCRat.mk (ratioOrbitOfCode (intToNat q.num.toInt) q.den.toNat hb))
    else none) = some (Quot.mk _ q)
  rw [dif_pos (q.den_toNat_ne_zero : q.den.toNat ≠ 0)]
  refine congrArg some (PRCRat.mk_eq_mk_of_crossEq ?_)
  rw [RatioOrbit.crossEq_iff_toIntCross]
  show (signedOfInt (intFromNat (intToNat q.num.toInt))).toInt *
      (q.den.toNat : ℤ) =
    q.num.toInt * (((DistinctionNat.ofNat q.den.toNat).toNat : ℕ) : ℤ)
  rw [signedOfInt_toInt, intFromNat_intToNat, DistinctionNat.toNat_ofNat]

/-- The covering decoder, packaged. -/
def reprRatDelta : Forced.Representation RatDelta where
  decode := decodeRatDelta
  complete := decodeRatDelta_complete

theorem representable_ratDelta : Forced.DeltaRepresentable RatDelta :=
  ⟨reprRatDelta⟩

/-- Boolean equality test on the quotient, lifted from decidable
cross-multiplication. -/
def ratDeltaEqb : RatDelta → RatDelta → Bool :=
  Quot.lift₂ (fun a b => decide (RatioOrbit.crossEq a b))
    (fun _ _ _ h => decide_eq_decide.mpr
      ⟨fun hab => RatioOrbit.crossEq_trans hab h,
       fun hab => RatioOrbit.crossEq_trans hab (RatioOrbit.crossEq_symm h)⟩)
    (fun _ _ _ h => decide_eq_decide.mpr
      ⟨fun hab => RatioOrbit.crossEq_trans (RatioOrbit.crossEq_symm h) hab,
       fun hab => RatioOrbit.crossEq_trans h hab⟩)

theorem ratDeltaEqb_self (x : RatDelta) : ratDeltaEqb x x = true := by
  refine Quot.induction_on x (fun a => ?_)
  exact decide_eq_true (RatioOrbit.crossEq_refl a)

theorem ratDeltaEqb_iff (x y : RatDelta) :
    ratDeltaEqb x y = true ↔ x = y := by
  constructor
  · refine Quot.induction_on x (fun a => ?_)
    refine Quot.induction_on y (fun b => ?_)
    intro h
    exact PRCRat.mk_eq_mk_of_crossEq (of_decide_eq_true h)
  · intro h
    rw [h]
    exact ratDeltaEqb_self y

/-- Decidable equality on ℚδ, from decidable cross-multiplication. This is the
discreteness hypothesis the least-code injection consumes. -/
instance instDecidableEqRatDelta : DecidableEq RatDelta :=
  fun x y => decidable_of_iff (ratDeltaEqb x y = true) (ratDeltaEqb_iff x y)

/-- ℚδ is δ-forced, choice-free: least-code injection from the covering
decoder (`Nat.find`), never the classical ℚ display. -/
theorem deltaForced_ratDelta : Forced.DeltaForced RatDelta :=
  Forced.deltaForced_of_representable representable_ratDelta

/-! ### The tagged exports -/

def natDelta_export : TowerExport NatDelta where
  provenance := .freeInitial
  deltaForced := deltaForced_natDelta
  displayName := "NatDelta"

def intDelta_export : TowerExport IntDelta where
  provenance := .constructedGroupCompletion
  deltaForced := deltaForced_intDelta
  displayName := "IntDelta"

def ratDelta_export : TowerExport RatDelta where
  provenance := .constructedFractions
  deltaForced := deltaForced_ratDelta
  displayName := "RatDelta"

/-- Free-vs-constructed discipline for the forced tower. -/
structure BootstrapTowerExportSpec : Prop where
  nat_free : (natDelta_export).provenance = TowerProvenance.freeInitial
  int_constructed :
      (intDelta_export).provenance = TowerProvenance.constructedGroupCompletion
  rat_constructed :
      (ratDelta_export).provenance = TowerProvenance.constructedFractions
  nat_forced : Forced.DeltaForced NatDelta
  int_forced : Forced.DeltaForced IntDelta
  rat_forced : Forced.DeltaForced RatDelta
  int_display_inj : Function.Injective PRCInt.toInt
  rat_field_cancel :
      ∀ a : PRCRat, a ≠ PRCRat.zero →
        PRCRat.mul a (PRCRat.recip a) = PRCRat.one

theorem bootstrap_tower_export : BootstrapTowerExportSpec where
  nat_free := rfl
  int_constructed := rfl
  rat_constructed := rfl
  nat_forced := deltaForced_natDelta
  int_forced := deltaForced_intDelta
  rat_forced := deltaForced_ratDelta
  int_display_inj := PRCInt.toInt_injective
  rat_field_cancel := fun _ h => PRCRat.mul_recip_cancel₀ h

/-- The δ-native tower is forced at the `deltaOnly` stratum: every certificate
above is choice-free. -/
theorem bootstrap_tower_export_deltaOnly :
    Tagged StrengthTag.deltaOnly
      (Forced.DeltaForced NatDelta ∧ Forced.DeltaForced IntDelta ∧
        Forced.DeltaForced RatDelta) where
  holds := ⟨deltaForced_natDelta, deltaForced_intDelta, deltaForced_ratDelta⟩

#print axioms deltaForced_natDelta
#print axioms deltaForced_intDelta
#print axioms deltaForced_ratDelta
#print axioms bootstrap_tower_export
#print axioms bootstrap_tower_export_deltaOnly

end ActualMathematics.DeltaKernel.Bootstrap

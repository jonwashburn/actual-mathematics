/-
  ActualMathematics/DeltaKernel/RecognitionQuotients.lean

  Machine-checked forms of delta Paper 1, Section 6
  ("Recognition quotients of the generated orbit"):
  the index-period catalogue of additive congruences on the δ-orbit
  (`orbit_congruence_catalogue`) and the recognition dichotomy for
  additive monoid homomorphisms out of the orbit (`recognizer_dichotomy`).

  Metatheory note: the catalogue and dichotomy intentionally use classical
  logic (`Classical.choice` / decidability) in the classification argument.
  The constructive layer (`ipCon`, `orbitIpCon`, `ipCon_inj`, `Mip`) is
  choice-free and audits to `{propext, Quot.sound}` or smaller.
-/

import Mathlib.GroupTheory.Congruence.Basic
import Mathlib.GroupTheory.Congruence.Hom
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Data.Nat.ModEq
import ActualMathematics.OrbitArithmetic

namespace ActualMathematics
namespace DistinctionNat

/-! ## Additive monoid structure on the δ-orbit -/

instance instZero : Zero DistinctionNat := ⟨zero⟩

theorem zero_def : (0 : DistinctionNat) = zero := rfl

instance instAddCommMonoid : AddCommMonoid DistinctionNat where
  add := add
  add_assoc := add_assoc
  zero := zero
  zero_add := zero_add_eq
  add_zero := add_zero_eq
  add_comm := add_comm
  nsmul := nsmulRec

/-- Verifier display as an additive monoid isomorphism. -/
def addEquivNat : DistinctionNat ≃+ ℕ where
  toEquiv := equivNat
  map_add' := toNat_add

@[simp] theorem addEquivNat_apply (x : DistinctionNat) : addEquivNat x = toNat x := rfl
@[simp] theorem addEquivNat_symm_apply (n : ℕ) : addEquivNat.symm n = ofNat n := rfl

theorem ofNat_add (x y : ℕ) : ofNat (x + y) = ofNat x + ofNat y := by
  apply toNat_inj
  simp [toNat_add, toNat_ofNat]

end DistinctionNat

open DistinctionNat

/-! ## Index-period congruences on ℕ -/

/-- If `r < p` and `(a + r) % p = a % p`, then `r = 0`. -/
theorem add_mod_eq_left_of_lt {a r p : ℕ} (hp : 0 < p) (hr : r < p)
    (h : (a + r) % p = a % p) : r = 0 := by
  have h' : (a % p + r) % p = a % p := by
    simpa [Nat.add_mod] using h
  by_cases h0 : r = 0
  · exact h0
  · exfalso
    have hr0 : 0 < r := Nat.pos_of_ne_zero h0
    have ha : a % p < p := Nat.mod_lt a hp
    by_cases hsum : a % p + r < p
    · rw [Nat.mod_eq_of_lt hsum] at h'
      omega
    · have hge : p ≤ a % p + r := by omega
      have hsublt : a % p + r - p < p := by omega
      have : (a % p + r) % p = a % p + r - p := by
        rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsublt]
      omega

theorem dvd_sub_of_mod_eq {x y p : ℕ} (hp : 0 < p) (hle : x ≤ y) (hm : x % p = y % p) :
    p ∣ y - x := by
  rw [Nat.dvd_iff_mod_eq_zero]
  have hyx : x + (y - x) = y := Nat.add_sub_of_le hle
  have : (x + (y - x)) % p = y % p := by rw [hyx]
  have h' : (x % p + (y - x) % p) % p = y % p := by simpa [Nat.add_mod] using this
  rw [hm] at h'
  exact add_mod_eq_left_of_lt hp (Nat.mod_lt (y - x) hp) (by
    simpa [Nat.add_mod, Nat.mod_mod] using h')

/-- The classical index-period congruence on `(ℕ, +, 0)`.
`x ≈_{i,p} y` means equality, or both are past index `i` and congruent mod `p`. -/
def ipCon (i p : ℕ) (_hp : 0 < p) : AddCon ℕ where
  r x y := x = y ∨ (i ≤ x ∧ i ≤ y ∧ x % p = y % p)
  iseqv := {
    refl := fun x => Or.inl rfl
    symm := by
      intro x y h
      rcases h with h | ⟨hx, hy, hm⟩
      · exact Or.inl h.symm
      · exact Or.inr ⟨hy, hx, hm.symm⟩
    trans := by
      intro x y z hxy hyz
      rcases hxy with rfl | ⟨hx, hy, hxy⟩
      · exact hyz
      · rcases hyz with rfl | ⟨_, hz, hyz⟩
        · exact Or.inr ⟨hx, hy, hxy⟩
        · exact Or.inr ⟨hx, hz, hxy.trans hyz⟩
  }
  add' := by
    intro w x y z hwx hyz
    rcases hwx with rfl | ⟨hw, hx, hwx⟩
    · rcases hyz with rfl | ⟨hy, hz, hyz⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨Nat.le_trans hy (Nat.le_add_left y w),
            Nat.le_trans hz (Nat.le_add_left z w), ?_⟩
        simp [Nat.add_mod, hyz]
    · rcases hyz with rfl | ⟨hy, hz, hyz⟩
      · refine Or.inr ⟨Nat.le_trans hw (Nat.le_add_right w y),
            Nat.le_trans hx (Nat.le_add_right x y), ?_⟩
        simp [Nat.add_mod, hwx]
      · refine Or.inr ⟨Nat.le_trans hw (Nat.le_add_right w y),
            Nat.le_trans hx (Nat.le_add_right x z), ?_⟩
        simp [Nat.add_mod, hwx, hyz]

theorem ipCon_rel (i p : ℕ) (hp : 0 < p) (x y : ℕ) :
    ipCon i p hp x y ↔ x = y ∨ (i ≤ x ∧ i ≤ y ∧ x % p = y % p) :=
  Iff.rfl

theorem ipCon_of_mod (i p : ℕ) (hp : 0 < p) {x y : ℕ}
    (hx : i ≤ x) (hy : i ≤ y) (hm : x % p = y % p) :
    ipCon i p hp x y :=
  Or.inr ⟨hx, hy, hm⟩

/-- Past the index, adjoining one period stays in the congruence. -/
theorem ipCon_add_period (i p : ℕ) (hp : 0 < p) {n : ℕ} (hn : i ≤ n) :
    ipCon i p hp n (n + p) :=
  ipCon_of_mod i p hp hn (Nat.le_trans hn (Nat.le_add_right n p)) (by simp [Nat.add_mod])

/-- Characterization: `n ≈ n + p` holds iff `i ≤ n`. -/
theorem ipCon_add_period_iff (i p : ℕ) (hp : 0 < p) (n : ℕ) :
    ipCon i p hp n (n + p) ↔ i ≤ n := by
  constructor
  · intro h
    rcases (ipCon_rel i p hp n (n + p)).mp h with hEq | ⟨hn, _, _⟩
    · exact absurd hEq (Nat.ne_of_lt (Nat.lt_add_of_pos_right hp))
    · exact hn
  · exact ipCon_add_period i p hp

/-- Distinct index-period pairs give distinct congruences. -/
theorem ipCon_inj {i p i' p' : ℕ} (hp : 0 < p) (hp' : 0 < p')
    (h : ipCon i p hp = ipCon i' p' hp') : i = i' ∧ p = p' := by
  have hrel : ∀ x y, ipCon i p hp x y ↔ ipCon i' p' hp' x y := by
    intro x y; rw [h]
  have hp'_dvd_p : p' ∣ p := by
    have hrel' : ipCon i' p' hp' i (i + p) :=
      (hrel i (i + p)).mp (ipCon_add_period i p hp le_rfl)
    have hm : i % p' = (i + p) % p' := by
      rcases (ipCon_rel i' p' hp' i (i + p)).mp hrel' with hEq | ⟨_, _, hm⟩
      · exact absurd hEq (Nat.ne_of_lt (Nat.lt_add_of_pos_right hp))
      · exact hm
    have : p % p' = 0 :=
      add_mod_eq_left_of_lt hp' (Nat.mod_lt p hp') (by
        simpa [Nat.add_mod, Nat.mod_mod] using hm.symm)
    exact Nat.dvd_iff_mod_eq_zero.mpr this
  have hp_dvd_p' : p ∣ p' := by
    have hrel' : ipCon i p hp i' (i' + p') :=
      (hrel i' (i' + p')).mpr (ipCon_add_period i' p' hp' le_rfl)
    have hm : i' % p = (i' + p') % p := by
      rcases (ipCon_rel i p hp i' (i' + p')).mp hrel' with hEq | ⟨_, _, hm⟩
      · exact absurd hEq (Nat.ne_of_lt (Nat.lt_add_of_pos_right hp'))
      · exact hm
    have : p' % p = 0 :=
      add_mod_eq_left_of_lt hp (Nat.mod_lt p' hp) (by
        simpa [Nat.add_mod, Nat.mod_mod] using hm.symm)
    exact Nat.dvd_iff_mod_eq_zero.mpr this
  have hpp : p = p' := Nat.dvd_antisymm hp_dvd_p' hp'_dvd_p
  subst hpp
  have h₁ : i ≤ i' :=
    (ipCon_add_period_iff i p hp i').mp
      ((hrel i' (i' + p)).mpr (ipCon_add_period i' p hp' le_rfl))
  have h₂ : i' ≤ i :=
    (ipCon_add_period_iff i' p hp' i).mp
      ((hrel i (i + p)).mp (ipCon_add_period i p hp le_rfl))
  exact ⟨le_antisymm h₁ h₂, rfl⟩

/-! ## Pullback to the δ-orbit -/

/-- Index-period congruence pulled back along `toNat`. -/
def orbitIpCon (i p : ℕ) (hp : 0 < p) : AddCon DistinctionNat where
  r x y := ipCon i p hp (toNat x) (toNat y)
  iseqv := {
    refl := fun x => (ipCon i p hp).refl (toNat x)
    symm := fun h => (ipCon i p hp).symm h
    trans := fun h₁ h₂ => (ipCon i p hp).trans h₁ h₂
  }
  add' := by
    intro w x y z hwx hyz
    change ipCon i p hp (toNat (w + y)) (toNat (x + z))
    rw [toNat_add, toNat_add]
    exact (ipCon i p hp).add hwx hyz

theorem orbitIpCon_rel (i p : ℕ) (hp : 0 < p) (x y : DistinctionNat) :
    orbitIpCon i p hp x y ↔ ipCon i p hp (toNat x) (toNat y) :=
  Iff.rfl

/-- The recognition quotient of index `i` and period `p`. -/
abbrev Mip (i p : ℕ) (hp : 0 < p) := (orbitIpCon i p hp).Quotient

/-! ## Transport of congruences along `ofNat` / `toNat` -/

/-- Push an orbit congruence to `ℕ` along `ofNat`. -/
def pushCon (c : AddCon DistinctionNat) : AddCon ℕ where
  r x y := c (ofNat x) (ofNat y)
  iseqv := {
    refl := fun x => c.refl (ofNat x)
    symm := fun h => c.symm h
    trans := fun h₁ h₂ => c.trans h₁ h₂
  }
  add' := by
    intro w x y z hwx hyz
    change c (ofNat (w + y)) (ofNat (x + z))
    rw [ofNat_add, ofNat_add]
    exact c.add hwx hyz

theorem pushCon_orbitIpCon (i p : ℕ) (hp : 0 < p) :
    pushCon (orbitIpCon i p hp) = ipCon i p hp := by
  ext x y
  simp [pushCon, orbitIpCon, toNat_ofNat]

theorem orbitIpCon_of_push (c : AddCon DistinctionNat) {i p : ℕ} {hp : 0 < p}
    (h : pushCon c = ipCon i p hp) : c = orbitIpCon i p hp := by
  ext x y
  calc
    c x y ↔ c (ofNat (toNat x)) (ofNat (toNat y)) := by simp [ofNat_toNat]
    _ ↔ pushCon c (toNat x) (toNat y) := Iff.rfl
    _ ↔ ipCon i p hp (toNat x) (toNat y) := by rw [h]
    _ ↔ orbitIpCon i p hp x y := Iff.rfl

theorem pushCon_inj_iff (c : AddCon DistinctionNat) :
    (∀ x y : ℕ, pushCon c x y → x = y) ↔
      (∀ x y : DistinctionNat, c x y → x = y) := by
  constructor
  · intro h x y hc
    apply toNat_inj
    exact h _ _ (by
      change c (ofNat (toNat x)) (ofNat (toNat y))
      simpa [ofNat_toNat] using hc)
  · intro h x y hc
    have := h _ _ hc
    simpa [toNat_ofNat] using congrArg toNat this

/-! ## Classification helpers on ℕ -/

namespace NatConHelpers

theorem rel_add_right (c : AddCon ℕ) {x y : ℕ} (h : c x y) (t : ℕ) : c (x + t) (y + t) :=
  c.add h (c.refl t)

theorem rel_nsmul (c : AddCon ℕ) {n d : ℕ} (hd : c n (n + d)) (k : ℕ) :
    c n (n + k * d) := by
  induction k with
  | zero => simpa using c.refl n
  | succ k ih =>
      have h1 : c (n + k * d) (n + d + k * d) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          c.add hd (c.refl (k * d))
      have : n + d + k * d = n + (k + 1) * d := by
        rw [Nat.add_assoc, Nat.add_comm d (k * d), Nat.succ_mul]
      rw [← this]
      exact c.trans ih h1

theorem period_at (c : AddCon ℕ) {i p : ℕ} (hA : c i (i + p)) {n : ℕ} (hn : i ≤ n) :
    c n (n + p) := by
  have h := rel_add_right c hA (n - i)
  have hni : i + (n - i) = n := Nat.add_sub_of_le hn
  have hnip : i + p + (n - i) = n + p := by
    omega
  simpa [hni, hnip] using h

theorem period_mul (c : AddCon ℕ) {i p : ℕ} (hA : c i (i + p))
    {n : ℕ} (hn : i ≤ n) (k : ℕ) : c n (n + k * p) := by
  induction k with
  | zero => simpa using c.refl n
  | succ k ih =>
      have h1 : c (n + k * p) (n + k * p + p) := period_at c hA (by omega)
      have : n + k * p + p = n + (k + 1) * p := by
        rw [Nat.succ_mul, Nat.add_assoc]
      rw [← this]
      exact c.trans ih h1

/-- Lemma B: past the index, equal residues imply related. -/
theorem lemma_B (c : AddCon ℕ) {i p : ℕ} (hp : 0 < p) (hA : c i (i + p))
    {x y : ℕ} (hx : i ≤ x) (hy : i ≤ y) (hm : x % p = y % p) : c x y := by
  wlog hle : x ≤ y generalizing x y
  · exact c.symm (this hy hx hm.symm (le_of_not_ge hle))
  obtain ⟨k, hk⟩ := dvd_sub_of_mod_eq hp hle hm
  -- hk : y - x = p * k
  have hyx : y = x + k * p := by
    have : y = x + (y - x) := (Nat.add_sub_of_le hle).symm
    rw [this, hk, Nat.mul_comm]
  rw [hyx]
  exact period_mul c hA hx k

/-- Lemma A: the least index is related to itself plus the least period. -/
theorem lemma_A (c : AddCon ℕ) {i p d₁ n : ℕ}
    (hd₁ : 0 < d₁) (h_i : c i (i + d₁))
    (hp : 0 < p) (hn : c n (n + p)) (hle : i ≤ n) :
    c i (i + p) := by
  let k := (n - i) / d₁ + 1
  have hk : n ≤ i + k * d₁ := by
    have hdiv : n - i < d₁ * ((n - i) / d₁ + 1) := Nat.lt_mul_div_succ (n - i) hd₁
    have : n - i < k * d₁ := by
      simpa [k, Nat.mul_comm] using hdiv
    omega
  let m := i + k * d₁
  have him : c i m := by
    simpa [m] using rel_nsmul c h_i k
  have hmp : c m (m + p) := by
    have h := rel_add_right c hn (m - n)
    have hmn : n + (m - n) = m := Nat.add_sub_of_le hk
    have hmnp : n + p + (m - n) = m + p := by omega
    simpa [hmn, hmnp] using h
  have h1 : c i (m + p) := c.trans him hmp
  have h2 : c (i + p) (m + p) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      c.add him (c.refl p)
  exact c.trans h1 (c.symm h2)

end NatConHelpers

/-! ## Catalogue theorems (classical) -/

open Classical
open NatConHelpers

/-- Classification of additive congruences on `ℕ`. -/
theorem nat_congruence_catalogue (c : AddCon ℕ) :
    (∀ x y, c x y → x = y) ∨ ∃ i p, ∃ hp : 0 < p, c = ipCon i p hp := by
  by_cases hEq : ∀ x y, c x y → x = y
  · exact Or.inl hEq
  · right
    push_neg at hEq
    obtain ⟨a, b, hab, hne⟩ := hEq
    wlog hlt : a < b generalizing a b
    · exact this b a (c.symm hab) (Ne.symm hne) (lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne))
    let I : ℕ → Prop := fun n => ∃ m, n < m ∧ c n m
    have haI : I a := ⟨b, hlt, hab⟩
    let i : ℕ := Nat.find (⟨a, haI⟩ : ∃ n, I n)
    have hiI : I i := Nat.find_spec (⟨a, haI⟩ : ∃ n, I n)
    have hi_min : ∀ n, I n → i ≤ n := fun n hn => Nat.find_min' (⟨a, haI⟩ : ∃ n, I n) hn
    obtain ⟨m₀, him₀, hc_im₀⟩ := hiI
    let d₁ : ℕ := m₀ - i
    have hd₁ : 0 < d₁ := Nat.sub_pos_of_lt him₀
    have h_id₁ : c i (i + d₁) := by
      have : i + d₁ = m₀ := Nat.add_sub_of_le (Nat.le_of_lt him₀)
      simpa [this] using hc_im₀
    let D : ℕ → Prop := fun d => 0 < d ∧ ∃ n, c n (n + d)
    have hD : D (b - a) := ⟨Nat.sub_pos_of_lt hlt, a, by
      have : a + (b - a) = b := Nat.add_sub_of_le (Nat.le_of_lt hlt)
      simpa [this] using hab⟩
    let p : ℕ := Nat.find (⟨b - a, hD⟩ : ∃ d, D d)
    have hpD : D p := Nat.find_spec (⟨b - a, hD⟩ : ∃ d, D d)
    have hp : 0 < p := hpD.1
    have hp_min : ∀ d, D d → p ≤ d := fun d hd =>
      Nat.find_min' (⟨b - a, hD⟩ : ∃ d, D d) hd
    obtain ⟨n, hn_rel⟩ := hpD.2
    have hnI : I n := ⟨n + p, Nat.lt_add_of_pos_right hp, hn_rel⟩
    have hle_in : i ≤ n := hi_min n hnI
    have hA : c i (i + p) := lemma_A c hd₁ h_id₁ hp hn_rel hle_in
    have hmin_period : ∀ d, 0 < d → (∃ t, c t (t + d)) → p ≤ d := by
      intro d hd ⟨t, ht⟩
      exact hp_min d ⟨hd, t, ht⟩
    -- Assemble equality of relations
    refine ⟨i, p, hp, ?_⟩
    ext x y
    constructor
    · intro hxy
      -- lemma C
      by_cases heq : x = y
      · exact Or.inl heq
      · right
        wlog hxy_lt : x < y generalizing x y
        · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hxy_lt) (Ne.symm heq)
          have ih := this y x (c.symm hxy) (Ne.symm heq) hyx
          exact ⟨ih.2.1, ih.1, ih.2.2.symm⟩
        have hxI : I x := ⟨y, hxy_lt, hxy⟩
        have hx : i ≤ x := hi_min x hxI
        have hy : i ≤ y := le_trans hx (Nat.le_of_lt hxy_lt)
        let d := y - x
        have hd : 0 < d := Nat.sub_pos_of_lt hxy_lt
        have hdD : D d := ⟨hd, x, by
          have : x + d = y := Nat.add_sub_of_le (Nat.le_of_lt hxy_lt)
          simpa [this] using hxy⟩
        have hpd : p ≤ d := hp_min d hdD
        -- Show p ∣ d
        let r := d % p
        by_cases hr0 : r = 0
        · have : x % p = y % p := by
            have hyx : y = x + d := (Nat.add_sub_of_le (Nat.le_of_lt hxy_lt)).symm
            have hdr : d % p = 0 := hr0
            rw [hyx, Nat.add_mod, hdr, Nat.add_zero, Nat.mod_mod]
          exact ⟨hx, hy, this⟩
        · exfalso
          have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
          have hrlt : r < p := Nat.mod_lt d hp
          have hpr : 0 < p - r := Nat.sub_pos_of_lt hrlt
          have hsum : d + (p - r) = p * (d / p + 1) := by
            let q := d / p
            have hmod : p * q + d % p = d := Nat.div_add_mod d p
            have hrdef : r = d % p := rfl
            have h1 : d + (p - r) = p * q + d % p + (p - r) :=
              congrArg (fun t => t + (p - r)) hmod.symm
            have h2 : p * q + d % p + (p - r) = p * q + r + (p - r) := by
              rw [hrdef]
            have h3 : p * q + r + (p - r) = p * q + (r + (p - r)) := by
              rw [Nat.add_assoc]
            have h4 : p * q + (r + (p - r)) = p * q + p := by
              rw [Nat.add_sub_of_le (Nat.le_of_lt hrlt)]
            have h5 : p * q + p = p * (q + 1) := by
              rw [Nat.mul_add, Nat.mul_one]
            exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
          have hdiv : p ∣ d + (p - r) := ⟨d / p + 1, hsum⟩
          have hx2 : i ≤ x + d + (p - r) := by omega
          have hm2 : x % p = (x + d + (p - r)) % p := by
            have : (d + (p - r)) % p = 0 := by
              rw [hsum, Nat.mul_mod_right]
            simp [Nat.add_assoc, Nat.add_mod, this]
          have hB : c x (x + d + (p - r)) :=
            lemma_B c hp hA hx hx2 hm2
          have hxd : c x (x + d) := by
            have : x + d = y := Nat.add_sub_of_le (Nat.le_of_lt hxy_lt)
            simpa [this] using hxy
          have hstep : c (x + d) (x + d + (p - r)) :=
            c.trans (c.symm hxd) hB
          have hDpr : D (p - r) := ⟨hpr, x + d, hstep⟩
          have : p ≤ p - r := hp_min (p - r) hDpr
          omega
    · intro h
      rcases h with rfl | ⟨hx, hy, hm⟩
      · exact c.refl x
      · exact lemma_B c hp hA hx hy hm

/-- The congruences on `(DistinctionNat, +, 0)` are equality and the orbit index-period family. -/
theorem orbit_congruence_catalogue (c : AddCon DistinctionNat) :
    (∀ x y, c x y → x = y) ∨ ∃ i p, ∃ hp : 0 < p, c = orbitIpCon i p hp := by
  rcases nat_congruence_catalogue (pushCon c) with h | ⟨i, p, hp, hpush⟩
  · exact Or.inl ((pushCon_inj_iff c).mp h)
  · exact Or.inr ⟨i, p, hp, orbitIpCon_of_push c hpush⟩

/-- The index-period pair in the non-trivial branch is unique. -/
theorem orbit_congruence_catalogue_unique (c : AddCon DistinctionNat)
    {i p i' p' : ℕ} (hp : 0 < p) (hp' : 0 < p')
    (h : c = orbitIpCon i p hp) (h' : c = orbitIpCon i' p' hp') :
    i = i' ∧ p = p' := by
  have : ipCon i p hp = ipCon i' p' hp' := by
    rw [← pushCon_orbitIpCon i p hp, ← pushCon_orbitIpCon i' p' hp', ← h, ← h']
  exact ipCon_inj hp hp' this

/-- A recognizer is injective, or its kernel is an index-period congruence. -/
theorem recognizer_dichotomy {V : Type*} [AddCommMonoid V] (r : DistinctionNat →+ V) :
    Function.Injective r ∨
      ∃ i p, ∃ hp : 0 < p, AddCon.ker r = orbitIpCon i p hp := by
  rcases orbit_congruence_catalogue (AddCon.ker r) with h | ⟨i, p, hp, hk⟩
  · left
    intro x y hxy
    exact h x y ((AddCon.ker_rel r).mpr hxy)
  · exact Or.inr ⟨i, p, hp, hk⟩

/-- First isomorphism corollary: kernel equal to `orbitIpCon` yields the recognition quotient. -/
noncomputable def recognizer_quotient_equiv {V : Type*} [AddCommMonoid V]
    (r : DistinctionNat →+ V) {i p : ℕ} {hp : 0 < p}
    (h : AddCon.ker r = orbitIpCon i p hp) :
    (AddCon.ker r).Quotient ≃+ Mip i p hp :=
  AddCon.congr h

/-- First isomorphism theorem: quotient by the kernel is the range. -/
noncomputable def recognizer_range_equiv {V : Type*} [AddCommMonoid V]
    (r : DistinctionNat →+ V) :
    (AddCon.ker r).Quotient ≃+ AddMonoidHom.mrange r :=
  AddCon.quotientKerEquivRange r

/-- Combined first-isomorphism form matching Paper 1: quotient ≅ M(i,p) ≅ im(r). -/
noncomputable def recognizer_first_iso {V : Type*} [AddCommMonoid V]
    (r : DistinctionNat →+ V) {i p : ℕ} {hp : 0 < p}
    (h : AddCon.ker r = orbitIpCon i p hp) :
    Mip i p hp ≃+ AddMonoidHom.mrange r :=
  (recognizer_quotient_equiv r h).symm.trans (recognizer_range_equiv r)

end ActualMathematics

#print axioms ActualMathematics.orbit_congruence_catalogue
#print axioms ActualMathematics.recognizer_dichotomy
#print axioms ActualMathematics.ipCon_inj

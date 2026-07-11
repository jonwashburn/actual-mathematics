import ActualMathematics.DeltaKernel.BootstrapTowerExport

/-!
# Bootstrap strengthening: source-sensitive δ tower generation

The old prototype fixed `NatDelta`, `IntDelta`, and `RatDelta` in the result
types of its step constructors. Its predecessor arguments could therefore be
erased without changing the admitted carriers. This replacement makes each
step compute a literal quotient from the predecessor bundle's own operations:

* `signedCompletion B` is the balanced-pair quotient formed with `B.add`;
* `fractionCompletion R` is the positive-denominator cross-product quotient
  formed with `R.mul` and `R.ofDen`.

The legal grammar has three stages. Signed completion consumes an orbit bundle,
and fraction completion consumes the resulting signed bundle. Repeating either
completion is not a legal term. The normal-form theorem is therefore the exact
three-stage theorem, proved by induction and the two quotient functoriality
maps. No absorption theorem is needed for this grammar.

Concrete membership is terminal. `IntDelta` and `RatDelta` are reached through
proved equivalences from the computed quotients. In particular,
`fractionIntEquivRat` is the Gate 0 equivalence. It never uses `PRCRat.toRat`
or representative choice.

Bare equivalence forgets construction history. The module publishes the exact
lower bound `towerGen_of_natDelta_equiv` and the witness `towerGen_evenNat`.
It does not claim a converse. Exclusivity lives in inspectable `CoreTower`
receipts and `core_normalForm`.

CLAIM: CLOSED positive for the stage-typed source-sensitive receipt calculus.
DOMAIN: the balanced-pair and positive-denominator cross-product quotients.
PREMISES:
  A1. The free source is the bundled `NatDelta` orbit.
  A2. Signed and fraction relations use predecessor operations literally.
  A3. Terminal carrier equivalence is intentionally structure-forgetting.
REACH:
  * computed quotient receipts generate NatDelta, IntDelta, and RatDelta;
  * every receipt yields DeltaForced and an explicit embedding of ℕ;
  * every core receipt has the exact stage normal form;
  * Fin 17 is excluded by the ℕ-embedding invariant alone;
  * ℝ is excluded in the isolated classical boundary.
does NOT license:
  * any initiality or completion characterization not stated and proved here;
  * extensional exclusivity among types equivalent to ℕ;
  * a biconditional between TowerGen and bare denumerability;
  * any change to PhysicallyReal.
-/

namespace ActualMathematics.DeltaKernel.Bootstrap

open ActualMathematics
open ActualMathematics.Forced

/-! ## Choice-free representation and quotient helpers -/

def representationEquiv {X Y : Type}
    (r : Representation X) (e : X ≃ Y) : Representation Y where
  decode n := (r.decode n).map e
  complete y := by
    obtain ⟨n, hn⟩ := r.complete (e.symm y)
    refine ⟨n, ?_⟩
    rw [hn]
    simp

def representationQuot {X : Type}
    (r : Representation X) (s : Setoid X) : Representation (Quot s) where
  decode n := (r.decode n).map (Quot.mk s)
  complete q := by
    refine Quot.induction_on q (fun x => ?_)
    obtain ⟨n, hn⟩ := r.complete x
    refine ⟨n, ?_⟩
    rw [hn]
    rfl

def quotDecidableEq {X : Type} (s : Setoid X) [DecidableRel s.r] :
    DecidableEq (Quot s) :=
  @Quotient.decidableEq X s inferInstance

def quotEquivOfEquiv {X Y : Type}
    (s : Setoid X) (t : Setoid Y) (e : X ≃ Y)
    (hrel : ∀ a b, s.r a b ↔ t.r (e a) (e b)) :
    Quot s ≃ Quot t where
  toFun :=
    Quot.lift (fun a => Quot.mk t (e a))
      (fun a b h => Quot.sound ((hrel a b).mp h))
  invFun :=
    Quot.lift (fun b => Quot.mk s (e.symm b))
      (fun a b h => Quot.sound ((hrel (e.symm a) (e.symm b)).mpr (by
        simpa using h)))
  left_inv q := by
    refine Quot.induction_on q (fun a => ?_)
    simp
  right_inv q := by
    refine Quot.induction_on q (fun b => ?_)
    simp

/-! ## Orbit bundles -/

/-- Data and checked arithmetic laws consumed by the signed-completion move.
The finite-code representation and decidable equality are operational data,
not generation assumptions. -/
structure OrbitBundle where
  Carrier : Type
  zero : Carrier
  one : Carrier
  add : Carrier → Carrier → Carrier
  mul : Carrier → Carrier → Carrier
  decEq : DecidableEq Carrier
  repr : Representation Carrier
  toNat : Carrier ↪ ℕ
  toNat_zero : toNat zero = 0
  toNat_one : toNat one = 1
  toNat_add : ∀ a b, toNat (add a b) = toNat a + toNat b
  toNat_mul : ∀ a b, toNat (mul a b) = toNat a * toNat b
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  zero_add : ∀ a, add zero a = a
  add_zero : ∀ a, add a zero = a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  one_mul : ∀ a, mul one a = a
  mul_one : ∀ a, mul a one = a
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  zero_ne_one : zero ≠ one

theorem OrbitBundle.mul_ne_zero (B : OrbitBundle) {a b : B.Carrier}
    (ha : a ≠ B.zero) (hb : b ≠ B.zero) :
    B.mul a b ≠ B.zero := by
  intro h
  have hnat :
      B.toNat (B.mul a b) = B.toNat B.zero :=
    congrArg (fun x => B.toNat x) h
  rw [B.toNat_mul, B.toNat_zero] at hnat
  rcases Nat.mul_eq_zero.mp hnat with hzero | hzero
  · apply ha
    apply B.toNat.injective
    rw [hzero, B.toNat_zero]
  · apply hb
    apply B.toNat.injective
    rw [hzero, B.toNat_zero]

def natDeltaRepresentation : Representation NatDelta where
  decode n := some (DistinctionNat.ofNat n)
  complete x := ⟨x.toNat, by rw [DistinctionNat.ofNat_toNat]⟩

def natDeltaToNatEmbedding : NatDelta ↪ ℕ :=
  ⟨DistinctionNat.toNat, fun _ _ => DistinctionNat.toNat_inj⟩

def natDeltaBundle : OrbitBundle where
  Carrier := NatDelta
  zero := DistinctionNat.zero
  one := DistinctionNat.succ DistinctionNat.zero
  add := (· + ·)
  mul := (· * ·)
  decEq := inferInstance
  repr := natDeltaRepresentation
  toNat := natDeltaToNatEmbedding
  toNat_zero := rfl
  toNat_one := rfl
  toNat_add := DistinctionNat.toNat_add
  toNat_mul := DistinctionNat.toNat_mul
  add_assoc := DistinctionNat.add_assoc
  add_comm := DistinctionNat.add_comm
  zero_add := DistinctionNat.zero_add_eq
  add_zero := DistinctionNat.add_zero_eq
  mul_assoc := by
    intro a b c
    apply DistinctionNat.toNat_inj
    rw [DistinctionNat.toNat_mul, DistinctionNat.toNat_mul,
      DistinctionNat.toNat_mul, DistinctionNat.toNat_mul]
    exact Nat.mul_assoc _ _ _
  mul_comm := DistinctionNat.mul_comm
  one_mul := by
    intro a
    apply DistinctionNat.toNat_inj
    rw [DistinctionNat.toNat_mul]
    change 1 * a.toNat = a.toNat
    exact Nat.one_mul _
  mul_one := by
    intro a
    apply DistinctionNat.toNat_inj
    rw [DistinctionNat.toNat_mul]
    exact Nat.mul_one _
  left_distrib := by
    intro a b c
    apply DistinctionNat.toNat_inj
    rw [DistinctionNat.toNat_mul, DistinctionNat.toNat_add,
      DistinctionNat.toNat_add, DistinctionNat.toNat_mul,
      DistinctionNat.toNat_mul]
    exact Nat.mul_add _ _ _
  zero_ne_one := DistinctionNat.zero_ne_succ DistinctionNat.zero

structure OrbitBundleIso (A B : OrbitBundle) where
  carrierEquiv : A.Carrier ≃ B.Carrier
  map_zero : carrierEquiv A.zero = B.zero
  map_one : carrierEquiv A.one = B.one
  map_add : ∀ a b, carrierEquiv (A.add a b) =
    B.add (carrierEquiv a) (carrierEquiv b)
  map_mul : ∀ a b, carrierEquiv (A.mul a b) =
    B.mul (carrierEquiv a) (carrierEquiv b)

def OrbitBundleIso.refl (A : OrbitBundle) : OrbitBundleIso A A where
  carrierEquiv := Equiv.refl _
  map_zero := rfl
  map_one := rfl
  map_add := fun _ _ => rfl
  map_mul := fun _ _ => rfl

/-! ## Literal signed completion -/

structure SignedRep (B : OrbitBundle) where
  pos : B.Carrier
  neg : B.Carrier

def signedValue (B : OrbitBundle) (z : SignedRep B) : ℤ :=
  (B.toNat z.pos : ℤ) - (B.toNat z.neg : ℤ)

def signedRel (B : OrbitBundle) (a b : SignedRep B) : Prop :=
  B.add a.pos b.neg = B.add b.pos a.neg

theorem signedRel_iff_value_eq (B : OrbitBundle) (a b : SignedRep B) :
    signedRel B a b ↔ signedValue B a = signedValue B b := by
  constructor
  · intro h
    have hnat :
        B.toNat (B.add a.pos b.neg) =
          B.toNat (B.add b.pos a.neg) :=
      congrArg (fun x => B.toNat x) h
    rw [B.toNat_add, B.toNat_add] at hnat
    have hnatZ :
        (B.toNat a.pos : ℤ) + B.toNat b.neg =
          B.toNat b.pos + B.toNat a.neg := by
      exact_mod_cast hnat
    unfold signedValue
    omega
  · intro h
    apply B.toNat.injective
    rw [B.toNat_add, B.toNat_add]
    unfold signedValue at h
    omega

def signedSetoid (B : OrbitBundle) : Setoid (SignedRep B) where
  r := signedRel B
  iseqv := {
    refl := fun a => (signedRel_iff_value_eq B a a).mpr rfl
    symm := fun h => (signedRel_iff_value_eq B _ _).mpr
      ((signedRel_iff_value_eq B _ _).mp h).symm
    trans := fun h₁ h₂ => (signedRel_iff_value_eq B _ _).mpr
      (((signedRel_iff_value_eq B _ _).mp h₁).trans
        ((signedRel_iff_value_eq B _ _).mp h₂))
  }

def SignedCarrier (B : OrbitBundle) : Type :=
  Quot (signedSetoid B)

def signedZeroRep (B : OrbitBundle) : SignedRep B := ⟨B.zero, B.zero⟩
def signedOneRep (B : OrbitBundle) : SignedRep B := ⟨B.one, B.zero⟩
def signedNegRep (B : OrbitBundle) (a : SignedRep B) : SignedRep B :=
  ⟨a.neg, a.pos⟩
def signedAddRep (B : OrbitBundle) (a b : SignedRep B) : SignedRep B :=
  ⟨B.add a.pos b.pos, B.add a.neg b.neg⟩
def signedMulRep (B : OrbitBundle) (a b : SignedRep B) : SignedRep B :=
  ⟨B.add (B.mul a.pos b.pos) (B.mul a.neg b.neg),
   B.add (B.mul a.pos b.neg) (B.mul a.neg b.pos)⟩

theorem signedValue_zero (B : OrbitBundle) :
    signedValue B (signedZeroRep B) = 0 := by
  simp [signedValue, signedZeroRep, B.toNat_zero]

theorem signedValue_one (B : OrbitBundle) :
    signedValue B (signedOneRep B) = 1 := by
  simp [signedValue, signedOneRep, B.toNat_zero, B.toNat_one]

theorem signedValue_neg (B : OrbitBundle) (a : SignedRep B) :
    signedValue B (signedNegRep B a) = -signedValue B a := by
  simp [signedValue, signedNegRep]

theorem signedValue_add (B : OrbitBundle) (a b : SignedRep B) :
    signedValue B (signedAddRep B a b) =
      signedValue B a + signedValue B b := by
  simp [signedValue, signedAddRep, B.toNat_add]
  ring

theorem signedValue_mul (B : OrbitBundle) (a b : SignedRep B) :
    signedValue B (signedMulRep B a b) =
      signedValue B a * signedValue B b := by
  simp [signedValue, signedMulRep, B.toNat_add, B.toNat_mul]
  ring

def signedZero (B : OrbitBundle) : SignedCarrier B :=
  Quot.mk (signedSetoid B) (signedZeroRep B)

def signedOne (B : OrbitBundle) : SignedCarrier B :=
  Quot.mk (signedSetoid B) (signedOneRep B)

def signedNeg (B : OrbitBundle) : SignedCarrier B → SignedCarrier B :=
  Quot.lift (fun a => Quot.mk (signedSetoid B) (signedNegRep B a)) (by
    intro a b h
    apply Quot.sound
    change signedRel B (signedNegRep B a) (signedNegRep B b)
    change signedRel B a b at h
    rw [signedRel_iff_value_eq, signedValue_neg, signedValue_neg]
    exact congrArg Neg.neg ((signedRel_iff_value_eq B a b).mp h))

def signedAdd (B : OrbitBundle) : SignedCarrier B → SignedCarrier B →
    SignedCarrier B :=
  Quot.lift₂
    (fun a b => Quot.mk (signedSetoid B) (signedAddRep B a b))
    (by
      intro a b₁ b₂ h
      apply Quot.sound
      change signedRel B (signedAddRep B a b₁) (signedAddRep B a b₂)
      change signedRel B b₁ b₂ at h
      rw [signedRel_iff_value_eq, signedValue_add, signedValue_add]
      exact congrArg (signedValue B a + ·)
        ((signedRel_iff_value_eq B b₁ b₂).mp h))
    (by
      intro a₁ a₂ b h
      apply Quot.sound
      change signedRel B (signedAddRep B a₁ b) (signedAddRep B a₂ b)
      change signedRel B a₁ a₂ at h
      rw [signedRel_iff_value_eq, signedValue_add, signedValue_add]
      exact congrArg (· + signedValue B b)
        ((signedRel_iff_value_eq B a₁ a₂).mp h))

def signedMul (B : OrbitBundle) : SignedCarrier B → SignedCarrier B →
    SignedCarrier B :=
  Quot.lift₂
    (fun a b => Quot.mk (signedSetoid B) (signedMulRep B a b))
    (by
      intro a b₁ b₂ h
      apply Quot.sound
      change signedRel B (signedMulRep B a b₁) (signedMulRep B a b₂)
      change signedRel B b₁ b₂ at h
      rw [signedRel_iff_value_eq, signedValue_mul, signedValue_mul]
      exact congrArg (signedValue B a * ·)
        ((signedRel_iff_value_eq B b₁ b₂).mp h))
    (by
      intro a₁ a₂ b h
      apply Quot.sound
      change signedRel B (signedMulRep B a₁ b) (signedMulRep B a₂ b)
      change signedRel B a₁ a₂ at h
      rw [signedRel_iff_value_eq, signedValue_mul, signedValue_mul]
      exact congrArg (· * signedValue B b)
        ((signedRel_iff_value_eq B a₁ a₂).mp h))

def signedToInt (B : OrbitBundle) : SignedCarrier B → ℤ :=
  Quot.lift (signedValue B)
    (fun a b h => (signedRel_iff_value_eq B a b).mp h)

theorem signedToInt_injective (B : OrbitBundle) :
    Function.Injective (signedToInt B) := by
  intro a b h
  induction a using Quot.ind with
  | _ a =>
      induction b using Quot.ind with
      | _ b =>
          apply Quot.sound
          apply (signedRel_iff_value_eq B a b).mpr
          exact h

def signedToIntEmbedding (B : OrbitBundle) : SignedCarrier B ↪ ℤ :=
  ⟨signedToInt B, signedToInt_injective B⟩

@[simp] theorem signedToInt_zero (B : OrbitBundle) :
    signedToInt B (signedZero B) = 0 := signedValue_zero B

@[simp] theorem signedToInt_one (B : OrbitBundle) :
    signedToInt B (signedOne B) = 1 := signedValue_one B

@[simp] theorem signedToInt_neg (B : OrbitBundle) (a : SignedCarrier B) :
    signedToInt B (signedNeg B a) = -signedToInt B a := by
  refine Quot.induction_on a (fun a => ?_)
  exact signedValue_neg B a

@[simp] theorem signedToInt_add (B : OrbitBundle) (a b : SignedCarrier B) :
    signedToInt B (signedAdd B a b) = signedToInt B a + signedToInt B b := by
  refine Quot.induction_on a (fun a => ?_)
  refine Quot.induction_on b (fun b => ?_)
  exact signedValue_add B a b

@[simp] theorem signedToInt_mul (B : OrbitBundle) (a b : SignedCarrier B) :
    signedToInt B (signedMul B a b) = signedToInt B a * signedToInt B b := by
  refine Quot.induction_on a (fun a => ?_)
  refine Quot.induction_on b (fun b => ?_)
  exact signedValue_mul B a b

def signedOfDen (B : OrbitBundle) (a : B.Carrier) : SignedCarrier B :=
  Quot.mk (signedSetoid B) ⟨a, B.zero⟩

@[simp] theorem signedToInt_ofDen (B : OrbitBundle) (a : B.Carrier) :
    signedToInt B (signedOfDen B a) = B.toNat a := by
  simp [signedToInt, signedOfDen, signedValue, B.toNat_zero]

def signedSourceEmbedding (B : OrbitBundle) : B.Carrier ↪ SignedCarrier B where
  toFun := signedOfDen B
  inj' := by
    intro a b h
    apply B.toNat.injective
    have := congrArg (signedToInt B) h
    simpa using this

def signedRepProdEquiv (B : OrbitBundle) :
    (B.Carrier × B.Carrier) ≃ SignedRep B where
  toFun p := ⟨p.1, p.2⟩
  invFun z := (z.pos, z.neg)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def signedRepresentation (B : OrbitBundle) : Representation (SignedCarrier B) :=
  representationQuot
    (representationEquiv (B.repr.prod B.repr) (signedRepProdEquiv B))
    (signedSetoid B)

def signedCarrierDecidableEq (B : OrbitBundle) : DecidableEq (SignedCarrier B) := by
  letI := B.decEq
  letI : DecidableRel (signedSetoid B).r := fun a b => by
    change Decidable (B.add a.pos b.neg = B.add b.pos a.neg)
    exact B.decEq _ _
  exact quotDecidableEq (signedSetoid B)

/-- The signed stage carries the operations and laws that the fraction move
will consume. Every field is computed from the source orbit bundle. -/
structure SignedBundle where
  denom : OrbitBundle
  Carrier : Type
  zero : Carrier
  one : Carrier
  add : Carrier → Carrier → Carrier
  mul : Carrier → Carrier → Carrier
  neg : Carrier → Carrier
  decEq : DecidableEq Carrier
  repr : Representation Carrier
  toInt : Carrier ↪ ℤ
  ofDen : denom.Carrier → Carrier
  toInt_zero : toInt zero = 0
  toInt_one : toInt one = 1
  toInt_add : ∀ a b, toInt (add a b) = toInt a + toInt b
  toInt_mul : ∀ a b, toInt (mul a b) = toInt a * toInt b
  toInt_neg : ∀ a, toInt (neg a) = -toInt a
  toInt_ofDen : ∀ a, toInt (ofDen a) = denom.toNat a
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  add_zero : ∀ a, add a zero = a
  add_neg : ∀ a, add a (neg a) = zero
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  mul_one : ∀ a, mul a one = a
  one_mul : ∀ a, mul one a = a
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  ofDen_one : ofDen denom.one = one
  zero_ne_one : zero ≠ one

theorem signedAdd_assoc_raw (B : OrbitBundle) (a b c : SignedCarrier B) :
    signedAdd B (signedAdd B a b) c =
      signedAdd B a (signedAdd B b c) := by
  apply signedToInt_injective B
  simp [Int.add_assoc]

theorem signedAdd_comm_raw (B : OrbitBundle) (a b : SignedCarrier B) :
    signedAdd B a b = signedAdd B b a := by
  apply signedToInt_injective B
  simp [Int.add_comm]

theorem signedAdd_zero_raw (B : OrbitBundle) (a : SignedCarrier B) :
    signedAdd B a (signedZero B) = a := by
  apply signedToInt_injective B
  simp

theorem signedAdd_neg_raw (B : OrbitBundle) (a : SignedCarrier B) :
    signedAdd B a (signedNeg B a) = signedZero B := by
  apply signedToInt_injective B
  simp

theorem signedMul_assoc_raw (B : OrbitBundle) (a b c : SignedCarrier B) :
    signedMul B (signedMul B a b) c =
      signedMul B a (signedMul B b c) := by
  apply signedToInt_injective B
  simp [Int.mul_assoc]

theorem signedMul_comm_raw (B : OrbitBundle) (a b : SignedCarrier B) :
    signedMul B a b = signedMul B b a := by
  apply signedToInt_injective B
  simp [Int.mul_comm]

theorem signedMul_one_raw (B : OrbitBundle) (a : SignedCarrier B) :
    signedMul B a (signedOne B) = a := by
  apply signedToInt_injective B
  simp

theorem signedOne_mul_raw (B : OrbitBundle) (a : SignedCarrier B) :
    signedMul B (signedOne B) a = a := by
  apply signedToInt_injective B
  simp

theorem signedLeft_distrib_raw (B : OrbitBundle)
    (a b c : SignedCarrier B) :
    signedMul B a (signedAdd B b c) =
      signedAdd B (signedMul B a b) (signedMul B a c) := by
  apply signedToInt_injective B
  simp [Int.mul_add]

theorem signedOfDen_one_raw (B : OrbitBundle) :
    signedOfDen B B.one = signedOne B := by
  apply signedToInt_injective B
  simp [B.toNat_one]

theorem signedZero_ne_one_raw (B : OrbitBundle) :
    signedZero B ≠ signedOne B := by
  intro h
  have h' := congrArg (signedToInt B) h
  rw [signedToInt_zero, signedToInt_one] at h'
  exact Int.zero_ne_one h'

def signedCompletion (B : OrbitBundle) : SignedBundle where
  denom := B
  Carrier := SignedCarrier B
  zero := signedZero B
  one := signedOne B
  add := signedAdd B
  mul := signedMul B
  neg := signedNeg B
  decEq := signedCarrierDecidableEq B
  repr := signedRepresentation B
  toInt := signedToIntEmbedding B
  ofDen := signedOfDen B
  toInt_zero := signedToInt_zero B
  toInt_one := signedToInt_one B
  toInt_add := signedToInt_add B
  toInt_mul := signedToInt_mul B
  toInt_neg := signedToInt_neg B
  toInt_ofDen := signedToInt_ofDen B
  add_assoc := signedAdd_assoc_raw B
  add_comm := signedAdd_comm_raw B
  add_zero := signedAdd_zero_raw B
  add_neg := signedAdd_neg_raw B
  mul_assoc := signedMul_assoc_raw B
  mul_comm := signedMul_comm_raw B
  mul_one := signedMul_one_raw B
  one_mul := signedOne_mul_raw B
  left_distrib := signedLeft_distrib_raw B
  ofDen_one := signedOfDen_one_raw B
  zero_ne_one := signedZero_ne_one_raw B

structure SignedBundleIso (A B : SignedBundle) where
  denomIso : OrbitBundleIso A.denom B.denom
  carrierEquiv : A.Carrier ≃ B.Carrier
  map_zero : carrierEquiv A.zero = B.zero
  map_one : carrierEquiv A.one = B.one
  map_add : ∀ a b, carrierEquiv (A.add a b) =
    B.add (carrierEquiv a) (carrierEquiv b)
  map_mul : ∀ a b, carrierEquiv (A.mul a b) =
    B.mul (carrierEquiv a) (carrierEquiv b)
  map_neg : ∀ a, carrierEquiv (A.neg a) = B.neg (carrierEquiv a)
  map_ofDen : ∀ a, carrierEquiv (A.ofDen a) =
    B.ofDen (denomIso.carrierEquiv a)

def SignedBundleIso.refl (A : SignedBundle) : SignedBundleIso A A where
  denomIso := OrbitBundleIso.refl A.denom
  carrierEquiv := Equiv.refl _
  map_zero := rfl
  map_one := rfl
  map_add := fun _ _ => rfl
  map_mul := fun _ _ => rfl
  map_neg := fun _ => rfl
  map_ofDen := fun _ => rfl

def signedRepMap {A B : OrbitBundle} (e : OrbitBundleIso A B) :
    SignedRep A ≃ SignedRep B where
  toFun z := ⟨e.carrierEquiv z.pos, e.carrierEquiv z.neg⟩
  invFun z := ⟨e.carrierEquiv.symm z.pos, e.carrierEquiv.symm z.neg⟩
  left_inv z := by cases z; simp
  right_inv z := by cases z; simp

theorem signedRepMap_rel {A B : OrbitBundle} (e : OrbitBundleIso A B)
    (a b : SignedRep A) :
    signedRel A a b ↔ signedRel B (signedRepMap e a) (signedRepMap e b) := by
  change
    A.add a.pos b.neg = A.add b.pos a.neg ↔
      B.add (e.carrierEquiv a.pos) (e.carrierEquiv b.neg) =
        B.add (e.carrierEquiv b.pos) (e.carrierEquiv a.neg)
  constructor
  · intro h
    rw [← e.map_add, ← e.map_add, h]
  · intro h
    apply e.carrierEquiv.injective
    simpa [e.map_add] using h

def signedCarrierMap {A B : OrbitBundle} (e : OrbitBundleIso A B) :
    SignedCarrier A ≃ SignedCarrier B :=
  quotEquivOfEquiv (signedSetoid A) (signedSetoid B) (signedRepMap e)
    (signedRepMap_rel e)

def signedMapIso {A B : OrbitBundle} (e : OrbitBundleIso A B) :
    SignedBundleIso (signedCompletion A) (signedCompletion B) where
  denomIso := e
  carrierEquiv := signedCarrierMap e
  map_zero := by
    change Quot.mk _ (signedRepMap e (signedZeroRep A)) =
      Quot.mk _ (signedZeroRep B)
    apply congrArg (Quot.mk (signedSetoid B))
    change (⟨e.carrierEquiv A.zero, e.carrierEquiv A.zero⟩ : SignedRep B) =
      ⟨B.zero, B.zero⟩
    rw [e.map_zero]
  map_one := by
    change Quot.mk _ (signedRepMap e (signedOneRep A)) =
      Quot.mk _ (signedOneRep B)
    apply congrArg (Quot.mk (signedSetoid B))
    change (⟨e.carrierEquiv A.one, e.carrierEquiv A.zero⟩ : SignedRep B) =
      ⟨B.one, B.zero⟩
    rw [e.map_one, e.map_zero]
  map_add := by
    intro a b
    refine Quot.induction_on a (fun a => ?_)
    refine Quot.induction_on b (fun b => ?_)
    change Quot.mk _ (signedRepMap e (signedAddRep A a b)) =
      Quot.mk _ (signedAddRep B (signedRepMap e a) (signedRepMap e b))
    apply congrArg (Quot.mk (signedSetoid B))
    change
      (⟨e.carrierEquiv (A.add a.pos b.pos),
        e.carrierEquiv (A.add a.neg b.neg)⟩ : SignedRep B) =
      ⟨B.add (e.carrierEquiv a.pos) (e.carrierEquiv b.pos),
       B.add (e.carrierEquiv a.neg) (e.carrierEquiv b.neg)⟩
    rw [e.map_add, e.map_add]
  map_mul := by
    intro a b
    refine Quot.induction_on a (fun a => ?_)
    refine Quot.induction_on b (fun b => ?_)
    change Quot.mk _ (signedRepMap e (signedMulRep A a b)) =
      Quot.mk _ (signedMulRep B (signedRepMap e a) (signedRepMap e b))
    apply congrArg (Quot.mk (signedSetoid B))
    change
      (⟨e.carrierEquiv
          (A.add (A.mul a.pos b.pos) (A.mul a.neg b.neg)),
        e.carrierEquiv
          (A.add (A.mul a.pos b.neg) (A.mul a.neg b.pos))⟩ : SignedRep B) =
      ⟨B.add
          (B.mul (e.carrierEquiv a.pos) (e.carrierEquiv b.pos))
          (B.mul (e.carrierEquiv a.neg) (e.carrierEquiv b.neg)),
       B.add
          (B.mul (e.carrierEquiv a.pos) (e.carrierEquiv b.neg))
          (B.mul (e.carrierEquiv a.neg) (e.carrierEquiv b.pos))⟩
    rw [e.map_add, e.map_add, e.map_mul, e.map_mul, e.map_mul, e.map_mul]
  map_neg := by
    intro a
    refine Quot.induction_on a (fun a => ?_)
    change Quot.mk _ (signedRepMap e (signedNegRep A a)) =
      Quot.mk _ (signedNegRep B (signedRepMap e a))
    rfl
  map_ofDen := by
    intro a
    change Quot.mk _ (signedRepMap e ⟨a, A.zero⟩) =
      Quot.mk _ ⟨e.carrierEquiv a, B.zero⟩
    apply congrArg (Quot.mk (signedSetoid B))
    change (⟨e.carrierEquiv a, e.carrierEquiv A.zero⟩ : SignedRep B) =
      ⟨e.carrierEquiv a, B.zero⟩
    rw [e.map_zero]

/-! ## Literal positive-denominator fraction completion -/

structure FractionRep (R : SignedBundle) where
  num : R.Carrier
  den : R.denom.Carrier
  den_ne_zero : den ≠ R.denom.zero

def fractionRel (R : SignedBundle) (a b : FractionRep R) : Prop :=
  R.mul a.num (R.ofDen b.den) = R.mul b.num (R.ofDen a.den)

theorem fractionRel_iff_intCross (R : SignedBundle) (a b : FractionRep R) :
    fractionRel R a b ↔
      R.toInt a.num * (R.denom.toNat b.den : ℤ) =
        R.toInt b.num * (R.denom.toNat a.den : ℤ) := by
  unfold fractionRel
  constructor
  · intro h
    have h' := congrArg (fun x => R.toInt x) h
    simpa [R.toInt_mul, R.toInt_ofDen] using h'
  · intro h
    apply R.toInt.injective
    simpa [R.toInt_mul, R.toInt_ofDen] using h

theorem fractionDenInt_ne_zero (R : SignedBundle) (a : FractionRep R) :
    (R.denom.toNat a.den : ℤ) ≠ 0 := by
  intro h
  have hn : R.denom.toNat a.den = 0 := by exact_mod_cast h
  apply a.den_ne_zero
  apply R.denom.toNat.injective
  rw [hn, R.denom.toNat_zero]

def fractionSetoid (R : SignedBundle) : Setoid (FractionRep R) where
  r := fractionRel R
  iseqv := {
    refl := fun a => by
      rw [fractionRel_iff_intCross]
    symm := fun h => by
      rw [fractionRel_iff_intCross] at h ⊢
      exact h.symm
    trans := by
      intro a b c hab hbc
      rw [fractionRel_iff_intCross] at hab hbc ⊢
      apply Int.eq_of_mul_eq_mul_right (fractionDenInt_ne_zero R b)
      linear_combination
        (R.denom.toNat c.den : ℤ) * hab +
        (R.denom.toNat a.den : ℤ) * hbc
  }

def FractionCarrier (R : SignedBundle) : Type :=
  Quot (fractionSetoid R)

def fractionRepSubtypeEquiv (R : SignedBundle) :
    {p : R.Carrier × R.denom.Carrier // p.2 ≠ R.denom.zero} ≃ FractionRep R where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  invFun q := ⟨(q.num, q.den), q.den_ne_zero⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def fractionRepresentation (R : SignedBundle) : Representation (FractionCarrier R) := by
  letI := R.denom.decEq
  exact representationQuot
    (representationEquiv
      ((R.repr.prod R.denom.repr).subtype
        (fun p => p.2 ≠ R.denom.zero))
      (fractionRepSubtypeEquiv R))
    (fractionSetoid R)

def fractionCarrierDecidableEq (R : SignedBundle) :
    DecidableEq (FractionCarrier R) := by
  letI := R.decEq
  letI : DecidableRel (fractionSetoid R).r := fun a b => by
    change Decidable
      (R.mul a.num (R.ofDen b.den) = R.mul b.num (R.ofDen a.den))
    exact R.decEq _ _
  exact quotDecidableEq (fractionSetoid R)

def fractionOf (R : SignedBundle) (a : R.Carrier) : FractionCarrier R :=
  Quot.mk (fractionSetoid R) ⟨a, R.denom.one, fun h =>
    R.denom.zero_ne_one h.symm⟩

theorem fractionOf_injective (R : SignedBundle) :
    Function.Injective (fractionOf R) := by
  intro a b h
  have hrel : fractionRel R
      ⟨a, R.denom.one, fun h => R.denom.zero_ne_one h.symm⟩
      ⟨b, R.denom.one, fun h => R.denom.zero_ne_one h.symm⟩ :=
    Quotient.exact h
  unfold fractionRel at hrel
  rw [R.ofDen_one, R.mul_one, R.mul_one] at hrel
  exact hrel

def fractionSourceEmbedding (R : SignedBundle) : R.Carrier ↪ FractionCarrier R :=
  ⟨fractionOf R, fractionOf_injective R⟩

def fractionZeroRep (R : SignedBundle) : FractionRep R :=
  ⟨R.zero, R.denom.one, fun h => R.denom.zero_ne_one h.symm⟩

def fractionOneRep (R : SignedBundle) : FractionRep R :=
  ⟨R.one, R.denom.one, fun h => R.denom.zero_ne_one h.symm⟩

def fractionNegRep (R : SignedBundle) (a : FractionRep R) : FractionRep R :=
  ⟨R.neg a.num, a.den, a.den_ne_zero⟩

def fractionAddRep (R : SignedBundle) (a b : FractionRep R) : FractionRep R :=
  ⟨R.add (R.mul a.num (R.ofDen b.den))
      (R.mul b.num (R.ofDen a.den)),
   R.denom.mul a.den b.den,
   R.denom.mul_ne_zero a.den_ne_zero b.den_ne_zero⟩

def fractionMulRep (R : SignedBundle) (a b : FractionRep R) : FractionRep R :=
  ⟨R.mul a.num b.num,
   R.denom.mul a.den b.den,
   R.denom.mul_ne_zero a.den_ne_zero b.den_ne_zero⟩

def fractionNumInt (R : SignedBundle) (a : FractionRep R) : ℤ :=
  R.toInt a.num

def fractionDenInt (R : SignedBundle) (a : FractionRep R) : ℤ :=
  R.denom.toNat a.den

@[simp] theorem fractionNumInt_zero (R : SignedBundle) :
    fractionNumInt R (fractionZeroRep R) = 0 := R.toInt_zero

@[simp] theorem fractionDenInt_zero (R : SignedBundle) :
    fractionDenInt R (fractionZeroRep R) = 1 := by
  change (R.denom.toNat R.denom.one : ℤ) = 1
  exact_mod_cast R.denom.toNat_one

@[simp] theorem fractionNumInt_one (R : SignedBundle) :
    fractionNumInt R (fractionOneRep R) = 1 := R.toInt_one

@[simp] theorem fractionDenInt_one (R : SignedBundle) :
    fractionDenInt R (fractionOneRep R) = 1 := by
  change (R.denom.toNat R.denom.one : ℤ) = 1
  exact_mod_cast R.denom.toNat_one

@[simp] theorem fractionNumInt_neg (R : SignedBundle) (a : FractionRep R) :
    fractionNumInt R (fractionNegRep R a) = -fractionNumInt R a :=
  R.toInt_neg a.num

@[simp] theorem fractionDenInt_neg (R : SignedBundle) (a : FractionRep R) :
    fractionDenInt R (fractionNegRep R a) = fractionDenInt R a := rfl

@[simp] theorem fractionNumInt_add (R : SignedBundle)
    (a b : FractionRep R) :
    fractionNumInt R (fractionAddRep R a b) =
      fractionNumInt R a * fractionDenInt R b +
        fractionNumInt R b * fractionDenInt R a := by
  simp [fractionNumInt, fractionDenInt, fractionAddRep,
    R.toInt_add, R.toInt_mul, R.toInt_ofDen]

@[simp] theorem fractionDenInt_add (R : SignedBundle)
    (a b : FractionRep R) :
    fractionDenInt R (fractionAddRep R a b) =
      fractionDenInt R a * fractionDenInt R b := by
  unfold fractionDenInt fractionAddRep
  exact_mod_cast R.denom.toNat_mul a.den b.den

@[simp] theorem fractionNumInt_mul (R : SignedBundle)
    (a b : FractionRep R) :
    fractionNumInt R (fractionMulRep R a b) =
      fractionNumInt R a * fractionNumInt R b := by
  exact R.toInt_mul a.num b.num

@[simp] theorem fractionDenInt_mul (R : SignedBundle)
    (a b : FractionRep R) :
    fractionDenInt R (fractionMulRep R a b) =
      fractionDenInt R a * fractionDenInt R b := by
  unfold fractionDenInt fractionMulRep
  exact_mod_cast R.denom.toNat_mul a.den b.den

def fractionZero (R : SignedBundle) : FractionCarrier R :=
  Quot.mk (fractionSetoid R) (fractionZeroRep R)

def fractionOne (R : SignedBundle) : FractionCarrier R :=
  Quot.mk (fractionSetoid R) (fractionOneRep R)

def fractionNeg (R : SignedBundle) : FractionCarrier R → FractionCarrier R :=
  Quot.lift (fun a => Quot.mk (fractionSetoid R) (fractionNegRep R a)) (by
    intro a b h
    apply Quot.sound
    change fractionRel R (fractionNegRep R a) (fractionNegRep R b)
    change fractionRel R a b at h
    rw [fractionRel_iff_intCross] at h ⊢
    change fractionNumInt R a * fractionDenInt R b =
      fractionNumInt R b * fractionDenInt R a at h
    change
      fractionNumInt R (fractionNegRep R a) *
          fractionDenInt R (fractionNegRep R b) =
        fractionNumInt R (fractionNegRep R b) *
          fractionDenInt R (fractionNegRep R a)
    simp only [fractionNumInt_neg, fractionDenInt_neg]
    linear_combination -h)

def fractionAdd (R : SignedBundle) : FractionCarrier R → FractionCarrier R →
    FractionCarrier R :=
  Quot.lift₂
    (fun a b => Quot.mk (fractionSetoid R) (fractionAddRep R a b))
    (by
      intro a b₁ b₂ h
      apply Quot.sound
      change fractionRel R (fractionAddRep R a b₁) (fractionAddRep R a b₂)
      change fractionRel R b₁ b₂ at h
      rw [fractionRel_iff_intCross] at h ⊢
      change fractionNumInt R b₁ * fractionDenInt R b₂ =
        fractionNumInt R b₂ * fractionDenInt R b₁ at h
      change
        fractionNumInt R (fractionAddRep R a b₁) *
            fractionDenInt R (fractionAddRep R a b₂) =
          fractionNumInt R (fractionAddRep R a b₂) *
            fractionDenInt R (fractionAddRep R a b₁)
      simp only [fractionNumInt_add, fractionDenInt_add]
      linear_combination
        (fractionDenInt R a * fractionDenInt R a) * h)
    (by
      intro a₁ a₂ b h
      apply Quot.sound
      change fractionRel R (fractionAddRep R a₁ b) (fractionAddRep R a₂ b)
      change fractionRel R a₁ a₂ at h
      rw [fractionRel_iff_intCross] at h ⊢
      change fractionNumInt R a₁ * fractionDenInt R a₂ =
        fractionNumInt R a₂ * fractionDenInt R a₁ at h
      change
        fractionNumInt R (fractionAddRep R a₁ b) *
            fractionDenInt R (fractionAddRep R a₂ b) =
          fractionNumInt R (fractionAddRep R a₂ b) *
            fractionDenInt R (fractionAddRep R a₁ b)
      simp only [fractionNumInt_add, fractionDenInt_add]
      linear_combination
        (fractionDenInt R b * fractionDenInt R b) * h)

def fractionMul (R : SignedBundle) : FractionCarrier R → FractionCarrier R →
    FractionCarrier R :=
  Quot.lift₂
    (fun a b => Quot.mk (fractionSetoid R) (fractionMulRep R a b))
    (by
      intro a b₁ b₂ h
      apply Quot.sound
      change fractionRel R (fractionMulRep R a b₁) (fractionMulRep R a b₂)
      change fractionRel R b₁ b₂ at h
      rw [fractionRel_iff_intCross] at h ⊢
      change fractionNumInt R b₁ * fractionDenInt R b₂ =
        fractionNumInt R b₂ * fractionDenInt R b₁ at h
      change
        fractionNumInt R (fractionMulRep R a b₁) *
            fractionDenInt R (fractionMulRep R a b₂) =
          fractionNumInt R (fractionMulRep R a b₂) *
            fractionDenInt R (fractionMulRep R a b₁)
      simp only [fractionNumInt_mul, fractionDenInt_mul]
      linear_combination
        (fractionNumInt R a * fractionDenInt R a) * h)
    (by
      intro a₁ a₂ b h
      apply Quot.sound
      change fractionRel R (fractionMulRep R a₁ b) (fractionMulRep R a₂ b)
      change fractionRel R a₁ a₂ at h
      rw [fractionRel_iff_intCross] at h ⊢
      change fractionNumInt R a₁ * fractionDenInt R a₂ =
        fractionNumInt R a₂ * fractionDenInt R a₁ at h
      change
        fractionNumInt R (fractionMulRep R a₁ b) *
            fractionDenInt R (fractionMulRep R a₂ b) =
          fractionNumInt R (fractionMulRep R a₂ b) *
            fractionDenInt R (fractionMulRep R a₁ b)
      simp only [fractionNumInt_mul, fractionDenInt_mul]
      linear_combination
        (fractionNumInt R b * fractionDenInt R b) * h)

theorem fractionAdd_assoc_raw (R : SignedBundle)
    (a b c : FractionCarrier R) :
    fractionAdd R (fractionAdd R a b) c =
      fractionAdd R a (fractionAdd R b c) := by
  refine Quot.induction_on a (fun a => ?_)
  refine Quot.induction_on b (fun b => ?_)
  refine Quot.induction_on c (fun c => ?_)
  apply Quot.sound
  change fractionRel R
    (fractionAddRep R (fractionAddRep R a b) c)
    (fractionAddRep R a (fractionAddRep R b c))
  rw [fractionRel_iff_intCross]
  change
    fractionNumInt R (fractionAddRep R (fractionAddRep R a b) c) *
        fractionDenInt R (fractionAddRep R a (fractionAddRep R b c)) =
      fractionNumInt R (fractionAddRep R a (fractionAddRep R b c)) *
        fractionDenInt R (fractionAddRep R (fractionAddRep R a b) c)
  simp only [fractionNumInt_add, fractionDenInt_add]
  ring

theorem fractionAdd_comm_raw (R : SignedBundle) (a b : FractionCarrier R) :
    fractionAdd R a b = fractionAdd R b a := by
  refine Quot.induction_on a (fun a => ?_)
  refine Quot.induction_on b (fun b => ?_)
  apply Quot.sound
  change fractionRel R (fractionAddRep R a b) (fractionAddRep R b a)
  rw [fractionRel_iff_intCross]
  change
    fractionNumInt R (fractionAddRep R a b) *
        fractionDenInt R (fractionAddRep R b a) =
      fractionNumInt R (fractionAddRep R b a) *
        fractionDenInt R (fractionAddRep R a b)
  simp only [fractionNumInt_add, fractionDenInt_add]
  ring

theorem fractionAdd_zero_raw (R : SignedBundle) (a : FractionCarrier R) :
    fractionAdd R a (fractionZero R) = a := by
  refine Quot.induction_on a (fun a => ?_)
  apply Quot.sound
  change fractionRel R (fractionAddRep R a (fractionZeroRep R)) a
  rw [fractionRel_iff_intCross]
  change
    fractionNumInt R (fractionAddRep R a (fractionZeroRep R)) *
        fractionDenInt R a =
      fractionNumInt R a *
        fractionDenInt R (fractionAddRep R a (fractionZeroRep R))
  simp only [fractionNumInt_add, fractionDenInt_add,
    fractionNumInt_zero, fractionDenInt_zero]
  ring

theorem fractionAdd_neg_raw (R : SignedBundle) (a : FractionCarrier R) :
    fractionAdd R a (fractionNeg R a) = fractionZero R := by
  refine Quot.induction_on a (fun a => ?_)
  apply Quot.sound
  change fractionRel R
    (fractionAddRep R a (fractionNegRep R a)) (fractionZeroRep R)
  rw [fractionRel_iff_intCross]
  change
    fractionNumInt R (fractionAddRep R a (fractionNegRep R a)) *
        fractionDenInt R (fractionZeroRep R) =
      fractionNumInt R (fractionZeroRep R) *
        fractionDenInt R (fractionAddRep R a (fractionNegRep R a))
  simp only [fractionNumInt_add, fractionDenInt_add,
    fractionNumInt_neg, fractionDenInt_neg,
    fractionNumInt_zero, fractionDenInt_zero]
  ring

theorem fractionMul_assoc_raw (R : SignedBundle)
    (a b c : FractionCarrier R) :
    fractionMul R (fractionMul R a b) c =
      fractionMul R a (fractionMul R b c) := by
  refine Quot.induction_on a (fun a => ?_)
  refine Quot.induction_on b (fun b => ?_)
  refine Quot.induction_on c (fun c => ?_)
  apply Quot.sound
  change fractionRel R
    (fractionMulRep R (fractionMulRep R a b) c)
    (fractionMulRep R a (fractionMulRep R b c))
  rw [fractionRel_iff_intCross]
  change
    fractionNumInt R (fractionMulRep R (fractionMulRep R a b) c) *
        fractionDenInt R (fractionMulRep R a (fractionMulRep R b c)) =
      fractionNumInt R (fractionMulRep R a (fractionMulRep R b c)) *
        fractionDenInt R (fractionMulRep R (fractionMulRep R a b) c)
  simp only [fractionNumInt_mul, fractionDenInt_mul]
  ring

theorem fractionMul_comm_raw (R : SignedBundle) (a b : FractionCarrier R) :
    fractionMul R a b = fractionMul R b a := by
  refine Quot.induction_on a (fun a => ?_)
  refine Quot.induction_on b (fun b => ?_)
  apply Quot.sound
  change fractionRel R (fractionMulRep R a b) (fractionMulRep R b a)
  rw [fractionRel_iff_intCross]
  change
    fractionNumInt R (fractionMulRep R a b) *
        fractionDenInt R (fractionMulRep R b a) =
      fractionNumInt R (fractionMulRep R b a) *
        fractionDenInt R (fractionMulRep R a b)
  simp only [fractionNumInt_mul, fractionDenInt_mul]
  ring

theorem fractionMul_one_raw (R : SignedBundle) (a : FractionCarrier R) :
    fractionMul R a (fractionOne R) = a := by
  refine Quot.induction_on a (fun a => ?_)
  apply Quot.sound
  change fractionRel R (fractionMulRep R a (fractionOneRep R)) a
  rw [fractionRel_iff_intCross]
  change
    fractionNumInt R (fractionMulRep R a (fractionOneRep R)) *
        fractionDenInt R a =
      fractionNumInt R a *
        fractionDenInt R (fractionMulRep R a (fractionOneRep R))
  simp only [fractionNumInt_mul, fractionDenInt_mul,
    fractionNumInt_one, fractionDenInt_one]
  ring

theorem fractionOne_mul_raw (R : SignedBundle) (a : FractionCarrier R) :
    fractionMul R (fractionOne R) a = a := by
  rw [fractionMul_comm_raw]
  exact fractionMul_one_raw R a

theorem fractionLeft_distrib_raw (R : SignedBundle)
    (a b c : FractionCarrier R) :
    fractionMul R a (fractionAdd R b c) =
      fractionAdd R (fractionMul R a b) (fractionMul R a c) := by
  refine Quot.induction_on a (fun a => ?_)
  refine Quot.induction_on b (fun b => ?_)
  refine Quot.induction_on c (fun c => ?_)
  apply Quot.sound
  change fractionRel R
    (fractionMulRep R a (fractionAddRep R b c))
    (fractionAddRep R (fractionMulRep R a b) (fractionMulRep R a c))
  rw [fractionRel_iff_intCross]
  change
    fractionNumInt R (fractionMulRep R a (fractionAddRep R b c)) *
        fractionDenInt R
          (fractionAddRep R (fractionMulRep R a b) (fractionMulRep R a c)) =
      fractionNumInt R
          (fractionAddRep R (fractionMulRep R a b) (fractionMulRep R a c)) *
        fractionDenInt R (fractionMulRep R a (fractionAddRep R b c))
  simp only [fractionNumInt_add, fractionDenInt_add,
    fractionNumInt_mul, fractionDenInt_mul]
  ring

theorem fractionZero_ne_one_raw (R : SignedBundle) :
    fractionZero R ≠ fractionOne R := by
  intro h
  have hrel : fractionRel R (fractionZeroRep R) (fractionOneRep R) :=
    Quotient.exact h
  rw [fractionRel_iff_intCross] at hrel
  change
    fractionNumInt R (fractionZeroRep R) *
        fractionDenInt R (fractionOneRep R) =
      fractionNumInt R (fractionOneRep R) *
        fractionDenInt R (fractionZeroRep R) at hrel
  simp only [fractionNumInt_zero, fractionDenInt_zero,
    fractionNumInt_one, fractionDenInt_one] at hrel
  exact Int.zero_ne_one hrel

/-- The terminal fraction bundle carries arithmetic computed on the quotient
whose relation was built from the signed source's own multiplication. -/
structure FractionBundle where
  source : SignedBundle
  Carrier : Type
  zero : Carrier
  one : Carrier
  add : Carrier → Carrier → Carrier
  mul : Carrier → Carrier → Carrier
  neg : Carrier → Carrier
  decEq : DecidableEq Carrier
  repr : Representation Carrier
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  add_zero : ∀ a, add a zero = a
  add_neg : ∀ a, add a (neg a) = zero
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  mul_one : ∀ a, mul a one = a
  one_mul : ∀ a, mul one a = a
  left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  zero_ne_one : zero ≠ one

def fractionCompletion (R : SignedBundle) : FractionBundle where
  source := R
  Carrier := FractionCarrier R
  zero := fractionZero R
  one := fractionOne R
  add := fractionAdd R
  mul := fractionMul R
  neg := fractionNeg R
  decEq := fractionCarrierDecidableEq R
  repr := fractionRepresentation R
  add_assoc := fractionAdd_assoc_raw R
  add_comm := fractionAdd_comm_raw R
  add_zero := fractionAdd_zero_raw R
  add_neg := fractionAdd_neg_raw R
  mul_assoc := fractionMul_assoc_raw R
  mul_comm := fractionMul_comm_raw R
  mul_one := fractionMul_one_raw R
  one_mul := fractionOne_mul_raw R
  left_distrib := fractionLeft_distrib_raw R
  zero_ne_one := fractionZero_ne_one_raw R

structure FractionBundleIso (A B : FractionBundle) where
  sourceIso : SignedBundleIso A.source B.source
  carrierEquiv : A.Carrier ≃ B.Carrier
  map_zero : carrierEquiv A.zero = B.zero
  map_one : carrierEquiv A.one = B.one
  map_add : ∀ a b, carrierEquiv (A.add a b) =
    B.add (carrierEquiv a) (carrierEquiv b)
  map_mul : ∀ a b, carrierEquiv (A.mul a b) =
    B.mul (carrierEquiv a) (carrierEquiv b)
  map_neg : ∀ a, carrierEquiv (A.neg a) = B.neg (carrierEquiv a)

def FractionBundleIso.refl (A : FractionBundle) : FractionBundleIso A A where
  sourceIso := SignedBundleIso.refl A.source
  carrierEquiv := Equiv.refl _
  map_zero := rfl
  map_one := rfl
  map_add := fun _ _ => rfl
  map_mul := fun _ _ => rfl
  map_neg := fun _ => rfl

def fractionRepMap {A B : SignedBundle} (e : SignedBundleIso A B) :
    FractionRep A ≃ FractionRep B where
  toFun q := {
    num := e.carrierEquiv q.num
    den := e.denomIso.carrierEquiv q.den
    den_ne_zero := by
      intro h
      apply q.den_ne_zero
      apply e.denomIso.carrierEquiv.injective
      simpa [e.denomIso.map_zero] using h
  }
  invFun q := {
    num := e.carrierEquiv.symm q.num
    den := e.denomIso.carrierEquiv.symm q.den
    den_ne_zero := by
      intro h
      apply q.den_ne_zero
      have h' := congrArg e.denomIso.carrierEquiv h
      simpa [e.denomIso.map_zero] using h'
  }
  left_inv q := by cases q; simp
  right_inv q := by cases q; simp

theorem fractionRepMap_rel {A B : SignedBundle} (e : SignedBundleIso A B)
    (a b : FractionRep A) :
    fractionRel A a b ↔
      fractionRel B (fractionRepMap e a) (fractionRepMap e b) := by
  change
    A.mul a.num (A.ofDen b.den) = A.mul b.num (A.ofDen a.den) ↔
      B.mul (e.carrierEquiv a.num)
          (B.ofDen (e.denomIso.carrierEquiv b.den)) =
        B.mul (e.carrierEquiv b.num)
          (B.ofDen (e.denomIso.carrierEquiv a.den))
  constructor
  · intro h
    rw [← e.map_ofDen, ← e.map_ofDen, ← e.map_mul, ← e.map_mul, h]
  · intro h
    apply e.carrierEquiv.injective
    simpa [e.map_mul, e.map_ofDen] using h

theorem fractionRep_ext {R : SignedBundle} {a b : FractionRep R}
    (hnum : a.num = b.num) (hden : a.den = b.den) :
    a = b := by
  cases a with
  | mk anum aden ah =>
      cases b with
      | mk bnum bden bh =>
          simp only at hnum hden
          subst bnum
          subst bden
          rfl

theorem fractionRepMap_zero {A B : SignedBundle} (e : SignedBundleIso A B) :
    fractionRepMap e (fractionZeroRep A) = fractionZeroRep B := by
  apply fractionRep_ext
  · exact e.map_zero
  · exact e.denomIso.map_one

theorem fractionRepMap_one {A B : SignedBundle} (e : SignedBundleIso A B) :
    fractionRepMap e (fractionOneRep A) = fractionOneRep B := by
  apply fractionRep_ext
  · exact e.map_one
  · exact e.denomIso.map_one

theorem fractionRepMap_neg {A B : SignedBundle} (e : SignedBundleIso A B)
    (a : FractionRep A) :
    fractionRepMap e (fractionNegRep A a) =
      fractionNegRep B (fractionRepMap e a) := by
  apply fractionRep_ext
  · exact e.map_neg a.num
  · rfl

theorem fractionRepMap_add {A B : SignedBundle} (e : SignedBundleIso A B)
    (a b : FractionRep A) :
    fractionRepMap e (fractionAddRep A a b) =
      fractionAddRep B (fractionRepMap e a) (fractionRepMap e b) := by
  apply fractionRep_ext
  · change
      e.carrierEquiv
          (A.add (A.mul a.num (A.ofDen b.den))
            (A.mul b.num (A.ofDen a.den))) =
        B.add
          (B.mul (e.carrierEquiv a.num)
            (B.ofDen (e.denomIso.carrierEquiv b.den)))
          (B.mul (e.carrierEquiv b.num)
            (B.ofDen (e.denomIso.carrierEquiv a.den)))
    rw [e.map_add, e.map_mul, e.map_mul, e.map_ofDen, e.map_ofDen]
  · exact e.denomIso.map_mul a.den b.den

theorem fractionRepMap_mul {A B : SignedBundle} (e : SignedBundleIso A B)
    (a b : FractionRep A) :
    fractionRepMap e (fractionMulRep A a b) =
      fractionMulRep B (fractionRepMap e a) (fractionRepMap e b) := by
  apply fractionRep_ext
  · exact e.map_mul a.num b.num
  · exact e.denomIso.map_mul a.den b.den

def fractionCarrierMap {A B : SignedBundle} (e : SignedBundleIso A B) :
    FractionCarrier A ≃ FractionCarrier B :=
  quotEquivOfEquiv (fractionSetoid A) (fractionSetoid B) (fractionRepMap e)
    (fractionRepMap_rel e)

def fractionMapIso {A B : SignedBundle} (e : SignedBundleIso A B) :
    FractionBundleIso (fractionCompletion A) (fractionCompletion B) where
  sourceIso := e
  carrierEquiv := fractionCarrierMap e
  map_zero := by
    change Quot.mk _ (fractionRepMap e (fractionZeroRep A)) =
      Quot.mk _ (fractionZeroRep B)
    rw [fractionRepMap_zero]
  map_one := by
    change Quot.mk _ (fractionRepMap e (fractionOneRep A)) =
      Quot.mk _ (fractionOneRep B)
    rw [fractionRepMap_one]
  map_add := by
    intro a b
    refine Quot.induction_on a (fun a => ?_)
    refine Quot.induction_on b (fun b => ?_)
    change Quot.mk _ (fractionRepMap e (fractionAddRep A a b)) =
      Quot.mk _ (fractionAddRep B (fractionRepMap e a) (fractionRepMap e b))
    rw [fractionRepMap_add]
  map_mul := by
    intro a b
    refine Quot.induction_on a (fun a => ?_)
    refine Quot.induction_on b (fun b => ?_)
    change Quot.mk _ (fractionRepMap e (fractionMulRep A a b)) =
      Quot.mk _ (fractionMulRep B (fractionRepMap e a) (fractionRepMap e b))
    rw [fractionRepMap_mul]
  map_neg := by
    intro a
    refine Quot.induction_on a (fun a => ?_)
    change Quot.mk _ (fractionRepMap e (fractionNegRep A a)) =
      Quot.mk _ (fractionNegRep B (fractionRepMap e a))
    rw [fractionRepMap_neg]

/-! ## Gate 0: computed quotients recover the exported carriers -/

def signedRepNatToOrbit (z : SignedRep natDeltaBundle) : SignedOrbit :=
  ⟨z.pos, z.neg⟩

def signedRepNatEquivOrbit : SignedRep natDeltaBundle ≃ SignedOrbit where
  toFun := signedRepNatToOrbit
  invFun z := ⟨z.pos, z.neg⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

theorem signedRepNat_rel (a b : SignedRep natDeltaBundle) :
    signedRel natDeltaBundle a b ↔
      signedOrbitSetoid.r (signedRepNatEquivOrbit a) (signedRepNatEquivOrbit b) := by
  rfl

def signedNatEquivInt :
    (signedCompletion natDeltaBundle).Carrier ≃ IntDelta :=
  quotEquivOfEquiv (signedSetoid natDeltaBundle) signedOrbitSetoid
    signedRepNatEquivOrbit signedRepNat_rel

theorem signedNatEquivInt_toInt (z : (signedCompletion natDeltaBundle).Carrier) :
    PRCInt.toInt (signedNatEquivInt z) =
      (signedCompletion natDeltaBundle).toInt z := by
  refine Quot.induction_on z (fun z => ?_)
  rfl

def fractionComputedToRatRep
    (q : FractionRep (signedCompletion natDeltaBundle)) : RatioOrbit where
  num := signedOfInt ((signedCompletion natDeltaBundle).toInt q.num)
  den := q.den
  den_ne_zero := q.den_ne_zero

theorem fractionComputedToRatRep_respects
    {a b : FractionRep (signedCompletion natDeltaBundle)}
    (h : fractionRel (signedCompletion natDeltaBundle) a b) :
    RatioOrbit.crossEq (fractionComputedToRatRep a)
      (fractionComputedToRatRep b) := by
  rw [RatioOrbit.crossEq_iff_toIntCross]
  simpa [fractionComputedToRatRep, signedOfInt_toInt] using
    (fractionRel_iff_intCross _ a b).mp h

def fractionComputedToRat :
    FractionCarrier (signedCompletion natDeltaBundle) → RatDelta :=
  Quot.lift (fun q => PRCRat.mk (fractionComputedToRatRep q))
    (fun _ _ h => Quot.sound (fractionComputedToRatRep_respects h))

def ratioOrbitToComputedRep (q : RatioOrbit) :
    FractionRep (signedCompletion natDeltaBundle) where
  num := Quot.mk (signedSetoid natDeltaBundle) ⟨q.num.pos, q.num.neg⟩
  den := q.den
  den_ne_zero := q.den_ne_zero

theorem ratioOrbitToComputedRep_respects {a b : RatioOrbit}
    (h : RatioOrbit.crossEq a b) :
    fractionRel (signedCompletion natDeltaBundle)
      (ratioOrbitToComputedRep a) (ratioOrbitToComputedRep b) := by
  rw [fractionRel_iff_intCross]
  rw [RatioOrbit.crossEq_iff_toIntCross] at h
  exact h

def ratToFractionComputed : RatDelta →
    FractionCarrier (signedCompletion natDeltaBundle) :=
  Quot.lift
    (fun q => Quot.mk (fractionSetoid _) (ratioOrbitToComputedRep q))
    (fun _ _ h => Quot.sound (ratioOrbitToComputedRep_respects h))

theorem ratToFractionComputed_leftInverse :
    Function.LeftInverse ratToFractionComputed fractionComputedToRat := by
  intro q
  refine Quot.induction_on q (fun q => ?_)
  apply Quot.sound
  change fractionRel (signedCompletion natDeltaBundle)
    (ratioOrbitToComputedRep (fractionComputedToRatRep q)) q
  rw [fractionRel_iff_intCross]
  have hnum :
      (signedCompletion natDeltaBundle).toInt
          (ratioOrbitToComputedRep (fractionComputedToRatRep q)).num =
        (signedCompletion natDeltaBundle).toInt q.num := by
    change (signedOfInt
      ((signedCompletion natDeltaBundle).toInt q.num)).toInt =
        (signedCompletion natDeltaBundle).toInt q.num
    exact signedOfInt_toInt _
  exact congrArg
    (fun z : ℤ => z * ((signedCompletion natDeltaBundle).denom.toNat q.den : ℤ))
    hnum

theorem ratToFractionComputed_rightInverse :
    Function.RightInverse ratToFractionComputed fractionComputedToRat := by
  intro q
  refine Quot.induction_on q (fun q => ?_)
  apply Quot.sound
  change RatioOrbit.crossEq
    (fractionComputedToRatRep (ratioOrbitToComputedRep q)) q
  rw [RatioOrbit.crossEq_iff_toIntCross]
  have hnum :
      (fractionComputedToRatRep (ratioOrbitToComputedRep q)).num.toInt =
        q.num.toInt := by
    change (signedOfInt q.num.toInt).toInt = q.num.toInt
    exact signedOfInt_toInt _
  exact congrArg (fun z : ℤ => z * (q.den.toNat : ℤ)) hnum

/-- Gate 0. The fraction quotient computed from the signed predecessor is
canonically equivalent to `RatDelta`. The proof normalizes signed numerators
through their integer display and keeps denominators in `NatDelta`; it never
uses `PRCRat.toRat` or representative choice. -/
def fractionIntEquivRat :
    (fractionCompletion (signedCompletion natDeltaBundle)).Carrier ≃ RatDelta where
  toFun := fractionComputedToRat
  invFun := ratToFractionComputed
  left_inv := ratToFractionComputed_leftInverse
  right_inv := ratToFractionComputed_rightInverse

/-! ## Stage-indexed derivations and exact normal form -/

inductive TowerStage where
  | orbit
  | signed
  | fraction
  deriving DecidableEq, Repr

def StageBundle : TowerStage → Type 1
  | .orbit => OrbitBundle
  | .signed => SignedBundle
  | .fraction => FractionBundle

def bundleCarrier {s : TowerStage} (B : StageBundle s) : Type :=
  match s, B with
  | .orbit, B => B.Carrier
  | .signed, B => B.Carrier
  | .fraction, B => B.Carrier

inductive CoreTower : {s : TowerStage} → StageBundle s → Type 1 where
  | free : CoreTower (s := .orbit) natDeltaBundle
  | signed {B : OrbitBundle} :
      CoreTower (s := .orbit) B →
        CoreTower (s := .signed) (signedCompletion B)
  | fraction {R : SignedBundle} :
      CoreTower (s := .signed) R →
        CoreTower (s := .fraction) (fractionCompletion R)

def canonicalBundle : (s : TowerStage) → StageBundle s
  | .orbit => natDeltaBundle
  | .signed => signedCompletion natDeltaBundle
  | .fraction => fractionCompletion (signedCompletion natDeltaBundle)

def BundleIso {s : TowerStage} (A B : StageBundle s) : Type :=
  match s with
  | .orbit => OrbitBundleIso A B
  | .signed => SignedBundleIso A B
  | .fraction => FractionBundleIso A B

def CoreTower.depth :
    {s : TowerStage} → {B : StageBundle s} → CoreTower B → ℕ
  | .orbit, _, .free => 0
  | .signed, _, .signed d => depth d + 1
  | .fraction, _, .fraction d => depth d + 1

/-- Every receipt has exactly the canonical bundle at its stage, up to the
operations preserved by that stage. The proof is genuine induction:
the signed case maps the predecessor orbit isomorphism through the balanced
quotient, and the fraction case maps the predecessor signed isomorphism through
the cross-product quotient. -/
theorem core_normalForm {s : TowerStage} {B : StageBundle s}
    (d : CoreTower B) :
    Nonempty (BundleIso B (canonicalBundle s)) := by
  induction d with
  | free => exact ⟨OrbitBundleIso.refl natDeltaBundle⟩
  | signed d ih =>
      rcases ih with ⟨e⟩
      exact ⟨signedMapIso e⟩
  | fraction d ih =>
      rcases ih with ⟨e⟩
      exact ⟨fractionMapIso e⟩

def coreNat : CoreTower (s := .orbit) natDeltaBundle := .free
def coreInt : CoreTower (s := .signed) (signedCompletion natDeltaBundle) :=
  .signed coreNat
def coreRat : CoreTower
    (s := .fraction)
    (fractionCompletion (signedCompletion natDeltaBundle)) := .fraction coreInt

theorem coreNat_depth : CoreTower.depth coreNat = 0 := rfl
theorem coreInt_depth : CoreTower.depth coreInt = 1 := rfl
theorem coreRat_depth : CoreTower.depth coreRat = 2 := rfl

structure TowerReceipt (X : Type) : Type 1 where
  stage : TowerStage
  bundle : StageBundle stage
  core : CoreTower (s := stage) bundle
  carrierEquiv : bundleCarrier bundle ≃ X

def TowerGen (X : Type) : Prop :=
  Nonempty (TowerReceipt X)

def natReceipt : TowerReceipt NatDelta where
  stage := .orbit
  bundle := natDeltaBundle
  core := coreNat
  carrierEquiv := Equiv.refl _

def intReceipt : TowerReceipt IntDelta where
  stage := .signed
  bundle := signedCompletion natDeltaBundle
  core := coreInt
  carrierEquiv := signedNatEquivInt

def ratReceipt : TowerReceipt RatDelta where
  stage := .fraction
  bundle := fractionCompletion (signedCompletion natDeltaBundle)
  core := coreRat
  carrierEquiv := fractionIntEquivRat

theorem towerGen_natDelta : TowerGen NatDelta := ⟨natReceipt⟩
theorem towerGen_intDelta : TowerGen IntDelta := ⟨intReceipt⟩
theorem towerGen_ratDelta : TowerGen RatDelta := ⟨ratReceipt⟩

theorem towerGen_equiv {X Y : Type} (e : X ≃ Y) :
    TowerGen X ↔ TowerGen Y := by
  constructor
  · rintro ⟨r⟩
    exact ⟨⟨r.stage, r.bundle, r.core, r.carrierEquiv.trans e⟩⟩
  · rintro ⟨r⟩
    exact ⟨⟨r.stage, r.bundle, r.core, r.carrierEquiv.trans e.symm⟩⟩

/-! ## Inductive invariants -/

def natToNatDelta (n : ℕ) : NatDelta := DistinctionNat.ofNat n

theorem natToNatDelta_injective : Function.Injective natToNatDelta := by
  intro a b h
  have h' := congrArg DistinctionNat.toNat h
  unfold natToNatDelta at h'
  rw [DistinctionNat.toNat_ofNat, DistinctionNat.toNat_ofNat] at h'
  exact h'

def natToNatDeltaEmbedding : ℕ ↪ NatDelta :=
  ⟨natToNatDelta, natToNatDelta_injective⟩

theorem deltaForced_signedCompletion (B : OrbitBundle) :
    DeltaForced (signedCompletion B).Carrier := by
  letI := (signedCompletion B).decEq
  exact deltaForced_of_representable ⟨(signedCompletion B).repr⟩

theorem deltaForced_fractionCompletion (R : SignedBundle) :
    DeltaForced (fractionCompletion R).Carrier := by
  letI := (fractionCompletion R).decEq
  exact deltaForced_of_representable ⟨(fractionCompletion R).repr⟩

def CoreTower.natEmbedding :
    {s : TowerStage} → {B : StageBundle s} →
      CoreTower B → (ℕ ↪ bundleCarrier B)
  | .orbit, _, .free => natToNatDeltaEmbedding
  | .signed, _, .signed d =>
      natEmbedding d |>.trans (signedSourceEmbedding _)
  | .fraction, _, .fraction d =>
      natEmbedding d |>.trans (fractionSourceEmbedding _)

theorem CoreTower.deltaForced {s : TowerStage} {B : StageBundle s}
    (d : CoreTower B) :
    DeltaForced (bundleCarrier B) := by
  induction d with
  | free => exact deltaForced_natDelta
  | signed d _ => exact deltaForced_signedCompletion _
  | fraction d _ => exact deltaForced_fractionCompletion _

theorem deltaForced_of_towerGen {X : Type} (h : TowerGen X) :
    DeltaForced X := by
  rcases h with ⟨r⟩
  rcases r.core.deltaForced with ⟨e⟩
  exact ⟨r.carrierEquiv.symm.toEmbedding.trans e⟩

theorem natEmbedding_of_towerGen {X : Type} (h : TowerGen X) :
    Nonempty (ℕ ↪ X) := by
  rcases h with ⟨r⟩
  exact ⟨r.core.natEmbedding.trans r.carrierEquiv.toEmbedding⟩

/-! ## Countability-independent finite exclusion -/

theorem no_injective_fin_succ :
    ∀ n : ℕ, ∀ f : Fin (n + 1) → Fin n, ¬ Function.Injective f
  | 0, f => fun _ => Fin.elim0 (f 0)
  | n + 1, f => by
      intro hf
      let p : Fin (n + 1) := f 0
      have hne (x : Fin (n + 1)) : f x.succ ≠ p := by
        intro h
        have hx : x.succ = (0 : Fin (n + 2)) := hf (by simpa [p] using h)
        exact Fin.succ_ne_zero x hx
      by_cases hp : p = Fin.last n
      · let g : Fin (n + 1) → Fin n := fun x =>
          (f x.succ).castPred (by simpa [hp] using hne x)
        have hg : Function.Injective g := by
          intro x y hxy
          apply Fin.succ_injective (n + 1)
          apply hf
          have hcast := congrArg Fin.castSucc hxy
          simpa [g] using hcast
        exact no_injective_fin_succ n g hg
      · let p' : Fin n := p.castPred hp
        let g : Fin (n + 1) → Fin n := fun x => p'.predAbove (f x.succ)
        have hg : Function.Injective g := by
          intro x y hxy
          apply Fin.succ_injective (n + 1)
          apply hf
          have hlift := congrArg (fun z => p'.castSucc.succAbove z) hxy
          have hnx : f x.succ ≠ p'.castSucc := by
            simpa [p', Fin.castSucc_castPred] using hne x
          have hny : f y.succ ≠ p'.castSucc := by
            simpa [p', Fin.castSucc_castPred] using hne y
          simpa [g, Fin.succAbove_predAbove hnx,
            Fin.succAbove_predAbove hny] using hlift
        exact no_injective_fin_succ n g hg

theorem no_nat_embedding_fin (n : ℕ) :
    ¬ Nonempty (ℕ ↪ Fin n) := by
  rintro ⟨e⟩
  let f : Fin (n + 1) → Fin n := fun x => e x.val
  apply no_injective_fin_succ n f
  intro a b hab
  apply Fin.ext
  exact e.injective hab

theorem infinite_of_towerGen {X : Type} (h : TowerGen X) :
    Infinite X where
  not_finite hfinite := by
    letI : Finite X := hfinite
    rcases Finite.exists_equiv_fin X with ⟨n, ⟨eFin⟩⟩
    rcases natEmbedding_of_towerGen h with ⟨eNat⟩
    exact no_nat_embedding_fin n ⟨eNat.trans eFin.toEmbedding⟩

theorem not_towerGen_fin17 : ¬ TowerGen (Fin 17) :=
  fun h => no_nat_embedding_fin 17 (natEmbedding_of_towerGen h)

theorem not_towerGen_fin2 : ¬ TowerGen (Fin 2) :=
  fun h => no_nat_embedding_fin 2 (natEmbedding_of_towerGen h)

theorem not_towerGen_fin0 : ¬ TowerGen (Fin 0) :=
  fun h => no_nat_embedding_fin 0 (natEmbedding_of_towerGen h)

/-! ## Exact bare-equivalence honesty surface -/

theorem towerGen_of_natDelta_equiv {X : Type} (e : NatDelta ≃ X) :
    TowerGen X :=
  (towerGen_equiv e).mp towerGen_natDelta

theorem equiv_invariant_predicate_contains_natDelta_equiv
    (P : Type → Prop)
    (hbase : P NatDelta)
    (htransport : ∀ {X Y : Type}, P X → (X ≃ Y) → P Y)
    {X : Type} (e : NatDelta ≃ X) :
    P X :=
  htransport hbase e

/-- Honesty capstone. Once a predicate on bare carriers contains `NatDelta`
and transports across arbitrary equivalences, it contains every explicitly
denumerable carrier. Therefore bare equivalence cannot preserve construction
provenance; that information lives in `CoreTower` and `core_normalForm`. -/
theorem equiv_invariant_predicate_contains_all_denumerable
    (P : Type → Prop)
    (hbase : P NatDelta)
    (htransport : ∀ {X Y : Type}, P X → (X ≃ Y) → P Y)
    {X : Type} (hX : Nonempty (ℕ ≃ X)) :
    P X := by
  rcases hX with ⟨e⟩
  exact equiv_invariant_predicate_contains_natDelta_equiv
    P hbase htransport (DistinctionNat.equivNat.trans e)

def natEquivEvenNat : ℕ ≃ {n : ℕ // Even n} where
  toFun n := ⟨2 * n, ⟨n, by omega⟩⟩
  invFun n := n.1 / 2
  left_inv n := by
    exact Nat.mul_div_cancel_left n (by omega)
  right_inv n := by
    apply Subtype.ext
    exact Nat.mul_div_cancel' (even_iff_two_dvd.mp n.2)

theorem towerGen_evenNat : TowerGen {n : ℕ // Even n} :=
  towerGen_of_natDelta_equiv (DistinctionNat.equivNat.trans natEquivEvenNat)

/-! ## Classical boundary -/

theorem not_towerGen_real : ¬ TowerGen ℝ := by
  intro h
  exact not_deltaForced_real (deltaForced_of_towerGen h)

/-! ## Split capstones -/

def BootstrapTowerGenerationCoreSpec : Prop :=
  TowerGen NatDelta ∧
  TowerGen IntDelta ∧
  TowerGen RatDelta ∧
  (∀ {X : Type}, TowerGen X → DeltaForced X) ∧
  (∀ {X : Type}, TowerGen X → Nonempty (ℕ ↪ X)) ∧
  (∀ {X : Type}, TowerGen X → Infinite X) ∧
  (∀ {s : TowerStage} {B : StageBundle s}, CoreTower B →
    Nonempty (BundleIso B (canonicalBundle s))) ∧
  (∀ {X : Type}, Nonempty (NatDelta ≃ X) → TowerGen X) ∧
  TowerGen {n : ℕ // Even n} ∧
  ¬ TowerGen (Fin 17) ∧
  ¬ TowerGen (Fin 2) ∧
  ¬ TowerGen (Fin 0)

theorem bootstrap_tower_generation_core :
    Tagged StrengthTag.deltaOnly BootstrapTowerGenerationCoreSpec where
  holds :=
    ⟨towerGen_natDelta,
     towerGen_intDelta,
     towerGen_ratDelta,
     deltaForced_of_towerGen,
     natEmbedding_of_towerGen,
     infinite_of_towerGen,
     core_normalForm,
     fun h => by rcases h with ⟨e⟩; exact towerGen_of_natDelta_equiv e,
     towerGen_evenNat,
     not_towerGen_fin17,
     not_towerGen_fin2,
     not_towerGen_fin0⟩

theorem bootstrap_tower_generation_real_boundary :
    Tagged StrengthTag.classicalExtension (¬ TowerGen ℝ) where
  holds := not_towerGen_real

def BootstrapTowerGenerationSpec : Prop :=
  BootstrapTowerGenerationCoreSpec ∧ ¬ TowerGen ℝ

theorem bootstrap_tower_generation : BootstrapTowerGenerationSpec :=
  ⟨bootstrap_tower_generation_core.holds, not_towerGen_real⟩

#print axioms signedNatEquivInt
#print axioms fractionIntEquivRat
#print axioms core_normalForm
#print axioms towerGen_natDelta
#print axioms towerGen_intDelta
#print axioms towerGen_ratDelta
#print axioms deltaForced_of_towerGen
#print axioms natEmbedding_of_towerGen
#print axioms infinite_of_towerGen
#print axioms not_towerGen_fin17
#print axioms towerGen_of_natDelta_equiv
#print axioms equiv_invariant_predicate_contains_all_denumerable
#print axioms towerGen_evenNat
#print axioms bootstrap_tower_generation_core
#print axioms bootstrap_tower_generation_real_boundary
#print axioms bootstrap_tower_generation

end ActualMathematics.DeltaKernel.Bootstrap

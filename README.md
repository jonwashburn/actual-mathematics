# Actual Mathematics

A standalone Lean 4 formalization of the mathematics that is **forced by the act of
distinction**: the number tower, its order and arithmetic, a constructive continuum,
factorization, and a recognition cost, built up from one primitive and checked by the
compiler. Where a result is tagged choice-free, its `#print axioms` is a subset of
`{propext, Quot.sound}` — no `Classical.choice`.

This is the δ framework (Primitive Recognition Calculus) of
[Recognition Science](https://recognitionphysics.org), extracted into its own library so
the forced-mathematics core can be read, built, and cited on its own, independent of the
physics it was originally embedded in.

## The thesis

To specify a set `A` is to distinguish `A` from what is not `A`. Abstract that act and
call it `δ`. From the structure one iterated distinction generates, the ordinary objects
of mathematics appear not as chosen axioms but as **forced** constructions:

```
δ  ⟶  T (the free monoid on δ)  ⟶  ℕ (the natural-number object)
ℕ  ⟶  ℤ (group completion)  ⟶  ℚ (field of fractions)  ⟶  ℝ (constructive continuum)
```

Each step is a universal construction, so it is determined up to unique isomorphism: not
posited, forced. The interesting boundary is where the forcing **stops**. The forced side
is constructive (finite-information) mathematics. What classical analysis adds on top is a
small, named family of non-constructive principles (omniscience for decidable order, the
least-upper-bound / completeness axiom), and the library marks that boundary explicitly.
Mathematics is what distinction permits.

## What is here

- **The number tower** (`ActualMathematics/Orbit*`, `IntegerRational`, `IntegerOrder`):
  ℕ, ℤ, and ℚ built from traces of `δ`, with a decidable total order.
- **The ordered field of ℚ, choice-free** (`ActualMathematics/Grow/*`): the order and the
  ordered-field arithmetic laws on ℚ (reflexivity, totality, transitivity, trichotomy,
  additive and multiplicative monotonicity, `0 < 1`, positivity of products, reciprocal
  positivity, the multiplicative-inverse law), each derived and machine-checked with no
  `Classical.choice`. These were grown rung by rung above the base tower.
- **The constructive continuum** (`ActualMathematics/Real*`, `DeltaReal`, `GenerableReal`,
  the certified-analytic layer): the reals as Cauchy data over ℚ, and the analysis that
  the constructive side supports.
- **Factorization** (`ActualMathematics/Factorization/*`): the recognition account of
  integer factorization (period spectra, unit groups, coordinate charts).
- **The recognition cost** (`ActualMathematics/Cost/*`): the cost functional
  `J(x) = ½(x + 1/x) − 1` and its uniqueness theorem `law_of_logic_forces_jcost` (an
  Aczél-style functional-equation classification), the bridge from the ordered field to a
  metric.
- **The demarcation** (`ActualMathematics/DeltaForced`): the predicate `DeltaForced X :=
  Nonempty (X ↪ ℕ)` (a checkable countable certificate) and its ontological reading
  `PhysicallyReal`, with the headline split `demarcation`: ℕ, ℤ, ℚ are δ-forced (the
  forced conjuncts choice-free), ℝ is not. The forced realm is closed under product,
  subtype, and sum.
- **The omniscience calibration** (`ActualMathematics/Omniscience`): `LPO`, `WLPO`,
  `LLPO`, and Markov's principle stated over `ℕ → Bool`, with the choice-free hierarchy
  (`LPO ⇒ WLPO`, `LPO ⇒ LLPO`, `LPO ⇒ Markov`, `WLPO ∧ Markov ⇒ LPO`). These are the units
  in which the strength of a completeness posit is measured.
- **The continuum tax** (`ActualMathematics/ContinuumTax`, with `RealLineNonNativity` for
  the cardinality teeth): renormalization as accounting on the continuum purchase. A
  UV-divergent cutoff display carries no finite certificate; every renormalization scheme's
  counterterm is itself divergent while its residue is certified; two schemes differ by a
  finite (certified) amount; and the φ-forced measure makes the mode sum converge to
  `c·φ²` where the flat (continuum) weighting diverges.

## Build

Requires [`elan`](https://github.com/leanprover/elan) (the toolchain is pinned in
`lean-toolchain`).

```bash
lake exe cache get      # fetch the prebuilt Mathlib oleans for the pinned revision
lake build              # build the whole library
```

Build a single module, e.g. the ℚ ordered-field rungs:

```bash
lake build ActualMathematics.Grow.RatioOrbitMulRecip
```

## Honest status

- The forced tower (ℕ → ℤ → ℚ) and the `Grow/` ordered-field laws are proved choice-free
  (`#print axioms` ⊆ `{propext, Quot.sound}`). That is the literal sense in which they are
  forced, not assumed.
- `law_of_logic_forces_jcost` is a real uniqueness theorem (no project-local axioms).
- `demarcation` and `continuumTaxCert_holds` carry `Classical.choice` by design: their ℝ
  conjuncts use the classical uncountability of the continuum, a fact about the
  display-tier object, not about the forced side. The forced conjuncts (`forcedTower`) and
  the omniscience implications are choice-free, machine-verified by `#print axioms`.
- The forced-vs-posited demarcation is the research frontier: the forced side is the
  constructive continuum; the unforced part is the named family of completeness /
  omniscience principles. Some of those are stated here as independence results; the full
  classification is ongoing.

### Provenance of the two provider modules

`ActualMathematics/Constants.lean` and `ActualMathematics/MeasureForcing.lean` are
self-contained providers, not derivations. In the parent Recognition Science library the
golden ratio φ is forced by the self-similarity fixed point of the recognition cost, and
the per-rung weight `ρ = φ⁻¹` (with partition function `Z = φ²`) is the T9-forced measure;
both come with large dependency trees. `ContinuumTax` needs only φ's closed form and three
arithmetic facts (`φ > 1`, `φ² = φ + 1`, `1 − ρ = 1/φ²`), so these two modules give φ in
closed form `(1 + √5)/2` and prove exactly those facts from Mathlib alone. This keeps the
demarcation library self-contained; the forcing derivation of φ lives in the parent
library, not here.

## Papers

- J. Washburn, M. Zlatanović, *Distinction, Initiality, and Recognition Quotients* (draft).
- J. Washburn, M. Zlatanović, *Uniqueness of the Canonical Reciprocal Cost*, Mathematics
  **14**(6), 935 (2026).
- J. Washburn, M. Zlatanović, E. Allahyarov, *Recognition Geometry*, Axioms **15**(2), 90 (2026).

## Author

Jonathan Washburn, Recognition Physics Institute, Austin, Texas.
`jon@recognitionphysics.org`

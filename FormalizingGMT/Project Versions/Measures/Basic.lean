import Mathlib

open MeasureTheory MeasureTheory.OuterMeasure MeasureTheory.Measure Set Filter
open scoped ENNReal Topology Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

/- This file contains basic properties of outer measures that are frequently used in geometric
measure theory. -/

/-!
## Notions of regularity for outer measures
-/

/- **TODO (Nathan): Locally finite** outer measure: an outer measure on a topological space is locally
finite if it assigns finite measure to every compact set. -/

/- **Borel** outer measure: an outer measure `μ` on a topological space `X` equipped with the
Borel σ-algebra is a Borel outer measure if all Borel sets are measurable for `μ`. -/
def BorelOuterMeasure {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) : Prop :=
  ‹MeasurableSpace X› ≤ μ.caratheodory


/- **TODO: regular** outer measure: an outer measure `μ` on a space `X` is
regular if for every set `E`, there exists a `μ`-measurable set set `F ⊇ E` with `μ E = μ F`. -/

/-- **Borel regular** outer measure: an outer measure `μ` on a topological space `X`
equipped with the Borel σ-algebra is Borel regular if:
1. All Borel sets are Carathéodory measurable for `μ`.
2. For every set `E`, there exists a Borel set `F ⊇ E` with `μ E = μ F`. -/
def IsBorelRegular {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) : Prop :=
  ‹MeasurableSpace X› ≤ μ.caratheodory ∧
  ∀ E : Set X, ∃ F : Set X,
    MeasurableSet F ∧
    E ⊆ F ∧
    μ E = μ F

/-- **Radon** outer measure: an outer measure `μ` on a topological space `X` equipped with the
Borel σ-algebra is a Radon outer measure if:
1. All Borel subsets of `X` are Carathéodory measurable for `μ`.
2. The associated Borel measure via `toMeasure` satisfies `Measure.Regular`. -/
def IsRadon {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) : Prop :=
  IsBorelRegular μ ∧
  ∃ h : ‹MeasurableSpace X› ≤ μ.caratheodory, (μ.toMeasure h).Regular

/- **TODO (Nathan): Support** of a measure: let μ be an outer measure on a topological space X. The support
of μ is the set of points x ∈ X such that every neighborhood of x has positive μ-measure. -/


/-!
## Basic facts about regular outer measures
-/

/- **TODO** Lemma: If `μ` is a regular outer measure on a space `X` and
`A⊆X`, then `A` is `μ`-measurable if and only if `μ(A)+μ(X∖A)=μ(X)`.

Reference: Bogachev - Measure Theory I, Proposition -/

import Mathlib

open MeasureTheory MeasureTheory.OuterMeasure MeasureTheory.Measure Set Filter
open scoped ENNReal Topology Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

/- This file contains definitions for some of the basic types of measures needed in
   Geometric Measure Theory: Borel regular measures, Radon measures, and Hausdorff content. -/

/-
## Notions of regularity for measures-/

/-- An outer measure `μ` on a topological space `X` (equipped with the Borel σ-algebra) is
**Borel regular** if:
1. All Borel sets are Carathéodory measurable for `μ`.
2. For every set `E`, there exists a Borel set `F ⊇ E` with `μ(E) = μ(F)`. -/
def IsBorelRegular {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) : Prop :=
  ‹MeasurableSpace X› ≤ μ.caratheodory ∧
  ∀ (E : Set X), ∃ (F : Set X),
    MeasurableSet F ∧
    E ⊆ F ∧
    μ E = μ F

/-- An outer measure `μ` on a topological space `X` (equipped with the Borel σ-algebra) is a
**Radon measure** if:
1. All Borel subsets of `X` are Carathéodory measurable for `μ`.
2. The associated Borel measure (via `toMeasure`) satisfies `Measure.Regular`. -/
def IsRadon {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) : Prop :=
  (IsBorelRegular μ) ∧ ∃ (h : ‹MeasurableSpace X› ≤ μ.caratheodory), (μ.toMeasure h).Regular

/-!
## Hausdorff content
-/

/-- The `d`-dimensional **Hausdorff content** of a set `s` with covers of diameter ≤ `δ`. -/
noncomputable def hausdorffContent
    {X : Type*} [EMetricSpace X] (d : ℝ) (δ : ENNReal) (s : Set X) : ENNReal :=
  ⨅ (t : ℕ → Set X) (_ : s ⊆ ⋃ n, t n) (_ : ∀ n, Metric.ediam (t n) ≤ δ),
    ∑' n, ⨆ (_ : (t n).Nonempty), (Metric.ediam (t n)) ^ d

/-- Unrestricted Hausdorff content `H^s_∞(E)`: infimum over all countable covers,
with no diameter bound. -/
noncomputable def hausdorffContentInfty
    {X : Type*} [EMetricSpace X] (s : ℝ) (E : Set X) : ENNReal :=
  ⨅ (t : ℕ → Set X) (_ : E ⊆ ⋃ i, t i),
    ∑' i, (Metric.ediam (t i)) ^ s


/-- The notion of `s-set` as described in Falconer's textbook: a set `E` has positive, finite
`s`-dimensional Hausdorff measure and is Carathéodory-measurable with respect to the
`s`-dimensional Hausdorff outer measure. -/
def HasPositiveFiniteHausdorff
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (s : ℝ) (E : Set X) : Prop :=
  @MeasurableSet X (MeasureTheory.OuterMeasure.mkMetric (fun r => r ^ s)).caratheodory E ∧
    0 < MeasureTheory.Measure.hausdorffMeasure s E ∧
    MeasureTheory.Measure.hausdorffMeasure s E < ⊤



/-!
## Hausdorff measure is Borel regular
-/

/-- The `s`-dimensional Hausdorff outer measure on an `EMetricSpace` is Borel regular for any
`s ≥ 0`. That is:

1. All Borel sets are Carathéodory measurable (this follows from the Hausdorff outer measure
   being a *metric* outer measure).
2. For every set `E`, there exists a Borel set `F ⊇ E` with the same outer measure (this
   follows from `OuterMeasure.trim_mkMetric`, which shows that `mkMetric m` is its own trim).

Note: condition (2) actually holds for *all* `mkMetric m` without the `0 ≤ s` hypothesis,
but we include it to match the standard measure-theoretic statement. -/
theorem hausdorff_isBorelRegular {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (s : ℝ) (hs : 0 ≤ s) :
    IsBorelRegular (MeasureTheory.OuterMeasure.mkMetric (X := X) (fun r => r ^ s)) := by
  refine ⟨?_, ?_⟩
  · -- Property 1: Borel sets are Carathéodory measurable for any metric outer measure
    have : ‹MeasurableSpace X› = borel X := BorelSpace.measurable_eq
    rw [this]
    exact (MeasureTheory.OuterMeasure.mkMetric'_isMetric _).borel_le_caratheodory
  · -- Property 2: For every set E, there exists a Borel superset F with μ(E) = μ(F)
    intro E
    obtain ⟨F, hEF, hF_meas, hF_eq⟩ :=
      MeasureTheory.OuterMeasure.exists_measurable_superset_eq_trim
        (MeasureTheory.OuterMeasure.mkMetric (X := X) (fun r => r ^ s)) E
    exact ⟨F, hF_meas, hEF, by rw [hF_eq, MeasureTheory.OuterMeasure.trim_mkMetric]⟩

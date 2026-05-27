import Mathlib

import FormalizingGMT.«Project Versions».Measures.Basic
import FormalizingGMT.«Project Versions».Densities.Basic
import FormalizingGMT.«Project Versions».Aux_definitions

open scoped BigOperators Real Nat Classical Pointwise

open MeasureTheory MeasureTheory.OuterMeasure Set

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false


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




/-- If `s ≥ 0` is finite, the restriction of the `s`-dimensional Hausdorff outer measure to a
Carathéodory-measurable set of finite measure is a Radon measure.

This combines `hausdorff_isBorelRegular` (the Hausdorff outer measure is Borel regular)
with `IsBorelRegular.restrict_isRadon` (restricting a Borel regular outer measure to a
finite measurable set yields a Radon measure). -/
theorem hausdorff_restrict_isRadon
    {X : Type*} [MetricSpace X] [SigmaCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (s : ℝ) (hs : 0 ≤ s) (E : Set X)
    (hE_meas : (OuterMeasure.mkMetric (X := X) (fun r => r ^ s)).IsCaratheodory E)
    (hE_fin : (OuterMeasure.mkMetric (X := X) (fun r => r ^ s)) E < ⊤) :
    IsRadon (OuterMeasure.restrict E (OuterMeasure.mkMetric (X := X) (fun r => r ^ s))) := by
  exact IsBorelRegular.restrict_isRadon _ (hausdorff_isBorelRegular s hs) E hE_meas hE_fin

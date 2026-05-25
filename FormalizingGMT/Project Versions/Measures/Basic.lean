import Mathlib

open MeasureTheory MeasureTheory.OuterMeasure MeasureTheory.Measure Set Filter
open scoped ENNReal Topology Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

/- This file contains definitions for some of the basic types of measures needed in
   Geometric Measure Theory: Borel regular measures, Radon measures, and Hausdorff content. -/

/-- An outer measure `μ` on a topological space `X` (equipped with the Borel σ-algebra) is
**Borel regular** if:
1. All Borel sets are Carathéodory measurable for `μ`.
2. For every set `E`, there exists a Borel set `F ⊇ E` with `μ(E) = μ(F)`. -/
def IsBorelRegular {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) : Prop :=
  ‹MeasurableSpace X› ≤ μ.caratheodory ∧
  ∀ (E : Set X), ∃ (F : Set X), MeasurableSet F ∧ E ⊆ F ∧ μ E = μ F

/-- An outer measure `μ` on a topological space `X` (equipped with the Borel σ-algebra) is a
**Radon measure** if:
1. All Borel subsets of `X` are Carathéodory measurable for `μ`.
2. The associated Borel measure (via `toMeasure`) satisfies `Measure.Regular`. -/
def IsRadon {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) : Prop :=
  ∃ (h : ‹MeasurableSpace X› ≤ μ.caratheodory), (μ.toMeasure h).Regular

/-!
## Hausdorff content
-/

/-- The `d`-dimensional Hausdorff content of a set `s` with covers of diameter ≤ `δ`. -/
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

/-- `E` has positive, finite `s`-dimensional Hausdorff measure and is measurable. -/
def HasPositiveFiniteHausdorff
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (s : ℝ) (E : Set X) : Prop :=
  MeasurableSet E ∧
    0 < MeasureTheory.Measure.hausdorffMeasure s E ∧
    MeasureTheory.Measure.hausdorffMeasure s E < ⊤


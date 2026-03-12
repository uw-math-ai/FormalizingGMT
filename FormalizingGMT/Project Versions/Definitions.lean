
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic

open scoped BigOperators Real Nat Pointwise
open MeasureTheory MeasureTheory.Measure Metric Set Filter Topology ENNReal

variable {n : ℕ}

/-
Here are some appropriate definitions for Mathlib (probably)
-/

/-- The s-density ratio of a measure μ at point x with radius r:
    `μ(B̄(x, r)) / (2r) ^ s`. Intended for Radon measures. -/
noncomputable def dimensional_density_ratio
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (s : ℝ) (x : X) (r : ℝ) : ℝ≥0∞ :=
  μ (Metric.closedBall x r) / ENNReal.ofReal ((2 * r) ^ s)

/-- Upper s-density of μ at x:
    `limsup_{r → 0⁺} μ(B̄(x, r)) / (2r) ^ s`. -/
noncomputable def dimensional_upper_density
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (s : ℝ) (x : X) : ℝ≥0∞ :=
  Filter.limsup (dimensional_density_ratio μ s x) (𝓝[>] 0)

/-- Lower s-density of μ at x:
    `liminf_{r → 0⁺} μ(B̄(x, r)) / (2r) ^ s`. -/
noncomputable def dimensional_lower_density
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (s : ℝ) (x : X) : ℝ≥0∞ :=
  Filter.liminf (dimensional_density_ratio μ s x) (𝓝[>] 0)

/-- A measure is Radon if it is regular and Borel Measurable (which implies the rest of
    the conditions)--/
def IsRadon {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) : Prop :=
  μ.Regular

/-
The definitions below are for Hausdorff related things, potentially useful for Mathlib,
but maybe not. (We should check if they are in Mathlib/in a generalized form)
-/

/-- The s-dimensional Hausdorff content of `s` with covers of diameter ≤ `δ`. -/
noncomputable def hausdorffContent
    {X : Type*} [EMetricSpace X] (d : ℝ) (δ : ENNReal) (s : Set X) : ENNReal :=
  ⨅ (t : ℕ → Set X) (_ : s ⊆ ⋃ n, t n) (_ : ∀ n, EMetric.diam (t n) ≤ δ),
    ∑' n, ⨆ (_ : (t n).Nonempty), (EMetric.diam (t n)) ^ d

-- Unrestricted Hausdorff content H^s_∞(E): infimum over all countable covers, no diameter bound.
noncomputable def hausdorffContentInfty (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨅ (t : ℕ → Set (EuclideanSpace ℝ (Fin n))) (_ : E ⊆ ⋃ i, t i),
    ∑' i, (EMetric.diam (t i)) ^ s

/-- `E` has positive, finite s-dimensional Hausdorff measure and is measurable. -/
def HasPositiveFiniteHausdorff (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  MeasurableSet E ∧ 0 < hausdorffMeasure s E ∧ hausdorffMeasure s E < ⊤

/-- `E` has a density at `x` with respect to `hausdorffMeasure s` if the dimensional
    density ratio converges as `r → 0⁺`. -/
def has_density (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  ∃ y, Tendsto
    (fun r => dimensional_density_ratio ((hausdorffMeasure s).restrict E) s x r)
    (𝓝[>] 0) (𝓝 y)

/-
The definitions below are used in Lemma 3.3, but are not appropriate for Mathlib
-/

/-- The set of points in `E` where every cover of diameter at most `δ` satisfies
    the Hausdorff density bound controlled by `τ`. Used in the proof of Lemma 3.3. -/
def cover_set {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (δ : ℝ) (τ : ℝ) : Set X :=
  {x ∈ E | ∀ C, x ∈ C → EMetric.diam C ≤ ENNReal.ofReal δ →
    MeasureTheory.Measure.hausdorffMeasure s (C ∩ E) ≤ ENNReal.ofReal τ * (EMetric.diam C) ^ s}

/-- The limiting version of `cover_set`: union over all scales `δ = 1/(n+1)`. -/
def cover_limit_set {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (τ : ℝ) : Set X :=
  ⋃ n : ℕ, cover_set E s (1 / (n + 1)) τ

open Classical in
noncomputable def truncated_cover {X : Type*} [EMetricSpace X]
    (U : ℕ → Set X) (E : Set X) (x : X) (n : ℕ) : Set X :=
  if (U n ∩ E).Nonempty then U n else {x}

import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic

open scoped BigOperators Real Nat Pointwise
open MeasureTheory MeasureTheory.Measure Metric Set Filter Topology ENNReal

variable {n : ℕ}

-- Section 1: Definitions

/-
The s-density ratio of a measure μ at point x with radius r:
    `μ(B̄(x, r)) / (2r) ^ s`. Intended for Radon measures.
-/
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

/-
Lower s-density of μ at x:
    `liminf_{r → 0⁺} μ(B̄(x, r)) / (2r) ^ s`.
-/
noncomputable def dimensional_lower_density
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (s : ℝ) (x : X) : ℝ≥0∞ :=
  Filter.liminf (dimensional_density_ratio μ s x) (𝓝[>] 0)

/-
A measure is Radon if it is regular and Borel Measurable.
-/
def IsRadon {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) : Prop :=
  μ.Regular

/- The s-dimensional density of μ at x exists if the density ratio converges as r → 0⁺. -/
def has_density
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (s : ℝ) (x : X) : Prop :=
  ∃ y, Tendsto (dimensional_density_ratio μ s x) (𝓝[>] 0) (𝓝 y)

-- Section 2: Basic facts
-- (proofs of comparison, non-negativity, and existence from lower/upper densities are TODO)

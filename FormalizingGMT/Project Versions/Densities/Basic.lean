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
    (μ : OuterMeasure X) (s : ℝ) (x : X) (r : ℝ) : ℝ≥0∞ :=
  μ (Metric.closedBall x r) / ENNReal.ofReal ((2 * r) ^ s)

/-- Upper s-density of μ at x:
    `limsup_{r → 0⁺} μ(B̄(x, r)) / (2r) ^ s`. -/
noncomputable def dimensional_upper_density
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) : ℝ≥0∞ :=
  Filter.limsup (dimensional_density_ratio μ s x) (𝓝[>] 0)

/-
Lower s-density of μ at x:
    `liminf_{r → 0⁺} μ(B̄(x, r)) / (2r) ^ s`.
-/
noncomputable def dimensional_lower_density
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) : ℝ≥0∞ :=
  Filter.liminf (dimensional_density_ratio μ s x) (𝓝[>] 0)




/- The s-dimensional density of μ at x exists if the density ratio converges as r → 0⁺. -/
def has_density
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) : Prop :=
  ∃ y, Tendsto (dimensional_density_ratio μ s x) (𝓝[>] 0) (𝓝 y)



-- Section 2: Basic facts

/-- Comparison between lower and upper density: Θ_*^s(μ, x) ≤ Θ^{*s}(μ, x). -/
lemma lower_le_upper_density
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) :
    dimensional_lower_density μ s x ≤ dimensional_upper_density μ s x :=
  Filter.liminf_le_limsup
    (⟨⊤, by simp⟩)
    (⟨0, Filter.eventually_map.2 <| Filter.eventually_of_mem self_mem_nhdsWithin
      fun _ _ => zero_le⟩)

/-- Non-negativity of lower density: 0 ≤ Θ_*^s(μ, x). -/
lemma lower_density_nonneg
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) :
    0 ≤ dimensional_lower_density μ s x :=
  zero_le

/-- Non-negativity of upper density: 0 ≤ Θ^{*s}(μ, x). -/
lemma upper_density_nonneg
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) :
    0 ≤ dimensional_upper_density μ s x :=
  zero_le

/-- If the lower and upper densities are equal, then the density limit exists.

Uses `tendsto_of_liminf_eq_limsup` from Mathlib, which directly gives convergence
when `liminf = limsup` in a conditionally complete linear order with order topology
(which `ℝ≥0∞` satisfies). -/
lemma density_exists_of_lower_eq_upper
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X)
    (h : dimensional_lower_density μ s x = dimensional_upper_density μ s x) :
    has_density μ s x :=
  ⟨_, tendsto_of_liminf_eq_limsup rfl h.symm⟩

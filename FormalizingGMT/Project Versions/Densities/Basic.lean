import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

open scoped BigOperators Real Nat Pointwise
open MeasureTheory MeasureTheory.Measure Metric Set Filter Topology ENNReal

variable {n : ℕ}

-- Section 1: Definitions

/-- The s-density ratio of a measure μ at point x with radius r:
    `μ(B̄(x, r)) / (2r) ^ s`. Intended for Radon measures. -/
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

/-- Lower s-density of μ at x:
    `liminf_{r → 0⁺} μ(B̄(x, r)) / (2r) ^ s`. -/
noncomputable def dimensional_lower_density
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) : ℝ≥0∞ :=
  Filter.liminf (dimensional_density_ratio μ s x) (𝓝[>] 0)

/-- The s-dimensional density of μ at x exists if the density ratio converges as r → 0⁺. -/
class HasDensity
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) : Prop where
  exists_tendsto : ∃ y, Tendsto (dimensional_density_ratio μ s x) (𝓝[>] 0) (𝓝 y)

/-- The s-dimensional density of μ at x (Definition 1.5).

When the limit exists (`has_density μ s x`), this equals
`lim_{r → 0⁺} μ(B̄(x, r)) / (2r) ^ s`.
When the limit does not exist, this returns a junk value. -/
noncomputable def dimensional_density
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) : ℝ≥0∞ :=
  Filter.limUnder (𝓝[>] (0 : ℝ)) (dimensional_density_ratio μ s x)

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

/-- Lemma 2.4: If Θ_*^s(μ, x) ≥ α, then Θ^{*s}(μ, x) ≥ α. -/
lemma upper_density_ge_of_lower_density_ge
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) (α : ℝ≥0∞)
    (h : α ≤ dimensional_lower_density μ s x) :
    α ≤ dimensional_upper_density μ s x :=
  h.trans (lower_le_upper_density μ s x)

/-- Lemma 2.5: If Θ^{*s}(μ, x) ≤ α, then Θ_*^s(μ, x) ≤ α. -/
lemma lower_density_le_of_upper_density_le
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) (α : ℝ≥0∞)
    (h : dimensional_upper_density μ s x ≤ α) :
    dimensional_lower_density μ s x ≤ α :=
  (lower_le_upper_density μ s x).trans h

/-- Lemma 2.6: If Θ_*^s(μ, x) > α, then eventually (for small enough r > 0)
    the density ratio is > α. -/
lemma eventually_gt_of_lower_density_gt
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) (α : ℝ≥0∞)
    (h : α < dimensional_lower_density μ s x) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), α < dimensional_density_ratio μ s x r :=
  Filter.eventually_lt_of_lt_liminf h

/-- Lemma 2.7: If Θ^{*s}(μ, x) < α, then eventually (for small enough r > 0)
    the density ratio is < α. -/
lemma eventually_lt_of_upper_density_lt
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) (α : ℝ≥0∞)
    (h : dimensional_upper_density μ s x < α) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), dimensional_density_ratio μ s x r < α :=
  Filter.eventually_lt_of_limsup_lt h

/-- Lemma 2.8: If Θ_*^s(μ, x) < α, then frequently (along r → 0⁺)
    the density ratio is < α. -/
lemma frequently_lt_of_lower_density_lt
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) (α : ℝ≥0∞)
    (h : dimensional_lower_density μ s x < α) :
    ∃ᶠ r in 𝓝[>] (0 : ℝ), dimensional_density_ratio μ s x r < α :=
  Filter.frequently_lt_of_liminf_lt ⟨⊤, fun _ _ => le_top⟩ h

/-- Lemma 2.9: If Θ^{*s}(μ, x) > α, then frequently (along r → 0⁺)
    the density ratio is > α. -/
lemma frequently_gt_of_upper_density_gt
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) (α : ℝ≥0∞)
    (h : α < dimensional_upper_density μ s x) :
    ∃ᶠ r in 𝓝[>] (0 : ℝ), α < dimensional_density_ratio μ s x r :=
  Filter.frequently_lt_of_lt_limsup ⟨0, fun _ _ => zero_le⟩ h

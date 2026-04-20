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

/-- Comparison between lower and upper density: Θ_*^s(μ, x) ≤ Θ^{*s}(μ, x). -/
lemma lower_le_upper_density
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (s : ℝ) (x : X) :
    dimensional_lower_density μ s x ≤ dimensional_upper_density μ s x := by
  apply_rules [Filter.liminf_le_limsup]
  · exact ⟨⊤, by simp⟩
  · exact ⟨0, Filter.eventually_map.2 <| Filter.eventually_of_mem self_mem_nhdsWithin
      fun r hr => zero_le _⟩

/-- Non-negativity of lower density: 0 ≤ Θ_*^s(μ, x). -/
lemma lower_density_nonneg
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (s : ℝ) (x : X) :
    0 ≤ dimensional_lower_density μ s x :=
  zero_le _

/-- Non-negativity of upper density: 0 ≤ Θ^{*s}(μ, x). -/
lemma upper_density_nonneg
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (s : ℝ) (x : X) :
    0 ≤ dimensional_upper_density μ s x :=
  zero_le _

/-- If the lower and upper densities are equal, then the density limit exists. -/
lemma density_exists_of_lower_eq_upper
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (s : ℝ) (x : X)
    (h : dimensional_lower_density μ s x = dimensional_upper_density μ s x) :
    has_density μ s x := by
  refine ⟨dimensional_lower_density μ s x, ?_⟩
  have h_lim_aux : Filter.limsup (dimensional_density_ratio μ s x) (𝓝[>] 0) =
      dimensional_lower_density μ s x := h.symm
  refine' tendsto_order.2 ⟨_, _⟩
  · intro a' ha'
    contrapose! ha'
    refine' csSup_le _ _
    · refine' ⟨0, _⟩; norm_num
    · intro b hb
      exact le_of_not_gt fun hba => ha' <| by
        filter_upwards [hb] with r hr using not_le_of_gt <| lt_of_lt_of_le hba hr
  · intro a ha
    contrapose! ha
    rw [← h_lim_aux]
    refine' le_csInf _ _ <;> norm_num
    · refine' ⟨⊤, _⟩; norm_num
    · intro b hb
      exact le_of_not_gt fun hb' => ha <| by
        filter_upwards [hb] with r hr
        exact not_le_of_gt <| lt_of_le_of_lt hr hb'

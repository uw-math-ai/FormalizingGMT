import Mathlib.Analysis.SpecialFunctions.Pow.Real 
import Mathlib.Topology.Algebra.Order.LiminfLimsup 
import Mathlib.Topology.MetricSpace.Basic       
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic

open scoped Real Topology
open Metric Set Filter ENNReal MeasureTheory

noncomputable def dimensional_density_ratio
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) (r : ℝ) : ℝ≥0∞ :=
  μ (Metric.closedBall x r) / ENNReal.ofReal ((2 * r) ^ s)

noncomputable def dimensional_upper_density
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) : ℝ≥0∞ :=
  Filter.limsup (dimensional_density_ratio μ s x) (𝓝[>] 0)

noncomputable def dimensional_lower_density
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) : ℝ≥0∞ :=
  Filter.liminf (dimensional_density_ratio μ s x) (𝓝[>] 0)

class HasDensity
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) : Prop where
  exists_tendsto : ∃ y, Tendsto (dimensional_density_ratio μ s x) (𝓝[>] 0) (𝓝 y)

noncomputable def dimensional_density
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) : ℝ≥0∞ :=
  Filter.limUnder (𝓝[>] (0 : ℝ)) (dimensional_density_ratio μ s x)

  lemma lower_le_upper_density
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) :
    dimensional_lower_density μ s x ≤ dimensional_upper_density μ s x :=
  Filter.liminf_le_limsup
    (⟨⊤, by simp⟩)
    (⟨0, Filter.eventually_map.2 <| Filter.eventually_of_mem self_mem_nhdsWithin
      fun _ _ => zero_le⟩)

lemma lower_density_nonneg
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) :
    0 ≤ dimensional_lower_density μ s x :=
  zero_le

lemma upper_density_nonneg
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) :
    0 ≤ dimensional_upper_density μ s x :=
  zero_le

lemma density_exists_of_lower_eq_upper
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X)
    (h : dimensional_lower_density μ s x = dimensional_upper_density μ s x) :
    HasDensity μ s x :=
  ⟨_, tendsto_of_liminf_eq_limsup rfl h.symm⟩

lemma upper_density_ge_of_lower_density_ge
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) (α : ℝ≥0∞)
    (h : α ≤ dimensional_lower_density μ s x) :
    α ≤ dimensional_upper_density μ s x :=
  h.trans (lower_le_upper_density μ s x)

lemma lower_density_le_of_upper_density_le
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) (α : ℝ≥0∞)
    (h : dimensional_upper_density μ s x ≤ α) :
    dimensional_lower_density μ s x ≤ α :=
  (lower_le_upper_density μ s x).trans h

lemma eventually_gt_of_lower_density_gt
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) (α : ℝ≥0∞)
    (h : α < dimensional_lower_density μ s x) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), α < dimensional_density_ratio μ s x r :=
  Filter.eventually_lt_of_lt_liminf h

lemma eventually_lt_of_upper_density_lt
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) (α : ℝ≥0∞)
    (h : dimensional_upper_density μ s x < α) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), dimensional_density_ratio μ s x r < α :=
  Filter.eventually_lt_of_limsup_lt h

lemma frequently_lt_of_lower_density_lt
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) (α : ℝ≥0∞)
    (h : dimensional_lower_density μ s x < α) :
    ∃ᶠ r in 𝓝[>] (0 : ℝ), dimensional_density_ratio μ s x r < α :=
  Filter.frequently_lt_of_liminf_lt ⟨⊤, fun _ _ => le_top⟩ h

lemma frequently_gt_of_upper_density_gt
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) (s : ℝ) (x : X) (α : ℝ≥0∞)
    (h : α < dimensional_upper_density μ s x) :
    ∃ᶠ r in 𝓝[>] (0 : ℝ), α < dimensional_density_ratio μ s x r :=
  Filter.frequently_lt_of_lt_limsup ⟨0, fun _ _ => zero_le⟩ h

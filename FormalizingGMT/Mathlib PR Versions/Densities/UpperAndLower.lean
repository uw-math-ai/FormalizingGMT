import Mathlib.Analysis.SpecialFunctions.Pow.Real 
import Mathlib.Topology.Algebra.Order.LiminfLimsup 
import Mathlib.Topology.MetricSpace.Basic       
import Mathlib.MeasureTheory.Measure.OuterMeasure 
import Mathlib.MeasureTheory.Constructions.BorelSpace
import Mathlib.Tactic

open scoped Real Topology
open Metric Set Filter ENNReal

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

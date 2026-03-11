
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
Radon measures (Mattila, Definition 1.5(4)):
A measure μ is Radon if it satisfies all three conditions:
  (i)   μ(K) < ∞ for every compact set K,
  (ii)  μ(V) = sup{μ(K) : K ⊆ V compact} for every open set V,
  (iii) μ(A) = inf{μ(V) : A ⊆ V open}  for every set A.

In Mathlib, `Measure.Regular` encodes exactly these three properties:
  - extends `IsFiniteMeasureOnCompacts`  (condition i)
  - extends `OuterRegular`              (condition iii)
  - has `innerRegular : μ.InnerRegularWRT IsCompact IsOpen` (condition ii)
-/
-- `Measure.Regular` in Mathlib directly encodes all three Radon conditions
-- (finite on compacts, outer regular, inner regular on opens by compacts),
-- so no separate `IsRadon` definition is needed; use `μ.Regular` throughout.

-- I think we should double check above...




/-
Below we have the definitions that are used in our proofs.
We would like to keep this to the level of Mathlib Definitions and
generality, but this will take some work.
-/

-- From Lemma3.3 File

/-- The set of points in `E` where every cover of diameter at most `δ` satisfies
    the Hausdorff density bound controlled by `τ`. Used in the proof of Lemma 3.3. -/
def cover_set {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (δ : ℝ) (τ : ℝ) : Set X :=
  {x ∈ E | ∀ C, x ∈ C → EMetric.diam C ≤ ENNReal.ofReal δ →
    MeasureTheory.Measure.hausdorffMeasure s (C ∩ E) ≤ ENNReal.ofReal τ * (EMetric.diam C) ^ s}

noncomputable def hausdorffContent
    {X : Type*} [EMetricSpace X] (d : ℝ) (δ : ENNReal) (s : Set X) : ENNReal :=
  ⨅ (t : ℕ → Set X) (_ : s ⊆ ⋃ n, t n) (_ : ∀ n, EMetric.diam (t n) ≤ δ),
    ∑' n, ⨆ (_ : (t n).Nonempty), (EMetric.diam (t n)) ^ d

open Classical in
noncomputable def truncated_cover {X : Type*} [EMetricSpace X]
    (U : ℕ → Set X) (E : Set X) (x : X) (n : ℕ) : Set X :=
  if (U n ∩ E).Nonempty then U n else {x}

/-- The limiting version of `cover_set`: union over all scales `δ = 1/(n+1)`. -/
def cover_limit_set {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (τ : ℝ) : Set X :=
  ⋃ n : ℕ, cover_set E s (1 / (n + 1)) τ

-- From Definitions File
/-- `E` has positive, finite s-dimensional Hausdorff measure and is measurable. -/
def HasPositiveFiniteHausdorff (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  MeasurableSet E ∧ 0 < hausdorffMeasure s E ∧ hausdorffMeasure s E < ⊤

/-- `E` has a density at `x` with respect to `hausdorffMeasure s` if the dimensional
    density ratio converges as `r → 0⁺`. -/
def has_density (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) :
Prop :=
  ∃ y, Tendsto (fun r => dimensional_density_ratio (hausdorffMeasure s) E x r) (𝓝[>] 0) (𝓝 y)

-- Unrestricted Hausdorff content H^s_∞(E): infimum over all countable covers, no diameter bound.
noncomputable def hausdorffContentInfty (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨅ (t : ℕ → Set (EuclideanSpace ℝ (Fin n))) (_ : E ⊆ ⋃ i, t i),
    ∑' i, (EMetric.diam (t i)) ^ s

/-
s-density for a Radon measure μ (Mattila, §6).
Convention: closed balls, denominator r^s (radius convention).
  - muDensityRatio μ s x r  = μ(B̄(x,r)) / r^s
  - upperMuDensity μ s x    = limsup_{r→0⁺} μ(B̄(x,r)) / r^s
  - lowerMuDensity μ s x    = liminf_{r→0⁺} μ(B̄(x,r)) / r^s
These are stated for a general metric space with a Borel σ-algebra;
μ is intended to be a Radon measure (i.e. μ.Regular holds).
-/

/-- The s-density ratio of a measure μ at point x with radius r:
    `μ(B̄(x, r)) / r ^ s`. Intended for Radon measures. -/
noncomputable def dimensional_density_ratio
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (s : ℝ) (x : X) (r : ℝ) : ℝ≥0∞ :=
  μ (Metric.closedBall x r) / ENNReal.ofReal ((2 * r) ^ s)

/-- Upper s-density of μ at x:
    `limsup_{r → 0⁺} μ(B̄(x, r)) / r ^ s`. -/
noncomputable def upper_dimensional_density
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (s : ℝ) (x : X) : ℝ≥0∞ :=
  Filter.limsup (dimensional_density_ratio μ s x) (𝓝[>] 0)

/-- Lower s-density of μ at x:
    `liminf_{r → 0⁺} μ(B̄(x, r)) / r ^ s`. -/
noncomputable def lower_dimensional_density
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (s : ℝ) (x : X) : ℝ≥0∞ :=
  Filter.liminf (dimensional_density_ratio μ s x) (𝓝[>] 0)

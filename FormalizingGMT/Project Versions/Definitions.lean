import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic
import FormalizingGMT.«Project Versions».Densities.Basic

open scoped BigOperators Real Nat Pointwise
open MeasureTheory MeasureTheory.Measure Metric Set Filter Topology ENNReal

variable {n : ℕ}

/-
Here are some appropriate definitions for Mathlib (probably)
-/

-- dimensional_density_ratio, dimensional_upper_density, dimensional_lower_density, IsRadon
-- are defined in Densities/Basic.lean and re-exported here via the import above.

/-
The definitions below are for Hausdorff related things, potentially useful for Mathlib,
but maybe not. (We should check if they are in Mathlib/in a generalized form)
-/

/- The s-dimensional Hausdorff content of `s` with covers of diameter ≤ `δ`. -/
noncomputable def hausdorffContent
    {X : Type*} [EMetricSpace X] (d : ℝ) (δ : ENNReal) (s : Set X) : ENNReal :=
  ⨅ (t : ℕ → Set X) (_ : s ⊆ ⋃ n, t n) (_ : ∀ n, EMetric.diam (t n) ≤ δ),
    ∑' n, ⨆ (_ : (t n).Nonempty), (EMetric.diam (t n)) ^ d

-- Unrestricted Hausdorff content H^s_∞(E): infimum over all countable covers, no diameter bound.
noncomputable def hausdorffContentInfty (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨅ (t : ℕ → Set (EuclideanSpace ℝ (Fin n))) (_ : E ⊆ ⋃ i, t i),
    ∑' i, (EMetric.diam (t i)) ^ s

/- `E` has positive, finite s-dimensional Hausdorff measure and is measurable. -/
def HasPositiveFiniteHausdorff (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  MeasurableSet E ∧ 0 < hausdorffMeasure s E ∧ hausdorffMeasure s E < ⊤

-- has_density is defined (more generally, for any measure μ) in Densities/Basic.lean.
-- The special case for hausdorffMeasure is: has_density ((hausdorffMeasure s).restrict E) s x

/-
The definitions below are used in Lemma 3.3, but are not appropriate for Mathlib
-/

/-
The set of points in `E` where every cover of diameter at most `δ` satisfies
the Hausdorff density bound controlled by `τ`. Used in the proof of Lemma 3.3.
-/
def cover_set {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (δ : ℝ) (τ : ℝ) : Set X :=
  {x ∈ E | ∀ C, x ∈ C → EMetric.diam C ≤ ENNReal.ofReal δ →
    MeasureTheory.Measure.hausdorffMeasure s (C ∩ E) ≤ ENNReal.ofReal τ * (EMetric.diam C) ^ s}

/-
The limiting version of `cover_set`: union over all scales `δ = 1/(n+1)`.
-/
def cover_limit_set {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (τ : ℝ) : Set X :=
  ⋃ n : ℕ, cover_set E s (1 / (n + 1)) τ

open Classical in
noncomputable def truncated_cover {X : Type*} [EMetricSpace X]
    (U : ℕ → Set X) (E : Set X) (x : X) (n : ℕ) : Set X :=
  if (U n ∩ E).Nonempty then U n else {x}

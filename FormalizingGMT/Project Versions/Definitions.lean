
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
/-- A Radon measure in the sense of Mattila: finite on compact sets,
    outer regular on all sets, and inner regular on open sets by compact sets.
    This is exactly `Measure.Regular` in Mathlib. -/
def IsRadon {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) : Prop :=
  μ.Regular

theorem isRadon_iff_regular {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) : IsRadon μ ↔ μ.Regular :=
  Iff.rfl

/-
Below we have the definitions that are used in our proofs.
We would like to keep this to the level of Mathlib Definitions and
generality, but this will take some work.
-/

-- From Lemma3.3 File

def E_delta_tau {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (δ : ℝ) (τ : ℝ) : Set X :=
  {x ∈ E | ∀ C, x ∈ C → EMetric.diam C ≤ ENNReal.ofReal δ →
    MeasureTheory.Measure.hausdorffMeasure s (C ∩ E) ≤ ENNReal.ofReal τ * (EMetric.diam C) ^ s}

noncomputable def hausdorffContent
    {X : Type*} [EMetricSpace X] (d : ℝ) (δ : ENNReal) (s : Set X) : ENNReal :=
  ⨅ (t : ℕ → Set X) (_ : s ⊆ ⋃ n, t n) (_ : ∀ n, EMetric.diam (t n) ≤ δ),
    ∑' n, ⨆ (_ : (t n).Nonempty), (EMetric.diam (t n)) ^ d

open Classical in
noncomputable def modified_cover {X : Type*} [EMetricSpace X]
    (U : ℕ → Set X) (E : Set X) (x : X) (n : ℕ) : Set X :=
  if (U n ∩ E).Nonempty then U n else {x}

def E_star_tau {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (τ : ℝ) : Set X :=
  ⋃ n : ℕ, E_delta_tau E s (1 / (n + 1)) τ

-- GMT convention: density uses closed balls B̄(x, r) = {y | d(x,y) ≤ r}
noncomputable def density_ratio
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (x : X) (r : ℝ) : ENNReal :=
  MeasureTheory.Measure.hausdorffMeasure s
      (E ∩ EMetric.closedBall x (ENNReal.ofReal r)) /
    (ENNReal.ofReal (2 * r)) ^ s

noncomputable def upper_density
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (x : X) : ENNReal :=
  Filter.limsup (fun r => density_ratio E s x r) (nhdsWithin 0 (Set.Ioi 0))

def bad_set
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) : Set X :=
  {x ∈ E | upper_density E s x < ENNReal.ofReal (1 / (2 : ℝ) ^ s)}


-- From Definitions File
def IsSSet (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  MeasurableSet E ∧ 0 < hausdorffMeasure s E ∧ hausdorffMeasure s E < ⊤

-- GMT convention: density uses closed balls B̄(x, r) = {y | d(x,y) ≤ r}
noncomputable def densityRatio (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) : ℝ≥0∞ :=
  hausdorffMeasure s (E ∩ closedBall x r) / (ENNReal.ofReal ((2 * r) ^ s))

noncomputable def Ds (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  liminf (densityRatio s E x) (𝓝[>] 0)

def HasDs (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ y, Tendsto (densityRatio s E x) (𝓝[>] 0) (𝓝 y) ∧ Ds s E x = y

-- Unrestricted Hausdorff content H^s_∞(E): infimum over all countable covers, no diameter bound.
noncomputable def hausdorffContentInfty (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨅ (t : ℕ → Set (EuclideanSpace ℝ (Fin n))) (_ : E ⊆ ⋃ i, t i),
    ∑' i, (EMetric.diam (t i)) ^ s

noncomputable def upperDs (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  limsup (densityRatio s E x) (𝓝[>] 0)

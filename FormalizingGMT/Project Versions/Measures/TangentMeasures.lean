import FormalizingGMT.«Project Versions».Measures.WeakConvergence

open MeasureTheory
open Topology

variable {n : ℕ}

/--
The blow-up map `T_{a,r}(x) = (x - a) / r` on Euclidean space `ℝⁿ`.
-/
def blowUpMap {n : ℕ}
    (a : EuclideanSpace ℝ (Fin n))
    (r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  r⁻¹ • (x - a)

/-- `IsTangentMeasure μ ν a` asserts that `ν` is a tangent measure of `μ` at point `a`. -/
def IsTangentMeasure
    (μ ν : OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : RadonOuterMeasure μ)
    (a : EuclideanSpace ℝ (Fin n)) : Prop :=
  RadonOuterMeasure ν ∧ ν ≠ 0 ∧
  ∃ (r : ℕ → ℝ) (c : ℕ → ℝ),
    (∀ i, 0 < r i) ∧
    (∀ i, 0 < c i) ∧
    Filter.Tendsto r Filter.atTop (𝓝 0) ∧
    ∃ (h_seq : ∀ i,
        RadonOuterMeasure
          (c i • (μ.map (blowUpMap a (r i))))),
      OuterMeasure.WeaklyConverges
        (fun i ↦ c i • (μ.map (blowUpMap a (r i))))
        ν
        h_seq
        ‹RadonOuterMeasure ν›
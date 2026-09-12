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
/-- Theorem 14.3 -/
theorem exists_subseq_blowUp_weaklyConverges_tangentMeasure
    (μ : OuterMeasure (EuclideanSpace ℝ (Fin n))) (hμ : RadonOuterMeasure μ)
    (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ SupportOuterMeasure μ)
    (hc : limsup (fun ρ : ℝ ↦ μ (ball a (2 * ρ)) / μ (ball a ρ)) (𝓝[>] (0 : ℝ)) < ∞)
    (r : ℕ → ℝ) (hr_pos : ∀ i, 0 < r i) (hr : Tendsto r atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ) (ν : OuterMeasure (EuclideanSpace ℝ (Fin n)))
        (hseq : ∀ j, RadonOuterMeasure
          ((μ (ball a (r (φ j))))⁻¹ • μ.map (blowUpMap a (r (φ j)))))
        (hν : RadonOuterMeasure ν),
      StrictMono φ ∧ IsTangentMeasure μ ν hμ a ∧
        OuterMeasure.WeaklyConverges
          (fun j ↦ (μ (ball a (r (φ j))))⁻¹ • μ.map (blowUpMap a (r (φ j)))) ν hseq hν

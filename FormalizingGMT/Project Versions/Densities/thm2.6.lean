import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Covering.Besicovitch

open Set Metric Filter
open MeasureTheory MeasureTheory.Measure
open scoped Topology

section DensityAtPointsNotInE

variable {n : ℕ} {s : ℝ}

noncomputable abbrev μHs (s : ℝ) : Measure (Fin n → ℝ) :=
  hausdorffMeasure (X := Fin n → ℝ) s

/--
Given convergence to `E.indicator 1 x`, points in `Eᶜ` give convergence to `0`.
This packages the only step needed to pass from the measurable-set density theorem
to the outside-of-`E` density conclusion.
-/
lemma tendsto_zero_of_tendsto_indicator_one
  {E : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hx : x ∈ Eᶜ)
    (hlim : Tendsto (fun r => (μHs (n := n) s) (E ∩ closedBall x r) /
      (μHs (n := n) s) (closedBall x r)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 (E.indicator (fun _ => (1 : ENNReal)) x))) :
    Tendsto (fun r => (μHs (n := n) s) (E ∩ closedBall x r) /
      (μHs (n := n) s) (closedBall x r)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (𝓝 (0 : ENNReal)) := by
  have hx' : x ∉ E := by simpa [Set.mem_compl] using hx
  have hix : E.indicator (fun _ => (1 : ENNReal)) x = 0 := by
    simp [hx']
  simpa [hix] using hlim

/--
Theorem 2.6 (density at points not in `E`): for a measurable set `E` of finite
`s`-dimensional Hausdorff measure, the density ratio with respect to Hausdorff measure
is `0` for `H^s`-a.e. point in `Eᶜ`.

Formal denominator: `(hausdorffMeasure s) (closedBall x r)`.
-/
theorem theorem2_6_densityAtPointsNotInE
  {E : Set (Fin n → ℝ)} (hE_meas : MeasurableSet E)
  [IsLocallyFiniteMeasure (μHs (n := n) s)]
  [HasBesicovitchCovering (Fin n → ℝ)]
    (_hE_finite : (μHs (n := n) s) E < ⊤) :
    ∀ᵐ x ∂(μHs (n := n) s).restrict Eᶜ,
      Tendsto (fun r => (μHs (n := n) s) (E ∩ closedBall x r) /
        (μHs (n := n) s) (closedBall x r)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (0 : ENNReal)) := by
  have h_density : ∀ᵐ x ∂(μHs (n := n) s),
      Tendsto (fun r => (μHs (n := n) s) (E ∩ closedBall x r) /
        (μHs (n := n) s) (closedBall x r)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (E.indicator (fun _ => (1 : ENNReal)) x)) :=
    Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet
      (μ := μHs (n := n) s) hE_meas
  have h_density_restrict : ∀ᵐ x ∂(μHs (n := n) s).restrict Eᶜ,
      Tendsto (fun r => (μHs (n := n) s) (E ∩ closedBall x r) /
        (μHs (n := n) s) (closedBall x r)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (E.indicator (fun _ => (1 : ENNReal)) x)) :=
    ae_restrict_of_ae h_density
  have h_mem_compl : ∀ᵐ x ∂(μHs (n := n) s).restrict Eᶜ, x ∈ Eᶜ :=
    ae_restrict_mem hE_meas.compl
  filter_upwards [h_density_restrict, h_mem_compl] with x hxlim hxcompl
  exact tendsto_zero_of_tendsto_indicator_one (s := s) hxcompl hxlim

end DensityAtPointsNotInE

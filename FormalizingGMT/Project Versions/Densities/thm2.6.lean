import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import FormalizingGMT.«Project Versions».Definitions

open Set Metric Filter
open MeasureTheory MeasureTheory.Measure
open scoped Topology

section DensityAtPointsNotInE

variable {n : ℕ} {s : ℝ}

-- Maybe use instance here (try to use instances to proof golf)

lemma isLocallyFiniteMeasure_of_closedBall_formula
  {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] (μ : Measure α)
    (hball : ∀ x : α,
      ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        μ (closedBall x r) = ENNReal.ofReal ((2 * r) ^ s)) :
    IsLocallyFiniteMeasure μ := by
  refine ⟨fun x => ?_⟩
  have h_event : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      μ (closedBall x r) = ENNReal.ofReal ((2 * r) ^ s) ∧ 0 < r := by
    filter_upwards [hball x, self_mem_nhdsWithin] with r hr hpos
    exact ⟨hr, hpos⟩
  rcases Filter.Eventually.exists h_event with ⟨r, hr, hrpos⟩
  refine ⟨closedBall x r, Metric.closedBall_mem_nhds x hrpos, ?_⟩
  rw [hr]
  exact ENNReal.ofReal_lt_top

lemma ae_tendsto_inter_closedBall_div_zero_on_compl
    {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
    [SecondCountableTopology α] [HasBesicovitchCovering α]
    (μ : Measure α) [IsLocallyFiniteMeasure μ] {E : Set α}
    (hE_meas : MeasurableSet E) :
    ∀ᵐ x ∂μ.restrict Eᶜ,
      Tendsto (fun r => μ (E ∩ closedBall x r) / μ (closedBall x r))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (0 : ENNReal)) := by
  have h_density : ∀ᵐ x ∂μ,
      Tendsto (fun r => μ (E ∩ closedBall x r) / μ (closedBall x r))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (E.indicator (fun _ => (1 : ENNReal)) x)) :=
    Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet (μ := μ) hE_meas
  have h_density_restrict : ∀ᵐ x ∂μ.restrict Eᶜ,
      Tendsto (fun r => μ (E ∩ closedBall x r) / μ (closedBall x r))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (E.indicator (fun _ => (1 : ENNReal)) x)) :=
    ae_restrict_of_ae h_density
  have h_mem_compl : ∀ᵐ x ∂μ.restrict Eᶜ, x ∈ Eᶜ :=
    ae_restrict_mem hE_meas.compl
  filter_upwards [h_density_restrict, h_mem_compl] with x hxlim hxcompl
  have hxnot : x ∉ E := by simpa [Set.mem_compl] using hxcompl
  have hix : E.indicator (fun _ => (1 : ENNReal)) x = 0 := by simp [hxnot]
  simpa [hix] using hxlim

lemma tendsto_dimensional_density_ratio_of_ball_formula
    {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) {E : Set α}
    (hrel : ∀ᵐ x ∂μ.restrict Eᶜ,
      Tendsto (fun r => μ (E ∩ closedBall x r) / μ (closedBall x r))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (0 : ENNReal)))
    (hball : ∀ x : α,
      ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        μ (closedBall x r) = ENNReal.ofReal ((2 * r) ^ s)) :
    ∀ᵐ x ∂μ.restrict Eᶜ,
      Tendsto (dimensional_density_ratio (μ.restrict E) s x)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (0 : ENNReal)) := by
  filter_upwards [hrel] with x hxrel
  have hEq :
      (fun r => μ (E ∩ closedBall x r) / μ (closedBall x r))
        =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (dimensional_density_ratio (μ.restrict E) s x) := by
    filter_upwards [hball x] with r hr
    calc
      μ (E ∩ closedBall x r) / μ (closedBall x r)
          = μ (E ∩ closedBall x r) / ENNReal.ofReal ((2 * r) ^ s) := by simp [hr]
      _ = (μ.restrict E) (closedBall x r) / ENNReal.ofReal ((2 * r) ^ s) := by
            congr 1
            rw [Measure.restrict_apply]
            · simp [inter_comm]
            · exact measurableSet_closedBall
      _ = dimensional_density_ratio (μ.restrict E) s x r := by
            simp [dimensional_density_ratio]
  exact Tendsto.congr' hEq hxrel


theorem theorem2_6_density_at_points_not_in_E
    {E : Set (Fin n → ℝ)}
    (hE_meas : MeasurableSet E)
    (hE_finite : (hausdorffMeasure s) E < ⊤)
    (hball : ∀ x : Fin n → ℝ,
      ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (hausdorffMeasure s) (closedBall x r) = ENNReal.ofReal ((2 * r) ^ s)) :
    ∀ᵐ x ∂(hausdorffMeasure s).restrict Eᶜ,
      Tendsto (dimensional_density_ratio ((hausdorffMeasure s).restrict E) s x)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 (0 : ENNReal)) :=
  by
  let μ : Measure (Fin n → ℝ) := hausdorffMeasure s
  haveI : IsLocallyFiniteMeasure μ :=
    isLocallyFiniteMeasure_of_closedBall_formula (s := s) μ (by simpa [μ] using hball)
  have h_rel : ∀ᵐ x ∂μ.restrict Eᶜ,
      Tendsto (fun r => μ (E ∩ closedBall x r) / μ (closedBall x r))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (0 : ENNReal)) :=
    ae_tendsto_inter_closedBall_div_zero_on_compl μ hE_meas
  have h_target : ∀ᵐ x ∂μ.restrict Eᶜ,
      Tendsto (dimensional_density_ratio (μ.restrict E) s x)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (0 : ENNReal)) :=
    tendsto_dimensional_density_ratio_of_ball_formula (s := s) μ h_rel
      (by simpa [μ] using hball)
  let _ := hE_finite
  simpa [μ] using h_target


end DensityAtPointsNotInE

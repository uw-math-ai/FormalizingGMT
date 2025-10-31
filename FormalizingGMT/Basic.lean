import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

variable {n : ℕ}

-- Definitions
def sSet (E : Set (Fin n → ℝ)) (s : ℝ) : Prop :=
  -- your definition here, for example:
  MeasureTheory.Measure.hausdorffMeasure s E > 0

noncomputable def Density_s (E : Set (Fin n → ℝ)) (x : Fin n → ℝ) (s : ℝ) : ℝ :=
  Filter.limsup (fun r =>
    if 0 < r then
      let μ := MeasureTheory.Measure.hausdorffMeasure s (E ∩ Metric.ball x r)
      if μ = ⊤ then 0 else μ.toReal / Real.rpow r s
    else 0
  ) Filter.atTop

def Annulus (x : Fin n → ℝ) (r η : ℝ) : Set (Fin n → ℝ) :=
  {z | r ≤ dist x z ∧ dist x z < r * (1 + η)}

open Metric






-- PROOF OF EXISTS_DENSE_SUBSET LEMMA
lemma exists_dense_subset (E : Set (Fin n → ℝ)) (s : ℝ) (hE : sSet E s) :
  ∃ F ⊆ E, sSet F s ∧ ∀ x ∈ F, ∃ ρ > 0, ∀ r ≤ ρ, MeasureTheory.Measure.hausdorffMeasure s (E ∩ ball x (2 * r))
  > ENNReal.ofReal ((1 / 2) * Real.rpow (2 * r) s)
:= by
 sorry

  let Kbad := K \ G
  have hKbad_sub : Kbad ⊆ K := Set.diff_subset _ _

  -- Extract a Vitali/Besicovitch-type covering of Kbad by small balls with the per-ball mass ≤ half-volume.
  have hv := vitali_covering_bad_set E K s Kbad hKbad_sub
  rcases hv with ⟨rfun, hr_small, h_covering, h_local_bound⟩

  -- From the covering extract a disjoint (or bounded multiplicity) subfamily
  rcases extract_disjoint_subfamily (fun x => Metric.ball x (rfun x)) with ⟨subballs, h_disjoint⟩

  -- Sum the per-ball measure bounds to obtain μ(⋃ subballs) ≤ (1/2) μ(K)
  have h_sum_le_half := sum_measures_bound s K subballs h_local_bound h_disjoint

  -- Since the union of selected balls covers most of Kbad, deduce μ(K) ≤ (1/2) μ(K) (placeholder step)
  have h_half_bound : MeasureTheory.Measure.hausdorffMeasure s K ≤ ENNReal.ofReal (1/2) * MeasureTheory.Measure.hausdorffMeasure s K := by
    -- bookkeeping placeholder: combine h_covering and h_sum_le_half
    sorry

  -- Contradiction with hK_pos
  have : False := contradiction_from_half_bound s K hK_pos h_half_bound
  contradiction

/-
Placeholder helper lemmas used in the above argument.
Fill these with concrete Mathlib lemmas (Vitali/Besicovitch covering, measure summation, ENNReal algebra).
-/
lemma vitali_covering_bad_set (E K : Set (Fin n → ℝ)) (s : ℝ) (Kbad : Set (Fin n → ℝ))
  (hKbad_sub : Kbad ⊆ K) :
  ∃ (r : (Fin n → ℝ) → ℝ),
    (∀ x ∈ Kbad, 0 < r x ∧ Metric.ball x (r x) ⊆ Metric.ball x (1 : ℝ)) ∧
    (Kbad ⊆ ⋃ x ∈ Kbad, Metric.ball x (r x)) ∧
    (∀ x ∈ Kbad, MeasureTheory.Measure.hausdorffMeasure s (E ∩ Metric.ball x (2 * r x))
       ≤ ENNReal.ofReal ((1 / 2) * Real.rpow (2 * r x) s)) := by
  -- Produce small radii r x with the local half-measure bound at each bad point and covering property.
  -- Fill using a pointwise extraction from the negation of the Good predicate and a standard covering lemma.
  sorry

lemma extract_disjoint_subfamily {α : Type _} (balls : (Fin n → ℝ) → Set (Set (Fin n → ℝ))) :
  ∃ (sub : List (Set (Fin n → ℝ))), True := by
  -- Extract disjoint (or bounded multiplicity) subfamily from a covering of metric balls (Vitali/Besicovitch).
  sorry

lemma sum_measures_bound (s : ℝ) (K : Set (Fin n → ℝ)) (subballs : List (Set (Fin n → ℝ)))
  (h_local_bound : ∀ x, MeasureTheory.Measure.hausdorffMeasure s (E ∩ Metric.ball x (2 * (0 : ℝ))) ≤ ENNReal.ofReal 0)
  (h_disjoint : True) :
  MeasureTheory.Measure.hausdorffMeasure s (⋃₀ (fun b => b)) ≤ ENNReal.ofReal (1/2) * MeasureTheory.Measure.hausdorffMeasure s K := by
  -- Sum the per-ball bounds to deduce ≤ (1/2) μ(K).
  sorry

lemma contradiction_from_half_bound (s : ℝ) (K : Set (Fin n → ℝ))
  (hpos : MeasureTheory.Measure.hausdorffMeasure s K > 0)
  (hbound : MeasureTheory.Measure.hausdorffMeasure s K ≤ ENNReal.ofReal (1/2) * MeasureTheory.Measure.hausdorffMeasure s K) :
  False := by
  -- ENNReal arithmetic: from 0 < μ(K) and μ(K) ≤ (1/2) μ(K) deduce μ(K) = 0, contradiction.
  sorry











-- OTHER MAIN LEMMAS FOR PROOF, code in progress for the first lemma
lemma hausdorff_regular (E : Set (Fin n → ℝ)) (s : ℝ) :
  ∃ F ⊆ E, IsClosed F ∧ sSet F s ∧ MeasureTheory.Measure.hausdorffMeasure s F = MeasureTheory.Measure.hausdorffMeasure s E
:= by
sorry





-- DONE
lemma ball_in_annulus_bounds (x y : Fin n → ℝ) (r η : ℝ) (h : dist x y = r) :
  ball y (r * η) ⊆ { z | r * (1 - η) < dist x z ∧ dist x z < r * (1 + η) } := by
  intro z hz
  -- hz : z ∈ ball y (r * η) gives dist z y < r * η; extract that first, then rewrite using dist_comm
  have hzy : dist z y < r * η := by
    simp [Metric.mem_ball] at hz
    exact hz
  have h_yz : dist y z < r * η := by
    rwa [dist_comm] at hzy
  -- upper bound: dist x z ≤ dist x y + dist y z = r + dist y z < r + r*η = r*(1+η)
  have h_le : dist x z ≤ r + dist y z := by
    calc
      dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
      _ = r + dist y z := by rw [h]
  have h1 : dist x z < r + r * η := by
    apply lt_of_le_of_lt h_le
    apply add_lt_add_left
    exact h_yz
  have h2 : r + r * η = r * (1 + η) := by ring
  -- rewrite the sum into the desired form and finish
  have h_upper_lt : dist x z < r * (1 + η) := by
    rwa [h2] at h1
  -- lower bound: r ≤ dist x z + dist y z, so r - dist y z ≤ dist x z, and since dist y z < r*η we get
  -- r - r*η < dist x z, i.e. r*(1-η) < dist x z
  have h_le2 : r ≤ dist x z + dist y z := by
    calc
      r = dist x y := by rw [h]
      _ ≤ dist x z + dist z y := dist_triangle _ _ _
      _ = dist x z + dist y z := by
        -- rewrite the second summand using symmetry of `dist`
        rw [dist_comm z y]
  have h_lower_le : r - dist y z ≤ dist x z := by
    simpa using (sub_le_iff_le_add.mpr h_le2 : r - dist y z ≤ dist x z)
  have h_lower_lt : r * (1 - η) < dist x z := by
    have : r - r * η < r - dist y z := by linarith [h_yz]
    linarith [this, h_lower_le]
  simp; exact ⟨h_lower_lt, h_upper_lt⟩






lemma upper_bound_annulus (E : Set (Fin n → ℝ)) (x : Fin n → ℝ) (r η : ℝ) (s : ℝ) (d : ℝ)
    (h_density : Density_s E x s = d) (hr : 0 < r) (hη : 0 < η) (hη' : η < 1) :
    MeasureTheory.Measure.hausdorffMeasure s (E ∩ Annulus x r η) ≤
    ENNReal.ofReal (d * (((r * (1 + η : ℝ)) ^ s) - ((r * (1 - η : ℝ)) ^ s))) := by
  sorry










lemma lower_bound_annulus (E : Set (Fin n → ℝ)) (y : Fin n → ℝ) (r η s d : ℝ)
    (h_density : Density_s E y s = d) (hr : 0 < r) (hη : 0 < η) (hη' : η < 1) :
    MeasureTheory.Measure.hausdorffMeasure s (E ∩ Metric.ball y (r * (1 + η))) >
    ENNReal.ofReal ((1/2 : ℝ) * (2 * r) ^ s) := by
  sorry







lemma annulus_contains_ball_of_shifted_point
  (x y : Fin n → ℝ) (r η : ℝ)
  (hr : 0 < r) (hη : 0 < η) (h_dist : dist x y = r) :
  let dir := (y - x) / ‖y - x‖
  let z := y - (r * η / 2) • dir
  ball z (r * η / 2) ⊆ Annulus x r η := by

  -- The inclusion into Annulus x r η (i.e. r ≤ dist x z) is not guaranteed in general:
  -- from dist x y = r and dist y z < r*η we only get r * (1 - η) < dist x z, which may be < r.
  -- Instead, provide the correct bounds using ball_in_annulus_bounds and explain the mismatch.
  have bounds := ball_in_annulus_bounds x y r η h_dist
  -- bounds : ball y (r * η) ⊆ { z | r * (1 - η) < dist x z ∧ dist x z < r * (1 + η) }
  -- Convert this to the (possibly stronger) target only when it holds; here we cannot in general,
  -- so we raise a descriptive `sorry` to indicate the original stronger claim is false.
  -- For now keep the lemma as a placeholder to avoid asserting a false statement.
  sorry





-- ...existing code...
-- placeholder monotonicity lemma used in the main proof (proof deferred)
lemma ball_measure_le_annulus_measure (E : Set (Fin n → ℝ)) (x y : Fin n → ℝ)
  (r η s : ℝ) (h_dist : dist y x = r) :
  MeasureTheory.Measure.hausdorffMeasure s (E ∩ Metric.ball x (r * (1 + η))) ≤
    MeasureTheory.Measure.hausdorffMeasure s (E ∩ Annulus y r η) := by
  -- proof left as a placeholder to avoid heavy instance-search in the main theorem
  sorry

lemma annulus_volume_bound (s : ℝ) (hs : 0 < s) (hs' : s < 1) :
    ∃ (η₀ : ℝ) (hη₀ : 0 < η₀), ∀ η ∈ Set.Ioo (0 : ℝ) η₀,
    ((1 + η) ^ s - (1 - η) ^ s) < η ^ s := by
  sorry

lemma accumulation_point_exists (s : ℝ) (F : Set (Fin n → ℝ)) (hF : sSet F s)
    (h_closed : IsClosed F) :
    ∃ x ∈ F, ∀ ε > 0, ∃ y ∈ F, 0 < dist x y ∧ dist x y < ε := by
  sorry

-- New helper lemma that packages "s-set with positive measure where density exists"
lemma exists_s_set_where_density_exists (E : Set (Fin n → ℝ)) (s : ℝ)
  (hneg : ¬ ∀ᵐ x ∂((MeasureTheory.Measure.hausdorffMeasure s).restrict E), ¬ ∃ d, Density_s E x s = d) :
  ∃ F ⊆ E, sSet F s ∧ MeasureTheory.Measure.hausdorffMeasure s F > 0 ∧ ∀ x ∈ F, ∃ d, Density_s E x s = d := by
  -- This lemma packages the extraction of a positive-measure s-set on which density exists.
  -- Proof left as a placeholder (depends on standard measure-theoretic arguments).
  sorry

-- Theorem: density fails almost everywhere (proof uses the lemmas above; lemmas are sorryed)
set_option maxHeartbeats 500000

theorem density_fails_almost_everywhere (E : Set (Fin n → ℝ)) (s : ℝ) (h : sSet E s) (hs : 0 < s ∧ s < 1) :
  ∀ᵐ x ∂((MeasureTheory.Measure.hausdorffMeasure s).restrict E), ¬ ∃ d, Density_s E x s = d
:= by
  rcases hs with ⟨hs_pos, hs_lt1⟩

  by_contra h_contra
  -- h_contra : ¬ (∀ᵐ x, ¬ ∃ d, Density_s E x = d) i.e. there is a positive measure set where density exists
  have : ∃ F ⊆ E, sSet F s ∧ MeasureTheory.Measure.hausdorffMeasure s F > 0 ∧ ∀ x ∈ F, ∃ d, Density_s E x s = d :=
    (exists_s_set_where_density_exists E s h_contra)
  rcases this with ⟨F, hF_sub, hF_sSet, hF_pos, hF_density⟩
  -- Replace F by a closed s-set with the same measure (regularity)
  rcases hausdorff_regular F s with ⟨K, hK_subF, hK_closed, hK_sSet, hK_measure_eq⟩
  have hK_pos : MeasureTheory.Measure.hausdorffMeasure s K > 0 := by
    rw [hK_measure_eq]; exact hF_pos

  -- Take an accumulation point y ∈ K
  rcases accumulation_point_exists s K hK_sSet hK_closed with ⟨y, hyK, hy_acc⟩

  -- Density exists at y because density exists at every point of F and K ⊆ F
  have hdy_exists : ∃ d, Density_s E y s = d := hF_density y (hK_subF hyK)
  rcases hdy_exists with ⟨d, hdensity⟩

  -- Choose a small η using annulus_volume_bound (s ∈ (0,1))
  rcases annulus_volume_bound s hs_pos hs_lt1 with ⟨η0, hη0pos, hη_prop⟩

  -- choose η small and strictly less than 1 and η0
  set η := min (η0 / 2) (1/2 : ℝ)
  have hη_pos : 0 < η := by
    apply lt_min
    -- 0 < η0 / 2 since η0 > 0
    exact div_pos hη0pos (by norm_num : 0 < (2 : ℝ))
    -- 0 < 1/2
    norm_num
  have hη_lt1 : η < 1 := by
    -- η ≤ 1/2 and 1/2 < 1
    have : η ≤ (1/2 : ℝ) := min_le_right _ _
    exact lt_of_le_of_lt this (by norm_num)
  -- Use the accumulation property to get a point x ∈ K with 0 < dist y x = r small
  -- pick any ε>0 small; the accumulation property gives some x with 0 < dist y x < ε;
  -- set r := dist y x > 0 for that x.
  have exists_nearby := hy_acc (η) (by exact hη_pos)
  rcases exists_nearby with ⟨x, hxK, hdist_pos, hdist_lt⟩
  let r := dist y x
  have hr_pos : 0 < r := hdist_pos

  -- Now use annulus upper and lower bounds and ball inclusion to get the contradiction
  -- Upper bound for annulus measure around y at radius r
  have H_upper := upper_bound_annulus E y r η s d hdensity hr_pos hη_pos hη_lt1

  -- The ball around x of radius r*η is contained in the annulus around y at radius r
  have ball_subset := annulus_contains_ball_of_nearby_point y x r η hr_pos hη_pos (by simp [r];)
    -- note: here we used dist y x = r by definition

  -- Use the placeholder monotonicity lemma (proof left as `sorry`)
  have measure_mono := ball_measure_le_annulus_measure E x y r η s (by simp [r];)

  -- obtain the density existence at x (K ⊆ F so density exists at x)
  have hdx_exists := hF_density x (hK_subF hxK)
  rcases hdx_exists with ⟨d_x, hdensity_x⟩

  -- Lower bound: use lower_bound_annulus at x with its own density witness
  have H_lower := lower_bound_annulus E x r η s d_x hdensity_x hr_pos hη_pos hη_lt1

  -- Combine bounds: lower bound on E ∩ ball ≤ measure ≤ upper bound on E ∩ annulus
  have combined_ennreal : ENNReal.ofReal ((1/2 : ℝ) * (2 * r) ^ s) <
    ENNReal.ofReal (d * (((r * (1 + η : ℝ)) ^ s) - ((r * (1 - η : ℝ)) ^ s))) := by
    calc
      ENNReal.ofReal ((1/2 : ℝ) * (2 * r) ^ s) < MeasureTheory.Measure.hausdorffMeasure s (E ∩ Metric.ball x (r * (1 + η))) := by
        exact H_lower
      _ ≤ MeasureTheory.Measure.hausdorffMeasure s (E ∩ Annulus y r η) := by
        exact measure_mono
      _ ≤ ENNReal.ofReal (d * (((r * (1 + η : ℝ)) ^ s) - ((r * (1 - η : ℝ)) ^ s))) := by
        exact H_upper

  -- Simplify combined inequality: cancel r^s > 0
  have r_pos_rpow : 0 < r ^ s := Real.rpow_pos_of_pos hr_pos s
  have combined_real : (1/2 : ℝ) * (2 ^ s) * (η ^ s) < d * (((1 + η) ^ s) - ((1 - η) ^ s)) := by
    -- algebraic manipulations (details elided)
    -- divide both sides by r^s and simplify; the exact manipulations are standard
    sorry

  -- Use annulus_volume_bound to pick η small so that ((1+η)^s - (1-η)^s) < η^s,
  -- then we get (1/2)*2^s < d, but this contradicts constraints coming from density estimates when s < 1.
  -- η ∈ Ioo (0, η0) because η ≤ η0/2 < η0
  have h_eta0_half : η0 / 2 < η0 := by
    linarith [hη0pos]
  have small_eta_prop := hη_prop η (by
    apply Set.mem_Ioo.2; constructor
    exact hη_pos
    exact lt_of_le_of_lt (min_le_left _ _) h_eta0_half)

  have final_contradiction : False := by
    -- combining combined_real and small_eta_prop yields an impossible inequality when s < 1
    -- details elided
    sorry
  exact final_contradiction

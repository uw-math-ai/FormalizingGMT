/-
This file contains most of the lemmas on the Overleaf. Initial version proved by Aristotle.


To-dos:
-Remove dependence on EMetric (move to Metric)
-Generalize where possible
-Remove unneccessary iterations provided by Aristotle
-Update things to work in latest version of Mathlib
-/


import Mathlib
-- Canonical definitions live in Definitions.lean:
-- HasPositiveFiniteHausdorff, dimensional_density_ratio, lower_dimensional_density,
-- has_density, upper_dimensional_density, hausdorffContentInfty
import FormalizingGMT.«Project Versions».Definitions

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxRecDepth 4000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Checking availability of EuclideanSpace and hausdorffMeasure.
-/
open MeasureTheory MeasureTheory.Measure Metric Set Filter Topology

/-
Definition of an s-set.
-/
open MeasureTheory MeasureTheory.Measure Metric Set Filter Topology ENNReal

/-- E is an s-set if E is H^s-measurable and 0 < H^s(E) < ⊤.
    Canonical version in Definitions.lean as `HasPositiveFiniteHausdorff`. -/
-- def HasPositiveFiniteHausdorff removed: imported from Definitions.lean

/-
Definition of s-density ratio and s-density. Note: The user text says "D^s(E,x) \
exists", which implies a limit. I defined Ds as liminf to have a value always, but \
HasDs checks if it is a limit.
Actually, looking at the text "D^s(E,x) fails to exist", it implies we should \
distinguish between existence and the value.
If I define Ds as liminf, then "Ds exists" is trivial if I just mean the value exists.
The user means the limit exists.
So `HasDs` is the condition.
And when they write `D^s(E,x)` in a context where it exists, they mean the limit.
If it doesn't exist, `Ds` (liminf) is still defined but might not be the limit \
(limit might not exist).
However, usually "density exists" means limsup = liminf.
I'll define `Ds` as `liminf` (or `limsup`? The text uses `limsup` in Lemma 2.4 \
"upper density lower bound").
Wait, Lemma 2.4 mentions `limsup`.
But the main theorem talks about `D^s(E,x)` existing.
If `D^s(E,x)` exists, then `liminf = limsup`.
So defining `Ds` as `liminf` is consistent with the value when it exists.
I will stick with `liminf` for `Ds` and `HasDs` for the limit existence.
Actually, `HasDs` should probably just be `Tendsto`.
And `Ds` should be the value.
If `Tendsto ... (𝓝 y)`, then `y` is the density.
I'll define `Ds` as `liminf`.
And `HasDs` as `Tendsto ... (𝓝 (Ds s E x))`.
This ensures that if `HasDs` holds, `Ds` is the limit.
One detail: `(2*r)^s` might be undefined for negative `r`, but we take limit at `𝓝[>] 0`.
Also `ENNReal.ofReal` handles negative values by returning 0.
I'll proceed with this.
-/
open MeasureTheory MeasureTheory.Measure Metric Set Filter Topology ENNReal

variable {n : ℕ}

-- TODO: Remove once ball → closedBall refactor is complete.
-- GMT convention (Mattila): density uses closed balls. Canonical version
-- is `dimensional_density_ratio` in Definitions.lean (takes an explicit measure μ).
-- Keeping this local Hausdorff-measure/(2r)^s version to preserve compilability of geometric proofs.
private noncomputable def densityRatio (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) : ℝ≥0∞ :=
  hausdorffMeasure s (E ∩ closedBall x r) / (ENNReal.ofReal ((2 * r) ^ s))

/-- The s-density of E at x (liminf version). Canonical version in Definitions.lean
    is `lower_dimensional_density`, built on `dimensional_density_ratio`. -/
private noncomputable def Ds (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  liminf (densityRatio s E x) (𝓝[>] 0)

/-- The proposition that the s-density exists at x. Canonical version in Definitions.lean
    is `has_density`, built on `dimensional_density_ratio`. -/
private def HasDs (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ y, Tendsto (densityRatio s E x) (𝓝[>] 0) (𝓝 y) ∧ Ds s E x = y

/-
Lemma 4.1: The diameter of a ball B(x,r) in Euclidean space is 2r (assuming dimension n ≠ 0).
-/
open MeasureTheory MeasureTheory.Measure Metric Set Filter Topology ENNReal

variable {n : ℕ}

theorem diam_ball_eq_two_mul_radius (hn : n ≠ 0) (x : EuclideanSpace ℝ (Fin n))
    (r : ℝ) (hr : 0 < r) :
  EMetric.diam (ball x r) = ENNReal.ofReal (2 * r) := by
    refine le_antisymm ?_ ?_
    · -- For any two points $y, z \in \text{ball}(x, r)$, we have $\text{dist}(y, z) \leq 2r$.
      have h_dist_le : ∀ y z : EuclideanSpace ℝ (Fin n),
        y ∈ Metric.ball x r → z ∈ Metric.ball x r → dist y z ≤ 2 * r := by
        exact fun y z hy hz => le_trans (dist_triangle_right _ _ _)
          (by linarith [Metric.mem_ball.mp hy, Metric.mem_ball.mp hz])
      refine EMetric.diam_le ?_
      exact fun y hy z hz => by
        simpa only [edist_dist] using ENNReal.ofReal_le_ofReal (h_dist_le y z hy hz)
    · -- For any ε > 0, there exist points y and z in the ball such that dist y z > 2r - ε.
      have h_eps : ∀ ε > 0, ∃ y z : EuclideanSpace ℝ (Fin n),
        y ∈ Metric.ball x r ∧ z ∈ Metric.ball x r ∧ dist y z > 2 * r - ε := by
        intro ε ε_pos
        obtain ⟨δ, hδ_pos, hδ_lt⟩ : ∃ δ > 0, δ < r ∧ ε > 2 * δ := by
          exact ⟨Min.min (ε / 4) (r / 2),
            lt_min (by positivity) (by positivity),
            min_lt_of_right_lt (by linarith),
            by linarith [min_le_left (ε / 4) (r / 2), min_le_right (ε / 4) (r / 2)]⟩
        -- Choose points $y$ and $z$ in the ball such that $dist y z = 2r - 2\delta$.
        obtain ⟨y, z, hyz⟩ : ∃ y z : EuclideanSpace ℝ (Fin n),
          y ∈ Metric.ball x r ∧ z ∈ Metric.ball x r ∧ dist y z = 2 * r - 2 * δ := by
          -- Choose points $y$ and $z$ in the ball such that $dist y z = 2r - 2\delta$.
          -- We can take $y = x + (r - \delta) \cdot e_1$ and $z = x - (r - \delta) \cdot e_1$,
          -- where $e_1$ is the first standard basis vector.
          use x + (r - δ) • (EuclideanSpace.single ⟨0, Nat.pos_of_ne_zero hn⟩ 1),
            x - (r - δ) • (EuclideanSpace.single ⟨0, Nat.pos_of_ne_zero hn⟩ 1)
          norm_num [dist_eq_norm, EuclideanSpace.norm_eq]
          exact ⟨by rw [Real.sqrt_sq] <;> linarith,
            by rw [Real.sqrt_eq_iff_mul_self_eq] <;>
               norm_num [Finset.sum_add_distrib, add_sq, Finset.mul_sum _ _ _,
                 Finset.sum_mul _ _ _, Finset.sum_ite, Finset.filter_eq',
                 Finset.filter_ne'] <;> nlinarith⟩
        exact ⟨y, z, hyz.1, hyz.2.1, by linarith⟩
      contrapose! h_eps;
      -- Since the diameter is less than 2r, we can choose ε = 2r - diameter.
      use 2 * r - ENNReal.toReal (EMetric.diam (Metric.ball x r));
      simp_all only [ne_eq, Nat.ofNat_nonneg, ofReal_mul, ofReal_ofNat, gt_iff_lt,
        sub_pos, mem_ball, _root_.sub_sub_cancel]
      apply And.intro
      · convert ENNReal.toReal_strict_mono _ h_eps using 1;
        · rw [ ENNReal.toReal_mul, ENNReal.toReal_ofReal hr.le ] ; norm_num;
        · norm_num [ ENNReal.mul_eq_top ];
      · intro x_1 x_2 _ __1
        · refine le_trans ?_ (ENNReal.toReal_mono ?_ <|
            EMetric.edist_le_diam_of_mem
              (Metric.mem_ball.mpr ‹Dist.dist x_1 x < r›)
              (Metric.mem_ball.mpr ‹Dist.dist x_2 x < r›))
          · norm_num [ edist_dist ];
          simp_all only [ne_eq]
          apply Aesop.BuiltinRules.not_intro
          intro a
          simp_all only [not_top_lt]



/-
Definition of Hausdorff content and inequality with Hausdorff measure (for s > 0).
-/
open MeasureTheory MeasureTheory.Measure Metric Set Filter Topology ENNReal

variable {n : ℕ}

-- TODO: Remove once ball → closedBall refactor is complete.
-- Canonical unrestricted Hausdorff content is
-- `hausdorffContentInfty` in Definitions.lean (same body, more general type).
/-- The s-dimensional Hausdorff content of a set E (no diameter cut-off). -/
private noncomputable def hausdorffContent (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨅ (t : ℕ → Set (EuclideanSpace ℝ (Fin n))) (_ : E ⊆ ⋃ i, t i),
    ∑' i, (EMetric.diam (t i)) ^ s

-- Proof involves nested infima manipulation requiring extended computation
theorem hausdorffContent_le_hausdorffMeasure
    (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n))) (hs : 0 < s) :
  hausdorffContent s E ≤ hausdorffMeasure s E := by
    -- By definition of Hausdorff measure, we know that
    simp only [hausdorffMeasure]
    rw [MeasureTheory.Measure.mkMetric_apply]
    -- For any $r > 0$, the infimum of the sums over covers with
    -- diameters $\leq r$ is at least the Hausdorff content.
    have h_inf_ge_hausdorff_content :
        ∀ r > 0, ⨅ (t : ℕ → Set (EuclideanSpace ℝ (Fin n))),
          ⨅ (_ : E ⊆ Set.iUnion t), ⨅ (_ : ∀ n, EMetric.diam (t n) ≤ r),
          ∑' n, ⨆ (_ : (t n).Nonempty), EMetric.diam (t n) ^ s ≥ hausdorffContent s E := by
      intro r hr
      refine le_iInf fun t => le_iInf fun ht => le_iInf fun ht' => ?_
      unfold hausdorffContent
      refine iInf₂_le_of_le t ht ?_
      refine ENNReal.tsum_le_tsum fun i => ?_
      by_cases hi : (t i).Nonempty
      · simp [hi]
      · simp [Set.not_nonempty_iff_eq_empty.mp hi, hs]
    refine le_trans ?_ (le_iSup₂ (1 : ℝ≥0∞) zero_lt_one)
    exact h_inf_ge_hausdorff_content 1 zero_lt_one

/-
Lemma 2.3: Approximation by compact sets.
If E is an s-set, there exists a compact subset F with positive Hausdorff measure.
-/
open MeasureTheory MeasureTheory.Measure Metric Set Filter Topology ENNReal

variable {n : ℕ}

lemma exists_compact_subset_pos_measure (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n)))
    (hE : HasPositiveFiniteHausdorff s E) :
  ∃ F, F ⊆ E ∧ IsCompact F ∧ 0 < hausdorffMeasure s F := by
    contrapose! hE;
    -- Since $E$ is an $s$-set, we have $0 < \mu_H^s(E)$.
    intro h
    obtain ⟨hE_meas, hE_pos, hE_finite⟩ := h;
    have := hE_meas.measure_eq_iSup_isCompact_of_ne_top hE_finite.ne;
    simp_all only [nonpos_iff_eq_zero, iSup_zero, ciSup_const, lt_self_iff_false]

/-
Definition of upper s-density.
-/
open MeasureTheory MeasureTheory.Measure Metric Set Filter Topology ENNReal

variable {n : ℕ}

-- TODO: Remove once ball → closedBall refactor is complete.
-- Canonical version is `upper_dimensional_density` in Definitions.lean
-- (takes an explicit measure μ; built on `dimensional_density_ratio`).
private noncomputable def upperDs (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  limsup (densityRatio s E x) (𝓝[>] 0)

/-
Lemma 2.5: If H^s(E) > 0 with s > 0, then E has an accumulation point.
-/
open MeasureTheory MeasureTheory.Measure Metric Set Filter Topology ENNReal

variable {n : ℕ}

lemma exists_accPt_of_pos_hausdorffMeasure (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n)))
    (hs : 0 < s) (hE : 0 < hausdorffMeasure s E) :
  ∃ x, AccPt x (𝓟 E) := by
    by_contra! h;
    -- If E has no accumulation points, then E is discrete.
    have h_discrete : DiscreteTopology E := by
      -- Since every point in E is isolated, E is discrete.
      have h_isolated : ∀ x ∈ E, ∃ U : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen U ∧ x ∈ U ∧ U ∩ E = {x} := by
        intro x hx; specialize h x; rw [ accPt_iff_frequently ] at h
        simp_all only [ne_eq, not_frequently, not_and]
        rw [ Metric.eventually_nhds_iff ] at h
        simp_all only [gt_iff_lt]
        obtain ⟨w, h⟩ := h
        obtain ⟨left, right⟩ := h
        exact ⟨Metric.ball x w, Metric.isOpen_ball, Metric.mem_ball_self left,
          Set.eq_singleton_iff_unique_mem.mpr ⟨⟨Metric.mem_ball_self left, hx⟩,
            fun y hy => open Classical in Classical.not_not.1 fun h => right hy.1
              (by simp_all only [dist_self, mem_inter_iff, mem_ball,
                 not_false_eq_true]) hy.2⟩⟩
      refine discreteTopology_iff_isOpen_singleton.mpr ?_
      intro x; specialize h_isolated x x.2;
      obtain ⟨val, property⟩ := x
      obtain ⟨w, h_1⟩ := h_isolated
      obtain ⟨left, right⟩ := h_1
      obtain ⟨left_1, right⟩ := right
      simp_all only
      rw [ Set.eq_singleton_iff_unique_mem ] at right ;
      simp_all only [mem_inter_iff, and_self, and_imp, true_and]
      exact ⟨ w, left, by
      ext x : 1
      simp_all only [mem_preimage, mem_singleton_iff]
      obtain ⟨val_1, property_1⟩ := x
      simp_all only [Subtype.mk.injEq]
      apply Iff.intro
      · intro a
        simp_all only
      · intro a
        subst a
        simp_all only ⟩;
    -- Since E is discrete, it is countable.
    have h_countable : Countable E := by
      exact countable_of_Lindelof_of_discrete;
    have h_hausdorff_zero : ∀ x ∈ E, μH[s] {x} = 0 := by
      intro x a
      simp_all only [countable_coe_iff]
      rw [ MeasureTheory.Measure.hausdorffMeasure_apply ];
      refine le_antisymm ?_ ?_
      · refine iSup_le fun r => iSup_le fun hr => ?_
        refine le_trans (iInf_le _ (fun _ => {x})) ?_
        simp_all only [iUnion_singleton_eq_range, range_const, subset_refl,
          EMetric.diam_singleton, zero_le, implies_true, singleton_nonempty,
          zero_rpow_of_pos, iSup_pos, tsum_zero, iInf_pos, le_refl]
      · exact zero_le _
    convert MeasureTheory.measure_iUnion_null fun x : E => h_hausdorff_zero x x.2
    simp_all only [countable_coe_iff, iUnion_singleton_eq_range,
      Subtype.range_coe_subtype, setOf_mem_eq, false_iff]
    apply Aesop.BuiltinRules.not_intro
    intro a
    simp_all only [lt_self_iff_false]

/-
Lemma 2.6: Ball contained in annulus. If x != y, r = |x-y|, 0 < eta < 1,
then B_{1/2 r eta}(x) is contained in the annulus A_{r,eta} centered at y.
-/
open MeasureTheory MeasureTheory.Measure Metric Set Filter Topology ENNReal

variable {n : ℕ}

lemma ball_contained_in_annulus (x y : EuclideanSpace ℝ (Fin n)) (hxy : x ≠ y)
    (η : ℝ) (hη : 0 < η) :
  let r := dist x y
  let A := ball y (r * (1 + η)) \ ball y (r * (1 - η))
  ball x (1/2 * r * η) ⊆ A := by
    refine fun z hz => ⟨?_, ?_⟩ <;>
    simp_all only [ne_eq, one_div, mem_ball]
    · -- Using the triangle inequality, we have dist z y ≤ dist z x + dist x y.
      have h_triangle : dist z y ≤ dist z x + dist x y := by
        exact dist_triangle _ _ _;
      norm_num at * ; nlinarith [ @dist_nonneg _ _ z x, @dist_nonneg _ _ x y ];
    · have := dist_triangle_left x y z;
      norm_num at * ; nlinarith [ dist_pos.2 hxy ]

/-
Lemma 2.7: Annular region measure lower bound.
-/
open MeasureTheory MeasureTheory.Measure Metric Set Filter Topology ENNReal

variable {n : ℕ}

lemma annular_density_ratio_lower_bound
    (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n))) (hs : 0 < s) (_hs1 : s < 1)
    (F : Set (EuclideanSpace ℝ (Fin n))) (_hF_subset : F ⊆ E) (_hF_sset : HasPositiveFiniteHausdorff s F)
    (ρ : ℝ) (_hρ : 0 < ρ)
    (h_density : ∀ x ∈ F, ∀ r, 0 < r → r ≤ ρ →
      hausdorffMeasure s (E ∩ ball x r) > ENNReal.ofReal ((1 / 2) * (2 * r) ^ s))
    (x y : EuclideanSpace ℝ (Fin n)) (hx : x ∈ F) (_hy : y ∈ F) (hxy : x ≠ y)
    (η : ℝ) (hη : 0 < η) (_hη1 : η < 1)
  (r : ℝ) (hr_def : r = dist x y)
  (hr_bound : r ≤ 2 * ρ / η) :
  let A := ball y (r * (1 + η)) \ ball y (r * (1 - η))
  ENNReal.ofReal ((1 / 2) * r ^ s * η ^ s) < hausdorffMeasure s (E ∩ A) := by
    -- By Lemma 2.6, we have $B_{1/2 r η}(x) \subset A_{r,η}$.
    have h_ball_subset_annulus :
        Metric.ball x (1 / 2 * r * η) ⊆
          Metric.ball y (r * (1 + η)) \ Metric.ball y (r * (1 - η)) := by
      intro z hz;
      subst hr_def
      simp_all only [one_div, inv_nonneg, Nat.ofNat_nonneg, ofReal_mul,
        Nat.ofNat_pos, ofReal_inv_of_pos, ofReal_ofNat, gt_iff_lt, ne_eq,
        mem_ball, mem_diff, not_lt]
      apply And.intro
      · have := dist_triangle z x y;
        norm_num at * ; nlinarith [ dist_pos.mpr hxy ];
      · have := dist_triangle_left x y z
        norm_num at *
        nlinarith [ @dist_nonneg _ _ x y, @dist_nonneg _ _ z y ]
    -- By Lemma 2.6, we have $E \cap B_{1/2 r η}(x) \subset E \cap A_{r,η}$.
    have h_inter_subset_annulus :
        E ∩ Metric.ball x (1 / 2 * r * η) ⊆
          E ∩ (Metric.ball y (r * (1 + η)) \ Metric.ball y (r * (1 - η))) := by
      exact Set.inter_subset_inter_right _ h_ball_subset_annulus
    -- By Lemma 2.6, we have $H^s(E \cap B_{1/2 r η}(x)) > 1/2 (2r')^s$.
    have h_measure_ball :
        μH[s] (E ∩ Metric.ball x (1 / 2 * r * η)) >
          ENNReal.ofReal (1 / 2 * (2 * (1 / 2 * r * η)) ^ s) := by
      exact h_density x hx _
        (mul_pos (mul_pos (by norm_num) (hr_def.symm ▸ dist_pos.mpr hxy)) hη)
        (by rw [le_div_iff₀ hη] at hr_bound; nlinarith)
    convert lt_of_lt_of_le h_measure_ball
      (MeasureTheory.measure_mono h_inter_subset_annulus) using 1
    ring_nf
    rw [ Real.mul_rpow ( by rw [ hr_def ] ; positivity ) ( by positivity ) ]

/-
Helper lemma: Limit of scaled density ratio.
-/
open MeasureTheory MeasureTheory.Measure Metric Set Filter Topology ENNReal

variable {n : ℕ}

lemma limit_density_ratio_scaled
    (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n))) (y : EuclideanSpace ℝ (Fin n))
    (h_density : HasDs s E y) (c : ℝ) (hc : 0 < c) :
  Tendsto (fun r => hausdorffMeasure s (E ∩ ball y (r * c)) / ENNReal.ofReal ((2 * r) ^ s)) (𝓝[>] 0)
    (𝓝 (Ds s E y * ENNReal.ofReal (c ^ s))) := by
      -- Recognize that the scaled density ratio is the original density ratio multiplied by $c^s$.
      have h_scaled : ∀ r > 0,
          (hausdorffMeasure s (E ∩ ball y (r * c))) / (ENNReal.ofReal ((2 * r) ^ s)) =
          (hausdorffMeasure s (E ∩ ball y (r * c))) /
            (ENNReal.ofReal ((2 * r * c) ^ s)) * ENNReal.ofReal (c ^ s) := by
        -- By properties of exponents, rewrite denominator as $(2r)^s \cdot c^s$.
        intro r hr
        have h_denom :
            ENNReal.ofReal ((2 * r * c) ^ s) =
              ENNReal.ofReal ((2 * r) ^ s) * ENNReal.ofReal (c ^ s) := by
          rw [← ENNReal.ofReal_mul (by positivity),
            Real.mul_rpow (by positivity) (by positivity)]
        rw [ENNReal.div_mul]
        · ring_nf at *
          simp_all only [gt_iff_lt]
          rw [ENNReal.mul_div_cancel_right (by positivity)
            (by simp_all only [ne_eq, ofReal_ne_top, not_false_eq_true])]
        · exact Or.inr (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hc _)))
        · exact Or.inl <| ENNReal.ofReal_ne_top
      -- Apply the fact that the original density ratio tends to Ds s E y.
      have h_original :
          Filter.Tendsto (fun r => (hausdorffMeasure s (E ∩ ball y (r * c))) /
            (ENNReal.ofReal ((2 * r * c) ^ s))) (𝓝[>] 0) (𝓝 (Ds s E y)) := by
        obtain ⟨ y, hy, hy' ⟩ := h_density
        convert hy.comp
          (show Filter.Tendsto (fun r : ℝ => r * c) (𝓝[>] 0) (𝓝[>] 0) from ?_) using 2
        · unfold densityRatio
          subst hy'
          simp_all only [gt_iff_lt, Function.comp_apply]
          ring_nf
        · rw [tendsto_nhdsWithin_iff]
          subst hy'
          simp_all only [gt_iff_lt, mem_Ioi, mul_pos_iff_of_pos_right]
          apply And.intro
          · exact tendsto_nhdsWithin_of_tendsto_nhds
              (Continuous.tendsto' (by continuity) _ _ (by norm_num))
          · exact self_mem_nhdsWithin
      -- Apply the fact that multiplication by a constant preserves limits.
      have h_final :
          Filter.Tendsto (fun r => (hausdorffMeasure s (E ∩ ball y (r * c))) /
            (ENNReal.ofReal ((2 * r * c) ^ s)) * ENNReal.ofReal (c ^ s))
            (𝓝[>] 0) (𝓝 (Ds s E y * ENNReal.ofReal (c ^ s))) := by
        -- Multiplication by a constant preserves limits in ENNReal.
        apply ENNReal.Tendsto.mul_const h_original
        exact Or.inr ENNReal.ofReal_ne_top
      exact h_final.congr'
        (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => h_scaled x hx ▸ rfl)

/-
Helper lemma: Measure of annulus intersection is difference of measures.
-/
open MeasureTheory MeasureTheory.Measure Metric Set Filter Topology ENNReal

variable {n : ℕ}

lemma measure_annulus_eq_sub
    (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n))) (y : EuclideanSpace ℝ (Fin n))
    (hE : HasPositiveFiniteHausdorff s E) (r η : ℝ) (hr : 0 < r) (hη : 0 < η) :
    hausdorffMeasure s (E ∩ (ball y (r * (1 + η)) \ ball y (r * (1 - η)))) =
      hausdorffMeasure s (E ∩ ball y (r * (1 + η))) -
        hausdorffMeasure s (E ∩ ball y (r * (1 - η))) := by
    rw [← MeasureTheory.measure_diff]
    · congr 1
      exact Set.inter_diff_distrib_left E (ball y (r * (1 + η))) (ball y (r * (1 - η)))
    · exact Set.inter_subset_inter_right _ (Metric.ball_subset_ball (by nlinarith))
    · exact hE.1.nullMeasurableSet.inter measurableSet_ball.nullMeasurableSet
    · exact ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left) hE.2.2)

/-
Lemma 2.8: Limit of annular density ratio.
-/
open MeasureTheory MeasureTheory.Measure Metric Set Filter Topology ENNReal

variable {n : ℕ}

lemma annular_density_ratio_limit
    (s : ℝ) (E : Set (EuclideanSpace ℝ (Fin n))) (y : EuclideanSpace ℝ (Fin n))
    (hE : HasPositiveFiniteHausdorff s E) (h_density : HasDs s E y) (h_finite : Ds s E y ≠ ⊤)
    (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
  let A := fun r => ball y (r * (1 + η)) \ ball y (r * (1 - η))
  Tendsto (fun r => hausdorffMeasure s (E ∩ A r) / ENNReal.ofReal ((2 * r) ^ s)) (𝓝[>] 0)
    (𝓝 (Ds s E y * ENNReal.ofReal ((1 + η) ^ s - (1 - η) ^ s))) := by
      -- Using the measure of the annulus = difference of measures of balls,
      -- we write the limit as difference of limits of density ratios.
      have h_diff :
          Filter.Tendsto (fun r =>
            (μH[s] (E ∩ ball y (r * (1 + η)))) / ENNReal.ofReal ((2 * r) ^ s) -
            (μH[s] (E ∩ ball y (r * (1 - η)))) / ENNReal.ofReal ((2 * r) ^ s))
            (𝓝[>] 0) (𝓝 (Ds s E y * ENNReal.ofReal ((1 + η) ^ s) -
              Ds s E y * ENNReal.ofReal ((1 - η) ^ s))) := by
        -- Difference of convergent functions converges to difference of limits.
        have h_diff :
            Filter.Tendsto (fun r =>
              (μH[s] (E ∩ ball y (r * (1 + η)))) / ENNReal.ofReal ((2 * r) ^ s))
              (𝓝[>] 0) (𝓝 (Ds s E y * ENNReal.ofReal ((1 + η) ^ s))) ∧
            Filter.Tendsto (fun r =>
              (μH[s] (E ∩ ball y (r * (1 - η)))) / ENNReal.ofReal ((2 * r) ^ s))
              (𝓝[>] 0) (𝓝 (Ds s E y * ENNReal.ofReal ((1 - η) ^ s))) := by
          exact ⟨by simpa using limit_density_ratio_scaled s E y h_density (1 + η) (by linarith),
            by simpa using limit_density_ratio_scaled s E y h_density (1 - η) (by linarith)⟩
        refine ENNReal.Tendsto.sub h_diff.1 h_diff.2 ?_
        exact Or.inl ( ENNReal.mul_ne_top h_finite <| ENNReal.ofReal_ne_top );
      refine h_diff.congr' ?_ |> fun h => h.trans ?_
      · filter_upwards [ self_mem_nhdsWithin ] with r hr;
        -- The measure of the annulus is the difference of the measures of the two balls.
        have h_annulus :
            μH[s] (E ∩ (Metric.ball y (r * (1 + η)) \ Metric.ball y (r * (1 - η)))) =
              μH[s] (E ∩ Metric.ball y (r * (1 + η))) -
              μH[s] (E ∩ Metric.ball y (r * (1 - η))) := by
          rw [← MeasureTheory.measure_diff]
          · congr 1
            exact Set.inter_diff_distrib_left E
              (ball y (r * (1 + η))) (ball y (r * (1 - η)))
          · exact Set.inter_subset_inter_right _
              (Metric.ball_subset_ball <| by nlinarith [hr.out])
          · exact hE.1.nullMeasurableSet.inter measurableSet_ball.nullMeasurableSet
          · exact ne_of_lt
              (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left) hE.2.2)
        rw [h_annulus, ENNReal.sub_div]
        exact fun _ _ =>
          ne_of_gt <| ENNReal.ofReal_pos.mpr <| Real.rpow_pos_of_pos (mul_pos zero_lt_two hr) _
      · -- Since ENNReal.ofReal is linear, we can rewrite the right-hand side of the inequality.
        have h_linear :
            ENNReal.ofReal ((1 + η) ^ s - (1 - η) ^ s) =
              ENNReal.ofReal ((1 + η) ^ s) - ENNReal.ofReal ((1 - η) ^ s) := by
          rw [ENNReal.ofReal_sub]
          exact Real.rpow_nonneg (by linarith) _
        rw [ h_linear, ENNReal.mul_sub ];
        tauto

/-
Lemma 2.9: Asymptotic estimate. (1+η)^s - (1-η)^s = 2sη + O(η^2) as η -> 0.
-/
open MeasureTheory MeasureTheory.Measure Metric Set Filter Topology ENNReal Asymptotics

variable {n : ℕ}

-- Mean Value Theorem proof requires extended computation for derivative bounds
set_option maxHeartbeats 400000 in
lemma asymptotic_estimate (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    IsBigO (𝓝 0) (fun η => (1 + η) ^ s - (1 - η) ^ s - 2 * s * η) (fun η => η ^ 2) := by
  refine Asymptotics.IsBigO.of_bound 2 ?_
  -- Using the fact that the second derivative of $(1 + x)^s$ and $(1 - x)^s$ is bounded near $x = 0$, we can show that the difference is $O(x^2)$.
  have h_second_deriv : ∀ᶠ x in 𝓝 0, |(1 + x) ^ s - (1 - x) ^ s - 2 * s * x| ≤ 2 * |x|^2 := by
    have h_deriv : ∀ᶠ x in 𝓝 0, |deriv (fun x => (1 + x) ^ s - (1 - x) ^ s - 2 * s * x) x| ≤ 2 * |x| := by
      have h_deriv : ∀ᶠ x in 𝓝 0, |s * (1 + x) ^ (s - 1) + s * (1 - x) ^ (s - 1) - 2 * s| ≤ 2 * |x| := by
        have h_deriv : HasDerivAt (fun x => s * (1 + x) ^ (s - 1) + s * (1 - x) ^ (s - 1) - 2 * s) (s * (s - 1) - s * (s - 1)) 0 := by
          convert HasDerivAt.sub ( HasDerivAt.add ( HasDerivAt.const_mul s ( HasDerivAt.rpow_const ( hasDerivAt_id 0 |> HasDerivAt.const_add 1 ) _ ) ) ( HasDerivAt.const_mul s ( HasDerivAt.rpow_const ( hasDerivAt_id 0 |> HasDerivAt.const_sub 1 ) _ ) ) ) ( hasDerivAt_const _ _ ) using 1 <;> norm_num
          ring
        have := h_deriv.isLittleO.def zero_lt_one
        simp_all only [_root_.sub_self, hasDerivAt_sub_const_iff, add_zero, Real.one_rpow, mul_one, sub_zero,
          sub_sub_sub_cancel_right, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, smul_eq_mul,
          mul_zero, Real.norm_eq_abs, one_mul]
        filter_upwards [ this ] with x hx using abs_le.mpr ⟨ by linarith [ abs_le.mp hx ], by linarith [ abs_le.mp hx ] ⟩
      -- The derivative of the function is exactly s*(1 + x)^(s-1) + s*(1 - x)^(s-1) - 2*s.
      have h_deriv_eq : ∀ x : ℝ, x ∈ Set.Ioo (-1 : ℝ) 1 → deriv (fun x => (1 + x) ^ s - (1 - x) ^ s - 2 * s * x) x = s * (1 + x) ^ (s - 1) + s * (1 - x) ^ (s - 1) - 2 * s := by
        intro x hx; norm_num [ add_comm, mul_comm, sub_eq_add_neg ]
        convert HasDerivAt.deriv ( HasDerivAt.add ( HasDerivAt.add ( HasDerivAt.rpow_const ( HasDerivAt.add ( hasDerivAt_id' x ) ( hasDerivAt_const _ _ ) ) _ ) ( HasDerivAt.neg ( HasDerivAt.rpow_const ( HasDerivAt.add ( hasDerivAt_neg x ) ( hasDerivAt_const _ _ ) ) _ ) ) ) ( HasDerivAt.neg ( HasDerivAt.mul ( hasDerivAt_id' x ) ( hasDerivAt_const _ _ ) ) ) ) using 1 <;> norm_num <;> ring_nf
        · exact Or.inl ( by linarith [ hx.1, hx.2 ] )
        · exact Or.inl <| by linarith [ hx.1, hx.2 ]
      filter_upwards [ h_deriv, Ioo_mem_nhds ( show -1 < 0 by norm_num ) ( show 0 < 1 by norm_num ) ] with x hx₁ hx₂ using by rw [ h_deriv_eq x hx₂ ] ; exact hx₁
    -- By the Mean Value Theorem, there exists some $c$ between $0$ and $x$ such that $f(x) = f(0) + f'(c)(x - 0)$.
    have h_mvt : ∀ x ∈ Set.Ioo (-1 / 2) (1 / 2), x ≠ 0 → ∃ c ∈ Set.Ioo (min 0 x) (max 0 x), (1 + x) ^ s - (1 - x) ^ s - 2 * s * x = deriv (fun x => (1 + x) ^ s - (1 - x) ^ s - 2 * s * x) c * x := by
      -- Apply the Mean Value Theorem to the interval [0, x] (or [x, 0] if x is negative).
      intros x hx hx_ne_zero
      have h_cont_diff : ContinuousOn (fun x => (1 + x) ^ s - (1 - x) ^ s - 2 * s * x) (Set.Icc (min 0 x) (max 0 x)) ∧ DifferentiableOn ℝ (fun x => (1 + x) ^ s - (1 - x) ^ s - 2 * s * x) (Set.Ioo (min 0 x) (max 0 x)) := by
        constructor
        · exact continuousOn_of_forall_continuousAt fun y hy => by
            exact ContinuousAt.sub ( ContinuousAt.sub ( ContinuousAt.rpow ( continuousAt_const.add continuousAt_id ) continuousAt_const <| Or.inr <| by linarith ) ( ContinuousAt.rpow ( continuousAt_const.sub continuousAt_id ) continuousAt_const <| Or.inr <| by linarith ) ) ( ContinuousAt.mul continuousAt_const continuousAt_id )
        · exact DifferentiableOn.sub ( DifferentiableOn.sub ( DifferentiableOn.rpow ( differentiableOn_id.const_add _ ) ( differentiableOn_const _ ) ( by intro y hy; cases max_cases 0 x <;> cases min_cases 0 x <;> linarith [ hy.1, hy.2, hx.1, hx.2 ] ) ) ( DifferentiableOn.rpow ( differentiableOn_id.const_sub _ ) ( differentiableOn_const _ ) ( by intro y hy; cases max_cases 0 x <;> cases min_cases 0 x <;> linarith [ hy.1, hy.2, hx.1, hx.2 ] ) ) ) ( DifferentiableOn.mul ( differentiableOn_const _ ) differentiableOn_id )
      cases le_total 0 x <;> simp_all +decide
      · have := exists_deriv_eq_slope ( f := fun x => ( 1 + x ) ^ s - ( 1 - x ) ^ s - 2 * s * x ) ( show x > 0 from lt_of_le_of_ne ‹_› ( Ne.symm hx_ne_zero ) )
        exact this h_cont_diff.1 h_cont_diff.2 |> fun ⟨ c, hc₁, hc₂ ⟩ => ⟨ c, hc₁, by rw [ hc₂, sub_zero, div_mul_cancel₀ _ hx_ne_zero ] ; norm_num ⟩
      · -- Apply the Mean Value Theorem to the interval [x, 0].
        have h_mvt : ∃ c ∈ Set.Ioo x 0, deriv (fun x => (1 + x) ^ s - (1 - x) ^ s - 2 * s * x) c = ( (1 + 0) ^ s - (1 - 0) ^ s - 2 * s * 0 - ( (1 + x) ^ s - (1 - x) ^ s - 2 * s * x ) ) / (0 - x) := by
          have := exists_deriv_eq_slope ( f := fun x => ( 1 + x ) ^ s - ( 1 - x ) ^ s - 2 * s * x ) ( show x < 0 from lt_of_le_of_ne ‹_› hx_ne_zero )
          simp_all only [mem_Ioo, add_zero, Real.one_rpow, sub_zero, _root_.sub_self, mul_zero, _root_.zero_sub,
            neg_sub, forall_const]
        grind
    rw [ Metric.eventually_nhds_iff ] at *
    obtain ⟨ ε, hε, H ⟩ := h_deriv; use Min.min ( 1 / 2 ) ε
    simp_all only [one_div, mem_Ioo, ne_eq, inf_lt_iff, lt_sup_iff, and_imp, gt_iff_lt, dist_zero_right,
      Real.norm_eq_abs, lt_inf_iff, inv_pos, Nat.ofNat_pos, and_self, sq_abs, true_and]
    intro y a a_1
    by_cases hy : y = 0
    · simp [hy]
    · have hy_lo : -1 / 2 < y := by linarith [abs_lt.mp a]
      have hy_hi : y < 2⁻¹ := by linarith [abs_lt.mp a]
      rcases h_mvt y hy_lo hy_hi hy with ⟨ c, ⟨ hc₁, hc₂ ⟩, hc₃ ⟩
      rw [ hc₃, abs_mul ]
      cases hc₁ with
      | inl h =>
        cases hc₂ with
        | inl h_1 => linarith
        | inr h_2 =>
          refine le_trans ( mul_le_mul_of_nonneg_right ( H ( show |c| < ε by rw [ abs_of_pos h ] ; linarith [ abs_lt.mp a, abs_lt.mp a_1 ] ) ) ( abs_nonneg _ ) ) ?_
          rw [ abs_of_pos h, abs_of_pos ( by linarith [ abs_lt.mp a, abs_lt.mp a_1 ] : 0 < y ) ]
          nlinarith [ abs_lt.mp a, abs_lt.mp a_1 ]
      | inr h_1 =>
        cases hc₂ with
        | inl h =>
          refine le_trans ( mul_le_mul_of_nonneg_right ( H ( show |c| < ε by exact abs_lt.mpr ⟨ by linarith [ abs_lt.mp a, abs_lt.mp a_1 ], by linarith [ abs_lt.mp a, abs_lt.mp a_1 ] ⟩ ) ) ( abs_nonneg _ ) ) ?_
          cases abs_cases y <;> cases abs_cases c <;> nlinarith
        | inr h_2 => linarith
  simp_all only [sq_abs, Real.norm_eq_abs, norm_pow]

import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic

/- Necessary basic definitions -/
import FormalizingGMT.«Project Versions».Measures.Basic
import FormalizingGMT.«Project Versions».Measures.HausdorffMeasure
import FormalizingGMT.«Project Versions».Densities.Basic
import FormalizingGMT.«Project Versions».Aux_definitions


/-!
# Theorem 2.6: Density at points not in E

For a σ-compact metric space X, s ≥ 0, E ⊂ X Caratheodory measurable with H^s(E) < ∞,
for H^s-almost every x ∈ X \ E:

  lim sup_{r → 0⁺} H^s(E ∩ B(x, r)) / (2r)^s = 0

where B(x, r) denotes the closed metric ball with center x and radius r.
-/

open MeasureTheory Measure Metric Set Filter ENNReal
open scoped NNReal Topology




/-! ## Abbreviations -/

variable {X : Type*} [MetricSpace X] [SigmaCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- The s-dimensional Hausdorff outer measure. -/
noncomputable abbrev Hs_outer (s : ℝ) : OuterMeasure X :=
  OuterMeasure.mkMetric (fun r : ℝ≥0∞ => r ^ s)

/-- The s-dimensional Hausdorff outer measure restricted to E. -/
noncomputable abbrev Hs_restrict (s : ℝ) (E : Set X) : OuterMeasure X :=
  OuterMeasure.restrict E (Hs_outer s)

/-! ## Definition of A_t -/

/-- The set A_t: points outside E where the upper s-density of H^s|_E exceeds t. -/
def A_set (s : ℝ) (E : Set X) (t : ℝ≥0∞) : Set X :=
  {x ∈ Eᶜ | dimensional_upper_density (Hs_restrict s E) s x > t}

omit [SigmaCompactSpace X] in
lemma A_set_subset_compl {s : ℝ} {E : Set X} {t : ℝ≥0∞} :
    A_set s E t ⊆ Eᶜ :=
  fun _ hx => hx.1

/-! ## Hausdorff measure equals outer measure -/

/-- The Hausdorff outer measure is its own trim: μH[s] agrees with Hs_outer on all sets. -/
lemma hausdorff_trim_eq (s : ℝ) :
    (Hs_outer (X := X) s).trim = Hs_outer s := by
  exact OuterMeasure.trim_mkMetric _

/-
μH[s] S = Hs_outer s S for all sets S.
-/
lemma hausdorff_measure_eq_outer (s : ℝ) (S : Set X) :
    μH[s] S = (Hs_outer (X := X) s) S := by
  convert ( MeasureTheory.Measure.toOuterMeasure_apply _ S ) using 1;
  convert ( hausdorff_trim_eq s ) |> Eq.symm |> fun h => congr_arg ( fun f => f S ) h using 1

/-! ## Borel regularity of the Hausdorff outer measure -/

/-
Every set has a Borel superset of the same Hausdorff outer measure.
-/
lemma borel_hull_exists (s : ℝ) (E : Set X) :
    ∃ F : Set X, MeasurableSet F ∧ E ⊆ F ∧ (Hs_outer (X := X) s) F = (Hs_outer s) E := by
  have := @hausdorff_trim_eq X;
  convert this s |> fun h => h ▸ MeasureTheory.OuterMeasure.exists_measurable_superset_eq_trim ( Hs_outer ( X := X ) s ) E using 1;
  grind

/-
The Hausdorff outer measure is Borel regular.
-/
theorem hausdorff_outer_borel_regular (s : ℝ) (hs : 0 ≤ s) :
    IsBorelRegular (Hs_outer (X := X) s) := by
  constructor;
  · convert OuterMeasure.IsMetric.borel_le_caratheodory _;
    convert BorelSpace.measurable_eq;
    all_goals try infer_instance;
    convert OuterMeasure.mkMetric'_isMetric _;
  · exact fun E => by obtain ⟨ F, hF₁, hF₂, hF₃ ⟩ := borel_hull_exists s E; exact ⟨ F, hF₁, hF₂, hF₃.symm ⟩ ;

/-! ## Restricted measure agreement -/

/-
If F ⊇ E, E is Caratheodory measurable, and Hs(F \ E) = 0, then
    Hs_restrict s E and Hs_restrict s F agree on all sets.
-/
lemma restrict_agree_of_null_diff {s : ℝ}
    {E F : Set X} (hEF : E ⊆ F)
    (hE_car : (Hs_outer (X := X) s).IsCaratheodory E)
    (hFE_null : (Hs_outer (X := X) s) (F \ E) = 0) :
    ∀ S : Set X, (Hs_restrict s E) S = (Hs_restrict s F) S := by
  intro S
  have h_eq : (Hs_outer s) (S ∩ F) = (Hs_outer s) (S ∩ E) := by
    refine' le_antisymm _ _;
    · refine' le_trans ( le_trans ( MeasureTheory.measure_mono ( show S ∩ F ⊆ ( S ∩ E ) ∪ ( F \ E ) from fun x hx => by by_cases h : x ∈ E <;> aesop ) ) ( MeasureTheory.measure_union_le _ _ ) ) _ ; aesop;
    · exact MeasureTheory.measure_mono ( Set.inter_subset_inter_right _ hEF );
  unfold Hs_restrict; aesop;

/-! ## Key lemmas -/

/-- For x ∈ A_t, there are arbitrarily small balls where the density exceeds t. -/
lemma fine_cover_of_mem_A_set
    {s : ℝ} {E : Set X} {t : ℝ≥0∞}
    {x : X} (hx : x ∈ A_set s E t) :
    ∀ δ > 0, ∃ ρ ∈ Ioo (0 : ℝ) δ,
      (Hs_restrict s E) (closedBall x ρ) >
        t * ENNReal.ofReal ((2 * ρ) ^ s) := by
  intro δ hδ_pos
  by_contra h_contra
  push_neg at h_contra
  have h_limsup : limsup (dimensional_density_ratio (Hs_restrict s E) s x) (𝓝[>] 0) ≤ t := by
    refine csInf_le ?_ ?_ <;> simp_all +decide [dimensional_density_ratio]
    filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ρ hρ using
      ENNReal.div_le_of_le_mul <| h_contra ρ hρ.1 hρ.2
  exact hx.right.not_ge h_limsup

/-
The Hausdorff measure of a set is bounded by gauge sums of scale-k covers.
-/
lemma hausdorffMeasure_le_of_scale_covers {d : ℝ} (hd : 0 ≤ d)
    {S : Set X} (bound : ℝ≥0∞)
    (h : ∀ k : ℕ,
      ∃ (T : Set X) (_ : T.Countable)
        (r : X → ℝ),
        S ⊆ ⋃ x ∈ T, closedBall x (r x) ∧
        (∀ x ∈ T, r x ∈ Ioo (0 : ℝ) (1 / (↑k + 1))) ∧
        ∑' x : T, ENNReal.ofReal ((2 * r ↑x) ^ d) ≤ bound) :
    μH[d] S ≤ bound := by
  -- Fix an arbitrary ε > 0.
  by_contra h_contra;
  choose T hT_countable r hr1 hr2 hr3 using h
  refine' h_contra (le_trans (_ : μH[d] S ≤ _) (le_trans (_ : _ ≤ _) (le_of_eq (by rfl))));
  convert hausdorffMeasure_le_liminf_tsum d S _ _ _ _ _;
  any_goals exact Nat;
  exact fun k => T k;
  exact fun k => Set.countable_coe_iff.mpr ( hT_countable k );
  exact Filter.atTop;
  use fun n => ENNReal.ofReal ( 2 / ( n + 1 ) );
  convert ENNReal.tendsto_ofReal ( tendsto_const_nhds.div_atTop ( Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) using 1 ; norm_num;
  use fun n x => Metric.closedBall x ( r n x );
  · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn i;
    refine' ediam_le fun x hx y hy => _;
    refine' le_trans ( edist_triangle_right _ _ _ ) _;
    exact ↑i;
    refine' le_trans ( add_le_add ( show edist x i ≤ ENNReal.ofReal ( r n i ) from _ ) ( show edist y i ≤ ENNReal.ofReal ( r n i ) from _ ) ) _;
    · rw [ edist_dist ] ; exact ENNReal.ofReal_le_ofReal hx;
    · rw [ edist_dist ] ; exact ENNReal.ofReal_le_ofReal hy;
    · rw [ ← ENNReal.ofReal_add ( le_of_lt ( hr2 n i i.2 |>.1 ) ) ( le_of_lt ( hr2 n i i.2 |>.1 ) ) ] ; ring_nf;
      exact ENNReal.ofReal_le_ofReal ( mul_le_mul_of_nonneg_right ( le_of_lt ( hr2 n i i.2 |>.2.trans_le ( by rw [ inv_eq_one_div, div_le_div_iff₀ ] <;> norm_cast <;> linarith ) ) ) zero_le_two );
  · filter_upwards [ Filter.eventually_gt_atTop 0 ] with k hk using fun x hx => by rcases Set.mem_iUnion₂.1 ( hr1 k hx ) with ⟨ y, hy, hy' ⟩ ; exact Set.mem_iUnion.2 ⟨ ⟨ y, hy ⟩, hy' ⟩ ;
  · refine' le_trans ( Filter.liminf_le_of_frequently_le _ _ ) _;
    exact bound;
    · refine' Filter.frequently_atTop.2 fun n => ⟨ n, le_rfl, le_trans _ ( hr3 n ) ⟩;
      refine' ENNReal.tsum_le_tsum fun x => _;
      refine' le_trans ( ENNReal.rpow_le_rpow ( ediam_le_of_forall_dist_le _ ) hd ) _;
      exact 2 * r n x;
      · exact fun y hy z hz => le_trans ( dist_triangle_right _ _ _ ) ( by linarith [ Metric.mem_closedBall.mp hy, Metric.mem_closedBall.mp hz ] );
      · rw [ ENNReal.ofReal_rpow_of_pos ( mul_pos zero_lt_two ( hr2 n x x.2 |>.1 ) ) ];
    refine' ⟨0, Filter.Eventually.of_forall (fun n => by positivity)⟩;
    · rfl

/-! ## Inner regularity helper -/

/-- For a Borel set F with Hs(F) < ∞ and Radon Hs|_F, there exists a compact
    K ⊆ F with Hs(F \ K) < ε. -/
lemma exists_compact_subset_of_radon
    {s : ℝ} (hs : 0 ≤ s) {F : Set X}
    (hF_borel : MeasurableSet F)
    (hF_fin : (Hs_outer (X := X) s) F < ⊤)
    (hF_radon : IsRadon (Hs_restrict s F))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K ⊆ F, IsCompact K ∧ (Hs_outer s) (F \ K) < ε := by
  rcases hF_radon with ⟨hBR, hRad⟩
  obtain ⟨K, hK_sub, hK_compact, hK_lt⟩ :
      ∃ K ⊆ F, IsCompact K ∧
        (Hs_restrict s F).toMeasure hRad.choose F <
          (Hs_restrict s F).toMeasure hRad.choose K + ε := by
    apply_rules [MeasurableSet.exists_isCompact_lt_add]
    · convert hF_fin.ne using 1
      convert MeasureTheory.Measure.ofMeasurable_apply _ hF_borel using 1
      simp +decide [Hs_restrict]
    · exact hε.ne'
    · have := hRad.choose_spec; infer_instance
  refine ⟨K, hK_sub, hK_compact, ?_⟩
  have h_toMeasure_apply :
      (Hs_restrict s F).toMeasure hRad.choose (F \ K) < ε := by
    convert ENNReal.lt_iff_exists_real_btwn.mp hK_lt using 1
    constructor <;> intro h
    · exact ENNReal.lt_iff_exists_real_btwn.mp hK_lt
    · obtain ⟨r, hr₀, hr₁, hr₂⟩ := h
      rw [MeasureTheory.measure_diff]
      · rw [ENNReal.sub_lt_iff_lt_right]
        · exact hr₁.trans_le (hr₂.le.trans (by rw [add_comm]))
        · exact ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono hK_sub)
            (lt_of_lt_of_le hr₁ le_top))
        · exact MeasureTheory.measure_mono hK_sub
      · assumption
      · exact hK_compact.measurableSet.nullMeasurableSet
      · grind +splitIndPred
  convert h_toMeasure_apply using 1
  convert hBR.2 (F \ K) |> Classical.choose_spec |> And.right |> And.right using 1
  · simp +decide [Hs_restrict]
    rw [Set.inter_eq_left.mpr Set.diff_subset]
  · convert hBR.2 (F \ K) |> Classical.choose_spec |> And.right |> And.right using 1
    convert MeasureTheory.Measure.ofMeasurable_apply _ _
    exact hF_borel.diff hK_compact.measurableSet

/-! ## Vitali-based covering -/

/-- Pairwise disjoint closed balls with positive radii are countable in a σ-compact metric space. -/
lemma countable_of_pairwise_disjoint_balls
    {ι : Type*} {s : Set ι} {x : ι → X} {r : ι → ℝ}
    (hr_pos : ∀ i ∈ s, 0 < r i)
    (hpd : s.PairwiseDisjoint (fun i => closedBall (x i) (r i))) :
    s.Countable := by
  apply Set.PairwiseDisjoint.countable_of_nonempty_interior
    (fun i hi j hj hij => Set.disjoint_left.mpr fun z hzi hzj =>
      Set.disjoint_left.mp (hpd hi hj hij)
        (Metric.ball_subset_closedBall hzi) (Metric.ball_subset_closedBall hzj))
  intro i hi
  exact ⟨x i, mem_interior_iff_mem_nhds.2 (Metric.ball_mem_nhds _ (hr_pos i hi))⟩

/-! ## A_null for Borel sets -/

/-- At each scale k, construct a cover of A_set s F t using Vitali covering. -/
lemma vitali_cover_at_scale (s : ℝ) (hs : 0 ≤ s)
    {F : Set X}
    (hF_borel : MeasurableSet F)
    (hF_car : (Hs_outer (X := X) s).IsCaratheodory F)
    {t : ℝ≥0∞} (ht : 0 < t) (ht_top : t ≠ ⊤)
    {K : Set X} (hK_sub : K ⊆ F) (hK_compact : IsCompact K)
    (k : ℕ) :
    ∃ (T : Set X) (_ : T.Countable) (r : X → ℝ),
      A_set s F t ⊆ ⋃ x ∈ T, closedBall x (r x) ∧
      (∀ x ∈ T, r x ∈ Ioo (0 : ℝ) (1 / (↑k + 1))) ∧
      ∑' x : T, ENNReal.ofReal ((2 * r ↑x) ^ s) ≤
        ENNReal.ofReal ((5 : ℝ) ^ s) * t⁻¹ * (Hs_outer s) (F \ K) := by
  /- Proof sketch:
     1. For each x ∈ A_set, choose ρ_x ∈ Ioo(0, min(1/(5(k+1)), infDist x K)) with
        Hs|_F(B(x,ρ_x)) > t·(2ρ_x)^s. This exists by fine_cover_of_mem_A_set.
     2. Apply Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
        with τ=5 to get disjoint u ⊆ A_set covering A_set by 5ρ-balls.
     3. T = u, r = 5ρ. Coverage and radius bounds follow directly.
     4. Gauge sum: ∑(2·5ρ)^s = 5^s·∑(2ρ)^s ≤ 5^s/t · ∑ Hs|_F(B_i)
        ≤ 5^s/t · Hs(F ∩ ∪B_i) ≤ 5^s/t · Hs(F\K)
        since the balls are disjoint and contained in X\K. -/
  sorry

/-
Core Vitali covering argument: for a Borel set F, H^s(B_t(F)) = 0.
    Here B_t(F) = {x ∈ Fᶜ | upper density of Hs|_F at x > t}.
-/
theorem A_null_borel (s : ℝ) (hs : 0 ≤ s)
    {F : Set X}
    (hF_borel : MeasurableSet F)
    (hF_car : (Hs_outer (X := X) s).IsCaratheodory F)
    (hF_fin : (Hs_outer (X := X) s) F < ⊤)
    {t : ℝ≥0∞} (ht : 0 < t) (ht_top : t ≠ ⊤) :
    μH[s] (A_set (X := X) s F t) = 0 := by
  -- Show ∀ δ > 0, μH[s](A_set) ≤ C * t⁻¹ * δ, which gives 0
  set C := ENNReal.ofReal ((5 : ℝ) ^ s)
  have hRadon : IsRadon (Hs_restrict s F) :=
    hausdorff_restrict_isRadon s hs F hF_car hF_fin
  -- Key: for any δ > 0, bound μH[s](A_set) ≤ C * t⁻¹ * δ
  have hmain : ∀ δ : ℝ≥0∞, 0 < δ →
      μH[s] (A_set s F t) ≤ C * t⁻¹ * δ := by
    intro δ hδ
    obtain ⟨K, hK_sub, hK_compact, hK_meas⟩ :=
      exists_compact_subset_of_radon hs hF_borel hF_fin hRadon hδ
    calc μH[s] (A_set s F t)
        ≤ C * t⁻¹ * (Hs_outer s) (F \ K) :=
          hausdorffMeasure_le_of_scale_covers hs _ fun k =>
            vitali_cover_at_scale s hs hF_borel hF_car ht ht_top hK_sub hK_compact k
      _ ≤ C * t⁻¹ * δ := by
          exact mul_le_mul_left' (le_of_lt hK_meas) _
  -- Since C * t⁻¹ < ⊤ (C is finite, t⁻¹ is finite since t ≠ ⊤ and t > 0),
  -- and the bound holds for all δ > 0, we get = 0.
  convert le_antisymm _ bot_le;
  convert le_of_forall_gt_imp_ge_of_dense fun ε hε => ?_;
  · infer_instance;
  · convert hmain ( ε / ( C * t⁻¹ ) ) _ using 1;
    · rw [ ENNReal.mul_div_cancel ];
      · simp +zetaDelta at *;
        exact ⟨ by positivity, ht_top ⟩;
      · exact ENNReal.mul_ne_top ( ENNReal.ofReal_ne_top ) ( ENNReal.inv_ne_top.mpr ht.ne' );
    · simp +zetaDelta at *;
      exact ⟨ hε.ne', ENNReal.mul_ne_top ( ENNReal.ofReal_ne_top ) ( ENNReal.inv_ne_top.mpr ht.ne' ) ⟩

/-! ## A(t) has Hausdorff measure zero -/

theorem A_null_set (s : ℝ) (hs : 0 ≤ s)
    {E : Set X}
    (hE_meas : (Hs_outer (X := X) s).IsCaratheodory E)
    (hE_fin : (Hs_outer (X := X) s) E < ⊤)
    {t : ℝ≥0∞} (ht : 0 < t) (ht_top : t ≠ ⊤) :
    μH[s] (A_set (X := X) s E t) = 0 := by
  -- Step 1: Find Borel hull F ⊇ E with Hs(F) = Hs(E)
  obtain ⟨F, hF_borel, hEF, hF_eq⟩ := borel_hull_exists (X := X) s E
  -- Step 2: Hs(F \ E) = 0 since E is Caratheodory and Hs(F) = Hs(E)
  have hFE_null : (Hs_outer (X := X) s) (F \ E) = 0 := by
    have := hE_meas F; simp_all +decide [ Set.inter_eq_self_of_subset_right hEF ] ;
    contrapose! hF_eq;
    refine' ne_of_gt ( ENNReal.lt_add_right _ _ ) <;> aesop
  -- Step 3: A_set s E t ⊆ A_set s F t ∪ (F \ E)
  have h_subset : A_set s E t ⊆ A_set s F t ∪ (F \ E) := by
    intro x hx
    simp [A_set] at hx;
    by_cases hx_F : x ∈ F <;> simp_all +decide [ A_set ];
    refine' hx.2.trans_le _;
    refine' Filter.limsup_le_limsup _;
    filter_upwards [ self_mem_nhdsWithin ] with r hr;
    have h_eq : (Hs_restrict s E) (Metric.closedBall x r) = (Hs_restrict s F) (Metric.closedBall x r) := by
      apply restrict_agree_of_null_diff hEF hE_meas hFE_null;
    unfold dimensional_density_ratio; aesop;
  -- Step 4: μH[s](A_set s E t) ≤ μH[s](A_set s F t) + μH[s](F \ E) = 0
  have hF_car : (Hs_outer (X := X) s).IsCaratheodory F := by
    have hle : ‹MeasurableSpace X› ≤ (Hs_outer (X := X) s).caratheodory := by
      calc ‹MeasurableSpace X› = borel X := BorelSpace.measurable_eq
        _ ≤ _ := (OuterMeasure.mkMetric'_isMetric (X := X) _).borel_le_caratheodory
    exact hle F hF_borel
  have h1 : μH[s] (A_set (X := X) s F t) = 0 :=
    A_null_borel s hs hF_borel hF_car (hF_eq ▸ hE_fin) ht ht_top
  have h2 : μH[s] (F \ E) = 0 := by
    rw [hausdorff_measure_eq_outer]; exact hFE_null
  have h3 : μH[s] (A_set s E t) ≤ μH[s] (A_set s F t) + μH[s] (F \ E) :=
    le_trans (measure_mono h_subset) (measure_union_le _ _)
  rw [h1, h2] at h3; simpa using h3

/-! ## Main theorem -/

/-
**Theorem 2.6** (Density at points not in E).
For a σ-compact metric space X, s ≥ 0, E ⊂ X Caratheodory-measurable with H^s(E) < ∞,
for H^s-almost every x ∈ X \ E, the s-dimensional upper density of H^s|_E at x is 0.
-/
theorem theorem2_6_density_at_points_not_in_E
    {s : ℝ} (hs : 0 ≤ s) {E : Set X}
    (hE_meas : (Hs_outer (X := X) s).IsCaratheodory E)
    (hE_fin : (Hs_outer (X := X) s) E < ⊤) :
    μH[s] {x | x ∉ E ∧
      dimensional_upper_density (Hs_restrict s E) s x ≠ 0} = 0 := by
  have h_union : {x | x ∉ E ∧ (dimensional_upper_density (Hs_restrict s E) s) x ≠ 0} ⊆ ⋃ (k : ℕ), A_set s E (1 / (k + 1)) := by
    intro x hx;
    -- By definition of $A_set$, we know that if $x \notin E$ and the upper density is not zero, then there exists some $k$ such that $x \in A_set s E (1 / (k + 1))$.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (1 / (k + 1) : ℝ≥0∞) < (dimensional_upper_density (Hs_restrict s E) s x) := by
      rcases ENNReal.exists_inv_nat_lt hx.2 with ⟨ k, hk ⟩;
      exact ⟨ k, lt_of_le_of_lt ( by simp +decide [ Nat.cast_add_one_ne_zero ] ) hk ⟩;
    exact Set.mem_iUnion.2 ⟨ k, hx.1, hk ⟩;
  have h_zero : ∀ k : ℕ, μH[s] (A_set s E (1 / (k + 1))) = 0 := by
    intro k
    apply A_null_set s hs hE_meas hE_fin
    simp [hs];
    simp +decide [ ENNReal.div_eq_top ];
  exact MeasureTheory.measure_mono_null h_union ( MeasureTheory.measure_iUnion_null h_zero )

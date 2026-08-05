module
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
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

/-- The s-dimensional Hausdorff outer measure restricted to E (Step a: µ = Hs|_E). -/
noncomputable abbrev Hs_restrict (s : ℝ) (E : Set X) : OuterMeasure X :=
  OuterMeasure.restrict E (Hs_outer s)

/-! ## A_set definition -/

/-- The set A_t: points outside E where the upper s-density of H^s|_E exceeds t. -/
def A_set (s : ℝ) (E : Set X) (t : ℝ≥0∞) : Set X :=
  {x ∈ Eᶜ | dimensional_upper_density (Hs_restrict s E) s x > t}

omit [SigmaCompactSpace X] in
lemma A_set_subset_compl {s : ℝ} {E : Set X} {t : ℝ≥0∞} :
    A_set s E t ⊆ Eᶜ :=
  fun _ hx => hx.1

/-! ## Hausdorff measure equals outer measure -/

lemma hausdorff_trim_eq (s : ℝ) :
    (Hs_outer (X := X) s).trim = Hs_outer s :=
  OuterMeasure.trim_mkMetric _

lemma hausdorff_measure_eq_outer (s : ℝ) (S : Set X) :
    μH[s] S = (Hs_outer (X := X) s) S := by
  convert congr_arg ( fun μ : MeasureTheory.OuterMeasure X => μ S ) ( hausdorff_trim_eq s ) using 1

/-! ## Step (e): Inner approximation by closed sets -/

/-- Under the assumptions of Theorem 2.6, given ε > 0, there exists a closed set K ⊆ E
    such that Hs(E \ K) < ε. -/
lemma approx_by_closed_inside
    {s : ℝ} (hs : 0 ≤ s) {E : Set X}
    (hE_meas : MeasurableSet[(Hs_outer (X := X) s).caratheodory] E)
    (hE_fin : (Hs_outer (X := X) s) E < ⊤)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : Set X, IsClosed K ∧ K ⊆ E ∧ (Hs_outer s) (E \ K) < ε := by
  letI : BorelRegularOuterMeasure (Hs_outer (X := X) s) :=
    Hausdorff.toBorelRegularOuterMeasure s hs
  exact closed_approx_of_isBorelRegular
    (Hs_outer (X := X) s) E hE_meas hE_fin ε hε

/-! ## Step (g): A_t ⊆ U = X \ K -/

/-- A_t ⊆ X \ K whenever K ⊆ E, since A_t ⊆ X \ E ⊆ X \ K. (Step g) -/
lemma A_subset_compl_K {s : ℝ} {E : Set X} {t : ℝ≥0∞}
    {K : Set X} (hK : K ⊆ E) :
    A_set s E t ⊆ Kᶜ :=
  fun x hx => mt (@hK x) (A_set_subset_compl hx)

/-! ## Step (j): Fine cover for points in A_t -/

/-
For x ∈ A_t, there are arbitrarily small balls where the density exceeds t.
-/
lemma fine_cover_of_mem_A_set
    {s : ℝ} {E : Set X} {t : ℝ≥0∞}
    {x : X} (hx : x ∈ A_set s E t) :
    ∀ δ > 0, ∃ ρ ∈ Ioo (0 : ℝ) δ,
      (Hs_restrict s E) (closedBall x ρ) >
        t * ENNReal.ofReal ((2 * ρ) ^ s) := by
  intro δ δ_pos;
  -- By contradiction, assume there's no such ρ.
  by_contra h_contra;
  convert hx.2.not_ge ?_ using 1
  generalize_proofs at *; (
  refine' csInf_le _ _ <;> norm_num;
  filter_upwards [ Ioo_mem_nhdsGT δ_pos ] with ρ hρ using by rw [ dimensional_density_ratio ] ; exact ENNReal.div_le_of_le_mul <| by aesop;)

/-
For x ∈ A_t ⊆ U (open), we can also ensure B(x, ρ) ⊆ U. (Steps i-j)
-/
lemma fine_cover_in_open
    {s : ℝ} {E : Set X} {t : ℝ≥0∞}
    {x : X} (hx : x ∈ A_set s E t)
    {U : Set X} (hU : IsOpen U) (hxU : x ∈ U) :
    ∀ δ > 0, ∃ ρ ∈ Ioo (0 : ℝ) δ,
      closedBall x ρ ⊆ U ∧
      (Hs_restrict s E) (closedBall x ρ) >
        t * ENNReal.ofReal ((2 * ρ) ^ s) := by
  obtain ⟨ δ₁, hδ₁, hδ₁' ⟩ := Metric.mem_nhds_iff.1 ( hU.mem_nhds hxU );
  intro δ hδ_pos
  obtain ⟨ ρ, hρ₁, hρ₂ ⟩ := fine_cover_of_mem_A_set hx (Min.min δ₁ δ) (lt_min hδ₁ hδ_pos)
  use ρ
  simp [hρ₁, hρ₂];
  exact ⟨ ⟨ hρ₁.1, hρ₁.2.trans_le ( min_le_right _ _ ) ⟩, fun y hy => hδ₁' <| Metric.mem_ball.2 <| lt_of_le_of_lt ( Metric.mem_closedBall.1 hy ) <| hρ₁.2.trans_le ( min_le_left _ _ ), by simpa [ Hs_restrict ] using hρ₂ ⟩

/-! ## Countability of pairwise disjoint balls -/

/-
Pairwise disjoint closed balls with positive radii are countable in a σ-compact metric space.
-/
lemma countable_of_pairwise_disjoint_balls
    {ι : Type*} {s : Set ι} {x : ι → X} {r : ι → ℝ}
    (hr_pos : ∀ i ∈ s, 0 < r i)
    (hpd : s.PairwiseDisjoint (fun i => closedBall (x i) (r i))) :
    s.Countable := by
  have h_countable : Set.Countable (Set.image (fun i => closedBall (x i) (r i)) s) := by
    have h_countable : Set.Countable {B : Set X | ∃ i ∈ s, B = closedBall (x i) (r i)} := by
      have h_disjoint : Set.PairwiseDisjoint {B : Set X | ∃ i ∈ s, B = closedBall (x i) (r i)} (fun B => interior B) := by
        intro B hB C hC hBC;
        obtain ⟨ i, hi, rfl ⟩ := hB; obtain ⟨ j, hj, rfl ⟩ := hC; exact Disjoint.mono ( interior_subset ) ( interior_subset ) ( hpd hi hj ( by aesop ) ) ;
      convert Set.PairwiseDisjoint.countable_of_nonempty_interior h_disjoint _;
      simp +decide [ interior_closedBall, hr_pos ];
      exact fun B i hi hB => hB.symm ▸ ⟨ x i, mem_interior_iff_mem_nhds.mpr ( Metric.closedBall_mem_nhds _ ( hr_pos i hi ) ) ⟩;
    exact h_countable.mono fun B hB => by obtain ⟨ i, hi, rfl ⟩ := hB; exact ⟨ i, hi, rfl ⟩ ;
  have h_inj : Set.InjOn (fun i => closedBall (x i) (r i)) s := by
    intro i hi j hj hij; have := hpd hi hj; simp_all +decide [ Set.disjoint_left ] ;
    contrapose! this;
    exact ⟨ this, x j, by simp +decide [ hr_pos j hj |> le_of_lt ] ⟩;
  exact?

/-! ## Borel ≤ Caratheodory for Hausdorff outer measure -/

omit [SigmaCompactSpace X] in
lemma Hs_borel_le_car (s : ℝ) :
    ‹MeasurableSpace X› ≤ (Hs_outer (X := X) s).caratheodory := by
  convert ( OuterMeasure.IsMetric.borel_le_caratheodory _ ) using 1;
  exact?;
  convert OuterMeasure.mkMetric'_isMetric _

/-! ## Outer measure additivity for pairwise disjoint Caratheodory sets -/

omit [SigmaCompactSpace X] in
/-- For pairwise disjoint Caratheodory-measurable sets indexed by ℕ,
    ∑ μ(t ∩ s_i) ≤ μ(t ∩ ⋃ s_i). Uses `OuterMeasure.isCaratheodory_sum`. -/
lemma outer_tsum_le_of_pairwise_disjoint_car
    {μ : OuterMeasure X}
    {B : ℕ → Set X}
    (hB_car : ∀ i, μ.IsCaratheodory (B i))
    (hB_disj : Pairwise fun i j => Disjoint (B i) (B j))
    (t : Set X) :
    ∑' i, μ (t ∩ B i) ≤ μ (t ∩ ⋃ i, B i) := by
  convert ENNReal.tsum_le_of_sum_range_le _;
  intro n;
  have h_sum : ∑ i ∈ Finset.range n, μ (t ∩ B i) = μ (t ∩ ⋃ i < n, B i) := by
    convert MeasureTheory.OuterMeasure.isCaratheodory_sum μ ( fun i => hB_car i ) ( fun i j hij => hB_disj hij ) using 1;
  exact h_sum.le.trans ( μ.mono <| Set.inter_subset_inter_right _ <| Set.iUnion_subset fun i => Set.iUnion_subset fun hi => Set.subset_iUnion _ _ )

/-! ## Steps (k)-(l): Vitali covering and gauge bound -/

/-
At each scale k, construct a cover of A_t using the Vitali covering lemma.
    The covering gives balls of radius < 1/(k+1) with gauge sum ≤ 5^s/t · Hs(E\K).
    Steps (k)-(l) of the PDF proof.
-/
omit [SigmaCompactSpace X] in
/-- Factor out 5^s from the gauge: (2 * (5 * ρ))^s = 5^s * (2 * ρ)^s -/
lemma gauge_factor_five (s : ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    ENNReal.ofReal ((2 * (5 * ρ)) ^ s) =
    ENNReal.ofReal ((5 : ℝ) ^ s) * ENNReal.ofReal ((2 * ρ) ^ s) := by
  rw [ ← ENNReal.ofReal_mul ( by positivity ), ← Real.mul_rpow ( by positivity ) ( by positivity ), mul_comm ] ; ring

omit [SigmaCompactSpace X] in
/-- From the density condition t * a < b, derive a ≤ t⁻¹ * b. -/
lemma density_bound_inv {t : ℝ≥0∞} (ht : 0 < t) (ht_top : t ≠ ⊤)
    {a b : ℝ≥0∞} (h : t * a < b) :
    a ≤ t⁻¹ * b := by
  rw [ ← ENNReal.mul_le_mul_iff_right ( show t ≠ 0 by exact ne_of_gt ht ) ( by aesop ) ];
  rw [ ← mul_assoc, ENNReal.mul_inv_cancel ht.ne' ht_top, one_mul ] ; exact le_of_lt h

/-  Helper: for pairwise disjoint balls in Kᶜ with density > t,
    the tsum of Hs_restrict values is bounded by Hs(E \ K). -/
lemma tsum_restrict_le_of_disjoint (s : ℝ)
    {E : Set X}
    (hE_car : MeasurableSet[(Hs_outer (X := X) s).caratheodory] E)
    {K : Set X} (hK_sub : K ⊆ E)
    {u : Set X} (hu_count : u.Countable)
    (ρ : X → ℝ)
    (hρ_pos : ∀ x ∈ u, 0 < ρ x)
    (hρ_ball : ∀ x ∈ u, closedBall x (ρ x) ⊆ Kᶜ)
    (hρ_disj : u.PairwiseDisjoint (fun x => closedBall x (ρ x))) :
    ∑' x : u, (Hs_outer s) (E ∩ closedBall (↑x) (ρ ↑x)) ≤ (Hs_outer s) (E \ K) := by
  haveI := hu_count.to_subtype;
  -- Apply the measure_iUnion theorem for the restricted measure.
  have h_measure_iUnion : (MeasureTheory.Measure.restrict (MeasureTheory.Measure.hausdorffMeasure s) E) (⋃ x : u, closedBall (x : X) (ρ x)) = ∑' x : u, (MeasureTheory.Measure.restrict (MeasureTheory.Measure.hausdorffMeasure s) E) (closedBall (x : X) (ρ x)) := by
    rw [ MeasureTheory.measure_iUnion ];
    · exact fun x y hxy => hρ_disj x.2 y.2 ( Subtype.coe_injective.ne hxy );
    · exact fun x => measurableSet_closedBall;
  convert h_measure_iUnion.le.trans _;
  · convert h_measure_iUnion.symm using 1;
    congr! 2;
    rw [ MeasureTheory.Measure.restrict_apply ];
    · rw [ Set.inter_comm, hausdorff_measure_eq_outer ];
    · exact measurableSet_closedBall;
  · rw [ ← h_measure_iUnion, MeasureTheory.Measure.restrict_apply ];
    · refine' le_trans _ ( MeasureTheory.measure_mono _ );
      convert le_rfl;
      · exact funext fun x => hausdorff_measure_eq_outer s x ▸ rfl;
      · simp_all +decide [ Set.subset_def ];
        exact fun x y hy hxy hx => hρ_ball y hy x hxy;
    · exact MeasurableSet.iUnion fun x => measurableSet_closedBall

lemma vitali_cover_at_scale (s : ℝ) (hs : 0 ≤ s)
    {E : Set X}
    (hE_meas : MeasurableSet[(Hs_outer (X := X) s).caratheodory] E)
    {t : ℝ≥0∞} (ht : 0 < t) (ht_top : t ≠ ⊤)
    {K : Set X} (hK_closed : IsClosed K) (hK_sub : K ⊆ E)
    (k : ℕ) :
    ∃ (T : Set X) (_ : T.Countable) (r : X → ℝ),
      A_set s E t ⊆ ⋃ x ∈ T, closedBall x (r x) ∧
      (∀ x ∈ T, r x ∈ Ioo (0 : ℝ) (1 / (↑k + 1))) ∧
      ∑' x : T, ENNReal.ofReal ((2 * r ↑x) ^ s) ≤
        ENNReal.ofReal ((5 : ℝ) ^ s) * t⁻¹ * (Hs_outer s) (E \ K) := by
  -- Step 1: For each x ∈ A_set, choose ρ_x with density and ball-in-U properties
  have h_fine : ∀ x ∈ A_set s E t, ∃ ρ ∈ Ioo (0 : ℝ) (1 / (5 * ((k : ℝ) + 1))),
      closedBall x ρ ⊆ Kᶜ ∧
      (Hs_restrict s E) (closedBall x ρ) > t * ENNReal.ofReal ((2 * ρ) ^ s) := by
    intro x hx
    exact fine_cover_in_open hx hK_closed.isOpen_compl (A_subset_compl_K hK_sub hx) _ (by positivity)
  choose! ρ hρ_range hρ_ball hρ_dens using h_fine
  -- Step 2: Apply Vitali covering theorem with τ = 5
  obtain ⟨u, hu_sub, hu_disj, hu_cover⟩ :=
    @Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall X X _
      (A_set s E t) id ρ (1 / (5 * ((k : ℝ) + 1)))
      (fun a ha => le_of_lt (hρ_range a ha).2) 5 (by norm_num : (3 : ℝ) < 5)
  -- Step 3: u is countable
  have hu_count : u.Countable :=
    countable_of_pairwise_disjoint_balls (fun x hx => (hρ_range x (hu_sub hx)).1) hu_disj
  -- Step 4: Output T = u, r = 5 * ρ
  refine ⟨u, hu_count, fun x => 5 * ρ x, ?_, ?_, ?_⟩
  -- Coverage: A_set ⊆ ⋃_{x∈u} B(x, 5ρ_x)
  · intro x hx
    obtain ⟨y, hy_mem, hy_sub⟩ := hu_cover x hx
    exact mem_iUnion₂.2 ⟨y, hy_mem, hy_sub (mem_closedBall_self (hρ_range x hx).1.le)⟩
  -- Radius bounds: 5ρ_x ∈ Ioo(0, 1/(k+1))
  · intro x hx
    have hρx := hρ_range x (hu_sub hx)
    exact ⟨mul_pos (by norm_num : (0:ℝ) < 5) hρx.1,
           calc 5 * ρ x < 5 * (1 / (5 * ((k : ℝ) + 1))) :=
                    mul_lt_mul_of_pos_left hρx.2 (by norm_num)
                _ = 1 / ((k : ℝ) + 1) := by field_simp⟩
  -- Gauge sum bound: ∑ (2·5ρ)^s ≤ 5^s · t⁻¹ · Hs(E\K)
  · -- Factor out 5^s
    have h_factor : ∀ x : u, ENNReal.ofReal ((2 * (5 * ρ ↑x)) ^ s) =
        ENNReal.ofReal ((5 : ℝ) ^ s) * ENNReal.ofReal ((2 * ρ ↑x) ^ s) := by
      intro x; exact gauge_factor_five s (ρ ↑x) (hρ_range ↑x (hu_sub x.2)).1
    simp_rw [h_factor]
    rw [ENNReal.tsum_mul_left]
    -- Bound ∑ (2ρ)^s ≤ t⁻¹ · ∑ Hs|_E(B(x,ρ))
    have h_dens_bound : ∑' x : u, ENNReal.ofReal ((2 * ρ ↑x) ^ s) ≤
        t⁻¹ * ∑' x : u, (Hs_outer s) (E ∩ closedBall (↑x) (ρ ↑x)) := by
      rw [← ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum fun x =>
        density_bound_inv ht ht_top (by
          have := hρ_dens ↑x (hu_sub x.2)
          simp only [Hs_restrict, OuterMeasure.restrict_apply, Set.inter_comm] at this
          exact this)
    -- Bound ∑ Hs(E ∩ B) ≤ Hs(E\K)
    have h_disj_bound : ∑' x : u, (Hs_outer s) (E ∩ closedBall (↑x) (ρ ↑x)) ≤
        (Hs_outer s) (E \ K) := by
      exact tsum_restrict_le_of_disjoint s hE_meas hK_sub hu_count ρ
        (fun x hx => (hρ_range x (hu_sub hx)).1) (fun x hx => hρ_ball x (hu_sub hx)) hu_disj
    -- Combine
    calc ENNReal.ofReal ((5 : ℝ) ^ s) * ∑' x : u, ENNReal.ofReal ((2 * ρ ↑x) ^ s)
        ≤ ENNReal.ofReal ((5 : ℝ) ^ s) * (t⁻¹ * ∑' x : u, (Hs_outer s) (E ∩ closedBall (↑x) (ρ ↑x))) :=
          mul_le_mul_right h_dens_bound _
      _ ≤ ENNReal.ofReal ((5 : ℝ) ^ s) * (t⁻¹ * (Hs_outer s) (E \ K)) :=
          mul_le_mul_right (mul_le_mul_right h_disj_bound _) _
      _ = ENNReal.ofReal ((5 : ℝ) ^ s) * t⁻¹ * (Hs_outer s) (E \ K) := by ring

/-! ## Hausdorff measure bound from scale covers -/

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
  have := @hausdorffMeasure_le_liminf_tsum;
  contrapose! this;
  choose T hT r hr₁ hr₂ hr₃ using h;
  refine' ⟨ X, inferInstance, inferInstance, inferInstance, ℕ, fun k => T k, _, d, S, Filter.atTop, fun k => ENNReal.ofReal ( 2 / ( k + 1 ) ), _, _ ⟩ <;> simp_all +decide [ div_eq_mul_inv ];
  · convert ENNReal.Tendsto.const_mul ( ENNReal.tendsto_ofReal ( tendsto_inv_atTop_zero.comp ( Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) ) _ using 1 <;> norm_num;
  · refine' ⟨ fun k x => Metric.closedBall x ( r k x ), _, _, _ ⟩;
    · refine' ⟨ 0, fun k hk x hx => _ ⟩;
      refine' le_trans ( Metric.ediam_le_of_forall_dist_le _ ) _;
      exact 2 * r k x;
      · exact fun y hy z hz => le_trans ( dist_triangle_right _ _ _ ) ( by linarith [ Metric.mem_closedBall.mp hy, Metric.mem_closedBall.mp hz ] );
      · rw [ ENNReal.ofReal_le_iff_le_toReal ] <;> norm_num;
        · rw [ ENNReal.toReal_ofReal ( by positivity ) ] ; linarith [ hr₂ k x hx ];
        · exact ENNReal.mul_ne_top ENNReal.coe_ne_top ( ENNReal.ofReal_ne_top );
    · exact ⟨ 0, fun k hk => by simpa using hr₁ k ⟩;
    · refine' lt_of_le_of_lt ( Filter.liminf_le_of_frequently_le _ _ ) this;
      · refine' Filter.Eventually.frequently _;
        filter_upwards [ Filter.eventually_gt_atTop 0 ] with k hk;
        refine' le_trans _ ( hr₃ k );
        refine' ENNReal.tsum_le_tsum fun x => _;
        refine' le_trans ( ENNReal.rpow_le_rpow ( show ediam ( closedBall ( x : X ) ( r k x ) ) ≤ ENNReal.ofReal ( 2 * r k x ) from _ ) hd ) _;
        · refine' ediam_le _;
          intro y hy z hz; rw [ edist_dist ] ; exact ENNReal.ofReal_le_ofReal ( by linarith [ dist_triangle_right y z x, Metric.mem_closedBall.mp hy, Metric.mem_closedBall.mp hz ] ) ;
        · rw [ ENNReal.ofReal_rpow_of_pos ( mul_pos zero_lt_two ( hr₂ k x x.2 |>.1 ) ) ];
      · refine' ⟨ 0, Filter.Eventually.of_forall fun n => _ ⟩;
        exact bot_le

/-! ## H^s(A_t) = 0 -/

/-
Core result: H^s(A_t) = 0. The proof fixes ε > 0, gets K from approx_by_closed_inside,
    applies vitali_cover_at_scale for each scale k, bounds μH[s](A_t) ≤ 5^s/t · ε,
    then lets ε → 0. (Step m)
-/
theorem A_t_null (s : ℝ) (hs : 0 ≤ s)
    {E : Set X}
    (hE_meas : MeasurableSet[(Hs_outer (X := X) s).caratheodory] E)
    (hE_fin : (Hs_outer (X := X) s) E < ⊤)
    {t : ℝ≥0∞} (ht : 0 < t) (ht_top : t ≠ ⊤) :
    μH[s] (A_set (X := X) s E t) = 0 := by
  refine' le_antisymm _ _;
  · have h_bound : ∀ ε > 0, μH[s] (A_set s E t) ≤ ENNReal.ofReal ((5 : ℝ) ^ s) * t⁻¹ * ε := by
      intro ε ε_pos
      obtain ⟨K, hK_closed, hK_sub, hK_fin⟩ : ∃ K : Set X, IsClosed K ∧ K ⊆ E ∧ (Hs_outer s) (E \ K) < ε := by
        exact?;
      refine' hausdorffMeasure_le_of_scale_covers hs _ _;
      intro k
      obtain ⟨T, hT_countable, r, hT_cover, hT_radius, hT_gauge⟩ := vitali_cover_at_scale s hs hE_meas ht ht_top hK_closed hK_sub k
      use T, hT_countable, r
      exact ⟨hT_cover, hT_radius, by
        exact hT_gauge.trans ( mul_le_mul_left' hK_fin.le _ )⟩;
    -- Let ε → 0.
    have h_zero : Filter.Tendsto (fun ε : ℝ≥0∞ => ENNReal.ofReal ((5 : ℝ) ^ s) * t⁻¹ * ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      convert ENNReal.Tendsto.const_mul ( Filter.tendsto_id.mono_left inf_le_left ) _ using 1 ; aesop;
      exact Or.inr ( ENNReal.mul_ne_top ( ENNReal.ofReal_ne_top ) ( ENNReal.inv_ne_top.mpr ht.ne' ) );
    exact le_of_tendsto_of_tendsto tendsto_const_nhds h_zero ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => h_bound ε hε );
  · exact bot_le

/-! ## Main theorem -/

/-
**Theorem 2.6** (Density at points not in E).
For a σ-compact metric space X, s ≥ 0, E ⊂ X Caratheodory-measurable with H^s(E) < ∞,
for H^s-almost every x ∈ X \ E, the s-dimensional upper density of H^s|_E at x is 0.
-/
theorem theorem2_6_density_at_points_not_in_E
    {s : ℝ} (hs : 0 ≤ s) {E : Set X}
    (hE_meas : MeasurableSet[(Hs_outer (X := X) s).caratheodory] E)
    (hE_fin : (Hs_outer (X := X) s) E < ⊤) :
    μH[s] {x | x ∉ E ∧
      dimensional_upper_density (Hs_restrict s E) s x ≠ 0} = 0 := by
  refine' MeasureTheory.measure_mono_null _ _;
  exact ⋃ n : ℕ, A_set s E ( 1 / ( n + 1 ) );
  · intro x hx; simp_all +decide [ A_set ] ;
    rcases ENNReal.exists_inv_nat_lt hx.2 with ⟨ n, hn ⟩;
    exact ⟨ n, lt_of_le_of_lt ( by simp ) hn ⟩;
  · refine' MeasureTheory.measure_iUnion_null fun n => A_t_null s hs hE_meas hE_fin _ _;
    · exact ENNReal.div_pos_iff.mpr ⟨ by norm_num, by norm_num ⟩;
    · simp +decide

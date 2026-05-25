/- This file contains the upper bound in Theorem 2.7 in [EG].
It needs to be modified so it does not assume that the ambient space
satisfies HasBesicovitchCovering -/

import Mathlib

/- Necessary basic definitions -/
import FormalizingGMT.«Project Versions».Measures.Basic
import FormalizingGMT.«Project Versions».Densities.Basic
import FormalizingGMT.«Project Versions».Aux_definitions

open scoped BigOperators Real Nat Pointwise
open MeasureTheory MeasureTheory.Measure Metric Set Filter Topology ENNReal

open MeasureTheory Measure Filter Metric Set ENNReal Topology
open scoped NNReal
set_option maxHeartbeats 800000
namespace HausdorffDensity
variable {X : Type*} [MetricSpace X] [SecondCountableTopology X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [HasBesicovitchCovering X]
noncomputable def density (s : ℝ) (E : Set X) (x : X) (r : ℝ) : ℝ≥0∞ :=
  hausdorffMeasure s (closedBall x r ∩ E) / ENNReal.ofReal ((2 * r) ^ s)
noncomputable def upperDensity (s : ℝ) (E : Set X) (x : X) : ℝ≥0∞ :=
  Filter.limsup (density s E x) (nhdsWithin 0 (Ioi 0))
/-! ## ENNReal helpers -/
theorem ENNReal.eq_zero_of_le_mul_self {a c : ℝ≥0∞} (hc : c < 1) (ha : a ≠ ⊤)
    (h : a ≤ c * a) : a = 0 := by
  contrapose! h
  rw [← ENNReal.toReal_lt_toReal] <;> norm_num [ha, h]
  · exact mul_lt_of_lt_one_left (ENNReal.toReal_pos h ha)
      (ENNReal.toReal_lt_of_lt_ofReal (by aesop))
  · exact ENNReal.mul_ne_top (ne_of_lt (lt_of_lt_of_le hc (by norm_num))) ha
theorem ENNReal.eq_zero_of_le_inv_add_eps {a t : ℝ≥0∞}
    (ht : 1 < t) (ht' : t ≠ ⊤) (ha : a ≠ ⊤)
    (h : ∀ ε : ℝ≥0∞, 0 < ε → a ≤ t⁻¹ * (a + ε)) : a = 0 := by
  have h_lim : a ≤ t⁻¹ * a := by
    contrapose! h
    have h_lim : Tendsto (fun ε : ℝ≥0∞ => t⁻¹ * (a + ε)) (nhdsWithin 0 (Ioi 0))
        (nhds (t⁻¹ * a)) := by
      convert ENNReal.Tendsto.const_mul
        (tendsto_const_nhds.add (tendsto_id.mono_left inf_le_left)) _ using 1 <;> aesop
    have := h_lim.eventually (gt_mem_nhds h)
    have := this.and self_mem_nhdsWithin
    obtain ⟨ε, hε₁, hε₂⟩ := this.exists
    exact ⟨ε, hε₂, hε₁⟩
  exact ENNReal.eq_zero_of_le_mul_self (ENNReal.inv_lt_one.mpr ht) ha h_lim
/-! ## Limsup gives frequently high density -/
theorem frequently_high_density {s : ℝ} {E : Set X} {x : X} {t : ℝ≥0∞}
    (hd : upperDensity s E x > t) :
    ∀ δ : ℝ, 0 < δ → ∃ r, r ∈ Ioo (0 : ℝ) δ ∧
      hausdorffMeasure s (closedBall x r ∩ E) > t * ENNReal.ofReal ((2 * r) ^ s) := by
  contrapose! hd
  obtain ⟨δ, δpos, hδ⟩ := hd
  rw [@upperDensity]
  refine csInf_le ?_ ?_ <;> norm_num
  filter_upwards [Ioo_mem_nhdsGT δpos] with r hr
  exact ENNReal.div_le_of_le_mul (hδ r hr)
/-! ## Hausdorff measure bound from covers -/
omit [SecondCountableTopology X] [CompleteSpace X] [HasBesicovitchCovering X] in
theorem hausdorffMeasure_le_of_covers {d : ℝ} {S : Set X}
    {ι : ℕ → Type*} [∀ n, Countable (ι n)]
    (C : (n : ℕ) → ι n → Set X) (bound : ℝ≥0∞)
    (hcover : ∀ n, S ⊆ ⋃ i, C n i)
    (hdiam : ∀ n, ∀ i, Metric.ediam (C n i) ≤ ENNReal.ofReal (2 / (↑n + 1)))
    (hsum : ∀ n, ∑' i, Metric.ediam (C n i) ^ d ≤ bound) :
    hausdorffMeasure d S ≤ bound := by
  have := @hausdorffMeasure_le_liminf_tsum
  contrapose! this
  refine ⟨X, inferInstance, inferInstance, inferInstance, ℕ, fun n => ι n, ?_, ?_⟩
  · grind +splitIndPred
  · refine ⟨d, S, atTop, fun n => ENNReal.ofReal (2 / (n + 1)), ?_, C, ?_, ?_, ?_⟩ <;> norm_num
    · simpa using ENNReal.tendsto_ofReal
        (tendsto_const_nhds.div_atTop
          (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop))
    · exact ⟨0, fun n _ i => hdiam n i⟩
    · exact ⟨0, fun n _ => hcover n⟩
    · exact lt_of_le_of_lt
        (liminf_le_of_frequently_le' (Frequently.mono (frequently_atTop.2 fun n =>
          ⟨n, le_rfl, hsum n⟩) fun _ h => h)) this
/-! ## Besicovitch covering at a fixed scale -/
/-
At each scale `n`, apply Besicovitch to get a covering of `B_t` with controlled
diameter and gauge sum.
-/
theorem besicovitch_cover_at_scale
    (s : ℝ) (hs : 0 ≤ s) (E : Set X) (hE : MeasurableSet E)
    (hEfin : hausdorffMeasure s E < ⊤)
    (t : ℝ≥0∞) (ht : 1 < t) (ht' : t ≠ ⊤)
    (ε : ℝ≥0∞) (hε : 0 < ε) (n : ℕ) :
    ∃ (T : Set X) (r : X → ℝ),
      T.Countable ∧
      T ⊆ {x ∈ E | upperDensity s E x > t} ∧
      (∀ x ∈ T, r x ∈ Ioo 0 (1 / (↑n + 1 : ℝ))) ∧
      (∀ x ∈ T, hausdorffMeasure s (closedBall x (r x) ∩ E) >
        t * ENNReal.ofReal ((2 * r x) ^ s)) ∧
      {x ∈ E | upperDensity s E x > t} ⊆ ⋃ x ∈ T, closedBall x (r x) ∧
      ∑' (x : T), hausdorffMeasure s (closedBall (↑x) (r ↑x) ∩ E) ≤
        hausdorffMeasure s {x ∈ E | upperDensity s E x > t} + ε := by
  have := @Besicovitch.exists_closedBall_covering_tsum_measure_le;
  convert this ( MeasureTheory.Measure.restrict ( MeasureTheory.Measure.hausdorffMeasure s ) E ) ( by simpa using hε.ne' ) ( fun x => { r : ℝ | 0 < r ∧ r < ( n + 1 : ℝ ) ⁻¹ ∧ μH[s] ( closedBall x r ∩ E ) > t * ENNReal.ofReal ( ( 2 * r ) ^ s ) } ) { x ∈ E | upperDensity s E x > t } _ using 1;
  · simp +decide [ Set.inter_eq_self_of_subset_left, hE ];
    grind;
  · use fun n => if n = 0 then μH[s].restrict E else 0;
    constructor;
    · intro n; split_ifs <;> simp +decide [ *, isFiniteMeasure_iff ] ;
    · ext; simp [sum];
      erw [ MeasureTheory.Measure.ofMeasurable_apply ];
      · simp +decide [ OuterMeasure.sum_apply ];
        rw [ tsum_eq_single 0 ] <;> simp +contextual;
      · assumption;
  · norm_num +zetaDelta at *;
    have h_outer_regular : MeasureTheory.Measure.OuterRegular (μH[s].restrict E) := by
      have h_finite : MeasureTheory.IsFiniteMeasure (μH[s].restrict E) := by
        constructor ; aesop
      infer_instance;
    exact h_outer_regular;
  · intro x hx δ hδ
    obtain ⟨r, hr₀, hr₁⟩ : ∃ r ∈ Ioo 0 (min δ ((n + 1 : ℝ)⁻¹)), μH[s] (closedBall x r ∩ E) > t * ENNReal.ofReal ((2 * r) ^ s) := by
      have := frequently_high_density hx.2 ( Min.min δ ( n + 1 : ℝ ) ⁻¹ ) ( lt_min hδ ( by positivity ) );
      exact this;
    exact ⟨ r, ⟨ hr₀.1, hr₀.2.trans_le ( min_le_right _ _ ), hr₁ ⟩, hr₀.1, hr₀.2.trans_le ( min_le_left _ _ ) ⟩
/-! ## Gauge sum bound from density -/
/-
From the density condition: if each ball has density > t, then
`∑ ediam(B_i)^s ≤ t⁻¹ * ∑ μ(B_i ∩ E)`.
-/
theorem gauge_sum_le_of_density
    {s : ℝ} (hs : 0 ≤ s) {t : ℝ≥0∞} (ht : 1 < t) (ht' : t ≠ ⊤)
    {E : Set X} {T : Set X} (hT : T.Countable) {r : X → ℝ}
    (hr_pos : ∀ x ∈ T, 0 < r x)
    (hdensity : ∀ x ∈ T, hausdorffMeasure s (closedBall x (r x) ∩ E) >
      t * ENNReal.ofReal ((2 * r x) ^ s)) :
    ∑' (x : T), Metric.ediam (closedBall (↑x : X) (r ↑x)) ^ s ≤
      t⁻¹ * ∑' (x : T), hausdorffMeasure s (closedBall (↑x : X) (r ↑x) ∩ E) := by
  have h_ineq : ∀ x ∈ T, ENNReal.ofReal ((2 * r x) ^ s) ≤ t⁻¹ * μH[s] (closedBall x (r x) ∩ E) := by
    intro x hx
    specialize hdensity x hx;
    rw [ ← ENNReal.div_eq_inv_mul ];
    rw [ ENNReal.le_div_iff_mul_le ];
    · simpa only [ mul_comm ] using hdensity.le;
    · exact Or.inl ( ne_of_gt ( lt_trans zero_lt_one ht ) );
    · exact Or.inl ht';
  -- Apply the inequality to each term in the sum.
  have h_sum_ineq : ∀ x ∈ T, (ediam (closedBall x (r x))) ^ s ≤ t⁻¹ * μH[s] (closedBall x (r x) ∩ E) := by
    intro x hx
    have h_ediam : ediam (closedBall x (r x)) ≤ ENNReal.ofReal (2 * r x) := by
      refine' ediam_le _;
      intro y hy z hz; rw [ edist_dist ] ; exact ENNReal.ofReal_le_ofReal ( by linarith [ dist_triangle_right y z x, Metric.mem_closedBall.mp hy, Metric.mem_closedBall.mp hz ] ) ;
    refine' le_trans _ ( h_ineq x hx );
    exact le_trans ( ENNReal.rpow_le_rpow h_ediam hs ) ( by rw [ ENNReal.ofReal_rpow_of_pos ( mul_pos zero_lt_two ( hr_pos x hx ) ) ] );
  rw [ ← ENNReal.tsum_mul_left ];
  apply_rules [ ENNReal.tsum_le_tsum ];
  exact fun x => h_sum_ineq x x.2
/-! ## Core theorem -/
theorem superlevelSet_null (s : ℝ) (hs : 0 ≤ s) (E : Set X) (hE : MeasurableSet E)
    (hEfin : hausdorffMeasure s E < ⊤) (t : ℝ≥0∞) (ht : 1 < t) (ht' : t ≠ ⊤) :
    hausdorffMeasure s {x ∈ E | upperDensity s E x > t} = 0 := by
  set B_t := {x ∈ E | upperDensity s E x > t}
  have hBt_sub : B_t ⊆ E := fun x hx => hx.1
  have hBt_fin : (hausdorffMeasure s : Measure X) B_t ≠ ⊤ :=
    ne_top_of_le_ne_top hEfin.ne (measure_mono hBt_sub)
  apply ENNReal.eq_zero_of_le_inv_add_eps ht ht' hBt_fin
  intro ε hε
  -- For each n, get a covering using besicovitch_cover_at_scale
  have h_cover := fun n => besicovitch_cover_at_scale s hs E hE hEfin t ht ht' ε hε n
  -- Use choice to extract the covers
  choose T r hcount hsub hrad hdensity hcover hsum using h_cover
  -- T n is countable
  have hT_count : ∀ n, Countable (T n) := fun n => (hcount n).to_subtype
  -- Apply hausdorffMeasure_le_of_covers
  apply hausdorffMeasure_le_of_covers
    (fun n => fun (x : T n) => closedBall (x : X) (r n x))
    (t⁻¹ * (hausdorffMeasure s B_t + ε))
  -- Coverage
  · intro n x hx
    obtain ⟨y, hy_mem, hy_ball⟩ := mem_iUnion₂.mp (hcover n hx)
    exact mem_iUnion.mpr ⟨⟨y, hy_mem⟩, hy_ball⟩
  -- Diameter bound
  · intro n ⟨x, hx⟩
    have hr := hrad n x hx
    refine' le_trans _ ( ENNReal.ofReal_le_ofReal <| show 2 * r n x ≤ 2 / ( n + 1 ) from _ );
    · refine' iSup_le fun y => iSup_le fun hy => iSup_le fun z => iSup_le fun hz => _;
      rw [ edist_dist ];
      exact ENNReal.ofReal_le_ofReal ( by linarith [ dist_triangle_right y z x, show dist y x ≤ r n x from by simpa using hy, show dist z x ≤ r n x from by simpa using hz ] );
    · simpa [ div_eq_mul_inv ] using mul_le_mul_of_nonneg_left hr.2.le zero_le_two -- ediam(closedBall x (r n x)) ≤ 2/(n+1) since r n x < 1/(n+1)
  -- Gauge sum bound
  · intro n
    have step1 := gauge_sum_le_of_density hs ht ht' (hcount n)
      (fun x hx => (hrad n x hx).1) (hdensity n) (E := E)
    simp only [B_t] at step1 ⊢
    exact step1.trans (mul_le_mul_left' (hsum n) _)
/-! ## Theorem assembly -/
theorem badSet_null (s : ℝ) (hs : 0 ≤ s) (E : Set X) (hE : MeasurableSet E)
    (hEfin : hausdorffMeasure s E < ⊤) :
    hausdorffMeasure s {x ∈ E | upperDensity s E x > 1} = 0 := by
  convert MeasureTheory.measure_biUnion_null_iff
      (Set.countable_range fun n : ℕ => 1 + (n + 1 : ℝ≥0∞)⁻¹) |>.2 _ using 1
  convert rfl
  rotate_left
  infer_instance
  use fun t => {x ∈ E | upperDensity s E x > t}
  · rintro _ ⟨n, rfl⟩
    convert superlevelSet_null s hs E hE hEfin (1 + (n + 1 : ℝ≥0∞)⁻¹) _ _ using 1 <;> norm_num
    exact ENNReal.lt_add_right (by norm_num) (by norm_num)
  · ext x
    simp +decide [Set.mem_iUnion, Set.mem_setOf_eq]
    intro hx
    constructor <;> intro h
    · exact lt_of_le_of_lt (le_add_of_nonneg_right <| by positivity) h.choose_spec
    · rcases ENNReal.lt_iff_exists_real_btwn.mp h with ⟨y, hy⟩
      rcases exists_nat_one_div_lt (show 0 < y - 1 by
        exact sub_pos.mpr <| by rw [ENNReal.lt_ofReal_iff_toReal_lt] at hy <;> aesop) with ⟨n, hn⟩
      refine ⟨n, lt_of_le_of_lt ?_ hy.2.2⟩
      rw [ENNReal.le_ofReal_iff_toReal_le] <;> norm_num
      · norm_num [ENNReal.toReal_add] at *; linarith
      · linarith
theorem upperDensity_le_one (s : ℝ) (hs : 0 ≤ s) (E : Set X) (hE : MeasurableSet E)
    (hEfin : hausdorffMeasure s E < ⊤) :
    ∀ᵐ x ∂(hausdorffMeasure s).restrict E, upperDensity s E x ≤ 1 := by
  refine MeasureTheory.ae_restrict_iff' hE |>.2 ?_
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
    (badSet_null s hs E hE hEfin)] with x hx using by contrapose! hx; aesop
end HausdorffDensity

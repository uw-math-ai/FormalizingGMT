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


-- Local definitions for Theorem 2.6
open MeasureTheory Measure Metric Set Filter ENNReal
open scoped NNReal Topology
namespace Thm26
variable {n : ℕ} {s : ℝ}
/-! ### Axiom: restriction of a regular measure to a finite-measure set is regular -/

lemma restriction_radon (μ : Measure (EuclideanSpace ℝ (Fin n))) [μ.Regular]
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : μ A < ⊤) : (μ.restrict A).Regular := by
  have hA' : μ A ≠ ⊤ := hA.ne
  exact Measure.Regular.restrict_of_measure_ne_top hA'

/-! ### Upper density and the bad set -/

/-- Upper s-density of H^s|_E at x (meaningful even for x ∉ E). -/
noncomputable def Theta_star (E : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  dimensional_upper_density ((hausdorffMeasure s).restrict E) s x

/-- Points outside E where the upper s-density of H^s|_E exceeds t. -/
def A (E : Set (EuclideanSpace ℝ (Fin n))) (t : ℝ≥0∞) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x ∈ Eᶜ | Theta_star (n := n) (s := s) E x > t}

lemma A_subset_compl {E : Set (EuclideanSpace ℝ (Fin n))} {t : ℝ≥0∞} :
    A (n := n) (s := s) E t ⊆ Eᶜ :=
  fun _ hx => hx.1
/-! ### H^s bounded by gauge sums of scale-k covers -/
/-
If for every scale k we have a cover of S by balls of radius < 1/(k+1)
    whose (2r)^d gauge sum is ≤ bound, then hausdorffMeasure d S ≤ bound.
-/
lemma hausdorffMeasure_le_of_scale_covers {d : ℝ} (hd : 0 ≤ d)
    {S : Set (EuclideanSpace ℝ (Fin n))} (bound : ℝ≥0∞)
    (h : ∀ k : ℕ,
      ∃ (T : Set (EuclideanSpace ℝ (Fin n))) (_ : T.Countable)
        (r : EuclideanSpace ℝ (Fin n) → ℝ),
        S ⊆ ⋃ x ∈ T, closedBall x (r x) ∧
        (∀ x ∈ T, r x ∈ Ioo (0 : ℝ) (1 / (↑k + 1))) ∧
        ∑' x : T, ENNReal.ofReal ((2 * r ↑x) ^ d) ≤ bound) :
    hausdorffMeasure d S ≤ bound := by
  choose T hT r hr₁ hr₂ hr₃ using h
  refine le_of_forall_gt_imp_ge_of_dense fun b hb => ?_
  have h_le_liminf := @hausdorffMeasure_le_liminf_tsum (EuclideanSpace ℝ (Fin n)) _ _ _
  contrapose! h_le_liminf
  let t_cov (k : ℕ) (i : (T k)) : Set (EuclideanSpace ℝ (Fin n)) := closedBall i (r k i)
  have h_tendsto :
      Filter.Tendsto (fun k : ℕ => ENNReal.ofReal (2 / (k + 1))) Filter.atTop (nhds 0) := by
    rw [← ENNReal.ofReal_zero]
    apply ENNReal.tendsto_ofReal
    apply Filter.Tendsto.div_atTop (tendsto_const_nhds (x := (2 : ℝ)))
    apply Filter.tendsto_atTop_add_const_right _ (1 : ℝ)
    exact tendsto_natCast_atTop_atTop
  have ediam_closedBall_le :
      ∀ C : EuclideanSpace ℝ (Fin n), ∀ ρ : ℝ, ediam (closedBall C ρ) ≤ ENNReal.ofReal (2 * ρ) := by
    intro C ρ
    apply ediam_le_of_forall_dist_le
    intro y hy z hz
    have h1 : dist y C ≤ ρ := mem_closedBall.mp hy
    have h2 : dist z C ≤ ρ := mem_closedBall.mp hz
    calc
      dist y z ≤ dist y C + dist C z := dist_triangle _ _ _
      _ = dist y C + dist z C := by rw [dist_comm C z]
      _ ≤ ρ + ρ := add_le_add h1 h2
      _ = 2 * ρ := by ring
  have h_diam : ∀ᶠ k in Filter.atTop, ∀ i : T k,
      ediam (t_cov k i) ≤ ENNReal.ofReal (2 / (k + 1)) := by
    refine Filter.Eventually.of_forall (fun k i => ?_)
    refine le_trans (ediam_closedBall_le _ _) ?_
    apply ENNReal.ofReal_le_ofReal
    have h1 : r k i < 1 / (k + 1 : ℝ) := hr₂ k i i.2 |>.2
    calc 2 * r k i ≤ 2 * (1 / (k + 1 : ℝ)) := mul_le_mul_of_nonneg_left h1.le zero_le_two
      _ = 2 / (k + 1 : ℝ) := mul_one_div 2 _
  have h_cov : ∀ᶠ k in Filter.atTop, S ⊆ ⋃ i : T k, t_cov k i := by
    refine Filter.Eventually.of_forall (fun k => ?_)
    intro x hx; simpa only [iUnion_coe_set] using hr₁ k hx
  refine ⟨ℕ, fun k => (T k), fun k => (hT k), d, S, Filter.atTop,
    (fun k => ENNReal.ofReal (2 / (k + 1))), h_tendsto, t_cov, h_diam, h_cov, ?_⟩
  apply lt_of_le_of_lt _ h_le_liminf
  have hu : IsBoundedUnder (fun x1 x2 ↦ x1 ≥ x2) Filter.atTop
    (fun k => ∑' i : T k, ediam (t_cov k i) ^ d) := ⟨0, Filter.Eventually.of_forall fun _ => bot_le⟩
  refine liminf_le_of_frequently_le (Filter.frequently_atTop.2 (fun k => ?_))
  refine ⟨k, le_rfl, le_trans ?_ (le_trans (hr₃ k) hb.le)⟩
  refine ENNReal.tsum_le_tsum (fun i => ?_)
  exact le_trans (ENNReal.rpow_le_rpow (ediam_closedBall_le _ _) hd)
    (by rw [ENNReal.ofReal_rpow_of_pos (mul_pos zero_lt_two (hr₂ k i i.2 |>.1))])
/-! ### Fine cover from upper density -/
/-! ### Fine cover from upper density -/
/-
For x ∈ A(t), there are arbitrarily small radii where H^s(E ∩ B(x,r)) > t·(2r)^s
-/
lemma fine_cover_of_mem_A
    {E : Set (EuclideanSpace ℝ (Fin n))} {t : ℝ≥0∞}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ A (n := n) (s := s) E t) :
    ∀ δ > 0, ∃ ρ ∈ Ioo (0 : ℝ) δ,
      (hausdorffMeasure s).restrict E (closedBall x ρ) >
        t * ENNReal.ofReal ((2 * ρ) ^ s) := by
  intro δ hδ;
  -- By definition of $A$, we know that $\Theta_*^s(E, x) > t$.
  have h_lim_sup : Filter.limsup (fun r => dimensional_density_ratio (μH[s].restrict E) s x r)
    (nhdsWithin 0 (Set.Ioi 0)) > t := by
    exact hx.2;
  contrapose! h_lim_sup;
  apply csInf_le
  · use 0; intro y' hy'; exact bot_le
  · filter_upwards [ Ioo_mem_nhdsGT hδ ] with ρ hρ using ENNReal.div_le_of_le_mul (by
      simpa [ mul_comm ] using h_lim_sup ρ hρ)
/-! ### A(t) has Hausdorff measure zero -/
theorem A_null (hs : 0 ≤ s)
    {E : Set (EuclideanSpace ℝ (Fin n))}
    (hE_meas : MeasurableSet E)
    (hE_fin : hausdorffMeasure s E < ⊤)
    (h_reg : (hausdorffMeasure (X := EuclideanSpace ℝ (Fin n)) s).Regular)
    {t : ℝ≥0∞} (ht : 0 < t) (ht_top : t ≠ ⊤) :
    hausdorffMeasure s (A (n := n) (s := s) E t) = 0 := by
  -- Set ν = H^s|_E. Since H^s(E) < ∞, ν is finite, hence locally finite.
  set ν := (hausdorffMeasure s).restrict E
  have hν_finite : ν (Set.univ : Set (EuclideanSpace ℝ (Fin n))) < ⊤ := by
    aesop;
  -- For any ε > 0, we show H^s(A(t)) ≤ t⁻¹ * ε using hausdorffMeasure_le_of_scale_covers.
  have h_scale_cover (ε : ℝ≥0∞) (hε : 0 < ε) : hausdorffMeasure s (A (n := n) (s := s) E t) ≤ t⁻¹ * ε := by
    -- For each scale k, use Besicovitch.exists_closedBall_covering_tsum_measure_le with ν, ε, and the fine cover from fine_cover_of_mem_A (radii where ν(B) > t*(2r)^s and r < 1/(k+1)).
    have h_scale_cover_step (k : ℕ) : ∃ (T : Set (EuclideanSpace ℝ (Fin n))) (_ : T.Countable) (r : EuclideanSpace ℝ (Fin n) → ℝ),
      A (n := n) (s := s) E t ⊆ ⋃ x ∈ T, closedBall x (r x) ∧
      (∀ x ∈ T, r x ∈ Ioo (0 : ℝ) (1 / (k + 1))) ∧
      ∑' x : T, ENNReal.ofReal ((2 * r ↑x) ^ s) ≤ t⁻¹ * ε := by
        have h_besi := @Besicovitch.exists_closedBall_covering_tsum_measure_le ( EuclideanSpace ℝ ( Fin n ) ) _ _ _ _;
        specialize h_besi ν ( show ε ≠ 0 from hε.ne' ) ( fun x => { r : ℝ | 0 < r ∧ r < 1 / ( k + 1 ) ∧ ν ( closedBall x r ) > t * ENNReal.ofReal ( ( 2 * r ) ^ s ) } ) ( A ( n := n ) ( s := s ) E t );
        -- Apply the hypothesis `h_besi` to obtain the countable set `T` and the function `r`.
        obtain ⟨T, r, hT_countable, hT_subset, hr_bounds, hT_cover, hT_sum⟩ := h_besi (by
        intro x hx δ hδ_pos
        obtain ⟨ρ, hρ_pos, hρ_lt⟩ : ∃ ρ ∈ Ioo (0 : ℝ) (min δ (1 / (k + 1))), ν (closedBall x ρ) > t * ENNReal.ofReal ((2 * ρ) ^ s) := by
          have := fine_cover_of_mem_A hx ( min δ ( 1 / ( k + 1 ) ) ) ( lt_min hδ_pos ( by positivity ) )
          aesop;
        exact ⟨ ρ, ⟨ ⟨ hρ_pos.1, hρ_pos.2.trans_le ( min_le_right _ _ ), hρ_lt ⟩, ⟨ hρ_pos.1, hρ_pos.2.trans_le ( min_le_left _ _ ) ⟩ ⟩ ⟩);
        refine ⟨ T, hT_countable, r, hT_cover, fun x hx => ⟨ hr_bounds x hx |>.1, hr_bounds x hx |>.2.1 ⟩, ?_ ⟩;
        have hT_sum_le : ∑' x : T, ν (closedBall x (r x)) ≥ t * ∑' x : T, ENNReal.ofReal ((2 * r x) ^ s) := by
          rw [ ← ENNReal.tsum_mul_left ];
          exact ENNReal.tsum_le_tsum fun x => le_of_lt ( hr_bounds x x.2 |>.2.2 );
        have hT_sum_le' : t * ∑' x : T, ENNReal.ofReal ((2 * r x) ^ s) ≤ ε := by
          refine le_trans hT_sum_le <| hT_sum.trans ?_;
          rw [ MeasureTheory.Measure.restrict_apply' ];
          · rw [ show A E t ∩ E = ∅ by exact Set.eq_empty_of_forall_notMem fun x hx => hx.1.1 hx.2 ] ; norm_num;
          · exact hE_meas;
        convert mul_le_mul_right hT_sum_le' t⁻¹ using 1;
        rw [ ← mul_assoc, ENNReal.inv_mul_cancel ht.ne' ht_top, one_mul ];
    apply hausdorffMeasure_le_of_scale_covers hs ( t⁻¹ * ε ) ; aesop;
  contrapose! h_scale_cover;
  cases' ENNReal.lt_iff_exists_nnreal_btwn.mp ( pos_iff_ne_zero.mpr h_scale_cover ) with ε hε;
  refine ⟨ t * ε, ?_, ?_ ⟩ <;> simp_all +decide [ mul_assoc, mul_comm ];
  · rw [ mul_left_comm, ENNReal.mul_inv_cancel ht.ne' ht_top, mul_one ] ; aesop
/-! ### Main theorem -/
/-
**Theorem 2.6** (Density at points not in E).
For an `s`-measurable set `E` with `H^s(E) < ∞`, and assuming `H^s` is regular,
for `H^s|_{Eᶜ}`-almost every point `x ∉ E`, the `s`-dimensional density ratio
of `H^s|_E` at `x` tends to `0` as `r → 0⁺`.
-/
theorem theorem2_6_density_at_points_not_in_E
    {E : Set (EuclideanSpace ℝ (Fin n))}
    (hE_meas : MeasurableSet E)
    (hE_fin : hausdorffMeasure s E < ⊤)
    (h_reg : (hausdorffMeasure (X := EuclideanSpace ℝ (Fin n)) s).Regular) :
    ∀ᵐ x ∂(hausdorffMeasure s).restrict Eᶜ,
      Tendsto (dimensional_density_ratio ((hausdorffMeasure s).restrict E) s x)
        (𝓝[>] 0) (𝓝 0) := by
  by_cases hs : 0 ≤ s;
  · -- For x ∈ Eᶜ, if the density ratio does not tend to 0, then upper density > 0, so there exists k with 1/(k+1) < upper density (by the Archimedean property), hence x ∈ A(1/(k+1)).
    have h_subset : {x ∈ Eᶜ | ¬Tendsto (dimensional_density_ratio (μH[s].restrict E) s x) (𝓝[>] 0) (𝓝 0)} ⊆ ⋃ k : ℕ, A (n := n) (s := s) E (1 / (k + 1) : ℝ≥0∞) := by
      intro x hx
      obtain ⟨hx_compl, hx_not_zero⟩ := hx
      have hx_upper_density : 0 < dimensional_upper_density (hausdorffMeasure s |>.restrict E) s x := by
        contrapose! hx_not_zero;
        have h_liminf : Filter.liminf (dimensional_density_ratio (hausdorffMeasure s |>.restrict E) s x) (𝓝[>] 0) = 0 := by
          exact le_antisymm ( le_trans ( lower_le_upper_density _ _ _ ) hx_not_zero ) ( lower_density_nonneg _ _ _ );
        convert tendsto_of_liminf_eq_limsup h_liminf _;
        exact le_antisymm hx_not_zero ( zero_le )
      have hx_A : ∃ k : ℕ, x ∈ A (n := n) (s := s) E (1 / (k + 1)) := by
        obtain ⟨k, hk⟩ : ∃ k : ℕ, (1 / (k + 1) : ℝ≥0∞) < dimensional_upper_density (hausdorffMeasure s |>.restrict E) s x := by
          rcases ENNReal.exists_inv_nat_lt hx_upper_density.ne' with ⟨ k, hk ⟩;
          exact ⟨ k, by simpa using hk.trans_le' <| by gcongr ; norm_num ⟩;
        exact ⟨ k, hx_compl, hk ⟩
      aesop;
    -- The union has H^s measure 0 by measure_iUnion_null and A_null.
    have h_union_null : μH[s] (⋃ k : ℕ, A (n := n) (s := s) E (1 / (k + 1) : ℝ≥0∞)) = 0 := by
      rw [ MeasureTheory.measure_iUnion_null_iff ];
      exact fun k => A_null hs hE_meas hE_fin h_reg ( by simp +decide ) ( by simp +decide );
    rw [ MeasureTheory.ae_restrict_iff' ];
    · filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h_union_null ] with x hx using fun hx' => Classical.not_not.1 fun hx'' => hx <| h_subset ⟨ hx', hx'' ⟩;
    · exact hE_meas.compl;
  · by_cases hE : E.Nonempty <;> simp_all +decide [ Set.Nonempty ];
    · obtain ⟨ x, hx ⟩ := hE;
      have := @hausdorffMeasure_zero_or_top ( EuclideanSpace ℝ ( Fin n ) );
      contrapose! this;
      refine' ⟨ inferInstance, inferInstance, inferInstance, s, 0, hs, { x }, _, _ ⟩ <;> norm_num;
      exact ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( Set.singleton_subset_iff.mpr hx ) ) hE_fin );
    · simp_all +decide [ show E = ∅ by ext; aesop ];
      unfold dimensional_density_ratio; aesop;
end Thm26

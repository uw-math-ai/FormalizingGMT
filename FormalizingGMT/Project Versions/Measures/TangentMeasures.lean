import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Covering.Differentiation
import FormalizingGMT.«Project Versions».Measures.WeakCompactness

open MeasureTheory Metric Set Filter
open Topology
open scoped ENNReal NNReal

noncomputable section

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

lemma continuous_blowUpMap (a : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    Continuous (blowUpMap a r) :=
  (continuous_id.sub continuous_const).const_smul r⁻¹

lemma measurable_blowUpMap (a : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    Measurable (blowUpMap a r) :=
  (continuous_blowUpMap a r).measurable

/-- `IsTangentMeasure μ ν a` asserts that `ν` is a tangent measure of `μ` at the point `a`:
`ν` is a nonzero Radon measure which is the weak limit of a sequence of rescaled blow-ups of `μ`
at `a` along radii tending to `0`. -/
def IsTangentMeasure
    (μ ν : Measure (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) : Prop :=
  ν.Regular ∧ ν ≠ 0 ∧
  ∃ (r : ℕ → ℝ) (c : ℕ → ℝ≥0∞),
    (∀ i, 0 < r i) ∧
    (∀ i, 0 < c i) ∧
    (∀ i, c i ≠ ∞) ∧
    Tendsto r atTop (𝓝 0) ∧
    Measure.WeaklyConverges
      (fun i ↦ c i • (μ.map (blowUpMap a (r i))))
      ν

/-! ## Elementary facts about weak convergence -/

namespace MeasureTheory

section WeakConvergenceFacts

variable {n : ℕ}

/-- Weak convergence is inherited by subsequences (more generally, by any reindexing along a
map tending to infinity). -/
lemma Measure.WeaklyConverges.comp
    {μ : ℕ → Measure (EuclideanSpace ℝ (Fin n))}
    {ν : Measure (EuclideanSpace ℝ (Fin n))}
    (h : Measure.WeaklyConverges μ ν) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) :
    Measure.WeaklyConverges (fun j ↦ μ (φ j)) ν :=
  fun f ↦ (h f).comp hφ

/-- Rescaling a weakly convergent sequence by constants tending to `1` does not change the
weak limit. -/
lemma Measure.WeaklyConverges.smul_of_tendsto_one
    {μ : ℕ → Measure (EuclideanSpace ℝ (Fin n))}
    {ν : Measure (EuclideanSpace ℝ (Fin n))}
    (h : Measure.WeaklyConverges μ ν) {e : ℕ → ℝ≥0∞}
    (he1 : Tendsto (fun i ↦ (e i).toReal) atTop (𝓝 1)) :
    Measure.WeaklyConverges (fun i ↦ e i • μ i) ν := by
  intro f
  have hint : ∀ i, ∫ x, f x ∂(e i • μ i) = (e i).toReal * ∫ x, f x ∂(μ i) := by
    intro i
    rw [integral_smul_measure, smul_eq_mul]
  simp only [hint]
  simpa using he1.mul (h f)

/-- Weak convergence only depends on the underlying sequence of measures. -/
lemma Measure.WeaklyConverges.congr_seq
    {F G : ℕ → Measure (EuclideanSpace ℝ (Fin n))}
    {ν : Measure (EuclideanSpace ℝ (Fin n))}
    (hFG : ∀ i, F i = G i)
    (h : Measure.WeaklyConverges G ν) :
    Measure.WeaklyConverges F ν := by
  rw [funext hFG]
  exact h

end WeakConvergenceFacts

end MeasureTheory

/-! ## Extracting a strictly decreasing sequence of radii -/

/-- A positive sequence tending to `0` has a strictly decreasing subsequence. -/
lemma exists_strictMono_strictAnti_subseq {r : ℕ → ℝ} (hpos : ∀ i, 0 < r i)
    (hr : Tendsto r atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ StrictAnti (fun j ↦ r (φ j)) := by
  have hstep : ∀ m : ℕ, ∃ k, m < k ∧ r k < r m := by
    intro m
    have h1 : ∀ᶠ k in atTop, r k < r m := hr.eventually_lt_const (hpos m)
    have h2 : ∀ᶠ k in atTop, m < k := eventually_gt_atTop m
    exact (h2.and h1).exists
  choose next hnext1 hnext2 using hstep
  refine ⟨fun j ↦ Nat.rec 0 (fun _ m ↦ next m) j, strictMono_nat_of_lt_succ (fun j ↦ ?_),
    strictAnti_nat_of_succ_lt (fun j ↦ ?_)⟩
  · exact hnext1 _
  · exact hnext2 _

/-! ## Basic properties of the blow-up maps -/

section BlowUp

variable {n : ℕ}

lemma blowUpMap_preimage_ball (a : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) (ρ : ℝ) :
    blowUpMap a r ⁻¹' (ball 0 ρ) = ball a (r * ρ) := by
  ext x
  simp only [blowUpMap, mem_preimage, mem_ball, dist_eq_norm]
  rw [sub_zero, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr, inv_mul_lt_iff₀ hr]

lemma blowUpMap_preimage_closedBall (a : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (ρ : ℝ) :
    blowUpMap a r ⁻¹' (closedBall 0 ρ) = closedBall a (r * ρ) := by
  ext x
  simp only [blowUpMap, mem_preimage, mem_closedBall, dist_eq_norm]
  rw [sub_zero, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr, inv_mul_le_iff₀ hr]

/-- The blow-up map as a homeomorphism of Euclidean space. -/
def blowUpHomeomorph (a : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : r ≠ 0) :
    EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  (Homeomorph.subRight a).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr))

/-- The push-forward of a Radon measure under a blow-up map is a Radon measure. -/
lemma regular_map_blowUp {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (hμ : μ.Regular) (a : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : r ≠ 0) :
    (μ.map (blowUpMap a r)).Regular := by
  letI : μ.Regular := hμ
  have hmap : μ.map (blowUpMap a r) = μ.map ⇑(blowUpHomeomorph a hr) := rfl
  rw [hmap]
  exact Measure.Regular.map (blowUpHomeomorph a hr)

/-- A finite rescaling of the push-forward of a Radon measure under a blow-up map is again a
Radon measure. -/
lemma regular_smul_map_blowUp {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (hμ : μ.Regular) (a : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : r ≠ 0) {c : ℝ≥0∞}
    (hc : c ≠ ∞) :
    (c • μ.map (blowUpMap a r)).Regular := by
  letI : (μ.map (blowUpMap a r)).Regular := regular_map_blowUp hμ a hr
  exact Measure.Regular.smul hc

lemma map_blowUp_apply_ball (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) (ρ : ℝ) :
    (μ.map (blowUpMap a r)) (ball 0 ρ) = μ (ball a (r * ρ)) := by
  rw [Measure.map_apply (measurable_blowUpMap a r) measurableSet_ball,
    blowUpMap_preimage_ball a hr]

lemma map_blowUp_apply_closedBall (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) (ρ : ℝ) :
    (μ.map (blowUpMap a r)) (closedBall 0 ρ) = μ (closedBall a (r * ρ)) := by
  rw [Measure.map_apply (measurable_blowUpMap a r) measurableSet_closedBall,
    blowUpMap_preimage_closedBall a hr]

end BlowUp

/-! ## Balls of positive and finite measure -/

section Balls

variable {n : ℕ}

lemma measure_ball_pos_of_mem_support {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {a : EuclideanSpace ℝ (Fin n)} (ha : a ∈ μ.support) {ρ : ℝ} (hρ : 0 < ρ) :
    0 < μ (ball a ρ) :=
  (Measure.mem_support_iff_forall a).mp ha _ (ball_mem_nhds a hρ)

lemma regular_measure_closedBall_lt_top {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (hμ : μ.Regular) (a : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) :
    μ (closedBall a ρ) < ∞ := by
  letI : μ.Regular := hμ
  exact (isCompact_closedBall a ρ).measure_lt_top

lemma regular_measure_ball_lt_top {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (hμ : μ.Regular) (a : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) :
    μ (ball a ρ) < ∞ :=
  lt_of_le_of_lt (measure_mono ball_subset_closedBall)
    (regular_measure_closedBall_lt_top hμ a ρ)

end Balls

/-! ## Consequences of the doubling assumption 14.3 (1) -/

section Doubling

variable {n : ℕ}

/-- Assumption 14.3 (1) gives a genuine doubling inequality at small scales. -/
lemma exists_doubling_constant {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (hμ : μ.Regular) {a : EuclideanSpace ℝ (Fin n)}
    (ha : a ∈ μ.support)
    (hdoub : limsup (fun ρ : ℝ ↦ μ (ball a (2 * ρ)) / μ (ball a ρ)) (𝓝[>] (0 : ℝ)) < ∞) :
    ∃ C : ℝ≥0∞, 1 ≤ C ∧ C ≠ ∞ ∧ ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < r₀ → μ (ball a (2 * ρ)) ≤ C * μ (ball a ρ) := by
  set L := limsup (fun ρ : ℝ ↦ μ (ball a (2 * ρ)) / μ (ball a ρ)) (𝓝[>] (0 : ℝ)) with hL
  refine ⟨L + 1, le_add_self, by simp [ENNReal.add_eq_top, hdoub.ne], ?_⟩
  have hlt : L < L + 1 := ENNReal.lt_add_right hdoub.ne one_ne_zero
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      μ (ball a (2 * ρ)) / μ (ball a ρ) < L + 1 := eventually_lt_of_limsup_lt hlt
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hh⟩ := hev
  refine ⟨ε, hε, fun ρ hρ hρε ↦ ?_⟩
  have hmem : dist ρ 0 < ε := by
    rwa [Real.dist_eq, sub_zero, abs_of_pos hρ]
  have hdiv := hh hmem hρ
  have hpos : μ (ball a ρ) ≠ 0 := (measure_ball_pos_of_mem_support ha hρ).ne'
  have hfin : μ (ball a ρ) ≠ ∞ := (regular_measure_ball_lt_top hμ a ρ).ne
  exact ((ENNReal.div_lt_iff (Or.inl hpos) (Or.inl hfin)).mp hdiv).le

/-- Iterating the doubling inequality. -/
lemma measure_ball_two_pow_le {μ : Measure (EuclideanSpace ℝ (Fin n))}
    {a : EuclideanSpace ℝ (Fin n)}
    {C : ℝ≥0∞} {r₀ : ℝ}
    (hC : ∀ ρ : ℝ, 0 < ρ → ρ < r₀ → μ (ball a (2 * ρ)) ≤ C * μ (ball a ρ)) (k : ℕ) :
    ∀ ρ : ℝ, 0 < ρ → 2 ^ k * ρ < r₀ → μ (ball a (2 ^ k * ρ)) ≤ C ^ k * μ (ball a ρ) := by
  induction k with
  | zero => intro ρ _ _; simp
  | succ k ih =>
    intro ρ hρ hlt
    have hpow : (0 : ℝ) < 2 ^ k := by positivity
    have hstep : (2 : ℝ) ^ k * ρ < r₀ := by
      refine lt_of_le_of_lt ?_ hlt
      have : (2 : ℝ) ^ k ≤ 2 ^ (k + 1) := by
        apply pow_le_pow_right₀ (by norm_num) (by omega)
      nlinarith
    have hrad : (2 : ℝ) ^ (k + 1) * ρ = 2 * (2 ^ k * ρ) := by ring
    calc μ (ball a (2 ^ (k + 1) * ρ)) = μ (ball a (2 * (2 ^ k * ρ))) := by rw [hrad]
      _ ≤ C * μ (ball a (2 ^ k * ρ)) := hC _ (by positivity) hstep
      _ ≤ C * (C ^ k * μ (ball a ρ)) := by gcongr; exact ih ρ hρ hstep
      _ = C ^ (k + 1) * μ (ball a ρ) := by ring

/-- Under assumption 14.3 (1), balls of comparable radii have comparable measures, uniformly
at small scales. -/
lemma exists_measure_ball_le_measure_ball {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (hμ : μ.Regular) {a : EuclideanSpace ℝ (Fin n)}
    (ha : a ∈ μ.support)
    (hdoub : limsup (fun ρ : ℝ ↦ μ (ball a (2 * ρ)) / μ (ball a ρ)) (𝓝[>] (0 : ℝ)) < ∞)
    (t : ℝ) :
    ∃ D : ℝ≥0∞, 1 ≤ D ∧ D ≠ ∞ ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ → μ (ball a (t * ρ)) ≤ D * μ (ball a ρ) := by
  obtain ⟨C, hC1, hCtop, r₀, hr₀, hC⟩ := exists_doubling_constant hμ ha hdoub
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (y := (2 : ℝ)) t (by norm_num)
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  refine ⟨C ^ k, one_le_pow₀ hC1, by simp [ENNReal.pow_eq_top_iff, hCtop], r₀ / 2 ^ k,
    by positivity, fun ρ hρ hρ0 ↦ ?_⟩
  have hlt : (2 : ℝ) ^ k * ρ < r₀ := by
    rw [lt_div_iff₀ hpow] at hρ0
    nlinarith
  calc μ (ball a (t * ρ)) ≤ μ (ball a (2 ^ k * ρ)) := by
        refine measure_mono (ball_subset_ball ?_)
        nlinarith
    _ ≤ C ^ k * μ (ball a ρ) := measure_ball_two_pow_le hC k ρ hρ hlt

end Doubling

/-! ## The normalizing constants of a tangent measure -/

section Normalization

variable {n : ℕ}

/-- Upper bound for the normalizing constants: the numbers `c i * μ (B (a, r i))` are
bounded above. -/
lemma limsup_normalizing_le {μ ν : Measure (EuclideanSpace ℝ (Fin n))}
    (hμ : μ.Regular) (hν : ν.Regular) {a : EuclideanSpace ℝ (Fin n)} {r : ℕ → ℝ}
    {c : ℕ → ℝ≥0∞} (hr : ∀ i, 0 < r i) (hc : ∀ i, c i ≠ ∞)
    (hconv : Measure.WeaklyConverges
      (fun i ↦ c i • μ.map (blowUpMap a (r i))) ν) :
    limsup (fun i ↦ c i * μ (closedBall a (r i))) atTop ≤ ν (closedBall 0 1) := by
  have hb := (Measure.weaklyConverges_iff_compactOpenBounds _ ν
    (fun i ↦ regular_smul_map_blowUp hμ a (hr i).ne' (hc i)) hν).mp hconv
  have h1 := hb.1 (closedBall 0 1) (isCompact_closedBall _ _)
  have heq : ∀ i, (c i • μ.map (blowUpMap a (r i))) (closedBall 0 1)
      = c i * μ (closedBall a (r i)) := by
    intro i
    rw [Measure.smul_apply, smul_eq_mul, map_blowUp_apply_closedBall μ a (hr i), mul_one]
  simpa only [heq] using h1

/-- Lower bound for the normalizing constants: under assumption 14.3 (1) the numbers
`c i * μ (B (a, r i))` are eventually bounded away from `0`. -/
lemma exists_le_normalizing {μ ν : Measure (EuclideanSpace ℝ (Fin n))}
    (hμ : μ.Regular) (hν : ν.Regular) {a : EuclideanSpace ℝ (Fin n)}
    (ha : a ∈ μ.support)
    (hdoub : limsup (fun ρ : ℝ ↦ μ (ball a (2 * ρ)) / μ (ball a ρ)) (𝓝[>] (0 : ℝ)) < ∞)
    {r : ℕ → ℝ} {c : ℕ → ℝ≥0∞} (hr : ∀ i, 0 < r i) (hc : ∀ i, c i ≠ ∞)
    (hr0 : Tendsto r atTop (𝓝 0)) (hν0 : ν ≠ 0)
    (hconv : Measure.WeaklyConverges
      (fun i ↦ c i • μ.map (blowUpMap a (r i))) ν) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ᶠ i in atTop, δ ≤ c i * μ (ball a (r i)) := by
  obtain ⟨R, hR1, hRpos⟩ : ∃ R : ℝ, 1 ≤ R ∧ 0 < ν (ball 0 R) := by
    by_contra hcon
    push_neg at hcon
    apply hν0
    have hz : ∀ k : ℕ, ν (ball 0 ((k : ℝ) + 1)) = 0 := by
      intro k
      have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by
        have := Nat.cast_nonneg (α := ℝ) k
        linarith
      exact le_antisymm (hcon _ hk) (zero_le)
    have hsub : (univ : Set (EuclideanSpace ℝ (Fin n))) ⊆ ⋃ k : ℕ, ball 0 ((k : ℝ) + 1) := by
      intro x _
      obtain ⟨k, hk⟩ := exists_nat_gt (dist x 0)
      exact mem_iUnion.2 ⟨k, by simp only [mem_ball]; linarith⟩
    have huniv : ν univ = 0 :=
      le_antisymm ((measure_mono hsub).trans_eq (measure_iUnion_null hz)) (zero_le)
    exact Measure.measure_univ_eq_zero.mp huniv
  have hfin : ν (ball 0 R) ≠ ∞ := (regular_measure_ball_lt_top hν 0 R).ne
  have hb := (Measure.weaklyConverges_iff_compactOpenBounds _ ν
    (fun i ↦ regular_smul_map_blowUp hμ a (hr i).ne' (hc i)) hν).mp hconv
  have hopen := hb.2 (ball 0 R) isOpen_ball
  have heq : ∀ i, (c i • μ.map (blowUpMap a (r i))) (ball 0 R)
      = c i * μ (ball a (r i * R)) := by
    intro i
    rw [Measure.smul_apply, smul_eq_mul, map_blowUp_apply_ball μ a (hr i)]
  have hopen' : ν (ball 0 R) ≤ liminf (fun i ↦ c i * μ (ball a (r i * R))) atTop := by
    simpa only [heq] using hopen
  have hhalf : ν (ball 0 R) / 2 < ν (ball 0 R) := ENNReal.half_lt_self hRpos.ne' hfin
  have hev1 : ∀ᶠ i in atTop, ν (ball 0 R) / 2 < c i * μ (ball a (r i * R)) :=
    eventually_lt_of_lt_liminf (lt_of_lt_of_le hhalf hopen')
  obtain ⟨D, hD1, hDtop, ρ₀, hρ₀, hD⟩ := exists_measure_ball_le_measure_ball hμ ha hdoub R
  have hev2 : ∀ᶠ i in atTop, r i < ρ₀ := hr0.eventually_lt_const hρ₀
  have hDne : D ≠ 0 := (lt_of_lt_of_le zero_lt_one hD1).ne'
  refine ⟨ν (ball 0 R) / 2 / D,
    ENNReal.div_pos_iff.2 ⟨(ENNReal.half_pos hRpos.ne').ne', hDtop⟩, ?_⟩
  filter_upwards [hev1, hev2] with i h1 h2
  have hcomp : μ (ball a (r i * R)) ≤ D * μ (ball a (r i)) := by
    have := hD (r i) (hr i) h2
    rwa [mul_comm R (r i)] at this
  have hkey : ν (ball 0 R) / 2 ≤ (c i * μ (ball a (r i))) * D := by
    refine le_of_lt (lt_of_lt_of_le h1 ?_)
    calc c i * μ (ball a (r i * R)) ≤ c i * (D * μ (ball a (r i))) := by gcongr
      _ = (c i * μ (ball a (r i))) * D := by ring
  exact (ENNReal.div_le_iff_le_mul (Or.inl hDne) (Or.inl hDtop)).2 hkey

end Normalization

/-! ## Consequence (2): the origin belongs to the support of every tangent measure -/

/-- **Mattila, Chapter 14, consequence (2) of assumption 14.3 (1).**
If `μ` is a Radon measure on `ℝⁿ`, `a ∈ spt μ` satisfies
`limsup_{ρ ↓ 0} μ (B (a, 2ρ)) / μ (B (a, ρ)) < ∞`, then `0 ∈ spt ν` for every tangent
measure `ν ∈ Tan (μ, a)`. -/
theorem zero_mem_support_of_isTangentMeasure {n : ℕ}
    (μ ν : Measure (EuclideanSpace ℝ (Fin n))) (hμ : μ.Regular)
    (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ μ.support)
    (hdoub : limsup (fun ρ : ℝ ↦ μ (ball a (2 * ρ)) / μ (ball a ρ)) (𝓝[>] (0 : ℝ)) < ∞)
    (htan : IsTangentMeasure μ ν a) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈ ν.support := by
  obtain ⟨hν, hν0, r, c, hr, hcpos, hcfin, hr0, hconv⟩ := htan
  have key : ∀ s : ℝ, 0 < s → 0 < ν (closedBall 0 s) := by
    intro s hs
    obtain ⟨δ, hδ, hδev⟩ := exists_le_normalizing hμ hν ha hdoub hr hcfin hr0 hν0 hconv
    obtain ⟨D, hD1, hDtop, ρ₀, hρ₀, hD⟩ :=
      exists_measure_ball_le_measure_ball hμ ha hdoub (max 1 s⁻¹)
    have hDne : D ≠ 0 := (lt_of_lt_of_le zero_lt_one hD1).ne'
    have hts : (1 : ℝ) ≤ max 1 s⁻¹ * s := by
      rcases le_or_gt 1 s with h | h
      · calc (1 : ℝ) ≤ s := h
          _ ≤ max 1 s⁻¹ * s := le_mul_of_one_le_left hs.le (le_max_left _ _)
      · have hinv : s⁻¹ ≤ max 1 s⁻¹ := le_max_right _ _
        have : (1 : ℝ) = s⁻¹ * s := by field_simp
        nlinarith
    have hev2 : ∀ᶠ i in atTop, r i * s < ρ₀ := by
      have h0 : Tendsto (fun i ↦ r i * s) atTop (𝓝 0) := by simpa using hr0.mul_const s
      exact h0.eventually_lt_const hρ₀
    have hbound : ∀ᶠ i in atTop, δ / D ≤ c i * μ (closedBall a (r i * s)) := by
      filter_upwards [hδev, hev2] with i h1 h2
      have hcomp : μ (ball a (r i)) ≤ D * μ (ball a (r i * s)) := by
        refine le_trans (measure_mono (ball_subset_ball ?_)) (hD (r i * s) (mul_pos (hr i) hs) h2)
        nlinarith [hr i]
      have hstep : δ ≤ (c i * μ (closedBall a (r i * s))) * D := by
        refine h1.trans ?_
        calc c i * μ (ball a (r i)) ≤ c i * (D * μ (ball a (r i * s))) := by gcongr
          _ = (c i * μ (ball a (r i * s))) * D := by ring
          _ ≤ (c i * μ (closedBall a (r i * s))) * D := by
              gcongr
              exact ball_subset_closedBall
      exact (ENNReal.div_le_iff_le_mul (Or.inl hDne) (Or.inl hDtop)).2 hstep
    have hb := (Measure.weaklyConverges_iff_compactOpenBounds _ ν
      (fun i ↦ regular_smul_map_blowUp hμ a (hr i).ne' (hcfin i)) hν).mp hconv
    have h1 := hb.1 (closedBall 0 s) (isCompact_closedBall _ _)
    have heq : ∀ i, (c i • μ.map (blowUpMap a (r i))) (closedBall 0 s)
        = c i * μ (closedBall a (r i * s)) := by
      intro i
      rw [Measure.smul_apply, smul_eq_mul, map_blowUp_apply_closedBall μ a (hr i)]
    have hlimsup : δ / D ≤ limsup (fun i ↦ c i * μ (closedBall a (r i * s))) atTop :=
      le_limsup_of_frequently_le hbound.frequently
    refine lt_of_lt_of_le (ENNReal.div_pos_iff.2 ⟨hδ.ne', hDtop⟩) ?_
    exact hlimsup.trans (by simpa only [heq] using h1)
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine lt_of_lt_of_le (key (ρ / 2) (by positivity)) (measure_mono ?_)
  exact (closedBall_subset_ball (by linarith)).trans hball

/-! ## Consequence (3): tangent measures arise from the canonical normalizations -/

/-- **Mattila, Chapter 14, consequence (3) of assumption 14.3 (1).**
If `μ` is a Radon measure on `ℝⁿ` and `a ∈ spt μ` satisfies
`limsup_{ρ ↓ 0} μ (B (a, 2ρ)) / μ (B (a, ρ)) < ∞`, then every tangent measure
`ν ∈ Tan (μ, a)` can be written as
`ν = c · lim_i μ (B (a, r i))⁻¹ • T_{a, r i #} μ`
for a strictly decreasing sequence of radii `r i ↓ 0` and a positive finite constant `c`. -/
theorem exists_normalized_blowUp_weaklyConverges_of_isTangentMeasure {n : ℕ}
    (μ ν : Measure (EuclideanSpace ℝ (Fin n))) (hμ : μ.Regular)
    (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ μ.support)
    (hdoub : limsup (fun ρ : ℝ ↦ μ (ball a (2 * ρ)) / μ (ball a ρ)) (𝓝[>] (0 : ℝ)) < ∞)
    (htan : IsTangentMeasure μ ν a) :
    ∃ (r : ℕ → ℝ) (c : ℝ≥0∞),
      (∀ i, 0 < r i) ∧ StrictAnti r ∧ Tendsto r atTop (𝓝 0) ∧ 0 < c ∧ c ≠ ∞ ∧
        Measure.WeaklyConverges
          (fun i ↦ c • (μ (ball a (r i)))⁻¹ • μ.map (blowUpMap a (r i))) ν := by
  obtain ⟨hν, hν0, r, c, hr, hcpos, hcfin, hr0, hconv⟩ := htan
  set T : ℕ → ℝ≥0∞ := fun i ↦ c i * μ (ball a (r i))
  obtain ⟨δ, hδ, hδev⟩ := exists_le_normalizing hμ hν ha hdoub hr hcfin hr0 hν0 hconv
  have hMfin : ν (closedBall 0 1) ≠ ∞ := (regular_measure_closedBall_lt_top hν 0 1).ne
  have hlimsupT : limsup T atTop ≤ ν (closedBall 0 1) := by
    refine le_trans (limsup_le_limsup (.of_forall fun i ↦ ?_))
      (limsup_normalizing_le hμ hν hr hcfin hconv)
    change c i * μ (ball a (r i)) ≤ c i * μ (closedBall a (r i))
    gcongr
    exact ball_subset_closedBall
  have hMev : ∀ᶠ i in atTop, T i < ν (closedBall 0 1) + 1 :=
    eventually_lt_of_limsup_lt
      (lt_of_le_of_lt hlimsupT (ENNReal.lt_add_right hMfin one_ne_zero))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hδev.and hMev)
  obtain ⟨t, -, φ, hφ, htend⟩ :=
    (isCompact_univ (X := ℝ≥0∞)).tendsto_subseq (x := fun j ↦ T (j + N)) (fun j ↦ mem_univ _)
  have hidx : Tendsto (fun j ↦ φ j + N) atTop atTop :=
    (tendsto_add_atTop_nat N).comp hφ.tendsto_atTop
  obtain ⟨ψ, hψ, hanti⟩ :=
    exists_strictMono_strictAnti_subseq (r := fun j ↦ r (φ j + N)) (fun j ↦ hr _)
      (hr0.comp hidx)
  set χ : ℕ → ℕ := fun j ↦ φ (ψ j) + N
  have hχ : Tendsto χ atTop atTop := hidx.comp hψ.tendsto_atTop
  have hTχ : Tendsto (fun j ↦ T (χ j)) atTop (𝓝 t) := htend.comp hψ.tendsto_atTop
  have hNle : ∀ j, N ≤ χ j := fun j ↦ Nat.le_add_left N _
  have hδt : δ ≤ t := ge_of_tendsto' hTχ (fun j ↦ (hN _ (hNle j)).1)
  have ht0 : 0 < t := lt_of_lt_of_le hδ hδt
  have httop : t ≠ ∞ := by
    have hle : t ≤ ν (closedBall 0 1) + 1 := le_of_tendsto' hTχ (fun j ↦ (hN _ (hNle j)).2.le)
    exact ne_top_of_le_ne_top (by simp [ENNReal.add_eq_top, hMfin]) hle
  have hTpos : ∀ j, T (χ j) ≠ 0 := fun j ↦ (lt_of_lt_of_le hδ (hN _ (hNle j)).1).ne'
  have he_top : ∀ j, t / T (χ j) ≠ ∞ := fun j ↦ (ENNReal.div_lt_top httop (hTpos j)).ne
  have hsmul_eq : ∀ j,
      t • (μ (ball a (r (χ j))))⁻¹ • μ.map (blowUpMap a (r (χ j)))
        = (t / T (χ j)) • (c (χ j) • μ.map (blowUpMap a (r (χ j)))) := by
    intro j
    have hc0 : c (χ j) ≠ 0 := (hcpos _).ne'
    have hctop : c (χ j) ≠ ∞ := hcfin _
    have hscalar : t / T (χ j) * c (χ j) = t * (μ (ball a (r (χ j))))⁻¹ := by
      have hTval : T (χ j) = c (χ j) * μ (ball a (r (χ j))) := rfl
      rw [hTval]
      calc t / (c (χ j) * μ (ball a (r (χ j)))) * c (χ j)
          = t * ((c (χ j) * μ (ball a (r (χ j))))⁻¹ * c (χ j)) := by
            rw [div_eq_mul_inv, mul_assoc]
        _ = t * ((c (χ j))⁻¹ * (μ (ball a (r (χ j))))⁻¹ * c (χ j)) := by
            rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop)]
        _ = t * ((μ (ball a (r (χ j))))⁻¹ * ((c (χ j))⁻¹ * c (χ j))) := by ring
        _ = t * (μ (ball a (r (χ j))))⁻¹ := by
            rw [ENNReal.inv_mul_cancel hc0 hctop, mul_one]
    rw [smul_smul, smul_smul, hscalar]
  refine ⟨fun j ↦ r (χ j), t, fun j ↦ hr _, hanti, hr0.comp hχ, ht0, httop, ?_⟩
  have hsub : Measure.WeaklyConverges
      (fun j ↦ c (χ j) • μ.map (blowUpMap a (r (χ j)))) ν := hconv.comp hχ
  have htoReal : Tendsto (fun j ↦ (T (χ j)).toReal) atTop (𝓝 t.toReal) :=
    (ENNReal.tendsto_toReal httop).comp hTχ
  have htr : t.toReal ≠ 0 := by
    simp [ENNReal.toReal_eq_zero_iff, ht0.ne', httop]
  have hetend : Tendsto (fun j ↦ (t / T (χ j)).toReal) atTop (𝓝 1) := by
    have hdiv : Tendsto (fun j ↦ t.toReal / (T (χ j)).toReal) atTop (𝓝 (t.toReal / t.toReal)) :=
      tendsto_const_nhds.div htoReal htr
    rw [div_self htr] at hdiv
    simpa only [ENNReal.toReal_div] using hdiv
  exact Measure.WeaklyConverges.congr_seq hsmul_eq
    (hsub.smul_of_tendsto_one hetend)

/-! ## Theorem 14.3: existence of tangent measures -/

/-- **Mattila, Theorem 14.3.**
Let `μ` be a Radon measure on `ℝⁿ` and let `a ∈ spt μ` satisfy assumption (1),
`limsup_{ρ ↓ 0} μ (B (a, 2ρ)) / μ (B (a, ρ)) < ∞`. Then every sequence of radii `r i ↓ 0` has a
subsequence along which the normalized blow-ups `μ (B (a, r i))⁻¹ T_{a, r i #} μ` converge
weakly to a tangent measure of `μ` at `a`. -/
theorem exists_subseq_blowUp_weaklyConverges_tangentMeasure {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : μ.Regular)
    (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ μ.support)
    (hc : limsup (fun ρ : ℝ ↦ μ (ball a (2 * ρ)) / μ (ball a ρ)) (𝓝[>] (0 : ℝ)) < ∞)
    (r : ℕ → ℝ) (hr_pos : ∀ i, 0 < r i) (hr : Tendsto r atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ) (ν : Measure (EuclideanSpace ℝ (Fin n))),
      StrictMono φ ∧ IsTangentMeasure μ ν a ∧
        Measure.WeaklyConverges
          (fun j ↦ (μ (ball a (r (φ j))))⁻¹ • μ.map (blowUpMap a (r (φ j)))) ν := by
  have hball_pos : ∀ i, μ (ball a (r i)) ≠ 0 := fun i ↦
    (measure_ball_pos_of_mem_support ha (hr_pos i)).ne'
  have hball_top : ∀ i, μ (ball a (r i)) ≠ ∞ := fun i ↦
    (regular_measure_ball_lt_top hμ a (r i)).ne
  set σ : ℕ → Measure (EuclideanSpace ℝ (Fin n)) :=
    fun i ↦ (μ (ball a (r i)))⁻¹ • μ.map (blowUpMap a (r i))
  have hσ : ∀ i, (σ i).Regular := fun i ↦
    regular_smul_map_blowUp hμ a (hr_pos i).ne' (ENNReal.inv_ne_top.2 (hball_pos i))
  have hclosed : ∀ (i : ℕ) (s : ℝ), σ i (closedBall 0 s)
      = (μ (ball a (r i)))⁻¹ * μ (closedBall a (r i * s)) := by
    intro i s
    change ((μ (ball a (r i)))⁻¹ • μ.map (blowUpMap a (r i))) (closedBall 0 s) = _
    rw [Measure.smul_apply, smul_eq_mul, map_blowUp_apply_closedBall μ a (hr_pos i)]
  have hbound : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      ∃ C : ℝ≥0, ∀ k, σ k K ≤ C := by
    intro K hK
    obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
    set R := max 1 R₀
    have hR1 : (1 : ℝ) ≤ R := le_max_left _ _
    have hKR : K ⊆ closedBall 0 R :=
      hR₀.trans (closedBall_subset_closedBall (le_max_right _ _))
    have hfin : ∀ k, σ k (closedBall 0 R) ≠ ∞ := by
      intro k
      rw [hclosed k R]
      exact (ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 (hball_pos k)))
        (regular_measure_closedBall_lt_top hμ a _)).ne
    obtain ⟨D, hD1, hDtop, ρ₀, hρ₀, hD⟩ := exists_measure_ball_le_measure_ball hμ ha hc (2 * R)
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hr.eventually_lt_const hρ₀)
    have htail : ∀ k, N ≤ k → σ k K ≤ D := by
      intro k hk
      have hsub : closedBall a (r k * R) ⊆ ball a (2 * R * r k) := by
        refine closedBall_subset_ball ?_
        nlinarith [hr_pos k]
      calc σ k K ≤ σ k (closedBall 0 R) := measure_mono hKR
        _ = (μ (ball a (r k)))⁻¹ * μ (closedBall a (r k * R)) := hclosed k R
        _ ≤ (μ (ball a (r k)))⁻¹ * μ (ball a (2 * R * r k)) := by gcongr
        _ ≤ (μ (ball a (r k)))⁻¹ * (D * μ (ball a (r k))) := by
            gcongr
            exact hD (r k) (hr_pos k) (hN k hk)
        _ = D * ((μ (ball a (r k)))⁻¹ * μ (ball a (r k))) := by ring
        _ = D := by rw [ENNReal.inv_mul_cancel (hball_pos k) (hball_top k), mul_one]
    refine ⟨max D.toNNReal ((Finset.range N).sup fun k ↦ (σ k (closedBall 0 R)).toNNReal),
      fun k ↦ ?_⟩
    rcases le_or_gt N k with hk | hk
    · refine (htail k hk).trans ?_
      calc D = (D.toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal hDtop).symm
        _ ≤ _ := by exact_mod_cast le_max_left _ _
    · refine (measure_mono hKR).trans ?_
      calc σ k (closedBall 0 R) = ((σ k (closedBall 0 R)).toNNReal : ℝ≥0∞) :=
            (ENNReal.coe_toNNReal (hfin k)).symm
        _ ≤ _ := by
            exact_mod_cast le_max_of_le_right
              (Finset.le_sup (f := fun k ↦ (σ k (closedBall 0 R)).toNNReal)
                (Finset.mem_range.2 hk))
  obtain ⟨φ, ν, hφ, hν_regular, hconv⟩ :=
    exists_vaguelyConvergent_subseq_of_compact_bounded σ hbound
  have hν0 : ν ≠ 0 := by
    have hb := (Measure.weaklyConverges_iff_compactOpenBounds _ ν
      (fun j ↦ hσ (φ j)) hν_regular).mp hconv
    have h1 := hb.1 (closedBall 0 1) (isCompact_closedBall _ _)
    have hge : ∀ j, (1 : ℝ≥0∞) ≤ σ (φ j) (closedBall 0 1) := by
      intro j
      rw [hclosed (φ j) 1, mul_one]
      calc (1 : ℝ≥0∞) = (μ (ball a (r (φ j))))⁻¹ * μ (ball a (r (φ j))) :=
            (ENNReal.inv_mul_cancel (hball_pos _) (hball_top _)).symm
        _ ≤ (μ (ball a (r (φ j))))⁻¹ * μ (closedBall a (r (φ j))) := by
            gcongr
            exact ball_subset_closedBall
    have hone : (1 : ℝ≥0∞) ≤ ν (closedBall 0 1) :=
      le_trans (le_limsup_of_frequently_le (Frequently.of_forall hge)) h1
    intro h0
    rw [h0] at hone
    simp at hone
  refine ⟨φ, ν, hφ, ?_, hconv⟩
  exact ⟨hν_regular, hν0, fun j ↦ r (φ j), fun j ↦ (μ (ball a (r (φ j))))⁻¹,
    fun j ↦ hr_pos _, fun j ↦ ENNReal.inv_pos.2 (hball_top _),
    fun j ↦ ENNReal.inv_ne_top.2 (hball_pos _), hr.comp hφ.tendsto_atTop, hconv⟩

/-! ## Auxiliary material for Lemmas 14.5 and 14.6 -/

section TangentAux

variable {n : ℕ}

/-- A positive sequence converging to `0` converges to `0` from the right. -/
lemma tendsto_nhdsGT_zero_of_pos {u : ℕ → ℝ} (hpos : ∀ i, 0 < u i)
    (h0 : Tendsto u atTop (𝓝 0)) : Tendsto u atTop (𝓝[>] (0 : ℝ)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h0 (Eventually.of_forall hpos)

/-- The integral of a compactly supported continuous function against a measure which is finite
on the support is bounded by the supremum norm times the measure of the support. -/
lemma norm_integral_cc_le {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (M : Measure X) (f : CompactlySupportedContinuousMap X ℝ) {K : Set X}
    (hK : tsupport f ⊆ K) (hfin : M K < ∞) :
    ‖∫ x, f x ∂M‖ ≤ ‖f.toBoundedContinuousFunction‖ * (M K).toReal := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K)
    (fun x hx ↦ image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hK h)))]
  simpa [Measure.real] using
    norm_setIntegral_le_of_norm_le_const (μ := M) (s := K) hfin
      (fun x _ ↦ f.toBoundedContinuousFunction.norm_coe_le_norm x)

/-- If two sequences of Radon measures have asymptotically the same integrals against
compactly supported continuous functions, then they have the same weak limits. -/
lemma weaklyConverges_of_tendsto_integral_sub
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    {F G : ℕ → Measure X} {ν : Measure X}
    (h : Measure.WeaklyConverges F ν)
    (hd : ∀ f : CompactlySupportedContinuousMap X ℝ,
      Tendsto (fun i ↦ (∫ x, f x ∂G i) - ∫ x, f x ∂F i) atTop (𝓝 0)) :
    Measure.WeaklyConverges G ν := by
  intro f
  simpa using (hd f).add (h f)

/-- Weak convergence of the blow-ups gives a uniform bound for the mass of balls. -/
lemma eventually_smul_measure_closedBall_le
    {μ ν : Measure (EuclideanSpace ℝ (Fin n))} {a : EuclideanSpace ℝ (Fin n)}
    {r : ℕ → ℝ} {c : ℕ → ℝ≥0∞} (hr : ∀ i, 0 < r i)
    {hseq : ∀ i, (c i • μ.map (blowUpMap a (r i))).Regular} {hν : ν.Regular}
    (hconv : Measure.WeaklyConverges (fun i ↦ c i • μ.map (blowUpMap a (r i))) ν)
    (S : ℝ) :
    ∀ᶠ i in atTop, c i * μ (closedBall a (r i * S)) ≤ ν (closedBall 0 S) + 1 := by
  have hb := (Measure.weaklyConverges_iff_compactOpenBounds _ ν hseq hν).mp hconv
  have h1 := hb.1 (closedBall 0 S) (isCompact_closedBall _ _)
  have heq : ∀ i, (c i • μ.map (blowUpMap a (r i))) (closedBall 0 S)
      = c i * μ (closedBall a (r i * S)) := by
    intro i
    rw [Measure.smul_apply, smul_eq_mul, map_blowUp_apply_closedBall μ a (hr i)]
  have hfin : ν (closedBall 0 S) ≠ ∞ := (regular_measure_closedBall_lt_top hν 0 S).ne
  have hlt : limsup (fun i ↦ c i * μ (closedBall a (r i * S))) atTop
      < ν (closedBall 0 S) + 1 := by
    refine lt_of_le_of_lt ?_ (ENNReal.lt_add_right hfin one_ne_zero)
    simpa only [heq] using h1
  exact (eventually_lt_of_limsup_lt hlt).mono fun i hi ↦ hi.le

/-- If `B` has density one at `a` and the normalized masses of the balls stay bounded, then
the normalized masses of the sets `B̄ (a, r i t) \ B` tend to `0`. -/
lemma tendsto_mul_measure_diff_zero
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hμ : μ.Regular)
    {a : EuclideanSpace ℝ (Fin n)} (ha : a ∈ μ.support)
    {B : Set (EuclideanSpace ℝ (Fin n))}
    (hdens : Tendsto (fun s : ℝ ↦ μ (ball a s \ B) / μ (ball a s)) (𝓝[>] (0 : ℝ)) (𝓝 0))
    {r : ℕ → ℝ} (hr : ∀ i, 0 < r i) (hr0 : Tendsto r atTop (𝓝 0))
    {c : ℕ → ℝ≥0∞} {t : ℝ} (ht : 0 < t) {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hbd : ∀ᶠ i in atTop, c i * μ (closedBall a (2 * (r i * t))) ≤ M) :
    Tendsto (fun i ↦ c i * μ (closedBall a (r i * t) \ B)) atTop (𝓝 0) := by
  set s : ℕ → ℝ := fun i ↦ 2 * (r i * t) with hs
  have hspos : ∀ i, 0 < s i := fun i ↦ by
    have := mul_pos (hr i) ht
    simp only [hs]
    linarith
  have hs0 : Tendsto s atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsGT_zero_of_pos hspos ?_
    have : Tendsto (fun i ↦ 2 * (r i * t)) atTop (𝓝 (2 * (0 * t))) :=
      (hr0.mul_const t).const_mul 2
    simpa using this
  have heps : Tendsto (fun i ↦ μ (ball a (s i) \ B) / μ (ball a (s i))) atTop (𝓝 0) :=
    hdens.comp hs0
  have hlim : Tendsto (fun i ↦ (μ (ball a (s i) \ B) / μ (ball a (s i))) * M)
      atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const heps (Or.inr hM)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun i ↦ zero_le) ?_
  filter_upwards [hbd] with i hi
  have hpos : μ (ball a (s i)) ≠ 0 := (measure_ball_pos_of_mem_support ha (hspos i)).ne'
  have hfin : μ (ball a (s i)) ≠ ∞ := (regular_measure_ball_lt_top hμ a (s i)).ne
  have hsub : closedBall a (r i * t) \ B ⊆ ball a (s i) \ B := by
    refine diff_subset_diff_left (closedBall_subset_ball ?_)
    have := mul_pos (hr i) ht
    simp only [hs]
    linarith
  calc c i * μ (closedBall a (r i * t) \ B) ≤ c i * μ (ball a (s i) \ B) := by gcongr
    _ = (μ (ball a (s i) \ B) / μ (ball a (s i))) * (c i * μ (ball a (s i))) := by
        rw [show (μ (ball a (s i) \ B) / μ (ball a (s i))) * (c i * μ (ball a (s i)))
            = c i * (μ (ball a (s i) \ B) / μ (ball a (s i)) * μ (ball a (s i))) from by
              ring,
          ENNReal.div_mul_cancel hpos hfin]
    _ ≤ (μ (ball a (s i) \ B) / μ (ball a (s i))) * M := by
        gcongr
        exact le_trans (by gcongr; exact ball_subset_closedBall) hi

/-- If `B` has density one at `a`, then at small scales the measure of a ball is at most twice
the measure of its intersection with `B`. -/
lemma eventually_measure_ball_le_two_mul_inter
    {μ : Measure (EuclideanSpace ℝ (Fin n))} (hμ : μ.Regular)
    {a : EuclideanSpace ℝ (Fin n)} (ha : a ∈ μ.support)
    {B : Set (EuclideanSpace ℝ (Fin n))} (hB : MeasurableSet B)
    (hdens : Tendsto (fun s : ℝ ↦ μ (ball a s \ B) / μ (ball a s)) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), μ (ball a s) ≤ 2 * μ (ball a s ∩ B) := by
  have hhalf : (0 : ℝ≥0∞) < 1 / 2 := by norm_num
  have hev : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), μ (ball a s \ B) / μ (ball a s) < 1 / 2 :=
    hdens (Iio_mem_nhds hhalf)
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hspos'
  have hspos : 0 < s := hspos'
  have hy0 : μ (ball a s) ≠ 0 := (measure_ball_pos_of_mem_support ha hspos).ne'
  have hytop : μ (ball a s) ≠ ∞ := (regular_measure_ball_lt_top hμ a s).ne
  have hsplit : μ (ball a s) = μ (ball a s ∩ B) + μ (ball a s \ B) := by
    exact (measure_inter_add_diff (μ := μ) (ball a s) hB).symm
  have hx : μ (ball a s \ B) < μ (ball a s) / 2 := by
    rw [ENNReal.div_lt_iff (Or.inl hy0) (Or.inl hytop)] at hs
    have heq : (1 : ℝ≥0∞) / 2 * μ (ball a s) = μ (ball a s) / 2 := by
      rw [div_eq_mul_inv, div_eq_mul_inv, one_mul, mul_comm]
    rwa [heq] at hs
  have hhalffin : μ (ball a s) / 2 ≠ ∞ := by simp [ENNReal.div_eq_top, hytop]
  have hkey : μ (ball a s) / 2 ≤ μ (ball a s ∩ B) := by
    have h1 : μ (ball a s) / 2 + μ (ball a s) / 2
        ≤ μ (ball a s ∩ B) + μ (ball a s) / 2 := by
      rw [ENNReal.add_halves]
      calc μ (ball a s) = μ (ball a s ∩ B) + μ (ball a s \ B) := hsplit
        _ ≤ μ (ball a s ∩ B) + μ (ball a s) / 2 := add_le_add le_rfl hx.le
    exact (ENNReal.add_le_add_iff_right hhalffin).mp h1
  calc μ (ball a s) = μ (ball a s) / 2 + μ (ball a s) / 2 := (ENNReal.add_halves _).symm
    _ ≤ μ (ball a s ∩ B) + μ (ball a s ∩ B) := add_le_add hkey hkey
    _ = 2 * μ (ball a s ∩ B) := (two_mul _).symm

/-- The key estimate behind Mattila's Lemma 14.5: if the normalized masses outside `B` tend
to `0`, then the blow-ups of `μ` and of `μ.restrict B` have asymptotically equal integrals. -/
lemma tendsto_integral_sub_restrict
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : μ.Regular)
    {B : Set (EuclideanSpace ℝ (Fin n))} (hB : MeasurableSet B)
    (a : EuclideanSpace ℝ (Fin n)) {r : ℕ → ℝ} (hr : ∀ i, 0 < r i) {c : ℕ → ℝ≥0∞}
    (hcfin : ∀ i, c i ≠ ∞)
    (hF : ∀ i, (c i • μ.map (blowUpMap a (r i))).Regular)
    (hdiff : ∀ t : ℝ, 0 < t →
      Tendsto (fun i ↦ c i * μ (closedBall a (r i * t) \ B)) atTop (𝓝 0))
    (f : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ) :
    Tendsto (fun i ↦
        (∫ x, f x ∂(c i • (μ.restrict B).map (blowUpMap a (r i))))
          - ∫ x, f x ∂(c i • μ.map (blowUpMap a (r i)))) atTop (𝓝 0) := by
  obtain ⟨t, ht, htsup⟩ : ∃ t : ℝ, 0 < t ∧ tsupport f ⊆ closedBall 0 t := by
    obtain ⟨R, hR⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall
      (0 : EuclideanSpace ℝ (Fin n))
    exact ⟨max 1 R, lt_of_lt_of_le one_pos (le_max_left _ _),
      hR.trans (closedBall_subset_closedBall (le_max_right _ _))⟩
  have key : ∀ i, ‖(∫ x, f x ∂(c i • (μ.restrict B).map (blowUpMap a (r i))))
          - ∫ x, f x ∂(c i • μ.map (blowUpMap a (r i)))‖
      ≤ ‖f.toBoundedContinuousFunction‖ * (c i * μ (closedBall a (r i * t) \ B)).toReal := by
    intro i
    have hmeas : Measurable (blowUpMap a (r i)) := measurable_blowUpMap a (r i)
    set D : Measure (EuclideanSpace ℝ (Fin n)) :=
      c i • (μ.restrict Bᶜ).map (blowUpMap a (r i)) with hD
    have hdec : c i • μ.map (blowUpMap a (r i))
        = c i • (μ.restrict B).map (blowUpMap a (r i)) + D := by
      rw [hD, ← smul_add, ← Measure.map_add _ _ hmeas,
        Measure.restrict_add_restrict_compl hB]
    haveI : (c i • μ.map (blowUpMap a (r i))).Regular := hF i
    have hintF : Integrable f (c i • μ.map (blowUpMap a (r i))) :=
      f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
    have hleG : c i • (μ.restrict B).map (blowUpMap a (r i))
        ≤ c i • μ.map (blowUpMap a (r i)) := by
      rw [hdec]
      exact Measure.le_add_right le_rfl
    have hleD : D ≤ c i • μ.map (blowUpMap a (r i)) := by
      rw [hdec]
      exact Measure.le_add_left le_rfl
    have hintG := hintF.mono_measure hleG
    have hintD := hintF.mono_measure hleD
    have hsplit : (∫ x, f x ∂(c i • μ.map (blowUpMap a (r i))))
        = (∫ x, f x ∂(c i • (μ.restrict B).map (blowUpMap a (r i))))
          + ∫ x, f x ∂D := by
      rw [hdec, integral_add_measure hintG hintD]
    have hDK : D (closedBall 0 t) = c i * μ (closedBall a (r i * t) \ B) := by
      rw [hD, Measure.smul_apply, smul_eq_mul,
        Measure.map_apply hmeas measurableSet_closedBall,
        blowUpMap_preimage_closedBall a (hr i), Measure.restrict_apply measurableSet_closedBall,
        ← Set.diff_eq]
    have hDfin : D (closedBall 0 t) < ∞ := by
      rw [hDK]
      exact ENNReal.mul_lt_top (hcfin i).lt_top
        (lt_of_le_of_lt (measure_mono diff_subset) (regular_measure_closedBall_lt_top hμ a _))
    rw [hsplit]
    have hbound : ‖-∫ x, f x ∂D‖
        ≤ ‖f.toBoundedContinuousFunction‖ * (D (closedBall 0 t)).toReal := by
      rw [norm_neg]
      exact norm_integral_cc_le D f htsup hDfin
    rw [hDK] at hbound
    simpa using hbound
  refine squeeze_zero_norm key ?_
  have h0 : Tendsto (fun i ↦ (c i * μ (closedBall a (r i * t) \ B)).toReal)
      atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal (a := 0) (by simp)).comp (hdiff t ht)
    simpa only [Function.comp_def, ENNReal.toReal_zero] using this
  simpa using h0.const_mul ‖f.toBoundedContinuousFunction‖

end TangentAux

/-- **Mattila, Lemma 14.5.** If `B` has density one with respect to `μ` at `a`, then
restricting `μ` to `B` does not change the tangent measures at `a`. -/
theorem isTangentMeasure_restrict_iff
    {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : μ.Regular)
    (B : Set (EuclideanSpace ℝ (Fin n))) (hB : MeasurableSet B)
    (hμB : (μ.restrict B).Regular) (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ μ.support)
    (hdens : Tendsto (fun r : ℝ ↦ μ (ball a r \ B) / μ (ball a r))
      (𝓝[>] (0 : ℝ)) (𝓝 0)) (ν : Measure (EuclideanSpace ℝ (Fin n))) :
    IsTangentMeasure μ ν a ↔ IsTangentMeasure (μ.restrict B) ν a := by
  constructor
  · rintro ⟨hν, hν0, r, c, hr, hcpos, hcfin, hr0, hconv⟩
    have hseq : ∀ i, (c i • μ.map (blowUpMap a (r i))).Regular := fun i ↦
      regular_smul_map_blowUp hμ a (hr i).ne' (hcfin i)
    have hdiff : ∀ t : ℝ, 0 < t →
        Tendsto (fun i ↦ c i * μ (closedBall a (r i * t) \ B)) atTop (𝓝 0) := by
      intro t ht
      have hbd := eventually_smul_measure_closedBall_le (hseq := hseq) (hν := hν) hr hconv (2 * t)
      refine tendsto_mul_measure_diff_zero hμ ha hdens hr hr0 ht
        (M := ν (closedBall 0 (2 * t)) + 1)
        (by simp [ENNReal.add_eq_top, (regular_measure_closedBall_lt_top hν 0 (2 * t)).ne]) ?_
      filter_upwards [hbd] with i hi
      have hrw : r i * (2 * t) = 2 * (r i * t) := by ring
      rwa [hrw] at hi
    exact ⟨hν, hν0, r, c, hr, hcpos, hcfin, hr0,
      weaklyConverges_of_tendsto_integral_sub hconv
        (tendsto_integral_sub_restrict μ hμ hB a hr hcfin hseq hdiff)⟩
  · rintro ⟨hν, hν0, r, c, hr, hcpos, hcfin, hr0, hconvB⟩
    have hseq : ∀ i, (c i • μ.map (blowUpMap a (r i))).Regular := fun i ↦
      regular_smul_map_blowUp hμ a (hr i).ne' (hcfin i)
    have hseqB : ∀ i, (c i • (μ.restrict B).map (blowUpMap a (r i))).Regular := fun i ↦
      regular_smul_map_blowUp hμB a (hr i).ne' (hcfin i)
    have hdiff : ∀ t : ℝ, 0 < t →
        Tendsto (fun i ↦ c i * μ (closedBall a (r i * t) \ B)) atTop (𝓝 0) := by
      intro t ht
      have hbd := eventually_smul_measure_closedBall_le (hseq := hseqB) (hν := hν)
        hr hconvB (4 * t)
      have hballs : ∀ᶠ i in atTop,
          μ (ball a (4 * (r i * t))) ≤ 2 * μ (ball a (4 * (r i * t)) ∩ B) := by
        have hu : Tendsto (fun i ↦ 4 * (r i * t)) atTop (𝓝[>] (0 : ℝ)) := by
          refine tendsto_nhdsGT_zero_of_pos
            (fun i ↦ by have := mul_pos (hr i) ht; linarith) ?_
          have h4 : Tendsto (fun i ↦ 4 * (r i * t)) atTop (𝓝 (4 * (0 * t))) :=
            (hr0.mul_const t).const_mul 4
          simpa using h4
        exact hu.eventually (eventually_measure_ball_le_two_mul_inter hμ ha hB hdens)
      refine tendsto_mul_measure_diff_zero hμ ha hdens hr hr0 ht
        (M := 2 * (ν (closedBall 0 (4 * t)) + 1))
        (by simp [ENNReal.mul_eq_top, ENNReal.add_eq_top,
          (regular_measure_closedBall_lt_top hν 0 (4 * t)).ne]) ?_
      filter_upwards [hbd, hballs] with i h1 h2
      have hrt : 0 < r i * t := mul_pos (hr i) ht
      calc c i * μ (closedBall a (2 * (r i * t)))
          ≤ c i * μ (ball a (4 * (r i * t))) := by
            gcongr
            exact closedBall_subset_ball (by linarith)
        _ ≤ c i * (2 * μ (ball a (4 * (r i * t)) ∩ B)) := by gcongr
        _ = 2 * (c i * μ (ball a (4 * (r i * t)) ∩ B)) := by ring
        _ ≤ 2 * (c i * (μ.restrict B) (closedBall a (r i * (4 * t)))) := by
            have hres : μ (ball a (4 * (r i * t)) ∩ B)
                ≤ (μ.restrict B) (closedBall a (r i * (4 * t))) := by
              rw [Measure.restrict_apply measurableSet_closedBall]
              exact measure_mono (inter_subset_inter_left B
                (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))))
            gcongr
        _ ≤ 2 * (ν (closedBall 0 (4 * t)) + 1) := by gcongr
    have hkey := tendsto_integral_sub_restrict μ hμ hB a hr hcfin hseq hdiff
    exact ⟨hν, hν0, r, c, hr, hcpos, hcfin, hr0,
      weaklyConverges_of_tendsto_integral_sub hconvB (fun f ↦ by simpa using (hkey f).neg)⟩

/-! ## Auxiliary material for Lemma 14.6 -/

section DensityAux

variable {n : ℕ}

/-- Two measures agreeing on bounded measurable sets are equal. -/
lemma measure_ext_of_bounded {m₁ m₂ : Measure (EuclideanSpace ℝ (Fin n))}
    (h : ∀ B : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet B → Bornology.IsBounded B →
      m₁ B = m₂ B) : m₁ = m₂ := by
  ext B hB
  have hcover : B = ⋃ k : ℕ, B ∩ closedBall 0 k := by
    ext y
    simp only [mem_iUnion, mem_inter_iff, mem_closedBall]
    constructor
    · intro hy
      obtain ⟨k, hk⟩ := exists_nat_ge (dist y 0)
      exact ⟨k, hy, hk⟩
    · rintro ⟨k, hy, -⟩
      exact hy
  have hdir : Directed (· ⊆ ·)
      (fun k : ℕ ↦ B ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) k) := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩ <;>
      exact inter_subset_inter_right _ (closedBall_subset_closedBall (by
        simp only [Nat.cast_le]
        omega))
  rw [hcover, hdir.measure_iUnion, hdir.measure_iUnion]
  exact iSup_congr fun k ↦ h _ (hB.inter measurableSet_closedBall)
    (Metric.isBounded_closedBall.subset inter_subset_right)

/-- A measure specified as `φ μ` on measurable sets is `μ.withDensity φ`. -/
lemma measure_eq_withDensity
    (μ L : Measure (EuclideanSpace ℝ (Fin n)))
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ_nonneg : ∀ x, 0 ≤ φ x)
    (hφ_loc : LocallyIntegrable φ μ)
    (hL_eq : ∀ B : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet B →
      L B = ENNReal.ofReal (∫ x in B, φ x ∂μ)) :
    L = μ.withDensity (fun x ↦ ENNReal.ofReal (φ x)) := by
  refine measure_ext_of_bounded fun B hB hBb ↦ ?_
  obtain ⟨R, hR⟩ := hBb.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  have hint : IntegrableOn φ B μ :=
    (hφ_loc.integrableOn_isCompact (isCompact_closedBall 0 R)).mono_set hR
  rw [hL_eq B hB, withDensity_apply _ hB,
    ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hφ_nonneg)]

/-- Lebesgue differentiation theorem for a Radon measure on Euclidean space. -/
lemma ae_tendsto_setAverage_norm_sub (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (hμ : μ.Regular) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ_loc : LocallyIntegrable φ μ) :
    ∀ᵐ a ∂μ, Tendsto (fun s : ℝ ↦ ⨍ y in closedBall a s, ‖φ y - φ a‖ ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  letI : μ.Regular := hμ
  filter_upwards [(Besicovitch.vitaliFamily μ).ae_tendsto_average_norm_sub hφ_loc] with a ha
  exact ha.comp (Besicovitch.tendsto_filterAt μ a)

/-- The integral of a compactly supported continuous function against a scaled blow-up. -/
lemma integral_blowUp_smul (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) (r : ℝ) (c : ℝ≥0∞)
    (f : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ) :
    (∫ x, f x ∂(c • μ.map (blowUpMap a r)))
      = c.toReal * ∫ x, f (blowUpMap a r x) ∂μ := by
  have hmeas : Measurable (blowUpMap a r) := measurable_blowUpMap a r
  rw [integral_smul_measure,
    integral_map (f := fun y ↦ f y) hmeas.aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop)), smul_eq_mul]

lemma integral_withDensity_real (m : Measure (EuclideanSpace ℝ (Fin n)))
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ_meas : Measurable φ)
    (hφ_nonneg : ∀ x, 0 ≤ φ x) (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∫ x, g x ∂(m.withDensity fun x ↦ ENNReal.ofReal (φ x)) = ∫ x, φ x * g x ∂m := by
  rw [integral_withDensity_eq_integral_toReal_smul hφ_meas.ennreal_ofReal
    (Eventually.of_forall fun x ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hφ_nonneg _), smul_eq_mul]

/-- The key per-scale estimate behind Mattila's Lemma 14.6. -/
lemma norm_integral_blowUp_density_sub_le
    (μ L : Measure (EuclideanSpace ℝ (Fin n))) (hμ : μ.Regular)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ_meas : Measurable φ)
    (hφ_nonneg : ∀ x, 0 ≤ φ x) (hφ_loc : LocallyIntegrable φ μ)
    (hLm : L = μ.withDensity (fun x ↦ ENNReal.ofReal (φ x)))
    (a : EuclideanSpace ℝ (Fin n)) (hφa : 0 < φ a) {r : ℝ} (hr : 0 < r) {c : ℝ≥0∞}
    (f : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ) {t : ℝ}
    (htsup : tsupport f ⊆ closedBall 0 t) :
    ‖(∫ x, f x ∂((c / ENNReal.ofReal (φ a)) • L.map (blowUpMap a r)))
        - ∫ x, f x ∂(c • μ.map (blowUpMap a r))‖
      ≤ (c.toReal / φ a) * ‖f.toBoundedContinuousFunction‖
          * ∫ y in closedBall a (r * t), ‖φ y - φ a‖ ∂μ := by
  set T := blowUpMap a r with hT
  set C := ‖f.toBoundedContinuousFunction‖ with hC
  set K := closedBall a (r * t) with hK
  have hCnn : (0 : ℝ) ≤ C := norm_nonneg _
  have hfbd : ∀ x, ‖f x‖ ≤ C := fun x ↦ f.toBoundedContinuousFunction.norm_coe_le_norm x
  have hTcont : Continuous T := continuous_blowUpMap a r
  have hpre : T ⁻¹' (closedBall 0 t) = K := blowUpMap_preimage_closedBall a hr t
  have hzero : ∀ x, x ∉ K → f (T x) = 0 := by
    intro x hx
    refine image_eq_zero_of_notMem_tsupport fun h ↦ hx ?_
    rw [← hpre]
    exact mem_preimage.2 (htsup h)
  letI : μ.Regular := hμ
  have hKcompact : IsCompact K := isCompact_closedBall _ _
  have hmfin : μ K < ∞ := hKcompact.measure_lt_top
  have hφB : IntegrableOn φ K μ := hφ_loc.integrableOn_isCompact hKcompact
  have hg1 : Integrable (fun x ↦ f (T x)) μ := by
    refine Continuous.integrable_of_hasCompactSupport (f.continuous.comp hTcont) ?_
    exact HasCompactSupport.intro hKcompact hzero
  have hg2 : Integrable (fun x ↦ φ x * f (T x)) μ := by
    refine IntegrableOn.integrable_of_forall_notMem_eq_zero
      (s := K) (hφB.mul_bdd ?_ (Eventually.of_forall fun x ↦ hfbd (T x))) ?_
    · exact (f.continuous.comp hTcont).aestronglyMeasurable
    · intro x hx
      simp [hzero x hx]
  have hg3 : Integrable (fun x ↦ (φ x - φ a) * f (T x)) μ := by
    have : (fun x ↦ (φ x - φ a) * f (T x))
        = fun x ↦ φ x * f (T x) - φ a * f (T x) := by
      ext x
      ring
    rw [this]
    exact hg2.sub (hg1.const_mul (φ a))
  rw [integral_blowUp_smul μ a r c f,
    integral_blowUp_smul L a r (c / ENNReal.ofReal (φ a)) f, hLm,
    integral_withDensity_real μ hφ_meas hφ_nonneg,
    ENNReal.toReal_div, ENNReal.toReal_ofReal hφa.le]
  have hsplit : c.toReal / φ a * (∫ x, φ x * f (T x) ∂μ)
      - c.toReal * ∫ x, f (T x) ∂μ
      = (c.toReal / φ a) * ∫ x, (φ x - φ a) * f (T x) ∂μ := by
    have hcongr : (fun x ↦ (φ x - φ a) * f (T x))
        = fun x ↦ φ x * f (T x) - φ a * f (T x) := by
      ext x
      ring
    rw [hcongr, integral_sub hg2 (hg1.const_mul (φ a)), integral_const_mul]
    field_simp
  rw [hsplit, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ c.toReal / φ a), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ‖∫ x, (φ x - φ a) * f (T x) ∂μ‖
        ≤ ∫ x, ‖(φ x - φ a) * f (T x)‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ x in K, ‖(φ x - φ a) * f (T x)‖ ∂μ := by
        refine (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
        intro x hx
        simp [hzero x hx]
    _ ≤ ∫ x in K, C * ‖φ x - φ a‖ ∂μ := by
        refine integral_mono ?_ ?_ ?_
        · exact hg3.norm.integrableOn
        · exact ((hφB.sub (integrableOn_const hmfin.ne)).norm.const_mul C)
        · intro x
          change ‖(φ x - φ a) * f (T x)‖ ≤ C * ‖φ x - φ a‖
          rw [norm_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hfbd (T x)) (norm_nonneg _)
    _ = C * ∫ x in K, ‖φ x - φ a‖ ∂μ := integral_const_mul _ _

lemma tendsto_mul_setIntegral_norm_sub_zero
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : μ.Regular)
    (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ μ.support)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hleb : Tendsto (fun s : ℝ ↦ ⨍ y in closedBall a s, ‖φ y - φ a‖ ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    {r : ℕ → ℝ} (hr : ∀ i, 0 < r i) (hr0 : Tendsto r atTop (𝓝 0)) {t : ℝ} (ht : 0 < t)
    {c : ℕ → ℝ≥0∞} {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hbdd : ∀ᶠ i in atTop, c i * μ (closedBall a (r i * t)) ≤ M) :
    Tendsto (fun i ↦ (c i).toReal * ∫ y in closedBall a (r i * t), ‖φ y - φ a‖ ∂μ)
      atTop (𝓝 0) := by
  letI : μ.Regular := hμ
  have hs : Tendsto (fun i ↦ r i * t) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsGT_zero_of_pos (fun i ↦ mul_pos (hr i) ht) (by simpa using hr0.mul_const t)
  have heps : Tendsto (fun i ↦ ⨍ y in closedBall a (r i * t), ‖φ y - φ a‖ ∂μ)
      atTop (𝓝 0) := hleb.comp hs
  have hlim : Tendsto
      (fun i ↦ M.toReal * ⨍ y in closedBall a (r i * t), ‖φ y - φ a‖ ∂μ)
      atTop (𝓝 0) := by
    simpa using heps.const_mul M.toReal
  refine squeeze_zero' (Eventually.of_forall fun i ↦ ?_) ?_ hlim
  · exact mul_nonneg ENNReal.toReal_nonneg (integral_nonneg fun y ↦ norm_nonneg _)
  filter_upwards [hbdd] with i hi
  have hmpos : 0 < μ (closedBall a (r i * t)) :=
    lt_of_lt_of_le (measure_ball_pos_of_mem_support ha (mul_pos (hr i) ht))
      (measure_mono ball_subset_closedBall)
  have hmfin : μ (closedBall a (r i * t)) < ∞ := (isCompact_closedBall _ _).measure_lt_top
  have hmreal : (μ (closedBall a (r i * t))).toReal ≠ 0 := by
    simp [ENNReal.toReal_eq_zero_iff, hmpos.ne', hmfin.ne]
  have hint : (∫ y in closedBall a (r i * t), ‖φ y - φ a‖ ∂μ)
      = (μ (closedBall a (r i * t))).toReal
        * ⨍ y in closedBall a (r i * t), ‖φ y - φ a‖ ∂μ := by
    rw [setAverage_eq, smul_eq_mul, ← mul_assoc, measureReal_def,
      mul_inv_cancel₀ hmreal, one_mul]
  have hle : (c i * μ (closedBall a (r i * t))).toReal ≤ M.toReal :=
    ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hM hi) hM |>.2 hi
  calc (c i).toReal * ∫ y in closedBall a (r i * t), ‖φ y - φ a‖ ∂μ
      = (c i * μ (closedBall a (r i * t))).toReal
        * ⨍ y in closedBall a (r i * t), ‖φ y - φ a‖ ∂μ := by
        rw [hint, ENNReal.toReal_mul, mul_assoc]
    _ ≤ M.toReal * ⨍ y in closedBall a (r i * t), ‖φ y - φ a‖ ∂μ := by
        refine mul_le_mul_of_nonneg_right hle ?_
        rw [setAverage_eq, smul_eq_mul]
        exact mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
          (integral_nonneg fun y ↦ norm_nonneg _)

/-- At a Lebesgue point `a` of `φ` with `φ a > 0`, the measure `L = φ μ` of a small ball is at
least `φ a / 2` times the `μ`-measure of that ball. -/
lemma eventually_ofReal_mul_measure_closedBall_le
    (μ L : Measure (EuclideanSpace ℝ (Fin n))) (hμ : μ.Regular)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ_loc : LocallyIntegrable φ μ)
    (hL_eq : ∀ B : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet B →
      L B = ENNReal.ofReal (∫ x in B, φ x ∂μ))
    (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ μ.support) (hφa : 0 < φ a)
    (hleb : Tendsto (fun s : ℝ ↦ ⨍ y in closedBall a s, ‖φ y - φ a‖ ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (φ a / 2) * μ (closedBall a s) ≤ L (closedBall a s) := by
  letI : μ.Regular := hμ
  have hev : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
      ⨍ y in closedBall a s, ‖φ y - φ a‖ ∂μ < φ a / 2 :=
    hleb (Iio_mem_nhds (by positivity))
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hspos'
  have hspos : 0 < s := hspos'
  have hmfin : μ (closedBall a s) < ∞ := (isCompact_closedBall _ _).measure_lt_top
  have hmpos : 0 < μ (closedBall a s) :=
    lt_of_lt_of_le (measure_ball_pos_of_mem_support ha hspos)
      (measure_mono ball_subset_closedBall)
  have hmreal : (0 : ℝ) < (μ (closedBall a s)).toReal := by
    simpa [ENNReal.toReal_pos_iff] using ⟨hmpos, hmfin⟩
  have hint : IntegrableOn φ (closedBall a s) μ :=
    hφ_loc.integrableOn_isCompact (isCompact_closedBall _ _)
  have hI : (∫ y in closedBall a s, ‖φ y - φ a‖ ∂μ)
      = (μ (closedBall a s)).toReal * ⨍ y in closedBall a s, ‖φ y - φ a‖ ∂μ := by
    rw [setAverage_eq, smul_eq_mul, ← mul_assoc, measureReal_def,
      mul_inv_cancel₀ hmreal.ne', one_mul]
  have hIle : (∫ y in closedBall a s, ‖φ y - φ a‖ ∂μ)
      ≤ (φ a / 2) * (μ (closedBall a s)).toReal := by
    rw [hI, mul_comm]
    exact mul_le_mul_of_nonneg_right hs.le hmreal.le
  have hlow : (φ a / 2) * (μ (closedBall a s)).toReal
      ≤ ∫ y in closedBall a s, φ y ∂μ := by
    have hconst : (∫ _y in closedBall a s, φ a ∂μ)
        = (μ (closedBall a s)).toReal * φ a := by
      rw [setIntegral_const, smul_eq_mul, measureReal_def]
    have h1 : (∫ y in closedBall a s, (φ y - φ a) ∂μ)
        = (∫ y in closedBall a s, φ y ∂μ) - (μ (closedBall a s)).toReal * φ a := by
      rw [integral_sub hint (integrableOn_const hmfin.ne), hconst]
    have h2 : |∫ y in closedBall a s, (φ y - φ a) ∂μ|
        ≤ ∫ y in closedBall a s, ‖φ y - φ a‖ ∂μ := by
      simpa [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := μ.restrict (closedBall a s))
          (f := fun y ↦ φ y - φ a)
    have h3 := (abs_le.mp (h2.trans hIle)).1
    have harith : (μ (closedBall a s)).toReal * φ a
        - (φ a / 2) * (μ (closedBall a s)).toReal
        = (φ a / 2) * (μ (closedBall a s)).toReal := by ring
    linarith [h1, h3, harith]
  rw [hL_eq _ measurableSet_closedBall]
  calc ENNReal.ofReal (φ a / 2) * μ (closedBall a s)
      = ENNReal.ofReal ((φ a / 2) * (μ (closedBall a s)).toReal) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hmfin.ne]
    _ ≤ ENNReal.ofReal (∫ y in closedBall a s, φ y ∂μ) := ENNReal.ofReal_le_ofReal hlow

/-- At a positive Lebesgue point of `φ`, appropriately normalized blow-ups of `μ` and `φ μ`
have asymptotically equal integrals. -/
lemma tendsto_integral_sub_density
    (μ L : Measure (EuclideanSpace ℝ (Fin n))) (hμ : μ.Regular)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ_meas : Measurable φ)
    (hφ_nonneg : ∀ x, 0 ≤ φ x) (hφ_loc : LocallyIntegrable φ μ)
    (hLm : L = μ.withDensity (fun x ↦ ENNReal.ofReal (φ x)))
    (a : EuclideanSpace ℝ (Fin n)) (hφa : 0 < φ a) (ha : a ∈ μ.support)
    (hleb : Tendsto (fun s : ℝ ↦ ⨍ y in closedBall a s, ‖φ y - φ a‖ ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    {r : ℕ → ℝ} (hr : ∀ i, 0 < r i) (hr0 : Tendsto r atTop (𝓝 0)) {c : ℕ → ℝ≥0∞}
    (hbdd : ∀ t : ℝ, 0 < t → ∃ M : ℝ≥0∞, M ≠ ∞ ∧
      ∀ᶠ i in atTop, c i * μ (closedBall a (r i * t)) ≤ M)
    (f : CompactlySupportedContinuousMap (EuclideanSpace ℝ (Fin n)) ℝ) :
    Tendsto (fun i ↦
        (∫ x, f x ∂((c i / ENNReal.ofReal (φ a)) • L.map (blowUpMap a (r i))))
          - ∫ x, f x ∂(c i • μ.map (blowUpMap a (r i)))) atTop (𝓝 0) := by
  set C := ‖f.toBoundedContinuousFunction‖ with hC
  obtain ⟨t, ht, htsup⟩ : ∃ t : ℝ, 0 < t ∧ tsupport f ⊆ closedBall 0 t := by
    obtain ⟨R, hR⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall
      (0 : EuclideanSpace ℝ (Fin n))
    exact ⟨max 1 R, lt_of_lt_of_le one_pos (le_max_left _ _),
      hR.trans (closedBall_subset_closedBall (le_max_right _ _))⟩
  obtain ⟨M, hM, hbd⟩ := hbdd t ht
  have hlim := tendsto_mul_setIntegral_norm_sub_zero μ hμ a ha φ hleb hr hr0 ht hM hbd
  refine squeeze_zero_norm (fun i ↦ ?_) (by simpa using hlim.const_mul (C / φ a))
  calc ‖(∫ x, f x ∂((c i / ENNReal.ofReal (φ a)) • L.map (blowUpMap a (r i))))
        - ∫ x, f x ∂(c i • μ.map (blowUpMap a (r i)))‖
      ≤ ((c i).toReal / φ a) * C
          * ∫ y in closedBall a (r i * t), ‖φ y - φ a‖ ∂μ :=
        norm_integral_blowUp_density_sub_le μ L hμ φ hφ_meas hφ_nonneg hφ_loc
          hLm a hφa (hr i) f htsup
    _ = C / φ a * ((c i).toReal
        * ∫ y in closedBall a (r i * t), ‖φ y - φ a‖ ∂μ) := by ring

/-- Mattila, Lemma 14.6, at a fixed Lebesgue point of the density. -/
lemma isTangentMeasure_iff_of_lebesgue_point
    (μ L : Measure (EuclideanSpace ℝ (Fin n))) (hμ : μ.Regular) (hL : L.Regular)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ_meas : Measurable φ)
    (hφ_nonneg : ∀ x, 0 ≤ φ x) (hφ_loc : LocallyIntegrable φ μ)
    (hL_eq : ∀ B : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet B →
      L B = ENNReal.ofReal (∫ x in B, φ x ∂μ))
    (hLm : L = μ.withDensity (fun x ↦ ENNReal.ofReal (φ x)))
    (a : EuclideanSpace ℝ (Fin n)) (hφa : 0 < φ a) (ha : a ∈ μ.support)
    (hleb : Tendsto (fun s : ℝ ↦ ⨍ y in closedBall a s, ‖φ y - φ a‖ ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) (ν : Measure (EuclideanSpace ℝ (Fin n))) :
    IsTangentMeasure μ ν a ↔ IsTangentMeasure L ν a := by
  have hofR0 : ENNReal.ofReal (φ a) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le, hφa]
  have hofRtop : ENNReal.ofReal (φ a) ≠ ∞ := ENNReal.ofReal_ne_top
  have hhalf0 : ENNReal.ofReal (φ a / 2) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le, hφa]
  constructor
  · rintro ⟨hν, hν0, r, c, hr, hcpos, hcfin, hr0, hconv⟩
    have hseq : ∀ i, (c i • μ.map (blowUpMap a (r i))).Regular := fun i ↦
      regular_smul_map_blowUp hμ a (hr i).ne' (hcfin i)
    have hcfin' : ∀ i, c i / ENNReal.ofReal (φ a) ≠ ∞ :=
      fun i ↦ (ENNReal.div_lt_top (hcfin i) hofR0).ne
    refine ⟨hν, hν0, r, fun i ↦ c i / ENNReal.ofReal (φ a), hr,
      fun i ↦ ENNReal.div_pos (hcpos i).ne' hofRtop, hcfin', hr0, ?_⟩
    refine weaklyConverges_of_tendsto_integral_sub hconv fun f ↦ ?_
    refine tendsto_integral_sub_density μ L hμ φ hφ_meas hφ_nonneg hφ_loc hLm
      a hφa ha hleb hr hr0 ?_ f
    intro t ht
    exact ⟨ν (closedBall 0 t) + 1,
      by simp [ENNReal.add_eq_top, (regular_measure_closedBall_lt_top hν 0 t).ne],
      eventually_smul_measure_closedBall_le (hseq := hseq) (hν := hν) hr hconv t⟩
  · rintro ⟨hν, hν0, r, cL, hr, hcpos, hcfin, hr0, hconvL⟩
    set c : ℕ → ℝ≥0∞ := fun i ↦ cL i * ENNReal.ofReal (φ a) with hc
    have hcancel : ∀ i, c i / ENNReal.ofReal (φ a) = cL i := fun i ↦
      ENNReal.mul_div_cancel_right hofR0 hofRtop
    have hcpos' : ∀ i, 0 < c i := fun i ↦ ENNReal.mul_pos (hcpos i).ne' hofR0
    have hcfin' : ∀ i, c i ≠ ∞ := fun i ↦ ENNReal.mul_ne_top (hcfin i) hofRtop
    have hseqL : ∀ i, (cL i • L.map (blowUpMap a (r i))).Regular := fun i ↦
      regular_smul_map_blowUp hL a (hr i).ne' (hcfin i)
    have hconvL' : Measure.WeaklyConverges
        (fun i ↦ (c i / ENNReal.ofReal (φ a)) • L.map (blowUpMap a (r i))) ν :=
      Measure.WeaklyConverges.congr_seq (fun i ↦ by rw [hcancel i]) hconvL
    have hbdd : ∀ t : ℝ, 0 < t → ∃ M : ℝ≥0∞, M ≠ ∞ ∧
        ∀ᶠ i in atTop, c i * μ (closedBall a (r i * t)) ≤ M := by
      intro t ht
      have hb0 := eventually_smul_measure_closedBall_le (hseq := hseqL) (hν := hν)
        hr hconvL t
      have hb1 : ∀ᶠ i in atTop, ENNReal.ofReal (φ a / 2) * μ (closedBall a (r i * t))
          ≤ L (closedBall a (r i * t)) := by
        have hu : Tendsto (fun i ↦ r i * t) atTop (𝓝[>] (0 : ℝ)) :=
          tendsto_nhdsGT_zero_of_pos (fun i ↦ mul_pos (hr i) ht)
            (by simpa using hr0.mul_const t)
        exact hu.eventually
          (eventually_ofReal_mul_measure_closedBall_le μ L hμ φ hφ_loc hL_eq
            a ha hφa hleb)
      refine ⟨ENNReal.ofReal (φ a)
        * ((ν (closedBall 0 t) + 1) / ENNReal.ofReal (φ a / 2)), ?_, ?_⟩
      · refine ENNReal.mul_ne_top hofRtop ?_
        exact (ENNReal.div_lt_top
          (by simp [ENNReal.add_eq_top, (regular_measure_closedBall_lt_top hν 0 t).ne])
          hhalf0).ne
      · filter_upwards [hb0, hb1] with i h0 h1
        have hstep : cL i * μ (closedBall a (r i * t))
            ≤ (ν (closedBall 0 t) + 1) / ENNReal.ofReal (φ a / 2) := by
          rw [ENNReal.le_div_iff_mul_le (Or.inl hhalf0) (Or.inl ENNReal.ofReal_ne_top)]
          calc cL i * μ (closedBall a (r i * t)) * ENNReal.ofReal (φ a / 2)
              = cL i * (ENNReal.ofReal (φ a / 2) * μ (closedBall a (r i * t))) := by ring
            _ ≤ cL i * L (closedBall a (r i * t)) := by gcongr
            _ ≤ ν (closedBall 0 t) + 1 := h0
        calc c i * μ (closedBall a (r i * t))
            = ENNReal.ofReal (φ a) * (cL i * μ (closedBall a (r i * t))) := by
                rw [hc]
                ring
          _ ≤ ENNReal.ofReal (φ a)
              * ((ν (closedBall 0 t) + 1) / ENNReal.ofReal (φ a / 2)) := by gcongr
    have hkey := tendsto_integral_sub_density μ L hμ φ hφ_meas hφ_nonneg hφ_loc
      hLm a hφa ha hleb hr hr0 hbdd
    exact ⟨hν, hν0, r, c, hr, hcpos', hcfin', hr0,
      weaklyConverges_of_tendsto_integral_sub hconvL' (fun f ↦ by simpa using (hkey f).neg)⟩

end DensityAux

/-- **Mattila, Lemma 14.6.** If `λ = φ μ` with `φ ≥ 0` locally `μ`-integrable, then `μ`
and `λ` have the same tangent measures at `λ`-almost every point. -/
theorem isTangentMeasure_iff_ae_of_density
    {n : ℕ} (μ «λ» : Measure (EuclideanSpace ℝ (Fin n)))
    (hμ : μ.Regular) («hλ» : «λ».Regular) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ_nonneg : ∀ x, 0 ≤ φ x) (hφ_loc : LocallyIntegrable φ μ)
    («hλ_eq» : ∀ B : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet B →
      «λ» B = ENNReal.ofReal (∫ x in B, φ x ∂μ)) :
    ∀ᵐ a ∂«λ», ∀ ν : Measure (EuclideanSpace ℝ (Fin n)),
      IsTangentMeasure μ ν a ↔ IsTangentMeasure «λ» ν a := by
  set g : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x ↦ max (hφ_loc.aestronglyMeasurable.mk φ x) 0 with hgdef
  have hg_meas : Measurable g :=
    (hφ_loc.aestronglyMeasurable.stronglyMeasurable_mk.measurable).max measurable_const
  have hg_nonneg : ∀ x, 0 ≤ g x := fun x ↦ le_max_right _ _
  have hgφ : φ =ᵐ[μ] g := by
    filter_upwards [hφ_loc.aestronglyMeasurable.ae_eq_mk] with x hx
    rw [hgdef]
    simp only
    rw [← hx, max_eq_left (hφ_nonneg x)]
  have hg_loc : LocallyIntegrable g μ := hφ_loc.congr hgφ
  have hg_eq : ∀ B : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet B →
      «λ» B = ENNReal.ofReal (∫ x in B, g x ∂μ) := by
    intro B hB
    rw [«hλ_eq» B hB]
    congr 1
    exact integral_congr_ae (ae_restrict_of_ae hgφ)
  have hLm : «λ» = μ.withDensity (fun x ↦ ENNReal.ofReal (g x)) :=
    measure_eq_withDensity μ «λ» g hg_nonneg hg_loc hg_eq
  have hac : «λ» ≪ μ := by
    rw [hLm]
    exact withDensity_absolutelyContinuous _ _
  have h1 : ∀ᵐ a ∂«λ», 0 < g a := by
    rw [hLm, ae_withDensity_iff hg_meas.ennreal_ofReal]
    filter_upwards with x hx
    simpa [ENNReal.ofReal_eq_zero, not_le] using hx
  have h2 : ∀ᵐ a ∂«λ», a ∈ μ.support :=
    hac.ae_le (ae_iff.2 μ.measure_compl_support)
  have h3 : ∀ᵐ a ∂«λ», Tendsto
      (fun s : ℝ ↦ ⨍ y in closedBall a s, ‖g y - g a‖ ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    hac.ae_le (ae_tendsto_setAverage_norm_sub μ hμ g hg_loc)
  filter_upwards [h1, h2, h3] with a ha1 ha2 ha3
  intro ν
  exact isTangentMeasure_iff_of_lebesgue_point μ «λ» hμ «hλ» g hg_meas hg_nonneg
    hg_loc hg_eq hLm a ha1 ha2 ha3 ν


/-- 14.7 stuff starts here -/

/-! ## Densities -/
/-- The **upper `s`-density** of an outer measure `μ` at a point `a`,
`Θ^{*s}(μ, a) = limsup_{r ↓ 0} μ (B (a, r)) / (2 r) ^ s`,
normalized by the diameter `2r` of the ball `B (a, r)`, as in Mattila, Chapter 6. -/
def upperSDensity {n : ℕ} (s : ℝ) (μ : OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  limsup (fun r : ℝ ↦ μ (closedBall a r) / ENNReal.ofReal ((2 * r) ^ s)) (𝓝[>] (0 : ℝ))
/-- The **lower `s`-density** of an outer measure `μ` at a point `a`,
`Θ^s_*(μ, a) = liminf_{r ↓ 0} μ (B (a, r)) / (2 r) ^ s`,
normalized by the diameter `2r` of the ball `B (a, r)`, as in Mattila, Chapter 6. -/
def lowerSDensity {n : ℕ} (s : ℝ) (μ : OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  liminf (fun r : ℝ ↦ μ (closedBall a r) / ENNReal.ofReal ((2 * r) ^ s)) (𝓝[>] (0 : ℝ))
/-- The set `A` of Mattila, Lemma 14.7: the points `a` at which
`0 < Θ^s_*(μ, a) ≤ Θ^{*s}(μ, a) < ∞`. -/
def positiveFiniteDensitySet {n : ℕ} (s : ℝ) (μ : OuterMeasure (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {a | 0 < lowerSDensity s μ a ∧ lowerSDensity s μ a ≤ upperSDensity s μ a ∧
    upperSDensity s μ a < ∞}
/-- The ratio `t (a) = Θ^s_*(μ, a) / Θ^{*s}(μ, a)` appearing in Mattila, Lemma 14.7 (1). -/
def sDensityRatio {n : ℕ} (s : ℝ) (μ : OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  lowerSDensity s μ a / upperSDensity s μ a
/-- The quantity `limsup_{δ ↓ 0} sup {d (B) ^ (-s) μ (B) : B a closed ball with z ∈ B and
d (B) < δ}` appearing in the hypothesis of Mattila, Lemma 14.7 (2). Here `d (B) = 2 ρ` is the
diameter of the ball `B = B (y, ρ)`. -/
def upperBallSDensity {n : ℕ} (s : ℝ) (μ : OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (z : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  limsup (fun δ : ℝ ↦ ⨆ (y : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (_ : 0 < ρ) (_ : 2 * ρ < δ)
      (_ : z ∈ closedBall y ρ), μ (closedBall y ρ) / ENNReal.ofReal ((2 * ρ) ^ s))
    (𝓝[>] (0 : ℝ))
/-! ## Supports -/
/-- A set all of whose points lie outside the support of `μ` is `μ`-null.
(Second countability of the space is what makes the usual Lindelöf argument work.) -/
lemma measure_eq_zero_of_disjoint_support {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] {μ : OuterMeasure X} {V : Set X}
    (h : ∀ y ∈ V, y ∉ SupportOuterMeasure μ) : μ V = 0 := by
  have hcover : ∀ y : V, ∃ U : Set X, IsOpen U ∧ (y : X) ∈ U ∧ μ U = 0 := by
    rintro ⟨y, hy⟩
    have hy' := h y hy
    simp only [SupportOuterMeasure, mem_setOf_eq, not_forall] at hy'
    obtain ⟨W, hW, hW0⟩ := hy'
    obtain ⟨U, hUW, hU, hyU⟩ := mem_nhds_iff.mp hW
    exact ⟨U, hU, hyU, le_antisymm (le_trans (measure_mono hUW) (not_lt.mp hW0)) (zero_le _)⟩
  choose U hU_open hU_mem hU_null using hcover
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable U hU_open
  have hVsub : V ⊆ ⋃ y ∈ T, U y := by
    intro z hz
    rw [hTU]
    exact mem_iUnion.2 ⟨⟨z, hz⟩, hU_mem ⟨z, hz⟩⟩
  refine le_antisymm (le_trans (measure_mono hVsub) ?_) (zero_le _)
  have : μ (⋃ y ∈ T, U y) = 0 := by
    haveI := hT.to_subtype
    rw [biUnion_eq_iUnion]
    exact measure_iUnion_null fun y ↦ hU_null y
  exact this.le
/-- An open set of positive measure contains a point of the support. -/
lemma exists_mem_support_of_measure_pos {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] {μ : OuterMeasure X} {V : Set X}
    (h : 0 < μ V) : ∃ y ∈ V, y ∈ SupportOuterMeasure μ := by
  by_contra hcon
  push_neg at hcon
  exact h.ne' (measure_eq_zero_of_disjoint_support hcon)
/-! ## Blow-ups of balls with arbitrary centres -/
variable {n : ℕ}
lemma blowUpMap_preimage_ball' (a x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) (ρ : ℝ) :
    blowUpMap a r ⁻¹' (ball x ρ) = ball (a + r • x) (r * ρ) := by
  ext y
  have hx : r⁻¹ • (r • x) = x := by rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hkey : r⁻¹ • (y - a) - x = r⁻¹ • (y - (a + r • x)) := by
    simp only [smul_sub, smul_add, hx]
    abel
  simp only [blowUpMap, mem_preimage, mem_ball, dist_eq_norm, hkey, norm_smul, norm_inv,
    Real.norm_eq_abs, abs_of_pos hr]
  rw [inv_mul_lt_iff₀ hr]
lemma blowUpMap_preimage_closedBall' (a x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (ρ : ℝ) :
    blowUpMap a r ⁻¹' (closedBall x ρ) = closedBall (a + r • x) (r * ρ) := by
  ext y
  have hx : r⁻¹ • (r • x) = x := by rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hkey : r⁻¹ • (y - a) - x = r⁻¹ • (y - (a + r • x)) := by
    simp only [smul_sub, smul_add, hx]
    abel
  simp only [blowUpMap, mem_preimage, mem_closedBall, dist_eq_norm, hkey, norm_smul, norm_inv,
    Real.norm_eq_abs, abs_of_pos hr]
  rw [inv_mul_le_iff₀ hr]
lemma blowUp_smul_apply_ball (μ : OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (a x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) (c : ℝ≥0∞) (ρ : ℝ) :
    (c • OuterMeasure.map (blowUpMap a r) μ) (ball x ρ) = c * μ (ball (a + r • x) (r * ρ)) := by
  rw [OuterMeasure.smul_apply, smul_eq_mul, OuterMeasure.map_apply,
    blowUpMap_preimage_ball' a x hr ρ]
lemma blowUp_smul_apply_closedBall (μ : OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (a x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) (c : ℝ≥0∞) (ρ : ℝ) :
    (c • OuterMeasure.map (blowUpMap a r) μ) (closedBall x ρ)
      = c * μ (closedBall (a + r • x) (r * ρ)) := by
  rw [OuterMeasure.smul_apply, smul_eq_mul, OuterMeasure.map_apply,
    blowUpMap_preimage_closedBall' a x hr ρ]



variable {n : ℕ}
namespace MattilaSupportGrowth
/-- Fubini bound: the integral over `x ∈ B (x₀, R)` of `ν (B (x, r))` is at most `r ^ n` times
the volume of the unit ball times `ν (B (x₀, R + r))`. -/
lemma lintegral_measure_closedBall_le (ν : Measure (EuclideanSpace ℝ (Fin n))) [SFinite ν]
    (x₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ) {r : ℝ} (hr0 : 0 < r) :
    ∫⁻ x in closedBall x₀ R, ν (closedBall x r) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
      ≤ ENNReal.ofReal (r ^ n) *
          volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * ν (closedBall x₀ (R + r)) := by
  classical
  set S : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) := {q | dist q.1 q.2 ≤ r} with hSdef
  have hS : MeasurableSet S := (isClosed_le (by fun_prop) continuous_const).measurableSet
  set f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := fun x y ↦ S.indicator 1 (x, y) with hfdef
  have hfmeas : Measurable (Function.uncurry f) := by
    have : Function.uncurry f = S.indicator (1 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ≥0∞) := by
      funext p; simp [hfdef, Function.uncurry]
    rw [this]
    exact (measurable_one).indicator hS
  -- the inner integral in `y` recovers the measure of a ball
  have hinner : ∀ x : EuclideanSpace ℝ (Fin n), ∫⁻ y, f x y ∂ν = ν (closedBall x r) := by
    intro x
    have hfun : (fun y ↦ f x y) = (closedBall x r).indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) := by
      funext y
      by_cases hy : y ∈ closedBall x r
      · have hxy : (x, y) ∈ S := by
          simpa [hSdef, dist_comm] using (mem_closedBall.mp hy)
        simp [hfdef, hy, hxy]
      · have hxy : (x, y) ∉ S := by
          simpa [hSdef, dist_comm, mem_closedBall] using hy
        simp [hfdef, hy, hxy]
    rw [hfun, lintegral_indicator measurableSet_closedBall]
    simp
  -- the inner integral in `x`
  have houter : ∀ y : EuclideanSpace ℝ (Fin n), ∫⁻ x in closedBall x₀ R, f x y ∂volume
      ≤ (closedBall x₀ (R + r)).indicator
        (fun _ ↦ ENNReal.ofReal (r ^ n) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) y := by
    intro y
    have hfun : (fun x ↦ f x y) = (closedBall y r).indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) := by
      funext x
      by_cases hx : x ∈ closedBall y r
      · have hxy : (x, y) ∈ S := by
          simpa [hSdef] using (mem_closedBall.mp hx)
        simp [hfdef, hx, hxy]
      · have hxy : (x, y) ∉ S := by
          simpa [hSdef, mem_closedBall] using hx
        simp [hfdef, hx, hxy]
    by_cases hy : y ∈ closedBall x₀ (R + r)
    · have hle : ∫⁻ x in closedBall x₀ R, f x y ∂volume
          ≤ ∫⁻ x, f x y ∂volume := setLIntegral_le_lintegral _ _
      have hval : ∫⁻ x, f x y ∂volume = volume (closedBall y r) := by
        rw [hfun, lintegral_indicator measurableSet_closedBall]
        simp
      have hball : volume (closedBall y r)
          = ENNReal.ofReal (r ^ n) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
        have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
        have h := Measure.addHaar_closedBall (volume : Measure (EuclideanSpace ℝ (Fin n))) y hr0.le
        rw [hfr] at h
        simpa using h
      simp only [hy, indicator_of_mem]
      rw [hval, hball] at hle
      exact hle
    · have hzero : ∫⁻ x in closedBall x₀ R, f x y ∂volume = 0 := by
        refine setLIntegral_eq_zero measurableSet_closedBall ?_
        intro x hx
        have hxy : (x, y) ∉ S := by
          simp only [hSdef, mem_setOf_eq, not_le]
          have h1 : dist x x₀ ≤ R := mem_closedBall.mp hx
          have h2 : R + r < dist y x₀ := by
            simpa [mem_closedBall, not_le] using hy
          have h3 := dist_triangle y x x₀
          rw [dist_comm x y]
          linarith
        simp [hfdef, hxy]
      simp [hzero]
  -- combine via Fubini
  have hswap : ∫⁻ x, ∫⁻ y, f x y ∂ν ∂(volume.restrict (closedBall x₀ R))
      = ∫⁻ y, ∫⁻ x in closedBall x₀ R, f x y ∂volume ∂ν :=
    lintegral_lintegral_swap hfmeas.aemeasurable
  calc ∫⁻ x in closedBall x₀ R, ν (closedBall x r) ∂volume
      = ∫⁻ x, ∫⁻ y, f x y ∂ν ∂(volume.restrict (closedBall x₀ R)) := by
        simp only [hinner]
    _ = ∫⁻ y, ∫⁻ x in closedBall x₀ R, f x y ∂volume ∂ν := hswap
    _ ≤ ∫⁻ y, (closedBall x₀ (R + r)).indicator
          (fun _ ↦ ENNReal.ofReal (r ^ n) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) y ∂ν :=
        lintegral_mono houter
    _ = ENNReal.ofReal (r ^ n) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * ν (closedBall x₀ (R + r)) := by
        rw [lintegral_indicator measurableSet_closedBall, setLIntegral_const]
/-- A locally finite Borel measure on `ℝⁿ` cannot satisfy a uniform lower bound
`c ρ ^ s ≤ ν (B (x, ρ))` at every point when `s < n` and `c > 0`. -/
theorem no_uniform_lower_bound_of_lt_dim {s : ℝ} (hsn : s < n)
    (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasureOnCompacts ν]
    {c : ℝ≥0∞} (hc : 0 < c)
    (hlow : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r → r < 1 →
      c * ENNReal.ofReal (r ^ s) ≤ ν (closedBall x r)) :
    False := by
  set E := EuclideanSpace ℝ (Fin n)
  set V : ℝ≥0∞ := volume (ball (0 : E) 1) with hV
  have hV0 : V ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
  have hVtop : V ≠ ∞ := measure_ball_lt_top.ne
  have hVclosed : volume (closedBall (0 : E) 1) = V := by
    have := Measure.addHaar_closedBall (volume : Measure E) (0 : E) (zero_le_one)
    simpa [hV] using this
  set K : ℝ≥0∞ := ν (closedBall (0 : E) 2) with hK
  have hKtop : K ≠ ∞ := (isCompact_closedBall _ _).measure_lt_top.ne
  -- the key inequality at every scale
  have hkey : ∀ r : ℝ, 0 < r → r < 1 → c ≤ ENNReal.ofReal (r ^ (n - s)) * K := by
    intro r hr0 hr1
    have hlower : c * ENNReal.ofReal (r ^ s) * V
        ≤ ∫⁻ x in closedBall (0 : E) 1, ν (closedBall x r) ∂volume := by
      calc c * ENNReal.ofReal (r ^ s) * V
          = ∫⁻ _ in closedBall (0 : E) 1, c * ENNReal.ofReal (r ^ s) ∂volume := by
            rw [setLIntegral_const, hVclosed]
        _ ≤ _ := lintegral_mono fun x ↦ hlow x r hr0 hr1
    have hupper : ∫⁻ x in closedBall (0 : E) 1, ν (closedBall x r) ∂volume
        ≤ ENNReal.ofReal (r ^ n) * volume (ball (0 : E) 1) * K := by
      refine (lintegral_measure_closedBall_le ν 0 1 hr0).trans ?_
      gcongr
      exact measure_mono (closedBall_subset_closedBall (by linarith))
    have hcomb : c * ENNReal.ofReal (r ^ s) * V ≤ ENNReal.ofReal (r ^ n) * V * K :=
      hlower.trans hupper
    -- rearrange so that the volume factor can be cancelled
    have hcomb' : (c * ENNReal.ofReal (r ^ s)) * V ≤ (ENNReal.ofReal (r ^ n) * K) * V := by
      calc (c * ENNReal.ofReal (r ^ s)) * V ≤ ENNReal.ofReal (r ^ n) * V * K := hcomb
        _ = (ENNReal.ofReal (r ^ n) * K) * V := by ring
    have hcancel : c * ENNReal.ofReal (r ^ s) ≤ ENNReal.ofReal (r ^ n) * K :=
      (ENNReal.mul_le_mul_iff_left hV0 hVtop).mp hcomb'
    -- split `r ^ n = r ^ s * r ^ (n - s)`
    have hsplit : ENNReal.ofReal (r ^ n) = ENNReal.ofReal (r ^ s) * ENNReal.ofReal (r ^ (n - s)) := by
      have hreal : (r : ℝ) ^ n = r ^ s * r ^ (n - s) := by
        rw [← Real.rpow_add hr0]
        rw [show s + ((n : ℝ) - s) = (n : ℝ) by ring, Real.rpow_natCast]
      rw [hreal, ENNReal.ofReal_mul (Real.rpow_nonneg hr0.le s)]
    have hpow0 : ENNReal.ofReal (r ^ s) ≠ 0 := by
      simp [ENNReal.ofReal_eq_zero, not_le, Real.rpow_pos_of_pos hr0 s]
    have hpowtop : ENNReal.ofReal (r ^ s) ≠ ∞ := ENNReal.ofReal_ne_top
    have : c * ENNReal.ofReal (r ^ s)
        ≤ (ENNReal.ofReal (r ^ (n - s)) * K) * ENNReal.ofReal (r ^ s) := by
      calc c * ENNReal.ofReal (r ^ s) ≤ ENNReal.ofReal (r ^ n) * K := hcancel
        _ = (ENNReal.ofReal (r ^ (n - s)) * K) * ENNReal.ofReal (r ^ s) := by
            rw [hsplit]; ring
    exact (ENNReal.mul_le_mul_iff_left hpow0 hpowtop).mp this
  -- let the radius tend to `0`
  have hexp : (0 : ℝ) < (n : ℝ) - s := by linarith
  set ρ : ℕ → ℝ := fun k ↦ 1 / (k + 2) with hρ
  have hρ0 : ∀ k, 0 < ρ k := by
    intro k
    have : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    simpa [hρ] using this
  have hρ1 : ∀ k, ρ k < 1 := by
    intro k
    have hk : (1 : ℝ) < (k : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    rw [hρ, div_lt_one (by linarith)]
    exact hk
  have hρtend : Tendsto ρ atTop (𝓝 0) := by
    have h2 : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    simpa [hρ, one_div] using h2.inv_tendsto_atTop
  have hpowtend : Tendsto (fun k ↦ ENNReal.ofReal (ρ k ^ ((n : ℝ) - s)) * K) atTop (𝓝 0) := by
    have hcont : ContinuousAt (fun x : ℝ ↦ x ^ ((n : ℝ) - s)) 0 :=
      Real.continuousAt_rpow_const 0 _ (Or.inr hexp.le)
    have h1 : Tendsto (fun k ↦ ρ k ^ ((n : ℝ) - s)) atTop (𝓝 ((0 : ℝ) ^ ((n : ℝ) - s))) :=
      hcont.tendsto.comp hρtend
    rw [Real.zero_rpow hexp.ne'] at h1
    have h2 : Tendsto (fun k ↦ ENNReal.ofReal (ρ k ^ ((n : ℝ) - s))) atTop (𝓝 0) := by
      simpa using (ENNReal.continuous_ofReal.tendsto 0).comp h1
    simpa using ENNReal.Tendsto.mul_const h2 (Or.inr hKtop)
  have hle : c ≤ 0 :=
    ge_of_tendsto' hpowtend fun k ↦ hkey (ρ k) (hρ0 k) (hρ1 k)
  exact absurd (le_antisymm hle (zero_le c)) hc.ne'
end MattilaSupportGrowth
/-- **The support of a measure with `s`-dimensional lower growth, `s < n`, is not everything.**
If `ν` is a Radon outer measure on `ℝⁿ` and there is `c > 0` with
`c ρ ^ s ≤ ν (B (x, ρ))` for every `x ∈ spt ν` and every `ρ > 0`, and if `s < n`, then
`spt ν ≠ ℝⁿ`.  This is the step of Mattila's proof of Lemma 14.7 (3) which produces a point
outside the support of the tangent measure supplied by part (1). -/
theorem support_ne_univ_of_lower_growth {s : ℝ} (hsn : s < n)
    (ν : OuterMeasure (EuclideanSpace ℝ (Fin n))) (hν : RadonOuterMeasure ν)
    {c : ℝ≥0∞} (hc : 0 < c)
    (hlow : ∀ x ∈ SupportOuterMeasure ν, ∀ ρ : ℝ, 0 < ρ →
      c * ENNReal.ofReal (ρ ^ s) ≤ ν (closedBall x ρ)) :
    SupportOuterMeasure ν ≠ (univ : Set (EuclideanSpace ℝ (Fin n))) := by
  intro hfull
  set νm : Measure (EuclideanSpace ℝ (Fin n)) := ν.toMeasure hν.measurable_le_caratheodory with hνm
  letI : νm.Regular := hν.regular_toMeasure
  have hmeas : ∀ (x : EuclideanSpace ℝ (Fin n)) (ρ : ℝ),
      νm (closedBall x ρ) = ν (closedBall x ρ) := fun x ρ ↦
    toMeasure_apply ν hν.measurable_le_caratheodory measurableSet_closedBall
  refine MattilaSupportGrowth.no_uniform_lower_bound_of_lt_dim hsn νm hc ?_
  intro x r hr0 _
  rw [hmeas]
  exact hlow x (by rw [hfull]; trivial) r hr0


variable {n : ℕ}
/-- **Holes at every scale.**
If `s < n` and the measures of the balls centred on `F` of radius `ρ < r₀` are between
`p ρ ^ s` and `q ρ ^ s`, then there is `κ > 0` such that every ball `B (x, δ)` with `x ∈ F` and
`δ < r₀ / 2` contains a point at distance more than `κ δ` from `F`. -/
theorem exists_hole_of_ball_bounds {s p q r₀ : ℝ} (hsn : s < n) (hp : 0 < p) (hq : 0 < q)
    (μ : OuterMeasure (EuclideanSpace ℝ (Fin n))) (hμ : RadonOuterMeasure μ)
    {F : Set (EuclideanSpace ℝ (Fin n))}
    (hupper : ∀ y ∈ F, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (q * ρ ^ s))
    (hlower : ∀ y ∈ F, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (p * ρ ^ s) ≤ μ (closedBall y ρ)) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∀ x ∈ F, ∀ δ : ℝ, 0 < δ → δ < r₀ / 2 →
      ∃ z, dist z x ≤ δ ∧ κ * δ < infDist z F := by
  have hexp : (0 : ℝ) < (n : ℝ) - s := by linarith
  set C : ℝ := (3 : ℝ) ^ (n : ℕ) * q * (2 : ℝ) ^ s with hC
  have hCpos : 0 < C := by
    have h2 : (0 : ℝ) < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
    have h3 : (0 : ℝ) < (3 : ℝ) ^ (n : ℕ) := by positivity
    rw [hC]; positivity
  set κ₀ : ℝ := (p / (2 * C)) ^ (1 / ((n : ℝ) - s)) with hκ₀
  have hpC : 0 < p / (2 * C) := by positivity
  have hκ₀pos : 0 < κ₀ := Real.rpow_pos_of_pos hpC _
  set κ : ℝ := min (1 / 3) κ₀ with hκdef
  have hκpos : 0 < κ := lt_min (by norm_num) hκ₀pos
  have hκ3 : κ ≤ 1 / 3 := min_le_left _ _
  have hκ1 : κ < 1 := lt_of_le_of_lt hκ3 (by norm_num)
  have hkey : C * κ ^ ((n : ℝ) - s) < p := by
    have h0 : κ₀ ^ ((n : ℝ) - s) = p / (2 * C) := by
      rw [hκ₀, ← Real.rpow_mul hpC.le, one_div, inv_mul_cancel₀ hexp.ne', Real.rpow_one]
    have h1 : κ ^ ((n : ℝ) - s) ≤ κ₀ ^ ((n : ℝ) - s) :=
      Real.rpow_le_rpow hκpos.le (min_le_right _ _) hexp.le
    calc C * κ ^ ((n : ℝ) - s) ≤ C * (p / (2 * C)) := by rw [← h0]; gcongr
      _ = p / 2 := by field_simp
      _ < p := by linarith
  refine ⟨κ, hκpos, hκ1, ?_⟩
  intro x hxF δ hδ hδr
  by_contra hcon
  push_neg at hcon
  -- the associated Borel measure
  set μm := μ.toMeasure hμ.measurable_le_caratheodory with hμm
  letI : μm.Regular := hμ.regular_toMeasure
  have hmeas : ∀ (y : EuclideanSpace ℝ (Fin n)) (ρ : ℝ),
      μm (closedBall y ρ) = μ (closedBall y ρ) := fun y ρ ↦
    toMeasure_apply μ hμ.measurable_le_caratheodory measurableSet_closedBall
  have hr₀ : 0 < r₀ := by linarith
  have hκδ : 0 < κ * δ := by positivity
  have hκδr : κ * δ < r₀ := by nlinarith
  -- a uniform lower bound for the measures of the balls `B (z, 3 κ δ)`, `z ∈ B (x, δ)`
  have hz : ∀ z ∈ closedBall x δ,
      ENNReal.ofReal (p * (κ * δ) ^ s) ≤ μm (closedBall z (3 * (κ * δ))) := by
    intro z hzmem
    have h1 : infDist z F ≤ κ * δ := hcon z (mem_closedBall.mp hzmem)
    have h2 : infDist z F < 2 * (κ * δ) := lt_of_le_of_lt h1 (by linarith)
    obtain ⟨y, hyF, hdy⟩ := (Metric.infDist_lt_iff ⟨x, hxF⟩).mp h2
    have hsub : closedBall y (κ * δ) ⊆ closedBall z (3 * (κ * δ)) := by
      intro w hw
      have h3 : dist w y ≤ κ * δ := mem_closedBall.mp hw
      have h4 : dist w z ≤ dist w y + dist y z := dist_triangle _ _ _
      rw [mem_closedBall]
      rw [dist_comm y z] at h4
      linarith
    calc ENNReal.ofReal (p * (κ * δ) ^ s) ≤ μ (closedBall y (κ * δ)) :=
          hlower y hyF _ hκδ hκδr
      _ = μm (closedBall y (κ * δ)) := (hmeas _ _).symm
      _ ≤ μm (closedBall z (3 * (κ * δ))) := measure_mono hsub
  -- Fubini
  set V : ℝ≥0∞ := volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) with hV
  have hV0 : V ≠ 0 := (measure_ball_pos _ _ one_pos).ne'
  have hVtop : V ≠ ∞ := measure_ball_lt_top.ne
  have hvol : volume (closedBall x δ) = ENNReal.ofReal (δ ^ (n : ℕ)) * V := by
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
    have h := Measure.addHaar_closedBall
      (volume : Measure (EuclideanSpace ℝ (Fin n))) x hδ.le
    rw [hfr] at h
    simpa [hV] using h
  have hint1 : ENNReal.ofReal (p * (κ * δ) ^ s) * volume (closedBall x δ)
      ≤ ∫⁻ z in closedBall x δ, μm (closedBall z (3 * (κ * δ))) ∂volume := by
    calc ENNReal.ofReal (p * (κ * δ) ^ s) * volume (closedBall x δ)
        = ∫⁻ _ in closedBall x δ, ENNReal.ofReal (p * (κ * δ) ^ s) ∂volume := by
          rw [setLIntegral_const]
      _ ≤ _ := setLIntegral_mono' measurableSet_closedBall hz
  have hint2 := MattilaSupportGrowth.lintegral_measure_closedBall_le μm x δ
    (show (0 : ℝ) < 3 * (κ * δ) by positivity)
  have hball2 : μm (closedBall x (δ + 3 * (κ * δ))) ≤ ENNReal.ofReal (q * (2 * δ) ^ s) := by
    calc μm (closedBall x (δ + 3 * (κ * δ))) ≤ μm (closedBall x (2 * δ)) := by
          refine measure_mono (closedBall_subset_closedBall ?_)
          nlinarith
      _ = μ (closedBall x (2 * δ)) := hmeas _ _
      _ ≤ ENNReal.ofReal (q * (2 * δ) ^ s) := hupper x hxF _ (by linarith) (by linarith)
  -- put the pieces together
  have hchain : ENNReal.ofReal (p * (κ * δ) ^ s) * (ENNReal.ofReal (δ ^ (n : ℕ)) * V)
      ≤ ENNReal.ofReal ((3 * (κ * δ)) ^ (n : ℕ)) * V * ENNReal.ofReal (q * (2 * δ) ^ s) := by
    rw [← hvol]
    exact hint1.trans (hint2.trans (by gcongr))
  have hreal : p * (κ * δ) ^ s * δ ^ (n : ℕ)
      ≤ (3 * (κ * δ)) ^ (n : ℕ) * (q * (2 * δ) ^ s) := by
    have hA : (0 : ℝ) ≤ p * (κ * δ) ^ s * δ ^ (n : ℕ) := by positivity
    have hB : (0 : ℝ) ≤ (3 * (κ * δ)) ^ (n : ℕ) * (q * (2 * δ) ^ s) := by positivity
    have h1 : ENNReal.ofReal (p * (κ * δ) ^ s * δ ^ (n : ℕ)) * V
        ≤ ENNReal.ofReal ((3 * (κ * δ)) ^ (n : ℕ) * (q * (2 * δ) ^ s)) * V := by
      calc ENNReal.ofReal (p * (κ * δ) ^ s * δ ^ (n : ℕ)) * V
          = ENNReal.ofReal (p * (κ * δ) ^ s) * (ENNReal.ofReal (δ ^ (n : ℕ)) * V) := by
            rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ p * (κ * δ) ^ s)]; ring
        _ ≤ ENNReal.ofReal ((3 * (κ * δ)) ^ (n : ℕ)) * V * ENNReal.ofReal (q * (2 * δ) ^ s) :=
            hchain
        _ = ENNReal.ofReal ((3 * (κ * δ)) ^ (n : ℕ) * (q * (2 * δ) ^ s)) * V := by
            rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (3 * (κ * δ)) ^ (n : ℕ))]; ring
    have h2 := (ENNReal.mul_le_mul_iff_left hV0 hVtop).mp h1
    exact (ENNReal.ofReal_le_ofReal_iff hB).mp h2
  -- and derive the contradiction with the choice of `κ`
  have hpow : (κ * δ) ^ s = κ ^ s * δ ^ s := Real.mul_rpow hκpos.le hδ.le
  have hpow2 : (2 * δ) ^ s = (2 : ℝ) ^ s * δ ^ s :=
    Real.mul_rpow (by norm_num) hδ.le
  have hpow3 : (3 * (κ * δ)) ^ (n : ℕ) = (3 : ℝ) ^ (n : ℕ) * κ ^ (n : ℕ) * δ ^ (n : ℕ) := by
    ring
  rw [hpow, hpow2, hpow3] at hreal
  have hδs : (0 : ℝ) < δ ^ s := Real.rpow_pos_of_pos hδ s
  have hδn : (0 : ℝ) < δ ^ (n : ℕ) := by positivity
  have hcancel : p * κ ^ s ≤ C * κ ^ (n : ℕ) := by
    have hpos : (0 : ℝ) < δ ^ s * δ ^ (n : ℕ) := by positivity
    rw [hC]
    refine le_of_mul_le_mul_right ?_ hpos
    calc (p * κ ^ s) * (δ ^ s * δ ^ (n : ℕ)) = p * (κ ^ s * δ ^ s) * δ ^ (n : ℕ) := by ring
      _ ≤ (3 : ℝ) ^ (n : ℕ) * κ ^ (n : ℕ) * δ ^ (n : ℕ) * (q * ((2 : ℝ) ^ s * δ ^ s)) := hreal
      _ = ((3 : ℝ) ^ (n : ℕ) * q * (2 : ℝ) ^ s * κ ^ (n : ℕ)) * (δ ^ s * δ ^ (n : ℕ)) := by ring
  have hsplit : κ ^ (n : ℕ) = κ ^ ((n : ℝ) - s) * κ ^ s := by
    rw [← Real.rpow_natCast κ n, ← Real.rpow_add hκpos]
    ring_nf
  have hκs : (0 : ℝ) < κ ^ s := Real.rpow_pos_of_pos hκpos s
  rw [hsplit, ← mul_assoc] at hcancel
  have hlt : C * κ ^ ((n : ℝ) - s) * κ ^ s < p * κ ^ s := mul_lt_mul_of_pos_right hkey hκs
  linarith



/-! ## A few elementary facts -/
/-- A nonzero outer measure charges some ball centred at the origin. -/
lemma exists_ball_pos_of_ne_zero {ν : OuterMeasure (EuclideanSpace ℝ (Fin n))} (hν0 : ν ≠ 0) :
    ∃ R : ℝ, 1 ≤ R ∧ 0 < ν (ball 0 R) := by
  by_contra hcon
  push_neg at hcon
  apply hν0
  have hz : ∀ k : ℕ, ν (ball 0 ((k : ℝ) + 1)) = 0 := by
    intro k
    have hk : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) k
      linarith
    exact le_antisymm (hcon _ hk) (zero_le _)
  have hsub : (univ : Set (EuclideanSpace ℝ (Fin n))) ⊆ ⋃ k : ℕ, ball 0 ((k : ℝ) + 1) := by
    intro x _
    obtain ⟨k, hk⟩ := exists_nat_gt (dist x 0)
    exact mem_iUnion.2 ⟨k, by simp only [mem_ball]; linarith⟩
  have huniv : ν univ = 0 :=
    le_antisymm ((measure_mono hsub).trans_eq (measure_iUnion_null hz)) (zero_le _)
  ext s
  exact le_antisymm ((measure_mono (subset_univ s)).trans_eq huniv) (zero_le _)
/-- Splitting off the scaling factor `r ^ s` from `d * (r * v) ^ s`. -/
lemma ofReal_mul_rpow_mul {d v ri s : ℝ} (hd : 0 ≤ d) (hv : 0 ≤ v) (hri : 0 ≤ ri) :
    ENNReal.ofReal (d * (ri * v) ^ s)
      = ENNReal.ofReal (d * v ^ s) * ENNReal.ofReal (ri ^ s) := by
  rw [Real.mul_rpow hri hv, show d * (ri ^ s * v ^ s) = d * v ^ s * ri ^ s by ring]
  exact ENNReal.ofReal_mul (mul_nonneg hd (Real.rpow_nonneg hv s))
/-! ## The engine behind Lemma 14.7 (4) -/
section Engine
variable {s d t r₀ : ℝ} {μ ν : OuterMeasure (EuclideanSpace ℝ (Fin n))}
  {a : EuclideanSpace ℝ (Fin n)} {rs : ℕ → ℝ} {cs : ℕ → ℝ≥0∞} {lam : ℝ≥0∞}
/-- If `x` belongs to the support of a blow-up limit `ν`, then, for large `i`, the point
`a + r i • x` is within distance `ε * r i` of the support of `μ`. -/
lemma tangent_exists_nearby_support_point
    (hrpos : ∀ i, 0 < rs i)
    {hseq : ∀ i, RadonOuterMeasure (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ)}
    {hν : RadonOuterMeasure ν}
    (hconv : OuterMeasure.WeaklyConverges
      (fun i ↦ cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) ν hseq hν)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ SupportOuterMeasure ν) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∃ y ∈ SupportOuterMeasure μ, dist y (a + rs i • x) < rs i * ε := by
  have hb := (OuterMeasure.weaklyConverges_iff_compactOpenBounds _ ν hseq hν).mp hconv
  have hpos : 0 < ν (ball x ε) := measure_ball_pos hx hε
  have hli := hb.2 (ball x ε) isOpen_ball
  have hev : ∀ᶠ i in atTop,
      0 < (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) (ball x ε) :=
    eventually_lt_of_lt_liminf (lt_of_lt_of_le hpos hli)
  filter_upwards [hev] with i hi
  rw [blowUp_smul_apply_ball μ a x (hrpos i) (cs i) ε] at hi
  have hμpos : 0 < μ (ball (a + rs i • x) (rs i * ε)) := by
    rcases eq_or_lt_of_le (zero_le (μ (ball (a + rs i • x) (rs i * ε)))) with h | h
    · rw [← h, mul_zero] at hi; exact absurd hi (lt_irrefl _)
    · exact h
  obtain ⟨y, hy, hyspt⟩ := exists_mem_support_of_measure_pos hμpos
  exact ⟨y, hyspt, mem_ball.mp hy⟩
/-- Upper bound in Lemma 14.7 (1), from the uniform upper bound on `spt μ`. -/
lemma tangent_closedBall_le
    (hd : 0 ≤ d) (hr₀ : 0 < r₀) {P : Set (EuclideanSpace ℝ (Fin n))}
    (hupper : ∀ y ∈ P, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (d * ρ ^ s))
    (hrpos : ∀ i, 0 < rs i) (hr0 : Tendsto rs atTop (𝓝 0))
    (hlam : Tendsto (fun i ↦ cs i * ENNReal.ofReal (rs i ^ s)) atTop (𝓝 lam))
    (hlamfin : lam ≠ ∞)
    {hseq : ∀ i, RadonOuterMeasure (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ)}
    {hν : RadonOuterMeasure ν}
    (hconv : OuterMeasure.WeaklyConverges
      (fun i ↦ cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) ν hseq hν)
    {x : EuclideanSpace ℝ (Fin n)}
    (hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∃ y ∈ P, dist y (a + rs i • x) < rs i * ε)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ν (closedBall x ρ) ≤ ENNReal.ofReal (d * ρ ^ s) * lam := by
  have hb := (OuterMeasure.weaklyConverges_iff_compactOpenBounds _ ν hseq hν).mp hconv
  have key : ∀ v : ℝ, ρ < v → ν (closedBall x ρ) ≤ ENNReal.ofReal (d * v ^ s) * lam := by
    intro v hv
    have hvpos : 0 < v := hρ.trans hv
    set u : ℝ := (ρ + v) / 2 with hu
    have hρu : ρ < u := by rw [hu]; linarith
    have huv : u < v := by rw [hu]; linarith
    have hupos : 0 < u := hρ.trans hρu
    have hεpos : 0 < v - u := by linarith
    have h1 : ν (closedBall x ρ) ≤ ν (ball x u) :=
      measure_mono (closedBall_subset_ball hρu)
    have h2 := hb.2 (ball x u) isOpen_ball
    have hsmall : ∀ᶠ i in atTop, rs i * v < r₀ := by
      have h0 : Tendsto (fun i ↦ rs i * v) atTop (𝓝 0) := by simpa using hr0.mul_const v
      exact h0.eventually_lt_const hr₀
    have h3 : ∀ᶠ i in atTop,
        (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) (ball x u)
          ≤ ENNReal.ofReal (d * v ^ s) * (cs i * ENNReal.ofReal (rs i ^ s)) := by
      filter_upwards [hnear (v - u) hεpos, hsmall] with i hi hsm
      obtain ⟨y, hyspt, hy⟩ := hi
      have hsub : ball (a + rs i • x) (rs i * u) ⊆ closedBall y (rs i * v) := by
        intro z hz
        rw [mem_ball] at hz
        rw [mem_closedBall]
        have : dist z y ≤ dist z (a + rs i • x) + dist (a + rs i • x) y :=
          dist_triangle _ _ _
        have hy' : dist (a + rs i • x) y < rs i * (v - u) := by
          rwa [dist_comm]
        refine le_of_lt ?_
        calc dist z y ≤ dist z (a + rs i • x) + dist (a + rs i • x) y := this
          _ < rs i * u + rs i * (v - u) := by gcongr
          _ = rs i * v := by ring
      rw [blowUp_smul_apply_ball μ a x (hrpos i) (cs i) u]
      calc cs i * μ (ball (a + rs i • x) (rs i * u))
          ≤ cs i * μ (closedBall y (rs i * v)) := by gcongr
        _ ≤ cs i * ENNReal.ofReal (d * (rs i * v) ^ s) := by
            gcongr
            exact hupper y hyspt _ (mul_pos (hrpos i) hvpos) hsm
        _ = ENNReal.ofReal (d * v ^ s) * (cs i * ENNReal.ofReal (rs i ^ s)) := by
            rw [ofReal_mul_rpow_mul hd hvpos.le (hrpos i).le]
            ring
    have hlim : Tendsto
        (fun i ↦ ENNReal.ofReal (d * v ^ s) * (cs i * ENNReal.ofReal (rs i ^ s))) atTop
        (𝓝 (ENNReal.ofReal (d * v ^ s) * lam)) :=
      ENNReal.Tendsto.const_mul hlam (Or.inr ENNReal.ofReal_ne_top)
    have h4 : liminf (fun i ↦ (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) (ball x u)) atTop
        ≤ ENNReal.ofReal (d * v ^ s) * lam := by
      calc liminf (fun i ↦ (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) (ball x u)) atTop
          ≤ liminf (fun i ↦ ENNReal.ofReal (d * v ^ s) *
              (cs i * ENNReal.ofReal (rs i ^ s))) atTop :=
            liminf_le_liminf h3
        _ = ENNReal.ofReal (d * v ^ s) * lam := hlim.liminf_eq
    exact h1.trans (h2.trans h4)
  have hcont : Tendsto (fun v : ℝ ↦ ENNReal.ofReal (d * v ^ s) * lam) (𝓝[>] ρ)
      (𝓝 (ENNReal.ofReal (d * ρ ^ s) * lam)) := by
    have h1 : ContinuousAt (fun v : ℝ ↦ d * v ^ s) ρ := by
      exact continuousAt_const.mul (Real.continuousAt_rpow_const ρ s (Or.inl hρ.ne'))
    have h2 : ContinuousAt (fun v : ℝ ↦ ENNReal.ofReal (d * v ^ s)) ρ :=
      ENNReal.continuous_ofReal.continuousAt.comp h1
    exact (ENNReal.Tendsto.mul_const (h2.tendsto.mono_left nhdsWithin_le_nhds)
      (Or.inr hlamfin))
  exact ge_of_tendsto hcont (eventually_nhdsWithin_of_forall key)
/-- Lower bound in Lemma 14.7 (1), from the uniform lower bound on `spt μ`. -/
lemma le_tangent_closedBall
    (hd : 0 ≤ d) (ht : 0 ≤ t) (hr₀ : 0 < r₀) {P : Set (EuclideanSpace ℝ (Fin n))}
    (hlower : ∀ y ∈ P, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (t * d * ρ ^ s) ≤ μ (closedBall y ρ))
    (hrpos : ∀ i, 0 < rs i) (hr0 : Tendsto rs atTop (𝓝 0))
    (hlam : Tendsto (fun i ↦ cs i * ENNReal.ofReal (rs i ^ s)) atTop (𝓝 lam))
    (hlamfin : lam ≠ ∞)
    {hseq : ∀ i, RadonOuterMeasure (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ)}
    {hν : RadonOuterMeasure ν}
    (hconv : OuterMeasure.WeaklyConverges
      (fun i ↦ cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) ν hseq hν)
    {x : EuclideanSpace ℝ (Fin n)}
    (hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∃ y ∈ P, dist y (a + rs i • x) < rs i * ε)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ENNReal.ofReal (t * d * ρ ^ s) * lam ≤ ν (closedBall x ρ) := by
  have hb := (OuterMeasure.weaklyConverges_iff_compactOpenBounds _ ν hseq hν).mp hconv
  have hcompact := hb.1 (closedBall x ρ) (isCompact_closedBall _ _)
  have key : ∀ w : ℝ, 0 < w → w < ρ →
      ENNReal.ofReal (t * d * w ^ s) * lam ≤ ν (closedBall x ρ) := by
    intro w hw hwρ
    have hεpos : 0 < ρ - w := by linarith
    have hsmall : ∀ᶠ i in atTop, rs i * w < r₀ := by
      have h0 : Tendsto (fun i ↦ rs i * w) atTop (𝓝 0) := by simpa using hr0.mul_const w
      exact h0.eventually_lt_const hr₀
    have h3 : ∀ᶠ i in atTop,
        ENNReal.ofReal (t * d * w ^ s) * (cs i * ENNReal.ofReal (rs i ^ s))
          ≤ (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) (closedBall x ρ) := by
      filter_upwards [hnear (ρ - w) hεpos, hsmall] with i hi hsm
      obtain ⟨y, hyspt, hy⟩ := hi
      have hsub : closedBall y (rs i * w) ⊆ closedBall (a + rs i • x) (rs i * ρ) := by
        intro z hz
        rw [mem_closedBall] at hz ⊢
        calc dist z (a + rs i • x) ≤ dist z y + dist y (a + rs i • x) := dist_triangle _ _ _
          _ ≤ rs i * w + rs i * (ρ - w) := by gcongr
          _ = rs i * ρ := by ring
      rw [blowUp_smul_apply_closedBall μ a x (hrpos i) (cs i) ρ]
      calc ENNReal.ofReal (t * d * w ^ s) * (cs i * ENNReal.ofReal (rs i ^ s))
          = cs i * ENNReal.ofReal (t * d * (rs i * w) ^ s) := by
            rw [ofReal_mul_rpow_mul (mul_nonneg ht hd) hw.le (hrpos i).le]
            ring
        _ ≤ cs i * μ (closedBall y (rs i * w)) := by
            gcongr
            exact hlower y hyspt _ (mul_pos (hrpos i) hw) hsm
        _ ≤ cs i * μ (closedBall (a + rs i • x) (rs i * ρ)) := by
            gcongr
    have hlim : Tendsto
        (fun i ↦ ENNReal.ofReal (t * d * w ^ s) * (cs i * ENNReal.ofReal (rs i ^ s))) atTop
        (𝓝 (ENNReal.ofReal (t * d * w ^ s) * lam)) :=
      ENNReal.Tendsto.const_mul hlam (Or.inr ENNReal.ofReal_ne_top)
    calc ENNReal.ofReal (t * d * w ^ s) * lam
        = liminf (fun i ↦ ENNReal.ofReal (t * d * w ^ s) *
            (cs i * ENNReal.ofReal (rs i ^ s))) atTop := hlim.liminf_eq.symm
      _ ≤ liminf (fun i ↦
            (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) (closedBall x ρ)) atTop :=
          liminf_le_liminf h3
      _ ≤ limsup (fun i ↦
            (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) (closedBall x ρ)) atTop :=
          liminf_le_limsup
      _ ≤ ν (closedBall x ρ) := hcompact
  have hcont : Tendsto (fun w : ℝ ↦ ENNReal.ofReal (t * d * w ^ s) * lam) (𝓝[<] ρ)
      (𝓝 (ENNReal.ofReal (t * d * ρ ^ s) * lam)) := by
    have h1 : ContinuousAt (fun w : ℝ ↦ t * d * w ^ s) ρ :=
      continuousAt_const.mul (Real.continuousAt_rpow_const ρ s (Or.inl hρ.ne'))
    have h2 : ContinuousAt (fun w : ℝ ↦ ENNReal.ofReal (t * d * w ^ s)) ρ :=
      ENNReal.continuous_ofReal.continuousAt.comp h1
    exact ENNReal.Tendsto.mul_const (h2.tendsto.mono_left nhdsWithin_le_nhds) (Or.inr hlamfin)
  refine le_of_tendsto hcont ?_
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
    (eventually_gt_nhds hρ)] with w hw1 hw2
  exact key w hw2 hw1
/-- The scaling constants of a blow-up sequence are bounded, under the uniform lower bound. -/
lemma tangent_scaling_lt_top
    (hd : 0 < d) (ht : 0 < t) (hr₀ : 0 < r₀) {P : Set (EuclideanSpace ℝ (Fin n))}
    (ha : a ∈ P)
    (hlower : ∀ y ∈ P, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (t * d * ρ ^ s) ≤ μ (closedBall y ρ))
    (hrpos : ∀ i, 0 < rs i) (hr0 : Tendsto rs atTop (𝓝 0))
    (hlam : Tendsto (fun i ↦ cs i * ENNReal.ofReal (rs i ^ s)) atTop (𝓝 lam))
    {hseq : ∀ i, RadonOuterMeasure (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ)}
    {hν : RadonOuterMeasure ν}
    (hconv : OuterMeasure.WeaklyConverges
      (fun i ↦ cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) ν hseq hν) :
    lam ≠ ∞ := by
  have hb := (OuterMeasure.weaklyConverges_iff_compactOpenBounds _ ν hseq hν).mp hconv
  have hcompact := hb.1 (closedBall 0 1) (isCompact_closedBall _ _)
  have hsmall : ∀ᶠ i in atTop, rs i < r₀ := hr0.eventually_lt_const hr₀
  have h3 : ∀ᶠ i in atTop,
      ENNReal.ofReal (t * d) * (cs i * ENNReal.ofReal (rs i ^ s))
        ≤ (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) (closedBall 0 1) := by
    filter_upwards [hsmall] with i hsm
    rw [blowUp_smul_apply_closedBall μ a 0 (hrpos i) (cs i) 1, smul_zero, add_zero, mul_one]
    calc ENNReal.ofReal (t * d) * (cs i * ENNReal.ofReal (rs i ^ s))
        = cs i * ENNReal.ofReal (t * d * rs i ^ s) := by
          rw [show t * d * rs i ^ s = (t * d) * rs i ^ s from rfl,
            ENNReal.ofReal_mul (mul_nonneg ht.le hd.le)]
          ring
      _ ≤ cs i * μ (closedBall a (rs i)) := by
          gcongr
          exact hlower a ha _ (hrpos i) hsm
  have hlim : Tendsto
      (fun i ↦ ENNReal.ofReal (t * d) * (cs i * ENNReal.ofReal (rs i ^ s))) atTop
      (𝓝 (ENNReal.ofReal (t * d) * lam)) :=
    ENNReal.Tendsto.const_mul hlam (Or.inr ENNReal.ofReal_ne_top)
  have hle : ENNReal.ofReal (t * d) * lam ≤ ν (closedBall 0 1) := by
    calc ENNReal.ofReal (t * d) * lam
        = liminf (fun i ↦ ENNReal.ofReal (t * d) *
            (cs i * ENNReal.ofReal (rs i ^ s))) atTop := hlim.liminf_eq.symm
      _ ≤ liminf (fun i ↦
            (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) (closedBall 0 1)) atTop :=
          liminf_le_liminf h3
      _ ≤ limsup (fun i ↦
            (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) (closedBall 0 1)) atTop :=
          liminf_le_limsup
      _ ≤ ν (closedBall 0 1) := hcompact
  intro hlamtop
  rw [hlamtop] at hle
  rw [ENNReal.mul_top (by simp [ENNReal.ofReal_eq_zero]; positivity)] at hle
  exact (measure_closedBall_lt_top hν 0 1).ne (top_le_iff.mp hle)
/-- The scaling constants of a blow-up sequence do not degenerate, under the uniform upper
bound. -/
lemma tangent_scaling_pos
    (hd : 0 < d) (hr₀ : 0 < r₀) {P : Set (EuclideanSpace ℝ (Fin n))}
    (ha : a ∈ P)
    (hupper : ∀ y ∈ P, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (d * ρ ^ s))
    (hrpos : ∀ i, 0 < rs i) (hr0 : Tendsto rs atTop (𝓝 0))
    (hlam : Tendsto (fun i ↦ cs i * ENNReal.ofReal (rs i ^ s)) atTop (𝓝 lam))
    (hν0 : ν ≠ 0)
    {hseq : ∀ i, RadonOuterMeasure (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ)}
    {hν : RadonOuterMeasure ν}
    (hconv : OuterMeasure.WeaklyConverges
      (fun i ↦ cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) ν hseq hν) :
    0 < lam := by
  have hb := (OuterMeasure.weaklyConverges_iff_compactOpenBounds _ ν hseq hν).mp hconv
  obtain ⟨R, hR1, hRpos⟩ := exists_ball_pos_of_ne_zero hν0
  have hRpos' : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR1
  have hopen := hb.2 (ball 0 R) isOpen_ball
  have hsmall : ∀ᶠ i in atTop, rs i * R < r₀ := by
    have h0 : Tendsto (fun i ↦ rs i * R) atTop (𝓝 0) := by simpa using hr0.mul_const R
    exact h0.eventually_lt_const hr₀
  have h3 : ∀ᶠ i in atTop,
      (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) (ball 0 R)
        ≤ ENNReal.ofReal (d * R ^ s) * (cs i * ENNReal.ofReal (rs i ^ s)) := by
    filter_upwards [hsmall] with i hsm
    rw [blowUp_smul_apply_ball μ a 0 (hrpos i) (cs i) R, smul_zero, add_zero]
    calc cs i * μ (ball a (rs i * R))
        ≤ cs i * μ (closedBall a (rs i * R)) := by
          gcongr
          exact ball_subset_closedBall
      _ ≤ cs i * ENNReal.ofReal (d * (rs i * R) ^ s) := by
          gcongr
          exact hupper a ha _ (mul_pos (hrpos i) hRpos') hsm
      _ = ENNReal.ofReal (d * R ^ s) * (cs i * ENNReal.ofReal (rs i ^ s)) := by
          rw [ofReal_mul_rpow_mul hd.le hRpos'.le (hrpos i).le]
          ring
  have hlim : Tendsto
      (fun i ↦ ENNReal.ofReal (d * R ^ s) * (cs i * ENNReal.ofReal (rs i ^ s))) atTop
      (𝓝 (ENNReal.ofReal (d * R ^ s) * lam)) :=
    ENNReal.Tendsto.const_mul hlam (Or.inr ENNReal.ofReal_ne_top)
  have hle : ν (ball 0 R) ≤ ENNReal.ofReal (d * R ^ s) * lam := by
    calc ν (ball 0 R)
        ≤ liminf (fun i ↦
            (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) (ball 0 R)) atTop := hopen
      _ ≤ liminf (fun i ↦ ENNReal.ofReal (d * R ^ s) *
            (cs i * ENNReal.ofReal (rs i ^ s))) atTop := liminf_le_liminf h3
      _ = ENNReal.ofReal (d * R ^ s) * lam := hlim.liminf_eq
  rcases eq_or_lt_of_le (zero_le lam) with h | h
  · rw [← h, mul_zero] at hle
    exact absurd (le_antisymm hle (zero_le _)) hRpos.ne'
  · exact h
end Engine
/-! ## The doubling condition from uniform ball bounds -/
section Doubling
variable {s d t r₀ : ℝ} {μ : OuterMeasure (EuclideanSpace ℝ (Fin n))}
  {a : EuclideanSpace ℝ (Fin n)}
/-- Uniform two-sided ball bounds on `spt μ` imply Mattila's assumption 14.3 (1) at every point
of `spt μ`. -/
lemma limsup_ball_ratio_lt_top_of_uniform
    (hd : 0 < d) (ht : 0 < t) (hr₀ : 0 < r₀) (ha : a ∈ SupportOuterMeasure μ)
    (hupper : ∀ y ∈ SupportOuterMeasure μ, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (d * ρ ^ s))
    (hlower : ∀ y ∈ SupportOuterMeasure μ, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (t * d * ρ ^ s) ≤ μ (closedBall y ρ)) :
    limsup (fun ρ : ℝ ↦ μ (ball a (2 * ρ)) / μ (ball a ρ)) (𝓝[>] (0 : ℝ)) < ∞ := by
  set K : ℝ := (4 : ℝ) ^ s / t with hK
  have hKpos : 0 < K := by
    apply div_pos _ ht
    exact Real.rpow_pos_of_pos (by norm_num) s
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      μ (ball a (2 * ρ)) / μ (ball a ρ) ≤ ENNReal.ofReal K := by
    have h1 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (0 : ℝ) < ρ := self_mem_nhdsWithin
    have h2 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ < r₀ / 2 :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (by positivity))
    filter_upwards [h1, h2] with ρ hρ hρ'
    have hρ2 : (0 : ℝ) < 2 * ρ := by linarith
    have hρhalf : (0 : ℝ) < ρ / 2 := by linarith
    have hkey : μ (ball a (2 * ρ)) ≤ ENNReal.ofReal K * μ (ball a ρ) := by
      have hup : μ (ball a (2 * ρ)) ≤ ENNReal.ofReal (d * (2 * ρ) ^ s) :=
        le_trans (measure_mono ball_subset_closedBall)
          (hupper a ha _ hρ2 (by linarith))
      have hlo : ENNReal.ofReal (t * d * (ρ / 2) ^ s) ≤ μ (ball a ρ) :=
        le_trans (hlower a ha _ hρhalf (by linarith))
          (measure_mono (closedBall_subset_ball (by linarith)))
      have hid : d * (2 * ρ) ^ s = K * (t * d * (ρ / 2) ^ s) := by
        have h4 : (2 : ℝ) * ρ = 4 * (ρ / 2) := by ring
        rw [h4, Real.mul_rpow (by norm_num) hρhalf.le, hK]
        field_simp
      calc μ (ball a (2 * ρ)) ≤ ENNReal.ofReal (d * (2 * ρ) ^ s) := hup
        _ = ENNReal.ofReal K * ENNReal.ofReal (t * d * (ρ / 2) ^ s) := by
            rw [hid, ENNReal.ofReal_mul hKpos.le]
        _ ≤ ENNReal.ofReal K * μ (ball a ρ) := by gcongr
    exact ENNReal.div_le_of_le_mul hkey
  exact lt_of_le_of_lt (limsup_le_of_le (by isBoundedDefault) hev) ENNReal.ofReal_lt_top
end Doubling
/-! ## Nearby points of a set with a density point
This is the ingredient which replaces, in the proof of Lemma 14.7 (1), the elementary fact used
for Lemma 14.7 (4) that an open set of positive measure meets `spt μ`. -/
section DensityPoint
variable {s p q r₀ : ℝ} {μ ν : OuterMeasure (EuclideanSpace ℝ (Fin n))}
  {a : EuclideanSpace ℝ (Fin n)} {rs : ℕ → ℝ} {cs : ℕ → ℝ≥0∞}
  {B : Set (EuclideanSpace ℝ (Fin n))}
/-- If `a` is a `μ`-density point of a set `B` on which the measures of small balls are
comparable to `ρ ^ s`, and `x` lies in the support of a blow-up limit `ν` of `μ` at `a`, then for
large `i` the point `a + r i • x` is within distance `ε * r i` of `B`. -/
lemma tangent_exists_nearby_point_of_density
    (hp : 0 < p) (hq : 0 < q) (hr₀ : 0 < r₀) (haB : a ∈ B)
    (hupper : ∀ y ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (q * ρ ^ s))
    (hlower : ∀ y ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (p * ρ ^ s) ≤ μ (closedBall y ρ))
    (hdens : ∀ γ : ℝ≥0∞, 0 < γ →
      ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μ (closedBall a ρ \ B) ≤ γ * μ (closedBall a ρ))
    (hrpos : ∀ i, 0 < rs i) (hr0 : Tendsto rs atTop (𝓝 0))
    {hseq : ∀ i, RadonOuterMeasure (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ)}
    {hν : RadonOuterMeasure ν}
    (hconv : OuterMeasure.WeaklyConverges
      (fun i ↦ cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) ν hseq hν)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ SupportOuterMeasure ν) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∃ y ∈ B, dist y (a + rs i • x) < rs i * ε := by
  have hb := (OuterMeasure.weaklyConverges_iff_compactOpenBounds _ ν hseq hν).mp hconv
  set R : ℝ := ‖x‖ + ε with hR
  have hRpos : 0 < R := by positivity
  -- a positive finite amount of mass in the limit ball `ball x ε`
  have hνpos : 0 < ν (ball x ε) := measure_ball_pos hx hε
  have hmin_pos : 0 < min (ν (ball x ε)) 1 := lt_min hνpos one_pos
  have hmin_ne_top : min (ν (ball x ε)) 1 ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  set β : ℝ≥0∞ := min (ν (ball x ε)) 1 / 2 with hβ
  have hβpos : 0 < β := ENNReal.half_pos hmin_pos.ne'
  have hβlt : β < ν (ball x ε) :=
    lt_of_lt_of_le (ENNReal.half_lt_self hmin_pos.ne' hmin_ne_top) (min_le_left _ _)
  have hev1 : ∀ᶠ i in atTop,
      β < (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) (ball x ε) :=
    eventually_lt_of_lt_liminf (lt_of_lt_of_le hβlt (hb.2 (ball x ε) isOpen_ball))
  -- the normalizing constants are eventually bounded above
  set M : ℝ≥0∞ := ν (closedBall 0 1) + 1 with hM
  have hνcb : ν (closedBall 0 1) ≠ ∞ := (measure_closedBall_lt_top hν 0 1).ne
  have hMtop : M ≠ ∞ := by simp [hM, ENNReal.add_eq_top, hνcb]
  have hev2 : ∀ᶠ i in atTop, cs i * μ (closedBall a (rs i)) < M := by
    have hlimsup := hb.1 (closedBall 0 1) (isCompact_closedBall _ _)
    have h := eventually_lt_of_limsup_lt
      (lt_of_le_of_lt hlimsup (ENNReal.lt_add_right hνcb one_ne_zero))
    filter_upwards [h] with i hi
    rwa [blowUp_smul_apply_closedBall μ a 0 (hrpos i) (cs i) 1, smul_zero, add_zero,
      mul_one] at hi
  -- comparison of the measures of the balls `B (a, R r i)` and `B (a, r i)`
  set K : ℝ≥0∞ := ENNReal.ofReal (q * R ^ s) / ENNReal.ofReal p with hK
  have hpne : ENNReal.ofReal p ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hp
  have hKtop : K ≠ ∞ := ENNReal.div_ne_top ENNReal.ofReal_ne_top hpne
  have hKMtop : K * M ≠ ∞ := ENNReal.mul_ne_top hKtop hMtop
  set γ : ℝ≥0∞ := β / (K * M) with hγ
  have hγpos : 0 < γ := ENNReal.div_pos_iff.2 ⟨hβpos.ne', hKMtop⟩
  -- the density hypothesis, transported to the sequence of radii `R * r i`
  have htendR : Tendsto (fun i ↦ rs i * R) atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · simpa using hr0.mul_const R
    · exact Eventually.of_forall fun i ↦ mul_pos (hrpos i) hRpos
  have hev3 : ∀ᶠ i in atTop,
      μ (closedBall a (rs i * R) \ B) ≤ γ * μ (closedBall a (rs i * R)) :=
    htendR.eventually (hdens γ hγpos)
  have hev4 : ∀ᶠ i in atTop, rs i * R < r₀ := by
    have h0 : Tendsto (fun i ↦ rs i * R) atTop (𝓝 0) := by simpa using hr0.mul_const R
    exact h0.eventually_lt_const hr₀
  have hev5 : ∀ᶠ i in atTop, rs i < r₀ := hr0.eventually_lt_const hr₀
  filter_upwards [hev1, hev2, hev3, hev4, hev5] with i h1 h2 h3 h4 h5
  by_contra hcon
  push_neg at hcon
  -- if no point of `B` is near `a + r i • x`, the ball `U i` is contained in `B (a, R r i) \ B`
  have hsub : ball (a + rs i • x) (rs i * ε) ⊆ closedBall a (rs i * R) \ B := by
    intro z hz
    rw [mem_ball] at hz
    have hdist : dist (a + rs i • x) a = rs i * ‖x‖ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (hrpos i)]
    constructor
    · rw [mem_closedBall]
      calc dist z a ≤ dist z (a + rs i • x) + dist (a + rs i • x) a := dist_triangle _ _ _
        _ ≤ rs i * ε + rs i * ‖x‖ := by rw [hdist]; gcongr
        _ = rs i * R := by rw [hR]; ring
    · intro hzB
      exact absurd hz (not_lt.2 (hcon z hzB))
  have hKineq : μ (closedBall a (rs i * R)) ≤ K * μ (closedBall a (rs i)) := by
    have hup : μ (closedBall a (rs i * R))
        ≤ ENNReal.ofReal (q * R ^ s) * ENNReal.ofReal (rs i ^ s) := by
      rw [← ofReal_mul_rpow_mul hq.le hRpos.le (hrpos i).le]
      exact hupper a haB _ (mul_pos (hrpos i) hRpos) h4
    have hlo : ENNReal.ofReal p * ENNReal.ofReal (rs i ^ s) ≤ μ (closedBall a (rs i)) := by
      rw [← ENNReal.ofReal_mul hp.le]
      exact hlower a haB _ (hrpos i) h5
    calc μ (closedBall a (rs i * R))
        ≤ ENNReal.ofReal (q * R ^ s) * ENNReal.ofReal (rs i ^ s) := hup
      _ = K * (ENNReal.ofReal p * ENNReal.ofReal (rs i ^ s)) := by
          rw [hK, ← mul_assoc, ENNReal.div_mul_cancel hpne ENNReal.ofReal_ne_top]
      _ ≤ K * μ (closedBall a (rs i)) := by gcongr
  have hchain : β < β := by
    calc β < (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) (ball x ε) := h1
      _ = cs i * μ (ball (a + rs i • x) (rs i * ε)) :=
          blowUp_smul_apply_ball μ a x (hrpos i) (cs i) ε
      _ ≤ cs i * (γ * (K * μ (closedBall a (rs i)))) := by
          gcongr
          calc μ (ball (a + rs i • x) (rs i * ε))
              ≤ μ (closedBall a (rs i * R) \ B) := measure_mono hsub
            _ ≤ γ * μ (closedBall a (rs i * R)) := h3
            _ ≤ γ * (K * μ (closedBall a (rs i))) := by gcongr
      _ = γ * K * (cs i * μ (closedBall a (rs i))) := by ring
      _ ≤ γ * K * M := by gcongr
      _ = γ * (K * M) := by ring
      _ ≤ β := ENNReal.mul_le_of_le_div le_rfl
  exact absurd hchain (lt_irrefl _)
/-- Under the hypotheses of the density-point lemma, the blow-ups give arbitrarily small mass to
sets which live at a fixed multiple of the scale `r i` around `a` and avoid `B`. -/
lemma tangent_smul_measure_le_of_disjoint
    (hp : 0 < p) (hq : 0 < q) (hr₀ : 0 < r₀) (haB : a ∈ B)
    (hupper : ∀ y ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (q * ρ ^ s))
    (hlower : ∀ y ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (p * ρ ^ s) ≤ μ (closedBall y ρ))
    (hdens : ∀ γ : ℝ≥0∞, 0 < γ →
      ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μ (closedBall a ρ \ B) ≤ γ * μ (closedBall a ρ))
    (hrpos : ∀ i, 0 < rs i) (hr0 : Tendsto rs atTop (𝓝 0))
    {hseq : ∀ i, RadonOuterMeasure (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ)}
    {hν : RadonOuterMeasure ν}
    (hconv : OuterMeasure.WeaklyConverges
      (fun i ↦ cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) ν hseq hν)
    {R : ℝ} (hR : 0 < R) {β : ℝ≥0∞} (hβ : 0 < β) :
    ∀ᶠ i in atTop, ∀ S : Set (EuclideanSpace ℝ (Fin n)),
      S ⊆ closedBall a (rs i * R) → Disjoint S B → cs i * μ S ≤ β := by
  have hb := (OuterMeasure.weaklyConverges_iff_compactOpenBounds _ ν hseq hν).mp hconv
  set M : ℝ≥0∞ := ν (closedBall 0 1) + 1 with hM
  have hνcb : ν (closedBall 0 1) ≠ ∞ := (measure_closedBall_lt_top hν 0 1).ne
  have hMtop : M ≠ ∞ := by simp [hM, ENNReal.add_eq_top, hνcb]
  have hev2 : ∀ᶠ i in atTop, cs i * μ (closedBall a (rs i)) < M := by
    have hlimsup := hb.1 (closedBall 0 1) (isCompact_closedBall _ _)
    have h := eventually_lt_of_limsup_lt
      (lt_of_le_of_lt hlimsup (ENNReal.lt_add_right hνcb one_ne_zero))
    filter_upwards [h] with i hi
    rwa [blowUp_smul_apply_closedBall μ a 0 (hrpos i) (cs i) 1, smul_zero, add_zero,
      mul_one] at hi
  set K : ℝ≥0∞ := ENNReal.ofReal (q * R ^ s) / ENNReal.ofReal p with hK
  have hpne : ENNReal.ofReal p ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hp
  have hKtop : K ≠ ∞ := ENNReal.div_ne_top ENNReal.ofReal_ne_top hpne
  have hKMtop : K * M ≠ ∞ := ENNReal.mul_ne_top hKtop hMtop
  set γ : ℝ≥0∞ := β / (K * M) with hγ
  have hγpos : 0 < γ := ENNReal.div_pos_iff.2 ⟨hβ.ne', hKMtop⟩
  have htendR : Tendsto (fun i ↦ rs i * R) atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨by simpa using hr0.mul_const R,
      Eventually.of_forall fun i ↦ mul_pos (hrpos i) hR⟩
  have hev3 : ∀ᶠ i in atTop,
      μ (closedBall a (rs i * R) \ B) ≤ γ * μ (closedBall a (rs i * R)) :=
    htendR.eventually (hdens γ hγpos)
  have hev4 : ∀ᶠ i in atTop, rs i * R < r₀ := by
    have h0 : Tendsto (fun i ↦ rs i * R) atTop (𝓝 0) := by simpa using hr0.mul_const R
    exact h0.eventually_lt_const hr₀
  have hev5 : ∀ᶠ i in atTop, rs i < r₀ := hr0.eventually_lt_const hr₀
  filter_upwards [hev2, hev3, hev4, hev5] with i h2 h3 h4 h5 S hSsub hSdisj
  have hKineq : μ (closedBall a (rs i * R)) ≤ K * μ (closedBall a (rs i)) := by
    have hup : μ (closedBall a (rs i * R))
        ≤ ENNReal.ofReal (q * R ^ s) * ENNReal.ofReal (rs i ^ s) := by
      rw [← ofReal_mul_rpow_mul hq.le hR.le (hrpos i).le]
      exact hupper a haB _ (mul_pos (hrpos i) hR) h4
    have hlo : ENNReal.ofReal p * ENNReal.ofReal (rs i ^ s) ≤ μ (closedBall a (rs i)) := by
      rw [← ENNReal.ofReal_mul hp.le]
      exact hlower a haB _ (hrpos i) h5
    calc μ (closedBall a (rs i * R))
        ≤ ENNReal.ofReal (q * R ^ s) * ENNReal.ofReal (rs i ^ s) := hup
      _ = K * (ENNReal.ofReal p * ENNReal.ofReal (rs i ^ s)) := by
          rw [hK, ← mul_assoc, ENNReal.div_mul_cancel hpne ENNReal.ofReal_ne_top]
      _ ≤ K * μ (closedBall a (rs i)) := by gcongr
  calc cs i * μ S ≤ cs i * (γ * (K * μ (closedBall a (rs i)))) := by
        gcongr
        calc μ S ≤ μ (closedBall a (rs i * R) \ B) :=
              measure_mono (subset_diff.2 ⟨hSsub, hSdisj⟩)
          _ ≤ γ * μ (closedBall a (rs i * R)) := h3
          _ ≤ γ * (K * μ (closedBall a (rs i))) := by gcongr
    _ = γ * K * (cs i * μ (closedBall a (rs i))) := by ring
    _ ≤ γ * K * M := by gcongr
    _ = γ * (K * M) := by ring
    _ ≤ β := ENNReal.mul_le_of_le_div le_rfl
/-- Upper bound for tangent measures of balls with **arbitrary** centres, from a bound on the
measures of all small balls meeting the set `P`. -/
lemma tangent_closedBall_le_of_ball_bounds {d : ℝ} {lam : ℝ≥0∞}
    (hd : 0 ≤ d) (hr₀ : 0 < r₀) {P : Set (EuclideanSpace ℝ (Fin n))}
    (hballbd : ∀ z ∈ P, ∀ (y : EuclideanSpace ℝ (Fin n)) (w : ℝ), 0 < w → w < r₀ →
      z ∈ closedBall y w → μ (closedBall y w) ≤ ENNReal.ofReal (d * w ^ s))
    (hrpos : ∀ i, 0 < rs i) (hr0 : Tendsto rs atTop (𝓝 0))
    (hlam : Tendsto (fun i ↦ cs i * ENNReal.ofReal (rs i ^ s)) atTop (𝓝 lam))
    (hlamfin : lam ≠ ∞)
    {hseq : ∀ i, RadonOuterMeasure (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ)}
    {hν : RadonOuterMeasure ν}
    (hconv : OuterMeasure.WeaklyConverges
      (fun i ↦ cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) ν hseq hν)
    (hsmall : ∀ β : ℝ≥0∞, 0 < β → ∀ R : ℝ, 0 < R → ∀ᶠ i in atTop,
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), S ⊆ closedBall a (rs i * R) → Disjoint S P →
        cs i * μ S ≤ β)
    (x : EuclideanSpace ℝ (Fin n)) {ρ : ℝ} (hρ : 0 < ρ) :
    ν (closedBall x ρ) ≤ ENNReal.ofReal (d * ρ ^ s) * lam := by
  have hb := (OuterMeasure.weaklyConverges_iff_compactOpenBounds _ ν hseq hν).mp hconv
  have key : ∀ u : ℝ, ρ < u → ν (closedBall x ρ) ≤ ENNReal.ofReal (d * u ^ s) * lam := by
    intro u hu
    have hupos : 0 < u := hρ.trans hu
    have hRpos : 0 < ‖x‖ + u := by positivity
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    have hβ : (0 : ℝ≥0∞) < (ε : ℝ≥0∞) := by exact_mod_cast hε
    have hsm : ∀ᶠ i in atTop, rs i * u < r₀ := by
      have h0 : Tendsto (fun i ↦ rs i * u) atTop (𝓝 0) := by simpa using hr0.mul_const u
      exact h0.eventually_lt_const hr₀
    have h3 : ∀ᶠ i in atTop,
        (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) (ball x u)
          ≤ ENNReal.ofReal (d * u ^ s) * (cs i * ENNReal.ofReal (rs i ^ s))
            + (ε : ℝ≥0∞) := by
      filter_upwards [hsmall (ε : ℝ≥0∞) hβ (‖x‖ + u) hRpos, hsm] with i hi hsmi
      rw [blowUp_smul_apply_ball μ a x (hrpos i) (cs i) u]
      by_cases hmeet : ∃ z ∈ P, z ∈ closedBall (a + rs i • x) (rs i * u)
      · obtain ⟨z, hzP, hz⟩ := hmeet
        have hball : μ (ball (a + rs i • x) (rs i * u))
            ≤ ENNReal.ofReal (d * (rs i * u) ^ s) :=
          le_trans (measure_mono ball_subset_closedBall)
            (hballbd z hzP _ _ (mul_pos (hrpos i) hupos) hsmi hz)
        calc cs i * μ (ball (a + rs i • x) (rs i * u))
            ≤ cs i * ENNReal.ofReal (d * (rs i * u) ^ s) := by gcongr
          _ = ENNReal.ofReal (d * u ^ s) * (cs i * ENNReal.ofReal (rs i ^ s)) := by
              rw [ofReal_mul_rpow_mul hd hupos.le (hrpos i).le]
              ring
          _ ≤ _ := le_self_add
      · push_neg at hmeet
        have hdisj : Disjoint (closedBall (a + rs i • x) (rs i * u)) P := by
          rw [Set.disjoint_right]
          intro z hzP hz
          exact hmeet z hzP hz
        have hsub : closedBall (a + rs i • x) (rs i * u)
            ⊆ closedBall a (rs i * (‖x‖ + u)) := by
          intro z hz
          rw [mem_closedBall] at hz ⊢
          have hdist : dist (a + rs i • x) a = rs i * ‖x‖ := by
            rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
              abs_of_pos (hrpos i)]
          calc dist z a ≤ dist z (a + rs i • x) + dist (a + rs i • x) a := dist_triangle _ _ _
            _ ≤ rs i * u + rs i * ‖x‖ := by rw [hdist]; gcongr
            _ = rs i * (‖x‖ + u) := by ring
        calc cs i * μ (ball (a + rs i • x) (rs i * u))
            ≤ cs i * μ (closedBall (a + rs i • x) (rs i * u)) := by
              gcongr
              exact ball_subset_closedBall
          _ ≤ (ε : ℝ≥0∞) := hi _ hsub hdisj
          _ ≤ _ := le_add_self
    have hlim : Tendsto
        (fun i ↦ ENNReal.ofReal (d * u ^ s) * (cs i * ENNReal.ofReal (rs i ^ s))
          + (ε : ℝ≥0∞)) atTop
        (𝓝 (ENNReal.ofReal (d * u ^ s) * lam + (ε : ℝ≥0∞))) :=
      (ENNReal.Tendsto.const_mul hlam (Or.inr ENNReal.ofReal_ne_top)).add tendsto_const_nhds
    calc ν (closedBall x ρ) ≤ ν (ball x u) := measure_mono (closedBall_subset_ball hu)
      _ ≤ liminf (fun i ↦ (cs i • OuterMeasure.map (blowUpMap a (rs i)) μ) (ball x u))
            atTop := hb.2 (ball x u) isOpen_ball
      _ ≤ liminf (fun i ↦ ENNReal.ofReal (d * u ^ s) * (cs i * ENNReal.ofReal (rs i ^ s))
            + (ε : ℝ≥0∞)) atTop := liminf_le_liminf h3
      _ = ENNReal.ofReal (d * u ^ s) * lam + (ε : ℝ≥0∞) := hlim.liminf_eq
  have hcont : Tendsto (fun u : ℝ ↦ ENNReal.ofReal (d * u ^ s) * lam) (𝓝[>] ρ)
      (𝓝 (ENNReal.ofReal (d * ρ ^ s) * lam)) := by
    have h1 : ContinuousAt (fun u : ℝ ↦ d * u ^ s) ρ :=
      continuousAt_const.mul (Real.continuousAt_rpow_const ρ s (Or.inl hρ.ne'))
    have h2 : ContinuousAt (fun u : ℝ ↦ ENNReal.ofReal (d * u ^ s)) ρ :=
      ENNReal.continuous_ofReal.continuousAt.comp h1
    exact ENNReal.Tendsto.mul_const (h2.tendsto.mono_left nhdsWithin_le_nhds) (Or.inr hlamfin)
  exact ge_of_tendsto hcont (eventually_nhdsWithin_of_forall key)
end DensityPoint
/-! ## Mattila's reduction step for Lemma 14.7 (1) -/
/-- **Mattila, Lemma 14.7, reduction step.**
Let `τ`, `d`, `r₀` be positive numbers and let `B` be a set with
`τ d ρ ^ s ≤ μ (B (y, ρ)) ≤ d ρ ^ s` for `y ∈ B` and `0 < ρ < r₀`.
If `a ∈ B` is a `μ`-density point of `B`, then every tangent measure `ν ∈ Tan (μ, a)` satisfies
`τ c ρ ^ s ≤ ν (B (x, ρ)) ≤ c ρ ^ s` for `x ∈ spt ν` and `0 < ρ < ∞`, for some positive finite
constant `c`. -/
theorem tangent_ball_bounds_of_density_point {s d t r₀ : ℝ}
    (hd : 0 < d) (ht : 0 < t) (hr₀ : 0 < r₀)
    (μ : OuterMeasure (EuclideanSpace ℝ (Fin n))) (hμ : RadonOuterMeasure μ)
    {B : Set (EuclideanSpace ℝ (Fin n))}
    (hbounds : ∀ y ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (t * d * ρ ^ s) ≤ μ (closedBall y ρ) ∧
        μ (closedBall y ρ) ≤ ENNReal.ofReal (d * ρ ^ s))
    {a : EuclideanSpace ℝ (Fin n)} (haB : a ∈ B)
    (hdens : ∀ γ : ℝ≥0∞, 0 < γ →
      ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μ (closedBall a ρ \ B) ≤ γ * μ (closedBall a ρ))
    (ν : OuterMeasure (EuclideanSpace ℝ (Fin n))) (htan : IsTangentMeasure μ ν hμ a) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
      ∀ x ∈ SupportOuterMeasure ν, ∀ ρ : ℝ, 0 < ρ →
        ENNReal.ofReal t * c * ENNReal.ofReal (ρ ^ s) ≤ ν (closedBall x ρ) ∧
          ν (closedBall x ρ) ≤ c * ENNReal.ofReal (ρ ^ s) := by
  have hupper : ∀ y ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (d * ρ ^ s) :=
    fun y hy ρ h1 h2 ↦ (hbounds y hy ρ h1 h2).2
  have hlower : ∀ y ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (t * d * ρ ^ s) ≤ μ (closedBall y ρ) :=
    fun y hy ρ h1 h2 ↦ (hbounds y hy ρ h1 h2).1
  obtain ⟨hν, hν0, rs, cs, hrpos, hcpos, hcfin, hr0, hseq, hconv⟩ := htan
  obtain ⟨lam, -, φ, hφ, hlam⟩ := (isCompact_univ (X := ℝ≥0∞)).tendsto_subseq
    (x := fun i ↦ cs i * ENNReal.ofReal (rs i ^ s)) (fun i ↦ mem_univ _)
  have hrpos' : ∀ j, 0 < rs (φ j) := fun j ↦ hrpos _
  have hr0' : Tendsto (fun j ↦ rs (φ j)) atTop (𝓝 0) := hr0.comp hφ.tendsto_atTop
  have hconv' : OuterMeasure.WeaklyConverges
      (fun j ↦ cs (φ j) • OuterMeasure.map (blowUpMap a (rs (φ j))) μ) ν
      (fun j ↦ hseq (φ j)) hν := hconv.comp hφ.tendsto_atTop
  have hlamfin : lam ≠ ∞ :=
    tangent_scaling_lt_top hd ht hr₀ haB hlower hrpos' hr0' hlam hconv'
  have hlampos : 0 < lam :=
    tangent_scaling_pos hd hr₀ haB hupper hrpos' hr0' hlam hν0 hconv'
  refine ⟨ENNReal.ofReal d * lam, ENNReal.mul_pos (ENNReal.ofReal_pos.2 hd).ne' hlampos.ne',
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hlamfin, ?_⟩
  intro x hx ρ hρ
  have hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
      ∃ y ∈ B, dist y (a + rs (φ j) • x) < rs (φ j) * ε :=
    fun ε hε ↦ tangent_exists_nearby_point_of_density (mul_pos ht hd) hd hr₀ haB hupper
      hlower hdens hrpos' hr0' hconv' hx hε
  have hup := tangent_closedBall_le hd.le hr₀ hupper hrpos' hr0' hlam hlamfin hconv' hnear hρ
  have hlo := le_tangent_closedBall hd.le ht.le hr₀ hlower hrpos' hr0' hlam hlamfin hconv'
    hnear hρ
  constructor
  · refine le_trans (le_of_eq ?_) hlo
    rw [ENNReal.ofReal_mul (mul_nonneg ht.le hd.le), ENNReal.ofReal_mul ht.le]
    ring
  · refine le_trans hup (le_of_eq ?_)
    rw [ENNReal.ofReal_mul hd.le]
    ring
/-! ## Mattila's reduction step for Lemma 14.7 (2) -/
/-- **Mattila, Lemma 14.7, reduction step for part (2).**
If, in addition to the hypotheses of the reduction step for part (1), the measures of *all* small
balls meeting `B` are bounded by `d ρ ^ s`, then the upper bound for the tangent measure holds for
balls with arbitrary centres, with the same constant `c`. -/
theorem tangent_ball_bounds_of_density_point_of_ball_bounds {s d t r₀ : ℝ}
    (hd : 0 < d) (ht : 0 < t) (hr₀ : 0 < r₀)
    (μ : OuterMeasure (EuclideanSpace ℝ (Fin n))) (hμ : RadonOuterMeasure μ)
    {B : Set (EuclideanSpace ℝ (Fin n))}
    (hbounds : ∀ y ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (t * d * ρ ^ s) ≤ μ (closedBall y ρ) ∧
        μ (closedBall y ρ) ≤ ENNReal.ofReal (d * ρ ^ s))
    (hballbd : ∀ z ∈ B, ∀ (y : EuclideanSpace ℝ (Fin n)) (w : ℝ), 0 < w → w < r₀ →
      z ∈ closedBall y w → μ (closedBall y w) ≤ ENNReal.ofReal (d * w ^ s))
    {a : EuclideanSpace ℝ (Fin n)} (haB : a ∈ B)
    (hdens : ∀ γ : ℝ≥0∞, 0 < γ →
      ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μ (closedBall a ρ \ B) ≤ γ * μ (closedBall a ρ))
    (ν : OuterMeasure (EuclideanSpace ℝ (Fin n))) (htan : IsTangentMeasure μ ν hμ a) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
      (∀ x ∈ SupportOuterMeasure ν, ∀ ρ : ℝ, 0 < ρ →
        ENNReal.ofReal t * c * ENNReal.ofReal (ρ ^ s) ≤ ν (closedBall x ρ)) ∧
      ∀ (x : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 < ρ →
        ν (closedBall x ρ) ≤ c * ENNReal.ofReal (ρ ^ s) := by
  have hupper : ∀ y ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (d * ρ ^ s) :=
    fun y hy ρ h1 h2 ↦ (hbounds y hy ρ h1 h2).2
  have hlower : ∀ y ∈ B, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (t * d * ρ ^ s) ≤ μ (closedBall y ρ) :=
    fun y hy ρ h1 h2 ↦ (hbounds y hy ρ h1 h2).1
  obtain ⟨hν, hν0, rs, cs, hrpos, hcpos, hcfin, hr0, hseq, hconv⟩ := htan
  obtain ⟨lam, -, φ, hφ, hlam⟩ := (isCompact_univ (X := ℝ≥0∞)).tendsto_subseq
    (x := fun i ↦ cs i * ENNReal.ofReal (rs i ^ s)) (fun i ↦ mem_univ _)
  have hrpos' : ∀ j, 0 < rs (φ j) := fun j ↦ hrpos _
  have hr0' : Tendsto (fun j ↦ rs (φ j)) atTop (𝓝 0) := hr0.comp hφ.tendsto_atTop
  have hconv' : OuterMeasure.WeaklyConverges
      (fun j ↦ cs (φ j) • OuterMeasure.map (blowUpMap a (rs (φ j))) μ) ν
      (fun j ↦ hseq (φ j)) hν := hconv.comp hφ.tendsto_atTop
  have hlamfin : lam ≠ ∞ :=
    tangent_scaling_lt_top hd ht hr₀ haB hlower hrpos' hr0' hlam hconv'
  have hlampos : 0 < lam :=
    tangent_scaling_pos hd hr₀ haB hupper hrpos' hr0' hlam hν0 hconv'
  have hsmall : ∀ β : ℝ≥0∞, 0 < β → ∀ R : ℝ, 0 < R → ∀ᶠ j in atTop,
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), S ⊆ closedBall a (rs (φ j) * R) →
        Disjoint S B → cs (φ j) * μ S ≤ β :=
    fun β hβ R hR ↦ tangent_smul_measure_le_of_disjoint (mul_pos ht hd) hd hr₀ haB hupper
      hlower hdens hrpos' hr0' hconv' hR hβ
  refine ⟨ENNReal.ofReal d * lam, ENNReal.mul_pos (ENNReal.ofReal_pos.2 hd).ne' hlampos.ne',
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hlamfin, ?_, ?_⟩
  · intro x hx ρ hρ
    have hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
        ∃ y ∈ B, dist y (a + rs (φ j) • x) < rs (φ j) * ε :=
      fun ε hε ↦ tangent_exists_nearby_point_of_density (mul_pos ht hd) hd hr₀ haB hupper
        hlower hdens hrpos' hr0' hconv' hx hε
    have hlo := le_tangent_closedBall hd.le ht.le hr₀ hlower hrpos' hr0' hlam hlamfin hconv'
      hnear hρ
    refine le_trans (le_of_eq ?_) hlo
    rw [ENNReal.ofReal_mul (mul_nonneg ht.le hd.le), ENNReal.ofReal_mul ht.le]
    ring
  · intro x ρ hρ
    have hup := tangent_closedBall_le_of_ball_bounds hd.le hr₀ hballbd hrpos' hr0' hlam
      hlamfin hconv' hsmall x hρ
    refine le_trans hup (le_of_eq ?_)
    rw [ENNReal.ofReal_mul hd.le]
    ring


/-! ## Points with uniformly comparable ball measures -/
/-- `goodSet s p q m μ` is the set of points `z` such that
`p ρ ^ s ≤ μ (B (z, ρ)) ≤ q ρ ^ s` for every radius `0 < ρ < 1 / (m + 1)`. -/
def goodSet (s p q : ℝ) (m : ℕ) (μ : OuterMeasure (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {z | ∀ ρ : ℝ, 0 < ρ → ρ < 1 / (m + 1) →
    ENNReal.ofReal (p * ρ ^ s) ≤ μ (closedBall z ρ) ∧
      μ (closedBall z ρ) ≤ ENNReal.ofReal (q * ρ ^ s)}
/-- Enlarging the admissible range `[p, q]` enlarges `goodSet`. -/
lemma goodSet_subset {s p q p' q' : ℝ} {m : ℕ}
    {μ : OuterMeasure (EuclideanSpace ℝ (Fin n))} (hp : p' ≤ p) (hq : q ≤ q') :
    goodSet s p q m μ ⊆ goodSet s p' q' m μ := by
  intro z hz ρ hρ hρm
  obtain ⟨h1, h2⟩ := hz ρ hρ hρm
  refine ⟨le_trans (ENNReal.ofReal_le_ofReal ?_) h1,
    le_trans h2 (ENNReal.ofReal_le_ofReal ?_)⟩
  · exact mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hρ.le s)
  · exact mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hρ.le s)
/-- Passing to a smaller range of radii enlarges `goodSet`. -/
lemma goodSet_mono_nat {s p q : ℝ} {m m' : ℕ}
    {μ : OuterMeasure (EuclideanSpace ℝ (Fin n))} (hm : m ≤ m') :
    goodSet s p q m μ ⊆ goodSet s p q m' μ := by
  intro z hz ρ hρ hρm
  refine hz ρ hρ (lt_of_lt_of_le hρm ?_)
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast Nat.add_le_add_right hm 1
/-- The sets `goodSet s p q m μ` are closed, hence Borel. -/
lemma isClosed_goodSet (s p q : ℝ) (m : ℕ)
    (μ : OuterMeasure (EuclideanSpace ℝ (Fin n))) : IsClosed (goodSet s p q m μ) := by
  refine isClosed_of_closure_subset fun z hz ρ hρ hρm ↦ ⟨?_, ?_⟩
  · -- shrink the radius slightly and let the shrinking tend to `0`
    have hbase : ContinuousAt (fun δ : ℝ ↦ ρ - δ) 0 := by fun_prop
    have hrpow : ContinuousAt (fun x : ℝ ↦ x ^ s) (ρ - 0) := by
      simpa using Real.continuousAt_rpow_const ρ s (Or.inl hρ.ne')
    have h1 : ContinuousAt (fun δ : ℝ ↦ p * (ρ - δ) ^ s) 0 :=
      continuousAt_const.mul (hrpow.comp hbase)
    have htend : Tendsto (fun δ : ℝ ↦ ENNReal.ofReal (p * (ρ - δ) ^ s)) (𝓝[>] (0 : ℝ))
        (𝓝 (ENNReal.ofReal (p * ρ ^ s))) := by
      have h2 := (ENNReal.continuous_ofReal.continuousAt.comp h1).tendsto
      simp only [Function.comp_def, sub_zero] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds hρ)] with δ hδ hδρ
    have hδ0 : 0 < δ := Set.mem_Ioi.mp hδ
    obtain ⟨y, hyB, hdist⟩ := Metric.mem_closure_iff.mp hz δ hδ0
    have hsub : closedBall y (ρ - δ) ⊆ closedBall z ρ := by
      intro w hw
      rw [mem_closedBall] at hw ⊢
      calc dist w z ≤ dist w y + dist y z := dist_triangle _ _ _
        _ ≤ (ρ - δ) + δ := by
            gcongr
            rw [dist_comm]
            exact hdist.le
        _ = ρ := by ring
    exact le_trans (hyB (ρ - δ) (by linarith) (by linarith)).1 (measure_mono hsub)
  · -- enlarge the radius slightly and let the enlargement tend to `0`
    have hbase : ContinuousAt (fun δ : ℝ ↦ ρ + δ) 0 := by fun_prop
    have hrpow : ContinuousAt (fun x : ℝ ↦ x ^ s) (ρ + 0) := by
      simpa using Real.continuousAt_rpow_const ρ s (Or.inl hρ.ne')
    have h1 : ContinuousAt (fun δ : ℝ ↦ q * (ρ + δ) ^ s) 0 :=
      continuousAt_const.mul (hrpow.comp hbase)
    have htend : Tendsto (fun δ : ℝ ↦ ENNReal.ofReal (q * (ρ + δ) ^ s)) (𝓝[>] (0 : ℝ))
        (𝓝 (ENNReal.ofReal (q * ρ ^ s))) := by
      have h2 := (ENNReal.continuous_ofReal.continuousAt.comp h1).tendsto
      simp only [Function.comp_def, add_zero] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds (show (0 : ℝ) < 1 / (m + 1) - ρ by linarith))]
      with δ hδ hδρ
    have hδ0 : 0 < δ := Set.mem_Ioi.mp hδ
    obtain ⟨y, hyB, hdist⟩ := Metric.mem_closure_iff.mp hz δ hδ0
    have hsub : closedBall z ρ ⊆ closedBall y (ρ + δ) := by
      intro w hw
      rw [mem_closedBall] at hw ⊢
      calc dist w y ≤ dist w z + dist z y := dist_triangle _ _ _
        _ ≤ ρ + δ := by gcongr
    exact le_trans (measure_mono hsub) (hyB (ρ + δ) (by linarith) (by linarith)).2
/-- Every point of `A` at which the density ratio exceeds `θ` lies in one of the sets
`goodSet s p q m μ` with `θ q ≤ p`. -/
lemma exists_goodSet_mem {s : ℝ} {μ : OuterMeasure (EuclideanSpace ℝ (Fin n))}
    {a : EuclideanSpace ℝ (Fin n)} (ha : a ∈ positiveFiniteDensitySet s μ)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ : ENNReal.ofReal θ < sDensityRatio s μ a) :
    ∃ (p q : ℚ) (m : ℕ), 0 < (p : ℝ) ∧ 0 < (q : ℝ) ∧ θ * (q : ℝ) ≤ (p : ℝ) ∧
      upperSDensity s μ a * ENNReal.ofReal ((2 : ℝ) ^ s) < ENNReal.ofReal (q : ℝ) ∧
      a ∈ goodSet s (p : ℝ) (q : ℝ) m μ := by
  obtain ⟨hl, hlu, hu⟩ := ha
  simp only [sDensityRatio] at hθ
  set l := lowerSDensity s μ a with hldef
  set u := upperSDensity s μ a with hudef
  have hupos : 0 < u := lt_of_lt_of_le hl hlu
  have hltop : l ≠ ∞ := ne_top_of_le_ne_top hu.ne hlu
  set L := l.toReal with hLdef
  set U := u.toReal with hUdef
  have hLpos : 0 < L := ENNReal.toReal_pos hl.ne' hltop
  have hUpos : 0 < U := ENNReal.toReal_pos hupos.ne' hu.ne
  have hLl : ENNReal.ofReal L = l := ENNReal.ofReal_toReal hltop
  have hUu : ENNReal.ofReal U = u := ENNReal.ofReal_toReal hu.ne
  -- the density hypothesis, in real form
  have hθLU : θ * U < L := by
    have h1 : ENNReal.ofReal θ < ENNReal.ofReal (L / U) := by
      rw [ENNReal.ofReal_div_of_pos hUpos, hLl, hUu]
      exact hθ
    have h2 : θ < L / U := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp h1
    rwa [lt_div_iff₀ hUpos] at h2
  -- a small margin `η`
  set D := L - θ * U with hD
  have hDpos : 0 < D := by simp only [hD]; linarith
  set η := min (L / 2) (D / (2 * (1 + θ))) with hη
  have hηpos : 0 < η := lt_min (by positivity) (by positivity)
  have hηL : η ≤ L / 2 := min_le_left _ _
  have hηD : η ≤ D / (2 * (1 + θ)) := min_le_right _ _
  have hLη : 0 < L - η := by linarith
  have hη2 : η * (2 * (1 + θ)) ≤ D := (le_div_iff₀ (by positivity)).mp hηD
  have hkey : θ * (U + η) < L - η := by
    have h3 : η * (1 + θ) < D := by nlinarith
    simp only [hD] at h3
    nlinarith
  -- the resulting constants
  set c2 : ℝ := (2 : ℝ) ^ s with hc2
  have hc2pos : 0 < c2 := Real.rpow_pos_of_pos (by norm_num) s
  set p₀ := c2 * (L - η) with hp₀def
  set q₀ := c2 * (U + η) with hq₀def
  have hp₀ : 0 < p₀ := mul_pos hc2pos hLη
  have hq₀ : 0 < q₀ := mul_pos hc2pos (by linarith)
  have hθq : θ * q₀ < p₀ := by
    simp only [hp₀def, hq₀def]
    nlinarith
  -- the two-sided ball bound at small scales
  have hev1 : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (L - η) < μ (closedBall a r) / ENNReal.ofReal ((2 * r) ^ s) := by
    refine eventually_lt_of_lt_liminf ?_
    have h' : ENNReal.ofReal (L - η) < l := by
      rw [← hLl]
      exact (ENNReal.ofReal_lt_ofReal_iff hLpos).mpr (by linarith)
    rwa [hldef, lowerSDensity] at h'
  have hev2 : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      μ (closedBall a r) / ENNReal.ofReal ((2 * r) ^ s) < ENNReal.ofReal (U + η) := by
    refine eventually_lt_of_limsup_lt ?_
    have h' : u < ENNReal.ofReal (U + η) := by
      rw [← hUu]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
    rwa [hudef, upperSDensity] at h'
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (p₀ * r ^ s) ≤ μ (closedBall a r) ∧
        μ (closedBall a r) ≤ ENNReal.ofReal (q₀ * r ^ s) := by
    filter_upwards [hev1, hev2, self_mem_nhdsWithin] with r h1 h2 hr0
    have hr : 0 < r := Set.mem_Ioi.mp hr0
    have hrs : (0 : ℝ) < (2 * r) ^ s := Real.rpow_pos_of_pos (by linarith) s
    have hden_ne : ENNReal.ofReal ((2 * r) ^ s) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact hrs
    have hprod : ∀ v : ℝ, 0 ≤ v →
        ENNReal.ofReal v * ENNReal.ofReal ((2 * r) ^ s)
          = ENNReal.ofReal (c2 * v * r ^ s) := by
      intro v hv
      rw [← ENNReal.ofReal_mul hv, Real.mul_rpow (by norm_num) hr.le]
      congr 1
      simp only [hc2]
      ring
    constructor
    · have hmul := (ENNReal.lt_div_iff_mul_lt (Or.inl hden_ne)
        (Or.inl ENNReal.ofReal_ne_top)).mp h1
      refine le_of_lt (lt_of_le_of_lt (le_of_eq ?_) hmul)
      rw [hprod (L - η) hLη.le, hp₀def]
    · have hmul := (ENNReal.div_lt_iff (Or.inl hden_ne)
        (Or.inl ENNReal.ofReal_ne_top)).mp h2
      refine le_of_lt (lt_of_lt_of_le hmul (le_of_eq ?_))
      rw [hprod (U + η) (by linarith), hq₀def]
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hh⟩ := hev
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  have hmem : a ∈ goodSet s p₀ q₀ m μ := by
    intro ρ hρ hρm
    refine hh (show dist ρ 0 < ε from ?_) (Set.mem_Ioi.mpr hρ)
    rw [Real.dist_eq, sub_zero, abs_of_pos hρ]
    exact lt_trans hρm hm
  -- finally, rational constants
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show (θ * q₀ + p₀) / 2 < p₀ by linarith)
  have hppos : 0 < (p : ℝ) := by nlinarith
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
    (show q₀ < (p : ℝ) / θ by rw [lt_div_iff₀ hθ0]; nlinarith)
  have hqpos : 0 < (q : ℝ) := lt_trans hq₀ hq1
  have hθqp : θ * (q : ℝ) ≤ (p : ℝ) := by
    have h := (lt_div_iff₀ hθ0).mp hq2
    nlinarith
  have hqsup : upperSDensity s μ a * ENNReal.ofReal ((2 : ℝ) ^ s) < ENNReal.ofReal (q : ℝ) := by
    rw [← hudef, ← hUu, ← ENNReal.ofReal_mul hUpos.le]
    refine (ENNReal.ofReal_lt_ofReal_iff hqpos).mpr ?_
    have : q₀ < (q : ℝ) := hq1
    simp only [hq₀def, hc2] at this
    nlinarith
  exact ⟨p, q, m, hppos, hqpos, hθqp, hqsup, goodSet_subset hp2.le hq1.le hmem⟩
/-! ## Points all of whose small balls are controlled -/
/-- `goodBallSet s q m μ` is the set of points `z` such that **every** closed ball of radius
`0 < w < 1 / (m + 1)` containing `z` has measure at most `q w ^ s`. -/
def goodBallSet (s q : ℝ) (m : ℕ) (μ : OuterMeasure (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {z | ∀ (y : EuclideanSpace ℝ (Fin n)) (w : ℝ), 0 < w → w < 1 / (m + 1) →
    z ∈ closedBall y w → μ (closedBall y w) ≤ ENNReal.ofReal (q * w ^ s)}
lemma goodBallSet_subset {s q q' : ℝ} {m : ℕ}
    {μ : OuterMeasure (EuclideanSpace ℝ (Fin n))} (hq : q ≤ q') :
    goodBallSet s q m μ ⊆ goodBallSet s q' m μ := by
  intro z hz y w hw hwm hmem
  refine le_trans (hz y w hw hwm hmem) (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hw.le s)
lemma goodBallSet_mono_nat {s q : ℝ} {m m' : ℕ}
    {μ : OuterMeasure (EuclideanSpace ℝ (Fin n))} (hm : m ≤ m') :
    goodBallSet s q m μ ⊆ goodBallSet s q m' μ := by
  intro z hz y w hw hwm hmem
  refine hz y w hw (lt_of_lt_of_le hwm ?_) hmem
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast Nat.add_le_add_right hm 1
lemma isClosed_goodBallSet (s q : ℝ) (m : ℕ)
    (μ : OuterMeasure (EuclideanSpace ℝ (Fin n))) : IsClosed (goodBallSet s q m μ) := by
  refine isClosed_of_closure_subset fun z hz y w hw hwm hmem ↦ ?_
  have hbase : ContinuousAt (fun δ : ℝ ↦ w + δ) 0 := by fun_prop
  have hrpow : ContinuousAt (fun v : ℝ ↦ v ^ s) (w + 0) := by
    simpa using Real.continuousAt_rpow_const w s (Or.inl hw.ne')
  have h1 : ContinuousAt (fun δ : ℝ ↦ q * (w + δ) ^ s) 0 :=
    continuousAt_const.mul (hrpow.comp hbase)
  have htend : Tendsto (fun δ : ℝ ↦ ENNReal.ofReal (q * (w + δ) ^ s)) (𝓝[>] (0 : ℝ))
      (𝓝 (ENNReal.ofReal (q * w ^ s))) := by
    have h2 := (ENNReal.continuous_ofReal.continuousAt.comp h1).tendsto
    simp only [Function.comp_def, add_zero] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (gt_mem_nhds (show (0 : ℝ) < 1 / (m + 1) - w by linarith))]
    with δ hδ hδw
  have hδ0 : 0 < δ := Set.mem_Ioi.mp hδ
  obtain ⟨z', hz'B, hdist⟩ := Metric.mem_closure_iff.mp hz δ hδ0
  have hz'mem : z' ∈ closedBall y (w + δ) := by
    rw [mem_closedBall] at hmem ⊢
    calc dist z' y ≤ dist z' z + dist z y := dist_triangle _ _ _
      _ ≤ δ + w := by
          gcongr
          rw [dist_comm]
          exact hdist.le
      _ = w + δ := by ring
  have hsub : closedBall y w ⊆ closedBall y (w + δ) :=
    closedBall_subset_closedBall (by linarith)
  exact le_trans (measure_mono hsub) (hz'B y (w + δ) (by linarith) (by linarith) hz'mem)
/-- Under the ball-density hypothesis of Lemma 14.7 (2), a point whose upper density is small
compared with `q` lies in one of the sets `goodBallSet s q m μ`. -/
lemma exists_goodBallSet_mem {s q : ℝ} {μ : OuterMeasure (EuclideanSpace ℝ (Fin n))}
    {a : EuclideanSpace ℝ (Fin n)} (hq : 0 < q)
    (hball : upperBallSDensity s μ a ≤ upperSDensity s μ a)
    (hqsup : upperSDensity s μ a * ENNReal.ofReal ((2 : ℝ) ^ s) < ENNReal.ofReal q) :
    ∃ m : ℕ, a ∈ goodBallSet s q m μ := by
  set c2 : ℝ := (2 : ℝ) ^ s with hc2
  have hc2pos : 0 < c2 := Real.rpow_pos_of_pos (by norm_num) s
  have hc2ne : ENNReal.ofReal c2 ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hc2pos
  set Q : ℝ≥0∞ := ENNReal.ofReal q / ENNReal.ofReal c2 with hQ
  have hlt : upperSDensity s μ a < Q := by
    rw [hQ, ENNReal.lt_div_iff_mul_lt (Or.inl hc2ne) (Or.inl ENNReal.ofReal_ne_top)]
    exact hqsup
  have hlimsup : upperBallSDensity s μ a < Q := lt_of_le_of_lt hball hlt
  rw [upperBallSDensity] at hlimsup
  have hev := eventually_lt_of_limsup_lt hlimsup
  obtain ⟨δ, hδQ, hδpos⟩ := (hev.and self_mem_nhdsWithin).exists
  have hδ : 0 < δ := Set.mem_Ioi.mp hδpos
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show (0 : ℝ) < δ / 2 by positivity)
  refine ⟨m, fun y w hw hwm hmem ↦ ?_⟩
  have h2w : 2 * w < δ := by
    have : w < δ / 2 := lt_trans hwm hm
    linarith
  have hratio : μ (closedBall y w) / ENNReal.ofReal ((2 * w) ^ s) < Q := by
    refine lt_of_le_of_lt ?_ hδQ
    exact le_iSup_of_le y (le_iSup_of_le w (le_iSup_of_le hw
      (le_iSup_of_le h2w (le_iSup_of_le hmem le_rfl))))
  have hden_ne : ENNReal.ofReal ((2 * w) ^ s) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.rpow_pos_of_pos (by linarith) s
  have hmul := (ENNReal.div_lt_iff (Or.inl hden_ne) (Or.inl ENNReal.ofReal_ne_top)).mp hratio
  refine le_of_lt (lt_of_lt_of_le hmul (le_of_eq ?_))
  have hsplit : ENNReal.ofReal ((2 * w) ^ s)
      = ENNReal.ofReal c2 * ENNReal.ofReal (w ^ s) := by
    rw [← ENNReal.ofReal_mul hc2pos.le, Real.mul_rpow (by norm_num) hw.le]
  rw [hsplit, hQ, ← mul_assoc, ENNReal.div_mul_cancel hc2ne ENNReal.ofReal_ne_top,
    ← ENNReal.ofReal_mul hq.le]
/-! ## The density theorem in the form required by the reduction step -/
/-- **Besicovitch density theorem** for a Radon outer measure, in the form used in Mattila's
proof of Lemma 14.7 (1): outside a `μ`-null set, every point of a Borel set `B` is a density
point of `B`, in the sense that the portion of a small ball around it which misses `B` is an
arbitrarily small fraction of the ball. -/
lemma exists_null_of_not_density_point (μ : OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : RadonOuterMeasure μ) {B : Set (EuclideanSpace ℝ (Fin n))} (hB : MeasurableSet B) :
    ∃ N : Set (EuclideanSpace ℝ (Fin n)), μ N = 0 ∧
      ∀ a ∈ B \ N, ∀ γ : ℝ≥0∞, 0 < γ →
        ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μ (closedBall a ρ \ B) ≤ γ * μ (closedBall a ρ) := by
  set μm := μ.toMeasure hμ.measurable_le_caratheodory with hμm
  letI : μm.Regular := hμ.regular_toMeasure
  set P : EuclideanSpace ℝ (Fin n) → Prop := fun x ↦
    Tendsto (fun r ↦ μm (B ∩ closedBall x r) / μm (closedBall x r)) (𝓝[>] (0 : ℝ)) (𝓝 1)
    with hP
  have hae : ∀ᵐ x ∂μm.restrict B, P x := Besicovitch.ae_tendsto_measure_inter_div μm B
  have hbad : μm ({x | ¬ P x} ∩ B) = 0 :=
    le_antisymm ((Measure.le_restrict_apply _ _).trans (ae_iff.mp hae).le) (zero_le _)
  obtain ⟨G, hGsub, hGmeas, hG0⟩ := exists_measurable_superset_of_null hbad
  refine ⟨G, ?_, ?_⟩
  · rw [show μ G = μm G from (toMeasure_apply μ hμ.measurable_le_caratheodory hGmeas).symm]
    exact hG0
  rintro a ⟨haB, haG⟩ γ hγ
  have hPa : P a := by
    by_contra hcon
    exact haG (hGsub ⟨hcon, haB⟩)
  set γ' : ℝ≥0∞ := min γ 1 with hγ'
  have hγ'pos : 0 < γ' := lt_min hγ one_pos
  have hγ'le : γ' ≤ 1 := min_le_right _ _
  have hlt : (1 : ℝ≥0∞) - γ' < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hγ'pos.ne'
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      (1 : ℝ≥0∞) - γ' < μm (B ∩ closedBall a ρ) / μm (closedBall a ρ) :=
    (tendsto_order.1 hPa).1 _ hlt
  filter_upwards [hev] with ρ hρ
  have hmeasdiff : MeasurableSet (closedBall a ρ \ B) :=
    (measurableSet_closedBall).diff hB
  have hdiff : μ (closedBall a ρ \ B) = μm (closedBall a ρ \ B) :=
    (toMeasure_apply μ hμ.measurable_le_caratheodory hmeasdiff).symm
  have hball : μ (closedBall a ρ) = μm (closedBall a ρ) :=
    (toMeasure_apply μ hμ.measurable_le_caratheodory measurableSet_closedBall).symm
  rw [hdiff, hball]
  set A := μm (closedBall a ρ) with hA
  set Ai := μm (B ∩ closedBall a ρ) with hAi
  set Ac := μm (closedBall a ρ \ B) with hAc
  have hAtop : A ≠ ∞ := (isCompact_closedBall a ρ).measure_lt_top.ne
  have hsum : Ai + Ac = A := by
    rw [hAi, hAc, hA, Set.inter_comm]
    exact measure_inter_add_diff _ hB
  rcases eq_or_ne A 0 with hA0 | hA0
  · have : Ac ≤ A := by rw [← hsum]; exact le_add_self
    rw [hA0] at this ⊢
    simpa using this
  have hkey : ((1 : ℝ≥0∞) - γ') * A < Ai :=
    (ENNReal.lt_div_iff_mul_lt (Or.inl hA0) (Or.inl hAtop)).mp hρ
  have hmulle : γ' * A ≤ A := by
    calc γ' * A ≤ 1 * A := by gcongr
      _ = A := one_mul A
  have hsub' : A - γ' * A ≤ Ai := by
    refine le_of_lt (lt_of_le_of_lt (le_of_eq ?_) hkey)
    rw [ENNReal.sub_mul (fun _ _ ↦ hAtop), one_mul]
  have hstep : (A - γ' * A) + Ac ≤ A := by
    calc (A - γ' * A) + Ac ≤ Ai + Ac := by gcongr
      _ = A := hsum
  have hfinal : Ac ≤ γ' * A := by
    have h := ENNReal.le_sub_of_add_le_left (ne_top_of_le_ne_top hAtop tsub_le_self) hstep
    rwa [ENNReal.sub_sub_cancel hAtop hmulle] at h
  exact hfinal.trans (by gcongr; exact min_le_left _ _)
/-! ## Passing to the limit in the constants -/
/-- If the two-sided ball estimate holds with constants `θ k` tending to `t`, then it holds
with the constant `t` itself. -/
lemma exists_uniform_constant_of_tendsto {s θ₀ : ℝ} {t : ℝ≥0∞} {θ : ℕ → ℝ}
    {ν : OuterMeasure (EuclideanSpace ℝ (Fin n))} (hν : RadonOuterMeasure ν) (hν0 : ν ≠ 0)
    (hθ₀ : 0 < θ₀) (hθlb : ∀ k, θ₀ ≤ θ k)
    (hθ : Tendsto (fun k ↦ ENNReal.ofReal (θ k)) atTop (𝓝 t))
    (h : ∀ k, ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
      ∀ x ∈ SupportOuterMeasure ν, ∀ ρ : ℝ, 0 < ρ →
        ENNReal.ofReal (θ k) * c * ENNReal.ofReal (ρ ^ s) ≤ ν (closedBall x ρ) ∧
          ν (closedBall x ρ) ≤ c * ENNReal.ofReal (ρ ^ s)) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
      ∀ x ∈ SupportOuterMeasure ν, ∀ ρ : ℝ, 0 < ρ →
        t * c * ENNReal.ofReal (ρ ^ s) ≤ ν (closedBall x ρ) ∧
          ν (closedBall x ρ) ≤ c * ENNReal.ofReal (ρ ^ s) := by
  choose c hcpos hctop hc using h
  obtain ⟨R, -, hRpos⟩ := exists_ball_pos_of_ne_zero hν0
  obtain ⟨x₀, -, hx₀⟩ := exists_mem_support_of_measure_pos hRpos
  set V := ν (closedBall x₀ 1) with hV
  have hVpos : 0 < V :=
    lt_of_lt_of_le (measure_ball_pos hx₀ one_pos) (measure_mono ball_subset_closedBall)
  have hVtop : V ≠ ∞ := (measure_closedBall_lt_top hν x₀ 1).ne
  have hθ₀ne : ENNReal.ofReal θ₀ ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hθ₀
  have hVle : ∀ k, V ≤ c k := by
    intro k
    simpa using (hc k x₀ hx₀ 1 one_pos).2
  have hcub : ∀ k, ENNReal.ofReal θ₀ * c k ≤ V := by
    intro k
    have hk := (hc k x₀ hx₀ 1 one_pos).1
    simp only [Real.one_rpow, ENNReal.ofReal_one, mul_one] at hk
    exact le_trans (by gcongr; exact hθlb k) hk
  obtain ⟨cl, -, φ, hφ, hcl⟩ :=
    (isCompact_univ (X := ℝ≥0∞)).tendsto_subseq (x := c) (fun k ↦ mem_univ _)
  have hclpos : 0 < cl := lt_of_lt_of_le hVpos (ge_of_tendsto' hcl fun j ↦ hVle (φ j))
  have hcltop : cl ≠ ∞ := by
    have hlim : ENNReal.ofReal θ₀ * cl ≤ V :=
      le_of_tendsto' (ENNReal.Tendsto.const_mul hcl (Or.inr ENNReal.ofReal_ne_top)) fun j ↦ hcub (φ j)
    intro htop
    rw [htop, ENNReal.mul_top hθ₀ne] at hlim
    exact hVtop (top_le_iff.mp hlim)
  refine ⟨cl, hclpos, hcltop, fun x hx ρ hρ ↦ ⟨?_, ?_⟩⟩
  · have hmul : Tendsto (fun j ↦ ENNReal.ofReal (θ (φ j)) * c (φ j) * ENNReal.ofReal (ρ ^ s))
        atTop (𝓝 (t * cl * ENNReal.ofReal (ρ ^ s))) := by
      refine ENNReal.Tendsto.mul_const ?_ (Or.inr ENNReal.ofReal_ne_top)
      exact ENNReal.Tendsto.mul (hθ.comp hφ.tendsto_atTop) (Or.inr hcltop) hcl
        (Or.inl hclpos.ne')
    exact le_of_tendsto' hmul fun j ↦ (hc (φ j) x hx ρ hρ).1
  · have hmul : Tendsto (fun j ↦ c (φ j) * ENNReal.ofReal (ρ ^ s)) atTop
        (𝓝 (cl * ENNReal.ofReal (ρ ^ s))) :=
      ENNReal.Tendsto.mul_const hcl (Or.inr ENNReal.ofReal_ne_top)
    exact ge_of_tendsto' hmul fun j ↦ (hc (φ j) x hx ρ hρ).2
/-- The analogue of `exists_uniform_constant_of_tendsto` for the situation of Lemma 14.7 (2),
where the upper bound holds for balls with arbitrary centres. -/
lemma exists_uniform_constant_of_tendsto_ball {s θ₀ : ℝ} {t : ℝ≥0∞} {θ : ℕ → ℝ}
    {ν : OuterMeasure (EuclideanSpace ℝ (Fin n))} (hν : RadonOuterMeasure ν) (hν0 : ν ≠ 0)
    (hθ₀ : 0 < θ₀) (hθlb : ∀ k, θ₀ ≤ θ k)
    (hθ : Tendsto (fun k ↦ ENNReal.ofReal (θ k)) atTop (𝓝 t))
    (h : ∀ k, ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
      (∀ x ∈ SupportOuterMeasure ν, ∀ ρ : ℝ, 0 < ρ →
        ENNReal.ofReal (θ k) * c * ENNReal.ofReal (ρ ^ s) ≤ ν (closedBall x ρ)) ∧
      ∀ (x : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 < ρ →
        ν (closedBall x ρ) ≤ c * ENNReal.ofReal (ρ ^ s)) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
      (∀ x ∈ SupportOuterMeasure ν, ∀ ρ : ℝ, 0 < ρ →
        t * c * ENNReal.ofReal (ρ ^ s) ≤ ν (closedBall x ρ)) ∧
      ∀ (x : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 < ρ →
        ν (closedBall x ρ) ≤ c * ENNReal.ofReal (ρ ^ s) := by
  choose c hcpos hctop hclo hcup using h
  obtain ⟨R, -, hRpos⟩ := exists_ball_pos_of_ne_zero hν0
  obtain ⟨x₀, -, hx₀⟩ := exists_mem_support_of_measure_pos hRpos
  set V := ν (closedBall x₀ 1) with hV
  have hVpos : 0 < V :=
    lt_of_lt_of_le (measure_ball_pos hx₀ one_pos) (measure_mono ball_subset_closedBall)
  have hVtop : V ≠ ∞ := (measure_closedBall_lt_top hν x₀ 1).ne
  have hθ₀ne : ENNReal.ofReal θ₀ ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hθ₀
  have hVle : ∀ k, V ≤ c k := by
    intro k
    simpa using hcup k x₀ 1 one_pos
  have hcub : ∀ k, ENNReal.ofReal θ₀ * c k ≤ V := by
    intro k
    have hk := hclo k x₀ hx₀ 1 one_pos
    simp only [Real.one_rpow, ENNReal.ofReal_one, mul_one] at hk
    exact le_trans (by gcongr; exact hθlb k) hk
  obtain ⟨cl, -, φ, hφ, hcl⟩ :=
    (isCompact_univ (X := ℝ≥0∞)).tendsto_subseq (x := c) (fun k ↦ mem_univ _)
  have hclpos : 0 < cl := lt_of_lt_of_le hVpos (ge_of_tendsto' hcl fun j ↦ hVle (φ j))
  have hcltop : cl ≠ ∞ := by
    have hlim : ENNReal.ofReal θ₀ * cl ≤ V :=
      le_of_tendsto' (ENNReal.Tendsto.const_mul hcl (Or.inr ENNReal.ofReal_ne_top))
        fun j ↦ hcub (φ j)
    intro htop
    rw [htop, ENNReal.mul_top hθ₀ne] at hlim
    exact hVtop (top_le_iff.mp hlim)
  refine ⟨cl, hclpos, hcltop, fun x hx ρ hρ ↦ ?_, fun x ρ hρ ↦ ?_⟩
  · have hmul : Tendsto (fun j ↦ ENNReal.ofReal (θ (φ j)) * c (φ j) * ENNReal.ofReal (ρ ^ s))
        atTop (𝓝 (t * cl * ENNReal.ofReal (ρ ^ s))) := by
      refine ENNReal.Tendsto.mul_const ?_ (Or.inr ENNReal.ofReal_ne_top)
      exact ENNReal.Tendsto.mul (hθ.comp hφ.tendsto_atTop) (Or.inr hcltop) hcl
        (Or.inl hclpos.ne')
    exact le_of_tendsto' hmul fun j ↦ hclo (φ j) x hx ρ hρ
  · have hmul : Tendsto (fun j ↦ c (φ j) * ENNReal.ofReal (ρ ^ s)) atTop
        (𝓝 (cl * ENNReal.ofReal (ρ ^ s))) :=
      ENNReal.Tendsto.mul_const hcl (Or.inr ENNReal.ofReal_ne_top)
    exact ge_of_tendsto' hmul fun j ↦ hcup (φ j) x ρ hρ



/-- The set of points `a ∈ F` which stay at distance at least `ε d` from every touching point
of a hole of `F` of size `d ≤ d₀`. -/
def farFromTouching (F : Set (EuclideanSpace ℝ (Fin n))) (ε d₀ : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {a | a ∈ F ∧ ∀ y ∈ F, ∀ z : EuclideanSpace ℝ (Fin n), dist z y = infDist z F →
    0 < infDist z F → infDist z F ≤ d₀ → ε * infDist z F ≤ dist y a}
lemma isClosed_farFromTouching {F : Set (EuclideanSpace ℝ (Fin n))} (hF : IsClosed F)
    (ε d₀ : ℝ) : IsClosed (farFromTouching F ε d₀) := by
  have hrw : farFromTouching F ε d₀ = F ∩ ⋂ (y : EuclideanSpace ℝ (Fin n)) (_ : y ∈ F)
      (z : EuclideanSpace ℝ (Fin n)) (_ : dist z y = infDist z F) (_ : 0 < infDist z F)
      (_ : infDist z F ≤ d₀), {a | ε * infDist z F ≤ dist y a} := by
    ext a
    simp only [farFromTouching, mem_setOf_eq, mem_inter_iff, mem_iInter]
  rw [hrw]
  refine hF.inter (isClosed_iInter fun y ↦ isClosed_iInter fun _ ↦ isClosed_iInter fun z ↦
    isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦ ?_)
  exact isClosed_le continuous_const (continuous_const.dist continuous_id)
/-- **Almost no point of `F` is uniformly far from all touching points.** -/
theorem measure_farFromTouching_eq_zero {s p q r₀ ε d₀ : ℝ} (hsn : s < n)
    (hp : 0 < p) (hq : 0 < q) (hr₀ : 0 < r₀) (hε : 0 < ε) (hε1 : ε ≤ 1) (hd₀ : 0 < d₀)
    (μ : OuterMeasure (EuclideanSpace ℝ (Fin n))) (hμ : RadonOuterMeasure μ)
    {F : Set (EuclideanSpace ℝ (Fin n))} (hFclosed : IsClosed F)
    (hupper : ∀ y ∈ F, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (q * ρ ^ s))
    (hlower : ∀ y ∈ F, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (p * ρ ^ s) ≤ μ (closedBall y ρ)) :
    μ (farFromTouching F ε d₀) = 0 := by
  obtain ⟨κ, hκ0, hκ1, hhole⟩ := exists_hole_of_ball_bounds hsn hp hq μ hμ hupper hlower
  set B := farFromTouching F ε d₀ with hBdef
  obtain ⟨N, hN0, hN⟩ :=
    exists_null_of_not_density_point μ hμ (isClosed_farFromTouching hFclosed ε d₀).measurableSet
  have hsub : B ⊆ N := by
    intro a haB
    by_contra haN
    obtain ⟨haF, haprop⟩ := haB
    -- the proportion of the measure of a small ball which is guaranteed to miss `B`
    set γ : ℝ≥0∞ := ENNReal.ofReal (p * (ε * κ / 2) ^ s / (q * 3 ^ s)) with hγdef
    have hγpos : 0 < γ := by
      rw [hγdef, ENNReal.ofReal_pos]
      have h1 : (0 : ℝ) < (ε * κ / 2) ^ s := Real.rpow_pos_of_pos (by positivity) s
      have h2 : (0 : ℝ) < (3 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
      positivity
    have hγtop : γ ≠ ∞ := ENNReal.ofReal_ne_top
    -- the density property of `a`
    have hev := hN a ⟨⟨haF, haprop⟩, haN⟩ (γ / 2) (ENNReal.half_pos hγpos.ne')
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨η, hη, hh⟩ := hev
    -- a scale which is small enough for all the constraints
    set δ : ℝ := min (η / 4) (min (r₀ / 4) d₀) with hδdef
    have hδ : 0 < δ := lt_min (by positivity) (lt_min (by positivity) hd₀)
    have hδη : 3 * δ < η := by
      have : δ ≤ η / 4 := min_le_left _ _
      linarith
    have hδr₀ : 3 * δ < r₀ := by
      have : δ ≤ r₀ / 4 := le_trans (min_le_right _ _) (min_le_left _ _)
      linarith
    have hδd₀ : δ ≤ d₀ := le_trans (min_le_right _ _) (min_le_right _ _)
    have hδhalf : δ < r₀ / 2 := by linarith
    -- the hole and its touching point
    obtain ⟨z, hzdist, hzfar⟩ := hhole a haF δ hδ hδhalf
    set d : ℝ := infDist z F with hddef
    have hdpos : 0 < d := lt_trans (by positivity) hzfar
    have hdle : d ≤ δ := le_trans (infDist_le_dist_of_mem haF) hzdist
    obtain ⟨y, hyF, hyd⟩ := hFclosed.exists_infDist_eq_dist ⟨a, haF⟩ z
    have hya : dist y a ≤ 2 * δ := by
      have h1 : dist y z = d := by rw [dist_comm, ← hyd]
      have h2 : dist y a ≤ dist y z + dist z a := dist_triangle _ _ _
      rw [h1] at h2
      linarith
    -- a ball around the touching point which misses `B`
    set w : ℝ := ε * κ * δ / 2 with hwdef
    have hwpos : 0 < w := by positivity
    have hwδ : w ≤ δ := by
      have h1 : ε * κ ≤ 1 := by nlinarith
      rw [hwdef]
      nlinarith
    have hwd : w < ε * d := by
      have h1 : ε * (κ * δ) < ε * d := by
        exact mul_lt_mul_of_pos_left hzfar hε
      rw [hwdef]
      nlinarith
    have hball : closedBall y w ⊆ closedBall a (3 * δ) \ B := by
      intro b hb
      have hby : dist b y ≤ w := mem_closedBall.mp hb
      refine ⟨?_, ?_⟩
      · rw [mem_closedBall]
        have : dist b a ≤ dist b y + dist y a := dist_triangle _ _ _
        linarith
      · intro hbB
        have := hbB.2 y hyF z hyd.symm hdpos (le_trans hdle hδd₀)
        rw [dist_comm y b] at this
        linarith
    -- the two sides of the density inequality
    have hlow2 : ENNReal.ofReal (p * w ^ s) ≤ μ (closedBall y w) :=
      hlower y hyF w hwpos (by linarith)
    have hMup : μ (closedBall a (3 * δ)) ≤ ENNReal.ofReal (q * (3 * δ) ^ s) :=
      hupper a haF _ (by linarith) hδr₀
    have hMlow : ENNReal.ofReal (p * (3 * δ) ^ s) ≤ μ (closedBall a (3 * δ)) :=
      hlower a haF _ (by linarith) hδr₀
    have hdiff : ENNReal.ofReal (p * w ^ s) ≤ μ (closedBall a (3 * δ) \ B) :=
      le_trans hlow2 (measure_mono hball)
    have hdens : μ (closedBall a (3 * δ) \ B) ≤ γ / 2 * μ (closedBall a (3 * δ)) := by
      have hd1 : dist (3 * δ) (0 : ℝ) < η := by
        rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 3 * δ)]
        exact hδη
      have hd2 : (0 : ℝ) < 3 * δ := by positivity
      exact hh hd1 hd2
    -- the identity relating `γ` to the two bounds
    have hident : γ * ENNReal.ofReal (q * (3 * δ) ^ s) = ENNReal.ofReal (p * w ^ s) := by
      rw [hγdef, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have h3 : (3 * δ) ^ s = (3 : ℝ) ^ s * δ ^ s := Real.mul_rpow (by norm_num) hδ.le
      have hw : w ^ s = (ε * κ / 2) ^ s * δ ^ s := by
        rw [hwdef, show ε * κ * δ / 2 = (ε * κ / 2) * δ by ring]
        exact Real.mul_rpow (by positivity) hδ.le
      have h3pos : (0 : ℝ) < (3 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
      rw [h3, hw]
      field_simp
    -- and the contradiction
    set M : ℝ≥0∞ := μ (closedBall a (3 * δ)) with hM
    have hM0 : M ≠ 0 := by
      have : (0 : ℝ≥0∞) < ENNReal.ofReal (p * (3 * δ) ^ s) := by
        rw [ENNReal.ofReal_pos]
        have : (0 : ℝ) < (3 * δ) ^ s := Real.rpow_pos_of_pos (by linarith) s
        positivity
      exact (lt_of_lt_of_le this hMlow).ne'
    have hMtop : M ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hMup
    have hchain : γ * M ≤ γ / 2 * M := by
      calc γ * M ≤ γ * ENNReal.ofReal (q * (3 * δ) ^ s) := by gcongr
        _ = ENNReal.ofReal (p * w ^ s) := hident
        _ ≤ μ (closedBall a (3 * δ) \ B) := hdiff
        _ ≤ γ / 2 * M := hdens
    have hle : γ ≤ γ / 2 := (ENNReal.mul_le_mul_iff_left hM0 hMtop).mp hchain
    exact absurd hle (not_le.2 (ENNReal.half_lt_self hγpos.ne' hγtop))
  exact le_antisymm (le_trans (measure_mono hsub) hN0.le) (zero_le _)
/-- **At almost every point of `F` there are touching points of relatively large holes.**
If the balls centred on the closed set `F` have measure comparable to `ρ ^ s` with `s < n`, then
outside a `μ`-null set every `a ∈ F` has, for every `ε > 0` and every `d₀ > 0`, a touching point
`y ∈ F` of a hole `B (z, d)` with `0 < d ≤ d₀` and `dist y a < ε d`. -/
theorem exists_touching_points_ae {s p q r₀ : ℝ} (hsn : s < n)
    (hp : 0 < p) (hq : 0 < q) (hr₀ : 0 < r₀)
    (μ : OuterMeasure (EuclideanSpace ℝ (Fin n))) (hμ : RadonOuterMeasure μ)
    {F : Set (EuclideanSpace ℝ (Fin n))} (hFclosed : IsClosed F)
    (hupper : ∀ y ∈ F, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (q * ρ ^ s))
    (hlower : ∀ y ∈ F, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (p * ρ ^ s) ≤ μ (closedBall y ρ)) :
    ∃ N : Set (EuclideanSpace ℝ (Fin n)), μ N = 0 ∧
      ∀ a ∈ F \ N, ∀ ε d₀ : ℝ, 0 < ε → 0 < d₀ →
        ∃ y z : EuclideanSpace ℝ (Fin n), y ∈ F ∧ dist z y = infDist z F ∧
          0 < infDist z F ∧ infDist z F ≤ d₀ ∧ dist y a < ε * infDist z F := by
  classical
  refine ⟨⋃ ij : ℕ × ℕ, farFromTouching F (1 / (ij.1 + 1)) (1 / (ij.2 + 1)), ?_, ?_⟩
  · refine measure_iUnion_null fun ij ↦ ?_
    refine measure_farFromTouching_eq_zero hsn hp hq hr₀ (by positivity) ?_ (by positivity)
      μ hμ hFclosed hupper hlower
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (ij.1 : ℝ) := Nat.cast_nonneg _
    linarith
  · rintro a ⟨haF, haN⟩ ε d₀ hε hd₀
    obtain ⟨i, hi⟩ := exists_nat_one_div_lt hε
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hd₀
    have hnot : a ∉ farFromTouching F (1 / (i + 1)) (1 / (j + 1)) := fun h ↦
      haN (mem_iUnion.2 ⟨(i, j), h⟩)
    rw [farFromTouching, mem_setOf_eq, not_and_or] at hnot
    have hfail : ¬ ∀ y ∈ F, ∀ z : EuclideanSpace ℝ (Fin n), dist z y = infDist z F →
        0 < infDist z F → infDist z F ≤ 1 / (j + 1) →
        1 / ((i : ℝ) + 1) * infDist z F ≤ dist y a := by
      rcases hnot with h | h
      · exact absurd haF h
      · exact h
    push_neg at hfail
    obtain ⟨y, hyF, z, hz1, hz2, hz3, hz4⟩ := hfail
    refine ⟨y, z, hyF, hz1, hz2, le_trans hz3 hj.le, lt_of_lt_of_le hz4 ?_⟩
    exact mul_le_mul_of_nonneg_right hi.le hz2.le


/-- A point whose balls have positive measure lies in the support. -/
lemma mem_supportOuterMeasure_of_ball_lower_bound {s p r₀ : ℝ} (hp : 0 < p) (hr₀ : 0 < r₀)
    {μ : OuterMeasure (EuclideanSpace ℝ (Fin n))} {a : EuclideanSpace ℝ (Fin n)}
    (hlower : ∀ ρ : ℝ, 0 < ρ → ρ < r₀ → ENNReal.ofReal (p * ρ ^ s) ≤ μ (closedBall a ρ)) :
    a ∈ SupportOuterMeasure μ := by
  intro U hU
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hU
  set ρ' : ℝ := min (ρ / 2) (r₀ / 2) with hρ'def
  have hρ'pos : 0 < ρ' := lt_min (by positivity) (by positivity)
  have h1 : ρ' < r₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have h2 : closedBall a ρ' ⊆ U :=
    subset_trans (closedBall_subset_ball (lt_of_le_of_lt (min_le_left _ _) (by linarith))) hball
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (p * ρ' ^ s) := by
    rw [ENNReal.ofReal_pos]
    have : (0 : ℝ) < ρ' ^ s := Real.rpow_pos_of_pos hρ'pos s
    positivity
  exact lt_of_lt_of_le hpos (le_trans (hlower ρ' hρ'pos h1) (measure_mono h2))
/-- Two-sided ball bounds at a single point `a` already give Mattila's assumption 14.3 (1)
at `a`. -/
lemma limsup_ball_ratio_lt_top_of_ball_bounds_at {s p q r₀ : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hr₀ : 0 < r₀) {μ : OuterMeasure (EuclideanSpace ℝ (Fin n))}
    {a : EuclideanSpace ℝ (Fin n)}
    (hupper : ∀ ρ : ℝ, 0 < ρ → ρ < r₀ → μ (closedBall a ρ) ≤ ENNReal.ofReal (q * ρ ^ s))
    (hlower : ∀ ρ : ℝ, 0 < ρ → ρ < r₀ → ENNReal.ofReal (p * ρ ^ s) ≤ μ (closedBall a ρ)) :
    limsup (fun ρ : ℝ ↦ μ (ball a (2 * ρ)) / μ (ball a ρ)) (𝓝[>] (0 : ℝ)) < ∞ := by
  set K : ℝ := q * (4 : ℝ) ^ s / p with hK
  have h4 : (0 : ℝ) < (4 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) s
  have hKpos : 0 < K := by rw [hK]; positivity
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      μ (ball a (2 * ρ)) / μ (ball a ρ) ≤ ENNReal.ofReal K := by
    have h1 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), (0 : ℝ) < ρ := self_mem_nhdsWithin
    have h2 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ < r₀ / 2 :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (by positivity))
    filter_upwards [h1, h2] with ρ hρ hρ'
    have hρ2 : (0 : ℝ) < 2 * ρ := by linarith
    have hρhalf : (0 : ℝ) < ρ / 2 := by linarith
    have hkey : μ (ball a (2 * ρ)) ≤ ENNReal.ofReal K * μ (ball a ρ) := by
      have hup : μ (ball a (2 * ρ)) ≤ ENNReal.ofReal (q * (2 * ρ) ^ s) :=
        le_trans (measure_mono ball_subset_closedBall) (hupper _ hρ2 (by linarith))
      have hlo : ENNReal.ofReal (p * (ρ / 2) ^ s) ≤ μ (ball a ρ) :=
        le_trans (hlower _ hρhalf (by linarith))
          (measure_mono (closedBall_subset_ball (by linarith)))
      have hid : q * (2 * ρ) ^ s = K * (p * (ρ / 2) ^ s) := by
        have h2ρ : (2 : ℝ) * ρ = 4 * (ρ / 2) := by ring
        rw [h2ρ, Real.mul_rpow (by norm_num) hρhalf.le, hK]
        field_simp
      calc μ (ball a (2 * ρ)) ≤ ENNReal.ofReal (q * (2 * ρ) ^ s) := hup
        _ = ENNReal.ofReal K * ENNReal.ofReal (p * (ρ / 2) ^ s) := by
            rw [hid, ENNReal.ofReal_mul hKpos.le]
        _ ≤ ENNReal.ofReal K * μ (ball a ρ) := by gcongr
    exact ENNReal.div_le_of_le_mul hkey
  exact lt_of_le_of_lt (limsup_le_of_le (by isBoundedDefault) hev) ENNReal.ofReal_lt_top
/-- **Half-space tangent measures at asymptotic touching points.**
If `a ∈ F` is a density point of `F`, the balls centred on `F` carry measure comparable to
`ρ ^ s`, and `a` is an asymptotic touching point of holes of `F`, then `μ` has a tangent measure
at `a` whose support lies in a closed half-space. -/
theorem exists_halfSpace_tangentMeasure_of_touching {s p q r₀ : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr₀ : 0 < r₀)
    (μ : OuterMeasure (EuclideanSpace ℝ (Fin n))) (hμ : RadonOuterMeasure μ)
    {F : Set (EuclideanSpace ℝ (Fin n))} {a : EuclideanSpace ℝ (Fin n)} (haF : a ∈ F)
    (hupper : ∀ y ∈ F, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (q * ρ ^ s))
    (hlower : ∀ y ∈ F, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (p * ρ ^ s) ≤ μ (closedBall y ρ))
    (hdens : ∀ γ : ℝ≥0∞, 0 < γ →
      ∀ᶠ ρ in 𝓝[>] (0 : ℝ), μ (closedBall a ρ \ F) ≤ γ * μ (closedBall a ρ))
    (htouch : ∀ ε d₀ : ℝ, 0 < ε → 0 < d₀ →
      ∃ y z : EuclideanSpace ℝ (Fin n), y ∈ F ∧ dist z y = infDist z F ∧
        0 < infDist z F ∧ infDist z F ≤ d₀ ∧ dist y a < ε * infDist z F) :
    ∃ (e : EuclideanSpace ℝ (Fin n)) (ν : OuterMeasure (EuclideanSpace ℝ (Fin n))),
      ‖e‖ = 1 ∧ IsTangentMeasure μ ν hμ a ∧
        SupportOuterMeasure ν ⊆ {x : EuclideanSpace ℝ (Fin n) | 0 ≤ inner ℝ x e} := by
  classical
  -- the touching data at the scales `1 / (k + 1)`
  have hchoice : ∀ k : ℕ, ∃ yz : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      yz.1 ∈ F ∧ dist yz.2 yz.1 = infDist yz.2 F ∧ 0 < infDist yz.2 F ∧
        infDist yz.2 F ≤ 1 / ((k : ℝ) + 1) ∧
        dist yz.1 a < 1 / ((k : ℝ) + 1) * infDist yz.2 F := by
    intro k
    obtain ⟨y, z, h1, h2, h3, h4, h5⟩ := htouch (1 / ((k : ℝ) + 1)) (1 / ((k : ℝ) + 1))
      (by positivity) (by positivity)
    exact ⟨(y, z), h1, h2, h3, h4, h5⟩
  choose YZ hYF hYZdist hDpos hDle hYa using hchoice
  set D : ℕ → ℝ := fun k ↦ infDist (YZ k).2 F with hDdef
  set ee : ℕ → EuclideanSpace ℝ (Fin n) :=
    fun k ↦ (D k)⁻¹ • ((YZ k).1 - (YZ k).2) with heedef
  have hDpos' : ∀ k, 0 < D k := hDpos
  have hDle' : ∀ k, D k ≤ 1 / ((k : ℝ) + 1) := hDle
  have hYa' : ∀ k, dist (YZ k).1 a < 1 / ((k : ℝ) + 1) * D k := hYa
  have hnormYZ : ∀ k, ‖(YZ k).1 - (YZ k).2‖ = D k := by
    intro k
    rw [← dist_eq_norm, dist_comm]
    exact hYZdist k
  have heeval : ∀ k, ee k = (D k)⁻¹ • ((YZ k).1 - (YZ k).2) := fun _ ↦ rfl
  have hee : ∀ k, ‖ee k‖ = 1 := by
    intro k
    rw [heeval k, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hDpos' k)), hnormYZ k,
      inv_mul_cancel₀ (hDpos' k).ne']
  -- a subsequence along which the directions converge
  obtain ⟨e, hesphere, ψ, hψ, hetend⟩ :=
    (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).tendsto_subseq
      (x := ee) (fun k ↦ by simpa [mem_sphere_zero_iff_norm] using hee k)
  have henorm : ‖e‖ = 1 := by simpa [mem_sphere_zero_iff_norm] using hesphere
  -- the blow-up scales
  set S : ℕ → ℝ := fun j ↦ Real.sqrt ((j : ℝ) + 1) with hSdef
  have hS1 : ∀ j, (1 : ℝ) ≤ S j := by
    intro j
    have h : (1 : ℝ) ≤ (j : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) j
      linarith
    show (1 : ℝ) ≤ Real.sqrt ((j : ℝ) + 1)
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt ((j : ℝ) + 1) := Real.sqrt_le_sqrt h
  have hSpos : ∀ j, 0 < S j := fun j ↦ lt_of_lt_of_le one_pos (hS1 j)
  have hSsq : ∀ j, S j ^ 2 = (j : ℝ) + 1 := fun j ↦ Real.sq_sqrt (by positivity)
  have hStend : Tendsto S atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  set rr : ℕ → ℝ := fun j ↦ D (ψ j) / S j with hrrdef
  have hrrpos : ∀ j, 0 < rr j := fun j ↦ div_pos (hDpos' _) (hSpos j)
  have hrrval : ∀ j, rr j = D (ψ j) / S j := fun _ ↦ rfl
  have hrrS : ∀ j, D (ψ j) = rr j * S j := by
    intro j
    rw [hrrval j, div_mul_cancel₀ _ (hSpos j).ne']
  have hψle : ∀ j : ℕ, (j : ℝ) ≤ (ψ j : ℝ) := by
    intro j
    exact_mod_cast hψ.le_apply
  have hrr0 : Tendsto rr atTop (𝓝 0) := by
    refine squeeze_zero (fun j ↦ (hrrpos j).le) (fun j ↦ ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : D (ψ j) ≤ 1 / ((ψ j : ℝ) + 1) := hDle' _
    have h3 : 1 / ((ψ j : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      linarith [hψle j]
    calc rr j ≤ D (ψ j) := by
          rw [hrrval j, div_le_iff₀ (hSpos j)]
          nlinarith [hDpos' (ψ j), hS1 j]
      _ ≤ 1 / ((j : ℝ) + 1) := le_trans h1 h3
  -- the tangent measure obtained by blowing up along these scales
  have hlowa : ∀ ρ : ℝ, 0 < ρ → ρ < r₀ → ENNReal.ofReal (p * ρ ^ s) ≤ μ (closedBall a ρ) :=
    fun ρ h1 h2 ↦ hlower a haF ρ h1 h2
  have huppa : ∀ ρ : ℝ, 0 < ρ → ρ < r₀ → μ (closedBall a ρ) ≤ ENNReal.ofReal (q * ρ ^ s) :=
    fun ρ h1 h2 ↦ hupper a haF ρ h1 h2
  have ha : a ∈ SupportOuterMeasure μ := mem_supportOuterMeasure_of_ball_lower_bound hp hr₀ hlowa
  have hdoub := limsup_ball_ratio_lt_top_of_ball_bounds_at hp hq hr₀ huppa hlowa
  obtain ⟨φ, ν, hseq, hν, hφ, htan, hconv⟩ :=
    exists_subseq_blowUp_weaklyConverges_tangentMeasure μ hμ a ha hdoub rr hrrpos hrr0
  refine ⟨e, ν, henorm, htan, ?_⟩
  intro x hx
  by_contra hcon
  simp only [mem_setOf_eq, not_le] at hcon
  set β : ℝ := -inner ℝ x e with hβdef
  have hxe : inner ℝ x e = -β := by rw [hβdef]; ring
  have hβ : 0 < β := by rw [hβdef]; linarith
  -- four eventual consequences of `S j → ∞`
  have hineq1 : ∀ᶠ j in atTop, inner ℝ x (ee (ψ j)) ≤ -(β / 2) := by
    have hcont : Tendsto (fun j ↦ (inner ℝ x (ee (ψ j)) : ℝ)) atTop (𝓝 (inner ℝ x e)) := by
      have hc : Continuous fun y : EuclideanSpace ℝ (Fin n) ↦ (inner ℝ x y : ℝ) := by fun_prop
      exact (hc.tendsto e).comp hetend
    have hlt : (inner ℝ x e : ℝ) < -(β / 2) := by rw [hxe]; linarith
    exact ((tendsto_order.1 hcont).2 _ hlt).mono fun j hj ↦ hj.le
  have hineq2 : ∀ᶠ j in atTop, rr j * ‖x‖ ^ 2 ≤ D (ψ j) * (β / 2) := by
    filter_upwards [hStend.eventually_ge_atTop (2 * ‖x‖ ^ 2 / β)] with j hj
    rw [div_le_iff₀ hβ] at hj
    have hmul := mul_le_mul_of_nonneg_left hj (hrrpos j).le
    rw [hrrS j]
    nlinarith [hrrpos j, hSpos j]
  have hineq3 : ∀ᶠ j in atTop, dist (YZ (ψ j)).1 a ≤ rr j * (β / 8) := by
    filter_upwards [hStend.eventually_ge_atTop (8 / β)] with j hj
    have hSβ : 8 ≤ S j * β := by
      rw [div_le_iff₀ hβ] at hj
      linarith
    have hA : dist (YZ (ψ j)).1 a < 1 / ((ψ j : ℝ) + 1) * D (ψ j) := hYa' _
    have h3 : 1 / ((ψ j : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      linarith [hψle j]
    have hB : 1 / ((ψ j : ℝ) + 1) * D (ψ j) ≤ 1 / ((j : ℝ) + 1) * D (ψ j) :=
      mul_le_mul_of_nonneg_right h3 (hDpos' _).le
    have hC : 1 / ((j : ℝ) + 1) * D (ψ j) ≤ rr j * (β / 8) := by
      rw [← hSsq j, hrrS j, div_mul_eq_mul_div, one_mul,
        div_le_iff₀ (by positivity : (0 : ℝ) < S j ^ 2)]
      nlinarith [hrrpos j, hSpos j, mul_pos (hrrpos j) (hSpos j)]
    linarith
  have hineq4 : ∀ᶠ j in atTop, rr j * (β / 4) ≤ D (ψ j) := by
    filter_upwards [hStend.eventually_ge_atTop (β / 4)] with j hj
    rw [hrrS j]
    nlinarith [hrrpos j]
  -- the blow-ups eventually push the points of `F` away from `x`
  have hfar : ∀ᶠ i in atTop, ∀ y' ∈ F, rr i * (β / 8) ≤ dist y' (a + rr i • x) := by
    filter_upwards [hineq1, hineq2, hineq3, hineq4] with i h1 h2 h3 h4 y' hy'
    have hdpos : 0 < D (ψ i) := hDpos' _
    have hejn : ‖ee (ψ i)‖ = 1 := hee _
    have hZ : (YZ (ψ i)).1 - (YZ (ψ i)).2 = D (ψ i) • ee (ψ i) := by
      rw [heeval (ψ i), smul_smul, mul_inv_cancel₀ hdpos.ne', one_smul]
    set v : EuclideanSpace ℝ (Fin n) := rr i • x + D (ψ i) • ee (ψ i) with hvdef
    have hexp : ‖v‖ ^ 2 = rr i ^ 2 * ‖x‖ ^ 2
        + 2 * (rr i * D (ψ i)) * inner ℝ x (ee (ψ i)) + D (ψ i) ^ 2 := by
      rw [hvdef, norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left,
        real_inner_smul_right, hejn]
      simp only [Real.norm_eq_abs, abs_of_pos (hrrpos i), abs_of_pos hdpos, mul_one]
      ring
    have hT : 0 ≤ D (ψ i) - rr i * (β / 4) := by linarith
    have hvle : ‖v‖ ≤ D (ψ i) - rr i * (β / 4) := by
      have hsq : ‖v‖ ^ 2 ≤ (D (ψ i) - rr i * (β / 4)) ^ 2 := by
        rw [hexp]
        have hA := mul_le_mul_of_nonneg_left h1 (mul_pos (hrrpos i) hdpos).le
        have hB := mul_le_mul_of_nonneg_left h2 (hrrpos i).le
        nlinarith [hA, hB, sq_nonneg (rr i * β), hrrpos i, hdpos]
      have hs := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (norm_nonneg v), Real.sqrt_sq hT] at hs
    have hudiff : (a + rr i • x) - (YZ (ψ i)).2 = (a - (YZ (ψ i)).1) + v := by
      rw [hvdef, ← hZ]; abel
    have hnormu : ‖(a + rr i • x) - (YZ (ψ i)).2‖ ≤ dist (YZ (ψ i)).1 a + ‖v‖ := by
      rw [hudiff]
      refine le_trans (norm_add_le _ _) ?_
      have hrw : ‖a - (YZ (ψ i)).1‖ = dist (YZ (ψ i)).1 a := by
        rw [dist_eq_norm, norm_sub_rev]
      rw [hrw]
    have hfarZ : D (ψ i) ≤ dist (YZ (ψ i)).2 y' := infDist_le_dist_of_mem hy'
    have htri : dist (YZ (ψ i)).2 y'
        ≤ dist (YZ (ψ i)).2 (a + rr i • x) + dist (a + rr i • x) y' := dist_triangle _ _ _
    have hZu : dist (YZ (ψ i)).2 (a + rr i • x) = ‖(a + rr i • x) - (YZ (ψ i)).2‖ := by
      rw [dist_comm, dist_eq_norm]
    rw [dist_comm y' (a + rr i • x)]
    linarith
  -- but the density of `F` at `a` forces points of `F` to be near `a + rr i • x`
  have hnear := tangent_exists_nearby_point_of_density hp hq hr₀ haF hupper hlower hdens
    (fun j ↦ hrrpos (φ j)) (hrr0.comp hφ.tendsto_atTop) hconv hx
    (show (0 : ℝ) < β / 8 by positivity)
  obtain ⟨j, hj1, hj2⟩ := (hnear.and (hφ.tendsto_atTop.eventually hfar)).exists
  obtain ⟨y', hy'F, hy'lt⟩ := hj1
  exact absurd hy'lt (not_lt.2 (hj2 y' hy'F))



/-! ## Mattila, Lemma 14.7 (1), (2) and (3)
The three statements below are the almost-everywhere statements of Lemma 14.7; `A` is the set
`positiveFiniteDensitySet s μ` of points where `0 < Θ^s_*(μ, a) ≤ Θ^{*s}(μ, a) < ∞`, and
"`μ` almost all points `a ∈ A`" is expressed by exhibiting a `μ`-null exceptional set `E`. -/
/-- **Mattila, Lemma 14.7 (1).**
At `μ` almost all points `a` of `A = {a | 0 < Θ^s_*(μ, a) ≤ Θ^{*s}(μ, a) < ∞}`: for every
tangent measure `ν ∈ Tan (μ, a)` there is a positive (finite) number `c` such that
`t c r ^ s ≤ ν (B (x, r)) ≤ c r ^ s` for `x ∈ spt ν` and `0 < r < ∞`, where
`t = t (a) = Θ^s_*(μ, a) / Θ^{*s}(μ, a)`.
The proof needs no sign assumption on the exponent `s`. -/
theorem mattila_14_7_1 {s : ℝ}
    (μ : OuterMeasure (EuclideanSpace ℝ (Fin n))) (hμ : RadonOuterMeasure μ) :
    ∃ E : Set (EuclideanSpace ℝ (Fin n)), μ E = 0 ∧
      ∀ a ∈ positiveFiniteDensitySet s μ \ E, ∀ ν, IsTangentMeasure μ ν hμ a →
        ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
          ∀ x ∈ SupportOuterMeasure ν, ∀ r : ℝ, 0 < r →
            sDensityRatio s μ a * c * ENNReal.ofReal (r ^ s) ≤ ν (closedBall x r) ∧
              ν (closedBall x r) ≤ c * ENNReal.ofReal (r ^ s) := by
  -- the exceptional set: the non-density points of the countably many sets `goodSet`
  have hex : ∀ i : ℚ × ℚ × ℕ, ∃ N : Set (EuclideanSpace ℝ (Fin n)), μ N = 0 ∧
      ∀ a ∈ goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ \ N, ∀ γ : ℝ≥0∞, 0 < γ →
        ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
          μ (closedBall a ρ \ goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ)
            ≤ γ * μ (closedBall a ρ) :=
    fun i ↦ exists_null_of_not_density_point μ hμ (isClosed_goodSet _ _ _ _ μ).measurableSet
  choose N hN0 hN using hex
  refine ⟨⋃ i, N i, measure_iUnion_null hN0, ?_⟩
  rintro a ⟨ha, haE⟩ ν htan
  obtain ⟨hνr, hν0, -⟩ := id htan
  obtain ⟨hl, hlu, hu⟩ := ha
  -- the sharp constant `t`
  set t := sDensityRatio s μ a with ht
  have htpos : 0 < t := ENNReal.div_pos hl.ne' hu.ne
  have htle : t ≤ 1 := by
    rw [ht, sDensityRatio]
    exact ENNReal.div_le_of_le_mul (by simpa using hlu)
  have httop : t ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top htle
  set T := t.toReal with hT
  have hTpos : 0 < T := ENNReal.toReal_pos htpos.ne' httop
  have hTt : ENNReal.ofReal T = t := ENNReal.ofReal_toReal httop
  -- a sequence of constants increasing to `t`
  set θ : ℕ → ℝ := fun k ↦ T - T / (k + 2) with hθdef
  have hθpos : ∀ k, 0 < θ k := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have : T / ((k : ℝ) + 2) < T := by
      rw [div_lt_iff₀ hk]
      nlinarith
    simpa [hθdef] using this
  have hθlb : ∀ k, T / 2 ≤ θ k := by
    intro k
    have hk : (2 : ℝ) ≤ (k : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have : T / ((k : ℝ) + 2) ≤ T / 2 :=
      div_le_div_of_nonneg_left hTpos.le (by norm_num) hk
    simp only [hθdef]
    linarith
  have hθlt : ∀ k, ENNReal.ofReal (θ k) < t := by
    intro k
    rw [← hTt]
    refine (ENNReal.ofReal_lt_ofReal_iff hTpos).mpr ?_
    have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have : 0 < T / ((k : ℝ) + 2) := by positivity
    simp only [hθdef]
    linarith
  have hθtend : Tendsto (fun k ↦ ENNReal.ofReal (θ k)) atTop (𝓝 t) := by
    have h2 : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have h1 : Tendsto (fun k : ℕ ↦ T / ((k : ℝ) + 2)) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds h2
    have h3 : Tendsto θ atTop (𝓝 T) := by
      simpa [hθdef] using tendsto_const_nhds.sub h1
    rw [← hTt]
    exact (ENNReal.continuous_ofReal.tendsto T).comp h3
  -- the estimate with constant `θ k`, for every `k`
  have hmain : ∀ k : ℕ, ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
      ∀ x ∈ SupportOuterMeasure ν, ∀ ρ : ℝ, 0 < ρ →
        ENNReal.ofReal (θ k) * c * ENNReal.ofReal (ρ ^ s) ≤ ν (closedBall x ρ) ∧
          ν (closedBall x ρ) ≤ c * ENNReal.ofReal (ρ ^ s) := by
    intro k
    obtain ⟨p, q, m, hp, hq, hθq, -, hmem⟩ :=
      exists_goodSet_mem ⟨hl, hlu, hu⟩ (hθpos k) (hθlt k)
    have haN : a ∉ N (p, q, m) := fun h ↦ haE (mem_iUnion.2 ⟨(p, q, m), h⟩)
    have hdens := hN (p, q, m) a ⟨hmem, haN⟩
    have hbounds : ∀ y ∈ goodSet s (p : ℝ) (q : ℝ) m μ, ∀ ρ : ℝ, 0 < ρ → ρ < 1 / (m + 1) →
        ENNReal.ofReal (θ k * (q : ℝ) * ρ ^ s) ≤ μ (closedBall y ρ) ∧
          μ (closedBall y ρ) ≤ ENNReal.ofReal ((q : ℝ) * ρ ^ s) := by
      intro y hy ρ hρ hρm
      obtain ⟨h1, h2⟩ := hy ρ hρ hρm
      refine ⟨le_trans (ENNReal.ofReal_le_ofReal ?_) h1, h2⟩
      have hpow : (0 : ℝ) ≤ ρ ^ s := Real.rpow_nonneg hρ.le s
      nlinarith
    have hr₀ : (0 : ℝ) < 1 / (m + 1) := by positivity
    exact tangent_ball_bounds_of_density_point hq (hθpos k) hr₀ μ hμ hbounds hmem hdens ν htan
  exact exists_uniform_constant_of_tendsto hνr hν0 (by positivity) hθlb hθtend hmain
/-- **Mattila, Lemma 14.7 (2).**
If, in addition, at `μ` almost all `z ∈ A` the upper bound
`limsup_{δ ↓ 0} sup {d (B) ^ (-s) μ (B) : B a closed ball with z ∈ B, d (B) < δ}
  ≤ Θ^{*s}(μ, z)`
holds, then at `μ` almost all `a ∈ A` every tangent measure `ν ∈ Tan (μ, a)` satisfies
`ν (B (x, r)) ≤ c r ^ s` for **all** `x ∈ ℝⁿ` and `r > 0`, with the same constant `c` as in
Lemma 14.7 (1). -/
theorem mattila_14_7_2 {s : ℝ}
    (μ : OuterMeasure (EuclideanSpace ℝ (Fin n))) (hμ : RadonOuterMeasure μ)
    (hball : ∃ E₀ : Set (EuclideanSpace ℝ (Fin n)), μ E₀ = 0 ∧
      ∀ z ∈ positiveFiniteDensitySet s μ \ E₀,
        upperBallSDensity s μ z ≤ upperSDensity s μ z) :
    ∃ E : Set (EuclideanSpace ℝ (Fin n)), μ E = 0 ∧
      ∀ a ∈ positiveFiniteDensitySet s μ \ E, ∀ ν, IsTangentMeasure μ ν hμ a →
        ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
          (∀ x ∈ SupportOuterMeasure ν, ∀ r : ℝ, 0 < r →
            sDensityRatio s μ a * c * ENNReal.ofReal (r ^ s) ≤ ν (closedBall x r) ∧
              ν (closedBall x r) ≤ c * ENNReal.ofReal (r ^ s)) ∧
          ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
            ν (closedBall x r) ≤ c * ENNReal.ofReal (r ^ s) := by
  obtain ⟨E₀, hE₀, hballdens⟩ := hball
  have hex : ∀ i : ℚ × ℚ × ℕ, ∃ N : Set (EuclideanSpace ℝ (Fin n)), μ N = 0 ∧
      ∀ a ∈ (goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ ∩ goodBallSet s (i.2.1 : ℝ) i.2.2 μ) \ N,
        ∀ γ : ℝ≥0∞, 0 < γ →
        ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
          μ (closedBall a ρ \
              (goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ ∩ goodBallSet s (i.2.1 : ℝ) i.2.2 μ))
            ≤ γ * μ (closedBall a ρ) :=
    fun i ↦ exists_null_of_not_density_point μ hμ
      (((isClosed_goodSet _ _ _ _ μ).inter (isClosed_goodBallSet _ _ _ μ)).measurableSet)
  choose N hN0 hN using hex
  have hUnull : μ (⋃ i, N i) = 0 := measure_iUnion_null hN0
  refine ⟨E₀ ∪ ⋃ i, N i, ?_, ?_⟩
  · refine le_antisymm (le_trans (measure_union_le _ _) ?_) (zero_le _)
    rw [hE₀, hUnull]
    simp
  rintro a ⟨ha, haE⟩ ν htan
  have haE₀ : a ∉ E₀ := fun h ↦ haE (Set.mem_union_left _ h)
  have haU : a ∉ ⋃ i, N i := fun h ↦ haE (Set.mem_union_right _ h)
  have hbd : upperBallSDensity s μ a ≤ upperSDensity s μ a := hballdens a ⟨ha, haE₀⟩
  obtain ⟨hνr, hν0, -⟩ := id htan
  obtain ⟨hl, hlu, hu⟩ := ha
  set t := sDensityRatio s μ a with ht
  have htpos : 0 < t := ENNReal.div_pos hl.ne' hu.ne
  have htle : t ≤ 1 := by
    rw [ht, sDensityRatio]
    exact ENNReal.div_le_of_le_mul (by simpa using hlu)
  have httop : t ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top htle
  set T := t.toReal with hT
  have hTpos : 0 < T := ENNReal.toReal_pos htpos.ne' httop
  have hTt : ENNReal.ofReal T = t := ENNReal.ofReal_toReal httop
  set θ : ℕ → ℝ := fun k ↦ T - T / (k + 2) with hθdef
  have hθpos : ∀ k, 0 < θ k := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have : T / ((k : ℝ) + 2) < T := by
      rw [div_lt_iff₀ hk]
      nlinarith
    simpa [hθdef] using this
  have hθlb : ∀ k, T / 2 ≤ θ k := by
    intro k
    have hk : (2 : ℝ) ≤ (k : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have : T / ((k : ℝ) + 2) ≤ T / 2 :=
      div_le_div_of_nonneg_left hTpos.le (by norm_num) hk
    simp only [hθdef]
    linarith
  have hθlt : ∀ k, ENNReal.ofReal (θ k) < t := by
    intro k
    rw [← hTt]
    refine (ENNReal.ofReal_lt_ofReal_iff hTpos).mpr ?_
    have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have : 0 < T / ((k : ℝ) + 2) := by positivity
    simp only [hθdef]
    linarith
  have hθtend : Tendsto (fun k ↦ ENNReal.ofReal (θ k)) atTop (𝓝 t) := by
    have h2 : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have h1 : Tendsto (fun k : ℕ ↦ T / ((k : ℝ) + 2)) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds h2
    have h3 : Tendsto θ atTop (𝓝 T) := by
      simpa [hθdef] using tendsto_const_nhds.sub h1
    rw [← hTt]
    exact (ENNReal.continuous_ofReal.tendsto T).comp h3
  have hmain : ∀ k : ℕ, ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
      (∀ x ∈ SupportOuterMeasure ν, ∀ ρ : ℝ, 0 < ρ →
        ENNReal.ofReal (θ k) * c * ENNReal.ofReal (ρ ^ s) ≤ ν (closedBall x ρ)) ∧
      ∀ (x : EuclideanSpace ℝ (Fin n)) (ρ : ℝ), 0 < ρ →
        ν (closedBall x ρ) ≤ c * ENNReal.ofReal (ρ ^ s) := by
    intro k
    obtain ⟨p, q, m, hp, hq, hθq, hqsup, hmem⟩ :=
      exists_goodSet_mem ⟨hl, hlu, hu⟩ (hθpos k) (hθlt k)
    obtain ⟨m', hmem'⟩ := exists_goodBallSet_mem hq hbd hqsup
    set M := max m m' with hM
    have hmemM : a ∈ goodSet s (p : ℝ) (q : ℝ) M μ :=
      goodSet_mono_nat (le_max_left _ _) hmem
    have hmemM' : a ∈ goodBallSet s (q : ℝ) M μ :=
      goodBallSet_mono_nat (le_max_right _ _) hmem'
    have haN : a ∉ N (p, q, M) := fun h ↦ haU (mem_iUnion.2 ⟨(p, q, M), h⟩)
    have hdens := hN (p, q, M) a ⟨⟨hmemM, hmemM'⟩, haN⟩
    have hbounds : ∀ y ∈ goodSet s (p : ℝ) (q : ℝ) M μ ∩ goodBallSet s (q : ℝ) M μ,
        ∀ ρ : ℝ, 0 < ρ → ρ < 1 / (M + 1) →
        ENNReal.ofReal (θ k * (q : ℝ) * ρ ^ s) ≤ μ (closedBall y ρ) ∧
          μ (closedBall y ρ) ≤ ENNReal.ofReal ((q : ℝ) * ρ ^ s) := by
      intro y hy ρ hρ hρm
      obtain ⟨h1, h2⟩ := hy.1 ρ hρ hρm
      refine ⟨le_trans (ENNReal.ofReal_le_ofReal ?_) h1, h2⟩
      have hpow : (0 : ℝ) ≤ ρ ^ s := Real.rpow_nonneg hρ.le s
      nlinarith
    have hballbd : ∀ z ∈ goodSet s (p : ℝ) (q : ℝ) M μ ∩ goodBallSet s (q : ℝ) M μ,
        ∀ (y : EuclideanSpace ℝ (Fin n)) (w : ℝ), 0 < w → w < 1 / (M + 1) →
        z ∈ closedBall y w → μ (closedBall y w) ≤ ENNReal.ofReal ((q : ℝ) * w ^ s) :=
      fun z hz y w hw hwm hzmem ↦ hz.2 y w hw hwm hzmem
    have hr₀ : (0 : ℝ) < 1 / (M + 1) := by positivity
    exact tangent_ball_bounds_of_density_point_of_ball_bounds hq (hθpos k) hr₀ μ hμ hbounds
      hballbd ⟨hmemM, hmemM'⟩ hdens ν htan
  obtain ⟨c, hc0, hctop, hclo, hcup⟩ :=
    exists_uniform_constant_of_tendsto_ball hνr hν0 (by positivity : (0 : ℝ) < T / 2) hθlb
      hθtend hmain
  exact ⟨c, hc0, hctop, fun x hx ρ hρ ↦ ⟨hclo x hx ρ hρ, hcup x ρ hρ⟩, hcup⟩
/-- **Mattila, Lemma 14.7 (3).**
If `s < n`, then at `μ` almost all `a ∈ A` there are a unit vector `e` and a tangent measure
`ν ∈ Tan (μ, a)` whose support is contained in the half-space `{x | 0 ≤ x ⬝ e}`.
The proof runs as follows.  Almost every `a ∈ A` lies in one of the closed sets
`F = goodSet s p q m μ`, on which the measures of all small balls are comparable to `ρ ^ s`, and
is a `μ`-density point of `F`.  Since `s < n`, a Fubini argument shows that a definite proportion
of every ball centred on `F` is a hole of `F` (`exists_hole_of_ball_bounds`), and a density
argument then shows that almost every point of `F` is an *asymptotic touching point*: there are
points `y ∈ F` touching holes `B (z, d)` with `d → 0` and `dist y a` negligible compared with `d`
(`exists_touching_points_ae`).  Blowing `μ` up at `a` at scales `r` with `dist y a ≪ r ≪ d` turns
these holes into balls of radius tending to infinity whose boundaries pass arbitrarily close to
the origin; in the limit they exhaust an open half-space, so the resulting tangent measure is
supported in the complementary closed half-space
(`exists_halfSpace_tangentMeasure_of_touching`).
The proof turned out not to need any positivity assumption on the exponent `s`, so the
hypothesis `0 < s` was dropped from the statement, as in parts (1) and (2). -/
theorem mattila_14_7_3 {s : ℝ} (hsn : s < n)
    (μ : OuterMeasure (EuclideanSpace ℝ (Fin n))) (hμ : RadonOuterMeasure μ) :
    ∃ E : Set (EuclideanSpace ℝ (Fin n)), μ E = 0 ∧
      ∀ a ∈ positiveFiniteDensitySet s μ \ E,
        ∃ (e : EuclideanSpace ℝ (Fin n)) (ν : OuterMeasure (EuclideanSpace ℝ (Fin n))),
          ‖e‖ = 1 ∧ IsTangentMeasure μ ν hμ a ∧
            SupportOuterMeasure ν ⊆ {x : EuclideanSpace ℝ (Fin n) | 0 ≤ inner ℝ x e} := by
  classical
  -- the upper and lower bounds carried by the sets `goodSet s p q m μ`
  have hup : ∀ (p q : ℝ) (m : ℕ), ∀ y ∈ goodSet s p q m μ, ∀ ρ : ℝ, 0 < ρ →
      ρ < 1 / ((m : ℝ) + 1) → μ (closedBall y ρ) ≤ ENNReal.ofReal (q * ρ ^ s) :=
    fun p q m y hy ρ h1 h2 ↦ (hy ρ h1 h2).2
  have hlo : ∀ (p q : ℝ) (m : ℕ), ∀ y ∈ goodSet s p q m μ, ∀ ρ : ℝ, 0 < ρ →
      ρ < 1 / ((m : ℝ) + 1) → ENNReal.ofReal (p * ρ ^ s) ≤ μ (closedBall y ρ) :=
    fun p q m y hy ρ h1 h2 ↦ (hy ρ h1 h2).1
  -- the first family of exceptional sets: the non-density points of the good sets
  have hdensex : ∀ i : ℚ × ℚ × ℕ, ∃ N : Set (EuclideanSpace ℝ (Fin n)), μ N = 0 ∧
      ∀ a ∈ goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ \ N, ∀ γ : ℝ≥0∞, 0 < γ →
        ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
          μ (closedBall a ρ \ goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ)
            ≤ γ * μ (closedBall a ρ) :=
    fun i ↦ exists_null_of_not_density_point μ hμ (isClosed_goodSet _ _ _ _ μ).measurableSet
  choose N₁ hN₁0 hN₁ using hdensex
  -- the second family: the points which are far from all touching points
  have htouchex : ∀ i : ℚ × ℚ × ℕ, ∃ N : Set (EuclideanSpace ℝ (Fin n)), μ N = 0 ∧
      (0 < (i.1 : ℝ) → 0 < (i.2.1 : ℝ) →
        ∀ a ∈ goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ \ N, ∀ ε d₀ : ℝ, 0 < ε → 0 < d₀ →
          ∃ y z : EuclideanSpace ℝ (Fin n),
            y ∈ goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ ∧
              dist z y = infDist z (goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ) ∧
              0 < infDist z (goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ) ∧
              infDist z (goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ) ≤ d₀ ∧
              dist y a < ε * infDist z (goodSet s (i.1 : ℝ) (i.2.1 : ℝ) i.2.2 μ)) := by
    intro i
    by_cases hpq : 0 < (i.1 : ℝ) ∧ 0 < (i.2.1 : ℝ)
    · obtain ⟨N, hN0, hN⟩ :=
        exists_touching_points_ae hsn hpq.1 hpq.2
          (show (0 : ℝ) < 1 / ((i.2.2 : ℝ) + 1) by positivity) μ hμ
          (isClosed_goodSet _ _ _ _ μ) (hup _ _ _) (hlo _ _ _)
      exact ⟨N, hN0, fun _ _ ↦ hN⟩
    · exact ⟨∅, by simp, fun h1 h2 ↦ absurd ⟨h1, h2⟩ hpq⟩
  choose N₂ hN₂0 hN₂ using htouchex
  refine ⟨⋃ i : ℚ × ℚ × ℕ, (N₁ i ∪ N₂ i), ?_, ?_⟩
  · refine measure_iUnion_null fun i ↦ le_antisymm ?_ (zero_le _)
    calc μ (N₁ i ∪ N₂ i) ≤ μ (N₁ i) + μ (N₂ i) := measure_union_le _ _
      _ = 0 := by rw [hN₁0, hN₂0]; simp
  · rintro a ⟨ha, haE⟩
    obtain ⟨hl, hlu, hu⟩ := ha
    -- the density ratio at `a` is positive, so `a` lies in one of the good sets
    set t := sDensityRatio s μ a with ht
    have htpos : 0 < t := ENNReal.div_pos hl.ne' hu.ne
    have htle : t ≤ 1 := by
      rw [ht, sDensityRatio]
      exact ENNReal.div_le_of_le_mul (by simpa using hlu)
    have httop : t ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top htle
    have hTpos : 0 < t.toReal := ENNReal.toReal_pos htpos.ne' httop
    have hTt : ENNReal.ofReal t.toReal = t := ENNReal.ofReal_toReal httop
    have hθlt : ENNReal.ofReal (t.toReal / 2) < t := by
      have h := (ENNReal.ofReal_lt_ofReal_iff hTpos).2 (half_lt_self hTpos)
      rwa [hTt] at h
    obtain ⟨p, q, m, hp, hq, -, -, hmem⟩ :=
      exists_goodSet_mem ⟨hl, hlu, hu⟩ (show (0 : ℝ) < t.toReal / 2 by positivity) hθlt
    have haN₁ : a ∉ N₁ (p, q, m) := fun h ↦ haE (mem_iUnion.2 ⟨(p, q, m), Or.inl h⟩)
    have haN₂ : a ∉ N₂ (p, q, m) := fun h ↦ haE (mem_iUnion.2 ⟨(p, q, m), Or.inr h⟩)
    exact exists_halfSpace_tangentMeasure_of_touching hp hq
      (show (0 : ℝ) < 1 / ((m : ℝ) + 1) by positivity) μ hμ hmem (hup _ _ _) (hlo _ _ _)
      (hN₁ (p, q, m) a ⟨hmem, haN₁⟩)
      (hN₂ (p, q, m) hp hq a ⟨hmem, haN₂⟩)
/-! ## Mattila, Lemma 14.7 (4) -/
/-- **Mattila, Lemma 14.7 (4).**
If there exist positive numbers `d`, `t` and `r₀` such that
`t d r ^ s ≤ μ (B (a, r)) ≤ d r ^ s` for all `a ∈ spt μ` and `0 < r < r₀`,
then at every point `a ∈ spt μ` the set `Tan (μ, a)` of tangent measures is nonempty, and every
tangent measure `ν ∈ Tan (μ, a)` satisfies the conclusion of Lemma 14.7 (1): there is a positive
finite constant `c` with `t c r ^ s ≤ ν (B (x, r)) ≤ c r ^ s` for all `x ∈ spt ν` and
`0 < r < ∞`. -/
theorem mattila_14_7_4 {s d t r₀ : ℝ} (hd : 0 < d) (ht : 0 < t) (hr₀ : 0 < r₀)
    (μ : OuterMeasure (EuclideanSpace ℝ (Fin n))) (hμ : RadonOuterMeasure μ)
    (hbounds : ∀ y ∈ SupportOuterMeasure μ, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (t * d * ρ ^ s) ≤ μ (closedBall y ρ) ∧
        μ (closedBall y ρ) ≤ ENNReal.ofReal (d * ρ ^ s))
    (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ SupportOuterMeasure μ) :
    (∃ ν, IsTangentMeasure μ ν hμ a) ∧
      ∀ ν, IsTangentMeasure μ ν hμ a →
        ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
          ∀ x ∈ SupportOuterMeasure ν, ∀ ρ : ℝ, 0 < ρ →
            ENNReal.ofReal t * c * ENNReal.ofReal (ρ ^ s) ≤ ν (closedBall x ρ) ∧
              ν (closedBall x ρ) ≤ c * ENNReal.ofReal (ρ ^ s) := by
  have hupper : ∀ y ∈ SupportOuterMeasure μ, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      μ (closedBall y ρ) ≤ ENNReal.ofReal (d * ρ ^ s) :=
    fun y hy ρ h1 h2 ↦ (hbounds y hy ρ h1 h2).2
  have hlower : ∀ y ∈ SupportOuterMeasure μ, ∀ ρ : ℝ, 0 < ρ → ρ < r₀ →
      ENNReal.ofReal (t * d * ρ ^ s) ≤ μ (closedBall y ρ) :=
    fun y hy ρ h1 h2 ↦ (hbounds y hy ρ h1 h2).1
  have hdoub : limsup (fun ρ : ℝ ↦ μ (ball a (2 * ρ)) / μ (ball a ρ)) (𝓝[>] (0 : ℝ)) < ∞ :=
    limsup_ball_ratio_lt_top_of_uniform hd ht hr₀ ha hupper hlower
  constructor
  · obtain ⟨φ, ν, hseq, hν, hφ, htan, hconv⟩ :=
      exists_subseq_blowUp_weaklyConverges_tangentMeasure μ hμ a ha hdoub
        (fun i ↦ 1 / ((i : ℝ) + 1)) (fun i ↦ by positivity)
        tendsto_one_div_add_atTop_nhds_zero_nat
    exact ⟨ν, htan⟩
  · rintro ν ⟨hν, hν0, rs, cs, hrpos, hcpos, hcfin, hr0, hseq, hconv⟩
    obtain ⟨lam, -, φ, hφ, hlam⟩ := (isCompact_univ (X := ℝ≥0∞)).tendsto_subseq
      (x := fun i ↦ cs i * ENNReal.ofReal (rs i ^ s)) (fun i ↦ mem_univ _)
    have hrpos' : ∀ j, 0 < rs (φ j) := fun j ↦ hrpos _
    have hr0' : Tendsto (fun j ↦ rs (φ j)) atTop (𝓝 0) := hr0.comp hφ.tendsto_atTop
    have hconv' : OuterMeasure.WeaklyConverges
        (fun j ↦ cs (φ j) • OuterMeasure.map (blowUpMap a (rs (φ j))) μ) ν
        (fun j ↦ hseq (φ j)) hν := hconv.comp hφ.tendsto_atTop
    have hlamfin : lam ≠ ∞ :=
      tangent_scaling_lt_top hd ht hr₀ ha hlower hrpos' hr0' hlam hconv'
    have hlampos : 0 < lam :=
      tangent_scaling_pos hd hr₀ ha hupper hrpos' hr0' hlam hν0 hconv'
    refine ⟨ENNReal.ofReal d * lam, ?_, ?_, ?_⟩
    · exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 hd).ne' hlampos.ne'
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hlamfin
    · intro x hx ρ hρ
      have hnear : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
          ∃ y ∈ SupportOuterMeasure μ, dist y (a + rs (φ j) • x) < rs (φ j) * ε :=
        fun ε hε ↦ tangent_exists_nearby_support_point hrpos' hconv' hx hε
      have hup := tangent_closedBall_le hd.le hr₀ hupper hrpos' hr0' hlam hlamfin hconv'
        hnear hρ
      have hlo := le_tangent_closedBall hd.le ht.le hr₀ hlower hrpos' hr0' hlam hlamfin
        hconv' hnear hρ
      constructor
      · refine le_trans (le_of_eq ?_) hlo
        rw [ENNReal.ofReal_mul (mul_nonneg ht.le hd.le), ENNReal.ofReal_mul ht.le]
        ring
      · refine le_trans hup (le_of_eq ?_)
        rw [ENNReal.ofReal_mul hd.le]
        ring

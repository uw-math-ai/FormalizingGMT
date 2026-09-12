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

/-! ## Scalar multiples of Radon outer measures -/
section Smul
/-- The measure associated to `c • ν` is `c` times the measure associated to `ν`. -/
lemma OuterMeasure.toMeasure_smul {X : Type*} [MeasurableSpace X] (ν : OuterMeasure X)
    (c : ℝ≥0∞)
    (h : ‹MeasurableSpace X› ≤ ν.caratheodory)
    (h' : ‹MeasurableSpace X› ≤ (c • ν).caratheodory) :
    (c • ν).toMeasure h' = c • ν.toMeasure h := by
  ext s hs
  rw [toMeasure_apply _ _ hs, Measure.smul_apply, toMeasure_apply _ _ hs]
  exact OuterMeasure.smul_apply c ν s
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
/-- A finite scalar multiple of a Radon outer measure is a Radon outer measure. -/
lemma RadonOuterMeasure.smul {ν : OuterMeasure X} (hν : RadonOuterMeasure ν) {c : ℝ≥0∞}
    (hc : c ≠ ∞) : RadonOuterMeasure (c • ν) := by
  have hcara : ‹MeasurableSpace X› ≤ (c • ν).caratheodory := by
    intro s hs
    have hs' : ν.IsCaratheodory s := hν.measurable_le_caratheodory s hs
    show (c • ν).IsCaratheodory s
    intro t
    simp only [OuterMeasure.smul_apply, smul_eq_mul, ← mul_add, hs' t]
  refine
    { measurable_le_caratheodory := hcara
      exists_measurable_superset := ?_
      regular_toMeasure := ?_ }
  · intro E
    obtain ⟨F, hF, hEF, hμF⟩ :=
      BorelRegularOuterMeasure.exists_measurable_superset (μ := ν) E
    refine ⟨F, hF, hEF, ?_⟩
    simp only [OuterMeasure.smul_apply, smul_eq_mul, hμF]
  · letI : (ν.toMeasure hν.measurable_le_caratheodory).Regular := hν.regular_toMeasure
    rw [OuterMeasure.toMeasure_smul ν c hν.measurable_le_caratheodory]
    exact Measure.Regular.smul hc
end Smul
/-! ## Elementary facts about weak convergence -/
namespace MeasureTheory
section WeakConvergenceFacts
variable {n : ℕ}
/-- Weak convergence is inherited by subsequences (more generally, by any reindexing along a
map tending to infinity). -/
lemma OuterMeasure.WeaklyConverges.comp
    {μ : ℕ → OuterMeasure (EuclideanSpace ℝ (Fin n))}
    {ν : OuterMeasure (EuclideanSpace ℝ (Fin n))}
    {hμ : ∀ k, RadonOuterMeasure (μ k)} {hν : RadonOuterMeasure ν}
    (h : OuterMeasure.WeaklyConverges μ ν hμ hν) {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) :
    OuterMeasure.WeaklyConverges (fun j ↦ μ (φ j)) ν (fun j ↦ hμ (φ j)) hν :=
  fun f ↦ (h f).comp hφ
/-- Rescaling a weakly convergent sequence by constants tending to `1` does not change the
weak limit. -/
lemma OuterMeasure.WeaklyConverges.smul_of_tendsto_one
    {μ : ℕ → OuterMeasure (EuclideanSpace ℝ (Fin n))}
    {ν : OuterMeasure (EuclideanSpace ℝ (Fin n))}
    {hμ : ∀ k, RadonOuterMeasure (μ k)} {hν : RadonOuterMeasure ν}
    (h : OuterMeasure.WeaklyConverges μ ν hμ hν) {e : ℕ → ℝ≥0∞}
    (he1 : Tendsto (fun i ↦ (e i).toReal) atTop (𝓝 1))
    (hsmul : ∀ i, RadonOuterMeasure (e i • μ i)) :
    OuterMeasure.WeaklyConverges (fun i ↦ e i • μ i) ν hsmul hν := by
  intro f
  have hint : ∀ i, ∫ x, f x ∂((e i • μ i).toMeasure (hsmul i).measurable_le_caratheodory)
      = (e i).toReal * ∫ x, f x ∂((μ i).toMeasure (hμ i).measurable_le_caratheodory) := by
    intro i
    rw [OuterMeasure.toMeasure_smul (μ i) (e i) (hμ i).measurable_le_caratheodory,
      integral_smul_measure, smul_eq_mul]
  simp only [hint]
  simpa using he1.mul (h f)
/-- Weak convergence only depends on the underlying sequence of outer measures. -/
lemma OuterMeasure.WeaklyConverges.congr_seq
    {F G : ℕ → OuterMeasure (EuclideanSpace ℝ (Fin n))}
    {ν : OuterMeasure (EuclideanSpace ℝ (Fin n))}
    (hFG : ∀ i, F i = G i)
    {hF : ∀ i, RadonOuterMeasure (F i)} {hG : ∀ i, RadonOuterMeasure (G i)}
    {hν : RadonOuterMeasure ν}
    (h : OuterMeasure.WeaklyConverges G ν hG hν) :
    OuterMeasure.WeaklyConverges F ν hF hν := by
  have hmeas : ∀ i, (F i).toMeasure (hF i).measurable_le_caratheodory
      = (G i).toMeasure (hG i).measurable_le_caratheodory := by
    intro i
    ext s hs
    rw [toMeasure_apply _ _ hs, toMeasure_apply _ _ hs, hFG i]
  intro f
  simpa only [hmeas] using h f
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
/-- The push-forward of a Radon outer measure under a blow-up map is a Radon outer measure. -/
lemma RadonOuterMeasure.map_blowUp {μ : OuterMeasure (EuclideanSpace ℝ (Fin n))}
    (hμ : RadonOuterMeasure μ) (a : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : r ≠ 0) :
    RadonOuterMeasure (OuterMeasure.map (blowUpMap a r) μ) := by
  set f := blowUpHomeomorph a hr
  have hfc : ⇑f = blowUpMap a r := rfl
  have hfmeas : Measurable (blowUpMap a r) := by
    rw [← hfc]; exact f.continuous.measurable
  have hcara : (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n))) ≤
      (OuterMeasure.map (blowUpMap a r) μ).caratheodory := by
    intro s hs
    show (OuterMeasure.map (blowUpMap a r) μ).IsCaratheodory s
    intro t
    have hpre : MeasurableSet (blowUpMap a r ⁻¹' s) := hfmeas hs
    have := hμ.measurable_le_caratheodory _ hpre (blowUpMap a r ⁻¹' t)
    simpa only [OuterMeasure.map_apply, preimage_inter, preimage_diff] using this
  refine
    { measurable_le_caratheodory := hcara
      exists_measurable_superset := ?_
      regular_toMeasure := ?_ }
  · intro E
    obtain ⟨F, hF, hEF, hμF⟩ :=
      BorelRegularOuterMeasure.exists_measurable_superset (μ := μ) (blowUpMap a r ⁻¹' E)
    refine ⟨⇑f.symm ⁻¹' F, f.symm.continuous.measurable hF, ?_, ?_⟩
    · intro y hy
      have : f.symm y ∈ blowUpMap a r ⁻¹' E := by
        simp only [mem_preimage, ← hfc, f.apply_symm_apply]
        exact hy
      exact hEF this
    · have hpre : blowUpMap a r ⁻¹' (⇑f.symm ⁻¹' F) = F := by
        ext x
        simp only [mem_preimage, ← hfc, f.symm_apply_apply]
      rw [OuterMeasure.map_apply, OuterMeasure.map_apply, hpre]
      exact hμF
  · letI : (μ.toMeasure hμ.measurable_le_caratheodory).Regular := hμ.regular_toMeasure
    have hmap : (OuterMeasure.map (blowUpMap a r) μ).toMeasure hcara
        = Measure.map ⇑f (μ.toMeasure hμ.measurable_le_caratheodory) := by
      ext s hs
      rw [toMeasure_apply _ _ hs, Measure.map_apply f.continuous.measurable hs,
        OuterMeasure.map_apply, hfc, toMeasure_apply _ _ (hfmeas hs)]
    rw [hmap]
    exact Measure.Regular.map f
end BlowUp
/-! ## Balls of positive and finite measure -/
section Balls
variable {n : ℕ}
lemma measure_ball_pos {μ : OuterMeasure (EuclideanSpace ℝ (Fin n))}
    {a : EuclideanSpace ℝ (Fin n)} (ha : a ∈ SupportOuterMeasure μ) {ρ : ℝ} (hρ : 0 < ρ) :
    0 < μ (ball a ρ) :=
  ha _ (ball_mem_nhds a hρ)
lemma measure_closedBall_lt_top {μ : OuterMeasure (EuclideanSpace ℝ (Fin n))}
    (hμ : RadonOuterMeasure μ) (a : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) :
    μ (closedBall a ρ) < ∞ := by
  letI : (μ.toMeasure hμ.measurable_le_caratheodory).Regular := hμ.regular_toMeasure
  have hcomp : IsCompact (closedBall a ρ) := isCompact_closedBall a ρ
  rw [← toMeasure_apply μ hμ.measurable_le_caratheodory hcomp.measurableSet]
  exact hcomp.measure_lt_top
lemma measure_ball_lt_top {μ : OuterMeasure (EuclideanSpace ℝ (Fin n))}
    (hμ : RadonOuterMeasure μ) (a : EuclideanSpace ℝ (Fin n)) (ρ : ℝ) :
    μ (ball a ρ) < ∞ :=
  lt_of_le_of_lt (measure_mono ball_subset_closedBall) (measure_closedBall_lt_top hμ a ρ)
end Balls
/-! ## Consequences of the doubling assumption 14.3 (1) -/
section Doubling
variable {n : ℕ}
/-- Assumption 14.3 (1) gives a genuine doubling inequality at small scales. -/
lemma exists_doubling_constant {μ : OuterMeasure (EuclideanSpace ℝ (Fin n))}
    (hμ : RadonOuterMeasure μ) {a : EuclideanSpace ℝ (Fin n)}
    (ha : a ∈ SupportOuterMeasure μ)
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
  have hpos : μ (ball a ρ) ≠ 0 := (measure_ball_pos ha hρ).ne'
  have hfin : μ (ball a ρ) ≠ ∞ := (measure_ball_lt_top hμ a ρ).ne
  exact ((ENNReal.div_lt_iff (Or.inl hpos) (Or.inl hfin)).mp hdiv).le
/-- Iterating the doubling inequality. -/
lemma measure_ball_two_pow_le {μ : OuterMeasure (EuclideanSpace ℝ (Fin n))}
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
lemma exists_measure_ball_le_measure_ball {μ : OuterMeasure (EuclideanSpace ℝ (Fin n))}
    (hμ : RadonOuterMeasure μ) {a : EuclideanSpace ℝ (Fin n)}
    (ha : a ∈ SupportOuterMeasure μ)
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
lemma limsup_normalizing_le {μ ν : OuterMeasure (EuclideanSpace ℝ (Fin n))}
    {a : EuclideanSpace ℝ (Fin n)} {r : ℕ → ℝ} {c : ℕ → ℝ≥0∞} (hr : ∀ i, 0 < r i)
    {hseq : ∀ i, RadonOuterMeasure (c i • OuterMeasure.map (blowUpMap a (r i)) μ)}
    {hν : RadonOuterMeasure ν}
    (hconv : OuterMeasure.WeaklyConverges
      (fun i ↦ c i • OuterMeasure.map (blowUpMap a (r i)) μ) ν hseq hν) :
    limsup (fun i ↦ c i * μ (closedBall a (r i))) atTop ≤ ν (closedBall 0 1) := by
  have hb := (OuterMeasure.weaklyConverges_iff_compactOpenBounds _ ν hseq hν).mp hconv
  have h1 := hb.1 (closedBall 0 1) (isCompact_closedBall _ _)
  have heq : ∀ i, (c i • OuterMeasure.map (blowUpMap a (r i)) μ) (closedBall 0 1)
      = c i * μ (closedBall a (r i)) := by
    intro i
    rw [OuterMeasure.smul_apply, smul_eq_mul, OuterMeasure.map_apply,
      blowUpMap_preimage_closedBall a (hr i), mul_one]
  simpa only [heq] using h1
/-- Lower bound for the normalizing constants: under assumption 14.3 (1) the numbers
`c i * μ (B (a, r i))` are eventually bounded away from `0`. -/
lemma exists_le_normalizing {μ ν : OuterMeasure (EuclideanSpace ℝ (Fin n))}
    (hμ : RadonOuterMeasure μ) {a : EuclideanSpace ℝ (Fin n)}
    (ha : a ∈ SupportOuterMeasure μ)
    (hdoub : limsup (fun ρ : ℝ ↦ μ (ball a (2 * ρ)) / μ (ball a ρ)) (𝓝[>] (0 : ℝ)) < ∞)
    {r : ℕ → ℝ} {c : ℕ → ℝ≥0∞} (hr : ∀ i, 0 < r i) (hr0 : Tendsto r atTop (𝓝 0))
    {hseq : ∀ i, RadonOuterMeasure (c i • OuterMeasure.map (blowUpMap a (r i)) μ)}
    {hν : RadonOuterMeasure ν} (hν0 : ν ≠ 0)
    (hconv : OuterMeasure.WeaklyConverges
      (fun i ↦ c i • OuterMeasure.map (blowUpMap a (r i)) μ) ν hseq hν) :
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
      exact le_antisymm (hcon _ hk) (zero_le _)
    have hsub : (univ : Set (EuclideanSpace ℝ (Fin n))) ⊆ ⋃ k : ℕ, ball 0 ((k : ℝ) + 1) := by
      intro x _
      obtain ⟨k, hk⟩ := exists_nat_gt (dist x 0)
      exact mem_iUnion.2 ⟨k, by simp only [mem_ball]; linarith⟩
    have huniv : ν univ = 0 :=
      le_antisymm ((measure_mono hsub).trans_eq (measure_iUnion_null hz)) (zero_le _)
    ext s
    exact le_antisymm ((measure_mono (subset_univ s)).trans_eq huniv) (zero_le _)
  have hfin : ν (ball 0 R) ≠ ∞ :=
    (lt_of_le_of_lt (measure_mono ball_subset_closedBall)
      (measure_closedBall_lt_top hν 0 R)).ne
  have hb := (OuterMeasure.weaklyConverges_iff_compactOpenBounds _ ν hseq hν).mp hconv
  have hopen := hb.2 (ball 0 R) isOpen_ball
  have heq : ∀ i, (c i • OuterMeasure.map (blowUpMap a (r i)) μ) (ball 0 R)
      = c i * μ (ball a (r i * R)) := by
    intro i
    rw [OuterMeasure.smul_apply, smul_eq_mul, OuterMeasure.map_apply,
      blowUpMap_preimage_ball a (hr i)]
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
If `μ` is a Radon outer measure on `ℝⁿ`, `a ∈ spt μ` satisfies
`limsup_{ρ ↓ 0} μ (B (a, 2ρ)) / μ (B (a, ρ)) < ∞`, then `0 ∈ spt ν` for every tangent
measure `ν ∈ Tan (μ, a)`. -/
theorem zero_mem_support_of_isTangentMeasure {n : ℕ}
    (μ ν : OuterMeasure (EuclideanSpace ℝ (Fin n))) (hμ : RadonOuterMeasure μ)
    (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ SupportOuterMeasure μ)
    (hdoub : limsup (fun ρ : ℝ ↦ μ (ball a (2 * ρ)) / μ (ball a ρ)) (𝓝[>] (0 : ℝ)) < ∞)
    (htan : IsTangentMeasure μ ν hμ a) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈ SupportOuterMeasure ν := by
  obtain ⟨hν, hν0, r, c, hr, hcpos, hcfin, hr0, hseq, hconv⟩ := htan
  have key : ∀ s : ℝ, 0 < s → 0 < ν (closedBall 0 s) := by
    intro s hs
    obtain ⟨δ, hδ, hδev⟩ := exists_le_normalizing hμ ha hdoub hr hr0 hν0 hconv
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
    have hb := (OuterMeasure.weaklyConverges_iff_compactOpenBounds _ ν hseq hν).mp hconv
    have h1 := hb.1 (closedBall 0 s) (isCompact_closedBall _ _)
    have heq : ∀ i, (c i • OuterMeasure.map (blowUpMap a (r i)) μ) (closedBall 0 s)
        = c i * μ (closedBall a (r i * s)) := by
      intro i
      rw [OuterMeasure.smul_apply, smul_eq_mul, OuterMeasure.map_apply,
        blowUpMap_preimage_closedBall a (hr i)]
    have hlimsup : δ / D ≤ limsup (fun i ↦ c i * μ (closedBall a (r i * s))) atTop :=
      le_limsup_of_frequently_le hbound.frequently
    refine lt_of_lt_of_le (ENNReal.div_pos_iff.2 ⟨hδ.ne', hDtop⟩) ?_
    exact hlimsup.trans (by simpa only [heq] using h1)
  intro U hU
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine lt_of_lt_of_le (key (ρ / 2) (by positivity)) (measure_mono ?_)
  exact (closedBall_subset_ball (by linarith)).trans hball
/-! ## Consequence (3): tangent measures arise from the canonical normalizations -/
/-- **Mattila, Chapter 14, consequence (3) of assumption 14.3 (1).**
If `μ` is a Radon outer measure on `ℝⁿ` and `a ∈ spt μ` satisfies
`limsup_{ρ ↓ 0} μ (B (a, 2ρ)) / μ (B (a, ρ)) < ∞`, then every tangent measure
`ν ∈ Tan (μ, a)` can be written as
`ν = c · lim_i μ (B (a, r i))⁻¹ • T_{a, r i #} μ`
for a strictly decreasing sequence of radii `r i ↓ 0` and a positive finite constant `c`. -/
theorem exists_normalized_blowUp_weaklyConverges_of_isTangentMeasure {n : ℕ}
    (μ ν : OuterMeasure (EuclideanSpace ℝ (Fin n))) (hμ : RadonOuterMeasure μ)
    (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ SupportOuterMeasure μ)
    (hdoub : limsup (fun ρ : ℝ ↦ μ (ball a (2 * ρ)) / μ (ball a ρ)) (𝓝[>] (0 : ℝ)) < ∞)
    (htan : IsTangentMeasure μ ν hμ a) :
    ∃ (r : ℕ → ℝ) (c : ℝ≥0∞),
      (∀ i, 0 < r i) ∧ StrictAnti r ∧ Tendsto r atTop (𝓝 0) ∧ 0 < c ∧ c ≠ ∞ ∧
      ∃ (hseq : ∀ i, RadonOuterMeasure
          (c • (μ (ball a (r i)))⁻¹ • OuterMeasure.map (blowUpMap a (r i)) μ))
        (hν : RadonOuterMeasure ν),
        OuterMeasure.WeaklyConverges
          (fun i ↦ c • (μ (ball a (r i)))⁻¹ • OuterMeasure.map (blowUpMap a (r i)) μ)
          ν hseq hν := by
  obtain ⟨hν, hν0, r, c, hr, hcpos, hcfin, hr0, hseq, hconv⟩ := htan
  set T : ℕ → ℝ≥0∞ := fun i ↦ c i * μ (ball a (r i))
  obtain ⟨δ, hδ, hδev⟩ := exists_le_normalizing hμ ha hdoub hr hr0 hν0 hconv
  have hMfin : ν (closedBall 0 1) ≠ ∞ := (measure_closedBall_lt_top hν 0 1).ne
  have hlimsupT : limsup T atTop ≤ ν (closedBall 0 1) := by
    refine le_trans (limsup_le_limsup (.of_forall fun i ↦ ?_)) (limsup_normalizing_le hr hconv)
    show c i * μ (ball a (r i)) ≤ c i * μ (closedBall a (r i))
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
      t • (μ (ball a (r (χ j))))⁻¹ • OuterMeasure.map (blowUpMap a (r (χ j))) μ
        = (t / T (χ j)) • (c (χ j) • OuterMeasure.map (blowUpMap a (r (χ j))) μ) := by
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
  have hradon_smul : ∀ j, RadonOuterMeasure
      ((t / T (χ j)) • (c (χ j) • OuterMeasure.map (blowUpMap a (r (χ j))) μ)) :=
    fun j ↦ (hseq (χ j)).smul (he_top j)
  have hradon : ∀ j, RadonOuterMeasure
      (t • (μ (ball a (r (χ j))))⁻¹ • OuterMeasure.map (blowUpMap a (r (χ j))) μ) := by
    intro j
    rw [hsmul_eq j]
    exact hradon_smul j
  refine ⟨fun j ↦ r (χ j), t, fun j ↦ hr _, hanti, hr0.comp hχ, ht0, httop, hradon, hν, ?_⟩
  have hsub : OuterMeasure.WeaklyConverges
      (fun j ↦ c (χ j) • OuterMeasure.map (blowUpMap a (r (χ j))) μ) ν
      (fun j ↦ hseq (χ j)) hν := hconv.comp hχ
  have htoReal : Tendsto (fun j ↦ (T (χ j)).toReal) atTop (𝓝 t.toReal) :=
    (ENNReal.tendsto_toReal httop).comp hTχ
  have htr : t.toReal ≠ 0 := by
    simp [ENNReal.toReal_eq_zero_iff, ht0.ne', httop]
  have hetend : Tendsto (fun j ↦ (t / T (χ j)).toReal) atTop (𝓝 1) := by
    have hdiv : Tendsto (fun j ↦ t.toReal / (T (χ j)).toReal) atTop (𝓝 (t.toReal / t.toReal)) :=
      tendsto_const_nhds.div htoReal htr
    rw [div_self htr] at hdiv
    simpa only [ENNReal.toReal_div] using hdiv
  exact OuterMeasure.WeaklyConverges.congr_seq hsmul_eq
    (hsub.smul_of_tendsto_one hetend hradon_smul)
/-! ## Theorem 14.3: existence of tangent measures -/
/-- **Mattila, Theorem 14.3.**
Let `μ` be a Radon outer measure on `ℝⁿ` and let `a ∈ spt μ` satisfy assumption (1),
`limsup_{ρ ↓ 0} μ (B (a, 2ρ)) / μ (B (a, ρ)) < ∞`. Then every sequence of radii `r i ↓ 0` has a
subsequence along which the normalized blow-ups `μ (B (a, r i))⁻¹ T_{a, r i #} μ` converge
weakly to a tangent measure of `μ` at `a`. -/
theorem exists_subseq_blowUp_weaklyConverges_tangentMeasure {n : ℕ}
    (μ : OuterMeasure (EuclideanSpace ℝ (Fin n))) (hμ : RadonOuterMeasure μ)
    (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ SupportOuterMeasure μ)
    (hc : limsup (fun ρ : ℝ ↦ μ (ball a (2 * ρ)) / μ (ball a ρ)) (𝓝[>] (0 : ℝ)) < ∞)
    (r : ℕ → ℝ) (hr_pos : ∀ i, 0 < r i) (hr : Tendsto r atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ) (ν : OuterMeasure (EuclideanSpace ℝ (Fin n)))
        (hseq : ∀ j, RadonOuterMeasure
          ((μ (ball a (r (φ j))))⁻¹ • OuterMeasure.map (blowUpMap a (r (φ j))) μ))
        (hν : RadonOuterMeasure ν),
      StrictMono φ ∧ IsTangentMeasure μ ν hμ a ∧
        OuterMeasure.WeaklyConverges
          (fun j ↦ (μ (ball a (r (φ j))))⁻¹ • OuterMeasure.map (blowUpMap a (r (φ j))) μ)
          ν hseq hν := by
  have hball_pos : ∀ i, μ (ball a (r i)) ≠ 0 := fun i ↦ (measure_ball_pos ha (hr_pos i)).ne'
  have hball_top : ∀ i, μ (ball a (r i)) ≠ ∞ := fun i ↦ (measure_ball_lt_top hμ a (r i)).ne
  set σ : ℕ → OuterMeasure (EuclideanSpace ℝ (Fin n)) :=
    fun i ↦ (μ (ball a (r i)))⁻¹ • OuterMeasure.map (blowUpMap a (r i)) μ
  have hσ : ∀ i, RadonOuterMeasure (σ i) := fun i ↦
    (hμ.map_blowUp a (hr_pos i).ne').smul (ENNReal.inv_ne_top.2 (hball_pos i))
  have hclosed : ∀ (i : ℕ) (s : ℝ), σ i (closedBall 0 s)
      = (μ (ball a (r i)))⁻¹ * μ (closedBall a (r i * s)) := by
    intro i s
    show ((μ (ball a (r i)))⁻¹ • OuterMeasure.map (blowUpMap a (r i)) μ) (closedBall 0 s) = _
    rw [OuterMeasure.smul_apply, smul_eq_mul, OuterMeasure.map_apply,
      blowUpMap_preimage_closedBall a (hr_pos i)]
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
        (measure_closedBall_lt_top hμ a _)).ne
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
  obtain ⟨φ, ν, hν_radon, hφ, hconv⟩ :=
    exists_vaguelyConvergent_subseq_of_compact_bounded σ hσ hbound
  have hν0 : ν ≠ 0 := by
    have hb := (OuterMeasure.weaklyConverges_iff_compactOpenBounds _ ν
      (fun j ↦ hσ (φ j)) hν_radon).mp hconv
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
  refine ⟨φ, ν, fun j ↦ hσ (φ j), hν_radon, hφ, ?_, hconv⟩
  exact ⟨hν_radon, hν0, fun j ↦ r (φ j), fun j ↦ (μ (ball a (r (φ j))))⁻¹,
    fun j ↦ hr_pos _, fun j ↦ ENNReal.inv_pos.2 (hball_top _),
    fun j ↦ ENNReal.inv_ne_top.2 (hball_pos _), hr.comp hφ.tendsto_atTop,
    fun j ↦ hσ (φ j), hconv⟩

import Mathlib

/- Necessary basic definitions -/

import Mathlib
import FormalizingGMT.«Project Versions».Measures.Basic
import FormalizingGMT.«Project Versions».Measures.HausdorffMeasure
import FormalizingGMT.«Project Versions».Densities.Basic
import FormalizingGMT.«Project Versions».Aux_definitions
import FormalizingGMT.«Project Versions».Thm1_25_VariantVitali

/- This file contains the upper bound in Theorem 2.7 in [EG]. -/

/-!
# Theorem 2.7, part II: the upper density bound

Let `X` be a σ-compact metric space, `s ≥ 0` and let `E ⊆ X` be measurable with respect to the
`s`-dimensional Hausdorff outer measure `H^s` (in the sense of Carathéodory), with `H^s(E) < ∞`.
Then for `H^s`-almost every `x ∈ E`,

  `limsup_{r ↘ 0} H^s(E ∩ B(x,r)) / (2r)^s ≤ 1`.

All balls occurring here are *closed* metric balls.

The proof follows the classical argument:

* `superlevelSet s E t` is the set `B_t` of points of `E` at which the upper density exceeds `t`;
* the restriction `H^s ⌞ E` is a Radon outer measure
  (`HausdorffRestrict.toRadonOuterMeasure`), so `B_t` can be approximated from outside by an
  open set `U`;
* the family `ballFamily` of closed balls contained in `U`, of radius `< δ`, on which the density
  exceeds `t`, is a fine cover of `B_t`, and the variant of Vitali's covering theorem
  (`vitali_variant_classical`) produces a countable disjoint subfamily whose `5`-fold enlargement
  (outside of any finite subfamily) still covers `B_t`;
* this yields covers of `B_t` of arbitrarily small mesh whose gauge sums are at most
  `t⁻¹ (H^s(B_t) + ε) + 5^s t⁻¹ ε`, whence `H^s(B_t) ≤ t⁻¹ H^s(B_t)` and so `H^s(B_t) = 0` for
  every `t > 1`;
* the exceptional set of the theorem is the countable union of the sets `B_{1 + 1/n}`.
-/


open scoped BigOperators Real Nat Pointwise ENNReal NNReal
open MeasureTheory MeasureTheory.OuterMeasure Metric Set Filter Topology

namespace HausdorffDensity

noncomputable section

variable {X : Type*} [MetricSpace X] [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-! ## Preliminaries on the Hausdorff measure and on closed balls -/

omit [SigmaCompactSpace X] in
/-- The Hausdorff measure, applied to an arbitrary (not necessarily measurable) set, agrees with
the Hausdorff outer measure `mkMetric (fun r => r ^ s)`; this is the Borel regularity of the
latter. -/
lemma hausdorffMeasure_eq_mkMetric (s : ℝ) (A : Set X) :
    μH[s] A = OuterMeasure.mkMetric (fun r => r ^ s) A := by
  rw [MeasureTheory.Measure.hausdorffMeasure, MeasureTheory.Measure.mkMetric]
  rw [show ((OuterMeasure.mkMetric (fun r => r ^ s) : OuterMeasure X).toMeasure (by
      rw [BorelSpace.measurable_eq (α := X)]
      exact (OuterMeasure.mkMetric'_isMetric _).borel_le_caratheodory) : Measure X) A
    = (OuterMeasure.mkMetric (fun r => r ^ s) : OuterMeasure X).trim A from rfl]
  rw [OuterMeasure.trim_mkMetric]

omit [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- A closed ball of radius `r` has diameter at most `2r`. -/
lemma ediam_closedBall_le (x : X) (r : ℝ) :
    Metric.ediam (Metric.closedBall x r) ≤ ENNReal.ofReal (2 * r) := by
  refine Metric.ediam_le_of_forall_dist_le ?_
  intro y hy z hz
  have hy' := Metric.mem_closedBall.mp hy
  have hz' := Metric.mem_closedBall.mp hz
  calc dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
    _ ≤ r + r := by rw [dist_comm x z]; linarith
    _ = 2 * r := by ring

/-! ## The sets `B_t` and the ball family `F` -/

/-- The super-level set of the upper `s`-density of `H^s ⌞ E`:
`B_t = {x ∈ E | limsup_{r → 0} H^s(B(x,r) ∩ E) / (2r)^s > t}`. -/
def superlevelSet (s : ℝ) (E : Set X) (t : ℝ≥0∞) : Set X :=
  {x ∈ E | t < dimensional_upper_density ((μH[s]).restrict E).toOuterMeasure s x}

/-- The family of closed balls `B(x,r) ⊆ U` with `0 < r < δ` on which the `s`-density
of `E` exceeds `t`; a ball is encoded by the pair `(x, r)` of its centre and radius. -/
def ballFamily (s : ℝ) (E U : Set X) (δ : ℝ) (t : ℝ≥0∞) : Set (X × ℝ) :=
  {a : X × ℝ | Metric.closedBall a.1 a.2 ⊆ U ∧ 0 < a.2 ∧ a.2 < δ ∧
    t * ENNReal.ofReal ((2 * a.2) ^ s) < μH[s] (E ∩ Metric.closedBall a.1 a.2)}

omit [SigmaCompactSpace X] in
lemma superlevelSet_subset (s : ℝ) (E : Set X) (t : ℝ≥0∞) : superlevelSet s E t ⊆ E :=
  fun _ hx => hx.1

omit [SigmaCompactSpace X] in
/-- The density ratio of the restricted Hausdorff measure is `H^s(B(x,r) ∩ E) / (2r)^s`. -/
lemma density_ratio_apply (s : ℝ) (E : Set X) (x : X) (r : ℝ) :
    dimensional_density_ratio ((μH[s]).restrict E).toOuterMeasure s x r
      = μH[s] (Metric.closedBall x r ∩ E) / ENNReal.ofReal ((2 * r) ^ s) := by
  rw [dimensional_density_ratio, Measure.toOuterMeasure_apply,
    Measure.restrict_apply Metric.isClosed_closedBall.measurableSet]

/-! ## Outer approximation coming from the Radon property -/

/-- Since `H^s ⌞ E` is a Radon outer measure, any subset `A` of `E`
is approximated from outside by open sets: for every `ε > 0` there is an open `U ⊇ A` with
`H^s(U ∩ E) < H^s(A) + ε`. -/
lemma exists_open_superset_measure_lt {s : ℝ} (hs : 0 ≤ s) {E : Set X}
    (hEmeas : MeasurableSet[(OuterMeasure.mkMetric (X := X) (fun r => r ^ s)).caratheodory] E)
    (hEfin : μH[s] E ≠ ⊤) (A : Set X) (hAE : A ⊆ E) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ μH[s] (U ∩ E) < μH[s] A + ε := by
  set Hs : OuterMeasure X := OuterMeasure.mkMetric (fun r => r ^ s) with hHs
  have hEfin' : Hs E < ∞ := by
    rw [hHs, ← hausdorffMeasure_eq_mkMetric]; exact lt_top_iff_ne_top.2 hEfin
  letI : RadonOuterMeasure (OuterMeasure.restrict E Hs) :=
    HausdorffRestrict.toRadonOuterMeasure s hs E hEmeas hEfin'
  set mu : OuterMeasure X := OuterMeasure.restrict E Hs with hmu
  have hcara : ‹MeasurableSpace X› ≤ mu.caratheodory :=
    BorelOuterMeasure.measurable_le_caratheodory (μ := mu)
  set m : Measure X := mu.toMeasure hcara with hm
  haveI : m.Regular := RadonOuterMeasure.regular_toMeasure (μ := mu)
  have hmuapp : ∀ S : Set X, mu S = Hs (S ∩ E) := by
    intro S; rw [hmu, OuterMeasure.restrict_apply]
  have hmA : m A ≤ μH[s] A := by
    obtain ⟨F, hAF, hFmeas, hFeq⟩ :=
      MeasureTheory.OuterMeasure.exists_measurable_superset_eq_trim Hs A
    calc m A ≤ m F := measure_mono hAF
      _ = mu F := by rw [hm, toMeasure_apply _ _ hFmeas]
      _ = Hs (F ∩ E) := hmuapp F
      _ ≤ Hs F := Hs.mono Set.inter_subset_left
      _ = Hs A := by rw [hFeq, hHs, OuterMeasure.trim_mkMetric]
      _ = μH[s] A := (hausdorffMeasure_eq_mkMetric s A).symm
  have hAfin : μH[s] A ≠ ⊤ := ne_top_of_le_ne_top hEfin (measure_mono hAE)
  obtain ⟨U, hAU, hUopen, hUlt⟩ := exists_isOpen_lt_of_lt (μ := m) A (μH[s] A + ε)
    (lt_of_le_of_lt hmA (ENNReal.lt_add_right hAfin hε))
  refine ⟨U, hUopen, hAU, ?_⟩
  calc μH[s] (U ∩ E) = Hs (U ∩ E) := hausdorffMeasure_eq_mkMetric s _
    _ = mu U := (hmuapp U).symm
    _ = m U := by rw [hm, toMeasure_apply _ _ hUopen.measurableSet]
    _ < μH[s] A + ε := hUlt

/-! ## Fineness of the ball family -/

omit [SigmaCompactSpace X] in
/-- The family `F` of balls is a *fine* cover of `B_t`: through every point of `B_t` there are
balls of `F` of arbitrarily small radius centred at that point. -/
lemma fine_ballFamily {s : ℝ} {E U : Set X} (hU : IsOpen U) {t : ℝ≥0∞} {δ : ℝ} (hδ : 0 < δ)
    (hBU : superlevelSet s E t ⊆ U) (x : X) (hx : x ∈ superlevelSet s E t) {η : ℝ} (hη : 0 < η) :
    ∃ a ∈ ballFamily s E U δ t, a.2 ≤ η ∧ a.1 = x := by
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.mp hU x (hBU hx)
  have hfreq : ∃ᶠ r in 𝓝[>] (0 : ℝ),
      t < dimensional_density_ratio ((μH[s]).restrict E).toOuterMeasure s x r :=
    frequently_gt_of_upper_density_gt _ s x t hx.2
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Set.Ioo 0 (min (min η δ) (r₀ / 2)) :=
    Ioo_mem_nhdsGT (by positivity)
  obtain ⟨r, hr1, hr2⟩ := (hfreq.and_eventually hev).exists
  have hrpos : 0 < r := hr2.1
  have hrη : r ≤ η := le_trans (le_of_lt hr2.2) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hrδ : r < δ := lt_of_lt_of_le hr2.2 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hrr₀ : r < r₀ := lt_of_lt_of_le hr2.2 (le_trans (min_le_right _ _) (by linarith))
  refine ⟨(x, r), ⟨?_, hrpos, hrδ, ?_⟩, hrη, rfl⟩
  · exact (Metric.closedBall_subset_ball hrr₀).trans hball
  · rw [density_ratio_apply] at hr1
    have hpos : (0 : ℝ) < (2 * r) ^ s := Real.rpow_pos_of_pos (by linarith) s
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by simpa using hpos))
      (Or.inl ENNReal.ofReal_ne_top)] at hr1
    simpa [Set.inter_comm] using hr1

/-! ## Choosing a finite subfamily carrying almost all of the mass -/

/-- Tails of a convergent sum in `ℝ≥0∞` are eventually small. -/
lemma exists_finset_tsum_compl_le {ι : Type*} (f : ι → ℝ≥0∞) (hf : ∑' i, f i ≠ ⊤)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ W : Finset ι, ∑' i : ((W : Set ι)ᶜ : Set ι), f i ≤ ε := by
  by_cases hle : ∑' i, f i ≤ ε
  · refine ⟨∅, le_trans ?_ hle⟩
    have := ENNReal.sum_add_tsum_compl (s := (∅ : Finset ι)) (f := f)
    simp only [Finset.sum_empty, zero_add] at this
    exact le_of_eq this
  · push_neg at hle
    have hsub : ∑' i, f i - ε < ∑' i, f i := ENNReal.sub_lt_self hf (by
      intro h; rw [h] at hle; exact absurd hle (by simp)) hε
    rw [ENNReal.tsum_eq_iSup_sum] at hsub
    obtain ⟨W, hW⟩ := lt_iSup_iff.mp hsub
    rw [← ENNReal.tsum_eq_iSup_sum] at hW
    refine ⟨W, ?_⟩
    have hsplit := ENNReal.sum_add_tsum_compl (s := W) (f := f)
    have hWfin : ∑ i ∈ W, f i ≠ ⊤ := by
      refine ne_top_of_le_ne_top hf ?_
      rw [← hsplit]; exact le_self_add
    have h1 : ∑' i, f i < ∑ i ∈ W, f i + ε :=
      (ENNReal.sub_lt_iff_lt_right (ne_top_of_lt hle) hle.le).mp hW
    rw [← hsplit] at h1
    exact le_of_lt ((ENNReal.add_lt_add_iff_left hWfin).mp h1)

/-! ## The covering estimate at scale `δ` -/

/-- For every `δ > 0` and `ε > 0` there is a countable cover of `B_t` by
sets of diameter at most `10 δ` whose gauge sum is at most
`t⁻¹ (H^s(B_t) + ε) + 5^s t⁻¹ ε`.

The cover is produced by applying the variant of Vitali's covering theorem
(`vitali_variant_classical`) to the fine family `ballFamily s E U δ t`, where `U` is an open set
containing `B_t` with `H^s(U ∩ E) < H^s(B_t) + ε`: one keeps the balls of a large finite
subfamily and the `5`-fold enlargements of the remaining ones. -/
lemma exists_cover_le {s : ℝ} (hs : 0 ≤ s) {E : Set X}
    (hEmeas : MeasurableSet[(OuterMeasure.mkMetric (X := X) (fun r => r ^ s)).caratheodory] E)
    (hEfin : μH[s] E ≠ ⊤) {t : ℝ≥0∞} (ht0 : t ≠ 0) (httop : t ≠ ⊤)
    {δ : ℝ} (hδ : 0 < δ) {ε : ℝ≥0∞} (hε0 : ε ≠ 0) :
    ∃ (u : Set (X × ℝ)) (C : X × ℝ → Set X), u.Countable ∧
      (∀ b ∈ u, Metric.ediam (C b) ≤ ENNReal.ofReal (10 * δ)) ∧
      superlevelSet s E t ⊆ ⋃ b ∈ u, C b ∧
      ∑' b : u, Metric.ediam (C ↑b) ^ s
        ≤ t⁻¹ * (μH[s] (superlevelSet s E t) + ε) + ENNReal.ofReal (5 ^ s) * t⁻¹ * ε := by
  classical
  set A := superlevelSet s E t with hA
  -- An open set `U ⊇ B_t` with `H^s(U ∩ E) < H^s(B_t) + ε`
  obtain ⟨U, hUopen, hAU, hUlt⟩ :=
    exists_open_superset_measure_lt hs hEmeas hEfin A (superlevelSet_subset s E t) hε0
  set T := ballFamily s E U δ t with hT
  -- **(g)** the variant of Vitali's covering theorem applied to the fine family `T`
  have hfine : ∀ x ∈ A, ∀ η > (0 : ℝ), ∃ a ∈ T, a.2 ≤ η ∧ a.1 = x :=
    fun x hx η hη => fine_ballFamily hUopen hδ hAU x hx hη
  have hrad : ∃ R, ∀ a ∈ T, a.2 ≤ R := ⟨δ, fun _ ha => le_of_lt ha.2.2.1⟩
  have hpos : ∀ a ∈ T, 0 < a.2 := fun _ ha => ha.2.1
  obtain ⟨u, hut, hucount, hudisj, hucov⟩ :=
    vitali_variant_classical (X := A) T Prod.fst Prod.snd hfine hrad hpos
  haveI : Countable ↥u := hucount.to_subtype
  -- the mass of `E` inside each selected ball
  set f : X × ℝ → ℝ≥0∞ := fun b => μH[s] (E ∩ Metric.closedBall b.1 b.2) with hf
  set nu : Measure X := (μH[s]).restrict E with hnu
  have hnuball : ∀ b : X × ℝ, nu (Metric.closedBall b.1 b.2) = f b := fun b => by
    rw [hnu, Measure.restrict_apply Metric.isClosed_closedBall.measurableSet, hf, Set.inter_comm]
  have hdisj' : Pairwise (Function.onFun Disjoint
      fun b : ↥u => Metric.closedBall (b : X × ℝ).1 (b : X × ℝ).2) :=
    fun b₁ b₂ hne => hudisj b₁.2 b₂.2 (fun h => hne (Subtype.ext h))
  -- **(i)** the total mass of the selected balls is finite, so a finite subfamily carries all
  -- but `ε` of it
  have htsum_le : ∑' b : ↥u, f ↑b ≤ μH[s] E := by
    have h1 : ∑' b : ↥u, f ↑b
        = nu (⋃ b : ↥u, Metric.closedBall (b : X × ℝ).1 (b : X × ℝ).2) := by
      rw [measure_iUnion hdisj' (fun _ => Metric.isClosed_closedBall.measurableSet)]
      exact tsum_congr fun b => (hnuball ↑b).symm
    rw [h1]
    calc nu (⋃ b : ↥u, Metric.closedBall (b : X × ℝ).1 (b : X × ℝ).2) ≤ nu Set.univ :=
          measure_mono (Set.subset_univ _)
      _ = μH[s] E := by rw [hnu, Measure.restrict_apply_univ]
  have htsum_fin : ∑' b : ↥u, f ↑b ≠ ⊤ := ne_top_of_le_ne_top hEfin htsum_le
  obtain ⟨W, hW⟩ := exists_finset_tsum_compl_le (fun b : ↥u => f ↑b) htsum_fin hε0
  set w : Finset (X × ℝ) := W.image Subtype.val with hw
  have hmemw : ∀ b : ↥u, ((↑b : X × ℝ) ∈ w) ↔ b ∈ W := by
    intro b
    rw [hw]
    constructor
    · intro h
      obtain ⟨c, hc, hcb⟩ := Finset.mem_image.mp h
      exact (Subtype.ext hcb : c = b) ▸ hc
    · intro h; exact Finset.mem_image.mpr ⟨b, h, rfl⟩
  have hwu : (w : Set (X × ℝ)) ⊆ u := by
    intro a ha
    rw [hw, Finset.coe_image] at ha
    obtain ⟨b, -, rfl⟩ := ha
    exact b.2
  have hwT : (w : Set (X × ℝ)) ⊆ T := hwu.trans hut
  -- the cover: the balls of the finite subfamily, and the `5`-fold enlargements of the others
  set C : X × ℝ → Set X := fun b =>
    if b ∈ w then Metric.closedBall b.1 b.2 else Metric.closedBall b.1 (5 * b.2) with hC
  have hballU : ∀ b ∈ u, Metric.closedBall (b : X × ℝ).1 (b : X × ℝ).2 ⊆ U :=
    fun b hb => (hut hb).1
  refine ⟨u, C, hucount, ?_, ?_, ?_⟩
  · -- diameters are at most `10 δ`
    intro b hb
    have hb2 : b.2 < δ := (hut hb).2.2.1
    have hb2pos : 0 < b.2 := (hut hb).2.1
    by_cases hbw : b ∈ w
    · rw [hC]
      simp only [if_pos hbw]
      exact le_trans (ediam_closedBall_le _ _) (ENNReal.ofReal_le_ofReal (by linarith))
    · rw [hC]
      simp only [if_neg hbw]
      refine le_trans (ediam_closedBall_le _ _) (ENNReal.ofReal_le_ofReal (by linarith))
  · -- the cover property, from the conclusion of Vitali's theorem
    intro x hx
    by_cases hcase : ∃ a ∈ w, x ∈ Metric.closedBall a.1 a.2
    · obtain ⟨a, haw, hxa⟩ := hcase
      refine Set.mem_biUnion (hwu haw) ?_
      rw [hC]; simpa only [if_pos haw] using hxa
    · push_neg at hcase
      have hxdiff : x ∈ A \ ⋃ a ∈ w, Metric.closedBall a.1 a.2 := by
        refine ⟨hx, ?_⟩
        simpa using hcase
      obtain ⟨b, hb, hxb⟩ := Set.mem_iUnion₂.mp (hucov w hwT hxdiff)
      have hbw : b ∉ w := fun h => hb.2 (Finset.mem_coe.mpr h)
      refine Set.mem_biUnion hb.1 ?_
      rw [hC]; simpa only [if_neg hbw] using hxb
  · -- **(h)** the gauge sum estimate
    have hbound : ∀ b : ↥u, Metric.ediam (C ↑b) ^ s ≤
        (if (↑b : X × ℝ) ∈ w then t⁻¹ * f ↑b
          else ENNReal.ofReal (5 ^ s) * (t⁻¹ * f ↑b)) := by
      intro b
      have hbT : (↑b : X × ℝ) ∈ T := hut b.2
      have hb2 : 0 < (↑b : X × ℝ).2 := hbT.2.1
      have hkey : ENNReal.ofReal ((2 * (↑b : X × ℝ).2) ^ s) ≤ t⁻¹ * f ↑b := by
        calc ENNReal.ofReal ((2 * (↑b : X × ℝ).2) ^ s)
            = t⁻¹ * (t * ENNReal.ofReal ((2 * (↑b : X × ℝ).2) ^ s)) := by
              rw [← mul_assoc, ENNReal.inv_mul_cancel ht0 httop, one_mul]
          _ ≤ t⁻¹ * f ↑b := by gcongr; exact hbT.2.2.2.le
      by_cases hbw : (↑b : X × ℝ) ∈ w
      · rw [hC]
        simp only [if_pos hbw]
        refine le_trans ?_ hkey
        calc Metric.ediam (Metric.closedBall (↑b : X × ℝ).1 (↑b : X × ℝ).2) ^ s
            ≤ ENNReal.ofReal (2 * (↑b : X × ℝ).2) ^ s :=
              ENNReal.rpow_le_rpow (ediam_closedBall_le _ _) hs
          _ = ENNReal.ofReal ((2 * (↑b : X × ℝ).2) ^ s) :=
              ENNReal.ofReal_rpow_of_nonneg (by positivity) hs
      · rw [hC]
        simp only [if_neg hbw]
        have h10 : (2 : ℝ) * (5 * (↑b : X × ℝ).2) = 5 * (2 * (↑b : X × ℝ).2) := by ring
        calc Metric.ediam (Metric.closedBall (↑b : X × ℝ).1 (5 * (↑b : X × ℝ).2)) ^ s
            ≤ ENNReal.ofReal (2 * (5 * (↑b : X × ℝ).2)) ^ s :=
              ENNReal.rpow_le_rpow (ediam_closedBall_le _ _) hs
          _ = ENNReal.ofReal ((5 * (2 * (↑b : X × ℝ).2)) ^ s) := by
              rw [h10, ENNReal.ofReal_rpow_of_nonneg (by positivity) hs]
          _ = ENNReal.ofReal (5 ^ s) * ENNReal.ofReal ((2 * (↑b : X × ℝ).2) ^ s) := by
              rw [Real.mul_rpow (by norm_num) (by positivity),
                ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) s)]
          _ ≤ ENNReal.ofReal (5 ^ s) * (t⁻¹ * f ↑b) := by gcongr
    have hfinite : ∑ b ∈ W, (if (↑b : X × ℝ) ∈ w then t⁻¹ * f ↑b
        else ENNReal.ofReal (5 ^ s) * (t⁻¹ * f ↑b)) ≤ t⁻¹ * μH[s] (U ∩ E) := by
      have h1 : ∑ b ∈ W, (if (↑b : X × ℝ) ∈ w then t⁻¹ * f ↑b
          else ENNReal.ofReal (5 ^ s) * (t⁻¹ * f ↑b)) = t⁻¹ * ∑ b ∈ W, f ↑b := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b hb => ?_
        rw [if_pos ((hmemw b).mpr hb)]
      rw [h1]
      have h2 : ∑ b ∈ W, f ↑b
          = nu (⋃ b ∈ W, Metric.closedBall (b : X × ℝ).1 (b : X × ℝ).2) := by
        rw [measure_biUnion_finset (fun b₁ hb₁ b₂ hb₂ hne => hdisj' hne)
          (fun _ _ => Metric.isClosed_closedBall.measurableSet)]
        exact Finset.sum_congr rfl fun b _ => (hnuball ↑b).symm
      rw [h2]
      have h3 : nu (⋃ b ∈ W, Metric.closedBall (b : X × ℝ).1 (b : X × ℝ).2) ≤ μH[s] (U ∩ E) := by
        have hsub : (⋃ b ∈ W, Metric.closedBall (b : X × ℝ).1 (b : X × ℝ).2) ⊆ U :=
          Set.iUnion₂_subset fun b _ => hballU _ b.2
        calc nu (⋃ b ∈ W, Metric.closedBall (b : X × ℝ).1 (b : X × ℝ).2)
            ≤ nu U := measure_mono hsub
          _ = μH[s] (U ∩ E) := by rw [hnu, Measure.restrict_apply hUopen.measurableSet]
      gcongr
    have htail : ∑' b : ((W : Set ↥u)ᶜ : Set ↥u),
        (if ((b : ↥u) : X × ℝ) ∈ w then t⁻¹ * f ↑(b : ↥u)
          else ENNReal.ofReal (5 ^ s) * (t⁻¹ * f ↑(b : ↥u)))
        ≤ ENNReal.ofReal (5 ^ s) * t⁻¹ * ε := by
      have h1 : ∀ b : ((W : Set ↥u)ᶜ : Set ↥u),
          (if ((b : ↥u) : X × ℝ) ∈ w then t⁻¹ * f ↑(b : ↥u)
            else ENNReal.ofReal (5 ^ s) * (t⁻¹ * f ↑(b : ↥u)))
          = ENNReal.ofReal (5 ^ s) * t⁻¹ * f ↑(b : ↥u) := by
        intro b
        have hb : ((b : ↥u) : X × ℝ) ∉ w := fun h => b.2 ((hmemw _).mp h)
        rw [if_neg hb, mul_assoc]
      rw [tsum_congr h1, ENNReal.tsum_mul_left]
      gcongr
    calc ∑' b : ↥u, Metric.ediam (C ↑b) ^ s
        ≤ ∑' b : ↥u, (if (↑b : X × ℝ) ∈ w then t⁻¹ * f ↑b
            else ENNReal.ofReal (5 ^ s) * (t⁻¹ * f ↑b)) := ENNReal.tsum_le_tsum hbound
      _ = ∑ b ∈ W, (if (↑b : X × ℝ) ∈ w then t⁻¹ * f ↑b
              else ENNReal.ofReal (5 ^ s) * (t⁻¹ * f ↑b))
            + ∑' b : ((W : Set ↥u)ᶜ : Set ↥u),
              (if ((b : ↥u) : X × ℝ) ∈ w then t⁻¹ * f ↑(b : ↥u)
                else ENNReal.ofReal (5 ^ s) * (t⁻¹ * f ↑(b : ↥u))) :=
          (ENNReal.sum_add_tsum_compl W _).symm
      _ ≤ t⁻¹ * μH[s] (U ∩ E) + ENNReal.ofReal (5 ^ s) * t⁻¹ * ε := add_le_add hfinite htail
      _ ≤ t⁻¹ * (μH[s] A + ε) + ENNReal.ofReal (5 ^ s) * t⁻¹ * ε := by gcongr

/-! ## The super-level sets are null -/

omit [SigmaCompactSpace X] in
/-- If `a ≤ c * a` with `c < 1` and `a ≠ ∞`, then `a = 0`. -/
lemma eq_zero_of_le_mul_self {a c : ℝ≥0∞} (hc : c < 1) (ha : a ≠ ⊤) (h : a ≤ c * a) : a = 0 := by
  by_contra h0
  have h1 : a * c < a * 1 := ENNReal.mul_lt_mul_right h0 ha hc
  rw [mul_one, mul_comm] at h1
  exact absurd (h.trans_lt h1) (lt_irrefl a)

/-- For every `t > 1` the set `B_t` is `H^s`-null. -/
theorem superlevelSet_null {s : ℝ} (hs : 0 ≤ s) {E : Set X}
    (hEmeas : MeasurableSet[(OuterMeasure.mkMetric (X := X) (fun r => r ^ s)).caratheodory] E)
    (hEfin : μH[s] E ≠ ⊤) {t : ℝ≥0∞} (ht : 1 < t) (httop : t ≠ ⊤) :
    μH[s] (superlevelSet s E t) = 0 := by
  set A := superlevelSet s E t with hA
  have hAE : A ⊆ E := superlevelSet_subset s E t
  have hAfin : μH[s] A ≠ ⊤ := ne_top_of_le_ne_top hEfin (measure_mono hAE)
  have ht0 : t ≠ 0 := (zero_lt_one.trans ht).ne'
  have htinv : t⁻¹ < 1 := ENNReal.inv_lt_one.mpr ht
  have htinv_top : t⁻¹ ≠ ⊤ := (lt_of_lt_of_le htinv le_top).ne
  -- For every `ε > 0`, `H^s(B_t) ≤ t⁻¹ (H^s(B_t) + ε) + 5^s t⁻¹ ε`; this comes from the
  -- covers of mesh `10/(n+1)` produced by `exists_cover_le`.
  have key : ∀ ε : ℝ≥0∞, ε ≠ 0 →
      μH[s] A ≤ t⁻¹ * (μH[s] A + ε) + ENNReal.ofReal (5 ^ s) * t⁻¹ * ε := by
    intro ε hε0
    choose u C hcount hdiam hcov hsum using
      fun n : ℕ => exists_cover_le hs hEmeas hEfin ht0 httop
        (δ := 1 / (n + 1 : ℝ)) (by positivity) hε0
    haveI : ∀ n : ℕ, Countable ↥(u n) := fun n => (hcount n).to_subtype
    have htend : Tendsto (fun n : ℕ => ENNReal.ofReal (10 * (1 / (n + 1 : ℝ)))) atTop (𝓝 0) := by
      have h : Tendsto (fun n : ℕ => 10 * (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (10 : ℝ)
      simpa using ENNReal.tendsto_ofReal h
    have hle := MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum (X := X) s A
      (fun n : ℕ => ENNReal.ofReal (10 * (1 / (n + 1 : ℝ)))) htend
      (fun n (i : ↥(u n)) => C n ↑i)
      (Eventually.of_forall (fun n i => hdiam n ↑i i.2))
      (Eventually.of_forall (fun n => by
        have h := hcov n
        rwa [Set.biUnion_eq_iUnion] at h))
    refine le_trans hle ?_
    refine le_trans (Filter.liminf_le_liminf (Eventually.of_forall (fun n => hsum n))) ?_
    simp [← hA]
  -- Letting `ε → 0` gives `H^s(B_t) ≤ t⁻¹ H^s(B_t)`.
  have h2 : μH[s] A ≤ t⁻¹ * μH[s] A := by
    set K : ℝ≥0∞ := t⁻¹ + ENNReal.ofReal (5 ^ s) * t⁻¹ with hK
    have hKtop : K ≠ ⊤ := by
      rw [hK]
      exact ENNReal.add_ne_top.mpr ⟨htinv_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top htinv_top⟩
    refine ENNReal.le_of_forall_pos_le_add ?_
    intro e he _
    set ee : ℝ≥0∞ := (e : ℝ≥0∞) / (K + 1) with hee
    have hK1 : K + 1 ≠ 0 := by positivity
    have hK1top : K + 1 ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hKtop, ENNReal.one_ne_top⟩
    have hee0 : ee ≠ 0 := by
      rw [hee]
      exact (ENNReal.div_ne_zero).mpr ⟨by exact_mod_cast he.ne', hK1top⟩
    have hkey := key ee hee0
    have hexp : t⁻¹ * (μH[s] A + ee) + ENNReal.ofReal (5 ^ s) * t⁻¹ * ee
        = t⁻¹ * μH[s] A + K * ee := by rw [hK]; ring
    rw [hexp] at hkey
    refine hkey.trans ?_
    have hfin : K * ee ≤ (e : ℝ≥0∞) :=
      calc K * ee ≤ (K + 1) * ee := by gcongr; exact le_self_add
        _ = (e : ℝ≥0∞) := by
            rw [hee]
            exact ENNReal.mul_div_cancel' (fun h => absurd h hK1) (fun h => absurd h hK1top)
    gcongr
  -- Since `H^s(B_t) < ∞` and `t⁻¹ < 1`, this forces `H^s(B_t) = 0`.
  exact eq_zero_of_le_mul_self htinv hAfin h2

/-! ## The main theorem -/

omit [SigmaCompactSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Every extended real number `> 1` exceeds `1 + 1/(n+1)` for some `n`. -/
lemma exists_nat_one_add_inv_lt {d : ℝ≥0∞} (hd : 1 < d) :
    ∃ n : ℕ, 1 + ((n : ℝ≥0∞) + 1)⁻¹ < d := by
  rcases eq_or_ne d ⊤ with rfl | hdtop
  · exact ⟨0, by norm_num⟩
  · have h1 : d - 1 ≠ 0 := by
      simp only [ne_eq, tsub_eq_zero_iff_le, not_le]
      exact hd
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt h1
    refine ⟨n, ?_⟩
    have h2 : ((n : ℝ≥0∞) + 1)⁻¹ ≤ (n : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.mpr le_self_add
    calc 1 + ((n : ℝ≥0∞) + 1)⁻¹ ≤ 1 + (n : ℝ≥0∞)⁻¹ := by gcongr
      _ < 1 + (d - 1) := ENNReal.add_lt_add_left ENNReal.one_ne_top hn
      _ = d := add_tsub_cancel_of_le hd.le

/-- Let `X` be a σ-compact metric space, `s ≥ 0`,
and let `E ⊆ X` be measurable with respect to the `s`-dimensional Hausdorff outer measure
(in the sense of Carathéodory), with `H^s(E) < ∞`. Then for `H^s`-almost every `x ∈ E`,

  `limsup_{r ↘ 0} H^s(E ∩ B(x,r)) / (2r)^s ≤ 1`,

that is, the set of points of `E` where the upper `s`-density of `H^s ⌞ E` exceeds `1` is
`H^s`-null. -/
theorem upperDensity_le_one {s : ℝ} (hs : 0 ≤ s) (E : Set X)
    (hEmeas : MeasurableSet[(OuterMeasure.mkMetric (X := X) (fun r => r ^ s)).caratheodory] E)
    (hEfin : μH[s] E ≠ ⊤) :
    μH[s] {x ∈ E | 1 < dimensional_upper_density ((μH[s]).restrict E).toOuterMeasure s x} = 0 := by
  -- Each `B_{1 + 1/(n+1)}` is null, hence so is their union.
  have hnull : ∀ n : ℕ, μH[s] (superlevelSet s E (1 + ((n : ℝ≥0∞) + 1)⁻¹)) = 0 := by
    intro n
    refine superlevelSet_null hs hEmeas hEfin ?_ ?_
    · exact ENNReal.lt_add_right ENNReal.one_ne_top (ENNReal.inv_ne_zero.mpr (by simp))
    · exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ENNReal.inv_ne_top.mpr (by positivity)⟩
  -- **(n)** The exceptional set is contained in that union.
  refine measure_mono_null ?_ (measure_iUnion_null hnull)
  rintro x ⟨hxE, hx⟩
  obtain ⟨n, hn⟩ := exists_nat_one_add_inv_lt hx
  exact Set.mem_iUnion.mpr ⟨n, hxE, hn⟩

end

end HausdorffDensity

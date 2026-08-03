import Mathlib

import FormalizingGMT.«Project Versions».Measures.Basic
import FormalizingGMT.«Project Versions».Measures.Thm1_7
import FormalizingGMT.«Project Versions».Densities.Basic
import FormalizingGMT.«Project Versions».Aux_definitions

open scoped BigOperators Real Nat Classical Pointwise
open MeasureTheory MeasureTheory.OuterMeasure Set
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option grind.warning false
/-!
## Hausdorff content
-/
/-- The `s`-dimensional **Hausdorff content** of a set `E` with covers of diameter ≤ `δ`.
Empty members of a cover contribute zero to the sum. -/
noncomputable def hausdorffContent
    {X : Type*} [EMetricSpace X] (s : ℝ) (δ : ENNReal) (E : Set X) : ENNReal :=
  ⨅ (t : ℕ → Set X) (_ : E ⊆ ⋃ i, t i) (_ : ∀ i, Metric.ediam (t i) ≤ δ),
    ∑' i, ⨆ (_ : (t i).Nonempty), (Metric.ediam (t i)) ^ s

/-- Unrestricted Hausdorff content `H^s_∞(E)`: infimum over all countable covers,
with no diameter bound. Empty members of a cover contribute zero to the sum. -/
noncomputable def hausdorffContentInfty
    {X : Type*} [EMetricSpace X] (s : ℝ) (E : Set X) : ENNReal :=
  ⨅ (t : ℕ → Set X) (_ : E ⊆ ⋃ i, t i),
    ∑' i, ⨆ (_ : (t i).Nonempty), (Metric.ediam (t i)) ^ s

/-- The notion of `s-set` as described in Falconer's textbook: a set `E` has positive, finite
`s`-dimensional Hausdorff measure and is Carathéodory-measurable with respect to the
`s`-dimensional Hausdorff outer measure. -/
def HasPositiveFiniteHausdorff
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (s : ℝ) (E : Set X) : Prop :=
  MeasurableSet[(OuterMeasure.mkMetric (X := X) (fun r => r ^ s)).caratheodory] E ∧
    0 < MeasureTheory.Measure.hausdorffMeasure s E ∧
    MeasureTheory.Measure.hausdorffMeasure s E < ⊤
/-!
## Hausdorff measure is Borel regular
-/
/-- The `s`-dimensional Hausdorff outer measure on an `EMetricSpace` is Borel regular for any
`s ≥ 0`. That is:
1. All Borel sets are Carathéodory measurable (this follows from the Hausdorff outer measure
   being a *metric* outer measure).
2. For every set `E`, there exists a Borel set `F ⊇ E` with the same outer measure (this
   follows from `OuterMeasure.trim_mkMetric`, which shows that `mkMetric m` is its own trim).
Note: condition (2) actually holds for *all* `mkMetric m` without the `0 ≤ s` hypothesis,
but we retain it to match the standard measure-theoretic statement; it is therefore not needed
by the proof. -/
instance Hausdorff.toBorelRegularOuterMeasure {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (s : ℝ) (hs : 0 ≤ s) :
    BorelRegularOuterMeasure (MeasureTheory.OuterMeasure.mkMetric (X := X) (fun r => r ^ s)) := by
  refine { measurable_le_caratheodory := ?_, exists_measurable_superset := ?_ }
  · -- Property 1: Borel sets are Carathéodory measurable for any metric outer measure
    have : ‹MeasurableSpace X› = borel X := BorelSpace.measurable_eq
    rw [this]
    exact (MeasureTheory.OuterMeasure.mkMetric'_isMetric _).borel_le_caratheodory
  · -- Property 2: For every set E, there exists a Borel superset F with μ(E) = μ(F)
    intro E
    obtain ⟨F, hEF, hF_meas, hF_eq⟩ :=
      MeasureTheory.OuterMeasure.exists_measurable_superset_eq_trim
        (MeasureTheory.OuterMeasure.mkMetric (X := X) (fun r => r ^ s)) E
    exact ⟨F, hF_meas, hEF, by rw [hF_eq, MeasureTheory.OuterMeasure.trim_mkMetric]⟩


/-- If `s ≥ 0` is finite, the restriction of the `s`-dimensional Hausdorff outer measure to a
Carathéodory-measurable set of finite measure is a Radon measure.
This combines `hausdorff_isBorelRegular` (the Hausdorff outer measure is Borel regular)
with `BorelRegularOuterMeasure.restrict_isRadon` (restricting a Borel regular outer measure to a
finite measurable set yields a Radon outer measure). -/
instance HausdorffRestrict.toRadonOuterMeasure
    {X : Type*} [MetricSpace X] [SigmaCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (s : ℝ) (hs : 0 ≤ s) (E : Set X)
    (hE_meas : MeasurableSet[
      (OuterMeasure.mkMetric (X := X) (fun r => r ^ s)).caratheodory] E)
    (hE_fin : (OuterMeasure.mkMetric (X := X) (fun r => r ^ s)) E < ⊤) :
    RadonOuterMeasure (OuterMeasure.restrict E (OuterMeasure.mkMetric (X := X) (fun r => r ^ s))) := by
  letI : BorelRegularOuterMeasure
      (OuterMeasure.mkMetric (X := X) (fun r => r ^ s)) :=
    Hausdorff.toBorelRegularOuterMeasure s hs
  exact BorelRegularOuterMeasure.restrict_isRadon _ E hE_meas hE_fin



/- **TODO:** everything below here should be reviewed for accuracy -/
  /-!
## Restricting the diameter bound to `≥ diam E` does not change the content

If `E` has diameter `≤ δ`, then the `δ`-restricted Hausdorff content of `E` agrees with the
unrestricted Hausdorff content `H^s_∞(E)`.  This is the standard fact that the Hausdorff content
`H^s_δ` stabilises once `δ` exceeds the diameter of the set being measured.
-/

/-- For a strictly positive exponent, the `Nonempty`-guarded summand used in `hausdorffContent`
coincides with the plain summand used in `hausdorffContentInfty`: the only place they could
differ is on the empty set, where both are `0` when `s > 0`. -/
lemma hausdorffContent_summand_eq {X : Type*} [EMetricSpace X] {s : ℝ} (hs : 0 < s)
    (U : Set X) :
    (⨆ (_ : U.Nonempty), (Metric.ediam U) ^ s) = (Metric.ediam U) ^ s := by
  by_cases h : U.Nonempty
  · rw [iSup_pos h]
  · rw [Set.not_nonempty_iff_eq_empty] at h
    rw [iSup_neg (by simp [h]), h, Metric.ediam_empty, ENNReal.zero_rpow_of_pos hs,
      ENNReal.bot_eq_zero]

/-- The unrestricted Hausdorff content is at most the `δ`-restricted content, because dropping
the diameter constraint enlarges the family of admissible covers. -/
lemma hausdorffContentInfty_le_hausdorffContent {X : Type*} [EMetricSpace X]
    (s : ℝ) (δ : ENNReal) (E : Set X) :
    hausdorffContentInfty s E ≤ hausdorffContent s δ E := by
  unfold hausdorffContent hausdorffContentInfty
  refine le_iInf fun t => le_iInf fun hcov => le_iInf fun _ => ?_
  exact iInf₂_le t hcov

/-- The `δ`-restricted Hausdorff content is at most the unrestricted content, provided `E` has
diameter at most `δ`. Given any cover `t` of `E`, intersect each `t i` with `E`: this shrinks each
diameter to at most `ediam E ≤ δ`, producing an admissible restricted cover with no larger sum. -/
lemma hausdorffContent_le_hausdorffContentInfty {X : Type*} [EMetricSpace X] {s : ℝ}
    (hs : 0 ≤ s) {δ : ENNReal} {E : Set X} (hE : Metric.ediam E ≤ δ) :
    hausdorffContent s δ E ≤ hausdorffContentInfty s E := by
  unfold hausdorffContent hausdorffContentInfty
  refine le_iInf fun t => le_iInf fun hcov => ?_
  set t' : ℕ → Set X := fun i => t i ∩ E with ht'
  have hcov' : E ⊆ ⋃ i, t' i := by
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcov hx)
    exact Set.mem_iUnion.mpr ⟨i, hxi, hx⟩
  have hdiam' : ∀ i, Metric.ediam (t' i) ≤ δ := by
    intro i
    exact le_trans (Metric.ediam_mono (by simp [ht', Set.inter_subset_right])) hE
  refine le_trans (iInf₂_le t' hcov') ?_
  refine le_trans (iInf_le _ hdiam') ?_
  refine ENNReal.tsum_le_tsum fun i => ?_
  apply iSup_le
  intro hti
  have hti' : (t i).Nonempty := hti.mono (by simp [ht', Set.inter_subset_left])
  refine le_iSup_of_le hti' ?_
  exact ENNReal.rpow_le_rpow
    (Metric.ediam_mono (by simp [ht', Set.inter_subset_left])) hs

/-- **Stabilisation of the Hausdorff content.** If `E` has `ediam E ≤ δ` and `s ≥ 0`, then its
`δ`-restricted Hausdorff content equals its unrestricted Hausdorff content. The hypothesis
`0 < δ` is retained in the standard positive-scale statement, though the proof does not need it. -/
theorem hausdorffContent_eq_hausdorffContentInfty_of_ediam_le {X : Type*} [EMetricSpace X]
    {s : ℝ} (hs : 0 ≤ s) {δ : ENNReal} (hδ : 0 < δ) {E : Set X} (hE : Metric.ediam E ≤ δ) :
    hausdorffContent s δ E = hausdorffContentInfty s E :=
  le_antisymm (hausdorffContent_le_hausdorffContentInfty hs hE)
    (hausdorffContentInfty_le_hausdorffContent s δ E)

/-!
## Hausdorff content is dominated by the Hausdorff measure
-/

/-- The `δ`-approximating Hausdorff content is at most the full Hausdorff measure:
    `H^s_δ(E) ≤ H^s(E)` for any diameter bound `δ > 0`. This holds because the Hausdorff
    measure is the supremum over all `r > 0` of the `r`-restricted contents
    (`MeasureTheory.Measure.hausdorffMeasure_apply`), and `hausdorffContent s δ` is exactly the
    term of that supremum at `r = δ`. -/
lemma hausdorffContent_le_hausdorffMeasure {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {s : ℝ} {δ : ENNReal} (hδ : 0 < δ) (E : Set X) :
    hausdorffContent s δ E ≤ MeasureTheory.Measure.hausdorffMeasure s E := by
  rw [MeasureTheory.Measure.hausdorffMeasure_apply]
  exact le_iSup₂_of_le δ hδ le_rfl

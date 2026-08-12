import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic

/- Necessary basic definitions -/
import FormalizingGMT.«Project Versions».Measures.Basic
import FormalizingGMT.«Project Versions».Measures.HausdorffMeasure
import FormalizingGMT.«Project Versions».Densities.Basic
import FormalizingGMT.«Project Versions».Aux_definitions




/-!
# Theorem 2.7, part I: the lower density bound

Let `X` be a σ-compact metric space, `s ≥ 0`, and let `E ⊆ X` be measurable with respect to the
`s`-dimensional Hausdorff outer measure `H^s`, with `H^s(E) < ∞`.  Then for `H^s`-almost every
`x ∈ E`,

  `limsup_{r ↘ 0} H^s_∞(E ∩ B(x,r)) / (2r)^s ≥ 1 / 2^s`,

and consequently the same holds with `H^s` in place of `H^s_∞`.

All balls occurring here are *closed* metric balls.
-/

open scoped BigOperators Real Nat Classical Pointwise ENNReal
open MeasureTheory MeasureTheory.OuterMeasure Set Filter Topology

noncomputable section

/-! ## The Hausdorff contents as outer measures

Both Hausdorff contents defined in `HausdorffMeasure.lean` are outer measures; we record this by
identifying them with `MeasureTheory.OuterMeasure.mkMetric'.pre` and
`MeasureTheory.OuterMeasure.boundedBy` respectively.  This gives us monotonicity and countable
subadditivity for free. -/

section Contents

variable {X : Type*} [EMetricSpace X]

/-- The `δ`-restricted Hausdorff content, packaged as an outer measure. -/
noncomputable def hausdorffContentOuter (s : ℝ) (δ : ℝ≥0∞) : OuterMeasure X :=
  OuterMeasure.mkMetric'.pre (fun t => (Metric.ediam t) ^ s) δ

/-- The unrestricted Hausdorff content `H^s_∞`, packaged as an outer measure. -/
noncomputable def hausdorffContentInftyOuter (s : ℝ) : OuterMeasure X :=
  OuterMeasure.boundedBy (fun t => (Metric.ediam t) ^ s)

/-- `hausdorffContentOuter` computes the `δ`-restricted Hausdorff content. -/
lemma hausdorffContentOuter_apply (s : ℝ) (δ : ℝ≥0∞) (E : Set X) :
    hausdorffContentOuter s δ E = hausdorffContent s δ E := by
  rw [hausdorffContentOuter, mkMetric'.pre, boundedBy_apply, hausdorffContent]
  refine le_antisymm ?_ ?_
  · refine le_iInf fun t => le_iInf fun hcov => le_iInf fun hd => ?_
    refine le_trans (iInf₂_le t hcov) (le_of_eq ?_)
    refine tsum_congr fun n => ?_
    rw [MeasureTheory.extend_eq (fun (u : Set X) (_ : Metric.ediam u ≤ δ) => (Metric.ediam u) ^ s)
      (hd n)]
  · refine le_iInf fun t => le_iInf fun hcov => ?_
    by_cases hd : ∀ i, Metric.ediam (t i) ≤ δ
    · refine le_trans (iInf₂_le t hcov) ?_
      refine le_trans (iInf_le _ hd) (le_of_eq ?_)
      refine tsum_congr fun n => ?_
      rw [MeasureTheory.extend_eq (fun (u : Set X) (_ : Metric.ediam u ≤ δ) => (Metric.ediam u) ^ s)
        (hd n)]
    · push_neg at hd
      obtain ⟨i, hi⟩ := hd
      have hi' : ¬ (Metric.ediam (t i) ≤ δ) := not_le.mpr hi
      have hne : (t i).Nonempty := by
        rcases Set.eq_empty_or_nonempty (t i) with h | h
        · exact absurd (h ▸ (by simp : Metric.ediam (∅ : Set X) ≤ δ)) hi'
        · exact h
      have hterm : (⨆ (_ : (t i).Nonempty), MeasureTheory.extend
          (fun (u : Set X) (_ : Metric.ediam u ≤ δ) => (Metric.ediam u) ^ s) (t i)) = ⊤ := by
        rw [iSup_pos hne, MeasureTheory.extend_eq_top
          (fun (u : Set X) (_ : Metric.ediam u ≤ δ) => (Metric.ediam u) ^ s) hi']
      have hle := ENNReal.le_tsum (f := fun n => ⨆ (_ : (t n).Nonempty), MeasureTheory.extend
          (fun (u : Set X) (_ : Metric.ediam u ≤ δ) => (Metric.ediam u) ^ s) (t n)) i
      rw [hterm, top_le_iff] at hle
      rw [hle]
      exact le_top

/-- `hausdorffContentInftyOuter` computes the unrestricted Hausdorff content. -/
lemma hausdorffContentInftyOuter_apply (s : ℝ) (E : Set X) :
    hausdorffContentInftyOuter s E = hausdorffContentInfty s E := by
  rw [hausdorffContentInftyOuter, boundedBy_apply, hausdorffContentInfty]

/-- Monotonicity of the `δ`-restricted Hausdorff content. -/
lemma hausdorffContent_mono {s : ℝ} {δ : ℝ≥0∞} {A B : Set X} (h : A ⊆ B) :
    hausdorffContent s δ A ≤ hausdorffContent s δ B := by
  rw [← hausdorffContentOuter_apply, ← hausdorffContentOuter_apply]
  exact measure_mono h

/-- Monotonicity of the unrestricted Hausdorff content. -/
lemma hausdorffContentInfty_mono {s : ℝ} {A B : Set X} (h : A ⊆ B) :
    hausdorffContentInfty s A ≤ hausdorffContentInfty s B := by
  rw [← hausdorffContentInftyOuter_apply, ← hausdorffContentInftyOuter_apply]
  exact measure_mono h

/-- Countable subadditivity of the `δ`-restricted Hausdorff content. -/
lemma hausdorffContent_iUnion_le {s : ℝ} {δ : ℝ≥0∞} (A : ℕ → Set X) :
    hausdorffContent s δ (⋃ i, A i) ≤ ∑' i, hausdorffContent s δ (A i) := by
  simp only [← hausdorffContentOuter_apply]
  exact measure_iUnion_le A

/-- The `δ`-restricted Hausdorff content of the empty set vanishes. -/
lemma hausdorffContent_empty (s : ℝ) (δ : ℝ≥0∞) :
    hausdorffContent s δ (∅ : Set X) = 0 := by
  rw [hausdorffContent]
  refine le_antisymm ?_ (by exact zero_le)
  refine le_trans (iInf₂_le (fun _ => (∅ : Set X)) (by simp)) ?_
  exact le_trans (iInf_le _ (by simp)) (by simp)

/-- The `δ`-restricted Hausdorff content is antitone in `δ`. -/
lemma hausdorffContent_antitone {s : ℝ} {δ δ' : ℝ≥0∞} (h : δ ≤ δ') (A : Set X) :
    hausdorffContent s δ' A ≤ hausdorffContent s δ A := by
  rw [hausdorffContent, hausdorffContent]
  refine le_iInf fun t => le_iInf fun hcov => le_iInf fun hd => ?_
  exact le_trans (iInf₂_le t hcov) (iInf_le _ (fun i => (hd i).trans h))

/-- For a positive exponent, a set of vanishing diameter has vanishing Hausdorff content. -/
lemma hausdorffContentInfty_eq_zero_of_ediam_eq_zero {s : ℝ} (hs : 0 < s) {A : Set X}
    (hA : Metric.ediam A = 0) : hausdorffContentInfty s A = 0 := by
  refine le_antisymm ?_ ?_
  · rw [hausdorffContentInfty]
    refine le_trans (iInf₂_le (fun _ => A) (Set.subset_iUnion (fun _ : ℕ => A) 0)) ?_
    simp [hA, ENNReal.zero_rpow_of_pos hs]
  · exact zero_le

end Contents

/-! ## The sets `E(δ, τ)` -/

section CoverSet

variable {X : Type*} [EMetricSpace X]

/-- `cover_set s E δ τ` is the set `E(δ, τ)` of Evans–Gariepy: the set of points `x ∈ E` such that
`H^s_δ(C ∩ E) ≤ τ (diam C)^s` whenever `C ⊆ X` contains `x` and has `diam C ≤ δ`. -/
private def cover_set (s : ℝ) (E : Set X) (δ τ : ℝ≥0∞) : Set X :=
  {x | x ∈ E ∧ ∀ C : Set X, x ∈ C → Metric.ediam C ≤ δ →
    hausdorffContent s δ (C ∩ E) ≤ τ * (Metric.ediam C) ^ s}

lemma cover_set_subset (s : ℝ) (E : Set X) (δ τ : ℝ≥0∞) : cover_set s E δ τ ⊆ E :=
  fun _ hx => hx.1

/-- `E(δ, τ)` is monotone in `τ`. -/
lemma cover_set_mono_tau (s : ℝ) (E : Set X) (δ : ℝ≥0∞) {τ τ' : ℝ≥0∞} (h : τ ≤ τ') :
    cover_set s E δ τ ⊆ cover_set s E δ τ' :=
  fun _ hx => ⟨hx.1, fun C hC hCd => (hx.2 C hC hCd).trans (by gcongr)⟩

/-- Equation (0.5): if `0 < δ ≤ δ'` then `E(δ', 1 - δ') ⊆ E(δ, 1 - δ)`.

Note that the two sets are defined through *different* Hausdorff contents, `H^s_δ` and `H^s_{δ'}`.
They agree on the relevant sets `C ∩ E`, whose diameter is at most `δ ≤ δ'`, by the stabilisation
lemma `hausdorffContent_eq_hausdorffContentInfty_of_ediam_le`. -/
lemma cover_set_mono_delta {s : ℝ} (hs : 0 ≤ s) (E : Set X) {δ δ' : ℝ≥0∞}
    (hδ : 0 < δ) (hδδ' : δ ≤ δ') :
    cover_set s E δ' (1 - δ') ⊆ cover_set s E δ (1 - δ) := by
  rintro x ⟨hxE, hx⟩
  refine ⟨hxE, fun C hxC hCd => ?_⟩
  have hCE : Metric.ediam (C ∩ E) ≤ δ := le_trans (Metric.ediam_mono Set.inter_subset_left) hCd
  have h1 : hausdorffContent s δ (C ∩ E) = hausdorffContentInfty s (C ∩ E) :=
    hausdorffContent_eq_hausdorffContentInfty_of_ediam_le hs hδ hCE
  have h2 : hausdorffContent s δ' (C ∩ E) = hausdorffContentInfty s (C ∩ E) :=
    hausdorffContent_eq_hausdorffContentInfty_of_ediam_le hs (lt_of_lt_of_le hδ hδδ')
      (hCE.trans hδδ')
  rw [h1, ← h2]
  refine (hx C hxC (hCd.trans hδδ')).trans ?_
  gcongr

/-- **Lemma 0.1 (covering estimate for `E(δ, τ)`).** General form: no nonemptiness assumption on
the pieces of the cover is needed. -/
lemma hausdorffContent_cover_set_le_tsum {s : ℝ} (E : Set X) {δ τ : ℝ≥0∞}
    (C : ℕ → Set X) (h_cover : cover_set s E δ τ ⊆ ⋃ i, C i)
    (h_diam : ∀ i, Metric.ediam (C i) ≤ δ) :
    hausdorffContent s δ (cover_set s E δ τ) ≤ τ * ∑' i, (Metric.ediam (C i)) ^ s := by
  set A := cover_set s E δ τ
  have h1 : A ⊆ ⋃ i, (C i ∩ A) := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (h_cover hx)
    exact Set.mem_iUnion.mpr ⟨i, hi, hx⟩
  have hterm : ∀ i, hausdorffContent s δ (C i ∩ A) ≤ τ * (Metric.ediam (C i)) ^ s := by
    intro i
    rcases Set.eq_empty_or_nonempty (C i ∩ A) with h | ⟨x, hxC, hxA⟩
    · rw [h, hausdorffContent_empty]
      exact zero_le
    · exact le_trans (hausdorffContent_mono
        (Set.inter_subset_inter_right _ (cover_set_subset s E δ τ))) (hxA.2 (C i) hxC (h_diam i))
  calc hausdorffContent s δ A ≤ hausdorffContent s δ (⋃ i, C i ∩ A) := hausdorffContent_mono h1
    _ ≤ ∑' i, hausdorffContent s δ (C i ∩ A) := hausdorffContent_iUnion_le _
    _ ≤ ∑' i, τ * (Metric.ediam (C i)) ^ s := ENNReal.tsum_le_tsum hterm
    _ = τ * ∑' i, (Metric.ediam (C i)) ^ s := ENNReal.tsum_mul_left

/-- **Lemma 0.1 (covering estimate for `E(δ, τ)`)**, in the exact form stated in the source: the
extra hypothesis that every piece of the cover meets `E(δ, τ)` is retained, although the proof
does not need it. -/
lemma hausdorffContent_cover_set_le_tsum' {s : ℝ} (E : Set X) {δ τ : ℝ≥0∞}
    (C : ℕ → Set X) (h_cover : cover_set s E δ τ ⊆ ⋃ i, C i)
    (h_diam : ∀ i, Metric.ediam (C i) ≤ δ)
    (h_meets : ∀ i, (C i ∩ cover_set s E δ τ).Nonempty) :
    hausdorffContent s δ (cover_set s E δ τ) ≤ τ * ∑' i, (Metric.ediam (C i)) ^ s :=
  hausdorffContent_cover_set_le_tsum E C h_cover h_diam

/-- **Lemma 0.2 (contraction).** `H^s_δ(E(δ,τ)) ≤ τ · H^s_δ(E(δ,τ))`. -/
lemma hausdorffContent_cover_set_contraction {s : ℝ} (hs : 0 < s) (E : Set X) {δ τ : ℝ≥0∞}
    (hτ : τ ≠ 0) (hτ' : τ ≠ ⊤) :
    hausdorffContent s δ (cover_set s E δ τ)
      ≤ τ * hausdorffContent s δ (cover_set s E δ τ) := by
  rw [mul_comm, ← ENNReal.div_le_iff_le_mul (Or.inl hτ) (Or.inl hτ'), hausdorffContent]
  refine le_iInf fun t => le_iInf fun hcov => le_iInf fun hd => ?_
  rw [ENNReal.div_le_iff_le_mul (Or.inl hτ) (Or.inl hτ'), mul_comm]
  refine (hausdorffContent_cover_set_le_tsum E t hcov hd).trans (le_of_eq ?_)
  congr 1
  exact tsum_congr fun i => (hausdorffContent_summand_eq hs _).symm

end CoverSet

/-! ## Vanishing of `H^s(E(δ, τ))` -/

section Vanishing

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Lemma 0.3 (vanishing `H^s_δ`).** If `H^s(E) < ∞` then `H^s_δ(E(δ,τ)) = 0`. -/
lemma hausdorffContent_cover_set_eq_zero {s : ℝ} (hs : 0 < s) (E : Set X) {δ τ : ℝ≥0∞}
    (hδ : 0 < δ) (hτ : τ ≠ 0) (hτ1 : τ < 1) (hE : μH[s] E ≠ ⊤) :
    hausdorffContent s δ (cover_set s E δ τ) = 0 := by
  have hfin : hausdorffContent s δ (cover_set s E δ τ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hE ?_
    exact (hausdorffContent_mono (cover_set_subset s E δ τ)).trans
      (hausdorffContent_le_hausdorffMeasure hδ E)
  have hcon := hausdorffContent_cover_set_contraction (δ := δ) hs E hτ (ne_top_of_lt hτ1)
  by_contra h0
  have h1 : (1 : ℝ≥0∞) * hausdorffContent s δ (cover_set s E δ τ)
      ≤ τ * hausdorffContent s δ (cover_set s E δ τ) := by rwa [one_mul]
  exact absurd ((ENNReal.mul_le_mul_iff_left h0 hfin).mp h1) (not_le.mpr hτ1)

omit [MeasurableSpace X] [BorelSpace X] in
/-- If the `δ`-restricted content of `A` vanishes for one `δ`, it vanishes for every `δ' > 0`.

(The positivity of `δ'` is essential: `H^s_0` only admits covers by singletons, so it may well be
infinite for a set of vanishing `s`-dimensional Hausdorff measure.) -/
lemma hausdorffContent_eq_zero_of_hausdorffContent_eq_zero {s : ℝ} (hs : 0 < s) {δ δ' : ℝ≥0∞}
    (hδ' : 0 < δ') {A : Set X} (h : hausdorffContent s δ A = 0) :
    hausdorffContent s δ' A = 0 := by
  rcases le_or_gt δ δ' with hle | hlt
  · exact le_antisymm (le_trans (hausdorffContent_antitone hle A) h.le) (zero_le)
  by_contra hne
  have hpos : 0 < hausdorffContent s δ' A := pos_iff_ne_zero.mpr hne
  have hδ'top : δ' ≠ ⊤ := (hlt.trans_le le_top).ne
  set η := min (hausdorffContent s δ' A) (δ' ^ s) with hη
  have hηpos : 0 < η := lt_min hpos (ENNReal.rpow_pos hδ' hδ'top)
  have hlt2 : hausdorffContent s δ A < η := h ▸ hηpos
  rw [hausdorffContent] at hlt2
  obtain ⟨t, ht⟩ := iInf_lt_iff.mp hlt2
  obtain ⟨hcov, ht2⟩ := iInf_lt_iff.mp ht
  obtain ⟨hd, ht3⟩ := iInf_lt_iff.mp ht2
  have hd' : ∀ i, Metric.ediam (t i) ≤ δ' := by
    intro i
    rcases Set.eq_empty_or_nonempty (t i) with he | hne'
    · simp [he]
    · have h1 : (Metric.ediam (t i)) ^ s
          ≤ ∑' n, ⨆ (_ : (t n).Nonempty), (Metric.ediam (t n)) ^ s := by
        refine le_trans (le_of_eq ?_) (ENNReal.le_tsum i)
        rw [iSup_pos hne']
      have h2 : (Metric.ediam (t i)) ^ s < δ' ^ s :=
        lt_of_le_of_lt h1 (ht3.trans_le (min_le_right _ _))
      exact le_of_lt ((ENNReal.rpow_lt_rpow_iff hs).mp h2)
  have hle2 : hausdorffContent s δ' A
      ≤ ∑' n, ⨆ (_ : (t n).Nonempty), (Metric.ediam (t n)) ^ s := by
    rw [hausdorffContent]
    exact le_trans (iInf₂_le t hcov) (iInf_le _ hd')
  exact absurd (lt_of_le_of_lt hle2 (ht3.trans_le (min_le_left _ _))) (lt_irrefl _)

/-- If some `δ`-restricted content of `A` vanishes, then so does the Hausdorff measure of `A`. -/
lemma hausdorffMeasure_eq_zero_of_hausdorffContent_eq_zero {s : ℝ} (hs : 0 < s) {δ : ℝ≥0∞}
    {A : Set X} (h : hausdorffContent s δ A = 0) : μH[s] A = 0 := by
  refine le_antisymm ?_ (zero_le)
  rw [MeasureTheory.Measure.hausdorffMeasure_apply]
  refine iSup_le fun r => iSup_le fun hr => ?_
  exact le_of_eq (hausdorffContent_eq_zero_of_hausdorffContent_eq_zero hs hr h)

/-- **Lemma 0.4.** `H^s(E(δ,τ)) = 0` for every `δ > 0` and `0 < τ < 1`. -/
lemma hausdorffMeasure_cover_set_eq_zero {s : ℝ} (hs : 0 < s) (E : Set X) {δ τ : ℝ≥0∞}
    (hδ : 0 < δ) (hτ : τ ≠ 0) (hτ1 : τ < 1) (hE : μH[s] E ≠ ⊤) :
    μH[s] (cover_set s E δ τ) = 0 :=
  hausdorffMeasure_eq_zero_of_hausdorffContent_eq_zero hs
    (hausdorffContent_cover_set_eq_zero hs E hδ hτ hτ1 hE)

/-- Step (g): `H^s (⋃ k, E(1/k, 1 - 1/k)) = 0`. -/
lemma hausdorffMeasure_iUnion_cover_set_eq_zero {s : ℝ} (hs : 0 < s) (E : Set X)
    (hE : μH[s] E ≠ ⊤) :
    μH[s] (⋃ k : ℕ+, cover_set s E ((k : ℝ≥0∞))⁻¹ (1 - ((k : ℝ≥0∞))⁻¹)) = 0 := by
  refine measure_iUnion_null fun k => ?_
  have hktop : ((k : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hδpos : (0 : ℝ≥0∞) < ((k : ℕ) : ℝ≥0∞)⁻¹ := ENNReal.inv_pos.mpr hktop
  rcases eq_or_lt_of_le k.one_le with hk1 | hk1
  · -- `k = 1`, so `τ = 0`; use monotonicity in `τ` and the already known case `τ = 1/2`.
    have hkeq : ((k : ℕ) : ℝ≥0∞) = 1 := by rw [← hk1]; simp
    rw [hkeq]
    simp only [inv_one, tsub_self]
    refine measure_mono_null
        (cover_set_mono_tau s E 1 (by exact (zero_le : (0 : ℝ≥0∞) ≤ (1 / 2 : ℝ≥0∞)))) ?_
    exact hausdorffMeasure_cover_set_eq_zero hs E one_pos (by norm_num) (by norm_num) hE
  · have h1k : (1 : ℝ≥0∞) < ((k : ℕ) : ℝ≥0∞) := by
      exact_mod_cast (by exact_mod_cast hk1 : (1 : ℕ) < (k : ℕ))
    have hτ0 : (1 : ℝ≥0∞) - ((k : ℕ) : ℝ≥0∞)⁻¹ ≠ 0 :=
      (tsub_pos_iff_lt.mpr (ENNReal.inv_lt_one.mpr h1k)).ne'
    have hτ1 : (1 : ℝ≥0∞) - ((k : ℕ) : ℝ≥0∞)⁻¹ < 1 :=
      ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hδpos.ne'
    exact hausdorffMeasure_cover_set_eq_zero hs E hδpos hτ0 hτ1 hE

omit [MeasurableSpace X] [BorelSpace X] in
/-- At the exponent `s = 0`, the unrestricted content of a nonempty set is at least `1`. -/
lemma one_le_hausdorffContentInfty_zero {A : Set X} (hA : A.Nonempty) :
    1 ≤ hausdorffContentInfty 0 A := by
  rw [hausdorffContentInfty]
  refine le_iInf fun t => le_iInf fun hcov => ?_
  obtain ⟨y, hy⟩ := hA
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hy)
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum i)
  rw [iSup_pos ⟨y, hi⟩, ENNReal.rpow_zero]

end Vanishing

/-! ## From a small upper density to membership in some `E(δ, τ)` -/

section Density

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The `s`-dimensional density ratio of `H^s_∞` restricted to `E`, written out explicitly. -/
lemma dimensional_density_ratio_contentInfty (s : ℝ) (E : Set X) (x : X) (r : ℝ) :
    dimensional_density_ratio (OuterMeasure.restrict E (hausdorffContentInftyOuter s)) s x r
      = hausdorffContentInfty s (Metric.closedBall x r ∩ E) / ENNReal.ofReal ((2 * r) ^ s) := by
  rw [dimensional_density_ratio, OuterMeasure.restrict_apply, hausdorffContentInftyOuter_apply]

/-- **Lemma 0.5 (from small density to small density ratio).** -/
lemma exists_delta_of_upper_density_lt {s : ℝ} (E : Set X) (x : X)
    (hx : dimensional_upper_density (OuterMeasure.restrict E (hausdorffContentInftyOuter s)) s x
      < ENNReal.ofReal (1 / 2 ^ s)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ r : ℝ, 0 < r → r ≤ δ →
      hausdorffContentInfty s (Metric.closedBall x r ∩ E) / ENNReal.ofReal ((2 * r) ^ s)
        < ENNReal.ofReal ((1 - δ) / 2 ^ s) := by
  obtain ⟨b, hb0, hb1, hb2⟩ := ENNReal.lt_iff_exists_real_btwn.mp hx
  have h2s : (0 : ℝ) < 2 ^ s := Real.rpow_pos_of_pos two_pos s
  have hblt : b < 1 / 2 ^ s := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hb2
  have hb2s : b * 2 ^ s < 1 := by
    rw [lt_div_iff₀ h2s] at hblt; linarith
  set δ₀ : ℝ := 1 - b * 2 ^ s with hδ₀
  have hδ₀pos : 0 < δ₀ := by simp only [hδ₀]; linarith
  have hδ₀le : δ₀ ≤ 1 := by
    simp only [hδ₀]
    nlinarith
  have hbeq : b = (1 - δ₀) / 2 ^ s := by
    rw [hδ₀]; field_simp; ring
  have hev := eventually_lt_of_upper_density_lt
    (OuterMeasure.restrict E (hausdorffContentInftyOuter s)) s x _ hb1
  rw [Filter.eventually_iff, mem_nhdsGT_iff_exists_Ioc_subset] at hev
  obtain ⟨u, hu, hsub⟩ := hev
  have hu0 : (0 : ℝ) < u := hu
  refine ⟨min δ₀ u, lt_min hδ₀pos hu0, (min_le_left _ _).trans hδ₀le, ?_⟩
  intro r hr0 hrle
  have hrmem : r ∈ Set.Ioc (0 : ℝ) u := ⟨hr0, hrle.trans (min_le_right _ _)⟩
  have hlt := hsub hrmem
  simp only [Set.mem_setOf_eq, dimensional_density_ratio_contentInfty] at hlt
  refine hlt.trans_le (ENNReal.ofReal_le_ofReal ?_)
  rw [hbeq]
  gcongr
  linarith [min_le_left δ₀ u]

omit [MeasurableSpace X] [BorelSpace X] in
/-- **Lemma 0.6.**  The hypothesis `x ∈ E` occurs in the statement in the source (`x ∈ E ∩ C`);
the proof only uses `x ∈ C`.  The bound `δ ≤ 1` is implicit in the source: for `δ > 1` the
hypothesis on the density ratios cannot be satisfied. -/
lemma hausdorffContentInfty_inter_le {s : ℝ} (hs : 0 < s) (E : Set X) (x : X) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {C : Set X} (hxE : x ∈ E) (hxC : x ∈ C)
    (hC : Metric.ediam C ≤ ENNReal.ofReal δ)
    (hdens : ∀ r : ℝ, 0 < r → r ≤ δ →
      hausdorffContentInfty s (Metric.closedBall x r ∩ E) / ENNReal.ofReal ((2 * r) ^ s)
        < ENNReal.ofReal ((1 - δ) / 2 ^ s)) :
    hausdorffContentInfty s (C ∩ E) ≤ ENNReal.ofReal (1 - δ) * (Metric.ediam C) ^ s := by
  have hle : 0 ≤ Metric.ediam C := by exact zero_le
  rcases eq_or_lt_of_le hle with h0 | hpos
  · have hz : Metric.ediam (C ∩ E) = 0 :=
      le_antisymm (h0 ▸ Metric.ediam_mono Set.inter_subset_left) (zero_le)
    rw [hausdorffContentInfty_eq_zero_of_ediam_eq_zero hs hz]
    exact zero_le
  · have hdtop : Metric.ediam C ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hC
    set d := (Metric.ediam C).toReal with hd
    have hd0 : 0 < d := ENNReal.toReal_pos hpos.ne' hdtop
    have hdeq : ENNReal.ofReal d = Metric.ediam C := ENNReal.ofReal_toReal hdtop
    have hdδ : d ≤ δ := by
      have h := (ENNReal.toReal_le_toReal hdtop ENNReal.ofReal_ne_top).mpr hC
      rwa [ENNReal.toReal_ofReal hδ.le] at h
    have hsub : C ∩ E ⊆ Metric.closedBall x d ∩ E := by
      rintro y ⟨hyC, hyE⟩
      refine ⟨?_, hyE⟩
      have h1 : edist y x ≤ Metric.ediam C := Metric.edist_le_ediam_of_mem hyC hxC
      rw [Metric.mem_closedBall]
      have h2 := (ENNReal.toReal_le_toReal (edist_ne_top y x) hdtop).mpr h1
      rwa [edist_dist, ENNReal.toReal_ofReal dist_nonneg] at h2
    have hb := hdens d hd0 hdδ
    have h2d : (0 : ℝ) < (2 * d) ^ s := Real.rpow_pos_of_pos (by linarith) s
    have h2s : (0 : ℝ) < 2 ^ s := Real.rpow_pos_of_pos two_pos s
    rw [ENNReal.div_lt_iff
      (Or.inl (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact h2d))
      (Or.inl ENNReal.ofReal_ne_top)] at hb
    refine le_trans (hausdorffContentInfty_mono hsub) (le_of_lt (hb.trans_le (le_of_eq ?_)))
    rw [← ENNReal.ofReal_mul (div_nonneg (by linarith) h2s.le)]
    rw [show (1 - δ) / 2 ^ s * (2 * d) ^ s = (1 - δ) * d ^ s by
      rw [Real.mul_rpow (by norm_num) hd0.le]
      field_simp]
    rw [ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_rpow_of_pos hd0, hdeq]

omit [MeasurableSpace X] [BorelSpace X] in
/-- Step (j): the same bound for the `δ`-restricted content, by
`hausdorffContent_le_hausdorffContentInfty`. -/
lemma hausdorffContent_inter_le {s : ℝ} (hs : 0 < s) (E : Set X) (x : X) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {C : Set X} (hxE : x ∈ E) (hxC : x ∈ C)
    (hC : Metric.ediam C ≤ ENNReal.ofReal δ)
    (hdens : ∀ r : ℝ, 0 < r → r ≤ δ →
      hausdorffContentInfty s (Metric.closedBall x r ∩ E) / ENNReal.ofReal ((2 * r) ^ s)
        < ENNReal.ofReal ((1 - δ) / 2 ^ s)) :
    hausdorffContent s (ENNReal.ofReal δ) (C ∩ E)
      ≤ ENNReal.ofReal (1 - δ) * (Metric.ediam C) ^ s :=
  le_trans (hausdorffContent_le_hausdorffContentInfty hs.le
      (le_trans (Metric.ediam_mono Set.inter_subset_left) hC))
    (hausdorffContentInfty_inter_le hs E x hδ hδ1 hxE hxC hC hdens)

omit [MeasurableSpace X] [BorelSpace X] in
/-- Step (k): `x ∈ E(δ, 1 - δ)`. -/
lemma mem_cover_set_of_density_lt {s : ℝ} (hs : 0 < s) (E : Set X) (x : X) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hxE : x ∈ E)
    (hdens : ∀ r : ℝ, 0 < r → r ≤ δ →
      hausdorffContentInfty s (Metric.closedBall x r ∩ E) / ENNReal.ofReal ((2 * r) ^ s)
        < ENNReal.ofReal ((1 - δ) / 2 ^ s)) :
    x ∈ cover_set s E (ENNReal.ofReal δ) (1 - ENNReal.ofReal δ) := by
  refine ⟨hxE, fun C hxC hCd => ?_⟩
  have h := hausdorffContent_inter_le hs E x hδ hδ1 hxE hxC hCd hdens
  rwa [show (1 : ℝ≥0∞) - ENNReal.ofReal δ = ENNReal.ofReal (1 - δ) by
    rw [ENNReal.ofReal_sub _ hδ.le, ENNReal.ofReal_one]]

/-- Step (l): a point of `E` with small upper density lies in one of the sets `E(1/k, 1 - 1/k)`. -/
lemma mem_iUnion_cover_set_of_upper_density_lt {s : ℝ} (hs : 0 < s) (E : Set X) (x : X)
    (hxE : x ∈ E)
    (hx : dimensional_upper_density (OuterMeasure.restrict E (hausdorffContentInftyOuter s)) s x
      < ENNReal.ofReal (1 / 2 ^ s)) :
    x ∈ ⋃ k : ℕ+, cover_set s E ((k : ℝ≥0∞))⁻¹ (1 - ((k : ℝ≥0∞))⁻¹) := by
  obtain ⟨δ, hδ, hδ1, hdens⟩ := exists_delta_of_upper_density_lt E x hx
  have hmem : x ∈ cover_set s E (ENNReal.ofReal δ) (1 - ENNReal.ofReal δ) :=
    mem_cover_set_of_density_lt hs E x hδ hδ1 hxE hdens
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  obtain ⟨k, hkval⟩ : ∃ k : ℕ+, ((k : ℕ) : ℝ) = (n : ℝ) + 1 :=
    ⟨⟨n + 1, Nat.succ_pos n⟩, by
      show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1
      push_cast; ring⟩
  have hkpos : (0 : ℝ) < ((k : ℕ) : ℝ) := by rw [hkval]; positivity
  have hkle : (((k : ℕ) : ℝ≥0∞))⁻¹ ≤ ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hkpos]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hkval, inv_eq_one_div]
    exact hn.le
  have hkinvpos : (0 : ℝ≥0∞) < (((k : ℕ) : ℝ≥0∞))⁻¹ :=
    ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)
  exact Set.mem_iUnion.mpr ⟨k, cover_set_mono_delta hs.le E hkinvpos hkle hmem⟩

end Density

/-! ## Theorem 0.3 and Corollary 0.1 -/

section Main

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **Theorem 0.3.** Let `X` be a σ-compact metric space, `s ≥ 0`, and let `E ⊆ X` be measurable
with respect to the `s`-dimensional Hausdorff outer measure with `H^s(E) < ∞`.  Then for
`H^s`-almost every `x ∈ E`,
`limsup_{r ↘ 0} H^s_∞(E ∩ B(x,r)) / (2r)^s ≥ 1 / 2^s`;
equivalently, the set of `x ∈ E` where the upper density is `< 1/2^s` is `H^s`-null.

The σ-compactness of `X` and the Carathéodory measurability of `E` are part of the statement of
the theorem as given, but the proof below does not use them; only the finiteness `H^s(E) < ∞`
is needed. -/
theorem hausdorffContentInfty_upper_density_ge [SigmaCompactSpace X] {s : ℝ} (hs : 0 ≤ s)
    (E : Set X)
    (hEmeas : MeasurableSet[(OuterMeasure.mkMetric (X := X) (fun r => r ^ s)).caratheodory] E)
    (hE : μH[s] E ≠ ⊤) :
    μH[s] {x ∈ E | dimensional_upper_density
        (OuterMeasure.restrict E (hausdorffContentInftyOuter s)) s x
        < ENNReal.ofReal (1 / 2 ^ s)} = 0 := by
  rcases eq_or_lt_of_le hs with h0 | hspos
  · -- `s = 0`: the exceptional set is empty, since `H^0_∞(B(x,r) ∩ E) ≥ 1` for `x ∈ E`.
    have hset : {x ∈ E | dimensional_upper_density
        (OuterMeasure.restrict E (hausdorffContentInftyOuter s)) s x
        < ENNReal.ofReal (1 / 2 ^ s)} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
      intro hxE
      have hone : ENNReal.ofReal (1 / 2 ^ s) = 1 := by
        rw [← h0]; norm_num
      rw [hone, dimensional_upper_density]
      refine Filter.le_limsup_of_frequently_le (Filter.Eventually.frequently ?_)
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [dimensional_density_ratio_contentInfty, ← h0]
      simp only [Real.rpow_zero, ENNReal.ofReal_one, div_one]
      exact one_le_hausdorffContentInfty_zero
        ⟨x, Metric.mem_closedBall_self (le_of_lt hr), hxE⟩
    rw [hset]
    exact measure_empty
  · exact measure_mono_null
      (fun x hx => mem_iUnion_cover_set_of_upper_density_lt hspos E x hx.1 hx.2)
      (hausdorffMeasure_iUnion_cover_set_eq_zero hspos E hE)

/-- **Corollary 0.1.** Under the same hypotheses, for `H^s`-almost every `x ∈ E`,
`limsup_{r ↘ 0} H^s(E ∩ B(x,r)) / (2r)^s ≥ 1 / 2^s`, the density being taken with respect to the
restriction of the `s`-dimensional Hausdorff measure to `E`.

This follows from Theorem 0.3, because `H^s_∞ ≤ H^s_1 ≤ H^s`, so the exceptional set of the
corollary is contained in the exceptional set of the theorem. -/
theorem hausdorffMeasure_upper_density_ge [SigmaCompactSpace X] {s : ℝ} (hs : 0 ≤ s)
    (E : Set X)
    (hEmeas : MeasurableSet[(OuterMeasure.mkMetric (X := X) (fun r => r ^ s)).caratheodory] E)
    (hE : μH[s] E ≠ ⊤) :
    μH[s] {x ∈ E | dimensional_upper_density ((μH[s]).restrict E).toOuterMeasure s x
        < ENNReal.ofReal (1 / 2 ^ s)} = 0 := by
  refine measure_mono_null ?_ (hausdorffContentInfty_upper_density_ge hs E hEmeas hE)
  rintro x ⟨hxE, hlt⟩
  refine ⟨hxE, lt_of_le_of_lt ?_ hlt⟩
  refine Filter.limsup_le_limsup (Filter.Eventually.of_forall fun r => ?_)
  rw [dimensional_density_ratio_contentInfty, dimensional_density_ratio]
  gcongr
  show hausdorffContentInfty s (Metric.closedBall x r ∩ E)
      ≤ ((μH[s]).restrict E) (Metric.closedBall x r)
  rw [Measure.restrict_apply Metric.isClosed_closedBall.measurableSet]
  exact le_trans (hausdorffContentInfty_le_hausdorffContent s 1 _)
    (hausdorffContent_le_hausdorffMeasure one_pos _)

end Main

/-
This is the full version of the lower bound in Theorm 2.7 in [EG]. There needs to be substantial edits.
-Match definitions to Mathlib
-Proof Golf


2/18 To-Do List:
- Get rid of depricated errors
- Figure out if assumptions can actually be removed, since we use some of them later when things are proved
- The stuff above too :)
- Look over Aaron's comments that he sent on Zulip
-/


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
import FormalizingGMT.«Project Versions».Densities.Basic
import FormalizingGMT.«Project Versions».Aux_definitions

set_option linter.mathlibStandardSet false
set_option linter.deprecated false
set_option linter.unusedVariables false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise




noncomputable section


lemma hausdorffContent_le_hausdorffMeasure {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {d : ℝ} {δ : ℝ} {s : Set X} (hδ : 0 < δ) :
    hausdorffContent d (ENNReal.ofReal δ) s ≤ MeasureTheory.Measure.hausdorffMeasure d s := by
      unfold hausdorffContent
      rw [MeasureTheory.Measure.hausdorffMeasure_apply]
      exact le_iSup₂_of_le (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ) le_rfl


/-
Covering estimate for E(delta, tau).
(formerly: lemma_1a_fix)
-/
lemma hausdorffContent_E_delta_tau_le_tau_mul_cover_sum {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (δ : ℝ) (τ : ℝ) (hδ : 0 < δ)
    (C : ℕ → Set X)
    (h_cover : cover_set E s δ τ ⊆ ⋃ i, C i)
    (h_diam : ∀ i, EMetric.diam (C i) ≤ ENNReal.ofReal δ)
    (h_inter : ∀ i, (C i ∩ cover_set E s δ τ).Nonempty) :
    hausdorffContent s (ENNReal.ofReal δ) (cover_set E s δ τ) ≤ ENNReal.ofReal τ * ∑' i, (EMetric.diam (C i)) ^ s := by
  have h_subset : ∀ i, MeasureTheory.Measure.hausdorffMeasure s (C i ∩ cover_set E s δ τ) ≤
      ENNReal.ofReal τ * (EMetric.diam (C i)) ^ s := by
    intro i
    obtain ⟨x, hx⟩ := h_inter i
    exact (MeasureTheory.measure_mono (Set.inter_subset_inter_right _ (fun _ hy => hy.1))).trans
      (hx.2.2 _ hx.1 (h_diam i))
  calc hausdorffContent s (ENNReal.ofReal δ) (cover_set E s δ τ)
      ≤ MeasureTheory.Measure.hausdorffMeasure s (cover_set E s δ τ) :=
        hausdorffContent_le_hausdorffMeasure hδ
    _ ≤ ∑' i, MeasureTheory.Measure.hausdorffMeasure s (C i ∩ cover_set E s δ τ) :=
        (MeasureTheory.measure_mono fun x hx => by
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (h_cover hx)
          exact Set.mem_iUnion.mpr ⟨i, hi, hx⟩).trans (MeasureTheory.measure_iUnion_le _)
    _ ≤ ∑' i, ENNReal.ofReal τ * (EMetric.diam (C i)) ^ s :=
        ENNReal.tsum_le_tsum h_subset
    _ = ENNReal.ofReal τ * ∑' i, (EMetric.diam (C i)) ^ s :=
        ENNReal.tsum_mul_left

/-
The modified cover covers the intersection of E and the original cover.
-/
lemma truncated_cover_subset {X : Type*} [EMetricSpace X] (U : ℕ → Set X) (E : Set X) (x : X) :
    E ∩ ⋃ n, U n ⊆ ⋃ k, truncated_cover U E x k := by
      -- Take any $y \in E \cap \bigcup U_n �$.� Then $y \in E$ and there exists $k$ such that $ �y� \in U_k$.
      intro y hy
      obtain ⟨k, hk⟩ : ∃ k, y ∈ U k := by
        aesop
      simp_all +decide [truncated_cover]
      exact ⟨ k, by
        rw [ if_pos ⟨ y, hk, hy.1 ⟩ ]
        exact hk ⟩


/-
The diameter of each set in the modified cover is bounded by the supremum of diameters in the original cover.
-/
lemma truncated_cover_diam_le {X : Type*} [EMetricSpace X] (U : ℕ → Set X) (E : Set X) (x : X) (k : ℕ) :
    EMetric.diam (truncated_cover U E x k) ≤ ⨆ n, EMetric.diam (U n) := by
      unfold truncated_cover
      split_ifs with h
      · exact le_ciSup ( show BddAbove ( Set.range fun n => EMetric.diam ( U n ) ) from ⟨ ⊤, Set.forall_mem_range.2 fun n => le_top ⟩ ) k
      · exact le_trans ( by simp +decide ) ( le_ciSup ( show BddAbove ( Set.range fun n => EMetric.diam ( U n ) ) from ⟨ ⊤, Set.forall_mem_range.2 fun n => le_top ⟩ ) k )

/-
The sum of powers of diameters of the modified cover is less than or equal to that of the original cover.
-/
lemma truncated_cover_sum_le {X : Type*} [EMetricSpace X] {s : ℝ} (hs : 0 < s)
    (U : ℕ → Set X) (E : Set X) (x : X) :
    ∑' k, (EMetric.diam (truncated_cover U E x k))^s ≤ ∑' n, (EMetric.diam (U n))^s := by
      apply_rules [ ENNReal.tsum_le_tsum ]
      intro n
      by_cases h : Set.Nonempty ( U n ∩ E ) <;> simp +decide [ *, truncated_cover ]

/-
Reduce a general cover to one with nonempty intersections using a modified cover anchored at a fixed point.
(formerly: lemma_1c_helper)
-/
lemma hausdorffContent_le_tau_mul_sum_of_anchor {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (δ : ℝ) (τ : ℝ) (hs : 0 < s)
    (h_impl : ∀ (C : ℕ → Set X),
      (cover_set E s δ τ ⊆ ⋃ i, C i) →
      (∀ i, EMetric.diam (C i) ≤ ENNReal.ofReal δ) →
      (∀ i, (C i ∩ cover_set E s δ τ).Nonempty) →
      hausdorffContent s (ENNReal.ofReal δ) (cover_set E s δ τ) ≤ ENNReal.ofReal τ * ∑' i, (EMetric.diam (C i)) ^ s)
    (C : ℕ → Set X)
    (h_cover : cover_set E s δ τ ⊆ ⋃ i, C i)
    (h_diam : ∀ i, EMetric.diam (C i) ≤ ENNReal.ofReal δ)
    (x : X) (hx : x ∈ cover_set E s δ τ) :
    hausdorffContent s (ENNReal.ofReal δ) (cover_set E s δ τ) ≤ ENNReal.ofReal τ * ∑' i, (EMetric.diam (C i)) ^ s := by
      -- Let's define the modified cover $C'$.
      set C' : ℕ → Set X := fun i => truncated_cover C (cover_set E s δ τ) x i
      refine' le_trans ( h_impl C' _ _ _ ) ( mul_le_mul_left' ( truncated_cover_sum_le hs C _ _ ) _ )
      · exact fun y hy => truncated_cover_subset C _ _ |> fun h => h <| Set.mem_inter hy ( h_cover hy )
      · intro i
        refine' le_trans ( truncated_cover_diam_le _ _ _ _ ) _
        exact ciSup_le h_diam
      · intro i
        simp only [C', truncated_cover]
        split_ifs with hi
        · exact hi
        · exact ⟨x, Set.mem_singleton x, hx⟩


/-
The Hausdorff content of E(delta, tau) satisfies a contraction inequality.
(formerly: lemma_1c)
-/
lemma hausdorffContent_E_delta_tau_contraction {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (δ : ℝ) (τ : ℝ) (hδ : 0 < δ) (hτ : 0 < τ) (hτ1 : τ < 1) (hs : 0 < s) :
    hausdorffContent s (ENNReal.ofReal δ) (cover_set E s δ τ) ≤ ENNReal.ofReal τ * hausdorffContent s (ENNReal.ofReal δ) (cover_set E s δ τ) := by
      by_cases h : cover_set E s δ τ = ∅
      · simp +decide [ h, hausdorffContent ]
        refine' le_trans _ ( mul_le_mul_left' ( le_iInf fun t => le_iInf fun ht => _ ) _ )
        rotate_left
        exact 0
        · exact zero_le _
        · refine' le_trans ( ciInf_le _ ( fun _ => ∅ ) ) _ <;> simp +decide
      · -- By definition of Hausdorff content, it suffices to show that for any cover $C$ of $E_{\delta, \tau}$ with diameters $\le \delta$, we have $hausdorffContent \le \tau \sum diam(C_i)^s$.
        suffices h_suff : ∀ (C : ℕ → Set X),
            (cover_set E s δ τ ⊆ ⋃ i, C i) →
            (∀ i, EMetric.diam (C i) ≤ ENNReal.ofReal δ) →
            hausdorffContent s (ENNReal.ofReal δ) (cover_set E s δ τ) ≤ ENNReal.ofReal τ * ∑' i, (EMetric.diam (C i)) ^ s by
              refine' le_trans _ ( mul_le_mul_left' ( le_iInf fun C => _ ) _ )
              rotate_left
              exact hausdorffContent s (ENNReal.ofReal δ) ( cover_set E s δ τ )
              · refine' le_iInf fun hC => le_iInf fun hC' => _
                refine' le_trans ( h_suff C hC hC' ) _
                rw [ ← ENNReal.tsum_mul_left ]
                refine' ENNReal.tsum_le_tsum fun n => _
                by_cases hn : ( C n ).Nonempty <;> simp +decide [ hn ]
                · exact mul_le_of_le_one_left ( by positivity ) ( ENNReal.ofReal_le_one.mpr hτ1.le )
                · simp_all +decide [ Set.not_nonempty_iff_eq_empty.mp hn ]
              · refine' le_trans ( le_of_eq _ ) ( mul_le_mul_left' ( le_iInf fun C => _ ) _ )
                rotate_left
                exact ( ENNReal.ofReal τ ) ⁻¹ * hausdorffContent s (ENNReal.ofReal δ) ( cover_set E s δ τ )
                · by_cases hC : cover_set E s δ τ ⊆ ⋃ n, C n <;> by_cases hC' : ∀ n, EMetric.diam ( C n ) ≤ ENNReal.ofReal δ <;> simp +decide [ hC, hC' ]
                  rw [ ENNReal.inv_mul_le_iff ]
                  · convert h_suff C hC hC' using 1
                    congr! 2
                    ext n
                    by_cases hn : ( C n ).Nonempty <;> simp +decide [ hn ]
                    rw [ show C n = ∅ by exact Set.not_nonempty_iff_eq_empty.mp hn, EMetric.diam_empty, ENNReal.zero_rpow_of_pos hs ]
                  · positivity
                  · exact ENNReal.ofReal_ne_top
                · rw [ ← mul_assoc, ENNReal.mul_inv_cancel ( by aesop ) ( by aesop ), one_mul ]
        -- Let $x \in E_{\delta, \tau}$.
        obtain ⟨x, hx⟩ : ∃ x, x ∈ cover_set E s δ τ := by
          exact Set.nonempty_iff_ne_empty.2 h
        intro C hC hC'
        apply hausdorffContent_le_tau_mul_sum_of_anchor
        exacts [ hs, fun C hC hC' hC'' => hausdorffContent_E_delta_tau_le_tau_mul_cover_sum E s δ τ hδ C hC hC' hC'', hC, hC', hx ]

/-
General ENNReal algebraic fact: if x ≤ τ * x with τ < 1 and x ≠ ⊤, then x = 0.
This is the "contraction implies zero" principle used in measure-theoretic arguments.
-/
private lemma ennreal_eq_zero_of_le_mul_of_lt_one {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    {x : ENNReal} (hx : x ≠ ⊤) (h : x ≤ ENNReal.ofReal τ * x) : x = 0 := by
  by_cases hx0 : x = 0
  · exact hx0
  have hmul : ENNReal.ofReal τ * x ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx
  rw [← ENNReal.toReal_le_toReal hx hmul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hτ0] at h
  nlinarith [ENNReal.toReal_pos hx0 hx]

/-
If the Hausdorff content is finite, it must be zero.
(formerly: lemma_1d)
Now a direct consequence of the contraction inequality and the general ENNReal algebraic fact.
-/
lemma hausdorffContent_E_delta_tau_eq_zero_of_ne_top {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (δ : ℝ) (τ : ℝ) (hδ : 0 < δ) (hτ : 0 < τ) (hτ1 : τ < 1) (hs : 0 < s)
    (h_fin : hausdorffContent s (ENNReal.ofReal δ) (cover_set E s δ τ) ≠ ⊤) :
    hausdorffContent s (ENNReal.ofReal δ) (cover_set E s δ τ) = 0 :=
  ennreal_eq_zero_of_le_mul_of_lt_one hτ.le hτ1 h_fin
    (hausdorffContent_E_delta_tau_contraction E s δ τ hδ hτ hτ1 hs)


/-
If the Hausdorff content is zero at some scale, it is zero at any scale.
-/
lemma hausdorffContent_zero_mono {X : Type*} [EMetricSpace X]
    {s : ℝ} {δ δ' : ℝ} {E : Set X} (hs : 0 < s) (_hδ : 0 < δ) (hδ' : 0 < δ')
    (h : hausdorffContent s (ENNReal.ofReal δ) E = 0) :
    hausdorffContent s (ENNReal.ofReal δ') E = 0 := by
      refine' le_antisymm ( le_trans ( le_of_eq ( Eq.symm _ ) ) ( le_of_forall_gt_imp_ge_of_dense _ ) ) bot_le
      exact rfl
      intro ε hε
      -- Choose η such that η < ε and η^(1/s) ≤ δ'.
      obtain ⟨η, hη₁, hη₂⟩ : ∃ η : ENNReal, 0 < η ∧ η < ε ∧ η^(1 / s) ≤ ENNReal.ofReal δ' := by
        -- Since $\eta^{1/s} \leq \delta'$, we can choose $\eta$ such that $\eta \leq (\delta')^s$.
        obtain ⟨η, hη₁, hη₂⟩ : ∃ η : ENNReal, 0 < η ∧ η < ε ∧ η ≤ (ENNReal.ofReal δ') ^ s := by
          by_cases hη : ENNReal.ofReal δ' ^ s < ε
          · exact ⟨ ENNReal.ofReal δ' ^ s, by positivity, hη, le_rfl ⟩
          · rcases ENNReal.lt_iff_exists_nnreal_btwn.mp hε with ⟨ η, hη₁, hη₂ ⟩
            exact ⟨ η, by simpa using hη₁, hη₂, le_trans ( by simpa using hη₂.le ) ( le_of_not_gt hη ) ⟩
        refine' ⟨ η, hη₁, hη₂.1, _ ⟩
        exact le_trans ( ENNReal.rpow_le_rpow hη₂.2 ( by positivity ) ) ( by rw [ ← ENNReal.rpow_mul, mul_one_div_cancel hs.ne', ENNReal.rpow_one ] )
      -- Since `hausdorffContent s (ENNReal.ofReal δ) E = 0`, for any `η > 0`, there exists a cover `{U_i}` such that `diam(U_i) ≤ δ` and `∑ diam(U_i)^s < η`.
      obtain ⟨U, hU₁, hU₂⟩ : ∃ U : ℕ → Set X, E ⊆ ⋃ i, U i ∧ ∀ i, EMetric.diam (U i) ≤ ENNReal.ofReal δ ∧ ∑' i, (EMetric.diam (U i)) ^ s < η := by
        contrapose! h
        refine' ne_of_gt ( lt_of_lt_of_le hη₁ ( le_iInf fun U => le_iInf fun hU => le_iInf fun hU' => _ ) )
        obtain ⟨ i, hi ⟩ := h U hU
        refine' le_trans ( hi ( hU' i ) ) _
        refine' ENNReal.tsum_le_tsum fun n => _
        by_cases h : ( U n ).Nonempty <;> simp +decide [ h ]
        simp_all +decide [ Set.not_nonempty_iff_eq_empty.mp h ]
      -- Since `η^(1/s) ≤ δ'`, for each `i`, `diam(U_i)^s ≤ ∑ diam(U_j)^s < η`, so `diam(U_i) < η^(1/s) ≤ δ'`.
      have h_diam_le : ∀ i, EMetric.diam (U i) ≤ ENNReal.ofReal δ' := by
        intro i
        have h_diam_le_i : (EMetric.diam (U i)) ^ s ≤ ∑' j, (EMetric.diam (U j)) ^ s := by
          exact ENNReal.le_tsum i
        refine' le_trans _ hη₂.2
        exact le_trans ( by rw [ ← ENNReal.rpow_mul, mul_one_div_cancel hs.ne', ENNReal.rpow_one ] ) ( ENNReal.rpow_le_rpow ( h_diam_le_i.trans ( le_of_lt ( hU₂ i |>.2 ) ) ) ( by positivity ) );
      refine' le_trans ( ciInf_le _ _ ) _
      exact ⟨ 0, Set.forall_mem_range.2 fun _ => zero_le _ ⟩
      exact U
      simp_all +decide
      refine' le_trans _ hη₂.1.le
      refine' le_trans _ ( le_of_lt ( hU₂ 0 |>.2 ) )
      refine' ENNReal.tsum_le_tsum fun i => _
      by_cases hi : ( U i ).Nonempty <;> simp +decide [ hi ]

/-
If the Hausdorff content is zero, the Hausdorff measure is zero.
-/
lemma hausdorffContent_zero_implies_hausdorffMeasure_zero {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {s : ℝ} {δ : ℝ} {E : Set X} (hs : 0 < s) (hδ : 0 < δ)
    (h : hausdorffContent s (ENNReal.ofReal δ) E = 0) :
    MeasureTheory.Measure.hausdorffMeasure s E = 0 := by
      -- By Lemma 2, since the Hausdorff content of E at scale δ is zero, the Hausdorff measure of E at scale δ' is also zero.
      have h_zero_content : ∀ δ' > 0, hausdorffContent s (ENNReal.ofReal δ') E = 0 := by
        intro δ' hδ'
        exact hausdorffContent_zero_mono hs hδ hδ' h
      simp +decide [MeasureTheory.Measure.hausdorffMeasure_apply]
      intro i hi
      specialize h_zero_content (ENNReal.toReal i)
      rcases eq_or_ne i ⊤ with rfl | hi' <;> simp_all +decide
      · refine' le_antisymm _ _
        · refine' le_trans _ ( le_of_eq h )
          refine' le_iInf fun t => le_iInf fun ht => le_iInf fun h => _
          exact iInf_le_of_le t ( iInf_le_of_le ht le_rfl )
        · exact zero_le _
      · convert h_zero_content (ENNReal.toReal_pos hi.ne' hi') using 1

/-
If the Hausdorff measure of E is finite, then the Hausdorff measure of E(delta, tau) is zero.
The proof chain: cover_set ⊆ E, so content(cover_set) ≤ measure(E) < ⊤;
the contraction inequality then forces content = 0; zero content implies zero measure.
-/
lemma lemma_1e {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (δ : ℝ) (τ : ℝ) (hδ : 0 < δ) (hτ : 0 < τ) (hτ1 : τ < 1) (hs : 0 < s)
    (h_fin : MeasureTheory.Measure.hausdorffMeasure s E ≠ ⊤) :
    MeasureTheory.Measure.hausdorffMeasure s (cover_set E s δ τ) = 0 :=
  hausdorffContent_zero_implies_hausdorffMeasure_zero hs hδ <|
    hausdorffContent_E_delta_tau_eq_zero_of_ne_top E s δ τ hδ hτ hτ1 hs <|
      ((hausdorffContent_le_hausdorffMeasure hδ).trans
        (MeasureTheory.measure_mono fun x hx => hx.1)).trans_lt
        (lt_top_iff_ne_top.mpr h_fin) |>.ne

/-
Lemma 7.6: From small density to small density ratio. If the upper density is strictly less than 1/2^s, then the density ratio is uniformly bounded by (1-δ)/2^s for small r.
-/
lemma lemma_7_6 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (x : X)
    (hx : x ∈ E ∧ dimensional_upper_density ((MeasureTheory.Measure.hausdorffMeasure s).restrict E) s x < ENNReal.ofReal (1 / (2 : ℝ) ^ s)) :
    ∃ δ > 0, ∀ r, 0 < r → r ≤ δ →
      dimensional_density_ratio ((MeasureTheory.Measure.hausdorffMeasure s).restrict E) s x r < ENNReal.ofReal ((1 - δ) / (2 : ℝ) ^ s) := by
        -- By Lemma 4.2, there exist ε > 0 and R > 0 such that for all r ∈ (0, R], density_ratio < 1/2^s - ε.
        obtain ⟨ε, hε_pos, R, hR_pos, hεR⟩ : ∃ ε > 0, ∃ R > 0, ∀ r : ℝ, 0 < r → r ≤ R → dimensional_density_ratio ((MeasureTheory.Measure.hausdorffMeasure s).restrict E) s x r < ENNReal.ofReal (1 / 2 ^ s) - ENNReal.ofReal ε := by
          obtain ⟨ε, hε⟩ : ∃ ε > 0, dimensional_upper_density ((MeasureTheory.Measure.hausdorffMeasure s).restrict E) s x < ENNReal.ofReal (1 / 2 ^ s) - ENNReal.ofReal ε := by
            rcases ENNReal.lt_iff_exists_add_pos_lt.mp hx.2 with ⟨ ε, hε_pos, hε ⟩
            refine' ⟨ ε, hε_pos, _ ⟩
            rw [ lt_tsub_iff_right ]
            aesop
          -- By definition of upper density, there exists R > 0 such that for all r ∈ (0, R], density_ratio < 1/2^s - ε.
          obtain ⟨R, hR_pos, hR⟩ : ∃ R > 0, ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), dimensional_density_ratio ((MeasureTheory.Measure.hausdorffMeasure s).restrict E) s x r < ENNReal.ofReal (1 / 2 ^ s) - ENNReal.ofReal ε := by
            contrapose! hε
            intro hε_pos
            refine' le_csInf _ _
            · refine' ⟨ ⊤, _ ⟩
              simp +decide
            · intro b hb
              contrapose! hε
              rcases ENNReal.lt_iff_exists_real_btwn.mp hε with ⟨ c, hc ⟩
              exact ⟨ 1, zero_lt_one, by filter_upwards [ hb ] with r hr using lt_of_le_of_lt hr hc.2.1 |> lt_of_lt_of_le <| le_of_lt hc.2.2 ⟩
          rcases ( Metric.mem_nhdsWithin_iff.mp hR ) with ⟨ δ, δpos, hδ ⟩
          exact ⟨ ε, hε.1, δ / 2, half_pos δpos, fun r hr₁ hr₂ => hδ ⟨ mem_ball_zero_iff.mpr ( abs_lt.mpr ⟨ by linarith, by linarith ⟩ ), hr₁ ⟩ ⟩
        -- Let δ = min{R, 2^s * ε}. Then δ/2^s ≤ ε, and for all r ∈ (0, δ] we have r ∈ (0, R], so density_ratio < 1/2^s - ε ≤ (1 - δ)/2^s.
        use min R (2 ^ s * ε) / 2
        (
        refine' ⟨ by positivity, fun r hr₁ hr₂ => lt_of_lt_of_le ( hεR r hr₁ ( hr₂.trans ( by linarith [ min_le_left R ( 2 ^ s * ε ) ] ) ) ) _ ⟩
        rw [ ← ENNReal.ofReal_sub ]
        · exact ENNReal.ofReal_le_ofReal ( by ring_nf; nlinarith [ min_le_left R ( 2 ^ s * ε ), min_le_right R ( 2 ^ s * ε ), Real.rpow_pos_of_pos zero_lt_two s, mul_inv_cancel₀ ( ne_of_gt ( Real.rpow_pos_of_pos zero_lt_two s ) ) ] )
        · positivity)

/-
Lemma 7.7: Bound on measure of intersection with C (strict diameter version).
-/
lemma lemma_7_7 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (C : Set X) (x : X) (δ : ℝ)
    (hs : 0 < s) (hδ : 0 < δ) (hx : x ∈ E ∩ C) (h_diam : EMetric.diam C < ENNReal.ofReal δ)
    (h_dens : ∀ r, 0 < r → r ≤ δ → dimensional_density_ratio ((MeasureTheory.Measure.hausdorffMeasure s).restrict E) s x r < ENNReal.ofReal ((1 - δ) / (2 : ℝ) ^ s)) :
    MeasureTheory.Measure.hausdorffMeasure s (C ∩ E) ≤ ENNReal.ofReal (1 - δ) * (EMetric.diam C) ^ s := by
      -- Applying the definition of density ratio and the hypothesis h_dens, we get that for any $r$ such that $d < r \leq \delta$, $H^s(closedBall(x, r) \cap E) < (1 - \delta) * r^s$.
      have h_ball : ∀ r, EMetric.diam C < ENNReal.ofReal r → r ≤ δ → (MeasureTheory.Measure.hausdorffMeasure s (EMetric.closedBall x (ENNReal.ofReal r) ∩ E)) < ENNReal.ofReal (1 - δ) * (ENNReal.ofReal r) ^ s := by
        intro r hr₁ hr₂
        have h_ball : (MeasureTheory.Measure.hausdorffMeasure s (EMetric.closedBall x (ENNReal.ofReal r) ∩ E)) / (ENNReal.ofReal (2 * r)) ^ s < ENNReal.ofReal ((1 - δ) / 2 ^ s) := by
          have hr0 : 0 < r :=
            lt_of_le_of_ne (le_of_not_gt fun h => by
              rw [ENNReal.ofReal_eq_zero.mpr h.le] at hr₁
              exact hr₁.not_ge <| by simp +decide) <| Ne.symm <| by
                rintro rfl
                exact hr₁.not_ge <| by simp +decide
          have h_dens' := h_dens r hr0 hr₂
          have h_ball_metric :
              ((MeasureTheory.Measure.hausdorffMeasure s).restrict E) (Metric.closedBall x r) /
                ENNReal.ofReal ((2 * r) ^ s) < ENNReal.ofReal ((1 - δ) / 2 ^ s) := by
            simpa [dimensional_density_ratio] using h_dens'
          have h_cb : EMetric.closedBall x (ENNReal.ofReal r) = Metric.closedBall x r := by
            ext y
            simp [EMetric.closedBall, Metric.closedBall, edist_dist, hr0.le]
          have h_num :
              ((MeasureTheory.Measure.hausdorffMeasure s).restrict E) (Metric.closedBall x r) =
                (MeasureTheory.Measure.hausdorffMeasure s) (EMetric.closedBall x (ENNReal.ofReal r) ∩ E) := by
            rw [MeasureTheory.Measure.restrict_apply]
            · simp [h_cb, Set.inter_comm]
            · exact Metric.isClosed_closedBall.measurableSet
          have h_den : ENNReal.ofReal ((2 * r) ^ s) = (ENNReal.ofReal (2 * r)) ^ s := by
            symm
            rw [ENNReal.ofReal_rpow_of_pos]
            positivity
          simpa [h_num, h_den] using h_ball_metric
        contrapose! h_ball
        rw [ ENNReal.le_div_iff_mul_le ]
        · convert h_ball using 1
          rw [ ENNReal.ofReal_div_of_pos ( by positivity ), ENNReal.ofReal_mul ( by positivity ) ]
          rw [ ENNReal.mul_rpow_of_nonneg _ _ ( by positivity ), ENNReal.ofReal_rpow_of_pos ( by positivity ) ]
          ring_nf
          rw [ ENNReal.div_mul_cancel ] <;> norm_num [ Real.rpow_pos_of_pos ]
          ring
        · simp +zetaDelta at *
          exact Or.inl ⟨ fun h => False.elim <| hr₁.not_ge <| by simp +decide [ENNReal.ofReal_eq_zero.mpr
                h], fun h => False.elim <| absurd h <| by simp +decide [ ENNReal.mul_eq_top ] ⟩
        · exact Or.inl ( ENNReal.rpow_ne_top_of_nonneg hs.le ( ENNReal.ofReal_ne_top ) )
      have h_inf : ∀ r, EMetric.diam C < ENNReal.ofReal r → r ≤ δ → (MeasureTheory.Measure.hausdorffMeasure s (C ∩ E)) ≤ ENNReal.ofReal (1 - δ) * (ENNReal.ofReal r) ^ s := by
        intro r hr₁ hr₂
        have h_subset : C ∩ E ⊆ EMetric.closedBall x (ENNReal.ofReal r) ∩ E := by
          intro y hy
          exact ⟨ le_of_lt ( lt_of_le_of_lt ( EMetric.edist_le_diam_of_mem hy.1 hx.2 ) hr₁ ), hy.2 ⟩
        exact le_trans ( MeasureTheory.measure_mono h_subset ) ( le_of_lt ( h_ball r hr₁ hr₂ ) )
      -- Taking the infimum over $r \in (d, \delta]$, we get $H^s(C \cap E) \leq (1 - \delta) * d^s$.
      have h_inf : (MeasureTheory.Measure.hausdorffMeasure s (C ∩ E)) ≤ ENNReal.ofReal (1 - δ) * (⨅ r ∈ Set.Ioc (EMetric.diam C).toReal δ, (ENNReal.ofReal r) ^ s) := by
        rw [ ENNReal.mul_iInf ]
        · refine' le_iInf fun r => _
          by_cases hr : r ∈ Set.Ioc (EMetric.diam C).toReal δ <;> simp_all +decide
          · refine' h_inf r _ hr.2
            rw [ ENNReal.lt_ofReal_iff_toReal_lt ] <;> aesop
          · by_cases h : ENNReal.ofReal ( 1 - δ ) = 0 <;> simp_all +decide
            grind
        · aesop
      refine' le_trans h_inf ( mul_le_mul_left' _ _ )
      have h_inf : Filter.Tendsto (fun r => (ENNReal.ofReal r) ^ s) (nhdsWithin (EMetric.diam C).toReal (Set.Ioi (EMetric.diam C).toReal)) (nhds ((EMetric.diam C) ^ s)) := by
        have h_inf : Filter.Tendsto (fun r => ENNReal.ofReal r) (nhdsWithin (EMetric.diam C).toReal (Set.Ioi (EMetric.diam C).toReal)) (nhds (EMetric.diam C)) := by
          convert ENNReal.tendsto_ofReal ( Filter.tendsto_id.mono_left inf_le_left ) using 1
          rw [ ENNReal.ofReal_toReal ]
          exact ne_of_lt ( lt_of_lt_of_le h_diam ( le_top ) )
        exact ENNReal.continuous_rpow_const.tendsto _ |> Filter.Tendsto.comp <| h_inf
      refine' le_of_tendsto_of_tendsto tendsto_const_nhds h_inf _
      filter_upwards [ self_mem_nhdsWithin, Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, show ( EMetric.diam C |> ENNReal.toReal ) < δ from by rw [ ← ENNReal.toReal_ofReal hδ.le ] ; exact ENNReal.toReal_strict_mono ( by aesop ) h_diam ⟩ ] with r hr₁ hr₂
      exact iInf₂_le r ⟨ hr₁, hr₂.2.le ⟩

/-
Lemma 7.8: The bad set is contained in a countable union of E(δ, τ) sets.
-/
lemma lemma_7_8 {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (hs : 0 < s)
    (h_fin : MeasureTheory.Measure.hausdorffMeasure s E ≠ ⊤) :
  {x ∈ E | dimensional_upper_density ((MeasureTheory.Measure.hausdorffMeasure s).restrict E) s x < ENNReal.ofReal (1 / (2 : ℝ) ^ s)} ⊆
      ⋃ (k : ℕ+), cover_set E s (1 / (k : ℝ)) (1 - 1 / (k : ℝ)) := by
      intro x hx
      obtain ⟨ δ, hδ_pos, hδ ⟩ := lemma_7_6 E s x hx
      simp +decide [ cover_set ]
      (
      obtain ⟨ k, hk ⟩ := exists_nat_one_div_lt hδ_pos
      use hx.1, ⟨ k + 1, Nat.succ_pos k ⟩
      intro C hx_C hC_diam
      have hC_diam_lt : EMetric.diam C < ENNReal.ofReal δ := by
        have hC_diam_lt : EMetric.diam C ≤ 1 / (k + 1 : ENNReal) := by
          rw [ ENNReal.le_div_iff_mul_le ] <;> aesop
        refine' lt_of_le_of_lt hC_diam_lt _
        rw [ ENNReal.lt_ofReal_iff_toReal_lt ] <;> aesop
      have := lemma_7_7 E s C x δ hs hδ_pos ⟨ hx.1, hx_C ⟩ hC_diam_lt ( fun r hr hr' => hδ r hr hr' )
      refine' le_trans this _
      gcongr
      simpa using hk.le)

/-
Main Theorem: The set of points where the upper density is less than 1/2^s has Hausdorff measure 0.
-/
theorem main_theorem {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (hs : 0 < s)
    (h_fin : MeasureTheory.Measure.hausdorffMeasure s E ≠ ⊤) :
    MeasureTheory.Measure.hausdorffMeasure s
  {x ∈ E | dimensional_upper_density ((MeasureTheory.Measure.hausdorffMeasure s).restrict E) s x < ENNReal.ofReal (1 / (2 : ℝ) ^ s)} = 0 := by
      have h_bad_set_zero : ∀ k : ℕ+, (MeasureTheory.Measure.hausdorffMeasure s) (cover_set E s (1 / (k : ℝ)) (1 - 1 / (k : ℝ))) = 0 := by
        intro k
        by_cases hk : k = 1
        · have h_subset : cover_set E s 1 0 ⊆ cover_set E s 1 (1 / 2) := by
            intro x hx
            unfold cover_set at *
            aesop
          have h_zero : (MeasureTheory.Measure.hausdorffMeasure s) (cover_set E s 1 (1 / 2)) = 0 := by
            apply_rules [ lemma_1e ] <;> norm_num
          convert MeasureTheory.measure_mono_null h_subset h_zero using 1
          aesop
        · convert lemma_1e E s ( 1 / ( k : ℝ ) ) ( 1 - ( 1 / ( k : ℝ ) ) ) _ _ _ hs h_fin using 1
          · positivity
          · exact sub_pos_of_lt ( by simpa using inv_lt_one_of_one_lt₀ ( mod_cast Ne.bot_lt hk ) )
          · exact sub_lt_self _ ( by positivity )
      refine' MeasureTheory.measure_mono_null _ ( MeasureTheory.measure_iUnion_null fun k => h_bad_set_zero k )
      exact lemma_7_8 E s hs h_fin

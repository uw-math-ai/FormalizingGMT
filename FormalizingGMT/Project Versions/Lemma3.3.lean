/-
This is the full version of Lemma 3.3. There needs to be substantial edits.
-Match definitions to Mathlib
-Proof Golf
-/


import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Definition of Hausdorff content at scale delta.
-/
def hausdorffContent {X : Type*} [EMetricSpace X] (d : ℝ) (δ : ℝ) (s : Set X) : ENNReal :=
  ⨅ (t : ℕ → Set X) (_ : s ⊆ ⋃ n, t n) (_ : ∀ n, EMetric.diam (t n) ≤ ENNReal.ofReal δ),
    ∑' n, (EMetric.diam (t n)) ^ d

/-
Definition of the set E(δ, τ).
-/
def E_delta_tau {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (δ : ℝ) (τ : ℝ) : Set X :=
  {x ∈ E | ∀ C, x ∈ C → EMetric.diam C ≤ ENNReal.ofReal δ →
    MeasureTheory.Measure.hausdorffMeasure s (C ∩ E) ≤ ENNReal.ofReal τ * (EMetric.diam C) ^ s}

/-
We first show that if $0<\delta\leq\delta'$, then $E(\delta',1-\delta')\subset E(\delta,1-\delta)$.
-/
lemma E_delta_tau_nested {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {E : Set X} {s : ℝ} {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ δ') :
    E_delta_tau E s δ' (1 - δ') ⊆ E_delta_tau E s δ (1 - δ) := by
      intro x hx;
      refine' ⟨ hx.1, fun C hx' hx'' => _ ⟩;
      refine' le_trans ( hx.2 C hx' _ ) _;
      · exact le_trans hx'' ( ENNReal.ofReal_le_ofReal hδ' );
      · gcongr

/-
Hausdorff content is less than or equal to Hausdorff measure.
-/
def hContent {X : Type*} [EMetricSpace X] (d : ℝ) (δ : ℝ) (s : Set X) : ENNReal :=
  ⨅ (t : ℕ → Set X) (_ : s ⊆ ⋃ n, t n) (_ : ∀ n, EMetric.diam (t n) ≤ ENNReal.ofReal δ),
    ∑' n, ⨆ (_ : (t n).Nonempty), (EMetric.diam (t n)) ^ d

lemma hContent_le_hausdorffMeasure {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {d : ℝ} {δ : ℝ} {s : Set X} (hδ : 0 < δ) :
    hContent d δ s ≤ MeasureTheory.Measure.hausdorffMeasure d s := by
      -- By definition of the Hausdorff measure, we know that for any $r > 0$, the content at scale $r$ is less than or equal to the Hausdorff measure. Therefore, we can choose $r = \delta$.
      have h_content_le_measure : ∀ r > 0, hContent d r s ≤ (MeasureTheory.Measure.hausdorffMeasure d) s := by
        intro r hr;
        rw [ MeasureTheory.Measure.hausdorffMeasure_apply ];
        refine' le_ciSup _ ( ENNReal.ofReal r ) |> le_trans _;
        · simp +decide [ hContent, ENNReal.ofReal_pos, hr ];
        · exact?;
      exact h_content_le_measure δ hδ

/-
Covering estimate for E(delta, tau).
-/
lemma lemma_1a_fix {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (δ : ℝ) (τ : ℝ) (hδ : 0 < δ) (hτ : 0 < τ) (hτ1 : τ < 1)
    (C : ℕ → Set X)
    (h_cover : E_delta_tau E s δ τ ⊆ ⋃ i, C i)
    (h_diam : ∀ i, EMetric.diam (C i) ≤ ENNReal.ofReal δ)
    (h_inter : ∀ i, (C i ∩ E_delta_tau E s δ τ).Nonempty) :
    hContent s δ (E_delta_tau E s δ τ) ≤ ENNReal.ofReal τ * ∑' i, (EMetric.diam (C i)) ^ s := by
      have := h_inter 0;
      revert this;
      -- Since $x_i \in C_i$, we have $C_i \subset B(x_i,\operatorname{diam} C_i)$.
      intro h_nonempty
      have h_subset : ∀ i, MeasureTheory.Measure.hausdorffMeasure s (C i ∩ E_delta_tau E s δ τ) ≤ ENNReal.ofReal τ * (EMetric.diam (C i)) ^ s := by
        intro i
        obtain ⟨x_i, hx_i⟩ : ∃ x_i, x_i ∈ C i ∩ E_delta_tau E s δ τ := h_inter i;
        have := hx_i.2;
        exact le_trans ( MeasureTheory.measure_mono ( Set.inter_subset_inter_right _ ( show E_delta_tau E s δ τ ⊆ E from fun x hx => hx.1 ) ) ) ( this.2 _ hx_i.1 ( h_diam i ) );
      -- Using sub-additivity of $\mathcal{H}^s_\delta$, it follows that
      have h_subadd : MeasureTheory.Measure.hausdorffMeasure s (E_delta_tau E s δ τ) ≤ ∑' i, MeasureTheory.Measure.hausdorffMeasure s (C i ∩ E_delta_tau E s δ τ) := by
        refine' le_trans ( MeasureTheory.measure_mono ( show E_delta_tau E s δ τ ⊆ ⋃ i, ( C i ∩ E_delta_tau E s δ τ ) from fun x hx => by have := h_cover hx; aesop ) ) ( MeasureTheory.measure_iUnion_le _ );
      refine' le_trans ( hContent_le_hausdorffMeasure hδ ) _;
      exact h_subadd.trans ( by rw [ ← ENNReal.tsum_mul_left ] ; exact ENNReal.tsum_le_tsum h_subset )

/-
Checking Encodable instances.
-/
#synth Encodable ℕ
#synth Encodable {n : ℕ // n > 5}

/-
Definition of modified cover.
-/
def modified_cover {X : Type*} [EMetricSpace X] (U : ℕ → Set X) (E : Set X) (x : X) (n : ℕ) : Set X :=
  if (U n ∩ E).Nonempty then U n else {x}

/-
The modified cover covers the intersection of E and the original cover.
-/
lemma modified_cover_subset {X : Type*} [EMetricSpace X] (U : ℕ → Set X) (E : Set X) (x : X) :
    E ∩ ⋃ n, U n ⊆ ⋃ k, modified_cover U E x k := by
      -- Take any $y \in E \cap \bigcup U_n �$.� Then $y \in E$ and there exists $k$ such that $ �y� \in U_k$.
      intro y hy
      obtain ⟨k, hk⟩ : ∃ k, y ∈ U k := by
        aesop;
      simp_all +decide [ Set.ext_iff, modified_cover ];
      exact ⟨ k, by rw [ if_pos ⟨ y, hk, hy.1 ⟩ ] ; exact hk ⟩

/-
The modified cover intersects E.
-/
lemma modified_cover_inter_nonempty {X : Type*} [EMetricSpace X] (U : ℕ → Set X) (E : Set X) (x : X) (hx : x ∈ E) :
    ∀ k, (modified_cover U E x k ∩ E).Nonempty := by
      unfold modified_cover;
      aesop

/-
The diameter of each set in the modified cover is bounded by the supremum of diameters in the original cover.
-/
lemma modified_cover_diam_le {X : Type*} [EMetricSpace X] (U : ℕ → Set X) (E : Set X) (x : X) (k : ℕ) :
    EMetric.diam (modified_cover U E x k) ≤ ⨆ n, EMetric.diam (U n) := by
      unfold modified_cover;
      split_ifs <;> [ exact le_ciSup ( show BddAbove ( Set.range fun n => EMetric.diam ( U n ) ) from ⟨ ⊤, Set.forall_mem_range.2 fun n => le_top ⟩ ) k; exact le_trans ( by simp +decide ) ( le_ciSup ( show BddAbove ( Set.range fun n => EMetric.diam ( U n ) ) from ⟨ ⊤, Set.forall_mem_range.2 fun n => le_top ⟩ ) k ) ]

/-
The sum of powers of diameters of the modified cover is less than or equal to that of the original cover.
-/
lemma modified_cover_sum_le {X : Type*} [EMetricSpace X] {s : ℝ} (hs : 0 < s)
    (U : ℕ → Set X) (E : Set X) (x : X) :
    ∑' k, (EMetric.diam (modified_cover U E x k))^s ≤ ∑' n, (EMetric.diam (U n))^s := by
      apply_rules [ ENNReal.tsum_le_tsum ];
      intro n; by_cases h : Set.Nonempty ( U n ∩ E ) <;> simp +decide [ *, modified_cover ] ;

/-
Helper lemma for 1c: bound for a specific cover.
-/
lemma lemma_1c_helper {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (δ : ℝ) (τ : ℝ) (hs : 0 < s)
    (h_impl : ∀ (C : ℕ → Set X),
      (E_delta_tau E s δ τ ⊆ ⋃ i, C i) →
      (∀ i, EMetric.diam (C i) ≤ ENNReal.ofReal δ) →
      (∀ i, (C i ∩ E_delta_tau E s δ τ).Nonempty) →
      hContent s δ (E_delta_tau E s δ τ) ≤ ENNReal.ofReal τ * ∑' i, (EMetric.diam (C i)) ^ s)
    (C : ℕ → Set X)
    (h_cover : E_delta_tau E s δ τ ⊆ ⋃ i, C i)
    (h_diam : ∀ i, EMetric.diam (C i) ≤ ENNReal.ofReal δ)
    (x : X) (hx : x ∈ E_delta_tau E s δ τ) :
    hContent s δ (E_delta_tau E s δ τ) ≤ ENNReal.ofReal τ * ∑' i, (EMetric.diam (C i)) ^ s := by
      -- Let's define the modified cover $C'$.
      set C' : ℕ → Set X := fun i => modified_cover C (E_delta_tau E s δ τ) x i;
      refine' le_trans ( h_impl C' _ _ _ ) ( mul_le_mul_left' ( modified_cover_sum_le hs C _ _ ) _ );
      · exact fun y hy => modified_cover_subset C _ _ |> fun h => h <| Set.mem_inter hy ( h_cover hy );
      · intro i;
        refine' le_trans ( modified_cover_diam_le _ _ _ _ ) _;
        exact ciSup_le h_diam;
      · exact?

/-
The sum of powers of diameters is equal to the term used in hContent definition.
-/
lemma sum_eq_content_term {X : Type*} [EMetricSpace X] {s : ℝ} (hs : 0 < s) (C : ℕ → Set X) :
    ∑' i, (EMetric.diam (C i)) ^ s = ∑' i, ⨆ (_ : (C i).Nonempty), (EMetric.diam (C i)) ^ s := by
      refine' tsum_congr fun i => _;
      by_cases hi : ( C i ).Nonempty <;> simp +decide [ hi ];
      simp_all +decide [ Set.not_nonempty_iff_eq_empty.mp hi ]


/-
The Hausdorff content of E(delta, tau) satisfies a contraction inequality.
-/
lemma lemma_1c {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (δ : ℝ) (τ : ℝ) (hδ : 0 < δ) (hτ : 0 < τ) (hτ1 : τ < 1) (hs : 0 < s) :
    hContent s δ (E_delta_tau E s δ τ) ≤ ENNReal.ofReal τ * hContent s δ (E_delta_tau E s δ τ) := by
      by_cases h : E_delta_tau E s δ τ = ∅;
      · simp +decide [ h, hContent ];
        refine' le_trans _ ( mul_le_mul_left' ( le_iInf fun t => le_iInf fun ht => _ ) _ );
        rotate_left;
        exact 0;
        · exact zero_le _;
        · refine' le_trans ( ciInf_le _ ( fun _ => ∅ ) ) _ <;> simp +decide;
      · -- By definition of Hausdorff content, it suffices to show that for any cover $C$ of $E_{\delta, \tau}$ with diameters $\le \delta$, we have $hContent \le \tau \sum diam(C_i)^s$.
        suffices h_suff : ∀ (C : ℕ → Set X),
            (E_delta_tau E s δ τ ⊆ ⋃ i, C i) →
            (∀ i, EMetric.diam (C i) ≤ ENNReal.ofReal δ) →
            hContent s δ (E_delta_tau E s δ τ) ≤ ENNReal.ofReal τ * ∑' i, (EMetric.diam (C i)) ^ s by
              refine' le_trans _ ( mul_le_mul_left' ( le_iInf fun C => _ ) _ );
              rotate_left;
              exact hContent s δ ( E_delta_tau E s δ τ );
              · refine' le_iInf fun hC => le_iInf fun hC' => _;
                refine' le_trans ( h_suff C hC hC' ) _;
                rw [ ← ENNReal.tsum_mul_left ];
                refine' ENNReal.tsum_le_tsum fun n => _;
                by_cases hn : ( C n ).Nonempty <;> simp +decide [ hn ];
                · exact mul_le_of_le_one_left ( by positivity ) ( ENNReal.ofReal_le_one.mpr hτ1.le );
                · simp_all +decide [ Set.not_nonempty_iff_eq_empty.mp hn ];
              · refine' le_trans ( le_of_eq _ ) ( mul_le_mul_left' ( le_iInf fun C => _ ) _ );
                rotate_left;
                exact ( ENNReal.ofReal τ ) ⁻¹ * hContent s δ ( E_delta_tau E s δ τ );
                · by_cases hC : E_delta_tau E s δ τ ⊆ ⋃ n, C n <;> by_cases hC' : ∀ n, EMetric.diam ( C n ) ≤ ENNReal.ofReal δ <;> simp +decide [ hC, hC' ];
                  rw [ ENNReal.inv_mul_le_iff ];
                  · convert h_suff C hC hC' using 1;
                    congr! 2;
                    ext n; by_cases hn : ( C n ).Nonempty <;> simp +decide [ hn ] ;
                    rw [ show C n = ∅ by exact Set.not_nonempty_iff_eq_empty.mp hn, EMetric.diam_empty, ENNReal.zero_rpow_of_pos hs ];
                  · positivity;
                  · exact ENNReal.ofReal_ne_top;
                · rw [ ← mul_assoc, ENNReal.mul_inv_cancel ( by aesop ) ( by aesop ), one_mul ];
        -- Let $x \in E_{\delta, \tau}$.
        obtain ⟨x, hx⟩ : ∃ x, x ∈ E_delta_tau E s δ τ := by
          exact Set.nonempty_iff_ne_empty.2 h;
        intro C hC hC';
        apply lemma_1c_helper;
        exacts [ hs, fun C hC hC' hC'' => lemma_1a_fix E s δ τ hδ hτ hτ1 C hC hC' hC'', hC, hC', hx ]

/-
If the Hausdorff content is finite, it must be zero.
-/
lemma lemma_1d {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (δ : ℝ) (τ : ℝ) (hδ : 0 < δ) (hτ : 0 < τ) (hτ1 : τ < 1) (hs : 0 < s)
    (h_fin : hContent s δ (E_delta_tau E s δ τ) ≠ ⊤) :
    hContent s δ (E_delta_tau E s δ τ) = 0 := by
      -- By `lemma_1c`, we have $hContent \le \tau * hContent$.
      have h_le : (hContent s δ (E_delta_tau E s δ τ)) ≤ ENNReal.ofReal τ * (hContent s δ (E_delta_tau E s δ τ)) := by
        convert lemma_1c E s δ τ hδ hτ hτ1 hs using 1;
      by_cases h : hContent s δ ( E_delta_tau E s δ τ ) = 0 <;> simp_all +decide [ ENNReal.ofReal ];
      rw [ ← ENNReal.toReal_le_toReal ] at h_le <;> norm_num at *;
      · exact absurd h_le ( by rw [ max_eq_left hτ.le ] ; nlinarith [ show 0 < ( hContent s δ ( E_delta_tau E s δ τ ) |> ENNReal.toReal ) from ENNReal.toReal_pos h h_fin ] );
      · exact h_fin;
      · exact ENNReal.mul_ne_top ENNReal.coe_ne_top h_fin

/-
If the Hausdorff content is zero at some scale, it is zero at any scale.
-/
lemma hContent_zero_mono {X : Type*} [EMetricSpace X]
    {s : ℝ} {δ δ' : ℝ} {E : Set X} (hs : 0 < s) (hδ : 0 < δ) (hδ' : 0 < δ')
    (h : hContent s δ E = 0) :
    hContent s δ' E = 0 := by
      refine' le_antisymm ( le_trans ( le_of_eq ( Eq.symm _ ) ) ( le_of_forall_gt_imp_ge_of_dense _ ) ) bot_le;
      exact?;
      intro ε hε;
      -- Choose η such that η < ε and η^(1/s) ≤ δ'.
      obtain ⟨η, hη₁, hη₂⟩ : ∃ η : ENNReal, 0 < η ∧ η < ε ∧ η^(1 / s) ≤ ENNReal.ofReal δ' := by
        -- Since $\eta^{1/s} \leq \delta'$, we can choose $\eta$ such that $\eta \leq (\delta')^s$.
        obtain ⟨η, hη₁, hη₂⟩ : ∃ η : ENNReal, 0 < η ∧ η < ε ∧ η ≤ (ENNReal.ofReal δ') ^ s := by
          by_cases hη : ENNReal.ofReal δ' ^ s < ε;
          · exact ⟨ ENNReal.ofReal δ' ^ s, by positivity, hη, le_rfl ⟩;
          · rcases ENNReal.lt_iff_exists_nnreal_btwn.mp hε with ⟨ η, hη₁, hη₂ ⟩;
            exact ⟨ η, by simpa using hη₁, hη₂, le_trans ( by simpa using hη₂.le ) ( le_of_not_gt hη ) ⟩;
        refine' ⟨ η, hη₁, hη₂.1, _ ⟩;
        exact le_trans ( ENNReal.rpow_le_rpow hη₂.2 ( by positivity ) ) ( by rw [ ← ENNReal.rpow_mul, mul_one_div_cancel hs.ne', ENNReal.rpow_one ] );
      -- Since `hContent s δ E = 0`, for any `η > 0`, there exists a cover `{U_i}` such that `diam(U_i) ≤ δ` and `∑ diam(U_i)^s < η`.
      obtain ⟨U, hU₁, hU₂⟩ : ∃ U : ℕ → Set X, E ⊆ ⋃ i, U i ∧ ∀ i, EMetric.diam (U i) ≤ ENNReal.ofReal δ ∧ ∑' i, (EMetric.diam (U i)) ^ s < η := by
        contrapose! h;
        refine' ne_of_gt ( lt_of_lt_of_le hη₁ ( le_iInf fun U => le_iInf fun hU => le_iInf fun hU' => _ ) );
        obtain ⟨ i, hi ⟩ := h U hU;
        refine' le_trans ( hi ( hU' i ) ) _;
        refine' ENNReal.tsum_le_tsum fun n => _;
        by_cases h : ( U n ).Nonempty <;> simp +decide [ h ];
        simp_all +decide [ Set.not_nonempty_iff_eq_empty.mp h ];
      -- Since `η^(1/s) ≤ δ'`, for each `i`, `diam(U_i)^s ≤ ∑ diam(U_j)^s < η`, so `diam(U_i) < η^(1/s) ≤ δ'`.
      have h_diam_le : ∀ i, EMetric.diam (U i) ≤ ENNReal.ofReal δ' := by
        intro i
        have h_diam_le_i : (EMetric.diam (U i)) ^ s ≤ ∑' j, (EMetric.diam (U j)) ^ s := by
          exact?;
        refine' le_trans _ hη₂.2;
        exact le_trans ( by rw [ ← ENNReal.rpow_mul, mul_one_div_cancel hs.ne', ENNReal.rpow_one ] ) ( ENNReal.rpow_le_rpow ( h_diam_le_i.trans ( le_of_lt ( hU₂ i |>.2 ) ) ) ( by positivity ) );
      refine' le_trans ( ciInf_le _ _ ) _;
      exact ⟨ 0, Set.forall_mem_range.2 fun _ => zero_le _ ⟩;
      exact U;
      simp_all +decide [ ciInf_eq_ite ];
      refine' le_trans _ hη₂.1.le;
      refine' le_trans _ ( le_of_lt ( hU₂ 0 |>.2 ) );
      refine' ENNReal.tsum_le_tsum fun i => _;
      by_cases hi : ( U i ).Nonempty <;> simp +decide [ hi ]

/-
If the Hausdorff content is zero, the Hausdorff measure is zero.
-/
lemma hContent_zero_implies_hausdorffMeasure_zero {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {s : ℝ} {δ : ℝ} {E : Set X} (hs : 0 < s) (hδ : 0 < δ)
    (h : hContent s δ E = 0) :
    MeasureTheory.Measure.hausdorffMeasure s E = 0 := by
      -- By Lemma 2, since the Hausdorff content of E at scale δ is zero, the Hausdorff measure of E at scale δ' is also zero.
      have h_zero_content : ∀ δ' > 0, hContent s δ' E = 0 := by
        exact?;
      simp +decide [ MeasureTheory.Measure.hausdorffMeasure_apply, h_zero_content ];
      intro i hi; specialize h_zero_content ( ENNReal.toReal i ) ; rcases eq_or_ne i ⊤ with rfl | hi' <;> simp_all +decide ;
      · refine' le_antisymm _ _;
        · refine' le_trans _ ( le_of_eq h );
          refine' le_iInf fun t => le_iInf fun ht => le_iInf fun h => _;
          exact iInf_le_of_le t ( iInf_le_of_le ht le_rfl );
        · exact zero_le _;
      · convert h_zero_content ( ENNReal.toReal_pos hi.ne' hi' ) using 1;
        unfold hContent; aesop;

/-
If the Hausdorff measure of E is finite, then the Hausdorff measure of E(delta, tau) is zero.
-/
lemma lemma_1e {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (δ : ℝ) (τ : ℝ) (hδ : 0 < δ) (hτ : 0 < τ) (hτ1 : τ < 1) (hs : 0 < s)
    (h_fin : MeasureTheory.Measure.hausdorffMeasure s E ≠ ⊤) :
    MeasureTheory.Measure.hausdorffMeasure s (E_delta_tau E s δ τ) = 0 := by
      convert hContent_zero_implies_hausdorffMeasure_zero hs hδ _;
      convert lemma_1d E s δ τ hδ hτ hτ1 hs _;
      refine' ne_of_lt ( lt_of_le_of_lt _ ( lt_top_iff_ne_top.mpr h_fin ) );
      refine' le_trans _ ( MeasureTheory.measure_mono _ );
      convert hContent_le_hausdorffMeasure hδ using 1;
      exact fun x hx => hx.1

/-
The set of points where the density is consistently low has measure zero.
-/
def E_star_tau {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (τ : ℝ) : Set X :=
  ⋃ n : ℕ, E_delta_tau E s (1 / (n + 1)) τ

lemma measure_E_star_tau_eq_zero {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ < 1) (hs : 0 < s)
    (h_fin : MeasureTheory.Measure.hausdorffMeasure s E ≠ ⊤) :
    MeasureTheory.Measure.hausdorffMeasure s (E_star_tau E s τ) = 0 := by
      -- Apply `lemma_1e` to conclude that the Hausdorff measure of `E_star_tau E s τ` is zero.
      have h_star_zero : ∀ δ > 0, (MeasureTheory.Measure.hausdorffMeasure s) (E_delta_tau E s δ τ) = 0 := by
        exact?;
      convert MeasureTheory.measure_mono_null ( fun a ha => ?_ ) ( MeasureTheory.measure_iUnion_null fun n : ℕ => h_star_zero ( 1/ ( n+1 ) ) <| by positivity ) using 1;
      grind

/-
Checking the name of Hausdorff measure.
-/
#check MeasureTheory.Measure.hausdorffMeasure

/-
Definitions of density ratio and upper density.
-/
def density_ratio {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (E : Set X) (s : ℝ) (x : X) (r : ℝ) : ENNReal :=
  MeasureTheory.Measure.hausdorffMeasure s (E ∩ EMetric.ball x (ENNReal.ofReal r)) / (ENNReal.ofReal (2 * r)) ^ s

def upper_density {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] (E : Set X) (s : ℝ) (x : X) : ENNReal :=
  Filter.limsup (fun r => density_ratio E s x r) (nhdsWithin 0 (Set.Ioi 0))

/-
The set of points in E where the upper density is less than 1/2^s.
-/
def bad_set {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] (E : Set X) (s : ℝ) : Set X :=
  {x ∈ E | upper_density E s x < ENNReal.ofReal (1 / (2 : ℝ) ^ s)}

/-
Lemma 7.6: From small density to small density ratio. If the upper density is strictly less than 1/2^s, then the density ratio is uniformly bounded by (1-δ)/2^s for small r.
-/
lemma lemma_7_6 {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (x : X) (hx : x ∈ E)
    (h : upper_density E s x < ENNReal.ofReal (1 / (2 : ℝ) ^ s)) :
    ∃ δ > 0, ∀ r, 0 < r → r ≤ δ →
      density_ratio E s x r < ENNReal.ofReal ((1 - δ) / (2 : ℝ) ^ s) := by
        -- By Lemma 4.2, there exist ε > 0 and R > 0 such that for all r ∈ (0, R], density_ratio < 1/2^s - ε.
        obtain ⟨ε, hε_pos, R, hR_pos, hεR⟩ : ∃ ε > 0, ∃ R > 0, ∀ r : ℝ, 0 < r → r ≤ R → density_ratio E s x r < ENNReal.ofReal (1 / 2 ^ s) - ENNReal.ofReal ε := by
          obtain ⟨ε, hε⟩ : ∃ ε > 0, upper_density E s x < ENNReal.ofReal (1 / 2 ^ s) - ENNReal.ofReal ε := by
            rcases ENNReal.lt_iff_exists_add_pos_lt.mp h with ⟨ ε, hε_pos, hε ⟩;
            refine' ⟨ ε, hε_pos, _ ⟩;
            rw [ lt_tsub_iff_right ] ; aesop;
          -- By definition of upper density, there exists R > 0 such that for all r ∈ (0, R], density_ratio < 1/2^s - ε.
          obtain ⟨R, hR_pos, hR⟩ : ∃ R > 0, ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), density_ratio E s x r < ENNReal.ofReal (1 / 2 ^ s) - ENNReal.ofReal ε := by
            contrapose! hε;
            intro hε_pos;
            refine' le_csInf _ _;
            · refine' ⟨ ⊤, _ ⟩ ; simp +decide;
            · intro b hb;
              contrapose! hε;
              rcases ENNReal.lt_iff_exists_real_btwn.mp hε with ⟨ c, hc ⟩;
              exact ⟨ 1, zero_lt_one, by filter_upwards [ hb ] with r hr using lt_of_le_of_lt hr hc.2.1 |> lt_of_lt_of_le <| le_of_lt hc.2.2 ⟩;
          rcases ( Metric.mem_nhdsWithin_iff.mp hR ) with ⟨ δ, δpos, hδ ⟩;
          exact ⟨ ε, hε.1, δ / 2, half_pos δpos, fun r hr₁ hr₂ => hδ ⟨ mem_ball_zero_iff.mpr ( abs_lt.mpr ⟨ by linarith, by linarith ⟩ ), hr₁ ⟩ ⟩;
        -- Let δ = min{R, 2^s * ε}. Then δ/2^s ≤ ε, and for all r ∈ (0, δ] we have r ∈ (0, R], so density_ratio < 1/2^s - ε ≤ (1 - δ)/2^s.
        use min R (2 ^ s * ε) / 2; (
        refine' ⟨ by positivity, fun r hr₁ hr₂ => lt_of_lt_of_le ( hεR r hr₁ ( hr₂.trans ( by linarith [ min_le_left R ( 2 ^ s * ε ) ] ) ) ) _ ⟩;
        rw [ ← ENNReal.ofReal_sub ];
        · exact ENNReal.ofReal_le_ofReal ( by ring_nf; nlinarith [ min_le_left R ( 2 ^ s * ε ), min_le_right R ( 2 ^ s * ε ), Real.rpow_pos_of_pos zero_lt_two s, mul_inv_cancel₀ ( ne_of_gt ( Real.rpow_pos_of_pos zero_lt_two s ) ) ] );
        · positivity)

/-
Lemma 7.7: Bound on measure of intersection with C (strict diameter version).
-/
lemma lemma_7_7 {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (C : Set X) (x : X) (δ : ℝ)
    (hs : 0 < s) (hδ : 0 < δ) (hx : x ∈ E ∩ C) (h_diam : EMetric.diam C < ENNReal.ofReal δ)
    (h_dens : ∀ r, 0 < r → r ≤ δ → density_ratio E s x r < ENNReal.ofReal ((1 - δ) / (2 : ℝ) ^ s)) :
    MeasureTheory.Measure.hausdorffMeasure s (C ∩ E) ≤ ENNReal.ofReal (1 - δ) * (EMetric.diam C) ^ s := by
      -- Applying the definition of density ratio and the hypothesis h_dens, we get that for any $r$ such that $d < r \leq \delta$, $H^s(ball(x, r) \cap E) < (1 - \delta) * r^s$.
      have h_ball : ∀ r, EMetric.diam C < ENNReal.ofReal r → r ≤ δ → (MeasureTheory.Measure.hausdorffMeasure s (EMetric.ball x (ENNReal.ofReal r) ∩ E)) < ENNReal.ofReal (1 - δ) * (ENNReal.ofReal r) ^ s := by
        intro r hr₁ hr₂
        have h_ball : (MeasureTheory.Measure.hausdorffMeasure s (EMetric.ball x (ENNReal.ofReal r) ∩ E)) / (ENNReal.ofReal (2 * r)) ^ s < ENNReal.ofReal ((1 - δ) / 2 ^ s) := by
          convert h_dens r ( lt_of_le_of_ne ( le_of_not_gt fun h => by rw [ ENNReal.ofReal_eq_zero.mpr h.le ] at hr₁; exact hr₁.not_ge <| by simp +decide ) <| Ne.symm <| by rintro rfl; exact hr₁.not_le <| by simp +decide ) hr₂ using 1;
          unfold density_ratio;
          rw [ Set.inter_comm ];
        contrapose! h_ball;
        rw [ ENNReal.le_div_iff_mul_le ];
        · convert h_ball using 1;
          rw [ ENNReal.ofReal_div_of_pos ( by positivity ), ENNReal.ofReal_mul ( by positivity ) ];
          rw [ ENNReal.mul_rpow_of_nonneg _ _ ( by positivity ), ENNReal.ofReal_rpow_of_pos ( by positivity ) ] ; ring;
          rw [ ENNReal.div_mul_cancel ] <;> norm_num [ Real.rpow_pos_of_pos ] ; ring;
        · simp +zetaDelta at *;
          exact Or.inl ⟨ fun h => False.elim <| hr₁.not_le <| by simp +decide [ h, ENNReal.ofReal_eq_zero.mpr h ], fun h => False.elim <| absurd h <| by simp +decide [ ENNReal.mul_eq_top ] ⟩;
        · exact Or.inl ( ENNReal.rpow_ne_top_of_nonneg hs.le ( ENNReal.ofReal_ne_top ) );
      have h_inf : ∀ r, EMetric.diam C < ENNReal.ofReal r → r ≤ δ → (MeasureTheory.Measure.hausdorffMeasure s (C ∩ E)) ≤ ENNReal.ofReal (1 - δ) * (ENNReal.ofReal r) ^ s := by
        intro r hr₁ hr₂
        have h_subset : C ∩ E ⊆ EMetric.ball x (ENNReal.ofReal r) ∩ E := by
          intro y hy;
          exact ⟨ lt_of_le_of_lt ( EMetric.edist_le_diam_of_mem hy.1 hx.2 ) hr₁, hy.2 ⟩;
        exact le_trans ( MeasureTheory.measure_mono h_subset ) ( le_of_lt ( h_ball r hr₁ hr₂ ) );
      -- Taking the infimum over $r \in (d, \delta]$, we get $H^s(C \cap E) \leq (1 - \delta) * d^s$.
      have h_inf : (MeasureTheory.Measure.hausdorffMeasure s (C ∩ E)) ≤ ENNReal.ofReal (1 - δ) * (⨅ r ∈ Set.Ioc (EMetric.diam C).toReal δ, (ENNReal.ofReal r) ^ s) := by
        rw [ ENNReal.mul_iInf ];
        · refine' le_iInf fun r => _;
          by_cases hr : r ∈ Set.Ioc (EMetric.diam C).toReal δ <;> simp_all +decide;
          · refine' h_inf r _ hr.2;
            rw [ ENNReal.lt_ofReal_iff_toReal_lt ] <;> aesop;
          · by_cases h : ENNReal.ofReal ( 1 - δ ) = 0 <;> simp_all +decide;
            grind;
        · aesop;
      refine' le_trans h_inf ( mul_le_mul_left' _ _ );
      have h_inf : Filter.Tendsto (fun r => (ENNReal.ofReal r) ^ s) (nhdsWithin (EMetric.diam C).toReal (Set.Ioi (EMetric.diam C).toReal)) (nhds ((EMetric.diam C) ^ s)) := by
        have h_inf : Filter.Tendsto (fun r => ENNReal.ofReal r) (nhdsWithin (EMetric.diam C).toReal (Set.Ioi (EMetric.diam C).toReal)) (nhds (EMetric.diam C)) := by
          convert ENNReal.tendsto_ofReal ( Filter.tendsto_id.mono_left inf_le_left ) using 1;
          rw [ ENNReal.ofReal_toReal ];
          exact ne_of_lt ( lt_of_lt_of_le h_diam ( le_top ) );
        exact ENNReal.continuous_rpow_const.tendsto _ |> Filter.Tendsto.comp <| h_inf;
      refine' le_of_tendsto_of_tendsto tendsto_const_nhds h_inf _;
      filter_upwards [ self_mem_nhdsWithin, Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, show ( EMetric.diam C |> ENNReal.toReal ) < δ from by rw [ ← ENNReal.toReal_ofReal hδ.le ] ; exact ENNReal.toReal_strict_mono ( by aesop ) h_diam ⟩ ] with r hr₁ hr₂;
      exact iInf₂_le r ⟨ hr₁, hr₂.2.le ⟩

/-
Lemma 7.8: The bad set is contained in a countable union of E(δ, τ) sets.
-/
lemma lemma_7_8 {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (hs : 0 < s)
    (h_fin : MeasureTheory.Measure.hausdorffMeasure s E ≠ ⊤) :
    {x ∈ E | upper_density E s x < ENNReal.ofReal (1 / 2 ^ s)} ⊆ ⋃ (k : ℕ+), E_delta_tau E s (1 / (k : ℝ)) (1 - 1 / (k : ℝ)) := by
      intro x hx; obtain ⟨ δ, hδ_pos, hδ ⟩ := lemma_7_6 E s x hx.1 hx.2; simp +decide [ E_delta_tau ] ; (
      obtain ⟨ k, hk ⟩ := exists_nat_one_div_lt hδ_pos;
      use hx.1, ⟨ k + 1, Nat.succ_pos k ⟩;
      intro C hx_C hC_diam
      have hC_diam_lt : EMetric.diam C < ENNReal.ofReal δ := by
        have hC_diam_lt : EMetric.diam C ≤ 1 / (k + 1 : ENNReal) := by
          rw [ ENNReal.le_div_iff_mul_le ] <;> aesop;
        refine' lt_of_le_of_lt hC_diam_lt _;
        rw [ ENNReal.lt_ofReal_iff_toReal_lt ] <;> aesop;
      have := lemma_7_7 E s C x δ hs hδ_pos ⟨ hx.1, hx_C ⟩ hC_diam_lt ( fun r hr hr' => hδ r hr hr' );
      refine' le_trans this _;
      gcongr;
      simpa using hk.le);

/-
Main Theorem: The set of points where the upper density is less than 1/2^s has Hausdorff measure 0.
-/
theorem main_theorem {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (E : Set X) (s : ℝ) (hs : 0 < s)
    (h_fin : MeasureTheory.Measure.hausdorffMeasure s E ≠ ⊤) :
    MeasureTheory.Measure.hausdorffMeasure s {x ∈ E | upper_density E s x < ENNReal.ofReal (1 / 2 ^ s)} = 0 := by
      have h_bad_set_zero : ∀ k : ℕ+, (MeasureTheory.Measure.hausdorffMeasure s) (E_delta_tau E s (1 / (k : ℝ)) (1 - 1 / (k : ℝ))) = 0 := by
        intro k;
        by_cases hk : k = 1;
        · have h_subset : E_delta_tau E s 1 0 ⊆ E_delta_tau E s 1 (1 / 2) := by
            intro x hx; unfold E_delta_tau at *; aesop;
          have h_zero : (MeasureTheory.Measure.hausdorffMeasure s) (E_delta_tau E s 1 (1 / 2)) = 0 := by
            apply_rules [ lemma_1e ];
            · norm_num;
            · norm_num;
            · norm_num;
          convert MeasureTheory.measure_mono_null h_subset h_zero using 1 ; aesop;
        · convert lemma_1e E s ( 1 / ( k : ℝ ) ) ( 1 - ( 1 / ( k : ℝ ) ) ) _ _ _ hs h_fin using 1;
          · positivity;
          · exact sub_pos_of_lt ( by simpa using inv_lt_one_of_one_lt₀ ( mod_cast Ne.bot_lt hk ) );
          · exact sub_lt_self _ ( by positivity );
      refine' MeasureTheory.measure_mono_null _ ( MeasureTheory.measure_iUnion_null fun k => h_bad_set_zero k );
      exact?

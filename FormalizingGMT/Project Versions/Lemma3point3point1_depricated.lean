/-
This file contains Lemma 3.3.1 and its sublemmas. Initial version proved by Aristotle.


To-dos:
-Remove dependence on EMetric (move to Metric)
-Generalize where possible
-Remove unneccessary iterations provided by Aristotle
-Update things to work in latest version of Mathlib
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
Definitions of Hausdorff content and the low density subset E(δ, τ).
-/
open Set Filter MeasureTheory MeasureTheory.Measure TopologicalSpace ENNReal Metric

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

noncomputable def hausdorffContent (d : ℝ) (s : Set X) : ℝ≥0∞ :=
  OuterMeasure.mkMetric'.pre (fun t => (EMetric.diam t) ^ d) ⊤ s

noncomputable def lowDensitySubset (E : Set X) (s : ℝ) (δ : ℝ) (τ : ℝ≥0∞) : Set X :=
  {x ∈ E | ∀ r : ℝ, 0 < r → r ≤ δ → hausdorffContent s (E ∩ ball x r) ≤ τ * (ENNReal.ofReal r) ^ s}

/-
Local estimate for Lemma 1(a).
-/
lemma lemma_1a_local (E : Set X) (C : Set X) (x : X) (s : ℝ) (δ : ℝ) (τ : ℝ≥0∞)
    (hx : x ∈ C ∩ lowDensitySubset E s δ τ)
    (h_diam : EMetric.diam C < ENNReal.ofReal δ) :
    hausdorffContent s (C ∩ E) ≤ τ * (EMetric.diam C) ^ s := by
  by_contra h;
  -- Since $C$ is contained in $B(x, r)$ for any $r > \text{diam}(C)$, and $r \leq \delta$, we can choose $r$ such that $\text{diam}(C) < r \leq \delta$.
  obtain ⟨r, hr₁, hr₂⟩ : ∃ r : ℝ, EMetric.diam C < ENNReal.ofReal r ∧ ENNReal.ofReal r ≤ ENNReal.ofReal δ ∧ τ * (ENNReal.ofReal r) ^ s < hausdorffContent s (C ∩ E) := by
    -- Since $\text{diam}(C) < \delta$, we can choose $r$ such that $\text{diam}(C) < r \leq \delta$.
    obtain ⟨r, hr₁, hr₂⟩ : ∃ r : ℝ, EMetric.diam C < ENNReal.ofReal r ∧ ENNReal.ofReal r ≤ ENNReal.ofReal δ ∧ τ * (ENNReal.ofReal r) ^ s < hausdorffContent s (C ∩ E) := by
      have hr₃ : Filter.Tendsto (fun r : ℝ => τ * (ENNReal.ofReal r) ^ s) (nhdsWithin (ENNReal.toReal (EMetric.diam C)) (Set.Ioi (ENNReal.toReal (EMetric.diam C)))) (nhds (τ * (EMetric.diam C) ^ s)) := by
        refine' ENNReal.Tendsto.const_mul _ _;
        · refine' Filter.Tendsto.mono_left _ nhdsWithin_le_nhds;
          convert ENNReal.continuous_rpow_const.continuousAt.tendsto.comp ( ENNReal.continuous_ofReal.continuousAt ) using 1;
          rw [ ENNReal.ofReal_toReal ];
          aesop;
        · refine' Or.inl _;
          intro H; simp_all +decide [ ENNReal.rpow_eq_zero_iff ] ;
          cases' H with H H <;> simp_all +decide [ EMetric.diam ];
          refine' h _;
          rw [ show C ∩ E = { x } from _ ];
          · refine' le_antisymm _ _;
            · refine' le_trans ( ciInf_le _ _ ) _;
              exact ⟨ 0, Set.forall_mem_range.2 fun _ => zero_le _ ⟩;
              use fun _ => { x };
              simp +decide [ MeasureTheory.extend ];
              exact H.2;
            · exact zero_le _;
          · exact Set.eq_singleton_iff_unique_mem.mpr ⟨ ⟨ hx.1, hx.2.1 ⟩, fun y hy => H.1 _ hy.1 _ hx.1 ⟩
      have := hr₃.eventually ( gt_mem_nhds <| lt_of_not_ge h );
      have := this.and ( Ioo_mem_nhdsGT <| show ( EMetric.diam C |> ENNReal.toReal ) < δ from ?_ );
      · rcases this.exists with ⟨ r, hr₁, hr₂, hr₃ ⟩;
        refine' ⟨ r, _, _, hr₁ ⟩;
        · rw [ ENNReal.lt_ofReal_iff_toReal_lt ] <;> aesop;
        · exact ENNReal.ofReal_le_ofReal hr₃.le;
      · rw [ ENNReal.lt_ofReal_iff_toReal_lt ] at h_diam <;> aesop;
    use r;
  -- Since $C$ is contained in $B(x, r)$ for any $r > \text{diam}(C)$, and $r \leq \delta$, we have $C \cap E \subseteq E \cap B(x, r)$.
  have h_subset : C ∩ E ⊆ E ∩ ball x r := by
    intro y hy;
    refine' ⟨ hy.2, _ ⟩;
    refine' lt_of_le_of_lt _ ( ENNReal.lt_ofReal_iff_toReal_lt _ |>.1 hr₁ );
    · refine' le_trans _ ( ENNReal.toReal_mono _ <| EMetric.edist_le_diam_of_mem hy.1 hx.1 );
      · simp +decide [ edist_dist ];
      · aesop;
    · aesop;
  -- By definition of $lowDensitySubset$, we have $hausdorffContent s (E ∩ ball x r) ≤ τ * (ENNReal.ofReal r) ^ s$.
  have h_low_density : hausdorffContent s (E ∩ ball x r) ≤ τ * (ENNReal.ofReal r) ^ s := by
    cases' hx with hx₁ hx₂;
    cases' hr₂ with hr₂₁ hr₂₂;
    cases' hx₂ with hx₂₁ hx₂₂;
    apply hx₂₂;
    · exact not_le.mp fun hr₃ => by rw [ ENNReal.ofReal_eq_zero.mpr hr₃ ] at hr₁; exact absurd hr₁ ( by simp +decide ) ;
    · rw [ ENNReal.ofReal_le_ofReal_iff ] at hr₂₁ <;> norm_cast at *;
      exact le_of_not_gt fun h => by rw [ ENNReal.ofReal_eq_zero.mpr h.le ] at h_diam; exact h_diam.not_le ( zero_le _ ) ;
  refine' hr₂.2.not_le ( le_trans _ h_low_density );
  apply_rules [ OuterMeasure.mono ]

/-
Lemma 1(a) with strict inequality for diameters.
-/
lemma lemma_1a_strict (E : Set X) (s : ℝ) (δ : ℝ) (τ : NNReal) (C : ℕ → Set X)
    (hδ : 0 < δ) (hτ : 0 < τ ∧ τ < 1) (hs : 0 ≤ s)
    (h_cover : lowDensitySubset E s δ τ ⊆ ⋃ i, C i)
    (h_diam : ∀ i, EMetric.diam (C i) < ENNReal.ofReal δ)
    (h_inter : ∀ i, (C i ∩ lowDensitySubset E s δ τ).Nonempty) :
    hausdorffContent s (lowDensitySubset E s δ τ) ≤ τ * ∑' i, (EMetric.diam (C i)) ^ s := by
      -- For each $i$, pick $x_i \in C_i \cap E(\delta, \tau)$.
      have h_picks : ∀ i, ∃ x : X, x ∈ C i ∧ x ∈ lowDensitySubset E s δ (↑τ : ℝ≥0∞) := by
        exact fun i => h_inter i;
      -- For each $i$, pick $x_i \in C_i \cap E(\delta, \tau)$ and apply Lemma 1(a) to get $H_s(C_i \cap E(\delta, \tau)) \leq \tau \cdot \text{diam}(C_i)^s$.
      have h_hausdorff_le : ∀ i, hausdorffContent s (C i ∩ lowDensitySubset E s δ (↑τ : ℝ≥0∞)) ≤ (↑τ : ℝ≥0∞) * (EMetric.diam (C i)) ^ s := by
        intro i
        obtain ⟨x, hx_C, hx_E⟩ := h_picks i
        have h_hausdorff_le_i : hausdorffContent s (C i ∩ E) ≤ (↑τ : ℝ≥0∞) * (EMetric.diam (C i)) ^ s := by
          apply lemma_1a_local E (C i) x s δ (τ : ℝ≥0∞) ⟨hx_C, hx_E⟩ (h_diam i);
        refine' le_trans _ h_hausdorff_le_i;
        apply_rules [ OuterMeasure.mono ];
        exact Set.inter_subset_inter_right _ ( fun x hx => hx.1 );
      -- Summing over all $i$, we get $H_s(E(\delta, \tau)) \leq \sum_{i=1}^\infty H_s(C_i \cap E(\delta, \tau))$.
      have h_sum_le : hausdorffContent s (⋃ i, C i ∩ lowDensitySubset E s δ (↑τ : ℝ≥0∞)) ≤ ∑' i, hausdorffContent s (C i ∩ lowDensitySubset E s δ (↑τ : ℝ≥0∞)) := by
        convert MeasureTheory.measure_iUnion_le _;
        · infer_instance;
        · infer_instance;
      refine' le_trans _ ( le_trans h_sum_le _ );
      · exact MeasureTheory.measure_mono fun x hx => by rcases Set.mem_iUnion.1 ( h_cover hx ) with ⟨ i, hi ⟩ ; exact Set.mem_iUnion.2 ⟨ i, ⟨ hi, hx ⟩ ⟩ ;
      · rw [ ← ENNReal.tsum_mul_left ] ; exact ENNReal.tsum_le_tsum h_hausdorff_le;

/-
Corrected definitions of Hausdorff content and low density subset (handling empty sets).
-/
noncomputable def hausdorffContent_v2 (d : ℝ) (s : Set X) : ℝ≥0∞ :=
  OuterMeasure.mkMetric'.pre (fun t => if t.Nonempty then (EMetric.diam t) ^ d else 0) ⊤ s

noncomputable def lowDensitySubset_v2 (E : Set X) (s : ℝ) (δ : ℝ) (τ : ℝ≥0∞) : Set X :=
  {x ∈ E | ∀ r : ℝ, 0 < r → r ≤ δ → hausdorffContent_v2 s (E ∩ ball x r) ≤ τ * (ENNReal.ofReal r) ^ s}

/-
Local estimate for Lemma 1(a) (v2).
-/
lemma lemma_1a_local_v2 (E : Set X) (C : Set X) (x : X) (s : ℝ) (δ : ℝ) (τ : ℝ≥0∞)
    (hx : x ∈ C ∩ lowDensitySubset_v2 E s δ τ)
    (h_diam : EMetric.diam C < ENNReal.ofReal δ) :
    hausdorffContent_v2 s (C ∩ E) ≤ τ * (EMetric.diam C) ^ s := by
  have := @lemma_1a_local ( X := X ) ( E := E ) ( s := s ) ( δ := δ ) ( τ := τ );
  simp +zetaDelta at *;
  contrapose! this;
  refine' ⟨ inferInstance, inferInstance, inferInstance, C, x, hx.1, _, _, _ ⟩;
  · convert hx.2 using 1;
    ext; simp [lowDensitySubset, lowDensitySubset_v2];
    intro hx'; refine' forall_congr' fun r => forall_congr' fun hr => forall_congr' fun hr' => _; simp +decide [ hx', hausdorffContent, hausdorffContent_v2 ] ;
    simp +decide [ MeasureTheory.OuterMeasure.mkMetric'.pre ];
    rw [ MeasureTheory.OuterMeasure.boundedBy, MeasureTheory.OuterMeasure.boundedBy ];
    simp +decide [ MeasureTheory.extend ];
    congr! 3;
    exact funext fun _ => by split_ifs <;> simp +decide [ * ] ;
  · exact h_diam;
  · refine' this.trans_le _;
    refine' iInf_mono fun ε => iInf_mono' fun hε => _;
    simp +decide [ MeasureTheory.extend ];
    exact ⟨ hε, le_of_eq <| tsum_congr fun i => by aesop ⟩

/-
Lemma 1(a) (v2) with strict inequality for diameters.
-/
lemma lemma_1a_strict_v2 (E : Set X) (s : ℝ) (δ : ℝ) (τ : NNReal) (C : ℕ → Set X)
    (hδ : 0 < δ) (hτ : 0 < τ ∧ τ < 1) (hs : 0 ≤ s)
    (h_cover : lowDensitySubset_v2 E s δ τ ⊆ ⋃ i, C i)
    (h_diam : ∀ i, EMetric.diam (C i) < ENNReal.ofReal δ)
    (h_inter : ∀ i, (C i ∩ lowDensitySubset_v2 E s δ τ).Nonempty) :
    hausdorffContent_v2 s (lowDensitySubset_v2 E s δ τ) ≤ τ * ∑' i, (EMetric.diam (C i)) ^ s := by
  -- We use the subadditivity of hausdorffContent_v2:
  have h_subadd : hausdorffContent_v2 s (lowDensitySubset_v2 E s δ (τ : ℝ≥0∞)) ≤ ∑' i, hausdorffContent_v2 s (C i ∩ lowDensitySubset_v2 E s δ (τ : ℝ≥0∞)) := by
    have h_subadd : ∀ (S : ℕ → Set X), hausdorffContent_v2 s (⋃ i, S i) ≤ ∑' i, hausdorffContent_v2 s (S i) := by
      intro S;
      convert MeasureTheory.measure_iUnion_le _;
      · infer_instance;
      · infer_instance;
    refine' le_trans _ ( h_subadd _ );
    exact MeasureTheory.OuterMeasure.mono _ ( fun x hx => by have := h_cover hx; aesop );
  -- For each i, pick x_i ∈ C_i ∩ E(δ, τ).
  have h_pick : ∀ i, ∃ x_i ∈ C i ∩ lowDensitySubset_v2 E s δ (τ : ℝ≥0∞), hausdorffContent_v2 s (C i ∩ lowDensitySubset_v2 E s δ (τ : ℝ≥0∞)) ≤ hausdorffContent_v2 s (C i ∩ E) := by
    intro i
    obtain ⟨x_i, hx_i⟩ : ∃ x_i ∈ C i ∩ lowDensitySubset_v2 E s δ (τ : ℝ≥0∞), True := by
      exact Exists.elim ( h_inter i ) fun x hx => ⟨ x, hx, trivial ⟩;
    refine' ⟨ x_i, hx_i.1, _ ⟩;
    apply_rules [ OuterMeasure.mono ];
    exact Set.inter_subset_inter_right _ ( fun x hx => hx.1 );
  -- Apply lemma_1a_local_v2 to get H(C_i ∩ E) ≤ τ * diam(C_i)^s.
  have h_local : ∀ i, hausdorffContent_v2 s (C i ∩ E) ≤ τ * (EMetric.diam (C i)) ^ s := by
    intro i
    obtain ⟨x_i, hx_i⟩ := h_pick i;
    convert lemma_1a_local_v2 E ( C i ) x_i s δ τ hx_i.1 ( h_diam i ) using 1;
  exact h_subadd.trans ( by rw [ ← ENNReal.tsum_mul_left ] ; exact ENNReal.tsum_le_tsum fun i => le_trans ( h_pick i |> Classical.choose_spec |> And.right ) ( h_local i ) )

/-
Existence of a cover approximating the Hausdorff measure with small diameters (handling empty sets).
-/
lemma lemma_approx_cover_v2 (S : Set X) (s : ℝ) (δ : ℝ) (ε : ℝ≥0∞)
    (hs : 0 ≤ s) (hδ : 0 < δ) (hε : 0 < ε) (h_fin : hausdorffMeasure s S ≠ ⊤) :
    ∃ C : ℕ → Set X, (S ⊆ ⋃ i, C i) ∧
      (∀ i, EMetric.diam (C i) < ENNReal.ofReal δ) ∧
      (∑' i, if (C i).Nonempty then (EMetric.diam (C i)) ^ s else 0) ≤ hausdorffMeasure s S + ε := by
  have := MeasureTheory.Measure.hausdorffMeasure_apply s S;
  contrapose! this;
  refine' ne_of_lt ( lt_of_lt_of_le _ ( le_iSup₂_of_le ( ENNReal.ofReal δ / 2 ) ( by simp +decide [ hδ ] ) _ ) );
  exact ENNReal.lt_add_right h_fin hε.ne';
  refine' le_iInf fun t => le_iInf fun ht => le_iInf fun ht' => _;
  refine' le_trans ( le_of_lt ( this t ht _ ) ) _;
  · exact fun n => lt_of_le_of_lt ( ht' n ) ( ENNReal.half_lt_self ( by simp +decide [ hδ ] ) ( by simp +decide [ hδ ] ) );
  · refine' ENNReal.tsum_le_tsum fun n => _;
    split_ifs <;> simp +decide [ * ]

/-
Lemma 1(a) (v3): Covering estimate handling non-intersecting sets.
-/
lemma lemma_1a_strict_v3 (E : Set X) (s : ℝ) (δ : ℝ) (τ : NNReal) (C : ℕ → Set X)
    (hδ : 0 < δ) (hτ : 0 < τ ∧ τ < 1) (hs : 0 ≤ s)
    (h_cover : lowDensitySubset_v2 E s δ τ ⊆ ⋃ i, C i)
    (h_diam : ∀ i, EMetric.diam (C i) < ENNReal.ofReal δ) :
    hausdorffContent_v2 s (lowDensitySubset_v2 E s δ τ) ≤ τ * ∑' i, if (C i ∩ lowDensitySubset_v2 E s δ τ).Nonempty then (EMetric.diam (C i)) ^ s else 0 := by
  -- Applying the definition of Hausdorff content and the fact that $LowDensitySubset_v2 E s δ τ ⊆ ⋃ i, C i$, we get:
  have h_subset : hausdorffContent_v2 s (lowDensitySubset_v2 E s δ τ) ≤ ∑' i, (hausdorffContent_v2 s (C i ∩ lowDensitySubset_v2 E s δ τ)) := by
    refine' le_trans _ ( MeasureTheory.measure_iUnion_le _ );
    refine' le_trans _ ( MeasureTheory.OuterMeasure.mono _ _ );
    exact?;
    exact fun x hx => by rcases Set.mem_iUnion.1 ( h_cover hx ) with ⟨ i, hi ⟩ ; exact Set.mem_iUnion.2 ⟨ i, hi, hx ⟩ ;
  -- Applying the local estimate to each term in the sum, we get:
  have h_local : ∀ i, hausdorffContent_v2 s (C i ∩ lowDensitySubset_v2 E s δ τ) ≤ τ * (if (C i ∩ lowDensitySubset_v2 E s δ τ).Nonempty then (EMetric.diam (C i)) ^ s else 0) := by
    intro i
    by_cases h_nonempty : (C i ∩ lowDensitySubset_v2 E s δ τ).Nonempty;
    · obtain ⟨ x, hx ⟩ := h_nonempty;
      have := lemma_1a_local_v2 E ( C i ) x s δ τ ⟨ hx.1, hx.2 ⟩ ( h_diam i );
      refine' le_trans _ ( this.trans _ );
      · apply_rules [ OuterMeasure.mono ];
        exact fun y hy => ⟨ hy.1, hy.2.1 ⟩;
      · rw [ if_pos ⟨ x, hx ⟩ ];
    · simp_all +decide [ Set.not_nonempty_iff_eq_empty.mp h_nonempty ];
      simp +decide [ hausdorffContent_v2 ];
  simpa only [ ENNReal.tsum_mul_left ] using h_subset.trans ( ENNReal.tsum_le_tsum h_local )

/-
Lemma 1(b): Hausdorff content versus Hausdorff measure on E(δ, τ) (v2)
-/
lemma lemma_1b_v2 (E : Set X) (s : ℝ) (δ : ℝ) (τ : NNReal)
    (hδ : 0 < δ) (hτ : 0 < τ ∧ τ < 1) (hs : 0 ≤ s) :
    hausdorffContent_v2 s (lowDensitySubset_v2 E s δ τ) ≤ τ * hausdorffMeasure s (lowDensitySubset_v2 E s δ τ) := by
  -- Consider two cases: $H^s(S) = \infty$ and $H^s(S) < \infty$.
  by_cases h_inf : (hausdorffMeasure s (lowDensitySubset_v2 E s δ τ)) = ⊤;
  · simp [h_inf];
    simp +decide [ ENNReal.mul_top, hτ.1.ne' ];
  · -- For any ε > 0, apply lemma_approx_cover_v2 to find a cover {C_i} of S such that diam(C_i) < δ and ∑ diam(C_i)^s ≤ H^s(S) + ε.
    have h_cover : ∀ ε > 0, ∃ C : ℕ → Set X, (lowDensitySubset_v2 E s δ τ ⊆ ⋃ i, C i) ∧
        (∀ i, EMetric.diam (C i) < ENNReal.ofReal δ) ∧
        (∑' i, if (C i).Nonempty then (EMetric.diam (C i)) ^ s else 0) ≤ hausdorffMeasure s (lowDensitySubset_v2 E s δ τ) + ε := by
          exact?;
    -- Apply lemma_1a_strict_v3 to this cover:
    have h_estimate : ∀ ε > 0, hausdorffContent_v2 s (lowDensitySubset_v2 E s δ τ) ≤ τ * (hausdorffMeasure s (lowDensitySubset_v2 E s δ τ) + ε) := by
      intro ε hε_pos
      obtain ⟨C, hC_cover, hC_diam, hC_sum⟩ := h_cover ε hε_pos;
      refine' le_trans _ ( mul_le_mul_left' hC_sum _ );
      refine' le_trans ( lemma_1a_strict_v3 E s δ τ C hδ hτ hs hC_cover hC_diam ) _;
      gcongr;
      split_ifs <;> simp_all +decide [ Set.Nonempty ];
    -- Since ε is arbitrary, we can take the limit as ε approaches 0.
    have h_limit : Filter.Tendsto (fun ε : ℝ≥0∞ => τ * (hausdorffMeasure s (lowDensitySubset_v2 E s δ τ) + ε)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (τ * hausdorffMeasure s (lowDensitySubset_v2 E s δ τ))) := by
      refine' tendsto_nhdsWithin_of_tendsto_nhds _;
      refine' Continuous.tendsto' _ _ _ _ <;> norm_num;
      fun_prop (disch := norm_num);
    exact le_of_tendsto_of_tendsto tendsto_const_nhds h_limit ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => h_estimate ε hε )

/-
If the sum of s-powers of diameters is less than R^s, then each diameter is less than R.
-/
lemma lemma_sum_small_implies_diam_small (C : ℕ → Set X) (s : ℝ) (R : ℝ)
    (hR : 0 < R) (hs : 0 < s)
    (h_sum : (∑' i, if (C i).Nonempty then (EMetric.diam (C i)) ^ s else 0) < ENNReal.ofReal R ^ s) :
    ∀ i, EMetric.diam (C i) < ENNReal.ofReal R := by
      intro i
      by_contra h_contra
      have h_term : (EMetric.diam (C i)) ^ s ≥ (ENNReal.ofReal R) ^ s := by
        gcongr ; aesop;
      refine' h_sum.not_le ( le_trans _ ( ENNReal.le_tsum i ) );
      split_ifs <;> simp_all +decide [ Set.Nonempty ];
      simp_all +decide [ show C i = ∅ by ext x; simp +decide [ * ] ]

/-
Local refinement lemma: If a small set C intersects the low density set, we can cover the intersection with even smaller sets with reduced cost.
-/
lemma lemma_local_refinement (E : Set X) (s : ℝ) (δ : ℝ) (τ : NNReal)
    (hδ : 0 < δ) (hτ : 0 < τ ∧ τ < 1) (hs : 0 < s)
    (δ' : ℝ) (hδ' : 0 < δ') (hδ'_le : δ' ≤ δ)
    (C : Set X) (h_diam : EMetric.diam C < ENNReal.ofReal δ')
    (h_inter : (C ∩ lowDensitySubset_v2 E s δ τ).Nonempty)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ D : ℕ → Set X, (C ∩ lowDensitySubset_v2 E s δ τ ⊆ ⋃ j, D j) ∧
      (∀ j, EMetric.diam (D j) < ENNReal.ofReal δ') ∧
      (∑' j, if (D j).Nonempty then (EMetric.diam (D j)) ^ s else 0) ≤ τ * (EMetric.diam C) ^ s + ε := by
        -- By Lemma 1(a), we have $\mathcal{H}^s_\infty(F \cap C) \leq \tau (\operatorname{diam} C)^s$.
        have h_1a : (hausdorffContent_v2 s (C ∩ lowDensitySubset_v2 E s δ (τ : ℝ≥0∞))) ≤ τ * (EMetric.diam C) ^ s := by
          have := @lemma_1a_local_v2 X _ _ _;
          obtain ⟨ x, hx ⟩ := h_inter;
          specialize this _ _ _ _ _ _ hx ( lt_of_lt_of_le h_diam ( ENNReal.ofReal_le_ofReal hδ'_le ) );
          refine' le_trans _ this;
          apply_rules [ OuterMeasure.mono];
          exact fun x hx => ⟨ hx.1, hx.2.1 ⟩;
        -- By definition of Hausdorff content, there exists a countable cover $\{D_j\}$ of $F \cap C$ such that $\sum (\operatorname{diam} D_j)^s \leq \tau (\operatorname{diam} C)^s + \epsilon$.
        obtain ⟨D, hD⟩ : ∃ D : ℕ → Set X, (C ∩ lowDensitySubset_v2 E s δ (τ : ℝ≥0∞)) ⊆ ⋃ j, D j ∧ (∑' j, if (D j).Nonempty then (EMetric.diam (D j)) ^ s else 0) ≤ (τ * (EMetric.diam C) ^ s) + ε := by
          have h_cover : ∀ {S : Set X}, (hausdorffContent_v2 s S) < ⊤ → ∀ ε > 0, ∃ D : ℕ → Set X, S ⊆ ⋃ j, D j ∧ (∑' j, if (D j).Nonempty then (EMetric.diam (D j)) ^ s else 0) ≤ (hausdorffContent_v2 s S) + ε := by
            intro S hS ε hε_pos
            obtain ⟨D, hD⟩ : ∃ D : ℕ → Set X, S ⊆ ⋃ j, D j ∧ (∑' j, if (D j).Nonempty then (EMetric.diam (D j)) ^ s else 0) ≤ (hausdorffContent_v2 s S) + ε := by
              have h_def : hausdorffContent_v2 s S = ⨅ (f : ℕ → Set X), ⨅ (_ : S ⊆ ⋃ i, f i), ∑' j, if (f j).Nonempty then (EMetric.diam (f j)) ^ s else 0 := by
                simp +decide [ hausdorffContent_v2, OuterMeasure.mkMetric'.pre ];
                rw [ OuterMeasure.boundedBy_apply ];
                simp +decide [ extend ];
                congr! 3;
                exact tsum_congr fun n => by split_ifs <;> simp +decide [ * ] ;
              contrapose! h_def;
              refine' ne_of_lt ( lt_of_lt_of_le _ ( le_iInf fun f => le_iInf fun hf => le_of_lt ( h_def f hf ) ) );
              exact ENNReal.lt_add_right ( ne_of_lt hS ) hε_pos.ne';
            use D;
          refine' Exists.elim ( h_cover _ ε hε ) fun D hD => ⟨ D, hD.1, le_trans hD.2 ( add_le_add_right h_1a _ ) ⟩;
          refine' lt_of_le_of_lt h_1a _;
          refine' ENNReal.mul_lt_top _ _;
          · exact ENNReal.coe_lt_top;
          · exact ENNReal.rpow_lt_top_of_nonneg hs.le ( ne_of_lt ( lt_of_lt_of_le h_diam ( le_top ) ) );
        refine' ⟨ fun j => D j ∩ C, _, _, _ ⟩ <;> simp_all +decide [ Set.subset_def ];
        · intro j; exact lt_of_le_of_lt ( EMetric.diam_mono ( Set.inter_subset_right ) ) h_diam;
        · refine' le_trans _ hD.2;
          refine' ENNReal.tsum_le_tsum fun j => _;
          split_ifs <;> simp_all +decide [ Set.Nonempty ];
          exact ENNReal.rpow_le_rpow ( EMetric.diam_mono <| Set.inter_subset_left ) hs.le

/-
Combining a double sequence of covers into a single sequence.
Given a double sequence of sets D_{ij}, we can reindex them into a single sequence D'_k such that the union is the same, every set in D' comes from D, and the sum of s-powers of diameters is preserved.
-/
lemma lemma_combine_covers (D : ℕ → ℕ → Set X) (s : ℝ) :
    ∃ D' : ℕ → Set X, (⋃ k, D' k) = (⋃ i, ⋃ j, D i j) ∧
    (∀ k, ∃ i j, D' k = D i j) ∧
    (∑' k, if (D' k).Nonempty then (EMetric.diam (D' k)) ^ s else 0) =
      ∑' i, ∑' j, if (D i j).Nonempty then (EMetric.diam (D i j)) ^ s else 0 := by
        -- Let's construct the bijection $e : \mathbb{N} \to \mathbb{N} \times \mathbb{N}$.
        obtain ⟨e, he_bij⟩ : ∃ e : ℕ ≃ ℕ × ℕ, True := by
          simp +zetaDelta at *;
        refine' ⟨ fun n => D ( e n |>.1 ) ( e n |>.2 ), _, _, _ ⟩;
        · simp +decide [ Set.ext_iff ];
          exact fun x => ⟨ fun ⟨ i, hi ⟩ => ⟨ _, _, hi ⟩, fun ⟨ i, j, hi ⟩ => ⟨ e.symm ( i, j ), by simpa using hi ⟩ ⟩;
        · exact fun k => ⟨ _, _, rfl ⟩;
        · convert ( Equiv.tsum_eq e ) _;
          rotate_right;
          use fun p => if ( D p.1 p.2 ).Nonempty then EMetric.diam ( D p.1 p.2 ) ^ s else 0;
          · rfl;
          · exact?

/-
Refinement Lemma: Given a cover C of F with diameters < delta', we can find a finer cover D with diameters < delta' such that the sum of powers is reduced by factor tau.
-/
lemma lemma_refinement (E : Set X) (s : ℝ) (δ : ℝ) (τ : NNReal)
    (hδ : 0 < δ) (hτ : 0 < τ ∧ τ < 1) (hs : 0 < s)
    (δ' : ℝ) (hδ' : 0 < δ') (hδ'_le : δ' ≤ δ)
    (C : ℕ → Set X)
    (h_diam : ∀ i, EMetric.diam (C i) < ENNReal.ofReal δ')
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ D : ℕ → Set X, (lowDensitySubset_v2 E s δ τ ∩ (⋃ i, C i) ⊆ ⋃ j, D j) ∧
      (∀ j, EMetric.diam (D j) < ENNReal.ofReal δ') ∧
      (∑' j, if (D j).Nonempty then (EMetric.diam (D j)) ^ s else 0) ≤
        τ * (∑' i, if (C i ∩ lowDensitySubset_v2 E s δ τ).Nonempty then (EMetric.diam (C i)) ^ s else 0) + ε := by
          -- For each $i$, define $\varepsilon_i = \varepsilon / 2^{i+1}$.
          set ε_i : ℕ → ℝ≥0∞ := fun i => ε / (ENNReal.ofReal (2 ^ (i + 1)) : ℝ≥0∞) with hε_i_def;
          -- For each $i$, if $C_i \cap F \neq \emptyset$, apply `lemma_local_refinement` to $C_i$ with $\varepsilon_i$.
          have h_refined : ∀ i, (C i ∩ lowDensitySubset_v2 E s δ τ).Nonempty → ∃ D_i : ℕ → Set X, (C i ∩ lowDensitySubset_v2 E s δ τ ⊆ ⋃ j, D_i j) ∧ (∀ j, EMetric.diam (D_i j) < ENNReal.ofReal δ') ∧ (∑' j, if (D_i j).Nonempty then (EMetric.diam (D_i j)) ^ s else 0) ≤ τ * (EMetric.diam (C i)) ^ s + ε_i i := by
            exact fun i hi => lemma_local_refinement E s δ τ hδ hτ hs δ' hδ' hδ'_le ( C i ) ( h_diam i ) hi ( ε_i i ) ( ENNReal.div_pos_iff.mpr ⟨ hε.ne', by simp +decide [ hε.ne' ] ⟩ ) |> fun ⟨ D_i, hD_i₁, hD_i₂, hD_i₃ ⟩ => ⟨ D_i, hD_i₁, hD_i₂, hD_i₃ ⟩;
          choose! D hD₁ hD₂ hD₃ using h_refined;
          -- Combine the covers $D_i$ into a single cover $D'$ using `lemma_combine_covers`.
          obtain ⟨D', hD'⟩ : ∃ D' : ℕ → Set X, (⋃ k, D' k) = (⋃ i, ⋃ j, if (C i ∩ lowDensitySubset_v2 E s δ τ).Nonempty then D i j else ∅) ∧
            (∀ k, ∃ i j, D' k = if (C i ∩ lowDensitySubset_v2 E s δ τ).Nonempty then D i j else ∅) ∧
            (∑' k, if (D' k).Nonempty then (EMetric.diam (D' k)) ^ s else 0) =
              ∑' i, ∑' j, if (C i ∩ lowDensitySubset_v2 E s δ τ).Nonempty then (if (D i j).Nonempty then (EMetric.diam (D i j)) ^ s else 0) else 0 := by
                have := @lemma_combine_covers X _ _ _ (fun i j => if (C i ∩ lowDensitySubset_v2 E s δ τ).Nonempty then D i j else ∅) s;
                convert this using 6;
                ext i; by_cases hi : ( C i ∩ lowDensitySubset_v2 E s δ τ ).Nonempty <;> simp +decide [ hi ] ;
          refine' ⟨ D', _, _, _ ⟩;
          · simp_all +decide [ Set.subset_def ];
            exact fun x hx i hi => ⟨ i, ⟨ x, hi, hx ⟩, hD₁ i ⟨ x, hi, hx ⟩ x hi hx ⟩;
          · intro k; obtain ⟨ i, j, hk ⟩ := hD'.2.1 k; by_cases hi : ( C i ∩ lowDensitySubset_v2 E s δ τ ).Nonempty <;> simp_all +decide ;
          · -- Apply the inequality from `hD₃` to each term in the sum.
            have h_sum_ineq : ∑' i, ∑' j, (if (C i ∩ lowDensitySubset_v2 E s δ τ).Nonempty then (if (D i j).Nonempty then (EMetric.diam (D i j)) ^ s else 0) else 0) ≤ ∑' i, (τ * (EMetric.diam (C i)) ^ s + ε_i i) * (if (C i ∩ lowDensitySubset_v2 E s δ τ).Nonempty then 1 else 0) := by
              refine' ENNReal.tsum_le_tsum fun i => _;
              by_cases hi : ( C i ∩ lowDensitySubset_v2 E s δ τ ).Nonempty <;> simp +decide [ hi ];
              exact hD₃ i hi;
            -- Apply the inequality from `h_sum_ineq` to conclude the proof.
            have h_final : ∑' i, (τ * (EMetric.diam (C i)) ^ s + ε_i i) * (if (C i ∩ lowDensitySubset_v2 E s δ τ).Nonempty then 1 else 0) ≤ τ * ∑' i, (if (C i ∩ lowDensitySubset_v2 E s δ τ).Nonempty then (EMetric.diam (C i)) ^ s else 0) + ∑' i, ε_i i := by
              simp +decide [ add_mul, mul_assoc, mul_comm, mul_left_comm, ← ENNReal.tsum_mul_left ];
              rw [ ← ENNReal.tsum_add ];
              exact ENNReal.tsum_le_tsum fun i => by split_ifs <;> simp +decide [ * ] ;
            refine' hD'.2.2 ▸ h_sum_ineq.trans ( h_final.trans _ );
            simp +zetaDelta at *;
            simp +decide [ div_eq_mul_inv, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right ];
            simp +decide [ pow_add, ENNReal.tsum_mul_left ];
            simp +decide [ ENNReal.mul_inv, ENNReal.inv_pow ];
            rw [ ENNReal.tsum_mul_right, ENNReal.tsum_geometric ] ; norm_num;
            rw [ ENNReal.mul_inv_cancel ] <;> norm_num

/-
Strict Hausdorff content. The infimum of sums of s-powers of diameters of covers with diameter strictly less than r.
-/
noncomputable def strictContent (E : Set X) (s : ℝ) (r : ℝ) : ℝ≥0∞ :=
  ⨅ (C : ℕ → Set X) (_ : E ⊆ ⋃ i, C i) (_ : ∀ i, EMetric.diam (C i) < ENNReal.ofReal r),
    ∑' i, if (C i).Nonempty then (EMetric.diam (C i)) ^ s else 0

/-
The strict content of the low density subset is finite.
-/
lemma lemma_strict_content_finite (E : Set X) (s : ℝ) (δ : ℝ) (τ : NNReal)
    (hE_fin : hausdorffMeasure s E ≠ ⊤)
    (hδ : 0 < δ) (hτ : 0 < τ ∧ τ < 1) (hs : 0 ≤ s)
    (r : ℝ) (hr : 0 < r) (hr_le : r ≤ δ) :
    strictContent (lowDensitySubset_v2 E s δ τ) s r < ⊤ := by
      -- By definition of strictContent, if there exists a cover with diameter less than r and sum less than infinity, then the strict content is less than infinity.
      have h_strictContent_finite : ∃ C : ℕ → Set X, (lowDensitySubset_v2 E s δ τ ⊆ ⋃ i, C i) ∧ (∀ i, EMetric.diam (C i) < ENNReal.ofReal r) ∧ (∑' i, if (C i).Nonempty then (EMetric.diam (C i)) ^ s else 0) < ⊤ := by
        -- Since $F$ is a subset of $E$ and $E$ has finite Hausdorff measure, $F$ also has finite Hausdorff measure.
        have hF_fin : μH[s] (lowDensitySubset_v2 E s δ τ) < ⊤ := by
          exact lt_of_le_of_lt ( MeasureTheory.measure_mono ( show lowDensitySubset_v2 E s δ ( τ : ENNReal ) ⊆ E from fun x hx => hx.1 ) ) ( lt_top_iff_ne_top.mpr hE_fin );
        -- By definition of Hausdorff measure, there exists a cover of $F$ with diameter less than $r$ and finite sum.
        obtain ⟨C, hC_cover, hC_finite⟩ : ∃ C : ℕ → Set X, (lowDensitySubset_v2 E s δ τ ⊆ ⋃ i, C i) ∧ (∀ i, EMetric.diam (C i) < ENNReal.ofReal r) ∧ (∑' i, if (C i).Nonempty then (EMetric.diam (C i)) ^ s else 0) ≤ μH[s] (lowDensitySubset_v2 E s δ τ) + 1 := by
          convert lemma_approx_cover_v2 ( lowDensitySubset_v2 E s δ τ ) s r 1 ( by positivity ) ( by positivity ) ( by positivity ) ( by simpa using hF_fin.ne ) using 1;
        exact ⟨ C, hC_cover, hC_finite.1, lt_of_le_of_lt hC_finite.2 ( ENNReal.add_lt_top.2 ⟨ hF_fin, ENNReal.one_lt_top ⟩ ) ⟩;
      exact lt_of_le_of_lt ( ciInf_le ⟨ 0, Set.forall_mem_range.2 fun _ => zero_le _ ⟩ h_strictContent_finite.choose ) ( lt_of_le_of_lt ( ciInf_le ⟨ 0, Set.forall_mem_range.2 fun _ => zero_le _ ⟩ h_strictContent_finite.choose_spec.1 ) ( lt_of_le_of_lt ( ciInf_le ⟨ 0, Set.forall_mem_range.2 fun _ => zero_le _ ⟩ h_strictContent_finite.choose_spec.2.1 ) h_strictContent_finite.choose_spec.2.2 ) )

/-
The strict content satisfies L <= tau * L.
-/
lemma lemma_strict_content_le (E : Set X) (s : ℝ) (δ : ℝ) (τ : NNReal)
    (hδ : 0 < δ) (hτ : 0 < τ ∧ τ < 1) (hs : 0 < s)
    (r : ℝ) (hr : 0 < r) (hr_le : r ≤ δ) :
    strictContent (lowDensitySubset_v2 E s δ τ) s r ≤ τ * strictContent (lowDensitySubset_v2 E s δ τ) s r := by
      by_contra h_contra;
      -- Choose η such that τ * (strictContent + η) + η < strictContent.
      obtain ⟨η, hη_pos, hη⟩ : ∃ η > 0, τ * (strictContent (lowDensitySubset_v2 E s δ τ) s r + η) + η < strictContent (lowDensitySubset_v2 E s δ τ) s r := by
        have h_eta : ∃ η > 0, η < (strictContent (lowDensitySubset_v2 E s δ τ) s r - τ * strictContent (lowDensitySubset_v2 E s δ τ) s r) / (τ + 1) := by
          refine' exists_between _;
          simp +zetaDelta at *;
          exact ne_of_gt ( tsub_pos_of_lt h_contra );
        obtain ⟨ η, hη₁, hη₂ ⟩ := h_eta;
        rw [ ENNReal.lt_div_iff_mul_lt ] at hη₂;
        · rw [ lt_tsub_iff_left ] at hη₂;
          exact ⟨ η, hη₁, by convert hη₂ using 1; ring ⟩;
        · exact Or.inl <| by positivity;
        · exact Or.inl <| ENNReal.add_ne_top.2 ⟨ ENNReal.coe_ne_top, ENNReal.one_ne_top ⟩;
      -- Choose a cover $C$ of $E(\delta, \tau)$ with diameter $< r$ such that $\text{sum}(C) \le \text{strictContent}(E(\delta, \tau), s, r) + \eta$.
      obtain ⟨C, hC_cover, hC_sum⟩ : ∃ C : ℕ → Set X, (lowDensitySubset_v2 E s δ τ ⊆ ⋃ i, C i) ∧ (∀ i, EMetric.diam (C i) < ENNReal.ofReal r) ∧ (∑' i, (if (C i).Nonempty then (EMetric.diam (C i)) ^ s else 0)) ≤ strictContent (lowDensitySubset_v2 E s δ τ) s r + η := by
        have h_inf : ∀ ε > 0, ∃ C : ℕ → Set X, (lowDensitySubset_v2 E s δ τ ⊆ ⋃ i, C i) ∧ (∀ i, EMetric.diam (C i) < ENNReal.ofReal r) ∧ (∑' i, (if (C i).Nonempty then (EMetric.diam (C i)) ^ s else 0)) ≤ strictContent (lowDensitySubset_v2 E s δ τ) s r + ε := by
          intro ε ε_pos
          have h_inf : strictContent (lowDensitySubset_v2 E s δ τ) s r = ⨅ (C : ℕ → Set X) (_ : lowDensitySubset_v2 E s δ τ ⊆ ⋃ i, C i) (_ : ∀ i, EMetric.diam (C i) < ENNReal.ofReal r), ∑' i, (if (C i).Nonempty then (EMetric.diam (C i)) ^ s else 0) := by
            exact?;
          contrapose! h_inf;
          refine' ne_of_lt ( lt_of_lt_of_le ( ENNReal.lt_add_right _ ε_pos.ne' ) _ );
          · exact ne_of_lt ( lt_top_iff_ne_top.mpr fun h => by simp_all +decide [ ENNReal.mul_top' ] );
          · refine' le_iInf fun C => le_iInf fun hC => le_iInf fun hC' => le_of_lt ( h_inf C hC hC' );
        exact h_inf η hη_pos;
      -- Apply `lemma_refinement` with $\delta' = r$ and $\epsilon = \eta$.
      obtain ⟨D, hD_cover, hD_sum⟩ : ∃ D : ℕ → Set X, (lowDensitySubset_v2 E s δ τ ∩ (⋃ i, C i) ⊆ ⋃ j, D j) ∧ (∀ j, EMetric.diam (D j) < ENNReal.ofReal r) ∧ (∑' j, (if (D j).Nonempty then (EMetric.diam (D j)) ^ s else 0)) ≤ τ * (∑' i, (if (C i ∩ lowDensitySubset_v2 E s δ τ).Nonempty then (EMetric.diam (C i)) ^ s else 0)) + η := by
        convert lemma_refinement E s δ τ hδ hτ hs r hr ( by linarith ) C hC_sum.1 η hη_pos using 1;
      -- Since $D$ is a cover of $E(\delta, \tau)$ with diameter $< r$, we have $\text{sum}(D) \ge \text{strictContent}(E(\delta, \tau), s, r)$.
      have hD_ge_strictContent : (∑' j, (if (D j).Nonempty then (EMetric.diam (D j)) ^ s else 0)) ≥ strictContent (lowDensitySubset_v2 E s δ τ) s r := by
        refine' le_trans ( ciInf_le _ _ ) _;
        exact ⟨ 0, Set.forall_mem_range.2 fun C => zero_le _ ⟩;
        use D;
        simp +decide [ Set.subset_def ] at *;
        exact ciInf_le_of_le ⟨ 0, Set.forall_mem_range.2 fun _ => zero_le _ ⟩ ( fun x hx => by obtain ⟨ i, hi ⟩ := hC_cover x hx; obtain ⟨ j, hj ⟩ := hD_cover x hx i hi; exact ⟨ j, hj ⟩ ) ( ciInf_le ⟨ 0, Set.forall_mem_range.2 fun _ => zero_le _ ⟩ hD_sum.1 );
      -- Since $C$ is a cover of $E(\delta, \tau)$ with diameter $< r$, we have $\text{sum}(C) \ge \text{strictContent}(E(\delta, \tau), s, r)$.
      have hC_ge_strictContent : (∑' i, (if (C i ∩ lowDensitySubset_v2 E s δ τ).Nonempty then (EMetric.diam (C i)) ^ s else 0)) ≤ (∑' i, (if (C i).Nonempty then (EMetric.diam (C i)) ^ s else 0)) := by
        refine' ENNReal.tsum_le_tsum fun i => _;
        split_ifs <;> simp_all +decide [ Set.Nonempty ];
      refine' hη.not_le _;
      refine' le_trans hD_ge_strictContent ( hD_sum.2.trans _ );
      gcongr;
      exact le_trans hC_ge_strictContent hC_sum.2

/-
The strict content is zero for s > 0.
-/
lemma lemma_strict_content_zero (E : Set X) (s : ℝ) (δ : ℝ) (τ : NNReal)
    (hE_fin : hausdorffMeasure s E ≠ ⊤)
    (hδ : 0 < δ) (hτ : 0 < τ ∧ τ < 1) (hs : 0 < s)
    (r : ℝ) (hr : 0 < r) (hr_le : r ≤ δ) :
    strictContent (lowDensitySubset_v2 E s δ τ) s r = 0 := by
      have := lemma_strict_content_le E s δ τ hδ hτ hs r hr hr_le;
      rcases eq_or_ne ( strictContent ( lowDensitySubset_v2 E s δ τ ) s r ) ⊤ with h | h;
      · exact absurd h ( ne_of_lt ( lemma_strict_content_finite E s δ τ hE_fin hδ hτ ( by linarith ) r hr hr_le ) );
      · cases' eq_or_ne ( strictContent ( lowDensitySubset_v2 E s δ τ ) s r ) 0 with h' h' <;> simp_all +decide [ ENNReal.mul_eq_top ];
        rw [ ← ENNReal.toReal_le_toReal ] at this <;> simp_all +decide [ ENNReal.toReal_mul, ENNReal.toReal_ofReal ];
        · exact this.not_lt ( mul_lt_of_lt_one_left ( ENNReal.toReal_pos h' h ) ( mod_cast hτ.2 ) );
        · exact ENNReal.mul_ne_top ( ENNReal.coe_ne_top ) h

/-
The standard pre-measure is bounded by the strict content.
-/
lemma lemma_pre_le_strict (E : Set X) (s : ℝ) (r : ℝ) (hr : 0 < r) :
    MeasureTheory.OuterMeasure.mkMetric'.pre (fun t => (EMetric.diam t) ^ s) (ENNReal.ofReal r) E ≤ strictContent E s r := by
      refine' le_iInf fun C => le_iInf fun hC => le_iInf fun hC' => _;
      refine' le_trans ( iInf_le _ C ) _;
      simp +decide [ hC, extend ];
      refine' ENNReal.tsum_le_tsum fun i => _;
      split_ifs <;> simp_all +decide [ le_of_lt ]


/-
Checking types of mkMetric and hausdorffMeasure
-/
#check MeasureTheory.OuterMeasure.mkMetric
#check MeasureTheory.Measure.hausdorffMeasure

/-
If the pre-measure is zero for all sufficiently small radii, then the metric outer measure is zero.
-/
lemma lemma_zero_of_pre_zero (m : Set X → ENNReal) (S : Set X) (δ : ℝ) (hδ : 0 < δ)
    (h : ∀ r, 0 < r → r ≤ δ → MeasureTheory.OuterMeasure.mkMetric'.pre m (ENNReal.ofReal r) S = 0) :
    MeasureTheory.OuterMeasure.mkMetric' m S = 0 := by
      refine' le_antisymm _ bot_le;
      refine' le_trans ( le_of_eq _ ) _;
      exact ⨆ r : ℝ, ⨆ hr : 0 < r, OuterMeasure.mkMetric'.pre m ( ENNReal.ofReal r ) S;
      · simp +decide [ OuterMeasure.mkMetric', iSup_and ];
        rw [ @ciSup_eq_of_forall_le_of_forall_lt_exists_gt ];
        · intro i;
          rcases i with ( _ | i ) <;> simp +decide [ ENNReal.ofReal ];
          · refine' le_iSup_of_le δ ( le_iSup_of_le hδ _ );
            apply_rules [ MeasureTheory.OuterMeasure.mkMetric'.mono_pre ];
            exact le_top;
          · exact fun hi => le_iSup_of_le ( i : ℝ ) ( by aesop );
        · intro w hw;
          contrapose! hw;
          refine' iSup_le fun r => _;
          by_cases hr : 0 < r <;> aesop;
      · refine' iSup_le fun r => iSup_le fun hr => _;
        by_cases hrδ : r ≤ δ;
        · rw [ h r hr hrδ ];
        · convert le_trans _ ( h δ hδ le_rfl |> le_of_eq ) using 1;
          apply_rules [ MeasureTheory.OuterMeasure.mkMetric'.mono_pre ];
          exact ENNReal.ofReal_le_ofReal ( le_of_not_ge hrδ )

/-
The metric outer measure of the low density subset is zero.
-/
lemma lemma_1_outer (E : Set X) (s : ℝ) (δ : ℝ) (τ : NNReal)
    (hE_fin : hausdorffMeasure s E ≠ ⊤)
    (hδ : 0 < δ) (hτ : 0 < τ ∧ τ < 1) (hs : 0 < s) :
    MeasureTheory.OuterMeasure.mkMetric' (fun t => (EMetric.diam t) ^ s) (lowDensitySubset_v2 E s δ τ) = 0 := by
      have h_zero : ∀ r, 0 < r → r ≤ δ → MeasureTheory.OuterMeasure.mkMetric'.pre (fun t => (EMetric.diam t) ^ s) (ENNReal.ofReal r) (lowDensitySubset_v2 E s δ τ) = 0 := by
        intro r hr hr_le
        have h_pre_le_strict : MeasureTheory.OuterMeasure.mkMetric'.pre (fun t => (EMetric.diam t) ^ s) (ENNReal.ofReal r) (lowDensitySubset_v2 E s δ τ) ≤ strictContent (lowDensitySubset_v2 E s δ τ) s r := by
          exact?;
        exact le_antisymm ( le_trans h_pre_le_strict ( by exact le_trans ( le_of_eq ( lemma_strict_content_zero E s δ τ hE_fin hδ hτ hs r hr hr_le ) ) ( by norm_num ) ) ) ( by norm_num );
      exact?

/-
Lemma 3.3.1: The low density subset has zero Hausdorff measure.
-/
lemma lemma_1 (E : Set X) (s : ℝ) (δ : ℝ) (τ : NNReal)
    (hE_meas : MeasurableSet E)
    (hE_pos : 0 < hausdorffMeasure s E)
    (hE_fin : hausdorffMeasure s E ≠ ⊤)
    (hδ : 0 < δ) (hτ : 0 < τ ∧ τ < 1) (hs : 0 < s) :
    hausdorffMeasure s (lowDensitySubset_v2 E s δ τ) = 0 := by
      convert lemma_1_outer E s δ τ hE_fin hδ hτ hs using 1;
      rw [ ← MeasureTheory.Measure.toOuterMeasure_apply ];
      simp +decide [ MeasureTheory.Measure.hausdorffMeasure ];
      simp +decide [ OuterMeasure.mkMetric, OuterMeasure.mkMetric' ]

import FormalizingGMT.«Project Versions».Measures.Basic

open scoped BigOperators Real Nat Pointwise ENNReal

open MeasureTheory MeasureTheory.OuterMeasure Set

set_option linter.style.setOption false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-! ## Helper lemmas -/

variable {X : Type*} [PseudoMetricSpace X] [SigmaCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-
Carathéodory-measurable sets for μ are also Carathéodory-measurable for the restriction
of μ to any set.
-/
set_option linter.unusedSectionVars false in
set_option linter.unusedSimpArgs false in
lemma caratheodory_restrict_of_caratheodory (μ : OuterMeasure X) (E : Set X)
    (h : ‹MeasurableSpace X› ≤ μ.caratheodory) :
    ‹MeasurableSpace X› ≤ (OuterMeasure.restrict E μ).caratheodory := by
  intro A H B; exact (by
  convert h _ H ( B ∩ E ) using 1;
  · simp +decide [ Set.inter_comm, OuterMeasure.restrict_apply ];
  · simp +decide [ Set.inter_assoc, Set.inter_comm, Set.inter_left_comm, Set.diff_eq ])

/-
If E is Carathéodory-measurable for μ, B ⊇ E is measurable with μ(B) = μ(E) < ∞,
then μ(B \ E) = 0.
-/
set_option linter.unusedSectionVars false in
set_option linter.unusedSimpArgs false in
lemma measure_diff_eq_zero (μ : OuterMeasure X) (E B : Set X)
    (hEB : E ⊆ B) (hμ : μ E = μ B)
    (hE_cara : μ.IsCaratheodory E) (hE_fin : μ E < ⊤) :
    μ (B \ E) = 0 := by
  have h_replace : μ (E ∪ (B \ E)) = μ E + μ (B \ E) := by
    have := hE_cara ( E ∪ B \ E );
    convert this using 2 <;>
      simp +decide [ Set.union_inter_cancel_left, Set.union_diff_cancel_left, hEB ];
  rw [ Set.union_diff_cancel hEB ] at h_replace;
  rw [ eq_comm ] at h_replace;
  contrapose! h_replace;
  exact ne_of_gt ( hμ ▸ ENNReal.lt_add_right hE_fin.ne h_replace )

/-
If B ⊇ E and μ(B \ E) = 0, then restrict E μ = restrict B μ as outer measures.
-/
set_option linter.unusedSectionVars false in
lemma restrict_eq_of_null_diff (μ : OuterMeasure X) (E B : Set X)
    (hEB : E ⊆ B) (h_null : μ (B \ E) = 0) :
    OuterMeasure.restrict E μ = OuterMeasure.restrict B μ := by
  apply le_antisymm
  · intro A
    rw [OuterMeasure.restrict_apply, OuterMeasure.restrict_apply]
    exact μ.mono (Set.inter_subset_inter_right A hEB)
  · intro A
    rw [OuterMeasure.restrict_apply, OuterMeasure.restrict_apply]
    calc
      μ (A ∩ B) ≤ μ ((A ∩ E) ∪ (B \ E)) := by
        refine μ.mono ?_
        intro x hx
        by_cases hxE : x ∈ E
        · exact Or.inl ⟨hx.1, hxE⟩
        · exact Or.inr ⟨hx.2, hxE⟩
      _ ≤ μ (A ∩ E) + μ (B \ E) := MeasureTheory.measure_union_le _ _
      _ = μ (A ∩ E) := by simp [h_null]

/-
For a measurable set B, the toMeasure of restrict B μ equals the restrict of μ.toMeasure.
-/
set_option linter.unusedSectionVars false in
lemma toMeasure_restrict_eq (μ : OuterMeasure X) (B : Set X)
    (hB : MeasurableSet B) (h : ‹MeasurableSpace X› ≤ μ.caratheodory)
    (h' : ‹MeasurableSpace X› ≤ (OuterMeasure.restrict B μ).caratheodory) :
    (OuterMeasure.restrict B μ).toMeasure h' = (μ.toMeasure h).restrict B := by
  ext s hs; simp +decide [ *, MeasureTheory.Measure.restrict_apply ] ;

/-
For a Borel regular outer measure and a Carathéodory-measurable set E with μ(E) < ∞,
for any set S there exists a Borel set F with (μ↾E)(S) = (μ↾E)(F).

The construction is: let G ⊇ S∩E be Borel with μ(G) = μ(S∩E), let C ⊇ E be Borel with
μ(C) = μ(E), and let D ⊇ S∩(C\E) be Borel with μ(D) = μ(S∩(C\E)) = 0.
Then F = G ∪ Cᶜ ∪ D works.
-/
lemma BorelRegularOuterMeasure.exists_borel_superset_restrict
    (μ : OuterMeasure X) [BorelRegularOuterMeasure μ] (E : Set X)
    (hE_meas : μ.IsCaratheodory E) (hE_fin : μ E < ⊤)
    (S : Set X) :
    ∃ F : Set X, MeasurableSet F ∧ S ⊆ F ∧
      (OuterMeasure.restrict E μ) S = (OuterMeasure.restrict E μ) F := by
  -- By assumption, there exists a Borel set $C \supseteq E$ with $\mu(C) = \mu(E)$.
  obtain ⟨C, hC_meas, hC⟩ : ∃ C : Set X, MeasurableSet C ∧ E ⊆ C ∧ μ E = μ C := by
    exact BorelRegularOuterMeasure.exists_measurable_superset (μ := μ) E;
  -- By assumption, there exists a Borel set `G ⊇ S ∩ E` with `μ G = μ (S ∩ E)`.
  obtain ⟨G, hG_meas, hG⟩ :
      ∃ G : Set X, MeasurableSet G ∧ S ∩ E ⊆ G ∧ μ G = μ (S ∩ E) := by
    have := BorelRegularOuterMeasure.exists_measurable_superset (μ := μ) ( S ∩ E ) ; aesop;
  -- By assumption, there exists a Borel set `D ⊇ S ∩ (C \ E)` with `μ D = 0`.
  obtain ⟨D, hD_meas, hD⟩ :
      ∃ D : Set X, MeasurableSet D ∧ S ∩ (C \ E) ⊆ D ∧ μ D = 0 := by
    have hD_zero : μ (C \ E) = 0 := by
      apply measure_diff_eq_zero μ E C hC.left hC.right hE_meas hE_fin;
    have := BorelRegularOuterMeasure.exists_measurable_superset (μ := μ) ( C \ E );
    exact ⟨ this.choose, this.choose_spec.1,
      Set.Subset.trans ( Set.inter_subset_right ) this.choose_spec.2.1,
      this.choose_spec.2.2.symm.trans hD_zero ⟩;
  refine ⟨ G ∪ Cᶜ ∪ D, ?_, ?_, ?_ ⟩;
  · exact MeasurableSet.union ( MeasurableSet.union hG_meas ( hC_meas.compl ) ) hD_meas;
  · grind +splitImp;
  · have h_eq : μ (S ∩ E) ≤ μ ((G ∪ Cᶜ ∪ D) ∩ E) ∧
        μ ((G ∪ Cᶜ ∪ D) ∩ E) ≤ μ (G ∩ E) + μ (D ∩ E) := by
      refine ⟨ μ.mono ?_, ?_ ⟩
      · exact fun x hx => ⟨ Or.inl <| Or.inl <| hG.1 hx, hx.2 ⟩;
      · exact le_trans (μ.mono (by grind)) (MeasureTheory.measure_union_le _ _)
    have h_eq : μ (G ∩ E) ≤ μ G ∧ μ (D ∩ E) ≤ μ D := by
      exact ⟨ μ.mono ( Set.inter_subset_left ), μ.mono ( Set.inter_subset_left ) ⟩;
    simp_all +decide [ OuterMeasure.restrict_apply ];
    grind

/-- **Restriction of a Borel regular measure is Borel regular**: the restriction of a Borel
regular outer measure to a Carathéodory-measurable set of finite measure is again Borel
regular. -/
lemma BorelRegularOuterMeasure.restrict
    (μ : OuterMeasure X) [BorelRegularOuterMeasure μ] (E : Set X)
    (hE_meas : μ.IsCaratheodory E) (hE_fin : μ E < ⊤) :
    BorelRegularOuterMeasure (OuterMeasure.restrict E μ) := by
  exact {
    measurable_le_caratheodory := caratheodory_restrict_of_caratheodory μ E
      (BorelOuterMeasure.measurable_le_caratheodory (μ := μ))
    exists_measurable_superset := fun S =>
      BorelRegularOuterMeasure.exists_borel_superset_restrict μ E hE_meas hE_fin S }



/- **Approximation of measurable finite measure sets by closed sets from inside**:
Let μ be a Borel regular outer measure on a topological space X. Then for every μ-measurable set
E ⊆ X with μ E < ∞ and ε > 0, there exists a closed set F ⊆ E such that μ (E \ F) < ε. -/

theorem closed_approx_of_isBorelRegular
    (μ : OuterMeasure X) [BorelRegularOuterMeasure μ]
    (E : Set X) (hE : μ.IsCaratheodory E) (hEfin : μ E < ∞)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ F : Set X, IsClosed F ∧ F ⊆ E ∧ μ (E \ F) < ε := by
  let ν : OuterMeasure X := OuterMeasure.restrict E μ
  letI : BorelRegularOuterMeasure ν :=
    BorelRegularOuterMeasure.restrict μ E hE hEfin
  let m : Measure X :=
    ν.toMeasure (BorelOuterMeasure.measurable_le_caratheodory (μ := ν))
  have hν_compl : ν Eᶜ = 0 := by
    simp [ν, OuterMeasure.restrict_apply, Set.compl_inter_self]
  obtain ⟨G, hG_meas, hEcG, hνG_eq⟩ := BorelRegularOuterMeasure.exists_measurable_superset (μ := ν) Eᶜ
  have hνG : ν G = 0 := by
    simpa [hν_compl] using hνG_eq.symm
  have hmG : m G = 0 := by
    change (ν.toMeasure (BorelOuterMeasure.measurable_le_caratheodory (μ := ν))) G = 0
    simpa [toMeasure_apply _ _ hG_meas] using hνG
  let A : Set X := Gᶜ
  have hA_meas : MeasurableSet A := hG_meas.compl
  have hAE : A ⊆ E := by
    intro x hxA
    by_contra hxE
    exact hxA (hEcG hxE)
  haveI : IsFiniteMeasure m := by
    refine ⟨?_⟩
    have hmuniv : m univ = μ E := by
      change (ν.toMeasure (BorelOuterMeasure.measurable_le_caratheodory (μ := ν))) univ = μ E
      rw [toMeasure_apply _ _ MeasurableSet.univ]
      simp [ν, OuterMeasure.restrict_apply]
    rw [hmuniv]
    exact hEfin
  have hmA_ne_top : m A ≠ ∞ := by
    exact ne_of_lt (measure_lt_top m A)
  have hε_ne : ε ≠ 0 := ne_of_gt hε
  obtain ⟨F, hFA, hF_closed, hm_diff_lt⟩ :
      ∃ F, F ⊆ A ∧ IsClosed F ∧ m (A \ F) < ε := by
    exact hA_meas.exists_isClosed_diff_lt hmA_ne_top hε_ne
  refine ⟨F, hF_closed, hFA.trans hAE, ?_⟩
  have hEF_subset : E \ F ⊆ (A \ F) ∪ G := by
    intro x hx
    by_cases hxG : x ∈ G
    · exact Or.inr hxG
    · exact Or.inl ⟨hxG, hx.2⟩
  have hν_EF_lt : ν (E \ F) < ε := by
    calc
      ν (E \ F) ≤ ν ((A \ F) ∪ G) := ν.mono hEF_subset
      _ ≤ ν (A \ F) + ν G := measure_union_le (A \ F) G
      _ = m (A \ F) + 0 := by
        rw [hνG]
        change ν (A \ F) + 0 =
          (ν.toMeasure (BorelOuterMeasure.measurable_le_caratheodory (μ := ν))) (A \ F) + 0
        rw [toMeasure_apply _ _ (hA_meas.diff hF_closed.measurableSet)]
      _ < ε := by simpa using hm_diff_lt
  calc
    μ (E \ F) = ν (E \ F) := by
      have hset : E \ F = (E \ F) ∩ E := by
        ext x
        simp only [Set.mem_diff, Set.mem_inter_iff]
        constructor
        · intro hx
          exact ⟨hx, hx.1⟩
        · intro hx
          exact hx.1
      rw [hset]
      change μ ((E \ F) ∩ E) = (OuterMeasure.restrict E μ) ((E \ F) ∩ E)
      rw [OuterMeasure.restrict_apply]
      congr 1
      ext x
      simp only [Set.mem_inter_iff, Set.mem_diff]
      constructor
      · intro hx
        exact ⟨hx, hx.2⟩
      · intro hx
        exact hx.1
    _ < ε := hν_EF_lt

/- Reference: Mattila's book, Theorem 1.10 (1), page 11.-/
/- **Note:** This lemma should be used to prove lemma approx_by_closed_inside in Thm2_6.lean.-/


/- **Approximation of measurable sets by open sets from outside**:
Let μ be a Borel regular outer measure on a topological space X. Let E ⊆ X be a μ-measurable set
with μ E < ∞ and let ε > 0. If there are open sets V_i such that E ⊆ ⋃ i : ℕ, V_i and
μ (V_i) < ∞ for all i, then there exists an open set F ⊇ E such that μ (F \ E) < ε. -/

/- Reference: Mattila's book, Theorem 1.10 (2), page 11.-/

theorem open_approx_of_isBorelRegular
    (μ : OuterMeasure X) [BorelRegularOuterMeasure μ]
    (E : Set X) (hE : μ.IsCaratheodory E) (_hEfin : μ E < ∞)
    (V : ℕ → Set X) (hV_open : ∀ i, IsOpen (V i))
    (hEV : E ⊆ ⋃ i, V i) (hVfin : ∀ i, μ (V i) < ∞)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ F : Set X, IsOpen F ∧ E ⊆ F ∧ μ (F \ E) < ε := by
  by_contra! h_contra;
  obtain ⟨δ, hδpos, hδsum⟩ : ∃ δ : ℕ → ℝ≥0∞, (∀ i, 0 < δ i) ∧ (∑' i, δ i < ε) := ENNReal.exists_pos_sum_of_countable' hε.ne' ℕ;
  -- For each $i$, apply the assumption `closed_approx_of_isBorelRegular` to the set $W_i = V_i \setminus E$.
  have h_closed_approx_i (i : ℕ) : ∃ C : Set X, IsClosed C ∧ C ⊆ V i \ E ∧ μ ((V i \ E) \ C) < δ i := by
    apply closed_approx_of_isBorelRegular μ (V i \ E) (by
    convert μ.isCaratheodory_diff
      (BorelOuterMeasure.measurable_le_caratheodory (μ := μ) _ ((hV_open i).measurableSet)) hE using 1) (by
    exact lt_of_le_of_lt ( μ.mono ( show V i \ E ⊆ V i from Set.diff_subset ) ) ( hVfin i )) (δ i) (hδpos i);
  choose C hCclosed hCsub hCdiff using h_closed_approx_i;
  refine' not_lt_of_ge ( h_contra ( ⋃ i, V i \ C i ) ( isOpen_iUnion fun i => IsOpen.sdiff ( hV_open i ) ( hCclosed i ) ) _ ) _;
  · exact fun x hx => by rcases Set.mem_iUnion.1 ( hEV hx ) with ⟨ i, hi ⟩ ; exact Set.mem_iUnion.2 ⟨ i, ⟨ hi, fun hi' => by have := hCsub i hi'; aesop ⟩ ⟩ ;
  · refine' lt_of_le_of_lt ( MeasureTheory.measure_mono _ ) ( lt_of_le_of_lt ( MeasureTheory.measure_iUnion_le _ ) ( lt_of_le_of_lt ( ENNReal.tsum_le_tsum fun i => le_of_lt ( hCdiff i ) ) hδsum ) );
    simp +contextual [ Set.subset_def ]


/- **TODO: Radon measure iff Borel regular and locally finite**:
Let μ be an outer measure on a topological space X. Then μ is a Radon measure if and only if μ is
locally finite and Borel regular. -/

/- Refernce: Mattila's book, Corollary 1.11, page 12.-/


/-- **Restriction of a Borel regular measure is Radon**: if `μ` is a Borel regular outer measure on
a topological space `X` with the Borel σ-algebra, and `E ⊆ X` is a μ-measurable set with
`μ E < ∞`, then the restriction `μ.restrict E` is a Radon measure.

We assume `PseudoMetricSpace X` and `SigmaCompactSpace X` to obtain
inner regularity with compact sets, following standard measure theory texts
(cf. Evans–Gariepy, Theorem 1.10). -/
theorem BorelRegularOuterMeasure.restrict_isRadon
    (μ : OuterMeasure X) [BorelRegularOuterMeasure μ] (E : Set X)
    (hE_meas : μ.IsCaratheodory E) (hE_fin : μ E < ⊤) :
    RadonOuterMeasure (OuterMeasure.restrict E μ) := by
  -- Borel ≤ caratheodory for restricted measure
  have h_cara : ‹MeasurableSpace X› ≤ (OuterMeasure.restrict E μ).caratheodory :=
    caratheodory_restrict_of_caratheodory μ E
      (BorelOuterMeasure.measurable_le_caratheodory (μ := μ))
  -- Get the Borel superset B ⊇ E with μ(B) = μ(E)
  obtain ⟨B, hB_meas, hEB, hμEB⟩ :=
    BorelRegularOuterMeasure.exists_measurable_superset (μ := μ) E
  -- μ(B \ E) = 0
  have h_null : μ (B \ E) = 0 :=
    measure_diff_eq_zero μ E B hEB hμEB hE_meas hE_fin
  -- restrict E μ = restrict B μ
  have h_eq_om : OuterMeasure.restrict E μ = OuterMeasure.restrict B μ :=
    restrict_eq_of_null_diff μ E B hEB h_null
  -- caratheodory for restrict B μ
  have h_cara_B : ‹MeasurableSpace X› ≤ (OuterMeasure.restrict B μ).caratheodory :=
    caratheodory_restrict_of_caratheodory μ B
      (BorelOuterMeasure.measurable_le_caratheodory (μ := μ))
  -- Relate toMeasure of restricted outer measure to Measure.restrict
  have h_eq_meas : (OuterMeasure.restrict E μ).toMeasure h_cara =
      (μ.toMeasure (BorelOuterMeasure.measurable_le_caratheodory (μ := μ))).restrict B := by
    have step1 : (OuterMeasure.restrict E μ).toMeasure h_cara =
        (OuterMeasure.restrict B μ).toMeasure h_cara_B := by
      ext s hs
      simp only [toMeasure_apply _ _ hs]
      exact congrFun (congrArg OuterMeasure.measureOf h_eq_om) s
    rw [step1]
    exact toMeasure_restrict_eq μ B hB_meas
      (BorelOuterMeasure.measurable_le_caratheodory (μ := μ)) h_cara_B
  -- Build the RadonOuterMeasure proof
  letI : BorelRegularOuterMeasure (OuterMeasure.restrict E μ) :=
    BorelRegularOuterMeasure.restrict μ E hE_meas hE_fin
  refine { regular_toMeasure := ?_ }
  rw [h_eq_meas]
  -- The restricted measure is finite, hence Regular by Mathlib instances
  have : IsFiniteMeasure
      ((μ.toMeasure (BorelOuterMeasure.measurable_le_caratheodory (μ := μ))).restrict B) := by
    rw [isFiniteMeasure_restrict]
    rw [toMeasure_apply₀ _ _ (hB_meas.nullMeasurableSet)]
    rw [← hμEB]
    exact hE_fin.ne
  exact inferInstance

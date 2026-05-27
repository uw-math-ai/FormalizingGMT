import Mathlib

import FormalizingGMT.«Project Versions».Measures.Basic

open scoped BigOperators Real Nat Classical Pointwise

open MeasureTheory MeasureTheory.OuterMeasure Set

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
    convert this using 2 <;> simp +decide [ Set.union_inter_cancel_left, Set.union_diff_cancel_left, hEB ];
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
  refine' le_antisymm _ _;
  · exact fun s => by simpa using μ.mono ( Set.inter_subset_inter_right _ hEB ) ;
  · intro AA; refine' le_trans _ ( MeasureTheory.measure_mono _ );
    rotate_left;
    exact AA \ ( B \ E );
    · grind;
    · simp +decide [*];
      exact le_trans (MeasureTheory.measure_mono (show AA ∩ B ⊆ (AA \ (B \ E) ∩ E) ∪ (B \ E) by intro x hx; by_cases h : x ∈ E <;> aesop)) (MeasureTheory.measure_union_le _ _) |> le_trans <| by aesop;

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
for any set S there exists a Borel set F ⊇ S with (μ↾E)(S) = (μ↾E)(F).

The construction is: let G ⊇ S∩E be Borel with μ(G) = μ(S∩E), let C ⊇ E be Borel with
μ(C) = μ(E), and let D ⊇ S∩(C\E) be Borel with μ(D) = μ(S∩(C\E)) = 0.
Then F = G ∪ Cᶜ ∪ D works.
-/
lemma IsBorelRegular.exists_borel_superset_restrict
    (μ : OuterMeasure X) (hμ : IsBorelRegular μ) (E : Set X)
    (hE_meas : μ.IsCaratheodory E) (hE_fin : μ E < ⊤)
    (S : Set X) :
    ∃ F : Set X, MeasurableSet F ∧ S ⊆ F ∧
      (OuterMeasure.restrict E μ) S = (OuterMeasure.restrict E μ) F := by
  -- By assumption, there exists a Borel set $C \supseteq E$ with $\mu(C) = \mu(E)$.
  obtain ⟨C, hC_meas, hC⟩ : ∃ C : Set X, MeasurableSet C ∧ E ⊆ C ∧ μ E = μ C := by
    exact hμ.2 E;
  -- By assumption, there exists a Borel set $G \supseteq S \cap E$ with $\mu(G) = \mu(S \cap E)$.
  obtain ⟨G, hG_meas, hG⟩ : ∃ G : Set X, MeasurableSet G ∧ S ∩ E ⊆ G ∧ μ G = μ (S ∩ E) := by
    have := hμ.2 ( S ∩ E ) ; aesop;
  -- By assumption, there exists a Borel set $D \supseteq S \cap (C \setminus E)$ with $\mu(D) = \mu(S \cap (C \setminus E)) = 0$.
  obtain ⟨D, hD_meas, hD⟩ : ∃ D : Set X, MeasurableSet D ∧ S ∩ (C \ E) ⊆ D ∧ μ D = 0 := by
    have hD_zero : μ (C \ E) = 0 := by
      apply measure_diff_eq_zero μ E C hC.left hC.right hE_meas hE_fin;
    have := hμ.2 ( C \ E );
    exact ⟨ this.choose, this.choose_spec.1, Set.Subset.trans ( Set.inter_subset_right ) this.choose_spec.2.1, this.choose_spec.2.2.symm.trans hD_zero ⟩;
  refine' ⟨ G ∪ Cᶜ ∪ D, _, _, _ ⟩;
  · exact MeasurableSet.union ( MeasurableSet.union hG_meas ( hC_meas.compl ) ) hD_meas;
  · grind +splitImp;
  · have h_eq : μ (S ∩ E) ≤ μ ((G ∪ Cᶜ ∪ D) ∩ E) ∧ μ ((G ∪ Cᶜ ∪ D) ∩ E) ≤ μ (G ∩ E) + μ (D ∩ E) := by
      refine' ⟨ μ.mono _, _ ⟩;
      · exact fun x hx => ⟨ Or.inl <| Or.inl <| hG.1 hx, hx.2 ⟩;
      · refine' le_trans ( μ.mono _ ) ( MeasureTheory.measure_union_le _ _ );
        grind;
    have h_eq : μ (G ∩ E) ≤ μ G ∧ μ (D ∩ E) ≤ μ D := by
      exact ⟨ μ.mono ( Set.inter_subset_left ), μ.mono ( Set.inter_subset_left ) ⟩;
    simp_all +decide [ OuterMeasure.restrict_apply ];
    grind

/-- The restriction of a Borel regular outer measure to a Carathéodory-measurable set
of finite measure is again Borel regular. -/
lemma IsBorelRegular.restrict_isBorelRegular
    (μ : OuterMeasure X) (hμ : IsBorelRegular μ) (E : Set X)
    (hE_meas : μ.IsCaratheodory E) (hE_fin : μ E < ⊤) :
    IsBorelRegular (OuterMeasure.restrict E μ) := by
  exact ⟨caratheodory_restrict_of_caratheodory μ E hμ.1,
    fun S => IsBorelRegular.exists_borel_superset_restrict μ hμ E hE_meas hE_fin S⟩

/-- **Theorem 1.7 / Theorem 0.3**: If `μ` is a Borel regular outer measure on a topological
space `X` (with the Borel σ-algebra), and `E ⊆ X` is a μ-measurable set with `μ(E) < ∞`,
then the restriction `μ.restrict E` is a Radon measure.

We assume `PseudoMetricSpace X` and `SigmaCompactSpace X` to obtain
inner regularity with compact sets, following standard measure theory texts
(cf. Evans–Gariepy, Theorem 1.10). -/
theorem IsBorelRegular.restrict_isRadon
    (μ : OuterMeasure X) (hμ : IsBorelRegular μ) (E : Set X)
    (hE_meas : μ.IsCaratheodory E) (hE_fin : μ E < ⊤) :
    IsRadon (OuterMeasure.restrict E μ) := by
  -- Borel ≤ caratheodory for restricted measure
  have h_cara : ‹MeasurableSpace X› ≤ (OuterMeasure.restrict E μ).caratheodory :=
    caratheodory_restrict_of_caratheodory μ E hμ.1
  -- Get the Borel superset B ⊇ E with μ(B) = μ(E)
  obtain ⟨B, hB_meas, hEB, hμEB⟩ := hμ.2 E
  -- μ(B \ E) = 0
  have h_null : μ (B \ E) = 0 :=
    measure_diff_eq_zero μ E B hEB hμEB hE_meas hE_fin
  -- restrict E μ = restrict B μ
  have h_eq_om : OuterMeasure.restrict E μ = OuterMeasure.restrict B μ :=
    restrict_eq_of_null_diff μ E B hEB h_null
  -- caratheodory for restrict B μ
  have h_cara_B : ‹MeasurableSpace X› ≤ (OuterMeasure.restrict B μ).caratheodory :=
    caratheodory_restrict_of_caratheodory μ B hμ.1
  -- Relate toMeasure of restricted outer measure to Measure.restrict
  have h_eq_meas : (OuterMeasure.restrict E μ).toMeasure h_cara =
      (μ.toMeasure hμ.1).restrict B := by
    have step1 : (OuterMeasure.restrict E μ).toMeasure h_cara =
        (OuterMeasure.restrict B μ).toMeasure h_cara_B := by
      ext s hs
      simp only [toMeasure_apply _ _ hs]
      exact congrFun (congrArg OuterMeasure.measureOf h_eq_om) s
    rw [step1]
    exact toMeasure_restrict_eq μ B hB_meas hμ.1 h_cara_B
  -- Build the IsRadon proof
  have h_br : IsBorelRegular (OuterMeasure.restrict E μ) :=
    IsBorelRegular.restrict_isBorelRegular μ hμ E hE_meas hE_fin
  refine ⟨h_br, h_cara, ?_⟩
  rw [h_eq_meas]
  -- The restricted measure is finite, hence Regular by Mathlib instances
  have : IsFiniteMeasure ((μ.toMeasure hμ.1).restrict B) := by
    rw [isFiniteMeasure_restrict]
    rw [toMeasure_apply₀ _ _ (hB_meas.nullMeasurableSet)]
    rw [← hμEB]
    exact hE_fin.ne
  exact inferInstance

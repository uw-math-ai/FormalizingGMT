import Mathlib

import FormalizingGMT.«Project Versions».Measures.Basic
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
  refine ⟨h_cara, ?_⟩
  rw [h_eq_meas]
  -- The restricted measure is finite, hence Regular by Mathlib instances
  have : IsFiniteMeasure ((μ.toMeasure hμ.1).restrict B) := by
    rw [isFiniteMeasure_restrict]
    rw [toMeasure_apply₀ _ _ (hB_meas.nullMeasurableSet)]
    rw [← hμEB]
    exact hE_fin.ne
  exact inferInstance

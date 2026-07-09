import Mathlib.MeasureTheory.Measure.Regular

open MeasureTheory MeasureTheory.OuterMeasure MeasureTheory.Measure Set Filter
open scoped ENNReal Topology Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

/- This file contains basic properties of outer measures that are frequently used in geometric
measure theory. -/

/-!
## Notions of regularity for outer measures
-/

/- **TODO (Nathan): Locally finite** outer measure: an outer measure on a topological space is locally
finite if it assigns finite measure to every compact set. -/

/- **Borel** outer measure: an outer measure `μ` on a topological space `X` equipped with the
Borel σ-algebra is a Borel outer measure if all Borel sets are measurable for `μ`. -/
class BorelOuterMeasure {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) : Prop where
  measurable_le_caratheodory : ‹MeasurableSpace X› ≤ μ.caratheodory


/- **TODO (Theo): regular** outer measure: an outer measure `μ` on a space `X` is
regular if for every set `E`, there exists a `μ`-measurable set set `F ⊇ E` with `μ E = μ F`. -/
class IsRegularOuterMeasure {X : Type*} (μ : OuterMeasure X) : Prop where
  exists_caratheodory_superset :
    ∀ E : Set X, ∃ F : Set X,
      μ.IsCaratheodory F ∧
      E ⊆ F ∧
      μ E = μ F

/-- **Borel regular** outer measure: an outer measure `μ` on a topological space `X`
equipped with the Borel σ-algebra is Borel regular if:
1. All Borel sets are Carathéodory measurable for `μ`.
2. For every set `E`, there exists a Borel set `F ⊇ E` with `μ E = μ F`. -/
class IsBorelRegular {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) : Prop extends BorelOuterMeasure μ where
  exists_measurable_superset :
    ∀ E : Set X, ∃ F : Set X,
      MeasurableSet F ∧
      E ⊆ F ∧
      μ E = μ F

/-- **Radon** outer measure: an outer measure `μ` on a topological space `X` equipped with the
Borel σ-algebra is a Radon outer measure if:
1. All Borel subsets of `X` are Carathéodory measurable for `μ`.
2. The associated Borel measure via `toMeasure` satisfies `Measure.Regular`. -/
class IsRadon {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) : Prop extends IsBorelRegular μ where
  regular_toMeasure :
    (μ.toMeasure (BorelOuterMeasure.measurable_le_caratheodory (μ := μ))).Regular

/-- **Support** of an outer measure: an outer measure `μ` on a topological space `X` has
support the set of points `x` such that every neighborhood of `x` has positive `μ`-measure.
(By monotonicity of `μ`, this equals the set of `x` whose every *open* neighborhood has positive
measure.) -/
def SupportOuterMeasure {X : Type*} [TopologicalSpace X]
    (μ : OuterMeasure X) : Set X :=
  {x | ∀ U ∈ 𝓝 x, 0 < μ U}


/-!
## Basic facts about regular outer measures
-/

/- **TODO (Theo)** Lemma: If `μ` is a regular outer measure on a space `X` and
`A⊆X`, then `A` is `μ`-measurable if and only if `μ(A)+μ(X∖A)=μ(X)`.

Reference: Bogachev - Measure Theory I, Proposition 1.11.7-/
theorem isCaratheodory_iff_add_compl_eq_univ_of_isRegularOuterMeasure
    {X : Type*} (μ : OuterMeasure X) (hμ : IsRegularOuterMeasure μ)
    (hμ_univ : μ univ < ∞) (A : Set X) :
    μ.IsCaratheodory A ↔ μ A + μ Aᶜ = μ univ := by
  constructor
  · intro hA
    simpa [Set.diff_eq] using (hA univ).symm
  · intro hA_eq
    obtain ⟨F, hF_meas, hAF, hμAF⟩ := hμ.exists_caratheodory_superset A
    have hμF_ne_top : μ F ≠ ∞ :=
      ne_of_lt ((measure_mono (subset_univ F)).trans_lt hμ_univ)
    have hμFc_ne_top : μ Fᶜ ≠ ∞ :=
      ne_of_lt ((measure_mono (subset_univ Fᶜ)).trans_lt hμ_univ)
    have h_compl_eq : μ Aᶜ = μ Fᶜ := by
      rw [← ENNReal.add_right_inj hμF_ne_top]
      calc
        μ F + μ Aᶜ = μ A + μ Aᶜ := by rw [hμAF]
        _ = μ univ := hA_eq
        _ = μ F + μ Fᶜ := by simpa [Set.diff_eq] using hF_meas univ
    have h_diff_zero : μ (F \ A) = 0 := by
      have hFc_subset_Ac : Fᶜ ⊆ Aᶜ := fun x hxF hxA => hxF (hAF hxA)
      have hsplit : μ Aᶜ = μ (F \ A) + μ Fᶜ := by
        simpa [Set.compl_inter, Set.diff_eq, Set.inter_assoc, Set.inter_comm,
          Set.inter_left_comm, inter_eq_self_of_subset_right hFc_subset_Ac] using hF_meas Aᶜ
      rw [h_compl_eq] at hsplit
      have hcancel : μ (F \ A) + μ Fᶜ = 0 + μ Fᶜ := by
        simpa using hsplit.symm
      exact (ENNReal.add_left_inj hμFc_ne_top).mp hcancel
    have h_diff_meas : μ.IsCaratheodory (F \ A) := by
      rw [OuterMeasure.isCaratheodory_iff_le']
      intro T
      have hT_inter_zero : μ (T ∩ (F \ A)) = 0 :=
        measure_mono_null (show T ∩ (F \ A) ⊆ F \ A from inter_subset_right) h_diff_zero
      calc
        μ (T ∩ (F \ A)) + μ (T \ (F \ A)) = μ (T \ (F \ A)) := by
          simp [hT_inter_zero]
        _ ≤ μ T := measure_mono diff_subset
    have hA_eq_set : F \ (F \ A) = A := by
      ext x
      constructor
      · intro hx
        by_contra hxA
        exact hx.2 ⟨hx.1, hxA⟩
      · intro hx
        exact ⟨hAF hx, fun h => h.2 hx⟩
    rw [← hA_eq_set]
    exact μ.isCaratheodory_diff hF_meas h_diff_meas

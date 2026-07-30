/-
Copyright (c) 2026 UW Math AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ignacio Tejeda, Theodore Meek, Annie Cao, Nathan Pao
-/
module

public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Regular outer measures

This file defines regularity conditions and support for outer measures on topological spaces,
together with basic facts about finite regular outer measures.

## References

* V. I. Bogachev, *Measure Theory I*, Proposition 1.11.7
-/

@[expose] public section

open MeasureTheory MeasureTheory.OuterMeasure MeasureTheory.Measure Set Filter
open scoped ENNReal Topology Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-- An outer measure on a topological space is finite on compact sets if it assigns finite measure
to every compact set. -/
class IsFiniteOnCompactOuterMeasure {X : Type*} [TopologicalSpace X]
    (μ : OuterMeasure X) : Prop where
  /-- Compact sets have finite outer measure. -/
  measure_lt_top_of_isCompact :
    ∀ ⦃K : Set X⦄, IsCompact K → μ K < ∞

/-- An outer measure `μ` on a topological space `X` equipped with the Borel σ-algebra is Borel if
all Borel sets are measurable for `μ`. -/
class BorelOuterMeasure {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) : Prop where
  /-- Every Borel set is Carathéodory-measurable. -/
  measurable_le_caratheodory : ‹MeasurableSpace X› ≤ μ.caratheodory

/-- An outer measure `μ` is regular if every set `E` has a Carathéodory-measurable superset `F`
with `μ E = μ F`. -/
class RegularOuterMeasure {X : Type*}
    (μ : OuterMeasure X) : Prop where
  /-- Every set has a Carathéodory-measurable superset with the same outer measure. -/
  exists_measurable_superset :
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
  /-- Every set has a measurable superset with the same outer measure. -/
  exists_measurable_superset :
    ∀ E : Set X, ∃ F : Set X,
      MeasurableSet F ∧
      E ⊆ F ∧
      μ E = μ F

/-- Every Borel regular outer measure is regular. -/
instance IsBorelRegular.toRegularOuterMeasure {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : OuterMeasure X) [IsBorelRegular μ] :
    RegularOuterMeasure μ where
  exists_measurable_superset E := by
    obtain ⟨F, hF, hEF, hμF⟩ :=
      IsBorelRegular.exists_measurable_superset (μ := μ) E
    exact ⟨F, BorelOuterMeasure.measurable_le_caratheodory (μ := μ) F hF, hEF, hμF⟩

/-- **Radon** outer measure: an outer measure `μ` on a topological space `X` equipped with the
Borel σ-algebra is a Radon outer measure if:
1. All Borel subsets of `X` are Carathéodory measurable for `μ`.
2. The associated Borel measure via `toMeasure` satisfies `Measure.Regular`. -/
class IsRadon {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) : Prop extends IsBorelRegular μ where
  /-- The measure associated to the outer measure is regular. -/
  regular_toMeasure :
    (μ.toMeasure (BorelOuterMeasure.measurable_le_caratheodory (μ := μ))).Regular

/-- **Support** of an outer measure: an outer measure `μ` on a topological space `X` has
support the set of points `x` such that every neighborhood of `x` has positive `μ`-measure. -/
def SupportOuterMeasure {X : Type*} [TopologicalSpace X]
    (μ : OuterMeasure X) : Set X :=
  {x | ∀ U ∈ 𝓝 x, 0 < μ U}

/-!
## Basic facts about regular outer measures
-/

-- TODO: Check whether this lemma already exists in Mathlib and belongs in another file.
/-- Sets with zero outer measure are Carathéodory-measurable. -/
lemma isCaratheodory_of_measure_eq_zero {X : Type*} {μ : OuterMeasure X} {A : Set X}
    (hA : μ A = 0) : μ.IsCaratheodory A := by
  rw [OuterMeasure.isCaratheodory_iff_le']
  intro T
  simpa [measure_mono_null inter_subset_right hA] using
    (measure_mono (diff_subset : T \ A ⊆ T) : μ (T \ A) ≤ μ T)

/-- The nontrivial direction of Bogachev's Proposition 1.11.7. -/
lemma isCaratheodory_of_measure_add_compl_eq_univ
    {X : Type*} (μ : OuterMeasure X) [RegularOuterMeasure μ]
    (hμ : μ univ ≠ ∞) {A : Set X} (hA : μ A + μ Aᶜ = μ univ) :
    μ.IsCaratheodory A := by
  rcases RegularOuterMeasure.exists_measurable_superset (μ := μ) A with ⟨F, hF, hAF, hμAF⟩
  have hfin (E : Set X) : μ E ≠ ∞ := ne_top_of_le_ne_top hμ (measure_mono (subset_univ E))
  have hAc : μ Aᶜ = μ Fᶜ := (ENNReal.add_right_inj (hfin F)).mp <| by
    simpa [hμAF, Set.diff_eq] using hA.trans (hF univ)
  have hFA : μ (F \ A) = 0 := (ENNReal.add_left_inj (hfin Fᶜ)).mp <| by
    simpa [hAc, Set.diff_eq, Set.compl_inter, Set.inter_assoc, Set.inter_comm,
      Set.inter_left_comm, inter_eq_self_of_subset_right (compl_subset_compl.mpr hAF)]
      using (hF Aᶜ).symm
  convert μ.isCaratheodory_diff hF (isCaratheodory_of_measure_eq_zero hFA) using 1; aesop

/-- A set is Carathéodory-measurable if and only if its outer measure plus the outer measure of its
complement equals the outer measure of the whole space. -/
lemma isCaratheodory_iff_measure_add_compl_eq_univ
    {X : Type*} (μ : OuterMeasure X) [RegularOuterMeasure μ]
    (hμ : μ univ ≠ ∞) (A : Set X) :
    μ.IsCaratheodory A ↔ μ A + μ Aᶜ = μ univ := by
  refine ⟨fun hA => ?_, isCaratheodory_of_measure_add_compl_eq_univ μ hμ⟩
  simpa [Set.diff_eq] using (hA univ).symm

/-- If `μ` is a regular outer measure on `X`, then for every set `A`, `μ A` is the infimum
of `μ M` over all Carathéodory-measurable supersets `M` of `A`. -/
lemma measure_eq_iInf_measurable_superset
    {X : Type*} (μ : OuterMeasure X) [RegularOuterMeasure μ] (A : Set X) :
    μ A = ⨅ (M : Set X) (_ : μ.IsCaratheodory M) (_ : A ⊆ M), μ M :=
  le_antisymm
    (le_iInf fun _ => le_iInf fun _ => le_iInf fun h => measure_mono h)
    (let ⟨F, hF, hAF, hμF⟩ := RegularOuterMeasure.exists_measurable_superset (μ := μ) A
     iInf_le_of_le F (iInf_le_of_le hF (iInf_le_of_le hAF hμF.symm.le)))

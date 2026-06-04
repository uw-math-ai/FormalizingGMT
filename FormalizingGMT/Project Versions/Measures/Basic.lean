import Mathlib

open MeasureTheory MeasureTheory.OuterMeasure MeasureTheory.Measure Set Filter
open scoped ENNReal Topology Pointwise

set_option relaxedAutoImplicit false
set_option autoImplicit false

/- This file contains definitions for some of the basic types of measures needed in
   Geometric Measure Theory: Borel regular measures, Radon measures, and Hausdorff content. -/

/-
## Notions of regularity for measures-/

/-- An outer measure `μ` on a topological space `X` (equipped with the Borel σ-algebra) is
**Borel regular** if:
1. All Borel sets are Carathéodory measurable for `μ`.
2. For every set `E`, there exists a Borel set `F ⊇ E` with `μ(E) = μ(F)`. -/
def IsBorelRegular {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) : Prop :=
  ‹MeasurableSpace X› ≤ μ.caratheodory ∧
  ∀ (E : Set X), ∃ (F : Set X),
    MeasurableSet F ∧
    E ⊆ F ∧
    μ E = μ F

/-- An outer measure `μ` on a topological space `X` (equipped with the Borel σ-algebra) is a
**Radon measure** if:
1. All Borel subsets of `X` are Carathéodory measurable for `μ`.
2. The associated Borel measure (via `toMeasure`) satisfies `Measure.Regular`. -/
def IsRadon {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : OuterMeasure X) : Prop :=
  (IsBorelRegular μ) ∧ ∃ (h : ‹MeasurableSpace X› ≤ μ.caratheodory), (μ.toMeasure h).Regular


def BorelOuterMeasurable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
   (μ : OuterMeasure X) : Prop :=
   ‹MeasurableSpace X› ≤ μ.caratheodory

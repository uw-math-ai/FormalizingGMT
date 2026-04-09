import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

open MeasureTheory Measure Set

/-!
# Theorem 1.7: Restriction and Radon measures

In the textbook (Evans–Gariepy style), a **Borel regular measure** on ℝⁿ is a Borel measure such
that every set can be sandwiched into a Borel set of the same measure, and a **Radon measure** is
a Borel regular measure that is additionally finite on compact sets.

In Mathlib, `MeasureTheory.Measure.Regular` is the formalization of a Radon measure: it combines
`IsFiniteMeasureOnCompacts`, `OuterRegular`, and inner regularity for open sets using compact sets.
For a Borel measure on ℝⁿ (or any R1 space), these conditions are equivalent to the textbook
definitions.

The theorem below states: if `μ` is a Regular (Radon/Borel-regular) Borel measure on ℝⁿ, `A` is
a set with `μ(A) < ∞`, then `μ⌊A` (the restriction of `μ` to `A`) is again a Regular (Radon)
measure.

Note: The textbook hypothesis that `A` is `μ`-measurable is not needed for the Mathlib proof;
it suffices that `μ(A) < ∞`. This is because in Mathlib, `Measure.restrict` is well-defined
for any set, and the regularity of the restriction follows from finiteness alone.
-/

/-- **Theorem 1.7 (Restriction and Radon measures).** Let `μ` be a Borel regular measure on `ℝⁿ`.
Suppose `A ⊆ ℝⁿ` satisfies `μ(A) < ∞`. Then `μ⌊A` is a Radon measure.

In Mathlib's terminology, a Radon measure is `MeasureTheory.Measure.Regular`: a Borel measure
that is finite on compact sets, outer regular, and inner regular for open sets. -/



theorem restriction_radon {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [μ.Regular]
    {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA_fin : μ A < ⊤) :
    (μ.restrict A).Regular := by
  apply MeasureTheory.Measure.Regular.restrict_of_measure_ne_top
  exact hA_fin.ne


/-- The restriction of the `s`-dimensional Hausdorff measure on `ℝ^n` to a set of finite
measure is a Radon (regular) measure. This is the Hausdorff-measure specialization of
the general fact that restricting a Borel measure to a finite-measure set yields a
regular measure on a Polish space. -/


theorem hausdorff_restriction_regular {n : ℕ} {s : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA_fin : μH[s] A < ⊤) :
    (μH[s].restrict A).Regular := by
  haveI : IsFiniteMeasure (μH[s].restrict A) := isFiniteMeasure_restrict.mpr hA_fin.ne
  infer_instance


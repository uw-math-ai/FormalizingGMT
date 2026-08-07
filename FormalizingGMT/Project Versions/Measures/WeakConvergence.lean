/-
Copyright (c) 2026 FormalizingGMT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalizingGMT contributors
-/

import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Bornology.Basic
import FormalizingGMT.«Project Versions».Measures.Basic

/-!
# Weak convergence of Radon outer measures

This file defines the three conditions for weak convergence of Radon outer measures appearing in
Evans--Gariepy, Revised Edition, Theorem 1.40. The source proves their equivalence for Radon
measures on Euclidean space.
-/

open scoped CompactlySupported
open Filter Topology

noncomputable section

namespace MeasureTheory

/-- A sequence of Radon outer measures `μ` converges weakly to a Radon outer measure `ν` if
integrals against every real-valued compactly supported continuous function converge.

Since an outer measure cannot be integrated against directly, each integral uses the Borel measure
associated to the corresponding Radon outer measure. This is called weak convergence by
Evans--Gariepy and is also commonly called vague convergence. -/
def OuterMeasure.WeaklyConverges
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : ℕ → OuterMeasure X) (ν : OuterMeasure X)
    (hμ : ∀ k, RadonOuterMeasure (μ k)) (hν : RadonOuterMeasure ν) : Prop :=
  ∀ f : C_c(X, ℝ),
    Tendsto
      (fun k ↦ ∫ x, f x ∂(μ k).toMeasure (hμ k).measurable_le_caratheodory)
      atTop
      (𝓝 (∫ x, f x ∂ν.toMeasure hν.measurable_le_caratheodory))

/-- Evans--Gariepy, Revised Edition, Theorem 1.40(ii): the compact-set upper bound and
open-set lower bound characterizing weak convergence.

Both clauses together constitute condition (ii); neither clause separately is equivalent to weak
convergence. -/
def OuterMeasure.WeaklyConvergesByCompactOpenBounds
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : ℕ → OuterMeasure X) (ν : OuterMeasure X) : Prop :=
  (∀ K : Set X, IsCompact K →
      atTop.limsup (fun k ↦ μ k K) ≤ ν K) ∧
    ∀ U : Set X, IsOpen U →
      ν U ≤ atTop.liminf (fun k ↦ μ k U)

/-- Evans--Gariepy, Revised Edition, Theorem 1.40(iii): convergence on every bounded Borel
continuity set of the limit outer measure.

Under `BorelSpace X`, `MeasurableSet B` says that `B` is Borel. For Euclidean space,
`Bornology.IsBounded B` is the usual metric boundedness condition. -/
def OuterMeasure.WeaklyConvergesOnBoundedContinuitySets
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [Bornology X]
    (μ : ℕ → OuterMeasure X) (ν : OuterMeasure X) : Prop :=
  ∀ B : Set X, Bornology.IsBounded B → MeasurableSet B →
    ν (frontier B) = 0 →
      Tendsto (fun k ↦ μ k B) atTop (𝓝 (ν B))

end MeasureTheory

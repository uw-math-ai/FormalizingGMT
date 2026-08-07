/-
Copyright (c) 2026 FormalizingGMT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalizingGMT contributors
-/

import Mathlib.MeasureTheory.Integral.CompactlySupported
import FormalizingGMT.«Project Versions».Measures.Basic

/-!
# Weak convergence of Radon outer measures

This file defines weak convergence of Radon outer measures using compactly supported continuous
test functions.
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

end MeasureTheory

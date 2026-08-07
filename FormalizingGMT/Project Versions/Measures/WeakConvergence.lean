/-
Copyright (c) 2026 FormalizingGMT contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalizingGMT contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import FormalizingGMT.«Project Versions».Measures.Basic

/-!
# Weak convergence of Radon outer measures

This file defines the three conditions for weak convergence of Radon outer measures appearing in
Evans--Gariepy, Revised Edition, Theorem 1.40, and proves their equivalence for Radon outer
measures on Euclidean space.
-/

open scoped CompactlySupported ENNReal NNReal
open Filter Function Set Topology

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

/-! ## Equivalence on Euclidean space -/

private def associatedMeasure {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : OuterMeasure X) (hμ : RadonOuterMeasure μ) : Measure X :=
  μ.toMeasure hμ.measurable_le_caratheodory

private theorem finiteMeasure_tendsto_of_open_liminf_of_mass_tendsto
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [Nonempty X] (μs : ℕ → FiniteMeasure X) (μ : FiniteMeasure X)
    (hopen : ∀ G : Set X, IsOpen G →
      (μ : Measure X) G ≤ atTop.liminf (fun k ↦ (μs k : Measure X) G))
    (hmass : Tendsto (fun k ↦ (μs k).mass) atTop (𝓝 μ.mass)) :
    Tendsto μs atTop (𝓝 μ) := by
  by_cases hμzero : μ = 0
  · subst μ
    apply FiniteMeasure.tendsto_zero_of_tendsto_zero_mass
    simpa using hmass
  have hmass_ne : μ.mass ≠ 0 := μ.mass_nonzero_iff.mpr hμzero
  have heventually_nonzero : ∀ᶠ k in atTop, μs k ≠ 0 := by
    simp_rw [← FiniteMeasure.mass_nonzero_iff]
    exact hmass (isOpen_compl_singleton.mem_nhds hmass_ne)
  have hmass_ennreal :
      Tendsto (fun k ↦ ((μs k).mass : ℝ≥0∞)) atTop (𝓝 (μ.mass : ℝ≥0∞)) :=
    ENNReal.continuous_coe.continuousAt.tendsto.comp hmass
  have hmass_inv :
      Tendsto (fun k ↦ ((μs k).mass : ℝ≥0∞)⁻¹) atTop
        (𝓝 ((μ.mass : ℝ≥0∞)⁻¹)) :=
    tendsto_inv_iff.mpr hmass_ennreal
  apply (FiniteMeasure.tendsto_normalize_iff_tendsto hμzero).mp
  refine ⟨tendsto_of_forall_isOpen_le_liminf' (μ := μ.normalize)
    (μs := fun k ↦ (μs k).normalize) ?_, hmass⟩
  intro G hG
  have hnormalized_eventually :
      ∀ᶠ k in atTop,
        ((μs k).normalize : Measure X) G =
          ((μs k).mass : ℝ≥0∞)⁻¹ * (μs k : Measure X) G := by
    filter_upwards [heventually_nonzero] with k hk
    rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero (μ := μs k) hk]
    simp only [Measure.coe_smul, Pi.smul_apply, Measure.nnreal_smul_coe_apply,
      ENNReal.coe_inv ((μs k).mass_nonzero_iff.mpr hk)]
  calc
    (μ.normalize : Measure X) G =
        (μ.mass : ℝ≥0∞)⁻¹ * (μ : Measure X) G := by
      rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero (μ := μ) hμzero]
      simp only [Measure.coe_smul, Pi.smul_apply, Measure.nnreal_smul_coe_apply,
        ENNReal.coe_inv hmass_ne]
    _ ≤ atTop.liminf (fun k ↦ ((μs k).mass : ℝ≥0∞)⁻¹) *
        atTop.liminf (fun k ↦ (μs k : Measure X) G) := by
      rw [hmass_inv.liminf_eq]
      exact mul_le_mul_right (hopen G hG) _
    _ ≤ atTop.liminf (fun k ↦
        ((μs k).mass : ℝ≥0∞)⁻¹ * (μs k : Measure X) G) :=
      ENNReal.le_liminf_mul
    _ = atTop.liminf (fun k ↦ ((μs k).normalize : Measure X) G) :=
      (liminf_congr hnormalized_eventually).symm

private theorem weaklyConverges_imp_compactOpenBounds
    {n : ℕ} (μ : ℕ → OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (ν : OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : ∀ k, RadonOuterMeasure (μ k)) (hν : RadonOuterMeasure ν)
    (h : OuterMeasure.WeaklyConverges μ ν hμ hν) :
    OuterMeasure.WeaklyConvergesByCompactOpenBounds μ ν := by
  let μm : ℕ → Measure (EuclideanSpace ℝ (Fin n)) :=
    fun k ↦ associatedMeasure (μ k) (hμ k)
  let νm : Measure (EuclideanSpace ℝ (Fin n)) := associatedMeasure ν hν
  letI : νm.Regular := hν.regular_toMeasure
  constructor
  · intro K hK
    have hK_meas : MeasurableSet K := hK.measurableSet
    have hμK (k : ℕ) : μm k K = μ k K :=
      toMeasure_apply (μ k) (hμ k).measurable_le_caratheodory hK_meas
    have hνK : νm K = ν K :=
      toMeasure_apply ν hν.measurable_le_caratheodory hK_meas
    rw [← hνK]
    simp_rw [← hμK]
    change atTop.limsup (fun k ↦ μm k K) ≤ νm K
    rw [hK.measure_eq_biInf_integral_hasCompactSupport νm]
    simp only [le_iInf_iff]
    intro f hf_cont hf_compact hf_one hf_nonneg
    let fc : C_c(EuclideanSpace ℝ (Fin n), ℝ) :=
      ⟨⟨f, hf_cont⟩, hf_compact⟩
    have htendsto :
        Tendsto (fun k ↦ ENNReal.ofReal (∫ x, f x ∂μm k)) atTop
          (𝓝 (ENNReal.ofReal (∫ x, f x ∂νm))) := by
      apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      simpa only [fc, μm, νm, associatedMeasure] using h fc
    calc
      atTop.limsup (fun k ↦ μm k K) ≤
          atTop.limsup (fun k ↦ ENNReal.ofReal (∫ x, f x ∂μm k)) := by
        apply limsup_le_limsup _ (by isBoundedDefault) (by isBoundedDefault)
        filter_upwards [] with k
        letI : (μm k).Regular := (hμ k).regular_toMeasure
        exact (hf_cont.integrable_of_hasCompactSupport hf_compact).measure_le_integral
          (.of_forall hf_nonneg) fun x hx ↦ (hf_one hx).ge
      _ = ENNReal.ofReal (∫ x, f x ∂νm) := htendsto.limsup_eq
  · intro U hU
    have hU_meas : MeasurableSet U := hU.measurableSet
    have hμU (k : ℕ) : μm k U = μ k U :=
      toMeasure_apply (μ k) (hμ k).measurable_le_caratheodory hU_meas
    have hνU : νm U = ν U :=
      toMeasure_apply ν hν.measurable_le_caratheodory hU_meas
    rw [← hνU]
    simp_rw [← hμU]
    change νm U ≤ atTop.liminf (fun k ↦ μm k U)
    rw [hU.measure_eq_iSup_isCompact νm]
    simp only [iSup_le_iff]
    intro K hKU hK
    obtain ⟨f, hf_one, hf_compact, hf_support, hf_range⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
    let fc : C_c(EuclideanSpace ℝ (Fin n), ℝ) := ⟨f, hf_compact⟩
    have hf_zero : Set.EqOn f 0 Uᶜ := by
      intro x hx
      by_contra hfx
      exact hx (hf_support (subset_tsupport f hfx))
    have htendsto :
        Tendsto (fun k ↦ ENNReal.ofReal (∫ x, f x ∂μm k)) atTop
          (𝓝 (ENNReal.ofReal (∫ x, f x ∂νm))) := by
      apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      simpa only [fc, μm, νm, associatedMeasure] using h fc
    calc
      νm K ≤ ENNReal.ofReal (∫ x, f x ∂νm) := by
        exact f.continuous.integrable_of_hasCompactSupport hf_compact |>.measure_le_integral
          (.of_forall fun x ↦ (hf_range x).1) fun x hx ↦ (hf_one hx).ge
      _ = atTop.liminf (fun k ↦ ENNReal.ofReal (∫ x, f x ∂μm k)) :=
        htendsto.liminf_eq.symm
      _ ≤ atTop.liminf (fun k ↦ μm k U) := by
        apply liminf_le_liminf _ (by isBoundedDefault) (by isBoundedDefault)
        filter_upwards [] with k
        exact integral_le_measure (fun x _ ↦ (hf_range x).2)
          (fun x hx ↦ (hf_zero hx).le)

private theorem compactOpenBounds_imp_boundedContinuitySets
    {n : ℕ} (μ : ℕ → OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (ν : OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : ∀ k, RadonOuterMeasure (μ k)) (hν : RadonOuterMeasure ν)
    (h : OuterMeasure.WeaklyConvergesByCompactOpenBounds μ ν) :
    OuterMeasure.WeaklyConvergesOnBoundedContinuitySets μ ν := by
  let μm : ℕ → Measure (EuclideanSpace ℝ (Fin n)) :=
    fun k ↦ associatedMeasure (μ k) (hμ k)
  let νm : Measure (EuclideanSpace ℝ (Fin n)) := associatedMeasure ν hν
  intro B hB_bounded hB_meas hB_frontier
  have hμB (k : ℕ) : μm k B = μ k B :=
    toMeasure_apply (μ k) (hμ k).measurable_le_caratheodory hB_meas
  have hνB : νm B = ν B :=
    toMeasure_apply ν hν.measurable_le_caratheodory hB_meas
  rw [← hνB]
  simp_rw [← hμB]
  apply tendsto_measure_of_le_liminf_measure_of_limsup_measure_le
      (μ := νm) (μs := μm) interior_subset subset_closure
  · have hfrontier_meas : MeasurableSet (frontier B) := isClosed_frontier.measurableSet
    have hνfrontier : νm (frontier B) = ν (frontier B) :=
      toMeasure_apply ν hν.measurable_le_caratheodory hfrontier_meas
    have : νm (frontier B) = 0 := hνfrontier.trans hB_frontier
    simpa only [frontier] using this
  · have hopen := h.2 (interior B) isOpen_interior
    have hinterior_meas : MeasurableSet (interior B) := isOpen_interior.measurableSet
    have hμinterior (k : ℕ) : μm k (interior B) = μ k (interior B) :=
      toMeasure_apply (μ k) (hμ k).measurable_le_caratheodory hinterior_meas
    have hνinterior : νm (interior B) = ν (interior B) :=
      toMeasure_apply ν hν.measurable_le_caratheodory hinterior_meas
    rw [hνinterior]
    simpa only [hμinterior] using hopen
  · have hclosure_compact : IsCompact (closure B) := hB_bounded.isCompact_closure
    have hclosed := h.1 (closure B) hclosure_compact
    have hclosure_meas : MeasurableSet (closure B) := isClosed_closure.measurableSet
    have hμclosure (k : ℕ) : μm k (closure B) = μ k (closure B) :=
      toMeasure_apply (μ k) (hμ k).measurable_le_caratheodory hclosure_meas
    have hνclosure : νm (closure B) = ν (closure B) :=
      toMeasure_apply ν hν.measurable_le_caratheodory hclosure_meas
    rw [hνclosure]
    simpa only [hμclosure] using hclosed

private lemma exists_bounded_open_null_frontier_between
    {n : ℕ} (ν : OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (hν : RadonOuterMeasure ν) {K U : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ B : Set (EuclideanSpace ℝ (Fin n)),
      K ⊆ B ∧ B ⊆ U ∧ IsOpen B ∧ Bornology.IsBounded B ∧ ν (frontier B) = 0 := by
  let νm : Measure (EuclideanSpace ℝ (Fin n)) := associatedMeasure ν hν
  letI : νm.Regular := hν.regular_toMeasure
  letI : SFinite νm := inferInstance
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨r, hr, hnull⟩ :=
    exists_null_frontier_thickening νm K hδ
  let B := Metric.thickening r K
  have hB_open : IsOpen B := Metric.isOpen_thickening
  have hB_bounded : Bornology.IsBounded B := hK.isBounded.thickening
  have hB_frontier : ν (frontier B) = 0 := by
    rw [← toMeasure_apply ν hν.measurable_le_caratheodory
      isClosed_frontier.measurableSet]
    exact hnull
  refine ⟨B, Metric.self_subset_thickening hr.1 K, ?_, hB_open, hB_bounded, hB_frontier⟩
  exact (Metric.thickening_subset_cthickening_of_le hr.2.le K).trans hδU

private theorem boundedContinuitySets_imp_compactOpenBounds
    {n : ℕ} (μ : ℕ → OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (ν : OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (hν : RadonOuterMeasure ν)
    (h : OuterMeasure.WeaklyConvergesOnBoundedContinuitySets μ ν) :
    OuterMeasure.WeaklyConvergesByCompactOpenBounds μ ν := by
  let νm : Measure (EuclideanSpace ℝ (Fin n)) := associatedMeasure ν hν
  letI : νm.Regular := hν.regular_toMeasure
  constructor
  · intro K hK
    have hK_meas : MeasurableSet K := hK.measurableSet
    have hνK : νm K = ν K :=
      toMeasure_apply ν hν.measurable_le_caratheodory hK_meas
    rw [← hνK, K.measure_eq_iInf_isOpen νm]
    simp only [le_iInf_iff]
    intro U hKU hU
    obtain ⟨B, hKB, hBU, hB_open, hB_bounded, hB_frontier⟩ :=
      exists_bounded_open_null_frontier_between ν hν hK hU hKU
    have hB_meas : MeasurableSet B := hB_open.measurableSet
    have htendsto := h B hB_bounded hB_meas hB_frontier
    have hνB : νm B = ν B :=
      toMeasure_apply ν hν.measurable_le_caratheodory hB_meas
    calc
      atTop.limsup (fun k ↦ μ k K) ≤ atTop.limsup (fun k ↦ μ k B) := by
        apply limsup_le_limsup _ (by isBoundedDefault) (by isBoundedDefault)
        exact .of_forall fun k ↦ (μ k).mono hKB
      _ = ν B := htendsto.limsup_eq
      _ = νm B := hνB.symm
      _ ≤ νm U := νm.mono hBU
  · intro U hU
    have hνU : νm U = ν U :=
      toMeasure_apply ν hν.measurable_le_caratheodory hU.measurableSet
    rw [← hνU, hU.measure_eq_iSup_isCompact νm]
    simp only [iSup_le_iff]
    intro K hKU hK
    obtain ⟨B, hKB, hBU, hB_open, hB_bounded, hB_frontier⟩ :=
      exists_bounded_open_null_frontier_between ν hν hK hU hKU
    have hB_meas : MeasurableSet B := hB_open.measurableSet
    have htendsto := h B hB_bounded hB_meas hB_frontier
    have hνB : νm B = ν B :=
      toMeasure_apply ν hν.measurable_le_caratheodory hB_meas
    calc
      νm K ≤ νm B := νm.mono hKB
      _ = ν B := hνB
      _ = atTop.liminf (fun k ↦ μ k B) := htendsto.liminf_eq.symm
      _ ≤ atTop.liminf (fun k ↦ μ k U) := by
        apply liminf_le_liminf _ (by isBoundedDefault) (by isBoundedDefault)
        exact .of_forall fun k ↦ (μ k).mono hBU

private theorem compactOpenBounds_imp_weaklyConverges
    {n : ℕ} (μ : ℕ → OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (ν : OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : ∀ k, RadonOuterMeasure (μ k)) (hν : RadonOuterMeasure ν)
    (h : OuterMeasure.WeaklyConvergesByCompactOpenBounds μ ν) :
    OuterMeasure.WeaklyConverges μ ν hμ hν := by
  let μm : ℕ → Measure (EuclideanSpace ℝ (Fin n)) :=
    fun k ↦ associatedMeasure (μ k) (hμ k)
  let νm : Measure (EuclideanSpace ℝ (Fin n)) := associatedMeasure ν hν
  intro f
  obtain ⟨O, hfO, -, hO_open, hO_bounded, hO_frontier⟩ :=
    exists_bounded_open_null_frontier_between ν hν f.hasCompactSupport isOpen_univ
      (subset_univ _)
  have hO_meas : MeasurableSet O := hO_open.measurableSet
  have hμO_eq (k : ℕ) : μm k O = μ k O :=
    toMeasure_apply (μ k) (hμ k).measurable_le_caratheodory hO_meas
  have hνO_eq : νm O = ν O :=
    toMeasure_apply ν hν.measurable_le_caratheodory hO_meas
  have hμO_lt_top (k : ℕ) : μm k O < ∞ := by
    letI : (μm k).Regular := (hμ k).regular_toMeasure
    exact hO_bounded.measure_lt_top
  have hνO_lt_top : νm O < ∞ := by
    letI : νm.Regular := hν.regular_toMeasure
    exact hO_bounded.measure_lt_top
  let μO : ℕ → FiniteMeasure (EuclideanSpace ℝ (Fin n)) := fun k ↦
    ⟨(μm k).restrict O, isFiniteMeasure_restrict.mpr (hμO_lt_top k).ne⟩
  let νO : FiniteMeasure (EuclideanSpace ℝ (Fin n)) :=
    ⟨νm.restrict O, isFiniteMeasure_restrict.mpr hνO_lt_top.ne⟩
  have hopen : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G →
      (νO : Measure (EuclideanSpace ℝ (Fin n))) G ≤
        atTop.liminf
          (fun k ↦ (μO k : Measure (EuclideanSpace ℝ (Fin n))) G) := by
    intro G hG
    have hGO_open : IsOpen (G ∩ O) := hG.inter hO_open
    have hμGO_eq (k : ℕ) : μm k (G ∩ O) = μ k (G ∩ O) :=
      toMeasure_apply (μ k) (hμ k).measurable_le_caratheodory hGO_open.measurableSet
    have hνGO_eq : νm (G ∩ O) = ν (G ∩ O) :=
      toMeasure_apply ν hν.measurable_le_caratheodory hGO_open.measurableSet
    change νm.restrict O G ≤ atTop.liminf (fun k ↦ (μm k).restrict O G)
    simp_rw [Measure.restrict_apply hG.measurableSet]
    rw [hνGO_eq]
    simpa only [hμGO_eq] using h.2 (G ∩ O) hGO_open
  have hO_tendsto :
      Tendsto (fun k ↦ μ k O) atTop (𝓝 (ν O)) :=
    compactOpenBounds_imp_boundedContinuitySets μ ν hμ hν h O hO_bounded hO_meas
      hO_frontier
  have hmass : Tendsto (fun k ↦ (μO k).mass) atTop (𝓝 νO.mass) := by
    apply ENNReal.tendsto_coe.mp
    simpa only [FiniteMeasure.ennreal_mass, μO, νO, FiniteMeasure.toMeasure_mk,
      Measure.restrict_apply_univ, hμO_eq, hνO_eq] using hO_tendsto
  have hfinite : Tendsto μO atTop (𝓝 νO) :=
    finiteMeasure_tendsto_of_open_liminf_of_mass_tendsto μO νO hopen hmass
  have hintegral :=
    FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hfinite
      f.toBoundedContinuousFunction
  have hf_zero : ∀ x, x ∉ O → f x = 0 :=
    fun x hx ↦ image_eq_zero_of_notMem_tsupport fun hxf ↦ hx (hfO hxf)
  have hrestrict (m : Measure (EuclideanSpace ℝ (Fin n))) :
      ∫ x, f.toBoundedContinuousFunction x ∂m.restrict O =
        ∫ x, f.toBoundedContinuousFunction x ∂m :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hf_zero
  simpa only [μO, νO, FiniteMeasure.toMeasure_mk, hrestrict, μm, νm, associatedMeasure]
    using hintegral

/-- Evans--Gariepy, Revised Edition, Theorem 1.40, equivalence of conditions (i) and (ii)
for Radon outer measures on Euclidean space. -/
theorem OuterMeasure.weaklyConverges_iff_compactOpenBounds
    {n : ℕ} (μ : ℕ → OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (ν : OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : ∀ k, RadonOuterMeasure (μ k)) (hν : RadonOuterMeasure ν) :
    OuterMeasure.WeaklyConverges μ ν hμ hν ↔
      OuterMeasure.WeaklyConvergesByCompactOpenBounds μ ν :=
  ⟨weaklyConverges_imp_compactOpenBounds μ ν hμ hν,
    compactOpenBounds_imp_weaklyConverges μ ν hμ hν⟩

/-- Evans--Gariepy, Revised Edition, Theorem 1.40, equivalence of conditions (ii) and (iii)
for Radon outer measures on Euclidean space. -/
theorem OuterMeasure.weaklyConvergesByCompactOpenBounds_iff_boundedContinuitySets
    {n : ℕ} (μ : ℕ → OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (ν : OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : ∀ k, RadonOuterMeasure (μ k)) (hν : RadonOuterMeasure ν) :
    OuterMeasure.WeaklyConvergesByCompactOpenBounds μ ν ↔
      OuterMeasure.WeaklyConvergesOnBoundedContinuitySets μ ν :=
  ⟨compactOpenBounds_imp_boundedContinuitySets μ ν hμ hν,
    boundedContinuitySets_imp_compactOpenBounds μ ν hν⟩

/-- Evans--Gariepy, Revised Edition, Theorem 1.40, equivalence of conditions (i) and (iii)
for Radon outer measures on Euclidean space. -/
theorem OuterMeasure.weaklyConverges_iff_boundedContinuitySets
    {n : ℕ} (μ : ℕ → OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (ν : OuterMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : ∀ k, RadonOuterMeasure (μ k)) (hν : RadonOuterMeasure ν) :
    OuterMeasure.WeaklyConverges μ ν hμ hν ↔
      OuterMeasure.WeaklyConvergesOnBoundedContinuitySets μ ν := by
  constructor
  · exact compactOpenBounds_imp_boundedContinuitySets μ ν hμ hν ∘
      weaklyConverges_imp_compactOpenBounds μ ν hμ hν
  · exact compactOpenBounds_imp_weaklyConverges μ ν hμ hν ∘
      boundedContinuitySets_imp_compactOpenBounds μ ν hν

end MeasureTheory

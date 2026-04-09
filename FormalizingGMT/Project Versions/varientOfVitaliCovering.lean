import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Bases
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic

open Set Metric
open scoped Topology

section VariantVitali

variable {α ι : Type*} [PseudoMetricSpace α]


-- Please break this up into lemmas and clean up the proofs. Lemmas should be reusable and general

/-
source
theorem Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall {α : Type u_1}  {ι : Type u_2}  [PseudoMetricSpace α]  (t : Set ι) (x : ι → α)  (r : ι → ℝ)  (R : ℝ)  (hr : ∀ a ∈ t, r a ≤ R)  (τ : ℝ) (hτ : 3 < τ) :
∃ u ⊆ t,
  (u.PairwiseDisjoint fun (a : ι) => Metric.closedBall (x a) (r a)) ∧     ∀ a ∈ t, ∃ b ∈ u, Metric.closedBall (x a) (r a) ⊆ Metric.closedBall (x b) (τ * r b)
-/


--This should be an assumption using the convention in source 'theorem Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall'
/-- `A` is covered by the closed balls indexed by `t`. -/
def CoversByClosedBalls (A : Set α) (t : Set ι) (c : ι → α) (r : ι → ℝ) : Prop :=
  A ⊆ ⋃ a ∈ t, Metric.closedBall (c a) (r a)

--Maybe keep this definition
/-- Fine-at-each-point hypothesis written in the same shape as the `hf` assumption used in
Mathlib's Vitali covering theorems. -/
def FineOnByClosedBalls (A : Set α) (t : Set ι) (c : ι → α) (r : ι → ℝ) : Prop :=
  ∀ x ∈ A, ∀ ε > (0 : ℝ), ∃ a ∈ t, c a = x ∧ r a ≤ ε

theorem variant_vitali_closedBall
  {X : Set α} [SecondCountableTopology α]
    (t : Set ι) (c : ι → α) (r : ι → ℝ)
    (_hcover : CoversByClosedBalls X t c r)
    (hfine : FineOnByClosedBalls X t c r)
    (_hdiam : ∃ D, ∀ a ∈ t, diam (Metric.closedBall (c a) (r a)) ≤ D)
    (hrad : ∃ R, ∀ a ∈ t, r a ≤ R)
    (hpos : ∀ a ∈ t, 0 < r a) :
    ∃ u ⊆ t,
      u.Countable ∧
        u.PairwiseDisjoint (fun a => Metric.closedBall (c a) (r a)) ∧
          ∀ w : Finset ι, (↑w : Set ι) ⊆ t →
            X \ (⋃ a ∈ w, Metric.closedBall (c a) (r a)) ⊆
              ⋃ b ∈ (u \ (w : Set ι)), Metric.closedBall (c b) (5 * r b) := by
  classical
  let B : ι → Set α := fun a => Metric.closedBall (c a) (r a)
  obtain ⟨R, hR⟩ := hrad
  let k : ℝ := 2
  have hk : 1 < k := by
    norm_num [k]
  have hnonneg : ∀ a ∈ t, 0 ≤ r a := fun a ha => le_of_lt (hpos a ha)
  have hne : ∀ a ∈ t, (B a).Nonempty := by
    intro a ha
    refine ⟨c a, ?_⟩
    simpa [B] using (Metric.mem_closedBall_self (x := c a) (hnonneg a ha))
  obtain ⟨u, hut, hdisj, hcovering⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement
      B t r k hk hnonneg R hR hne
  have hu_countable : u.Countable := by
    refine hdisj.countable_of_nonempty_interior ?_
    intro a ha
    have hpa : 0 < r a := hpos a (hut ha)
    refine Set.Nonempty.mono Metric.ball_subset_interior_closedBall ?_
    exact ⟨c a, Metric.mem_ball_self hpa⟩
  refine ⟨u, hut, hu_countable, ?_, ?_⟩
  · simpa [B] using hdisj
  · intro w hw x hx
    rcases hx with ⟨hxX, hx_not_removed⟩
    have hclosed_removed : IsClosed (⋃ a ∈ (w : Set ι), Metric.closedBall (c a) (r a)) :=
      w.finite_toSet.isClosed_biUnion fun _ _ => Metric.isClosed_closedBall
    have hx_compl : x ∈ (⋃ a ∈ (w : Set ι), Metric.closedBall (c a) (r a))ᶜ := by
      simpa [Set.mem_compl] using hx_not_removed
    have hnhds : (⋃ a ∈ (w : Set ι), Metric.closedBall (c a) (r a))ᶜ ∈ 𝓝 x :=
      hclosed_removed.isOpen_compl.mem_nhds hx_compl
    rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hεpos, hεsubset⟩
    rcases hfine x hxX (ε / 2) (half_pos hεpos) with ⟨a, hat, hca, hra⟩
    have hax : x ∈ B a := by
      have hpa : 0 < r a := hpos a hat
      have hca_mem : c a ∈ B a := by
        simpa [B] using (Metric.mem_closedBall_self (x := c a) (le_of_lt hpa))
      simpa [hca] using hca_mem
    have hBa_disjoint_removed : B a ⊆
        (⋃ i ∈ (w : Set ι), Metric.closedBall (c i) (r i))ᶜ := by
      intro y hy
      have hy_closedBall_x : y ∈ Metric.closedBall x (ε / 2) := by
        apply (closedBall_subset_closedBall hra)
        simpa [B, hca] using hy
      have hy_ball_x : y ∈ Metric.ball x ε :=
        (closedBall_subset_ball (half_lt_self hεpos)) hy_closedBall_x
      exact hεsubset hy_ball_x
    rcases hcovering a hat with ⟨b, hbu, hab_nonempty, hab_radius⟩
    have hb_not_w : b ∉ (w : Set ι) := by
      intro hbw
      rcases hab_nonempty with ⟨y, hya, hyb⟩
      have hy_compl : y ∈
          (⋃ i ∈ (w : Set ι), Metric.closedBall (c i) (r i))ᶜ := hBa_disjoint_removed hya
      have hy_union : y ∈ ⋃ i ∈ (w : Set ι), Metric.closedBall (c i) (r i) := by
        refine mem_iUnion.2 ⟨b, mem_iUnion.2 ⟨hbw, hyb⟩⟩
      exact hy_compl hy_union
    have hsubset_hat : B a ⊆ Metric.closedBall (c b) (5 * r b) := by
      intro y hy
      have hcenter_dist : dist (c a) (c b) ≤ r a + r b :=
        dist_le_add_of_nonempty_closedBall_inter_closedBall (by simpa [B] using hab_nonempty)
      have hy_dist : dist y (c a) ≤ r a := by simpa [B] using hy
      have hrb_nonneg : 0 ≤ r b := hnonneg b (hut hbu)
      have hlin : 2 * r a + r b ≤ 5 * r b := by
        have hab' : r a ≤ 2 * r b := by simpa [k] using hab_radius
        linarith [hab', hrb_nonneg]
      calc
        dist y (c b) ≤ dist y (c a) + dist (c a) (c b) := dist_triangle _ _ _
        _ ≤ r a + (r a + r b) := by gcongr
        _ = 2 * r a + r b := by ring
        _ ≤ 5 * r b := hlin
    have hx_hat : x ∈ Metric.closedBall (c b) (5 * r b) := hsubset_hat hax
    refine mem_iUnion.2 ⟨b, mem_iUnion.2 ⟨⟨hbu, hb_not_w⟩, hx_hat⟩⟩






/-- Classical fine cover: for each `x ∈ A`, there exist balls in the family containing `x`
with arbitrarily small diameters. -/
def FineCoverClassical (A : Set α) (t : Set ι) (c : ι → α) (r : ι → ℝ) : Prop :=
  ∀ x ∈ A, ∀ ε > 0, ∃ a ∈ t, x ∈ Metric.closedBall (c a) (r a) ∧
    diam (Metric.closedBall (c a) (r a)) < ε

theorem vitali_variant_classical
    {X : Set α} [SecondCountableTopology α]
    (t : Set ι) (c : ι → α) (r : ι → ℝ)
    (_hcover : CoversByClosedBalls X t c r)
    (hfine : FineCoverClassical X t c r)
    (_hdiam_bound : ∃ D, ∀ a ∈ t, diam (Metric.closedBall (c a) (r a)) ≤ D)
    (hrad : ∃ R, ∀ a ∈ t, r a ≤ R)
    (hpos : ∀ a ∈ t, 0 < r a) :
    ∃ u ⊆ t,
      u.Countable ∧
      u.PairwiseDisjoint (fun a => Metric.closedBall (c a) (r a)) ∧
      ∀ w : Finset ι, (w : Set ι) ⊆ t →
        X \ (⋃ a ∈ w, Metric.closedBall (c a) (r a)) ⊆
          ⋃ b ∈ (u \ (w : Set ι)), Metric.closedBall (c b) (5 * r b) := by
  classical
  let B : ι → Set α := fun a => Metric.closedBall (c a) (r a)
  obtain ⟨R, hR⟩ := hrad
  let k : ℝ := 2
  have hk : 1 < k := by
    norm_num [k]
  have hnonneg : ∀ a ∈ t, 0 ≤ r a := fun a ha => le_of_lt (hpos a ha)
  have hne : ∀ a ∈ t, (B a).Nonempty := by
    intro a ha
    refine ⟨c a, ?_⟩
    simpa [B] using (Metric.mem_closedBall_self (x := c a) (hnonneg a ha))
  obtain ⟨u, hut, hdisj, hcovering⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement
      B t r k hk hnonneg R hR hne
  have hu_countable : u.Countable := by
    refine hdisj.countable_of_nonempty_interior ?_
    intro a ha
    have hpa : 0 < r a := hpos a (hut ha)
    refine Set.Nonempty.mono Metric.ball_subset_interior_closedBall ?_
    exact ⟨c a, Metric.mem_ball_self hpa⟩
  refine ⟨u, hut, hu_countable, ?_, ?_⟩
  · simpa [B] using hdisj
  · intro w hw x hx
    rcases hx with ⟨hxX, hx_not_removed⟩
    have hclosed_removed : IsClosed (⋃ a ∈ (w : Set ι), Metric.closedBall (c a) (r a)) :=
      w.finite_toSet.isClosed_biUnion fun _ _ => Metric.isClosed_closedBall
    have hx_compl : x ∈ (⋃ a ∈ (w : Set ι), Metric.closedBall (c a) (r a))ᶜ := by
      simpa [Set.mem_compl] using hx_not_removed
    have hnhds : (⋃ a ∈ (w : Set ι), Metric.closedBall (c a) (r a))ᶜ ∈ 𝓝 x :=
      hclosed_removed.isOpen_compl.mem_nhds hx_compl
    rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hεpos, hεsubset⟩
    rcases hfine x hxX ε hεpos with ⟨a, hat, hxa, hdiam_lt⟩
    have hBa_disjoint_removed : B a ⊆
        (⋃ i ∈ (w : Set ι), Metric.closedBall (c i) (r i))ᶜ := by
      intro y hy
      have hbounded_Ba : Bornology.IsBounded (B a) := by
        simpa [B] using
          (isBounded_closedBall : Bornology.IsBounded (Metric.closedBall (c a) (r a)))
      have hdist : dist y x ≤ diam (B a) := by
        have hy' : y ∈ B a := hy
        exact dist_le_diam_of_mem hbounded_Ba hy' hxa
      have hy_ball_x : y ∈ Metric.ball x ε := by
        exact lt_of_le_of_lt hdist hdiam_lt
      exact hεsubset hy_ball_x
    rcases hcovering a hat with ⟨b, hbu, hab_nonempty, hab_radius⟩
    have hb_not_w : b ∉ (w : Set ι) := by
      intro hbw
      rcases hab_nonempty with ⟨y, hya, hyb⟩
      have hy_compl : y ∈
          (⋃ i ∈ (w : Set ι), Metric.closedBall (c i) (r i))ᶜ := hBa_disjoint_removed hya
      have hy_union : y ∈ ⋃ i ∈ (w : Set ι), Metric.closedBall (c i) (r i) := by
        refine mem_iUnion.2 ⟨b, mem_iUnion.2 ⟨hbw, hyb⟩⟩
      exact hy_compl hy_union
    have hsubset_hat : B a ⊆ Metric.closedBall (c b) (5 * r b) := by
      intro y hy
      have hcenter_dist : dist (c a) (c b) ≤ r a + r b :=
        dist_le_add_of_nonempty_closedBall_inter_closedBall (by simpa [B] using hab_nonempty)
      have hy_dist : dist y (c a) ≤ r a := by simpa [B] using hy
      have hrb_nonneg : 0 ≤ r b := hnonneg b (hut hbu)
      have hlin : 2 * r a + r b ≤ 5 * r b := by
        have hab' : r a ≤ 2 * r b := by simpa [k] using hab_radius
        linarith [hab', hrb_nonneg]
      calc
        dist y (c b) ≤ dist y (c a) + dist (c a) (c b) := dist_triangle _ _ _
        _ ≤ r a + (r a + r b) := by gcongr
        _ = 2 * r a + r b := by ring
        _ ≤ 5 * r b := hlin
    have hx_hat : x ∈ Metric.closedBall (c b) (5 * r b) := hsubset_hat hxa
    refine mem_iUnion.2 ⟨b, mem_iUnion.2 ⟨⟨hbu, hb_not_w⟩, hx_hat⟩⟩


end VariantVitali

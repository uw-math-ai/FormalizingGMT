import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.Tactic

open Set Metric
open scoped Topology

section VariantVitali

variable {α ι : Type*} [PseudoMetricSpace α]

/--
If two closed balls intersect and the first radius is at most twice the second,
then the first ball is contained in the `5`-times enlargement of the second.

This is the geometric core used in the classical Vitali-type enlargement step.
-/
lemma closedBall_subset_closedBall_five_mul
    {ca cb y : α} {ra rb : ℝ}
    (hy : y ∈ Metric.closedBall ca ra)
    (hinter : (Metric.closedBall ca ra ∩ Metric.closedBall cb rb).Nonempty)
  (hra : ra ≤ 2 * rb) :
    y ∈ Metric.closedBall cb (5 * rb) := by
  have hcenter_dist : dist ca cb ≤ ra + rb :=
    dist_le_add_of_nonempty_closedBall_inter_closedBall hinter
  have hy_dist : dist y ca ≤ ra := by
    simpa using hy
  have hlin : 2 * ra + rb ≤ 5 * rb := by
    linarith [hra]
  refine (Metric.mem_closedBall.2 ?_)
  calc
    dist y cb ≤ dist y ca + dist ca cb := dist_triangle _ _ _
    _ ≤ ra + (ra + rb) := by gcongr
    _ = 2 * ra + rb := by ring
    _ ≤ 5 * rb := hlin

lemma closedBall_subset_removed_of_fine
    (w : Finset ι) (c : ι → α) (r : ι → ℝ)
    {x : α} {a : ι} {ε : ℝ}
    (hεpos : 0 < ε)
    (hεsubset : Metric.ball x ε ⊆ (⋃ i ∈ (w : Set ι), Metric.closedBall (c i) (r i))ᶜ)
    (hca : c a = x) (hra : r a ≤ ε / 2) :
    Metric.closedBall (c a) (r a) ⊆
      (⋃ i ∈ (w : Set ι), Metric.closedBall (c i) (r i))ᶜ := by
  intro y hy
  have hy_dist : dist y x ≤ r a := by
    simpa [hca, dist_comm] using hy
  have hlt : dist y x < ε := by
    have hhalf : ε / 2 < ε := by linarith
    exact lt_of_le_of_lt (hy_dist.trans hra) hhalf
  exact hεsubset (Metric.mem_ball.2 hlt)

lemma not_mem_finset_of_inter_nonempty_and_subset_compl
    (w : Finset ι) (c : ι → α) (r : ι → ℝ)
    {a b : ι}
    (hab_nonempty :
      (Metric.closedBall (c a) (r a) ∩ Metric.closedBall (c b) (r b)).Nonempty)
    (hBa_compl : Metric.closedBall (c a) (r a) ⊆
      (⋃ i ∈ (w : Set ι), Metric.closedBall (c i) (r i))ᶜ) :
    b ∉ (w : Set ι) := by
  intro hbw
  rcases hab_nonempty with ⟨y, hya, hyb⟩
  have hy_compl : y ∈ (⋃ i ∈ (w : Set ι), Metric.closedBall (c i) (r i))ᶜ := hBa_compl hya
  have hy_union : y ∈ ⋃ i ∈ (w : Set ι), Metric.closedBall (c i) (r i) := by
    refine mem_iUnion.2 ⟨b, mem_iUnion.2 ⟨hbw, ?_⟩⟩
    exact hyb
  exact hy_compl hy_union

theorem vitali_variant_classical
    {X : Set α} [SecondCountableTopology α]
    (t : Set ι) (c : ι → α) (r : ι → ℝ)
    (hf : ∀ x ∈ X, ∀ ε > (0 : ℝ), ∃ a ∈ t, r a ≤ ε ∧ c a = x)
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
    rcases hf x hxX (ε / 2) (half_pos hεpos) with ⟨a, hat, hra, hca⟩
    have hxa : x ∈ B a := by
      have hna : 0 ≤ r a := hnonneg a hat
      simpa [B, hca] using Metric.mem_closedBall_self (x := x) hna
    have hBa_disjoint_removed : B a ⊆
        (⋃ i ∈ (w : Set ι), Metric.closedBall (c i) (r i))ᶜ := by
      simpa [B] using
        closedBall_subset_removed_of_fine w c r hεpos hεsubset hca hra
    rcases hcovering a hat with ⟨b, hbu, hab_nonempty, hab_radius⟩
    have hb_not_w : b ∉ (w : Set ι) := by
      exact not_mem_finset_of_inter_nonempty_and_subset_compl
        w c r (by simpa [B] using hab_nonempty) (by simpa [B] using hBa_disjoint_removed)
    have hsubset_hat : B a ⊆ Metric.closedBall (c b) (5 * r b) := by
      intro y hy
      have hra : r a ≤ 2 * r b := by simpa [k] using hab_radius
      exact closedBall_subset_closedBall_five_mul
        (by simpa [B] using hy)
        (by simpa [B] using hab_nonempty)
        hra
    have hx_hat : x ∈ Metric.closedBall (c b) (5 * r b) := hsubset_hat hxa
    refine mem_iUnion.2 ⟨b, mem_iUnion.2 ⟨⟨hbu, hb_not_w⟩, hx_hat⟩⟩


end VariantVitali

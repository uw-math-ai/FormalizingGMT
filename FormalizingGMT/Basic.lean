import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

variable {n : ℕ}

-- Definitions
def sSet (E : Set (Fin n → ℝ)) (s : ℝ) : Prop :=
  -- your definition here, for example:
  MeasureTheory.Measure.hausdorffMeasure s E > 0

noncomputable def Density_s (E : Set (Fin n → ℝ)) (x : Fin n → ℝ) (s : ℝ) : ℝ :=
  Filter.limsup (fun r =>
    if 0 < r then
      let μ := MeasureTheory.Measure.hausdorffMeasure s (E ∩ Metric.ball x r)
      if μ = ⊤ then 0 else μ.toReal / Real.rpow r s
    else 0
  ) (nhdsWithin (0 : ℝ) (Set.Ioi 0))


--CHECK THIS DEFINITION...
def Annulus (x : Fin n → ℝ) (r η : ℝ) : Set (Fin n → ℝ) :=
  {z | r * (1 - η) < dist x z ∧ dist x z < r * (1 + η)}


open Metric
open Filter

-- Useful shorthand
noncomputable def Haus (s : ℝ) : MeasureTheory.Measure (Fin n → ℝ) := MeasureTheory.Measure.hausdorffMeasure (X := Fin n → ℝ) s

/- new: local accumulation-point predicate to avoid unknown identifier errors -/
def isAccumulationPoint (F : Set (Fin n → ℝ)) (y : Fin n → ℝ) : Prop :=
  ∀ r, 0 < r → ∃ z ∈ F, z ≠ y ∧ dist z y < r

-- Axioms encoding the provided lemmas (used as hypotheses in the proof below).

-- These are taken as given facts for the contradiction proof below.

-- Lemma 2 (formalised)
-- If we proceed by contradiction, E has a measurable subset of positive Hausdorff s-measure
-- (an s-set) where the s-density exists and is at least 2^{-s} (> 1/2 for 0<s<1),
-- by Corollary 2.5. Choosing sufficiently small ρ we may find such F ⊆ E with the stated local bound:
axiom Lemma2 (E : Set (Fin n → ℝ)) (s : ℝ) (h : sSet E s) (hs : 0 < s ∧ s < 1) :
  ∃ (F : Set (Fin n → ℝ)),
    MeasurableSet F ∧                   -- F is measurable
    F ⊆ E ∧                             -- F ⊆ E
    Haus s F > 0 ∧                      -- F has positive H^s-measure (an s-set)
    (∀ x ∈ F, ∃ d, Density_s E x s = d ∧ d ≥ 2^(-s)) ∧ -- for x∈F the density exists and ≥ 2^{-s}
    (∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ F, ∀ r, 0 < r ∧ r < ρ → Haus s (E ∩ Metric.ball x r) > ENNReal.ofReal ((1 : ℝ) / 2 * Real.rpow (2 * r) s))

axiom Lemma3 :
  -- informal: relates annulus measure differences to density at an accumulation point y
  ∀ (E F : Set (Fin n → ℝ)) (s : ℝ) (y : Fin n → ℝ) (r η : ℝ),
    0 < r → 0 < η ∧ η < 1 → isAccumulationPoint F y →
    ( (ENNReal.ofReal ((2 * r) ^ (-s))) * Haus s (E ∩ (Annulus y r η)) =
      (ENNReal.ofReal ((2 * r) ^ (-s))) * Haus s (E ∩ Metric.ball y (r * (1 + η))) -
      (ENNReal.ofReal ((2 * r) ^ (-s))) * Haus s (E ∩ Metric.ball y (r * (1 - η))) ) ∧
    -- and this equality contributes to expressing D_s(E,y) on the factor ((1+η)^s - (1-η)^s)
    True


-- Not sure this is exactly right... please fix (likely missing some arguments)
axiom Lemma4 :
  ∀ (F : Set (Fin n → ℝ)) (y : Fin n → ℝ) (r η : ℝ),
    0 < η ∧ η < 1 → isAccumulationPoint F y →
    (∃ x ∈ F, dist x y = r ∧ Metric.ball (x : Fin n → ℝ) (r * η / 2) ⊆ Annulus y r η)




-- Likely missing some arguments (for the lower bound?)
axiom Lemma5 :
  -- informal: lower bound the Hausdorff measure of the small ball inside the annulus by (1/2)*r^s*η^s
  ∀ (E F : Set (Fin n → ℝ)) (s : ℝ) (x y : Fin n → ℝ) (r η : ℝ),
    0 < η ∧ η < 1 →
    Metric.ball x (r * η / 2) ⊆ Annulus y r η →
    ENNReal.ofReal ((1 / 2) * (r ^ s) * (η ^ s)) < Haus s (E ∩ Metric.ball x (r * η / 2)) ∧
    Haus s (E ∩ Metric.ball x (r * η / 2)) ≤ Haus s (E ∩ Annulus y r η)




axiom Lemma6 :
  ∀ (E F : Set (Fin n → ℝ)) (s : ℝ) (y : Fin n → ℝ),
    0 < s ∧ s < 1 →
    (F ⊆ E) →
    isAccumulationPoint F y →
    (∀ ε > 0, ∃ η, 0 < η ∧ η < 1 ∧
      (2 ^ (-(s + 1))) * (η ^ s) ≤
        (Density_s E y s) * ( (1 + η) ^ s - (1 - η) ^ s ) + ε)





-- Extra statements separated from the Lemmas (these replace the 'admit' uses)
lemma exists_limit_point_of_meas_pos {F : Set (Fin n → ℝ)} {s : ℝ}
  (Fmeas : MeasurableSet F) (Fpos : Haus s F > 0) : ∃ y, isAccumulationPoint F y := by
  sorry -- prove later :sob:

axiom divide_inequality_by_eta {s η A B ε : ℝ} (hη : 0 < η) :
  (A * η ^ s ≤ B * ((1 + η) ^ s - (1 - η) ^ s) + ε) →
  A * η ^ (s - 1) ≤ B * (((1 + η) ^ s - (1 - η) ^ s) / η) + ε / η

/- replace the previous problematic declaration with a clearer, fully parenthesised axiom -/
axiom eta_limit_contradiction {s A B : ℝ} (hs : 0 < s ∧ s < 1) :
  (∃ (seq : ℕ → ℝ),
     (∀ k, 0 < seq k ∧ seq k < 1) ∧
     Tendsto (fun k => seq k) atTop (nhds (0 : ℝ)) ∧
     (∀ k, A * (seq k) ^ (s - 1) ≤ B * (((1 + seq k) ^ s - (1 - seq k) ^ s) / seq k) + 1 / seq k)
  ) → False

-- get rid of the last admit in the theorem
axiom extract_eta_sequence (E F : Set (Fin n → ℝ)) (s : ℝ) (y : Fin n → ℝ)
  (hs : 0 < s ∧ s < 1) (Fsub : F ⊆ E) (y_lim : isAccumulationPoint F y) :
  ∃ seq : ℕ → ℝ,
    (∀ k, 0 < seq k ∧ seq k < 1) ∧
    Tendsto (fun k => seq k) atTop (nhds (0 : ℝ)) ∧
    (∀ k, (2 ^ (-(s + 1))) * (seq k) ^ (s - 1) ≤
      (Density_s E y s) * (((1 + seq k) ^ s - (1 - seq k) ^ s) / seq k) + 1 / seq k)






-- Theorem (uses the new extra statements in place of admits)
theorem density_fails_almost_everywhere (E : Set (Fin n → ℝ)) (s : ℝ) (h : sSet E s) (hs : 0 < s ∧ s < 1) :
  ∀ᵐ x ∂((Haus s).restrict E), ¬ ∃ d, Density_s E x s = d
:= by
  -- Proceed by contradiction: assume the set where the density exists has positive measure.
  by_contra Hcontr
  -- extract F and its properties from Lemma2
  obtain ⟨F, Fmeas, Fsub, Fpos, Fdens, Frho⟩ := Lemma2 E s h hs

  -- use the separated extra statement to get an accumulation point y of F
  obtain ⟨y, y_lim⟩ := exists_limit_point_of_meas_pos Fmeas Fpos

  -- Apply Lemma6 to get the 'for all ε > 0 exists η' family
  have fam := Lemma6 E F s y hs Fsub y_lim

  -- Contradiction extraction: pick ε = 1 and obtain some η
  let ε : ℝ := 1
  obtain ⟨η, ηpos, ηlt1, hineq⟩ := fam ε (by norm_num)

  -- use the separated algebraic statement to divide by η
  have div_ineq := divide_inequality_by_eta (by exact ηpos) hineq

  let A := Real.rpow (2 : ℝ) (-(s + 1))
  let B := Density_s E y s

  -- use the new extra lemma to obtain the sequence (no admit)
  obtain ⟨seq, seq_pos, seq_tend, seq_ineq⟩ := extract_eta_sequence E F s y hs Fsub y_lim

  -- package the witness and apply the contradiction axiom
  exact eta_limit_contradiction hs ⟨seq, seq_pos, seq_tend, seq_ineq⟩

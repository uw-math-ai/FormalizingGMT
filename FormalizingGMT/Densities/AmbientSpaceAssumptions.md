# Assumptions on the ambient space `X` in the main density theorems

This report covers the four main theorems in

* `FormalizingGMT/Densities/HausdorffUpperDensityInside.lean` (Theorem 2.7, at points of `E`), and
* `FormalizingGMT/Densities/HausdorffUpperDensityOutside.lean` (Theorem 2.6, at points outside `E`).

For each theorem it lists:

* the type-class assumptions on `X` that appear in the Lean statement;
* the hypotheses on `s` and `E`, for context;
* which assumptions the current proof actually needs, and which follow from the others.

"Checked" means the claim was confirmed by compiling a scratch copy of the theorem in this project
(Lean 4.34.1, the pinned Mathlib).

## Background on the type classes

| Type class | Meaning |
| --- | --- |
| `MetricSpace X` | `X` is a metric space. This gives closed balls `Metric.closedBall x r` and the Hausdorff measure. A metric space is automatically Hausdorff (`T2Space`). |
| `MeasurableSpace X`, `BorelSpace X` | `X` has a σ-algebra, and it is the Borel σ-algebra. Mathlib's `μH[s]` (`MeasureTheory.Measure.hausdorffMeasure`) needs both. |
| `SigmaCompactSpace X` | `X` is a countable union of compact sets. |
| `LocallyCompactSpace X` | Every point has a basis of compact neighbourhoods. |
| `SecondCountableTopology X` | The topology has a countable base. For a metric space this is the same as being separable. |

A Mathlib instance makes every locally compact, second countable space σ-compact. So
`[LocallyCompactSpace X] [SecondCountableTopology X]` already gives `[SigmaCompactSpace X]`.

*Update:* following this report, σ-compactness and the measurability hypothesis on `E` were removed
from both Part I theorems, and σ-compactness was removed from Theorem 2.6 (and from the variables of
its lemma file). The sections below describe the current statements.

The Carathéodory measurability hypothesis on `E`, where it is assumed (Part II and Theorem 2.6), is:
`MeasurableSet[(OuterMeasure.mkMetric (fun r => r ^ s)).caratheodory] E`. It says that `E` is
measurable for the `s`-dimensional Hausdorff outer measure. In Lean's display this appears simply
as `MeasurableSet E`.

---

## 1. `hausdorffContentInfty_upperDensity_ge_ae_mem` (Theorem 2.7, Part I, file `HausdorffUpperDensityInside.lean`)

**Statement.** For `H^s`-almost every `x ∈ E`, the upper `s`-density at `x` of `H^s_∞`
restricted to `E` is at least `1 / 2^s`.

**Assumptions on `X` in the statement:**

* `[MetricSpace X]`
* `[MeasurableSpace X] [BorelSpace X]`

**Other hypotheses:** `0 ≤ s`; `μH[s] E ≠ ⊤`. `E` is an arbitrary set.

**What the proof actually uses:**

* `MetricSpace X`, `MeasurableSpace X` and `BorelSpace X` are needed. Closed balls require the
  metric, and `μH[s]` requires the Borel measurable structure.
* `SigmaCompactSpace X` and Carathéodory measurability of `E` were assumed in an earlier version
  but never used; both have been removed from the statement.

## 2. `hausdorffMeasure_upperDensity_ge_ae_mem` (Corollary of Theorem 2.7, Part I, file `HausdorffUpperDensityInside.lean`)

**Statement.** For `H^s`-almost every `x ∈ E`, the upper `s`-density at `x` of `H^s` restricted to
`E` is at least `1 / 2^s`.

**Assumptions on `X` in the statement:**

* `[MetricSpace X]`
* `[MeasurableSpace X] [BorelSpace X]`

**Other hypotheses:** the same as in Theorem 1.

**What the proof actually uses:** the same as Theorem 1. σ-compactness and measurability of `E`
have been removed from this statement as well.

## 3. `hausdorffMeasure_upperDensity_le_one_ae_mem` (Theorem 2.7, Part II, file `HausdorffUpperDensityInside.lean`)

**Statement.** For `H^s`-almost every `x ∈ E`, the upper `s`-density at `x` of `H^s` restricted to
`E` is at most `1`.

**Assumptions on `X` in the statement:**

* `[MetricSpace X]`
* `[LocallyCompactSpace X]`
* `[SecondCountableTopology X]`
* `[MeasurableSpace X] [BorelSpace X]`

**Other hypotheses:** `0 ≤ s`; `E` is Carathéodory measurable for the `s`-dimensional Hausdorff outer
measure; `μH[s] E ≠ ⊤`.

**What the proof actually uses:**

* Local compactness and second countability are what make the restricted measure `H^s ⌞ E`
  regular. This goes through `HausdorffRestrict.toRadonOuterMeasure`, which needs
  `[LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]`; `T2Space` comes for free from
  `MetricSpace`. Regularity gives the open set `U ⊇ B_t` with `H^s(U ∩ E) < H^s(B_t) + ε`.
* The Vitali-type covering step (`vitali_variant_classical`) and the fine-cover lemma only need the
  metric structure.
* σ-compactness is not among the assumptions, but it follows from local compactness together with
  second countability.

## 4. `hausdorffMeasure_upperDensity_eq_zero_ae_notMem` (Theorem 2.6, file `HausdorffUpperDensityOutside.lean`)

**Statement.** For `H^s`-almost every `x ∉ E`, the upper `s`-density at `x` of the `s`-dimensional
Hausdorff outer measure restricted to `E` is `0`.

**Assumptions on `X` in the statement** (file-level `variable`):

* `[MetricSpace X]`
* `[LocallyCompactSpace X]`
* `[SecondCountableTopology X]`
* `[MeasurableSpace X] [BorelSpace X]`

**Other hypotheses:** `0 ≤ s`; `E` is Carathéodory measurable for `Hs_outer s`, which is the outer
measure `OuterMeasure.mkMetric (fun r => r ^ s)`, i.e. the `s`-dimensional Hausdorff outer measure;
`Hs_outer s E < ⊤`. The density is taken for `Hs_restrict s E`, the restriction of `Hs_outer s` to
`E`.

**What the proof actually uses:**

* `[SigmaCompactSpace X]` was assumed in an earlier version but is redundant, since it follows from
  `[LocallyCompactSpace X]` and `[SecondCountableTopology X]`. It has been removed from the theorem
  and from the lemma file; where a lemma needs σ-compactness, Lean derives it automatically. The
  docstring now describes `X` as a locally compact, second countable metric space.
* The local compactness and second countability assumptions are passed to the technical lemmas
  `approx_by_closed_inside`, `vitali_cover_at_scale` and `A_t_null`. There they are used to
  approximate `E` from inside by a closed set `K`, which needs regularity of the restricted
  Hausdorff measure, and to run the Vitali covering argument.

---

## Summary table

| Theorem | `MetricSpace` | `MeasurableSpace` + `BorelSpace` | `SigmaCompactSpace` | `LocallyCompactSpace` | `SecondCountableTopology` |
| --- | --- | --- | --- | --- | --- |
| `hausdorffContentInfty_upperDensity_ge_ae_mem` | assumed, used | assumed, used | – (removed) | – | – |
| `hausdorffMeasure_upperDensity_ge_ae_mem` | assumed, used | assumed, used | – (removed) | – | – |
| `hausdorffMeasure_upperDensity_le_one_ae_mem` | assumed, used | assumed, used | – (follows from the next two) | assumed, used | assumed, used |
| `hausdorffMeasure_upperDensity_eq_zero_ae_notMem` | assumed, used | assumed, used | – (removed; follows from the next two) | assumed, used | assumed, used |

Notes:

* "Used" means the current proof relies on this assumption, directly or through lemmas whose
  statements require it. Whether a different proof could do without it was not investigated.
* All four theorems use **closed** balls in the densities.
* The finiteness hypotheses look different but say the same thing. Theorem 2.7 writes
  `μH[s] E ≠ ⊤`; Theorem 2.6 writes `Hs_outer s E < ⊤`. Both are the `s`-dimensional Hausdorff
  outer measure of `E`.
* `0 ≤ s` is assumed in all four theorems.

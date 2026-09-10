import Mathlib.Analysis.InnerProductSpace.PiL2

open Topology

/--
The blow-up map `T_{a,r}(x) = (x - a) / r` on Euclidean space `ℝⁿ`.
-/
def blowUpMap {n : ℕ}
    (a : EuclideanSpace ℝ (Fin n))
    (r : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  r⁻¹ • (x - a)
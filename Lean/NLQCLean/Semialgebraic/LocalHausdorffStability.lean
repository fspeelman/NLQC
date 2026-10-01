/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.LocalSignStability
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Identification of locally stable membership under Hausdorff convergence

The argument uses both directions of the extended Hausdorff
distance. It is valid for empty sets and uses no real-valued empty-distance
convention. The final lemma applies it to normalized polynomial templates.
-/

section

open Filter MeasureTheory Metric
open scoped Topology

namespace NLQCLean

/-- A stable local truth value agrees with membership in a closed Hausdorff
limit. Inclusion uses distance to the limit; exclusion uses the reverse
Hausdorff inclusion to produce nearby approximating points. -/
theorem mem_iff_of_hausdorff_local_stability {E : Type*} [MetricSpace E]
    {S : ℕ → Set E} {Slimit : Set E} (hclosed : IsClosed Slimit)
    (hlim : Tendsto (fun k => hausdorffEDist (S k) Slimit) atTop (𝓝 0))
    (x : E) (P : Prop) (hlocal : ∃ V ∈ 𝓝 x, ∀ᶠ k in atTop, ∀ y ∈ V, (y ∈ S k ↔ P)) :
    P ↔ x ∈ Slimit := by
  obtain ⟨V, hV, hlocal⟩ := hlocal
  constructor
  · intro hP
    have hevent : ∀ᶠ k in atTop, x ∈ S k :=
      hlocal.mono (fun _ hk => (hk x (mem_of_mem_nhds hV)).mpr hP)
    have hle : infEDist x Slimit ≤ 0 :=
      ge_of_tendsto hlim (hevent.mono (fun _ hk => infEDist_le_hausdorffEDist_of_mem hk))
    exact (mem_iff_infEDist_zero_of_closed hclosed).mpr (le_antisymm hle bot_le)
  · intro hx
    by_contra hP
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
    have hnear : ∀ᶠ k in atTop, hausdorffEDist (S k) Slimit < ENNReal.ofReal ε :=
      hlim.eventually (eventually_lt_nhds (ENNReal.ofReal_pos.mpr hε))
    obtain ⟨k, hk, hnear⟩ := (hlocal.and hnear).exists
    have hreverse : hausdorffEDist Slimit (S k) < ENNReal.ofReal ε := by
      rwa [hausdorffEDist_comm]
    obtain ⟨y, hy, hxy⟩ := exists_edist_lt_of_hausdorffEDist_lt hx hreverse
    apply hP
    apply (hk y (hball ?_)).mp hy
    simpa only [Metric.mem_ball, dist_comm] using edist_lt_ofReal.mp hxy

/-- Almost-everywhere eventual membership agreement with the closed Hausdorff
limit, for convergent normalized coefficient descriptions. -/
theorem PolynomialFormatTemplate.ae_eventually_mem_iff_of_hausdorff {n D r b : ℕ}
    (T : PolynomialFormatTemplate r b) {a : ℕ → PolynomialFormatCoefficients n D r b}
    {aLimit : PolynomialFormatCoefficients n D r b} {Slimit : Set (RealEuclidean n)}
    (ha : ∀ k, NormalizedFormatCoefficients (a k)) (hlim : Tendsto a atTop (𝓝 aLimit))
    (hclosed : IsClosed Slimit)
    (hhaus : Tendsto (fun k => hausdorffEDist (T.source (a k)) Slimit) atTop (𝓝 0)) :
    ∀ᵐ x : RealEuclidean n, ∀ᶠ k in atTop, (x ∈ T.source (a k) ↔ x ∈ Slimit) := by
  filter_upwards [T.ae_local_source_stability ha hlim] with x hx
  have hid := mem_iff_of_hausdorff_local_stability hclosed hhaus x (x ∈ T.source aLimit) hx
  obtain ⟨V, hV, hevent⟩ := hx
  exact hevent.mono (fun _ hk => (hk x (mem_of_mem_nhds hV)).trans hid)

end NLQCLean
end

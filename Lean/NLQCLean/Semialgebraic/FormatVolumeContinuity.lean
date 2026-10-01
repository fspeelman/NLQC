/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Semialgebraic.LocalHausdorffStability
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Bounded-format Hausdorff volume continuity

A fixed finite polynomial format prevents the fine-grid obstruction
to volume convergence. The limit need not be given by polynomials. The proof
uses compact coefficient subsequences, polynomial zero-set nullity, local
membership stability, both Hausdorff inclusions and dominated convergence.
No external semialgebraic theorem is an argument.
-/

section

open Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace NLQCLean

/-- Dominated convergence for eventually agreeing measurable-set indicators. -/
theorem tendsto_measure_of_ae_eventually_mem_iff {E : Type*} [MeasurableSpace E]
    (μ : Measure E) {S : ℕ → Set E} {Slimit B : Set E}
    (hS : ∀ k, MeasurableSet (S k)) (hlimit : MeasurableSet Slimit)
    (hB : MeasurableSet B) (hfinite : μ B ≠ ∞) (hsub : ∀ k, S k ⊆ B)
    (hmem : ∀ᵐ x ∂μ, ∀ᶠ k in atTop, (x ∈ S k ↔ x ∈ Slimit)) :
    Tendsto (fun k => μ (S k)) atTop (𝓝 (μ Slimit)) := by
  classical
  have hind : ∀ᵐ x ∂μ, Tendsto (fun k => (S k).indicator (fun _ => (1 : ℝ≥0∞)) x)
      atTop (𝓝 (Slimit.indicator (fun _ => (1 : ℝ≥0∞)) x)) := by
    filter_upwards [hmem] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hx] with k hk
    simp only [Set.indicator, hk]
  have hdom (k : ℕ) : (S k).indicator (fun _ => (1 : ℝ≥0∞)) ≤ᵐ[μ]
      B.indicator (fun _ => (1 : ℝ≥0∞)) := by
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ S k
    · simp [hx, hsub k hx]
    · simp [hx]
  have hfin : ∫⁻ x, B.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ ≠ ∞ := by
    simpa [lintegral_indicator hB] using hfinite
  have h := tendsto_lintegral_of_dominated_convergence
    (B.indicator (fun _ => (1 : ℝ≥0∞)))
    (fun k => measurable_const.indicator (hS k)) hdom hfin hind
  simpa [lintegral_indicator, hS, hlimit] using h

/-- Uniform polynomial format plus Hausdorff convergence implies volume
convergence in a common finite ball. Only the approximating sets require a
polynomial representation; the limit need only be closed. Empty sets and
dimension zero are included by the extended Hausdorff convention. -/
theorem tendsto_volume_of_bounded_format_hausdorff {n c D : ℕ}
    (S : ℕ → Set (RealEuclidean n)) (Slimit : Set (RealEuclidean n))
    (hcompact : ∀ k, IsCompact (S k)) (hclosed : IsClosed Slimit)
    (hformat : ∀ k, HasSemialgebraicFormat (S k) c D)
    (R : ℝ) (hbound : ∀ k, S k ⊆ closedBall 0 R)
    (hhaus : Tendsto (fun k => hausdorffEDist (S k) Slimit) atTop (𝓝 0)) :
    Tendsto (fun k => volume (S k)) atTop (𝓝 (volume Slimit)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro u hu
  obtain ⟨T, a, aLimit, k, hk, ha, hsource, _, hlim⟩ :=
    exists_convergent_format_subsequence (fun j => S (u j)) (fun j => hformat (u j))
  refine ⟨k, ?_⟩
  have hhaus' : Tendsto (fun j => hausdorffEDist (T.source (a j)) Slimit) atTop (𝓝 0) := by
    simpa only [hsource, Function.comp_def] using hhaus.comp (hu.comp hk.tendsto_atTop)
  have hmem : ∀ᵐ x : RealEuclidean n, ∀ᶠ j in atTop, (x ∈ S (u (k j)) ↔ x ∈ Slimit) := by
    simpa only [hsource] using T.ae_eventually_mem_iff_of_hausdorff ha hlim hclosed hhaus'
  exact tendsto_measure_of_ae_eventually_mem_iff volume
    (fun j => (hcompact (u (k j))).measurableSet) hclosed.measurableSet
    isClosed_closedBall.measurableSet (measure_closedBall_lt_top.ne) (fun j => hbound (u (k j))) hmem

/-- Real-valued volume convergence for a compact limit, matching the source's
ordinary finite Lebesgue-volume convention. -/
theorem tendsto_realVolume_of_bounded_format_hausdorff {n c D : ℕ}
    (S : ℕ → Set (RealEuclidean n)) (Slimit : Set (RealEuclidean n))
    (hcompact : ∀ k, IsCompact (S k)) (hlimit : IsCompact Slimit)
    (hformat : ∀ k, HasSemialgebraicFormat (S k) c D)
    (R : ℝ) (hbound : ∀ k, S k ⊆ closedBall 0 R)
    (hhaus : Tendsto (fun k => hausdorffEDist (S k) Slimit) atTop (𝓝 0)) :
    Tendsto (fun k => (volume (S k)).toReal) atTop (𝓝 (volume Slimit).toReal) :=
  (ENNReal.continuousAt_toReal hlimit.measure_lt_top.ne).tendsto.comp
    (tendsto_volume_of_bounded_format_hausdorff S Slimit hcompact hlimit.isClosed hformat R hbound hhaus)

/-- In particular, null sets in a bounded ball approaching a positive-volume
closed set cannot have one uniform polynomial format. Finite increasingly
fine grids in positive dimension are an instance of this obstruction. -/
theorem not_uniform_format_of_null_hausdorff_limit {n : ℕ}
    (S : ℕ → Set (RealEuclidean n)) (Slimit : Set (RealEuclidean n))
    (hcompact : ∀ k, IsCompact (S k)) (hclosed : IsClosed Slimit)
    (hnull : ∀ k, volume (S k) = 0) (hpositive : 0 < volume Slimit)
    (R : ℝ) (hbound : ∀ k, S k ⊆ closedBall 0 R)
    (hhaus : Tendsto (fun k => hausdorffEDist (S k) Slimit) atTop (𝓝 0)) :
    ¬ ∃ c D : ℕ, ∀ k, HasSemialgebraicFormat (S k) c D := by
  rintro ⟨c, D, hformat⟩
  have h := tendsto_volume_of_bounded_format_hausdorff S Slimit hcompact hclosed hformat R hbound hhaus
  have hz : Tendsto (fun k => volume (S k)) atTop (𝓝 0) := by
    simpa only [hnull] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  exact (ne_of_gt hpositive) (tendsto_nhds_unique h hz)

end NLQCLean
end

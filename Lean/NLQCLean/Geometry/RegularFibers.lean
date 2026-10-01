/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Bases

/-!
# Regular fibers of equal-dimensional maps are countable

In a second-countable space, a set whose points
are each isolated by a neighborhood is countable. At a point with a strict
derivative of nonzero determinant, the inverse function theorem gives an open
source on which the map is injective, so such points are isolated in their
fiber. No external premise, openness of the domain or global inverse is used.
Discreteness alone does not give finiteness.
-/

section

open Set Filter
open scoped Topology

namespace NLQCLean

theorem Set.countable_of_forall_exists_nhds_inter_subset_singleton {α : Type*}
    [TopologicalSpace α] [SecondCountableTopology α] {T : Set α}
    (h : ∀ x ∈ T, ∃ U ∈ 𝓝 x, U ∩ T ⊆ {x}) : T.Countable := by
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis α
  choose! U hU hUT using h
  have hV : ∀ x ∈ T, ∃ v ∈ b, x ∈ v ∧ v ⊆ U x := fun x hx => by
    obtain ⟨v, hvb, hxv, hvU⟩ :=
      hb.exists_subset_of_mem_open (mem_interior_iff_mem_nhds.mpr (hU x hx)) isOpen_interior
    exact ⟨v, hvb, hxv, hvU.trans interior_subset⟩
  choose! V hVb hxV hVU using hV
  refine MapsTo.countable_of_injOn (f := V) (fun x hx => hVb x hx) ?_ hbc
  intro x hx z hz hxz
  have hzV : z ∈ V x := by
    rw [hxz]
    exact hxV z hz
  exact (Set.mem_singleton_iff.mp (hUT x hx ⟨hVU x hx hzV, hz⟩)).symm

/-- Regular-fiber countability: if every point of `s` in the fiber over `y` has a
strict derivative with nonzero determinant, that part of the fiber is countable. -/
theorem countable_inter_preimage_singleton_of_det_ne_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → E} {f' : E → E →L[ℝ] E} {s : Set E} {y : E}
    (hf : ∀ x ∈ s, f x = y → HasStrictFDerivAt f (f' x) x ∧ (f' x).det ≠ 0) :
    (s ∩ f ⁻¹' {y}).Countable := by
  apply Set.countable_of_forall_exists_nhds_inter_subset_singleton
  rintro x ⟨hxs, hxy⟩
  have hxy' : f x = y := hxy
  obtain ⟨hstrict, hdet⟩ := hf x hxs hxy'
  have hs' : HasStrictFDerivAt f
      ((f' x).toContinuousLinearEquivOfDetNeZero hdet : E →L[ℝ] E) x := by
    rwa [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
  refine ⟨(hs'.toOpenPartialHomeomorph f).source,
    (hs'.toOpenPartialHomeomorph f).open_source.mem_nhds hs'.mem_toOpenPartialHomeomorph_source, ?_⟩
  rintro z ⟨hze, -, hzy⟩
  have hzy' : f z = y := hzy
  exact Set.mem_singleton_iff.mpr ((hs'.toOpenPartialHomeomorph f).injOn hze
    hs'.mem_toOpenPartialHomeomorph_source (by
      change f z = f x
      rw [hzy', hxy']))

end NLQCLean
end

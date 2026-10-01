/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Geometry.CoordinateMinors

/-!
# Jacobian bound on the constructed coordinate charts

Differentiate the chart identity and transfer the maximal
minor comparison to the graph derivative. No slope or chart-count premise
is introduced.
-/

section

open Set Filter
open scoped Topology

namespace NLQCLean

theorem CoordinateGraphChart.fderiv_graph_comp_projection {a m : ℕ}
    {φ : RealEuclidean m → RealEuclidean a} {I : Fin m → Fin a}
    (P : CoordinateGraphChart φ I) (hφ : ContDiffOn ℝ 1 φ (openUnitCube m))
    {x : RealEuclidean m} (hx : x ∈ P.parameterDomain) :
    (fderiv ℝ P.graph (coordinateProjection I (φ x))).comp
      ((coordinateProjectionL I).comp (fderiv ℝ φ x)) = fderiv ℝ φ x := by
  have hφAt := (hφ x (P.parameter_subset hx)).contDiffAt
    ((isOpen_openUnitCube m).mem_nhds (P.parameter_subset hx))
  have hy := P.mapsTo_base hx
  have hgAt := (P.smooth _ hy).contDiffAt (P.open_baseDomain.mem_nhds hy)
  have hder := hgAt.differentiableAt_one.hasFDerivAt.comp x
    ((coordinateProjectionL I).hasFDerivAt.comp x hφAt.differentiableAt_one.hasFDerivAt)
  have heq : (P.graph ∘ (coordinateProjection I ∘ φ)) =ᶠ[𝓝 x] φ := by
    filter_upwards [P.open_parameterDomain.mem_nhds hx] with z hz
    exact P.graph_on_parameter z hz
  have hfd := heq.fderiv_eq (𝕜 := ℝ)
  exact hder.fderiv.symm.trans hfd

theorem coordinateMinor_det_comp {a m : ℕ}
    (J : Fin m → Fin a) (A : RealEuclidean m →L[ℝ] RealEuclidean a)
    (B : RealEuclidean m →L[ℝ] RealEuclidean m) :
    ((coordinateProjectionL J).comp (A.comp B)).det =
      ((coordinateProjectionL J).comp A).det * B.det := by
  rw [← ContinuousLinearMap.comp_assoc]
  exact LinearMap.det_comp _ _

theorem CoordinateGraphChart.sqrt_gram_det_le_of_maximal {a m : ℕ}
    {φ : RealEuclidean m → RealEuclidean a} {s : Set.powersetCard (Fin a) m}
    (P : CoordinateGraphChart φ (coordinateMinorAxes s))
    (hφ : ContDiffOn ℝ 1 φ (openUnitCube m)) {x : RealEuclidean m}
    (hx : x ∈ P.parameterDomain)
    (hne : ((coordinateProjectionL (coordinateMinorAxes s)).comp (fderiv ℝ φ x)).det ≠ 0)
    (hmax : ∀ t : Set.powersetCard (Fin a) m,
      |((coordinateProjectionL (coordinateMinorAxes t)).comp (fderiv ℝ φ x)).det| ≤
        |((coordinateProjectionL (coordinateMinorAxes s)).comp (fderiv ℝ φ x)).det|) :
    Real.sqrt (((fderiv ℝ P.graph (coordinateProjection (coordinateMinorAxes s) (φ x))).adjoint).comp
      (fderiv ℝ P.graph (coordinateProjection (coordinateMinorAxes s) (φ x)))).det ≤ (2 : ℝ) ^ a := by
  let G := fderiv ℝ P.graph (coordinateProjection (coordinateMinorAxes s) (φ x))
  let B := (coordinateProjectionL (coordinateMinorAxes s)).comp (fderiv ℝ φ x)
  have hfactor : G.comp B = fderiv ℝ φ x := P.fderiv_graph_comp_projection hφ hx
  have hbound : ∀ t : Set.powersetCard (Fin a) m,
      |((coordinateProjectionL (coordinateMinorAxes t)).comp G).det| ≤ 1 := by
    intro t
    have hdet := coordinateMinor_det_comp (coordinateMinorAxes t) G B
    rw [hfactor] at hdet
    have ht := hmax t
    rw [hdet, abs_mul] at ht
    have hBpos : 0 < |B.det| := abs_pos.mpr hne
    apply (mul_le_mul_iff_left₀ hBpos).mp
    simpa only [B, mul_one, one_mul, mul_comm] using ht
  simpa only [mul_one] using sqrt_gram_det_le_of_coordinateMinors_le G zero_le_one hbound

theorem CoordinateGraphChart.composite_det_le_of_maximal {a m : ℕ}
    {φ : RealEuclidean m → RealEuclidean a} {s : Set.powersetCard (Fin a) m}
    (P : CoordinateGraphChart φ (coordinateMinorAxes s))
    (hφ : ContDiffOn ℝ 1 φ (openUnitCube m)) {x : RealEuclidean m}
    (hx : x ∈ P.parameterDomain)
    (hne : ((coordinateProjectionL (coordinateMinorAxes s)).comp (fderiv ℝ φ x)).det ≠ 0)
    (hmax : ∀ t : Set.powersetCard (Fin a) m,
      |((coordinateProjectionL (coordinateMinorAxes t)).comp (fderiv ℝ φ x)).det| ≤
        |((coordinateProjectionL (coordinateMinorAxes s)).comp (fderiv ℝ φ x)).det|)
    (L : RealEuclidean a →L[ℝ] RealEuclidean m) {b : ℝ} (hb : topRealJacobian L ≤ b) :
    |(L.comp (fderiv ℝ P.graph (coordinateProjection (coordinateMinorAxes s) (φ x)))).det| ≤
      b * (2 : ℝ) ^ a := by
  exact (rectangular_det_le L _).trans (mul_le_mul hb
    (P.sqrt_gram_det_le_of_maximal hφ hx hne hmax) (Real.sqrt_nonneg _)
    ((topRealJacobian_nonneg L).trans hb))

end NLQCLean
end

import NLQCLean.Approx.PVMExtendedPolynomial
import NLQCLean.Rigidity.PVMCoordinateDifferential
import NLQCLean.Geometry.ThickenedJacobian

/-!
# The PVM polynomial witness Jacobian bound

The evaluated polynomial has an ambient rank-plus-error
decomposition on its exact source. The top-Jacobian convention
then gives the determinant bound needed by the image-volume theorem.
-/

namespace NLQCLean
open scoped Matrix.Norms.Frobenius

theorem pvmMotionRank_le_ambientDimension {d : ℕ} (hd : 2 ≤ d) :
    3 * d ^ 2 - 2 ≤ 2 * d ^ 4 := by
  have hs : 4 ≤ d ^ 2 := by nlinarith
  have hp : d ^ 4 = d ^ 2 * d ^ 2 := by ring
  rw [hp]
  have hm : 3 * d ^ 2 ≤ 2 * (d ^ 2 * d ^ 2) := by nlinarith
  exact (Nat.sub_le _ _).trans hm

namespace PVMReverseBlocks
variable {d K : ℕ} (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) {P : ℕ} (hP : PVMReverseShape.AdmissibleBudget s P)

/-- Euclidean rank/error bounds for the evaluated polynomial map on
the exact basic closed source.  -/
theorem witnessFormat_ambient_rank_error (hd2 : 2 ≤ d) {δ : ℝ} (hδ : 0 ≤ δ)
    {x : RealEuclidean P} (hx : x ∈ (witnessFormat s hd hfloor hP δ).source) :
    ∃ T R : RealEuclidean P →L[ℝ] RealEuclidean (2 * d ^ 4),
      fderiv ℝ (coordinateOverlapPolynomial s hd hfloor hP).eval x = T + R ∧
      Module.finrank ℝ (LinearMap.range T.toLinearMap) ≤ 3 * d ^ 2 - 2 ∧
      ‖fderiv ℝ (coordinateOverlapPolynomial s hd hfloor hP).eval x‖ ≤ (P : ℝ) ∧
      ‖R‖ ≤ δ * P := by
  obtain ⟨hv, _, hdef⟩ := (mem_witnessFormat_source_iff s hd hfloor hP δ x).mp hx
  have he : (coordinateOverlapPolynomial s hd hfloor hP).eval = coordinateOverlap s hd hfloor hP :=
    funext (coordinateOverlapPolynomial_eval s hd hfloor hP)
  rw [he]
  exact exists_coordinateOverlap_rank_error_decomposition s hd hfloor hP hd2 hv hδ hdef

/-- The variational tail estimate: the adjoint is small outside a subspace
of dimension at most 3d²−2. All source directions are ambient directions. -/
theorem witnessFormat_ambient_transverse_bound (hd2 : 2 ≤ d) {δ : ℝ} (hδ : 0 ≤ δ)
    {x : RealEuclidean P}
    (hx : x ∈ (witnessFormat s hd hfloor hP δ).source) :
    ∃ V : Submodule ℝ (RealEuclidean (2 * d ^ 4)),
      Module.finrank ℝ V ≤ 3 * d ^ 2 - 2 ∧
      ∀ y ∈ Vᗮ,
        ‖(fderiv ℝ (coordinateOverlapPolynomial s hd hfloor hP).eval x).adjoint y‖ ≤
          (δ * P) * ‖y‖ := by
  obtain ⟨T, R, he, ht, _, hr⟩ := witnessFormat_ambient_rank_error s hd hfloor hP hd2 hδ hx
  refine ⟨T.range, ht, ?_⟩
  intro y hy
  have hyT : T.adjoint y = 0 := by
    change y ∈ T.adjoint.ker
    rwa [← T.orthogonal_range]
  rw [he, map_add, add_apply, hyT, zero_add]
  exact (R.adjoint.le_opNorm y).trans (mul_le_mul_of_nonneg_right
    (by simpa only [LinearIsometryEquiv.norm_map] using hr) (norm_nonneg y))

/-- The target-dimensional thickened Jacobian in the unchanged
image-volume bound. -/
theorem witnessFormat_thickenedJacobian_le
    (hd2 : 2 ≤ d) {δ c : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hc : 0 ≤ c)
    {x : RealEuclidean P}
    (hx : x ∈ (witnessFormat s hd hfloor hP δ).source) :
    topRealJacobian (thickenedLinearMap (fderiv ℝ (coordinateOverlapPolynomial s hd hfloor hP).eval x) c) ≤
      ((P : ℝ) + c) ^ (3 * d ^ 2 - 2) *
        (δ * P + c) ^ (2 * d ^ 4 - (3 * d ^ 2 - 2)) := by
  obtain ⟨T, R, he, ht, hn, hr⟩ := witnessFormat_ambient_rank_error s hd hfloor hP hd2 hδ hx
  exact topRealJacobian_thickenedLinearMap_le _ T R he
    (Λ := (P : ℝ)) (μ := δ * P)
    (by positivity) (by nlinarith [show 0 ≤ (P : ℝ) by positivity]) hc hn hr ht
    (pvmMotionRank_le_ambientDimension hd2)

/-- The displayed bound is a nonnegative admissible Jacobian bound. -/
theorem witnessFormat_jacobianBound_nonneg {δ c : ℝ} (hδ : 0 ≤ δ) (hc : 0 ≤ c) :
    0 ≤ ((P : ℝ) + c) ^ (3 * d ^ 2 - 2) *
      (δ * P + c) ^ (2 * d ^ 4 - (3 * d ^ 2 - 2)) := by
  positivity

end PVMReverseBlocks
end NLQCLean

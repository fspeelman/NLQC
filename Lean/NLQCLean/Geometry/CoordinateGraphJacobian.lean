/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Geometry.PolynomialImageVolumeHypothesis
import NLQCLean.Semialgebraic.CoordinateGraphs
import Mathlib.Analysis.InnerProductSpace.ExteriorPower

/-!
# Rectangular Jacobians and coordinate minors

The rectangular determinant inequality follows from the Gram
inner product on exterior powers and Cauchy--Schwarz, including singular maps.
-/

section

open Set Matrix
open scoped RealInnerProductSpace

namespace NLQCLean

theorem abs_det_inner_le_sqrt_gram {a m : ℕ}
    (x y : Fin m → RealEuclidean a) :
    |(Matrix.of fun i j => inner ℝ (x j) (y i)).det| ≤
      Real.sqrt (Matrix.gram ℝ x).det * Real.sqrt (Matrix.gram ℝ y).det := by
  have h := abs_real_inner_le_norm (exteriorPower.ιMulti ℝ m x) (exteriorPower.ιMulti ℝ m y)
  have hn (v : Fin m → RealEuclidean a) :
      ‖exteriorPower.ιMulti ℝ m v‖ = Real.sqrt (Matrix.gram ℝ v).det := by
    rw [norm_eq_sqrt_real_inner, exteriorPower.inner_ιMulti_self]
  rw [exteriorPower.inner_ιMulti_ιMulti, hn x, hn y] at h
  exact h

theorem gram_det_eq_adjoint_comp_det {a m : ℕ}
    (A : RealEuclidean m →L[ℝ] RealEuclidean a) :
    (Matrix.gram ℝ (fun i => A (EuclideanSpace.basisFun (Fin m) ℝ i))).det =
      (A.adjoint.comp A).det := by
  let b := EuclideanSpace.basisFun (Fin m) ℝ
  have heq : Matrix.gram ℝ (fun i => A (b i)) =
      LinearMap.toMatrix b.toBasis b.toBasis (A.adjoint.comp A).toLinearMap := by
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply]
    change inner ℝ (A (b i)) (A (b j)) = (A.adjoint (A (b j))) i
    rw [← EuclideanSpace.basisFun_inner]
    exact (A.adjoint_inner_right (b i) (A (b j))).symm
  change (Matrix.gram ℝ (fun i => A (b i))).det = _
  rw [heq, LinearMap.det_toMatrix]

theorem rectangular_det_le {a m : ℕ}
    (L : RealEuclidean a →L[ℝ] RealEuclidean m)
    (A : RealEuclidean m →L[ℝ] RealEuclidean a) :
    |(L.comp A).det| ≤ topRealJacobian L * Real.sqrt (A.adjoint.comp A).det := by
  let b := EuclideanSpace.basisFun (Fin m) ℝ
  have h := abs_det_inner_le_sqrt_gram (fun i => A (b i)) (fun i => L.adjoint (b i))
  have heq : (Matrix.of fun i j => inner ℝ (A (b j)) (L.adjoint (b i))) =
      LinearMap.toMatrix b.toBasis b.toBasis (L.comp A).toLinearMap := by
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply]
    change inner ℝ (A (b j)) (L.adjoint (b i)) = (L (A (b j))) i
    rw [L.adjoint_inner_right]
    exact EuclideanSpace.inner_basisFun_real (Fin m) (L (A (b j))) i
  have hleft : |(L.comp A).det| =
      |(Matrix.of fun i j => inner ℝ (A (b j)) (L.adjoint (b i))).det| :=
    (congrArg abs ((congrArg Matrix.det heq).trans
      (LinearMap.det_toMatrix b.toBasis (L.comp A).toLinearMap))).symm
  have hL : (Matrix.gram ℝ (fun i => L.adjoint (b i))).det = (L.comp L.adjoint).det := by
    exact (gram_det_eq_adjoint_comp_det L.adjoint).trans
      (congrArg (fun f : RealEuclidean a →L[ℝ] RealEuclidean m => (f.comp L.adjoint).det)
        (ContinuousLinearMap.adjoint_adjoint L))
  have hright : Real.sqrt (Matrix.gram ℝ (fun i => A (b i))).det *
      Real.sqrt (Matrix.gram ℝ (fun i => L.adjoint (b i))).det =
        topRealJacobian L * Real.sqrt (A.adjoint.comp A).det := by
    calc
      _ = Real.sqrt (A.adjoint.comp A).det * Real.sqrt (L.comp L.adjoint).det :=
        congrArg₂ (fun x y : ℝ => x * y)
          (congrArg Real.sqrt (gram_det_eq_adjoint_comp_det A)) (congrArg Real.sqrt hL)
      _ = _ := mul_comm _ _
  exact hleft.trans_le (h.trans_eq hright)

end NLQCLean
end

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Geometry.CoordinateGraphJacobian
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Coordinate minors indexed by subsets

Parseval in the exterior-power orthonormal basis gives the
Cauchy--Binet sum of squared coordinate minors, with at most 2^a terms.
-/

section

open Set Matrix
open scoped RealInnerProductSpace BigOperators

namespace NLQCLean

noncomputable def coordinateMinorAxes {a m : ℕ} (s : Set.powersetCard (Fin a) m) :
    Fin m → Fin a := Set.powersetCard.ofFinEmbEquiv.symm s

theorem coordinateMinorAxes_injective {a m : ℕ} (s : Set.powersetCard (Fin a) m) :
    Function.Injective (coordinateMinorAxes s) :=
  (Set.powersetCard.ofFinEmbEquiv.symm s).injective

theorem card_coordinateMinorIndices_le (a m : ℕ) :
    Fintype.card (Set.powersetCard (Fin a) m) ≤ 2 ^ a := by
  rw [← Nat.card_eq_fintype_card, Set.powersetCard.card]
  simpa using Nat.choose_le_two_pow a m

theorem exterior_coordinate_eq_det {a m : ℕ}
    (A : RealEuclidean m →L[ℝ] RealEuclidean a) (s : Set.powersetCard (Fin a) m) :
    inner ℝ ((EuclideanSpace.basisFun (Fin a) ℝ).exteriorPower m s)
      (exteriorPower.ιMulti ℝ m (fun i => A (EuclideanSpace.basisFun (Fin m) ℝ i))) =
        ((coordinateProjectionL (coordinateMinorAxes s)).comp A).det := by
  let ba := EuclideanSpace.basisFun (Fin a) ℝ
  let bm := EuclideanSpace.basisFun (Fin m) ℝ
  have hb : ba.exteriorPower m s =
      exteriorPower.ιMulti ℝ m (fun j => ba (coordinateMinorAxes s j)) := by
    change (ba.exteriorPower m).toBasis s = _
    rw [OrthonormalBasis.toBasis_exteriorPower, exteriorPower.basis_apply]
    rfl
  change inner ℝ (ba.exteriorPower m s) (exteriorPower.ιMulti ℝ m (fun i => A (bm i))) = _
  rw [hb, exteriorPower.inner_ιMulti_ιMulti]
  have heq : (Matrix.of fun i j => inner ℝ (ba (coordinateMinorAxes s j)) (A (bm i))) =
      (LinearMap.toMatrix bm.toBasis bm.toBasis
        ((coordinateProjectionL (coordinateMinorAxes s)).comp A).toLinearMap).transpose := by
    ext i j
    rw [Matrix.transpose_apply, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply]
    change inner ℝ (ba (coordinateMinorAxes s j)) (A (bm i)) = (A (bm i)) (coordinateMinorAxes s j)
    exact EuclideanSpace.basisFun_inner (Fin a) ℝ _ _
  rw [heq, Matrix.det_transpose, LinearMap.det_toMatrix]

theorem sum_sq_coordinateMinors {a m : ℕ}
    (A : RealEuclidean m →L[ℝ] RealEuclidean a) :
    ∑ s : Set.powersetCard (Fin a) m,
      (((coordinateProjectionL (coordinateMinorAxes s)).comp A).det) ^ 2 =
        (A.adjoint.comp A).det := by
  let w := exteriorPower.ιMulti ℝ m (fun i => A (EuclideanSpace.basisFun (Fin m) ℝ i))
  calc
    _ = ∑ s, (inner ℝ ((EuclideanSpace.basisFun (Fin a) ℝ).exteriorPower m s) w) ^ 2 := by
      apply Finset.sum_congr rfl
      intro s _
      rw [exterior_coordinate_eq_det]
    _ = ‖w‖ ^ 2 := ((EuclideanSpace.basisFun (Fin a) ℝ).exteriorPower m).sum_sq_inner_right w
    _ = (Matrix.gram ℝ (fun i => A (EuclideanSpace.basisFun (Fin m) ℝ i))).det := by
      rw [← real_inner_self_eq_norm_sq, exteriorPower.inner_ιMulti_self]
    _ = _ := gram_det_eq_adjoint_comp_det A

theorem sqrt_gram_det_le_of_coordinateMinors_le {a m : ℕ}
    (A : RealEuclidean m →L[ℝ] RealEuclidean a) {K : ℝ} (hK : 0 ≤ K)
    (hminor : ∀ s : Set.powersetCard (Fin a) m,
      |((coordinateProjectionL (coordinateMinorAxes s)).comp A).det| ≤ K) :
    Real.sqrt (A.adjoint.comp A).det ≤ (2 : ℝ) ^ a * K := by
  have hsum : ∑ s : Set.powersetCard (Fin a) m,
      (((coordinateProjectionL (coordinateMinorAxes s)).comp A).det) ^ 2 ≤
        ∑ _ : Set.powersetCard (Fin a) m, K ^ 2 := by
    apply Finset.sum_le_sum
    intro s _
    exact sq_le_sq' (by have := (abs_le.mp (hminor s)).1; linarith) (abs_le.mp (hminor s)).2
  have hcard : (Fintype.card (Set.powersetCard (Fin a) m) : ℝ) ≤ (2 : ℝ) ^ a := by
    exact_mod_cast card_coordinateMinorIndices_le a m
  have hpow : 1 ≤ (2 : ℝ) ^ a := one_le_pow₀ (by norm_num)
  have hsqrt : Real.sqrt (Fintype.card (Set.powersetCard (Fin a) m) : ℝ) ≤ (2 : ℝ) ^ a := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, hcard.trans ?_⟩
    nlinarith
  calc
    _ = Real.sqrt (∑ s : Set.powersetCard (Fin a) m,
        (((coordinateProjectionL (coordinateMinorAxes s)).comp A).det) ^ 2) :=
      congrArg Real.sqrt (sum_sq_coordinateMinors A).symm
    _ ≤ Real.sqrt (∑ _ : Set.powersetCard (Fin a) m, K ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (Fintype.card (Set.powersetCard (Fin a) m) : ℝ) * K := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.sqrt_mul (Nat.cast_nonneg _),
        Real.sqrt_sq hK]
    _ ≤ _ := mul_le_mul_of_nonneg_right hsqrt hK

theorem exists_maximal_coordinateMinor {a m : ℕ}
    (A : RealEuclidean m →L[ℝ] RealEuclidean a) (hA : Function.Injective A) :
    ∃ s : Set.powersetCard (Fin a) m,
      ((coordinateProjectionL (coordinateMinorAxes s)).comp A).det ≠ 0 ∧
      (∀ t : Set.powersetCard (Fin a) m,
        |((coordinateProjectionL (coordinateMinorAxes t)).comp A).det| ≤
          |((coordinateProjectionL (coordinateMinorAxes s)).comp A).det|) ∧
      Real.sqrt (A.adjoint.comp A).det ≤ (2 : ℝ) ^ a *
        |((coordinateProjectionL (coordinateMinorAxes s)).comp A).det| := by
  have hdet : (A.adjoint.comp A).det ≠ 0 := by
    intro h
    have hk := LinearMap.det_eq_zero_iff_ker_ne_bot.mp h
    apply hk
    change (A.adjoint.comp A).ker = ⊥
    rw [ContinuousLinearMap.ker_adjoint_comp_self]
    exact LinearMap.ker_eq_bot.mpr hA
  obtain ⟨s, hs⟩ : ∃ s : Set.powersetCard (Fin a) m,
      ((coordinateProjectionL (coordinateMinorAxes s)).comp A).det ≠ 0 := by
    by_contra! h
    apply hdet
    rw [← sum_sq_coordinateMinors]
    simp only [h, zero_pow (by omega : 2 ≠ 0), Finset.sum_const_zero]
  have : Nonempty (Set.powersetCard (Fin a) m) := ⟨s⟩
  obtain ⟨t, _, ht⟩ := Finset.univ.exists_max_image
    (fun t : Set.powersetCard (Fin a) m => |((coordinateProjectionL (coordinateMinorAxes t)).comp A).det|)
    Finset.univ_nonempty
  have hmax := fun u => ht u (Finset.mem_univ u)
  refine ⟨t, ?_, hmax, sqrt_gram_det_le_of_coordinateMinors_le A (abs_nonneg _) hmax⟩
  intro hz
  have := hmax s
  rw [hz, abs_zero] at this
  exact hs (abs_eq_zero.mp (le_antisymm this (abs_nonneg _)))

theorem exists_large_coordinateMinor_of_isometry {a m : ℕ}
    (A : RealEuclidean m →L[ℝ] RealEuclidean a)
    (hA : A.adjoint.comp A = ContinuousLinearMap.id ℝ (RealEuclidean m)) :
    ∃ s : Set.powersetCard (Fin a) m,
      1 / (2 : ℝ) ^ a ≤ |((coordinateProjectionL (coordinateMinorAxes s)).comp A).det| := by
  have hinj : Function.Injective A := by
    intro x y hxy
    have h := congrArg A.adjoint hxy
    have hx := congrArg (fun f : RealEuclidean m →L[ℝ] RealEuclidean m => f x) hA
    have hy := congrArg (fun f : RealEuclidean m →L[ℝ] RealEuclidean m => f y) hA
    exact hx.symm.trans (h.trans hy)
  obtain ⟨s, _, _, hs⟩ := exists_maximal_coordinateMinor A hinj
  refine ⟨s, (div_le_iff₀ (by positivity)).mpr ?_⟩
  have hone : (A.adjoint.comp A).det = 1 := by
    rw [hA]
    exact LinearMap.det_id
  rw [hone, Real.sqrt_one] at hs
  simpa only [mul_comm] using hs

end NLQCLean
end

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

import NLQCLean.Geometry.CoordinateMinors

/-!
# Determinants with a varying block of rows

An alternating `m`-form on `ℝ^a` is a linear functional on the exterior power. Expanding
in the orthonormal basis of coordinate wedges and applying Cauchy--Schwarz bounds its value
at `l` by `‖l₁ ∧ ⋯ ∧ lₘ‖ = √det(gram l)` times the sum of its values on coordinate frames.

This is applied to square matrices on `Fin a ⊕ Fin m` whose first `a` rows are fixed and
whose last `m` rows are supported on the first block of columns. Their determinant is an
alternating function of the last rows.
-/

namespace NLQCLean

open Matrix
open scoped RealInnerProductSpace

/-- Every alternating form is bounded by the Gram volume times the sum of its values on
coordinate frames. -/
theorem abs_alternatingMap_le {a m : ℕ} (ω : RealEuclidean a [⋀^Fin m]→ₗ[ℝ] ℝ)
    (l : Fin m → RealEuclidean a) :
    |ω l| ≤ Real.sqrt (Matrix.gram ℝ l).det *
      ∑ s : Set.powersetCard (Fin a) m,
        |ω (fun k => EuclideanSpace.basisFun (Fin a) ℝ (coordinateMinorAxes s k))| := by
  let ba := EuclideanSpace.basisFun (Fin a) ℝ
  let bΛ := ba.exteriorPower m
  let Ω := exteriorPower.alternatingMapLinearEquiv ω
  have hb : ∀ s, bΛ s = exteriorPower.ιMulti ℝ m (fun j => ba (coordinateMinorAxes s j)) := by
    intro s
    change (ba.exteriorPower m).toBasis s = _
    rw [OrthonormalBasis.toBasis_exteriorPower, exteriorPower.basis_apply]
    rfl
  have hnorm : ‖exteriorPower.ιMulti ℝ m l‖ = Real.sqrt (Matrix.gram ℝ l).det := by
    rw [norm_eq_sqrt_real_inner, exteriorPower.inner_ιMulti_self]
  have hexp : ω l = ∑ s, ⟪bΛ s, exteriorPower.ιMulti ℝ m l⟫ * ω (fun k => ba (coordinateMinorAxes s k)) := by
    rw [← exteriorPower.alternatingMapLinearEquiv_apply_ιMulti ω l]
    conv_lhs => rw [← bΛ.sum_repr' (exteriorPower.ιMulti ℝ m l)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, smul_eq_mul, hb s, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rw [hexp, ← hnorm, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [abs_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  calc |⟪bΛ s, exteriorPower.ιMulti ℝ m l⟫| ≤ ‖bΛ s‖ * ‖exteriorPower.ιMulti ℝ m l‖ :=
        abs_real_inner_le_norm _ _
    _ = ‖exteriorPower.ιMulti ℝ m l‖ := by rw [bΛ.orthonormal.1 s, one_mul]

/-- The row of the lower block determined by a vector of the first block. -/
def lowerBlockRow {a m : ℕ} (v : RealEuclidean a) : Fin a ⊕ Fin m → ℝ :=
  Sum.elim (fun c => v c) 0

theorem lowerBlockRow_add {a m : ℕ} (v w : RealEuclidean a) :
    (lowerBlockRow (m := m) (v + w)) = lowerBlockRow v + lowerBlockRow w := by
  funext c
  rcases c with c | c <;> simp [lowerBlockRow]

theorem lowerBlockRow_smul {a m : ℕ} (t : ℝ) (v : RealEuclidean a) :
    (lowerBlockRow (m := m) (t • v)) = t • lowerBlockRow v := by
  funext c
  rcases c with c | c <;> simp [lowerBlockRow]

/-- Fixed upper rows and lower rows supported on the first block of columns. -/
def blockRowMatrix {a m : ℕ} (R : Fin a → Fin a ⊕ Fin m → ℝ) (l : Fin m → RealEuclidean a) :
    Matrix (Fin a ⊕ Fin m) (Fin a ⊕ Fin m) ℝ :=
  Matrix.of fun r => Sum.elim R (fun k => lowerBlockRow (l k)) r

theorem blockRowMatrix_update {a m : ℕ} [DecidableEq (Fin m)] (R : Fin a → Fin a ⊕ Fin m → ℝ)
    (l : Fin m → RealEuclidean a) (k : Fin m) (v : RealEuclidean a) :
    blockRowMatrix R (Function.update l k v) =
      (blockRowMatrix R l).updateRow (Sum.inr k) (lowerBlockRow v) := by
  ext r c
  rcases r with j | j
  · simp [blockRowMatrix, Matrix.updateRow_apply]
  · by_cases hj : j = k
    · subst hj
      simp [blockRowMatrix, Matrix.updateRow_apply]
    · simp [blockRowMatrix, Matrix.updateRow_apply, hj]

/-- The determinant as an alternating function of the lower rows. -/
noncomputable def blockRowDet {a m : ℕ} (R : Fin a → Fin a ⊕ Fin m → ℝ) :
    RealEuclidean a [⋀^Fin m]→ₗ[ℝ] ℝ where
  toFun l := (blockRowMatrix R l).det
  map_update_add' := by
    intro inst l k v w
    obtain rfl : inst = instDecidableEqFin m := Subsingleton.elim _ _
    rw [blockRowMatrix_update, blockRowMatrix_update, blockRowMatrix_update,
      lowerBlockRow_add, det_updateRow_add]
  map_update_smul' := by
    intro inst l k t v
    obtain rfl : inst = instDecidableEqFin m := Subsingleton.elim _ _
    rw [blockRowMatrix_update, blockRowMatrix_update, lowerBlockRow_smul, det_updateRow_smul,
      smul_eq_mul]
  map_eq_zero_of_eq' l i j hij hne := by
    refine det_zero_of_row_eq (i := Sum.inr i) (j := Sum.inr j) (fun h => hne ?_) ?_
    · exact Sum.inr_injective h
    · change lowerBlockRow (l i) = lowerBlockRow (l j)
      rw [hij]

theorem blockRowDet_apply {a m : ℕ} (R : Fin a → Fin a ⊕ Fin m → ℝ)
    (l : Fin m → RealEuclidean a) : blockRowDet R l = (blockRowMatrix R l).det := rfl

/-- **Block Cauchy--Binet inequality.** -/
theorem abs_det_blockRowMatrix_le {a m : ℕ} (R : Fin a → Fin a ⊕ Fin m → ℝ)
    (l : Fin m → RealEuclidean a) :
    |(blockRowMatrix R l).det| ≤ Real.sqrt (Matrix.gram ℝ l).det *
      ∑ s : Set.powersetCard (Fin a) m,
        |(blockRowMatrix R
          (fun k => EuclideanSpace.basisFun (Fin a) ℝ (coordinateMinorAxes s k))).det| :=
  abs_alternatingMap_le (blockRowDet R) l

end NLQCLean

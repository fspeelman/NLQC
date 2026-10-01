import NLQCLean.Models.ClassicalCommunication.TwoLevelDecoder
import NLQCLean.Invariants.LocalUnitaryPurity

/-!
# Local-unitary cancellation in an exact channel restriction

Local inverse unitaries can be absorbed into actual input embeddings and
output Stinespring maps. The resulting restricted channel agrees exactly
with that for the original target. All spectator environments are retained.
-/

namespace NLQCLean.ClassicalCommunication

attribute [local implicit_reducible] Matrix

open Matrix
open scoped Kronecker

variable {ιA ιB τA τB κA κB δA δB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype τA] [Fintype τB]
variable [Fintype δA] [Fintype δB]
variable [DecidableEq ιA] [DecidableEq ιB]

/-- The restricted ideal channel, with both local output environments discarded. -/
def localChannelRestriction (EA : Matrix ιA τA ℂ) (EB : Matrix ιB τB ℂ)
    (HA : Matrix (κA × δA) ιA ℂ) (HB : Matrix (κB × δB) ιB ℂ)
    (U : Matrix (ιA × ιB) (ιA × ιB) ℂ) :=
  (tensorChannels (channelOf HA) (channelOf HB)).comp
    ((adConj U).comp (adConj (EA ⊗ₖ EB)))

/-- The same restriction as a single actual Stinespring matrix. -/
theorem localChannelRestriction_eq_channelOf
    (EA : Matrix ιA τA ℂ) (EB : Matrix ιB τB ℂ)
    (HA : Matrix (κA × δA) ιA ℂ) (HB : Matrix (κB × δB) ιB ℂ)
    (U : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    localChannelRestriction EA EB HA HB U =
      channelOf (((HA ⊗ₖ HB).submatrix (outputRegroup κA κB δA δB) id * U) *
        (EA ⊗ₖ EB)) := by
  rw [localChannelRestriction, tensorChannels_channelOf_regrouped,
    ← LinearMap.comp_assoc, ← channelOf_mul_eq_comp, ← channelOf_mul_eq_comp]

/-- A unitary adjoint is an isometry, so it may be inserted into physical maps. -/
theorem isIsometry_conjTranspose_of_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U : Matrix ι ι ℂ} (hU : U ∈ Matrix.unitaryGroup ι ℂ) : IsIsometry Uᴴ := by
  change Uᴴᴴ * Uᴴ = 1
  rw [Matrix.conjTranspose_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff.mp hU

/-- Cancel all four local factors inside the actual restricted dilation. -/
theorem localChannelRestriction_local_unitary_cancel
    (EA : Matrix ιA τA ℂ) (EB : Matrix ιB τB ℂ)
    (HA : Matrix (κA × δA) ιA ℂ) (HB : Matrix (κB × δB) ιB ℂ)
    (U : Matrix (ιA × ιB) (ιA × ιB) ℂ)
    {LA LB RA RB}
    (hLA : LA ∈ Matrix.unitaryGroup ιA ℂ) (hLB : LB ∈ Matrix.unitaryGroup ιB ℂ)
    (hRA : RA ∈ Matrix.unitaryGroup ιA ℂ) (hRB : RB ∈ Matrix.unitaryGroup ιB ℂ) :
    localChannelRestriction (RAᴴ * EA) (RBᴴ * EB) (HA * LAᴴ) (HB * LBᴴ)
      ((LA ⊗ₖ LB) * U * (RA ⊗ₖ RB)) = localChannelRestriction EA EB HA HB U := by
  rw [localChannelRestriction_eq_channelOf, localChannelRestriction_eq_channelOf]
  have hpost : ((HA * LAᴴ) ⊗ₖ (HB * LBᴴ)).submatrix
      (outputRegroup κA κB δA δB) id =
      (HA ⊗ₖ HB).submatrix (outputRegroup κA κB δA δB) id * (LA ⊗ₖ LB)ᴴ := by
    rw [Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul,
      Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_id_id]
  have hpre : (RAᴴ * EA) ⊗ₖ (RBᴴ * EB) = (RA ⊗ₖ RB)ᴴ * (EA ⊗ₖ EB) := by
    rw [Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul]
  have hL : (LA ⊗ₖ LB)ᴴ * (LA ⊗ₖ LB) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.kronecker_mem_unitary hLA hLB)
  have hR : (RA ⊗ₖ RB) * (RA ⊗ₖ RB)ᴴ = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (Matrix.kronecker_mem_unitary hRA hRB)
  rw [hpost, hpre]
  congr 1
  calc
    _ = (HA ⊗ₖ HB).submatrix (outputRegroup κA κB δA δB) id *
        ((LA ⊗ₖ LB)ᴴ * (LA ⊗ₖ LB)) * U *
        ((RA ⊗ₖ RB) * (RA ⊗ₖ RB)ᴴ) * (EA ⊗ₖ EB) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hL, hR, Matrix.mul_one, Matrix.mul_one]

/-- Independent local basis equivalences preserve the actual restricted channel. -/
theorem localChannelRestriction_reindex {νA νB : Type*}
    [Fintype νA] [Fintype νB] [DecidableEq νA] [DecidableEq νB]
    (eA : νA ≃ ιA) (eB : νB ≃ ιB)
    (EA : Matrix ιA τA ℂ) (EB : Matrix ιB τB ℂ)
    (HA : Matrix (κA × δA) ιA ℂ) (HB : Matrix (κB × δB) ιB ℂ)
    (U : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    localChannelRestriction (EA.submatrix eA id) (EB.submatrix eB id)
      (HA.submatrix id eA) (HB.submatrix id eB)
      (U.submatrix (eA.prodCongr eB) (eA.prodCongr eB)) =
      localChannelRestriction EA EB HA HB U := by
  rw [localChannelRestriction_eq_channelOf, localChannelRestriction_eq_channelOf]
  have hpost : ((HA.submatrix id eA) ⊗ₖ (HB.submatrix id eB)).submatrix
      (outputRegroup κA κB δA δB) id =
      (HA ⊗ₖ HB).submatrix (outputRegroup κA κB δA δB) (eA.prodCongr eB) := rfl
  have hpre : (EA.submatrix eA id) ⊗ₖ (EB.submatrix eB id) =
      (EA ⊗ₖ EB).submatrix (eA.prodCongr eB) id := rfl
  rw [hpost, hpre, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_id_id,
    Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, Matrix.submatrix_id_id]

end NLQCLean.ClassicalCommunication

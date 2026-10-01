import NLQCLean.Models.ChargedCompactProtocols
import NLQCLean.Models.ChargedCompactPVMProtocols

/-!
# Physical examples for charged compact optimization

The unitary identity has an exact budget-one physical implementation. The PVM
budget-one family is also physically nonempty, without a claim that it performs
every target PVM exactly.
-/

namespace NLQCLean

open Matrix
open scoped Kronecker

theorem identityFinProtocol_performs_identity (d : ℕ) :
    (identityFinProtocol d).PerformsUnitary
      (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) := by
  let F : Matrix ((Fin d × Fin 1) × (Fin d × Fin 1)) (Fin d × Fin d) ℂ :=
    (identityFinProtocol d).globalIsometry
  have hF : F =
      insertResource (Fin d) (Fin d) (fun _ : Fin 1 × Fin 1 => (1 : ℂ)) := by
    change NLQCLean.globalIsometry (fun _ : Fin 1 × Fin 1 => (1 : ℂ))
      (1 : Matrix (Fin d × Fin 1) (Fin d × Fin 1) ℂ)
      (1 : Matrix (Fin d × Fin 1) (Fin d × Fin 1) ℂ)
      (1 : Matrix (Fin d × Fin 1) (Fin d × Fin 1) ℂ)
      (1 : Matrix (Fin d × Fin 1) (Fin d × Fin 1) ℂ) = _
    simp only [globalIsometry_eq, Matrix.one_kronecker_one, Matrix.one_mul]
    rw [exchangeMatrix_mul]
    rfl
  have hγ : IsUnitVector (fun _ : Fin 1 × Fin 1 => (1 : ℂ)) := by
    simp [IsUnitVector]
  change channelOf (F.submatrix
    (outputRegroup (Fin d) (Fin d) (Fin 1) (Fin 1)) id) = adConj _
  rw [hF, ← insertVector_eq_insertResource_submatrix]
  simpa only [Matrix.mul_one] using channelOf_insertVector_mul hγ
    (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)

theorem unitaryScoreDeficit_identity_eq_zero {d K : ℕ} (hd : 2 ≤ d) (hK : 1 ≤ K) :
    unitaryScoreDeficit (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K = 0 :=
  (unitaryScoreDeficit_eq_zero_iff hd hK _ isIsometry_one).mpr
    ⟨_, identityFinProtocol d, identityFinProtocol_hasFootprint d hK,
      identityFinProtocol_performs_identity d⟩

theorem identity_mem_pureReachable_one {d : ℕ} (hd : 2 ≤ d) :
    (1 : Matrix.unitaryGroup (Fin d × Fin d) ℂ) ∈ pureReachable d 1 0 := by
  let : NeZero d := ⟨by omega⟩
  let P := identityFinProtocol d
  refine ⟨_, P, identityFinProtocol_hasFootprint d le_rfl, ?_⟩
  have hchan := identityFinProtocol_performs_identity d
  change P.operationalChannel = adConj (1 : Matrix (Fin d × Fin d) _ ℂ) at hchan
  change 1 - 0 ≤ scoreU (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    P.operationalChannel
  rw [hchan, scoreU_adConj_self isIsometry_one]
  norm_num

theorem identity_mem_mixedReachable_one {d : ℕ} (hd : 2 ≤ d) :
    (1 : Matrix.unitaryGroup (Fin d × Fin d) ℂ) ∈ mixedReachable d 1 0 := by
  rw [mixedReachable_eq_pureReachable]
  exact identity_mem_pureReachable_one hd

end NLQCLean

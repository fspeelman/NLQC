import NLQCLean.Models.ChoiAlgebra

/-!
# The actual Choi-to-diamond and diamond-to-score bridges

The normalized maximally entangled input is a trace-norm-one
test in the all-ancilla diamond supremum. The trace-zero projection test
then gives normalized Choi infidelity at most normalized diamond error.
-/

namespace NLQCLean

open Matrix
open scoped ComplexOrder

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The normalized maximally entangled input is the Choi state of the identity. -/
noncomputable def maximallyEntangledInput (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix (ι × ι) (ι × ι) ℂ := choiMatrix (adConj (1 : Matrix ι ι ℂ))

theorem traceNorm_maximallyEntangledInput [Nonempty ι] :
    traceNorm (maximallyEntangledInput ι) = 1 := by
  rw [maximallyEntangledInput,
    PosSemidef.traceNorm_eq_trace (posSemidef_choiMatrix_adConj (1 : Matrix ι ι ℂ)),
    trace_choiMatrix_adConj_eq_one (by simp [IsIsometry])]
  rfl

omit [Fintype κ] [DecidableEq κ] in
/-- The Choi matrix is exactly the amplified channel on that normalized input. -/
theorem amplify_maximallyEntangledInput (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    amplify Φ ι (maximallyEntangledInput ι) = choiMatrix Φ := by
  ext p q
  rw [amplify_apply_block]
  have he : (fun i j => maximallyEntangledInput ι (i, p.2) (j, q.2)) =
      (Fintype.card ι : ℂ)⁻¹ • Matrix.single p.2 q.2 (1 : ℂ) := by
    ext i j
    simp [maximallyEntangledInput,
      Matrix.single_apply, ite_and, eq_comm]
  rw [he, map_smul]
  rfl

/-- The maximally entangled state is one of the actual diamond-norm tests. -/
theorem traceNorm_choiMatrix_le_diamondNorm [Nonempty ι]
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    traceNorm (choiMatrix Φ) ≤ diamondNorm Φ := by
  rw [← amplify_maximallyEntangledInput]
  exact traceNorm_amplify_le_diamondNorm Φ _ (by rw [traceNorm_maximallyEntangledInput])

theorem half_traceNorm_choi_sub_le_diamondError [Nonempty ι]
    (Φ Ψ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    traceNorm (choiMatrix Φ - choiMatrix Ψ) / 2 ≤ diamondError Φ Ψ := by
  rw [← choiMatrix_sub]
  exact div_le_div_of_nonneg_right (traceNorm_choiMatrix_le_diamondNorm (Φ - Ψ)) (by norm_num)

/-- The score-to-trace-distance inequality needs only the actual trace-one identity. -/
theorem one_sub_scoreU_le_half_traceNorm [Nonempty ι] {U : Matrix κ ι ℂ}
    (hU : IsIsometry U) (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (hΦ : (choiMatrix Φ).trace = 1) :
    1 - scoreU U Φ ≤ traceNorm (choiMatrix Φ - choiMatrix (adConj U)) / 2 := by
  have hP := posSemidef_choiMatrix_adConj U
  have hPP := choiMatrix_adConj_mul_self hU
  have htr : (choiMatrix (adConj U) - choiMatrix Φ).trace = 0 := by
    rw [Matrix.trace_sub, trace_choiMatrix_adConj_eq_one hU, hΦ, sub_self]
  have h := re_trace_projection_mul_le_half_traceNorm hP.1 hPP htr
  have he : (choiMatrix (adConj U) * (choiMatrix (adConj U) - choiMatrix Φ)).trace.re =
      1 - scoreU U Φ := by
    rw [Matrix.mul_sub, hPP, Matrix.trace_sub, Complex.sub_re,
      trace_choiMatrix_adConj_eq_one hU, ← scoreU_eq_re_trace_choi_mul]
    rfl
  rw [he] at h
  have hn : traceNorm (choiMatrix (adConj U) - choiMatrix Φ) =
      traceNorm (choiMatrix Φ - choiMatrix (adConj U)) := by
    rw [← traceNorm_neg (choiMatrix (adConj U) - choiMatrix Φ), neg_sub]
  rwa [hn] at h

/-- Normalized Choi infidelity is bounded by diamond error for every trace-one Choi map. -/
theorem one_sub_scoreU_le_diamondError [Nonempty ι] {U : Matrix κ ι ℂ}
    (hU : IsIsometry U) (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (hΦ : (choiMatrix Φ).trace = 1) : 1 - scoreU U Φ ≤ diamondError Φ (adConj U) :=
  (one_sub_scoreU_le_half_traceNorm hU Φ hΦ).trans
    (half_traceNorm_choi_sub_le_diamondError Φ (adConj U))

/-- The operational isometric-channel bridge, with its trace identity proved. -/
theorem one_sub_scoreU_channelOf_le_diamondError {ε : Type*} [Fintype ε] [DecidableEq ε]
    [Nonempty ι] {U : Matrix κ ι ℂ} (hU : IsIsometry U) {F : Matrix (κ × ε) ι ℂ}
    (hF : IsIsometry F) : 1 - scoreU U (channelOf F) ≤ diamondError (channelOf F) (adConj U) :=
  one_sub_scoreU_le_diamondError hU _ (trace_choiMatrix_channelOf_eq_one hF)

end NLQCLean

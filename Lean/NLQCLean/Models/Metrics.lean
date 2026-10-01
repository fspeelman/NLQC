import NLQCLean.Models.ChannelAmplification
import NLQCLean.LinearAlgebra.TraceNormReindex

/-!
# The all-ancilla diamond norm and normalized diamond error

This is the supremum of amplified trace norms over every finite
ancilla and every input in the trace-norm unit ball. A proved coefficient
bound makes the supremum finite. Basis invariance covers arbitrary finite
ancilla types. No stabilization theorem or assumed metric bridge is used.
-/

namespace NLQCLean

open Matrix
open scoped Kronecker

variable {ι κ α : Type*} [Fintype ι] [Fintype κ] [Fintype α]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq α]

/-- All finite ancillary tests in the completely bounded trace norm. -/
def diamondTests (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) : Set ℝ :=
  {r | ∃ a : ℕ, ∃ X : Matrix (ι × Fin a) (ι × Fin a) ℂ,
    traceNorm X ≤ 1 ∧ r = traceNorm (amplify Φ (Fin a) X)}

/-- The ordinary diamond norm, before the normalized-error factor one half. -/
noncomputable def diamondNorm (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) : ℝ :=
  sSup (diamondTests Φ)

theorem zero_mem_diamondTests (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    0 ∈ diamondTests Φ := by
  refine ⟨0, 0, ?_, ?_⟩ <;> simp

theorem bddAbove_diamondTests (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    BddAbove (diamondTests Φ) := by
  refine ⟨channelCoefficientBound Φ, ?_⟩
  rintro _ ⟨a, X, hX, rfl⟩
  exact (traceNorm_amplify_le Φ X).trans (by
    simpa using mul_le_mul_of_nonneg_left hX (channelCoefficientBound_nonneg Φ))

theorem diamondNorm_nonneg (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) : 0 ≤ diamondNorm Φ :=
  le_csSup (bddAbove_diamondTests Φ) (zero_mem_diamondTests Φ)

theorem diamondNorm_le {Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ} {c : ℝ}
    (h : ∀ a : ℕ, ∀ X : Matrix (ι × Fin a) (ι × Fin a) ℂ,
      traceNorm X ≤ 1 → traceNorm (amplify Φ (Fin a) X) ≤ c) : diamondNorm Φ ≤ c := by
  apply csSup_le ⟨0, zero_mem_diamondTests Φ⟩
  rintro _ ⟨a, X, hX, rfl⟩
  exact h a X hX

theorem diamondNorm_le_coefficientBound (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    diamondNorm Φ ≤ channelCoefficientBound Φ := by
  apply diamondNorm_le
  intro a X hX
  exact (traceNorm_amplify_le Φ X).trans (by
    simpa using mul_le_mul_of_nonneg_left hX (channelCoefficientBound_nonneg Φ))

theorem traceNorm_amplify_fin_le_diamondNorm (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (a : ℕ) (X : Matrix (ι × Fin a) (ι × Fin a) ℂ) (hX : traceNorm X ≤ 1) :
    traceNorm (amplify Φ (Fin a) X) ≤ diamondNorm Φ :=
  le_csSup (bddAbove_diamondTests Φ) ⟨a, X, hX, rfl⟩

/-- All arbitrary finite ancilla types are tests in the same dimension-indexed norm. -/
theorem traceNorm_amplify_le_diamondNorm (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (X : Matrix (ι × α) (ι × α) ℂ) (hX : traceNorm X ≤ 1) :
    traceNorm (amplify Φ α X) ≤ diamondNorm Φ := by
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  have h := traceNorm_amplify_fin_le_diamondNorm Φ (Fintype.card α)
    (X.submatrix ((Equiv.refl ι).prodCongr e) ((Equiv.refl ι).prodCongr e))
    (by simpa only [traceNorm_submatrix_equiv] using hX)
  rw [amplify_submatrix_ancilla, traceNorm_submatrix_equiv] at h
  exact h

/-- The full induced-norm inequality, for inputs of any trace norm. -/
theorem traceNorm_amplify_le_diamondNorm_mul (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (X : Matrix (ι × α) (ι × α) ℂ) :
    traceNorm (amplify Φ α X) ≤ diamondNorm Φ * traceNorm X := by
  by_cases hX : traceNorm X = 0
  · have hz := (traceNorm_eq_zero_iff X).mp hX
    simp [hz]
  have hp : 0 < traceNorm X := lt_of_le_of_ne (traceNorm_nonneg X) (Ne.symm hX)
  let c : ℂ := ((traceNorm X)⁻¹ : ℝ)
  have hc : ‖c‖ = (traceNorm X)⁻¹ := by
    simp only [c, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  have htest : traceNorm (c • X) ≤ 1 := by
    rw [traceNorm_smul, hc, inv_mul_cancel₀ hX]
  have h := traceNorm_amplify_le_diamondNorm Φ (c • X) htest
  rw [map_smul, traceNorm_smul, hc] at h
  have h' := mul_le_mul_of_nonneg_left h hp.le
  rw [← mul_assoc, mul_inv_cancel₀ hX, one_mul] at h'
  simpa only [mul_comm] using h'

@[simp] theorem diamondNorm_zero : diamondNorm (0 : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) = 0 := by
  apply le_antisymm _ (diamondNorm_nonneg _)
  apply diamondNorm_le
  intro a X hX
  simp

theorem diamondNorm_add_le (Φ Ψ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    diamondNorm (Φ + Ψ) ≤ diamondNorm Φ + diamondNorm Ψ := by
  apply diamondNorm_le
  intro a X hX
  rw [amplify_add]
  exact (traceNorm_add_le _ _).trans (add_le_add
    (traceNorm_amplify_fin_le_diamondNorm Φ a X hX)
    (traceNorm_amplify_fin_le_diamondNorm Ψ a X hX))

theorem diamondNorm_smul_le (c : ℂ) (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    diamondNorm (c • Φ) ≤ ‖c‖ * diamondNorm Φ := by
  apply diamondNorm_le
  intro a X hX
  rw [amplify_smul, traceNorm_smul]
  exact mul_le_mul_of_nonneg_left (traceNorm_amplify_fin_le_diamondNorm Φ a X hX) (norm_nonneg c)

@[simp] theorem diamondNorm_smul (c : ℂ) (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    diamondNorm (c • Φ) = ‖c‖ * diamondNorm Φ := by
  by_cases hc : c = 0
  · simp [hc]
  apply le_antisymm (diamondNorm_smul_le c Φ)
  have h := diamondNorm_smul_le c⁻¹ (c • Φ)
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul, norm_inv] at h
  have h' := mul_le_mul_of_nonneg_left h (norm_nonneg c)
  rw [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hc), one_mul] at h'
  exact h'

@[simp] theorem diamondNorm_neg (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    diamondNorm (-Φ) = diamondNorm Φ := by
  have h := diamondNorm_smul (-1 : ℂ) Φ
  have hn : (-1 : ℂ) • Φ = -Φ := by
    ext X k l
    simp
  rw [hn] at h
  norm_num at h
  exact h

/-- Even a one-dimensional ancilla detects every nonzero map. -/
@[simp] theorem diamondNorm_eq_zero_iff (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    diamondNorm Φ = 0 ↔ Φ = 0 := by
  constructor
  · intro hΦ
    ext X k l
    have h := traceNorm_amplify_le_diamondNorm_mul Φ (X ⊗ₖ (1 : Matrix Unit Unit ℂ))
    rw [hΦ, zero_mul, amplify_kronecker] at h
    have hz : Φ X ⊗ₖ (1 : Matrix Unit Unit ℂ) = 0 :=
      (traceNorm_eq_zero_iff _).mp (le_antisymm h (traceNorm_nonneg _))
    have he := congrArg (fun A : Matrix (κ × Unit) (κ × Unit) ℂ => A (k, ()) (l, ())) hz
    simpa [Matrix.kroneckerMap_apply] using he
  · rintro rfl
    exact diamondNorm_zero

/-- Normalized diamond error is half the diamond norm of the map difference. -/
noncomputable def diamondError (Φ Ψ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) : ℝ :=
  diamondNorm (Φ - Ψ) / 2

theorem diamondError_nonneg (Φ Ψ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) : 0 ≤ diamondError Φ Ψ :=
  div_nonneg (diamondNorm_nonneg _) (by norm_num)

@[simp] theorem diamondError_eq_zero_iff (Φ Ψ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    diamondError Φ Ψ = 0 ↔ Φ = Ψ := by
  simp [diamondError, sub_eq_zero]

theorem diamondError_symm (Φ Ψ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    diamondError Φ Ψ = diamondError Ψ Φ := by
  unfold diamondError
  rw [← diamondNorm_neg (Φ - Ψ), neg_sub]

theorem diamondError_triangle (Φ Ψ Ω : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    diamondError Φ Ω ≤ diamondError Φ Ψ + diamondError Ψ Ω := by
  have h := diamondNorm_add_le (Φ - Ψ) (Ψ - Ω)
  rw [sub_add_sub_cancel] at h
  unfold diamondError
  linarith

end NLQCLean

import NLQCLean.Models.UnitaryScore
import NLQCLean.Models.ProjectiveScore

/-!
# The actual target scores as real-linear channel functionals

Both scores use their existing channel-level definitions and normalizations.
The projective score reads the same correct joint output label at both parties.
-/

namespace NLQCLean.ClassicalCommunication

attribute [local implicit_reducible] Matrix

variable {ι κ δ : Type*} [Fintype ι] [Fintype κ] [Fintype δ]
variable [DecidableEq ι] [DecidableEq δ]

/-- The existing normalized unitary Choi score, bundled over the real scalars. -/
noncomputable def unitaryScoreRealLinear (U : Matrix κ ι ℂ) :
    (Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) →ₗ[ℝ] ℝ where
  toFun Φ := scoreU U Φ
  map_add' Φ Ψ := by
    simpa [Fin.sum_univ_two] using
      scoreU_sum_smul U (fun _ : Fin 2 => (1 : ℝ)) ![Φ, Ψ]
  map_smul' c Φ := by
    change scoreU U ((c : ℂ) • Φ) = c * scoreU U Φ
    simpa only [Fintype.sum_unique] using
      scoreU_sum_smul U (fun _ : Unit => c) (fun _ => Φ)

@[simp] theorem unitaryScoreRealLinear_apply (U : Matrix κ ι ℂ)
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    unitaryScoreRealLinear U Φ = scoreU U Φ := rfl

/-- The actual two-sided PVM score, with both correct labels retained. -/
noncomputable def pvmScoreRealLinear (M : Matrix δ δ ℂ) :
    (Matrix δ δ ℂ →ₗ[ℂ] Matrix (δ × δ) (δ × δ) ℂ) →ₗ[ℝ] ℝ where
  toFun Φ := scorePVM M Φ
  map_add' Φ Ψ := by
    simpa [Fin.sum_univ_two] using
      scorePVM_sum_smul M (fun _ : Fin 2 => (1 : ℝ)) ![Φ, Ψ]
  map_smul' c Φ := by
    change scorePVM M ((c : ℂ) • Φ) = c * scorePVM M Φ
    simpa only [Fintype.sum_unique] using
      scorePVM_sum_smul M (fun _ : Unit => c) (fun _ => Φ)

omit [DecidableEq δ] in
@[simp] theorem pvmScoreRealLinear_apply (M : Matrix δ δ ℂ)
    (Φ : Matrix δ δ ℂ →ₗ[ℂ] Matrix (δ × δ) (δ × δ) ℂ) :
    pvmScoreRealLinear M Φ = scorePVM M Φ := rfl

end NLQCLean.ClassicalCommunication

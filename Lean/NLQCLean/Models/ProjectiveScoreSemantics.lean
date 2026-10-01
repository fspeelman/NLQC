import NLQCLean.Models.ProjectiveExactness
import NLQCLean.LinearAlgebra.RealCoordinates

/-!
# Phase invariance and continuity of the PVM score

Basis columns may have independent unit phases. The
score is jointly smooth in the target and the actual purified dilation,
without choosing garbage supports or restricting to exact protocols.
-/

namespace NLQCLean
open Matrix
open scoped Matrix.Norms.Frobenius

section Phases
variable {n δ : Type*} [Fintype n] [Fintype δ] [DecidableEq δ]

omit [Fintype n] in
/-- Independent unit column phases cancel in each rank-one projector. -/
theorem pvmProj_mul_diagonal_phase
    (M : Matrix n δ ℂ) (z : δ → ℂ) (hz : ∀ i, Complex.normSq (z i) = 1) (i : δ) :
    pvmProj (M * Matrix.diagonal z) i = pvmProj M i := by
  ext j k
  simp only [pvmProj, pureState_apply, pvmColumn_apply, Matrix.mul_diagonal, star_mul]
  calc
    _ = (z i * star (z i)) * (M j i * star (M k i)) := by ring
    _ = _ := by rw [← starRingEnd_apply, Complex.mul_conj, hz i]; simp

/-- Phase invariance is a channel-level identity, so also applies to finite
mixed resources before any component selection. -/
theorem scorePVM_mul_diagonal_phase
    (M : Matrix δ δ ℂ) (z : δ → ℂ) (hz : ∀ i, Complex.normSq (z i) = 1)
    (N : Matrix δ δ ℂ →ₗ[ℂ] Matrix (δ × δ) (δ × δ) ℂ) :
    scorePVM (M * Matrix.diagonal z) N = scorePVM M N := by
  simp only [scorePVM, pvmProj_mul_diagonal_phase M z hz]

variable {εA εB : Type*} [Fintype εA] [Fintype εB]

/-- The exact all-input task also depends only on the ordered projectors. -/
theorem twoSidedExact_mul_diagonal_phase_iff
    (F : Matrix ((δ × εA) × (δ × εB)) n ℂ)
    (M : Matrix n δ ℂ) (z : δ → ℂ) (hz : ∀ i, Complex.normSq (z i) = 1) :
    TwoSidedExact F (M * Matrix.diagonal z) ↔ TwoSidedExact F M := by
  constructor <;> intro h
  · exact ⟨by simpa only [pvmProj_mul_diagonal_phase M z hz] using h.agree, h.disagree⟩
  · exact ⟨by simpa only [pvmProj_mul_diagonal_phase M z hz] using h.agree, h.disagree⟩

omit [Fintype n] [Fintype εA] [Fintype εB] in
/-- The frozen convention is covariant: multiply each environment vector
by the column's phase while taking the adjoint of the new basis matrix. -/
theorem flag_mul_adjoint_phase
    (ω : δ → εA × εB → ℂ) (M : Matrix n δ ℂ)
    (z : δ → ℂ) (hz : ∀ i, Complex.normSq (z i) = 1) :
    flagIsometry (fun i => z i • ω i) * (M * Matrix.diagonal z)ᴴ =
      flagIsometry ω * Mᴴ := by
  classical
  ext p j
  rcases p with ⟨⟨a,eA⟩,⟨b,eB⟩⟩
  change outcomeBlock (flagIsometry (fun i => z i • ω i) * (M * Matrix.diagonal z)ᴴ)
      a b (eA,eB) j = outcomeBlock (flagIsometry ω * Mᴴ) a b (eA,eB) j
  rw [outcomeBlock_flag_mul_adjoint_apply, outcomeBlock_flag_mul_adjoint_apply]
  split_ifs
  · simp only [Pi.smul_apply, smul_eq_mul, Matrix.mul_diagonal, star_mul]
    calc
      _ = (z a * star (z a)) * (ω a (eA,eB) * star (M j a)) := by ring
      _ = _ := by rw [← starRingEnd_apply, Complex.mul_conj, hz a]; simp
  · rfl

end Phases

section Smoothness
variable {δ εA εB : Type*}
variable [Fintype δ] [Fintype εA] [Fintype εB]
variable [DecidableEq δ] [DecidableEq εA] [DecidableEq εB]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {r : WithTop ℕ∞}

omit [DecidableEq δ] [DecidableEq εA] [DecidableEq εB] in
/-- Smoothness in both the target and dilation uses the actual finite
sum of squared correct-block amplitudes, with the Frobenius topology. -/
theorem ContDiff.scorePVM_channelOf_joint
    {M : E → Matrix δ δ ℂ}
    {F : E → Matrix ((δ × εA) × (δ × εB)) δ ℂ}
    (hM : ContDiff ℝ r M) (hF : ContDiff ℝ r F) :
    ContDiff ℝ r (fun x => scorePVM (M x)
      (channelOf ((F x).submatrix (outputRegroup δ δ εA εB) id))) := by
  have heq : (fun x => scorePVM (M x)
      (channelOf ((F x).submatrix (outputRegroup δ δ εA εB) id))) =
      fun x => (Fintype.card δ : ℝ)⁻¹ * ∑ i, ∑ e : εA × εB,
        Complex.normSq ((F x * M x) ((i,e.1),(i,e.2)) i) := by
    funext x
    rw [scorePVM_channelOf_regrouped]
    rfl
  rw [heq]
  exact contDiff_const.mul (_root_.ContDiff.sum fun i _ =>
    _root_.ContDiff.sum fun e _ =>
      ContDiff.complexNormSq (ContDiff.matrixEntry (ContDiff.matrixMul hF hM)
        ((i,e.1),(i,e.2)) i))

omit [DecidableEq δ] [DecidableEq εA] [DecidableEq εB] in
/-- Joint continuity, including nonisometric ambient parameters. -/
theorem continuous_scorePVM_channelOf_joint :
    Continuous (fun x : Matrix δ δ ℂ × Matrix ((δ × εA) × (δ × εB)) δ ℂ =>
      scorePVM x.1 (channelOf (x.2.submatrix (outputRegroup δ δ εA εB) id))) :=
  (ContDiff.scorePVM_channelOf_joint (r := ⊤) contDiff_fst contDiff_snd).continuous

end Smoothness
end NLQCLean

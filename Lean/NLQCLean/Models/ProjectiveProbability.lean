import NLQCLean.Models.ProjectiveScore

/-!
# Actual joint PVM probabilities and score bounds

Both output labels are retained. Probabilities are those
of the existing purified isometry and are normalized on every density
matrix, with no bound on the finite private environments.
-/

namespace NLQCLean
open Matrix
open scoped ComplexOrder

section Probabilities
variable {n δ εA εB : Type*}
variable [Fintype n] [Fintype δ] [Fintype εA] [Fintype εB]
variable [DecidableEq n] [DecidableEq δ] [DecidableEq εA] [DecidableEq εB]

omit [Fintype δ] [DecidableEq n] [DecidableEq δ] [DecidableEq εA] [DecidableEq εB] in
/-- Discarding the environments gives the actual joint outcome probability,
for every input matrix and every pair of labels, including mismatches. -/
theorem channelOf_regrouped_diag
    (F : Matrix ((δ × εA) × (δ × εB)) n ℂ) (ρ : Matrix n n ℂ) (a b : δ) :
    channelOf (F.submatrix (outputRegroup δ δ εA εB) id) ρ (a, b) (a, b) =
      outcomeProb F ρ a b := by
  simp only [channelOf_apply, ptraceB_apply, outcomeProb, Matrix.trace, Matrix.diag_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply,
    outputRegroup_apply, outcomeBlock_apply, id_eq]

omit [DecidableEq n] [DecidableEq δ] [DecidableEq εA] [DecidableEq εB] in
/-- Summing all joint blocks is the trace of the full dilated output. -/
theorem sum_outcomeProb_eq_trace
    (F : Matrix ((δ × εA) × (δ × εB)) n ℂ) (ρ : Matrix n n ℂ) :
    ∑ ab : δ × δ, outcomeProb F ρ ab.1 ab.2 = (F * ρ * Fᴴ).trace := by
  simp only [outcomeProb, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, outcomeBlock_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

omit [DecidableEq δ] [DecidableEq εA] [DecidableEq εB] in
/-- Physical isometries preserve the total probability of every input state. -/
theorem sum_outcomeProb_eq_one
    {F : Matrix ((δ × εA) × (δ × εB)) n ℂ} (hF : IsIsometry F)
    {ρ : Matrix n n ℂ} (hρ : IsState ρ) :
    ∑ ab : δ × δ, outcomeProb F ρ ab.1 ab.2 = 1 := by
  rw [sum_outcomeProb_eq_trace, Matrix.trace_mul_cycle, hF.conjTranspose_mul_self,
    Matrix.one_mul, hρ.2]

omit [Fintype δ] [DecidableEq n] [DecidableEq δ] [DecidableEq εA] [DecidableEq εB] in
/-- Positivity also proves that the complex trace is real. -/
theorem outcomeProb_nonneg_complex
    (F : Matrix ((δ × εA) × (δ × εB)) n ℂ)
    {ρ : Matrix n n ℂ} (hρ : IsState ρ) (a b : δ) :
    0 ≤ outcomeProb F ρ a b :=
  (hρ.1.mul_mul_conjTranspose_same (outcomeBlock F a b)).trace_nonneg

omit [Fintype δ] [DecidableEq n] [DecidableEq δ] [DecidableEq εA] [DecidableEq εB] in
theorem outcomeProb_nonneg
    (F : Matrix ((δ × εA) × (δ × εB)) n ℂ)
    {ρ : Matrix n n ℂ} (hρ : IsState ρ) (a b : δ) :
    0 ≤ (outcomeProb F ρ a b).re :=
  (Complex.nonneg_iff.mp (outcomeProb_nonneg_complex F hρ a b)).1

omit [Fintype δ] [DecidableEq n] [DecidableEq δ] [DecidableEq εA] [DecidableEq εB] in
theorem outcomeProb_im_eq_zero
    (F : Matrix ((δ × εA) × (δ × εB)) n ℂ)
    {ρ : Matrix n n ℂ} (hρ : IsState ρ) (a b : δ) :
    (outcomeProb F ρ a b).im = 0 :=
  (Complex.nonneg_iff.mp (outcomeProb_nonneg_complex F hρ a b)).2.symm

omit [DecidableEq δ] [DecidableEq εA] [DecidableEq εB] in
theorem sum_outcomeProb_re_eq_one
    {F : Matrix ((δ × εA) × (δ × εB)) n ℂ} (hF : IsIsometry F)
    {ρ : Matrix n n ℂ} (hρ : IsState ρ) :
    ∑ ab : δ × δ, (outcomeProb F ρ ab.1 ab.2).re = 1 := by
  rw [← Complex.re_sum, sum_outcomeProb_eq_one hF hρ, Complex.one_re]

omit [DecidableEq δ] [DecidableEq εA] [DecidableEq εB] in
theorem outcomeProb_le_one
    {F : Matrix ((δ × εA) × (δ × εB)) n ℂ} (hF : IsIsometry F)
    {ρ : Matrix n n ℂ} (hρ : IsState ρ) (a b : δ) :
    (outcomeProb F ρ a b).re ≤ 1 := by
  rw [← sum_outcomeProb_re_eq_one hF hρ]
  exact Finset.single_le_sum (fun ab _ => outcomeProb_nonneg F hρ ab.1 ab.2)
    (Finset.mem_univ (a, b))

omit [DecidableEq δ] [DecidableEq εA] [DecidableEq εB] in
/-- Squared norm of each correct block is at most one on a unit input. -/
theorem sum_normSq_outcomeBlock_le_one
    {F : Matrix ((δ × εA) × (δ × εB)) n ℂ} (hF : IsIsometry F)
    {x : n → ℂ} (hx : IsUnitVector x) (a b : δ) :
    ∑ e, Complex.normSq ((outcomeBlock F a b *ᵥ x) e) ≤ 1 := by
  simpa only [outcomeProb_pureState, Complex.ofReal_re] using
    outcomeProb_le_one hF (isState_pureState hx) a b

omit [Fintype δ] [DecidableEq n] [DecidableEq δ] in
/-- The ideal effect probability in basis coordinates. -/
theorem trace_pvmProj_mul_eq_diag
    (M : Matrix n δ ℂ) (ρ : Matrix n n ℂ) (i : δ) :
    (pvmProj M i * ρ).trace = (Mᴴ * ρ * M) i i := by
  simp only [pvmProj, pureState_apply, pvmColumn_apply, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end Probabilities

section Score
variable {δ εA εB : Type*}
variable [Fintype δ] [Fintype εA] [Fintype εB]
variable [DecidableEq δ] [DecidableEq εA] [DecidableEq εB]

omit [DecidableEq εA] [DecidableEq εB] in
/-- The existing average basis score is at most one for a physical isometry
and an orthonormal target basis. Empty label types give score zero. -/
theorem scorePVM_channelOf_regrouped_le_one
    {F : Matrix ((δ × εA) × (δ × εB)) δ ℂ} {M : Matrix δ δ ℂ}
    (hF : IsIsometry F) (hM : IsIsometry M) :
    scorePVM M (channelOf (F.submatrix (outputRegroup δ δ εA εB) id)) ≤ 1 := by
  by_cases hD : Fintype.card δ = 0
  · simp [scorePVM, hD]
  rw [scorePVM_channelOf_regrouped]
  calc
    _ ≤ (Fintype.card δ : ℝ)⁻¹ * ∑ _i : δ, (1 : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
        sum_normSq_outcomeBlock_le_one hF (isUnitVector_pvmColumn hM i) i i)
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = 1 := by simp [hD]

omit [DecidableEq εA] [DecidableEq εB] in
/-- The joint-outcome score lies in the unit interval. -/
theorem scorePVM_channelOf_regrouped_mem_Icc
    {F : Matrix ((δ × εA) × (δ × εB)) δ ℂ} {M : Matrix δ δ ℂ}
    (hF : IsIsometry F) (hM : IsIsometry M) :
    scorePVM M (channelOf (F.submatrix (outputRegroup δ δ εA εB) id)) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨scorePVM_channelOf_regrouped_nonneg F M, scorePVM_channelOf_regrouped_le_one hF hM⟩

end Score
end NLQCLean

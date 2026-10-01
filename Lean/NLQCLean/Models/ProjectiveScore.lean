/-
The scalar score for the two-sided rank-one PVM task.
-/
import NLQCLean.Models.ProjectiveTask

/-!
# The projective-task score

`rem:scalar-approximation-input` (snapshot L1311-1340) packages approximate
correctness for an ordered rank-one PVM `Φ = (φ_i)_i` into the scalar

  `q_Φ = D⁻¹ ∑ i, Pr[(O_A, O_B) = (i, i) | φ_i]`.

This module defines that score on the induced channel.  Keeping the score at
channel level is essential: it makes the functional affine under a convex
mixture of resources, exactly as used at snapshot L1240-1244.  Taking the
real part only exposes the real-valued outcome probability.

The sum-of-squares identity below is the form needed by
`lem:residual-witnesses`: it identifies `q_Φ` with the average squared norm of
the correct diagonal blocks.  It also proves nonnegativity without assuming
exactness.  Finally,
`scorePVM_channelOf_regrouped_eq_one_of_twoSidedExact` checks that an exact
implementation of an orthonormal projective basis has score one.
-/

namespace NLQCLean

open Matrix

section Score

variable {δ εA εB : Type*}
variable [Fintype δ] [Fintype εA] [Fintype εB]
variable [DecidableEq δ] [DecidableEq εA] [DecidableEq εB]

/-- The projective-task scalar score `q_Φ` of
`rem:scalar-approximation-input` (snapshot L1319-1324), evaluated on the
induced channel `𝒩` with joint classical output `(O_A, O_B)`.

The normalization is by the number `D` of basis labels.  The definition also
makes sense for an empty label type (where it is zero); exact score one needs
the explicit `[Nonempty δ]` assumption used below. -/
noncomputable def scorePVM (M : Matrix δ δ ℂ)
    (𝒩 : Matrix δ δ ℂ →ₗ[ℂ] Matrix (δ × δ) (δ × δ) ℂ) : ℝ :=
  (Fintype.card δ : ℝ)⁻¹ *
    ∑ i, (𝒩 (pvmProj M i) (i, i) (i, i)).re

omit [DecidableEq δ] in
/-- `q_Φ` is real-affine in the channel.  This is the algebraic step behind
the component selection at snapshot L1240-1244. -/
theorem scorePVM_sum_smul {κ : Type*} [Fintype κ]
    (M : Matrix δ δ ℂ) (w : κ → ℝ)
    (𝒩 : κ → Matrix δ δ ℂ →ₗ[ℂ] Matrix (δ × δ) (δ × δ) ℂ) :
    scorePVM M (∑ k, ((w k : ℂ)) • 𝒩 k) =
      ∑ k, w k * scorePVM M (𝒩 k) := by
  simp only [scorePVM, LinearMap.sum_apply, LinearMap.smul_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Complex.re_sum,
    Complex.re_ofReal_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring_nf

omit [DecidableEq δ] in
/-- A real convex combination has a component whose PVM score is at least
the score of the mixture. -/
theorem exists_scorePVM_ge_of_convex {κ : Type*} [Fintype κ] [Nonempty κ]
    (M : Matrix δ δ ℂ) (w : κ → ℝ)
    (𝒩 : κ → Matrix δ δ ℂ →ₗ[ℂ] Matrix (δ × δ) (δ × δ) ℂ)
    (hw : ∀ k, 0 ≤ w k) (hsum : ∑ k, w k = 1) :
    ∃ k, scorePVM M (∑ j, ((w j : ℂ)) • 𝒩 j) ≤ scorePVM M (𝒩 k) := by
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image Finset.univ
    (fun j => scorePVM M (𝒩 j)) Finset.univ_nonempty
  refine ⟨k, ?_⟩
  rw [scorePVM_sum_smul]
  calc
    ∑ j, w j * scorePVM M (𝒩 j)
        ≤ ∑ j, w j * scorePVM M (𝒩 k) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
        (hk j (Finset.mem_univ j)) (hw j)
    _ = scorePVM M (𝒩 k) := by rw [← Finset.sum_mul, hsum, one_mul]

omit [DecidableEq δ] [DecidableEq εA] [DecidableEq εB] in
/-- Reading the diagonal output of the regrouped purified channel gives the
same correct-outcome probability as `outcomeProb` in the by-laboratory
grouping. -/
theorem channelOf_regrouped_pvmProj_diag
    (F : Matrix ((δ × εA) × (δ × εB)) δ ℂ) (M : Matrix δ δ ℂ) (i : δ) :
    channelOf
        (F.submatrix (outputRegroup δ δ εA εB) id)
        (pvmProj M i) (i, i) (i, i)
      = outcomeProb F (pureState (pvmColumn M i)) i i := by
  simp only [channelOf_apply, ptraceB_apply, outcomeProb, Matrix.trace,
    Matrix.diag_apply, pvmProj]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.submatrix_apply, outputRegroup_apply, outcomeBlock_apply,
    pureState_apply, id_eq]

omit [DecidableEq εA] [DecidableEq εB] in
omit [DecidableEq δ] in
/-- For a purified implementation, `q_Φ` is the average squared norm of the
correct diagonal outcome blocks on the target basis vectors.  This is the
PVM counterpart of `scoreU_channelOf` and the form consumed by
`lem:residual-witnesses`. -/
theorem scorePVM_channelOf_regrouped
    (F : Matrix ((δ × εA) × (δ × εB)) δ ℂ) (M : Matrix δ δ ℂ) :
    scorePVM M
        (channelOf (F.submatrix (outputRegroup δ δ εA εB) id)) =
      (Fintype.card δ : ℝ)⁻¹ *
        ∑ i, ∑ e, Complex.normSq
          ((outcomeBlock F i i *ᵥ pvmColumn M i) e) := by
  simp_rw [scorePVM, channelOf_regrouped_pvmProj_diag,
    outcomeProb_pureState, Complex.ofReal_re]

omit [DecidableEq εA] [DecidableEq εB] [DecidableEq δ] in
/-- The projective-task score of every purified implementation is
nonnegative. -/
theorem scorePVM_channelOf_regrouped_nonneg
    (F : Matrix ((δ × εA) × (δ × εB)) δ ℂ) (M : Matrix δ δ ℂ) :
    0 ≤ scorePVM M
      (channelOf (F.submatrix (outputRegroup δ δ εA εB) id)) := by
  rw [scorePVM_channelOf_regrouped]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun e _ => Complex.normSq_nonneg _)

omit [DecidableEq εA] [DecidableEq εB] in
/-- An exact implementation of an ordered
orthonormal rank-one PVM has projective-task score one. -/
theorem scorePVM_channelOf_regrouped_eq_one_of_twoSidedExact [Nonempty δ]
    {F : Matrix ((δ × εA) × (δ × εB)) δ ℂ} {M : Matrix δ δ ℂ}
    (hM : Mᴴ * M = 1) (hex : TwoSidedExact F M) :
    scorePVM M (channelOf
      (F.submatrix (outputRegroup δ δ εA εB) id)) = 1 := by
  rw [scorePVM_channelOf_regrouped]
  have hterm : ∀ i : δ,
      ∑ e, Complex.normSq ((outcomeBlock F i i *ᵥ pvmColumn M i) e) = 1 := by
    intro i
    have h := sum_normSq_diag_block hex (isUnitVector_pvmColumn hM i) i
    rw [pvmColumn_inner_self hM i, Complex.normSq_one] at h
    exact h
  simp [hterm, Fintype.card_ne_zero]

end Score

section MixedScore

variable {ιA ιB ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq εA] [DecidableEq εB]
variable {n : ℕ}

omit [DecidableEq εA] [DecidableEq εB] in
/-- The PVM score of a mixed-resource protocol is the weighted average of
the scores of its pure components.  This specializes `scorePVM_sum_smul` to
the honest channel decomposition in `MixedResource.mixedChannel`. -/
theorem MixedResource.scorePVM_mixedChannel
    (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix ((ιA × ιB) × εA) (κA × μB) ℂ)
    (DB : Matrix ((ιA × ιB) × εB) (κB × μA) ℂ)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    scorePVM M (m.mixedChannel VA VB DA DB) =
      ∑ k, m.weight k * scorePVM M
        (operationalChannel (m.component k) VA VB DA DB) := by
  rw [MixedResource.mixedChannel, scorePVM_sum_smul]

omit [DecidableEq εA] [DecidableEq εB] in
/-- Some pure component of a mixed-resource protocol has PVM score at least
that of the mixed protocol.  No nonemptiness assumption on `Fin n` is needed:
the convex weights summing to one supply a positive-weight component. -/
theorem MixedResource.exists_component_scorePVM_ge
    (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix ((ιA × ιB) × εA) (κA × μB) ℂ)
    (DB : Matrix ((ιA × ιB) × εB) (κB × μA) ℂ)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) :
    ∃ k, scorePVM M (m.mixedChannel VA VB DA DB) ≤
      scorePVM M (operationalChannel (m.component k) VA VB DA DB) := by
  have hpositive : ∃ k, 0 < m.weight k := by
    by_contra h
    push Not at h
    have hzero : ∀ k, m.weight k = 0 :=
      fun k => le_antisymm (h k) (m.weight_nonneg k)
    simpa [hzero] using m.weight_sum
  obtain ⟨k₀, _⟩ := hpositive
  let _ : Nonempty (Fin n) := ⟨k₀⟩
  rw [MixedResource.mixedChannel]
  exact exists_scorePVM_ge_of_convex M m.weight
    (fun k => operationalChannel (m.component k) VA VB DA DB)
    m.weight_nonneg m.weight_sum

end MixedScore

end NLQCLean

/-
Channels of purified isometries, Choi matrices, and the unitary target score.
-/
import NLQCLean.LinearAlgebra.Bipartite
import NLQCLean.LinearAlgebra.FrobeniusInner
import NLQCLean.LinearAlgebra.Isometry

/-!
# Channels and the scalar score

`rem:scalar-approximation-input` (snapshot L1311-1340) is the interface
between operational error and the approximation machinery: for a channel `𝒩`
with normalized Choi state `J(𝒩)`, the unitary target score is

  `q_U(𝒩) = ⟨⟨U| J(𝒩) |U⟩⟩`,

and the residual lemma `lem:residual-witnesses` is stated with this score in
its hypothesis. This module defines:

* `NLQCLean.channelOf F` — the operational channel `ρ ↦ Tr_E(F ρ F†)` of a
  purified isometry (snapshot L461-463);
* `NLQCLean.adConj U` — the target channel `Ad_U(ρ) = U ρ U†` (L474-475);
* `NLQCLean.choiMatrix 𝒩` — the normalized Choi matrix
  `J(𝒩) = (𝒩 ⊗ id)(|Ω_D⟩⟨Ω_D|)`, `|Ω_D⟩ = D^{-1/2} Σ_j |jj⟩` (L1178-1181);
* `NLQCLean.scoreU U 𝒩` — the score `q_U`;

and proves:

* `scoreU_adConj_self` — an exact implementation has score `1`;
* `scoreU_channelOf` — for a purified isometry the score is
  `Σ_e |D⁻¹⟨U, F_e⟩_F|²` over environment slices, the form in which
  `lem:residual-witnesses` consumes it (and which shows `q_U ≥ 0`).

`scoreU` takes the real part; for a completely positive `𝒩` the quadratic
form is real, so nothing is lost, and `scoreU_channelOf` proves this in the
case used downstream.

The PVM score `q_Φ`, which needs the outcome-label register structure, is
defined in `NLQCLean.Models.ProjectiveScore`. The operational metrics `Δ_◇`
and `Δ_pvm` (eq:diamond-error, eq:pvm-error) are defined in their dedicated
model modules.
-/

namespace NLQCLean

open Matrix

variable {ι κ ε : Type*} [Fintype ι] [Fintype κ] [Fintype ε]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq ε]

section Channels

/-- The operational channel of a purified isometry `F : H → K ⊗ E`: apply,
then discard the environment (snapshot L461-463). -/
def channelOf (F : Matrix (κ × ε) ι ℂ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ where
  toFun ρ := ptraceB κ ε (F * ρ * Fᴴ)
  map_add' ρ σ := by rw [Matrix.mul_add, Matrix.add_mul, map_add]
  map_smul' c ρ := by
    rw [Matrix.mul_smul, Matrix.smul_mul, map_smul]
    rfl

/-- The target channel `Ad_U(ρ) = U ρ U†` (snapshot L474-475), stated for a
general rectangular `U` so that isometric dilations are included. -/
def adConj (U : Matrix κ ι ℂ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ where
  toFun ρ := U * ρ * Uᴴ
  map_add' ρ σ := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c ρ := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] [DecidableEq ε] in
@[simp] theorem channelOf_apply (F : Matrix (κ × ε) ι ℂ) (ρ : Matrix ι ι ℂ) :
    channelOf F ρ = ptraceB κ ε (F * ρ * Fᴴ) := rfl

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
@[simp] theorem adConj_apply (U : Matrix κ ι ℂ) (ρ : Matrix ι ι ℂ) :
    adConj U ρ = U * ρ * Uᴴ := rfl

end Channels

section Choi

/-- The normalized Choi matrix `J(𝒩) = (𝒩 ⊗ id)(|Ω_D⟩⟨Ω_D|)`
(rem:scalar-approximation-input; `|Ω_D⟩` at snapshot L1178-1181).
Entrywise, `J p q = D⁻¹ · 𝒩(|p₂⟩⟨q₂|) p₁ q₁`. -/
noncomputable def choiMatrix (𝒩 : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    Matrix (κ × ι) (κ × ι) ℂ :=
  Matrix.of fun p q =>
    (Fintype.card ι : ℂ)⁻¹ * 𝒩 (Matrix.single p.2 q.2 1) p.1 q.1

omit [Fintype κ] [DecidableEq κ] in
@[simp] theorem choiMatrix_apply (𝒩 : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (p q : κ × ι) :
    choiMatrix 𝒩 p q
      = (Fintype.card ι : ℂ)⁻¹ * 𝒩 (Matrix.single p.2 q.2 1) p.1 q.1 := rfl

omit [Fintype κ] [DecidableEq κ] in
/-- The Choi matrix of `Ad_U` is the normalized rank-one projector onto the
vectorization of `U`. -/
theorem choiMatrix_adConj (U : Matrix κ ι ℂ) (p q : κ × ι) :
    choiMatrix (adConj U) p q
      = (Fintype.card ι : ℂ)⁻¹ * (U p.1 p.2 * star (U q.1 q.2)) := by
  simp only [choiMatrix_apply, adConj_apply]
  congr 1
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and]

omit [Fintype κ] [DecidableEq κ] [DecidableEq ε] in
/-- The Choi matrix of the channel of a purified isometry, as a sum over
environment slices. -/
theorem choiMatrix_channelOf (F : Matrix (κ × ε) ι ℂ) (p q : κ × ι) :
    choiMatrix (channelOf F) p q
      = (Fintype.card ι : ℂ)⁻¹
          * ∑ e, F (p.1, e) p.2 * star (F (q.1, e) q.2) := by
  simp only [choiMatrix_apply, channelOf_apply, ptraceB_apply]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  simp [Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply, ite_and]

end Choi

section Score

/-- The unitary target score `q_U(𝒩) = ⟨⟨U| J(𝒩) |U⟩⟩`
(rem:scalar-approximation-input, snapshot L1313-1318), with `|U⟩⟩` the
normalized Choi vector of `U`. -/
noncomputable def scoreU (U : Matrix κ ι ℂ) (𝒩 : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) : ℝ :=
  ((Fintype.card ι : ℂ)⁻¹
    * ∑ p, ∑ q, star (U p.1 p.2) * choiMatrix 𝒩 p q * U q.1 q.2).re

/-- The environment slice `F_e`: the matrix `(F_e)_{k,i} = F_{(k,e),i}`. -/
def sliceAt (F : Matrix (κ × ε) ι ℂ) (e : ε) : Matrix κ ι ℂ :=
  Matrix.of fun k i => F (k, e) i

omit [Fintype ι] [Fintype κ] [Fintype ε] [DecidableEq ι] [DecidableEq κ] [DecidableEq ε] in
@[simp] theorem sliceAt_apply (F : Matrix (κ × ε) ι ℂ) (e : ε) (k : κ) (i : ι) :
    sliceAt F e k i = F (k, e) i := rfl

omit [DecidableEq ι] [DecidableEq κ] in
/-- Bilinear rearrangement common to the two score computations:
`Σ_p Σ_q (c · a_p · b_q) = c · (Σ_p a_p) · (Σ_q b_q)`. -/
private theorem sum_sum_mul_mul (c : ℂ) (a b : (κ × ι) → ℂ) :
    ∑ p : κ × ι, ∑ q : κ × ι, c * a p * b q
      = c * (∑ p, a p) * (∑ q, b q) := by
  calc ∑ p : κ × ι, ∑ q : κ × ι, c * a p * b q
      = ∑ p : κ × ι, c * a p * ∑ q, b q :=
        Finset.sum_congr rfl fun p _ => (Finset.mul_sum _ _ _).symm
    _ = c * (∑ p, a p) * ∑ q, b q := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]

omit [DecidableEq κ] in
/-- An exact implementation of an isometric target has score one.
The input index must be nonempty:
over an empty input space the score degenerates to `0`. -/
theorem scoreU_adConj_self [Nonempty ι] {U : Matrix κ ι ℂ} (hU : IsIsometry U) :
    scoreU U (adConj U) = 1 := by
  have hD : (Fintype.card ι : ℂ) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have hsum : ∑ p : κ × ι, star (U p.1 p.2) * U p.1 p.2 = (Fintype.card ι : ℂ) := by
    rw [← frobInner_eq_sum_prod, frobInner_self_of_isometry hU]
  have key : ∑ p : κ × ι, ∑ q : κ × ι,
      star (U p.1 p.2) * choiMatrix (adConj U) p q * U q.1 q.2
      = (Fintype.card ι : ℂ) := by
    have step : ∀ p q : κ × ι,
        star (U p.1 p.2) * choiMatrix (adConj U) p q * U q.1 q.2
          = (Fintype.card ι : ℂ)⁻¹ * (star (U p.1 p.2) * U p.1 p.2)
              * (star (U q.1 q.2) * U q.1 q.2) := by
      intro p q
      rw [choiMatrix_adConj]
      ring
    simp only [step]
    rw [sum_sum_mul_mul, hsum, inv_mul_cancel₀ hD, one_mul]
  rw [scoreU, key, inv_mul_cancel₀ hD]
  simp

omit [DecidableEq κ] [DecidableEq ε] in
/-- **The slice identity**: for a purified isometry,
`q_U = Σ_e |D⁻¹ ⟨U, F_e⟩_F|²`.  This is the form in which
`lem:residual-witnesses` consumes the score, and it exhibits `q_U ≥ 0`. -/
theorem scoreU_channelOf (U : Matrix κ ι ℂ) (F : Matrix (κ × ε) ι ℂ) :
    scoreU U (channelOf F)
      = ∑ e, Complex.normSq
          ((Fintype.card ι : ℂ)⁻¹ * frobInner U (sliceAt F e)) := by
  set D : ℂ := (Fintype.card ι : ℂ) with hDdef
  set w : ε → ℂ := fun e => frobInner U (sliceAt F e) with hw
  have hwe : ∀ e, w e = ∑ p : κ × ι, star (U p.1 p.2) * F (p.1, e) p.2 := by
    intro e
    show frobInner U (sliceAt F e) = _
    rw [frobInner_eq_sum_prod]
    rfl
  have key : ∑ p : κ × ι, ∑ q : κ × ι,
      star (U p.1 p.2) * choiMatrix (channelOf F) p q * U q.1 q.2
      = D⁻¹ * ∑ e, ((Complex.normSq (w e) : ℝ) : ℂ) := by
    have step : ∀ p q : κ × ι,
        star (U p.1 p.2) * choiMatrix (channelOf F) p q * U q.1 q.2
          = ∑ e, D⁻¹ * (star (U p.1 p.2) * F (p.1, e) p.2)
              * (star (F (q.1, e) q.2) * U q.1 q.2) := by
      intro p q
      rw [choiMatrix_channelOf, ← hDdef, Finset.mul_sum, Finset.mul_sum,
        Finset.sum_mul]
      exact Finset.sum_congr rfl fun e _ => by ring
    simp only [step]
    have swap1 : ∀ p : κ × ι,
        (∑ q : κ × ι, ∑ e, D⁻¹ * (star (U p.1 p.2) * F (p.1, e) p.2)
            * (star (F (q.1, e) q.2) * U q.1 q.2))
          = ∑ e, ∑ q : κ × ι, D⁻¹ * (star (U p.1 p.2) * F (p.1, e) p.2)
            * (star (F (q.1, e) q.2) * U q.1 q.2) := fun p => Finset.sum_comm
    simp only [swap1]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [sum_sum_mul_mul, ← hwe]
    have hconj : ∑ q : κ × ι, star (F (q.1, e) q.2) * U q.1 q.2 = star (w e) := by
      rw [hwe, star_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [star_mul, star_star]
    rw [hconj, mul_assoc, ← starRingEnd_apply, Complex.mul_conj]
  rw [scoreU, key]
  have hr : D⁻¹ = ((((Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) := by
    rw [hDdef]
    push_cast
    ring
  rw [hr]
  rw [show ((((Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ)
        * (((((Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) * ∑ e, ((Complex.normSq (w e) : ℝ) : ℂ))
      = ((((Fintype.card ι : ℝ))⁻¹ * (((Fintype.card ι : ℝ))⁻¹
          * ∑ e, Complex.normSq (w e)) : ℝ) : ℂ) by push_cast; ring]
  rw [Complex.ofReal_re]
  simp only [Complex.normSq_mul, Complex.normSq_ofReal]
  rw [← Finset.mul_sum]
  ring

omit [DecidableEq κ] [DecidableEq ε] in
/-- The score of a purified-isometry channel is nonnegative. -/
theorem scoreU_channelOf_nonneg (U : Matrix κ ι ℂ) (F : Matrix (κ × ε) ι ℂ) :
    0 ≤ scoreU U (channelOf F) := by
  rw [scoreU_channelOf]
  exact Finset.sum_nonneg fun e _ => Complex.normSq_nonneg _

end Score

end NLQCLean

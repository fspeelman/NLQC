import NLQCLean.Models.Metrics
import NLQCLean.Models.UnitaryScore

/-!
# Normalized Choi states and the unitary test projection

These identities concern the existing normalized Choi matrix
and score. Isometric channels have trace-one positive Choi states; the
unitary target gives an orthogonal rank-one projection.
-/

namespace NLQCLean

open Matrix
open scoped ComplexOrder

variable {ι κ ε : Type*} [Fintype ι] [Fintype κ] [Fintype ε]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq ε]

omit [Fintype κ] [DecidableEq κ] in
@[simp] theorem choiMatrix_sub (Φ Ψ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    choiMatrix (Φ - Ψ) = choiMatrix Φ - choiMatrix Ψ := by
  ext p q
  simp [choiMatrix_apply, mul_sub]

omit [DecidableEq κ] in
/-- Choi trace respects finite real-weighted channel sums. -/
theorem trace_choiMatrix_sum_smul {a : Type*} [Fintype a] (w : a → ℝ)
    (Φ : a → Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    (choiMatrix (∑ k, (w k : ℂ) • Φ k)).trace =
      ∑ k, (w k : ℂ) * (choiMatrix (Φ k)).trace := by
  simp only [Matrix.trace, Matrix.diag, choiMatrix_sum_smul, Finset.mul_sum]
  exact Finset.sum_comm

omit [Fintype κ] [DecidableEq κ] in
/-- The target Choi matrix is a scaled vectorized outer product. -/
theorem choiMatrix_adConj_eq_outer (U : Matrix κ ι ℂ) :
    choiMatrix (adConj U) = (Fintype.card ι : ℂ)⁻¹ •
      Matrix.vecMulVec (fun p : κ × ι => U p.1 p.2) (star (fun p : κ × ι => U p.1 p.2)) := by
  ext p q
  rw [choiMatrix_adConj]
  rfl

omit [DecidableEq κ] in
theorem posSemidef_choiMatrix_adConj (U : Matrix κ ι ℂ) :
    (choiMatrix (adConj U)).PosSemidef := by
  rw [choiMatrix_adConj_eq_outer]
  exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by positivity)

omit [DecidableEq κ] in
theorem trace_choiMatrix_adConj (U : Matrix κ ι ℂ) :
    (choiMatrix (adConj U)).trace = (Fintype.card ι : ℂ)⁻¹ * frobInner U U := by
  rw [choiMatrix_adConj_eq_outer, Matrix.trace_smul, Matrix.trace_vecMulVec]
  simp [dotProduct, frobInner_eq_sum_prod, mul_comm]

omit [DecidableEq κ] in
theorem trace_choiMatrix_adConj_eq_one [Nonempty ι] {U : Matrix κ ι ℂ} (hU : IsIsometry U) :
    (choiMatrix (adConj U)).trace = 1 := by
  rw [trace_choiMatrix_adConj, frobInner_self_of_isometry hU]
  exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := ι))

omit [DecidableEq κ] in
/-- The normalized unitary Choi matrix is an orthogonal projection. -/
theorem choiMatrix_adConj_mul_self [Nonempty ι] {U : Matrix κ ι ℂ} (hU : IsIsometry U) :
    choiMatrix (adConj U) * choiMatrix (adConj U) = choiMatrix (adConj U) := by
  let v : κ × ι → ℂ := fun p => U p.1 p.2
  have hv : star v ⬝ᵥ v = (Fintype.card ι : ℂ) := by
    simpa only [dotProduct, Pi.star_apply, v, ← frobInner_eq_sum_prod] using
      frobInner_self_of_isometry hU
  have hd : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := ι)
  rw [choiMatrix_adConj_eq_outer]
  change ((Fintype.card ι : ℂ)⁻¹ • Matrix.vecMulVec v (star v)) *
      ((Fintype.card ι : ℂ)⁻¹ • Matrix.vecMulVec v (star v)) = _
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, hv]
  ext p q
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  rfl

omit [Fintype κ] [DecidableEq κ] [DecidableEq ε] in
/-- The environment slices give a Gram factorization for a channel's Choi matrix. -/
theorem choiMatrix_channelOf_eq_gram (F : Matrix (κ × ε) ι ℂ) :
    choiMatrix (channelOf F) = (Fintype.card ι : ℂ)⁻¹ •
      ((Matrix.of fun (p : κ × ι) (e : ε) => F (p.1, e) p.2) *
        (Matrix.of fun (p : κ × ι) (e : ε) => F (p.1, e) p.2)ᴴ) := by
  ext p q
  rw [choiMatrix_channelOf]
  rfl

omit [DecidableEq κ] [DecidableEq ε] in
theorem posSemidef_choiMatrix_channelOf (F : Matrix (κ × ε) ι ℂ) :
    (choiMatrix (channelOf F)).PosSemidef := by
  rw [choiMatrix_channelOf_eq_gram]
  exact (Matrix.posSemidef_self_mul_conjTranspose _).smul (by positivity)

omit [DecidableEq κ] [DecidableEq ε] in
theorem trace_choiMatrix_channelOf (F : Matrix (κ × ε) ι ℂ) :
    (choiMatrix (channelOf F)).trace = (Fintype.card ι : ℂ)⁻¹ * frobInner F F := by
  simp only [Matrix.trace, Matrix.diag, choiMatrix_channelOf, ← Finset.mul_sum,
    Fintype.sum_prod_type, frobInner]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  simp only [mul_comm]

omit [DecidableEq κ] [DecidableEq ε] in
theorem trace_choiMatrix_channelOf_eq_one [Nonempty ι] {F : Matrix (κ × ε) ι ℂ}
    (hF : IsIsometry F) : (choiMatrix (channelOf F)).trace = 1 := by
  rw [trace_choiMatrix_channelOf, frobInner_self_of_isometry hF]
  exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := ι))

omit [DecidableEq κ] in
/-- The existing score is exactly the expectation of the unitary Choi projection. -/
theorem scoreU_eq_re_trace_choi_mul (U : Matrix κ ι ℂ)
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    scoreU U Φ = (choiMatrix (adConj U) * choiMatrix Φ).trace.re := by
  unfold scoreU
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, choiMatrix_adConj,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

end NLQCLean

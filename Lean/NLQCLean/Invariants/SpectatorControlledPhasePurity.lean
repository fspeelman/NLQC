import NLQCLean.Exact.SpectatorControlledPhase
import NLQCLean.Exact.BitstringControlledPhase
import NLQCLean.Invariants.PurityReindex
import NLQCLean.Invariants.PurityEstimates

/-!
# Operator purity of a controlled phase with spectators

The diagonal swap trace depends on four local indices. For a gate acting only
on their first qubits, the four spectator sums contribute exactly the fourth
power of the spectator cardinality. The original normalization cancels this
factor and leaves the two-qubit controlled-phase purity.
-/

namespace NLQCLean

open Matrix
open scoped Kronecker

section DiagonalTrace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The realignment Gram trace of a diagonal bipartite matrix has four local
indices, as in the source operator-purity computation. -/
theorem realign_gram_sq_trace_diagonal (f : ι × ι → ℂ) :
    Matrix.trace ((realign (Matrix.diagonal f) * (realign (Matrix.diagonal f))ᴴ) *
      (realign (Matrix.diagonal f) * (realign (Matrix.diagonal f))ᴴ)) =
      ∑ p : (ι × ι) × (ι × ι),
        (f p.1 * f p.2) * star (f (swapFirstCopies p).1 * f (swapFirstCopies p).2) := by
  rw [realign_trace_eq_swap_trace]
  simp only [Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_conjTranspose]
  rw [mul_firstCopiesSwapMatrix, mul_firstCopiesSwapMatrix]
  simp only [Matrix.trace, Matrix.diag_apply]
  apply Finset.sum_congr rfl
  intro p _
  rw [Matrix.mul_apply, Finset.sum_eq_single_of_mem (swapFirstCopies p) (Finset.mem_univ _)]
  · simp [Matrix.submatrix_apply]
  · intro q _ hq
    simp [Matrix.submatrix_apply, Matrix.diagonal_apply, hq]

end DiagonalTrace

section SpectatorTrace

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Four spectator sums multiply the unnormalized diagonal trace by
`card σ ^ 4`, with no nonemptiness assumption. -/
theorem realign_gram_sq_trace_diagonal_spectators (f : Fin 2 × Fin 2 → ℂ) :
    Matrix.trace
      ((realign (Matrix.diagonal (fun p : (Fin 2 × σ) × (Fin 2 × σ) => f (p.1.1, p.2.1))) *
        (realign (Matrix.diagonal (fun p : (Fin 2 × σ) × (Fin 2 × σ) => f (p.1.1, p.2.1))))ᴴ) *
      (realign (Matrix.diagonal (fun p : (Fin 2 × σ) × (Fin 2 × σ) => f (p.1.1, p.2.1))) *
        (realign (Matrix.diagonal (fun p : (Fin 2 × σ) × (Fin 2 × σ) => f (p.1.1, p.2.1))))ᴴ)) =
      (Fintype.card σ : ℂ) ^ 4 *
        Matrix.trace ((realign (Matrix.diagonal f) * (realign (Matrix.diagonal f))ᴴ) *
          (realign (Matrix.diagonal f) * (realign (Matrix.diagonal f))ᴴ)) := by
  rw [realign_gram_sq_trace_diagonal, realign_gram_sq_trace_diagonal]
  simp only [swapFirstCopies, Fintype.sum_prod_type, Fin.sum_univ_two,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The original purity scalar is retained when the spectator factor is
extracted from the complex trace. -/
theorem purity_diagonal_spectators (c : ℝ) (f : Fin 2 × Fin 2 → ℂ) :
    purity c (Matrix.diagonal (fun p : (Fin 2 × σ) × (Fin 2 × σ) => f (p.1.1, p.2.1))) =
      (Fintype.card σ : ℝ) ^ 4 * purity c (Matrix.diagonal f) := by
  unfold purity
  rw [realign_gram_sq_trace_diagonal_spectators]
  have hcast : (Fintype.card σ : ℂ) ^ 4 = (((Fintype.card σ : ℝ) ^ 4 : ℝ) : ℂ) := by
    norm_cast
  rw [hcast]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- Adding identity spectators contributes only the spectator cardinality
factor to the unnormalized controlled-phase purity. -/
theorem purity_spectatorControlledPhase_scale (c θ : ℝ) :
    purity c (spectatorControlledPhase (σA := σ) (σB := σ) θ) =
      (Fintype.card σ : ℝ) ^ 4 * purity c (controlledPhase θ) := by
  simpa [spectatorControlledPhase, controlledPhase, qubitCornerPhase, Prod.mk.injEq] using
    purity_diagonal_spectators (σ := σ) c
      (fun q : Fin 2 × Fin 2 =>
        if q = (1, 1) then Complex.exp ((θ : ℂ) * Complex.I) else 1)

/-- The source normalized purity formula holds for every nonempty finite
spectator register. Its local dimension is `2 * card σ`. -/
theorem purity_spectatorControlledPhase [Nonempty σ] (θ : ℝ) :
    purity (((2 * (Fintype.card σ : ℝ)) ^ 4)⁻¹)
        (spectatorControlledPhase (σA := σ) (σB := σ) θ) =
      phasePurityValue θ := by
  have hcard : (Fintype.card σ : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hnormalization : (Fintype.card σ : ℝ) ^ 4 *
      (16 * ((2 * (Fintype.card σ : ℝ)) ^ 4)⁻¹) = 1 := by
    field_simp [hcard]
    ring
  have hscale (c : ℝ) : purity c (controlledPhase θ) =
      (16 * c) * purity (1 / 16) (controlledPhase θ) := by
    unfold purity
    ring
  rw [purity_spectatorControlledPhase_scale, hscale]
  rw [← mul_assoc, hnormalization, one_mul, purity_controlledPhase]
  rfl

end SpectatorTrace

/-- The source normalized purity formula on the actual `k + 1`-qubit
bitstring basis, including the two-qubit case `k = 0`. -/
theorem purity_bitstringControlledPhase (k : ℕ) (θ : ℝ) :
    purity ((((2 : ℝ) ^ (k + 1)) ^ 4)⁻¹) (bitstringControlledPhase k θ) =
      phasePurityValue θ := by
  classical
  have hdim : (2 : ℝ) ^ (k + 1) =
      2 * (Fintype.card (QubitString k) : ℝ) := by
    rw [card_qubitString, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
    ring
  rw [bitstringControlledPhase, purity_reindex_equiv, hdim]
  exact purity_spectatorControlledPhase (σ := QubitString k) θ

end NLQCLean

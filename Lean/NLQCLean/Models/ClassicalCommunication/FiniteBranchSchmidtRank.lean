import NLQCLean.Models.ClassicalCommunication.CoherentConversion
import NLQCLean.Approx.ChoiProjection
import NLQCLean.Models.ProtocolMetrics

/-!
# Schmidt rank and trace weights of finite classical branches

The classical outcomes and all Kraus and garbage labels are fixed in each
branch. Only the quantum messages cross the laboratory cut. Branch Choi
vectors remain unnormalized, and their squared norms sum to one.
-/

namespace NLQCLean.ClassicalCommunication.FiniteClassicalProtocol

open Matrix
open scoped Kronecker Matrix.Norms.Frobenius

variable {ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype σA] [Fintype σB] [Fintype ηA] [Fintype ηB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable (P : FiniteClassicalProtocol
  ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB)

/-- Fixing both outcomes and both instrument Kraus labels leaves an actual
unnormalized vector, whose laboratory rank charges only the quantum messages. -/
theorem rank_labChoiMatrix_branchAmplitude_le (x : σA) (y : σB) (e : ηA) (f : ηB) :
    (labChoiMatrix (P.branchAmplitude x y e f)).rank ≤
      schmidtRank P.resource * Fintype.card μA * Fintype.card μB := by
  unfold branchAmplitude NLQCLean.globalIsometry decoder encodedState
  apply (rank_labChoiMatrix_local_le (P.decA x y) (P.decB x y) _).trans
  apply (rank_labChoiMatrix_exchange_le _).trans
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
    ((rank_labChoiMatrix_local_le (P.instrumentA.operator x e)
      (P.instrumentB.operator y f) _).trans
      (rank_labChoiMatrix_insertResource_le P.resource)))

/-- The normalized logical-input Choi convention does not normalize an
individual branch's probability. Its rank still has the quantum-only cap. -/
theorem rank_normalizedLabChoiMatrix_branchAmplitude_le
    (x : σA) (y : σB) (e : ηA) (f : ηB) {K : ℕ}
    (hK : P.HasQuantumFootprint K) :
    (normalizedLabChoiMatrix (P.branchAmplitude x y e f)).rank ≤ K :=
  (rank_normalizedLabChoiMatrix_le _).trans
    ((P.rank_labChoiMatrix_branchAmplitude_le x y e f).trans
      ((hasFootprint_iff K P.resource).mp hK))

/-- The complete finite index also fixes the two discarded local environments. -/
abbrev BranchIndex := σA × (σB × (ηA × (ηB × (εA × εB))))

/-- The physical Kraus operator after conditioning on classical, instrument,
and discarded-garbage labels. No division by branch probability occurs. -/
def branchKraus (t : BranchIndex (σA := σA) (σB := σB)
    (ηA := ηA) (ηB := ηB) (εA := εA) (εB := εB)) :
    Matrix (ιA' × ιB') (ιA × ιB) ℂ :=
  fun a i => P.branchAmplitude t.1 t.2.1 t.2.2.1 t.2.2.2.1
    ((a.1, t.2.2.2.2.1), (a.2, t.2.2.2.2.2)) i

/-- Discarding the garbage is a local row/column selection on each branch's
Choi coefficient matrix and therefore cannot increase Schmidt rank. -/
theorem rank_normalizedLabChoiMatrix_branchKraus_le
    (t : BranchIndex (σA := σA) (σB := σB)
      (ηA := ηA) (ηB := ηB) (εA := εA) (εB := εB))
    {K : ℕ} (hK : P.HasQuantumFootprint K) :
    (normalizedLabChoiMatrix (P.branchKraus t)).rank ≤ K := by
  let A := normalizedLabChoiMatrix
    (P.branchAmplitude t.1 t.2.1 t.2.2.1 t.2.2.2.1)
  change (A.submatrix (fun a : ιA' × ιA => ((a.1, t.2.2.2.2.1), a.2))
    (fun b : ιB' × ιB => ((b.1, t.2.2.2.2.2), b.2))).rank ≤ K
  exact (Matrix.rank_submatrix_le A _ _).trans
    (P.rank_normalizedLabChoiMatrix_branchAmplitude_le _ _ _ _ hK)

/-- The operational channel is exactly the sum of the unnormalized physical
Kraus branches, including every discarded environment coordinate. -/
theorem operationalChannel_eq_sum_branchKraus :
    P.operationalChannel = ∑ t, adConj (P.branchKraus t) := by
  simp only [operationalChannel, channelOf_eq_sum_adConj,
    Fintype.sum_prod_type]
  rfl

/-- The normalized Choi trace of one Kraus operator equals its squared
coefficient-vector norm, including a zero-probability branch. -/
theorem re_trace_choiMatrix_adConj_eq_norm_sq_normalizedLabChoiMatrix
    (F : Matrix (ιA' × ιB') (ιA × ιB) ℂ) :
    (choiMatrix (adConj F)).trace.re = ‖normalizedLabChoiMatrix F‖ ^ 2 := by
  rw [trace_choiMatrix_adConj, frobInner_self_eq_norm_sq]
  have hcast : (Fintype.card (ιA × ιB) : ℂ)⁻¹ =
      ((Fintype.card (ιA × ιB) : ℝ)⁻¹ : ℂ) := by simp only [Complex.ofReal_natCast]
  rw [hcast, ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re,
    norm_normalizedLabChoiMatrix, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact (mul_comm _ _).trans (div_eq_mul_inv _ _).symm

variable [DecidableEq σA] [DecidableEq σB] [DecidableEq ηA] [DecidableEq ηB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB]

/-- All actual branches have total Choi trace one, without individually
renormalizing any classical outcome or assuming bounded private registers. -/
theorem sum_norm_sq_normalizedLabChoiMatrix_branchKraus [Nonempty ιA] [Nonempty ιB] :
    ∑ t, ‖normalizedLabChoiMatrix (P.branchKraus t)‖ ^ 2 = 1 := by
  have htrace : (choiMatrix P.operationalChannel).trace = 1 := by
    rw [← P.coherentProtocol_operationalChannel]
    exact P.coherentProtocol.trace_choiMatrix_eq_one
  have hsum : (choiMatrix P.operationalChannel).trace =
      ∑ t, (choiMatrix (adConj (P.branchKraus t))).trace := by
    rw [P.operationalChannel_eq_sum_branchKraus]
    simpa using trace_choiMatrix_sum_smul
      (fun _ : BranchIndex (σA := σA) (σB := σB)
        (ηA := ηA) (ηB := ηB) (εA := εA) (εB := εB) => (1 : ℝ))
      (fun t => adConj (P.branchKraus t))
  have hre := congrArg Complex.re (hsum.symm.trans htrace)
  simpa only [Complex.re_sum,
    re_trace_choiMatrix_adConj_eq_norm_sq_normalizedLabChoiMatrix,
    Complex.one_re] using hre

end NLQCLean.ClassicalCommunication.FiniteClassicalProtocol

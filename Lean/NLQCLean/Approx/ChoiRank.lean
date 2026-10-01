import NLQCLean.LinearAlgebra.SchmidtRank
import NLQCLean.Models.Resource

/-!
# Rank of a protocol's purified Choi vector

References stay in their own laboratories. The only
rank cost is the product of the two full message dimensions; all original
resource, retained, and environment registers may be arbitrary finite types.
-/

namespace NLQCLean

open Matrix
open scoped Kronecker

/-- Local maximally entangled input-reference pairs add no laboratory rank. -/
theorem rank_labChoiMatrix_insertResource_le {i j a b : Type*}
    [Fintype i] [Fintype j] [Fintype a] [Fintype b]
    [DecidableEq i] [DecidableEq j] (η : a × b → ℂ) :
    (labChoiMatrix (insertResource i j η)).rank ≤ schmidtRank η := by
  classical
  obtain ⟨J, B, _, hη⟩ := exists_isometry_rank_factorization (resourceMatrix η)
  let L : Matrix ((i × a) × i) (Fin (schmidtRank η)) ℂ :=
    fun x k ↦ if x.1.1 = x.2 then J x.1.2 k else 0
  let R : Matrix (Fin (schmidtRank η)) ((j × b) × j) ℂ :=
    fun k y ↦ if y.1.1 = y.2 then B k y.1.2 else 0
  have hfac : labChoiMatrix (insertResource i j η) = L * R := by
    ext x y
    have he := congrArg (fun N : Matrix a b ℂ ↦ N x.1.2 y.1.2) hη
    change η (x.1.2, y.1.2) = ∑ k, J x.1.2 k * B k y.1.2 at he
    change insertResource i j η (x.1, y.1) (x.2, y.2) = ∑ k, L x k * R k y
    by_cases hx : x.1.1 = x.2 <;> by_cases hy : y.1.1 = y.2 <;>
      simp [insertResource_apply, L, R, hx, hy, he]
    rfl
  rw [hfac]
  exact (Matrix.rank_mul_le_left L R).trans (by
    simpa using Matrix.rank_le_card_width L)

/-- The simultaneous exchange multiplies laboratory rank by at most the
product of both message dimensions, independently of the private registers. -/
theorem rank_labChoiMatrix_exchange_le {a b μ ν i j : Type*}
    [Fintype a] [Fintype b] [Fintype μ] [Fintype ν] [Fintype i] [Fintype j]
    [DecidableEq a] [DecidableEq b] [DecidableEq μ] [DecidableEq ν]
    (F : Matrix ((a × μ) × (b × ν)) (i × j) ℂ) :
    (labChoiMatrix (exchangeMatrix a μ b ν * F)).rank ≤
      (labChoiMatrix F).rank * Fintype.card μ * Fintype.card ν := by
  classical
  let C := labChoiMatrix F
  obtain ⟨J, B, _, hC⟩ := exists_isometry_rank_factorization C
  let L : Matrix ((a × ν) × i) ((Fin C.rank × μ) × ν) ℂ :=
    fun x k ↦ if x.1.2 = k.2 then J ((x.1.1, k.1.2), x.2) k.1.1 else 0
  let R : Matrix ((Fin C.rank × μ) × ν) ((b × μ) × j) ℂ :=
    fun k y ↦ if k.1.2 = y.1.2 then B k.1.1 ((y.1.1, k.2), y.2) else 0
  have hfac : labChoiMatrix (exchangeMatrix a μ b ν * F) = L * R := by
    ext x y
    rw [exchangeMatrix_mul]
    change C ((x.1.1, y.1.2), x.2) ((y.1.1, x.1.2), y.2) =
      ∑ k, L x k * R k y
    simp [L, R, Fintype.sum_prod_type, ite_mul, mul_ite, Finset.sum_ite_irrel]
    exact congrArg (fun N : Matrix ((a × μ) × i) ((b × ν) × j) ℂ ↦
      N ((x.1.1, y.1.2), x.2) ((y.1.1, x.1.2), y.2)) hC
  rw [hfac]
  exact (Matrix.rank_mul_le_left L R).trans (by
    simpa [C, Fintype.card_prod] using Matrix.rank_le_card_width L)

section Protocol

variable {ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB]

/-- R:protocolrank in the original arbitrary-finite-register model, before
normalization of the Choi vector. Only the resource rank is charged. -/
theorem PureProtocol.rank_labChoiMatrix_le
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB) :
    (labChoiMatrix P.globalIsometry).rank ≤
      schmidtRank P.resource * Fintype.card μA * Fintype.card μB := by
  apply (rank_labChoiMatrix_local_le P.decA P.decB _).trans
  apply (rank_labChoiMatrix_exchange_le _).trans
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
    ((rank_labChoiMatrix_local_le P.encA P.encB _).trans
      (rank_labChoiMatrix_insertResource_le P.resource)))

/-- A budget bounds the purified Choi laboratory rank, with both complete
outgoing messages charged by the existing footprint predicate. -/
theorem PureProtocol.rank_labChoiMatrix_le_of_hasFootprint
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB)
    {K : ℕ} (hK : NLQCLean.HasFootprint K P.resource μA μB) :
    (labChoiMatrix P.globalIsometry).rank ≤ K :=
  P.rank_labChoiMatrix_le.trans ((hasFootprint_iff K P.resource).mp hK)

/-- For the normalized purified Choi vector, its laboratory Schmidt
rank is at most the charged footprint. No bound on private dimensions occurs. -/
theorem PureProtocol.rank_normalizedLabChoiMatrix_le_of_hasFootprint
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB)
    {K : ℕ} (hK : NLQCLean.HasFootprint K P.resource μA μB) :
    (normalizedLabChoiMatrix P.globalIsometry).rank ≤ K :=
  (rank_normalizedLabChoiMatrix_le _).trans (P.rank_labChoiMatrix_le_of_hasFootprint hK)

end Protocol

end NLQCLean

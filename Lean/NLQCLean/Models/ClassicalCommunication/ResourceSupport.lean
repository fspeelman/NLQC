import NLQCLean.Models.ClassicalCommunication.FiniteProtocol
import NLQCLean.Models.ForwardCompression

/-!
# Rank-based resource supports for finite instruments

The resource inclusions are absorbed into the actual instrument operators.
All quantum message registers and all outcome-dependent decoders are kept.
The complete operational channel is unchanged, not merely its target score.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix
open scoped Kronecker

namespace FiniteKrausInstrument

variable {ι ι' κ σ ε : Type*}
variable [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype σ] [Fintype ε]
variable [DecidableEq ι] [DecidableEq ι']

/-- Restrict an instrument input along an actual isometric support inclusion. -/
def precomposeIsometry (I : FiniteKrausInstrument ι κ σ ε)
    (J : Matrix ι ι' ℂ) (hJ : IsIsometry J) : FiniteKrausInstrument ι' κ σ ε where
  operator := fun x e => I.operator x e * J
  normalized := by
    have he (x : σ) (e : ε) :
        (I.operator x e * J)ᴴ * (I.operator x e * J) =
          Jᴴ * ((I.operator x e)ᴴ * I.operator x e) * J := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    simp only [he, ← Matrix.sum_mul, ← Matrix.mul_sum, I.normalized,
      Matrix.mul_one, hJ.conjTranspose_mul_self]

@[simp] theorem precomposeIsometry_operator
    (I : FiniteKrausInstrument ι κ σ ε) (J : Matrix ι ι' ℂ) (hJ : IsIsometry J)
    (x : σ) (e : ε) : (I.precomposeIsometry J hJ).operator x e = I.operator x e * J := rfl

end FiniteKrausInstrument

namespace FiniteClassicalProtocol

variable {ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype σA] [Fintype σB] [Fintype ηA] [Fintype ηB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq σA] [DecidableEq σB] [DecidableEq ηA] [DecidableEq ηB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB]

omit [DecidableEq σA] [DecidableEq σB] [DecidableEq ηA] [DecidableEq ηB]
  [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB] in
/-- Actual rank-sized resource registers suffice for the entire finite
classical protocol, without increasing its quantum footprint. -/
theorem exists_resource_support_protocol
    (P : FiniteClassicalProtocol
      ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB) :
    ∃ Q : FiniteClassicalProtocol ιA ιB
        (Fin (schmidtRank P.resource)) (Fin (schmidtRank P.resource))
        κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB,
      P.operationalChannel = Q.operationalChannel ∧
      schmidtRank Q.resource ≤ schmidtRank P.resource ∧
      ∀ K, P.HasQuantumFootprint K → Q.HasQuantumFootprint K := by
  obtain ⟨JA, JB, γ, hJA, hJB, hγ, hresource⟩ :=
    exists_resource_support_factorization P.resource P.resource_unit
  let Q : FiniteClassicalProtocol ιA ιB
      (Fin (schmidtRank P.resource)) (Fin (schmidtRank P.resource))
      κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB :=
    { resource := γ
      resource_unit := hγ
      instrumentA := P.instrumentA.precomposeIsometry
        ((1 : Matrix ιA ιA ℂ) ⊗ₖ JA) (isIsometry_one.kronecker hJA)
      instrumentB := P.instrumentB.precomposeIsometry
        ((1 : Matrix ιB ιB ℂ) ⊗ₖ JB) (isIsometry_one.kronecker hJB)
      decA := P.decA
      decB := P.decB
      decA_isometry := P.decA_isometry
      decB_isometry := P.decB_isometry }
  have hrank : schmidtRank Q.resource ≤ schmidtRank P.resource := by
    simpa only [Fintype.card_fin] using schmidtRank_le_card_left Q.resource
  refine ⟨Q, ?_, hrank, ?_⟩
  · have hbranch (x : σA) (y : σB) (e : ηA) (f : ηB) :
        P.branchAmplitude x y e f = Q.branchAmplitude x y e f := by
      change NLQCLean.globalIsometry P.resource _ _ _ _ = _
      conv_lhs => rw [hresource]
      rw [globalIsometry_resource_inclusions]
      rfl
    simp only [operationalChannel, hbranch]
  · intro K hK
    change HasFootprint K Q.resource μA μB
    apply (hasFootprint_iff K Q.resource).mpr
    exact (Nat.mul_le_mul_right (Fintype.card μB)
      (Nat.mul_le_mul_right (Fintype.card μA) hrank)).trans
        ((hasFootprint_iff K P.resource).mp hK)

end FiniteClassicalProtocol
end NLQCLean.ClassicalCommunication

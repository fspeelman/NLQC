import NLQCLean.Models.ForwardCompression

/-!
# Exact encoder compression for PVM protocols

This variant of forward compression keeps the logical output and discarded
environment types unchanged.  It compresses only the pure resource supports
and the retained private encoder spaces, so equality holds already for the
global Stinespring isometries.
-/

namespace NLQCLean

open Matrix
open scoped Kronecker

section Assembly

variable {d : ℕ}
variable {oA oB ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype oA] [Fintype oB]
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq oA] [DecidableEq oB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

/-- Exact compression of the resource and retained encoder spaces, with the
logical outputs and environments left at their original types.  In particular,
this applies to the PVM specialization `oA = oB = Fin d × Fin d`.

The resource dimension is its exact Schmidt rank.  The retained private
dimensions are bounded by the input dimension, resource rank, and the complete
message dimension on the corresponding side. -/
theorem PureProtocol.exists_compressed_pvm_encoders
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB oA oB εA εB) :
    ∃ r kA kB : ℕ, r = schmidtRank P.resource ∧
      kA ≤ d * r * Fintype.card μA ∧ kB ≤ d * r * Fintype.card μB ∧
      ∃ Q : PureProtocol (Fin d) (Fin d) (Fin r) (Fin r) (Fin kA) (Fin kB)
        μA μB oA oB εA εB,
        P.globalIsometry = Q.globalIsometry ∧
          P.operationalChannel = Q.operationalChannel := by
  have hfac := exists_resource_support_factorization P.resource P.resource_unit
  generalize hr : schmidtRank P.resource = r at hfac
  obtain ⟨JA, JB, η, hJA, hJB, hη, hresource⟩ := hfac
  let VA0 := P.encA * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ JA)
  let VB0 := P.encB * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ JB)
  have hVA0 : IsIsometry VA0 := P.encA_isometry.mul (isIsometry_one.kronecker hJA)
  have hVB0 : IsIsometry VB0 := P.encB_isometry.mul (isIsometry_one.kronecker hJB)
  obtain ⟨kA, hkA, KA, VA, hKA, hA⟩ := exists_left_coefficient_factorization VA0
  obtain ⟨kB, hkB, KB, VB, hKB, hB⟩ := exists_left_coefficient_factorization VB0
  have hVA : IsIsometry VA :=
    ((hKA.kronecker isIsometry_one).mul_iff VA).mp (hA ▸ hVA0)
  have hVB : IsIsometry VB :=
    ((hKB.kronecker isIsometry_one).mul_iff VB).mp (hB ▸ hVB0)
  let DA0 := P.decA * (KA ⊗ₖ (1 : Matrix μB μB ℂ))
  let DB0 := P.decB * (KB ⊗ₖ (1 : Matrix μA μA ℂ))
  have hDA0 : IsIsometry DA0 := P.decA_isometry.mul (hKA.kronecker isIsometry_one)
  have hDB0 : IsIsometry DB0 := P.decB_isometry.mul (hKB.kronecker isIsometry_one)
  let Q : PureProtocol (Fin d) (Fin d) (Fin r) (Fin r) (Fin kA) (Fin kB)
      μA μB oA oB εA εB :=
    ⟨η, hη, VA, VB, hVA, hVB, DA0, DB0, hDA0, hDB0⟩
  have hF : P.globalIsometry = Q.globalIsometry := by
    change NLQCLean.globalIsometry P.resource P.encA P.encB P.decA P.decB =
      NLQCLean.globalIsometry η VA VB DA0 DB0
    rw [hresource, globalIsometry_resource_inclusions]
    change NLQCLean.globalIsometry η VA0 VB0 P.decA P.decB = _
    rw [hA, hB, globalIsometry_private_inclusions]
  refine ⟨r, kA, kB, rfl, ?_, ?_, Q, hF, ?_⟩
  · simpa only [Fintype.card_prod, Fintype.card_fin] using hkA
  · simpa only [Fintype.card_prod, Fintype.card_fin] using hkB
  · change channelOf
        (P.globalIsometry.submatrix (outputRegroup oA oB εA εB) id) =
      channelOf (Q.globalIsometry.submatrix (outputRegroup oA oB εA εB) id)
    rw [hF]

end Assembly

end NLQCLean

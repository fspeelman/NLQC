import NLQCLean.Models.ClassicalCommunication.ResourceSupport
import NLQCLean.Models.ClassicalCommunication.FiniteMixed
import NLQCLean.Models.ClassicalCommunication.TwoLevelDecoder

/-!
# Local logical-input restrictions of actual finite classical protocols

Input embeddings are absorbed into the original local instrument operators.
The original pure resource, both quantum messages, classical outcomes and
private systems are unchanged. The full operational channel is the actual
precomposed original channel, also for a common-map mixed resource.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix
open scoped Kronecker

attribute [local implicit_reducible] Matrix

section LogicalWiring

variable {ιA ιB τA τB ρA ρB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype τA] [Fintype τB]
variable [Fintype ρA] [Fintype ρB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq τA] [DecidableEq τB]
variable [DecidableEq ρA] [DecidableEq ρB]

/-- Local logical maps commute with the genuine by-laboratory resource
insertion. The resource is not projected, replaced or charged differently. -/
theorem insertResource_logical_precompose
    (EA : Matrix ιA τA ℂ) (EB : Matrix ιB τB ℂ) (γ : ρA × ρB → ℂ) :
    ((EA ⊗ₖ (1 : Matrix ρA ρA ℂ)) ⊗ₖ (EB ⊗ₖ (1 : Matrix ρB ρB ℂ))) *
        insertResource τA τB γ = insertResource ιA ιB γ * (EA ⊗ₖ EB) := by
  ext p q
  simp [Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type,
    Matrix.one_apply, insertResource_apply, mul_comm, mul_assoc]

variable {κA κB μA μB ιA' ιB' εA εB : Type*}
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]

omit [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB] in
/-- The actual unnormalized global branch amplitude restricts its logical
inputs by exactly the tensor product of the two local embeddings. -/
theorem globalIsometry_logical_precompose
    (EA : Matrix ιA τA ℂ) (EB : Matrix ιB τB ℂ) (γ : ρA × ρB → ℂ)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix (ιA' × εA) (κA × μB) ℂ)
    (DB : Matrix (ιB' × εB) (κB × μA) ℂ) :
    NLQCLean.globalIsometry γ
        (VA * (EA ⊗ₖ (1 : Matrix ρA ρA ℂ)))
        (VB * (EB ⊗ₖ (1 : Matrix ρB ρB ℂ))) DA DB =
      NLQCLean.globalIsometry γ VA VB DA DB * (EA ⊗ₖ EB) := by
  simp only [NLQCLean.globalIsometry_eq, Matrix.mul_kronecker_mul, Matrix.mul_assoc,
    insertResource_logical_precompose]

end LogicalWiring

namespace FiniteClassicalProtocol

variable {ιA ιB τA τB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype τA] [Fintype τB]
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype σA] [Fintype σB]
variable [Fintype ηA] [Fintype ηB] [Fintype ιA'] [Fintype ιB']
variable [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq τA] [DecidableEq τB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB]
variable (P : FiniteClassicalProtocol
  ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB)
variable (EA : Matrix ιA τA ℂ) (EB : Matrix ιB τB ℂ)
variable (hEA : IsIsometry EA) (hEB : IsIsometry EB)

/-- An actual protocol on locally embedded logical inputs, with every
original quantum message and classical alphabet kept unchanged. -/
def precomposeLogicalInputs : FiniteClassicalProtocol
    τA τB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB where
  resource := P.resource
  resource_unit := P.resource_unit
  instrumentA := P.instrumentA.precomposeIsometry
    (EA ⊗ₖ (1 : Matrix ρA ρA ℂ)) (hEA.kronecker isIsometry_one)
  instrumentB := P.instrumentB.precomposeIsometry
    (EB ⊗ₖ (1 : Matrix ρB ρB ℂ)) (hEB.kronecker isIsometry_one)
  decA := P.decA
  decB := P.decB
  decA_isometry := P.decA_isometry
  decB_isometry := P.decB_isometry

@[simp] theorem precomposeLogicalInputs_resource :
    (P.precomposeLogicalInputs EA EB hEA hEB).resource = P.resource := rfl

/-- Quantum charging is exactly the original charging, not a new support cap. -/
theorem precomposeLogicalInputs_hasQuantumFootprint_iff (K : ℕ) :
    (P.precomposeLogicalInputs EA EB hEA hEB).HasQuantumFootprint K ↔
      P.HasQuantumFootprint K := Iff.rfl

theorem precomposeLogicalInputs_branchAmplitude (x : σA) (y : σB) (e : ηA) (f : ηB) :
    (P.precomposeLogicalInputs EA EB hEA hEB).branchAmplitude x y e f =
      P.branchAmplitude x y e f * (EA ⊗ₖ EB) :=
  globalIsometry_logical_precompose EA EB P.resource
    (P.instrumentA.operator x e) (P.instrumentB.operator y f) (P.decA x y) (P.decB x y)

/-- The complete operational channel, before any score selection, is the
actual original channel precomposed with the isometric input channel. -/
theorem precomposeLogicalInputs_operationalChannel :
    (P.precomposeLogicalInputs EA EB hEA hEB).operationalChannel =
      P.operationalChannel.comp (adConj (EA ⊗ₖ EB)) := by
  have hrow (x : σA) (y : σB) (e : ηA) (f : ηB) :
      ((P.precomposeLogicalInputs EA EB hEA hEB).branchAmplitude x y e f).submatrix
          (outputRegroup ιA' ιB' εA εB) id =
        (P.branchAmplitude x y e f).submatrix (outputRegroup ιA' ιB' εA εB) id *
          (EA ⊗ₖ EB) := by
    rw [P.precomposeLogicalInputs_branchAmplitude EA EB hEA hEB]
    rw [Matrix.submatrix_mul _ _ _ id id Function.bijective_id, Matrix.submatrix_id_id]
  apply LinearMap.ext
  intro X
  simp only [operationalChannel, LinearMap.sum_apply, hrow, channelOf_mul_eq_comp,
    LinearMap.comp_apply]

/-- Restriction changes no common-map resource decomposition or component cap. -/
theorem precomposeLogicalInputs_hasMixedQuantumFootprint_iff {n : ℕ}
    (m : MixedResource ρA ρB n) (K : ℕ) :
    (P.precomposeLogicalInputs EA EB hEA hEB).HasMixedQuantumFootprint m K ↔
      P.HasMixedQuantumFootprint m K := Iff.rfl

theorem precomposeLogicalInputs_componentProtocol {n : ℕ}
    (m : MixedResource ρA ρB n) (k : Fin n) :
    (P.precomposeLogicalInputs EA EB hEA hEB).componentProtocol m k =
      (P.componentProtocol m k).precomposeLogicalInputs EA EB hEA hEB := rfl

/-- Common local instruments and decoders remain common across every mixed
component, and restriction commutes with the actual convex channel mixture. -/
theorem precomposeLogicalInputs_mixedOperationalChannel {n : ℕ}
    (m : MixedResource ρA ρB n) :
    (P.precomposeLogicalInputs EA EB hEA hEB).mixedOperationalChannel m =
      (P.mixedOperationalChannel m).comp (adConj (EA ⊗ₖ EB)) := by
  apply LinearMap.ext
  intro X
  simp only [mixedOperationalChannel, LinearMap.sum_apply, LinearMap.smul_apply,
    P.precomposeLogicalInputs_componentProtocol EA EB hEA hEB,
    precomposeLogicalInputs_operationalChannel, LinearMap.comp_apply]

end FiniteClassicalProtocol

end NLQCLean.ClassicalCommunication

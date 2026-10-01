import NLQCLean.Models.ClassicalCommunication.FiniteLogicalRestriction
import NLQCLean.Models.ClassicalCommunication.RectangularDiagonalRestriction

/-!
# Actual finite-protocol output restriction

Local isometric Stinespring output maps are absorbed into every original
decoder. Only private environments are enlarged: the resource, both quantum
messages, all classical outcomes and the encoding instruments stay fixed.
The whole operational channel is postcomposed by the actual local channels,
also for common-map mixed resources. Combining this construction with the
actual two-level input embeddings gives a rectangular diagonal restriction
with the same quantum footprint and no increase in normalized diamond error.
-/

namespace NLQCLean.ClassicalCommunication

open Matrix
open scoped Kronecker

attribute [local implicit_reducible] Matrix

/-- Compose physical output dilations, retaining the new and old environments. -/
def composeOutputStinespring {ι κ τ δ ε : Type*}
    [Fintype κ] [Fintype ε] [DecidableEq ε]
    (H : Matrix (τ × δ) κ ℂ) (D : Matrix (κ × ε) ι ℂ) :
    Matrix (τ × (δ × ε)) ι ℂ :=
  ((H ⊗ₖ (1 : Matrix ε ε ℂ)) * D).submatrix (Equiv.prodAssoc τ δ ε).symm id

theorem composeOutputStinespring_isometry {ι κ τ δ ε : Type*}
    [Fintype ι] [Fintype κ] [Fintype τ] [Fintype δ] [Fintype ε]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq ε]
    {H : Matrix (τ × δ) κ ℂ} {D : Matrix (κ × ε) ι ℂ}
    (hH : IsIsometry H) (hD : IsIsometry D) :
    IsIsometry (composeOutputStinespring H D) :=
  ((hH.kronecker isIsometry_one).mul hD).submatrix_equiv
    (Equiv.prodAssoc τ δ ε).symm (Equiv.refl ι)

/-- Every new Kraus slice is the product of the corresponding actual slices. -/
theorem sliceAt_composeOutputStinespring {ι κ τ δ ε : Type*}
    [Fintype κ] [Fintype ε] [DecidableEq ε]
    (H : Matrix (τ × δ) κ ℂ) (D : Matrix (κ × ε) ι ℂ) (u : δ) (e : ε) :
    sliceAt (composeOutputStinespring H D) (u, e) = sliceAt H u * sliceAt D e := by
  ext k i
  simp [composeOutputStinespring, sliceAt_apply, Matrix.submatrix_apply,
    Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply]

/-- Physical dilation composition is exactly channel composition on every matrix. -/
theorem channelOf_composeOutputStinespring {ι κ τ δ ε : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ] [Fintype ε] [DecidableEq ε]
    (H : Matrix (τ × δ) κ ℂ) (D : Matrix (κ × ε) ι ℂ) :
    channelOf (composeOutputStinespring H D) = (channelOf H).comp (channelOf D) := by
  rw [channelOf_eq_sum_adConj, channelOf_eq_sum_adConj, channelOf_eq_sum_adConj]
  apply LinearMap.ext
  intro X
  simp only [Fintype.sum_prod_type, LinearMap.sum_apply, LinearMap.comp_apply,
    sliceAt_composeOutputStinespring, adConj_mul_eq_comp, map_sum]
  exact Finset.sum_comm
    (f := fun (u : δ) (e : ε) => adConj (sliceAt H u) (adConj (sliceAt D e) X))

/-- A right-hand matrix acts before taking the genuine environment slice. -/
theorem sliceAt_mul_right {ι κ τ ε : Type*} [Fintype ι]
    (F : Matrix (κ × ε) ι ℂ) (A : Matrix ι τ ℂ) (e : ε) :
    sliceAt (F * A) e = sliceAt F e * A := rfl

/-- A regrouped tensor dilation has the corresponding tensor Kraus slices. -/
theorem sliceAt_regrouped_tensor {ιA ιB κA κB εA εB : Type*}
    (FA : Matrix (κA × εA) ιA ℂ) (FB : Matrix (κB × εB) ιB ℂ)
    (eA : εA) (eB : εB) :
    sliceAt ((FA ⊗ₖ FB).submatrix (outputRegroup κA κB εA εB) id) (eA, eB) =
      sliceAt FA eA ⊗ₖ sliceAt FB eB := rfl

section LocalOutputWiring

variable {ι κA κB oA oB τA τB δA δB εA εB : Type*}
variable [Fintype κA] [Fintype κB] [Fintype oA] [Fintype oB]
variable [Fintype εA] [Fintype εB]
variable [DecidableEq εA] [DecidableEq εB]

/-- Actual local output processing acts by the product of its two Kraus slices
on each old joint slice, without normalizing any branch. -/
theorem sliceAt_local_output_postcompose
    (HA : Matrix (τA × δA) oA ℂ) (HB : Matrix (τB × δB) oB ℂ)
    (DA : Matrix (oA × εA) κA ℂ) (DB : Matrix (oB × εB) κB ℂ)
    (Y : Matrix (κA × κB) ι ℂ) (uA : δA) (uB : δB) (eA : εA) (eB : εB) :
    sliceAt (((composeOutputStinespring HA DA ⊗ₖ composeOutputStinespring HB DB) * Y).submatrix
      (outputRegroup τA τB (δA × εA) (δB × εB)) id) ((uA, eA), (uB, eB)) =
        (sliceAt HA uA ⊗ₖ sliceAt HB uB) *
          sliceAt (((DA ⊗ₖ DB) * Y).submatrix (outputRegroup oA oB εA εB) id) (eA, eB) := by
  rw [Matrix.submatrix_mul _ _ _ id id Function.bijective_id, Matrix.submatrix_id_id,
    Matrix.submatrix_mul (DA ⊗ₖ DB) Y _ id id Function.bijective_id, Matrix.submatrix_id_id]
  rw [sliceAt_mul_right, sliceAt_mul_right, sliceAt_regrouped_tensor,
    sliceAt_regrouped_tensor, sliceAt_composeOutputStinespring,
    sliceAt_composeOutputStinespring, Matrix.mul_kronecker_mul, Matrix.mul_assoc]

variable [Fintype ι] [Fintype δA] [Fintype δB]
variable [DecidableEq oA] [DecidableEq oB]

/-- The whole unnormalized joint channel after local output maps is their
tensor channel postcomposed with the original unnormalized joint channel. -/
theorem channelOf_local_output_postcompose
    (HA : Matrix (τA × δA) oA ℂ) (HB : Matrix (τB × δB) oB ℂ)
    (DA : Matrix (oA × εA) κA ℂ) (DB : Matrix (oB × εB) κB ℂ)
    (Y : Matrix (κA × κB) ι ℂ) :
    channelOf (((composeOutputStinespring HA DA ⊗ₖ composeOutputStinespring HB DB) * Y).submatrix
      (outputRegroup τA τB (δA × εA) (δB × εB)) id) =
        (tensorChannels (channelOf HA) (channelOf HB)).comp
          (channelOf (((DA ⊗ₖ DB) * Y).submatrix (outputRegroup oA oB εA εB) id)) := by
  rw [tensorChannels_channelOf_regrouped, channelOf_eq_sum_adConj,
    channelOf_eq_sum_adConj, channelOf_eq_sum_adConj]
  apply LinearMap.ext
  intro X
  simp only [Fintype.sum_prod_type, LinearMap.sum_apply, LinearMap.comp_apply, map_sum,
    sliceAt_local_output_postcompose, sliceAt_regrouped_tensor, adConj_mul_eq_comp]
  let f (uA : δA) (eA : εA) (uB : δB) (eB : εB) :
      Matrix (τA × τB) (τA × τB) ℂ :=
    adConj (sliceAt HA uA ⊗ₖ sliceAt HB uB)
      (adConj (sliceAt (((DA ⊗ₖ DB) * Y).submatrix
        (outputRegroup oA oB εA εB) id) (eA, eB)) X)
  change (∑ uA, ∑ eA, ∑ uB, ∑ eB, f uA eA uB eB) =
    ∑ eA, ∑ eB, ∑ uA, ∑ uB, f uA eA uB eB
  calc
    _ = ∑ eA, ∑ uA, ∑ uB, ∑ eB, f uA eA uB eB :=
      Finset.sum_comm (f := fun uA eA => ∑ uB, ∑ eB, f uA eA uB eB)
    _ = ∑ eA, ∑ uA, ∑ eB, ∑ uB, f uA eA uB eB :=
      Finset.sum_congr rfl (fun eA _ => Finset.sum_congr rfl (fun uA _ =>
        Finset.sum_comm (f := fun uB eB => f uA eA uB eB)))
    _ = _ := Finset.sum_congr rfl (fun eA _ =>
      Finset.sum_comm (f := fun uA eB => ∑ uB, f uA eA uB eB))

end LocalOutputWiring

namespace FiniteClassicalProtocol

section OutputPostcomposition

variable {ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB τA τB δA δB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype σA] [Fintype σB] [Fintype ηA] [Fintype ηB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [Fintype τA] [Fintype τB] [Fintype δA] [Fintype δB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB]
variable (P : FiniteClassicalProtocol
  ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB ιA' ιB' εA εB)
variable (HA : Matrix (τA × δA) ιA' ℂ) (HB : Matrix (τB × δB) ιB' ℂ)
variable (hHA : IsIsometry HA) (hHB : IsIsometry HB)

/-- An actual output-postprocessed protocol, keeping all original resource,
quantum-message and classical registers; only private environments are enlarged. -/
def postcomposeLogicalOutputs : FiniteClassicalProtocol
    ιA ιB ρA ρB κA κB μA μB σA σB ηA ηB τA τB (δA × εA) (δB × εB) where
  resource := P.resource
  resource_unit := P.resource_unit
  instrumentA := P.instrumentA
  instrumentB := P.instrumentB
  decA := fun x y => composeOutputStinespring HA (P.decA x y)
  decB := fun x y => composeOutputStinespring HB (P.decB x y)
  decA_isometry := fun x y => composeOutputStinespring_isometry hHA (P.decA_isometry x y)
  decB_isometry := fun x y => composeOutputStinespring_isometry hHB (P.decB_isometry x y)

@[simp] theorem postcomposeLogicalOutputs_resource :
    (P.postcomposeLogicalOutputs HA HB hHA hHB).resource = P.resource := rfl

theorem postcomposeLogicalOutputs_instruments :
    (P.postcomposeLogicalOutputs HA HB hHA hHB).instrumentA = P.instrumentA ∧
    (P.postcomposeLogicalOutputs HA HB hHA hHB).instrumentB = P.instrumentB := ⟨rfl, rfl⟩

/-- Both original quantum messages and the exact resource rank are charged. -/
theorem postcomposeLogicalOutputs_hasQuantumFootprint_iff (K : ℕ) :
    (P.postcomposeLogicalOutputs HA HB hHA hHB).HasQuantumFootprint K ↔
      P.HasQuantumFootprint K := Iff.rfl

theorem postcomposeLogicalOutputs_branchChannel (x : σA) (y : σB) (e : ηA) (f : ηB) :
    channelOf (((P.postcomposeLogicalOutputs HA HB hHA hHB).branchAmplitude x y e f).submatrix
      (outputRegroup τA τB (δA × εA) (δB × εB)) id) =
        (tensorChannels (channelOf HA) (channelOf HB)).comp
          (channelOf ((P.branchAmplitude x y e f).submatrix
            (outputRegroup ιA' ιB' εA εB) id)) :=
  channelOf_local_output_postcompose HA HB (P.decA x y) (P.decB x y)
    (encodedState P.resource (P.instrumentA.operator x e) (P.instrumentB.operator y f))

/-- The complete operational channel equality holds before any score selection. -/
theorem postcomposeLogicalOutputs_operationalChannel :
    (P.postcomposeLogicalOutputs HA HB hHA hHB).operationalChannel =
      (tensorChannels (channelOf HA) (channelOf HB)).comp P.operationalChannel := by
  apply LinearMap.ext
  intro X
  simp only [operationalChannel, LinearMap.sum_apply,
    P.postcomposeLogicalOutputs_branchChannel HA HB hHA hHB, LinearMap.comp_apply, map_sum]

theorem postcomposeLogicalOutputs_hasMixedQuantumFootprint_iff {n : ℕ}
    (m : MixedResource ρA ρB n) (K : ℕ) :
    (P.postcomposeLogicalOutputs HA HB hHA hHB).HasMixedQuantumFootprint m K ↔
      P.HasMixedQuantumFootprint m K := Iff.rfl

theorem postcomposeLogicalOutputs_componentProtocol {n : ℕ}
    (m : MixedResource ρA ρB n) (k : Fin n) :
    (P.postcomposeLogicalOutputs HA HB hHA hHB).componentProtocol m k =
      (P.componentProtocol m k).postcomposeLogicalOutputs HA HB hHA hHB := rfl

/-- The same actual output maps are common to all components of the mixture. -/
theorem postcomposeLogicalOutputs_mixedOperationalChannel {n : ℕ}
    (m : MixedResource ρA ρB n) :
    (P.postcomposeLogicalOutputs HA HB hHA hHB).mixedOperationalChannel m =
      (tensorChannels (channelOf HA) (channelOf HB)).comp (P.mixedOperationalChannel m) := by
  apply LinearMap.ext
  intro X
  simp only [mixedOperationalChannel, LinearMap.sum_apply, LinearMap.smul_apply,
    P.postcomposeLogicalOutputs_componentProtocol HA HB hHA hHB,
    postcomposeLogicalOutputs_operationalChannel, LinearMap.comp_apply, map_sum, map_smul]

end OutputPostcomposition

section RectangularDiagonal

variable {dA dB : ℕ}
variable {ρA ρB κA κB μA μB σA σB ηA ηB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype σA] [Fintype σB]
variable [Fintype ηA] [Fintype ηB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]
variable (P : FiniteClassicalProtocol
  (Fin dA) (Fin dB) ρA ρB κA κB μA μB σA σB ηA ηB (Fin dA) (Fin dB) εA εB)
variable (hA : 2 ≤ dA) (hB : 2 ≤ dB) (θ : Fin dA × Fin dB → ℝ)

/-- A genuine finite protocol on two qubits obtained from the original
rectangular protocol by actual local input and corrected TP output maps. -/
noncomputable def restrictRectangularDiagonal : FiniteClassicalProtocol
    (Fin 2) (Fin 2) ρA ρB κA κB μA μB σA σB ηA ηB
      (Fin 2) (Fin 2) (Fin dA × εA) (Fin dB × εB) :=
  (P.precomposeLogicalInputs (twoLevelIsometry hA) (twoLevelIsometry hB)
    (twoLevelIsometry_isometry hA) (twoLevelIsometry_isometry hB)).postcomposeLogicalOutputs
      (rectangularDiagonalDecoderA hA hB θ) (rectangularDiagonalDecoderB hA hB θ)
        (rectangularDiagonalDecoderA_isometry hA hB θ)
        (rectangularDiagonalDecoderB_isometry hA hB θ)

@[simp] theorem restrictRectangularDiagonal_resource :
    (P.restrictRectangularDiagonal hA hB θ).resource = P.resource := rfl

/-- The actual original resource rank and both message dimensions are unchanged. -/
theorem restrictRectangularDiagonal_hasQuantumFootprint_iff (K : ℕ) :
    (P.restrictRectangularDiagonal hA hB θ).HasQuantumFootprint K ↔
      P.HasQuantumFootprint K := Iff.rfl

theorem restrictRectangularDiagonal_operationalChannel :
    (P.restrictRectangularDiagonal hA hB θ).operationalChannel =
      rectangularDiagonalRestrictedChannel hA hB θ P.operationalChannel := by
  rw [restrictRectangularDiagonal, postcomposeLogicalOutputs_operationalChannel,
    precomposeLogicalInputs_operationalChannel, ← rectangularDiagonalDecoderChannel_eq_local_tensor]
  rfl

/-- The full actual restricted protocol inherits the original normalized
diamond error to the rectangular target, with no score-only surrogate. -/
theorem restrictRectangularDiagonal_diamondError_le :
    diamondError (P.restrictRectangularDiagonal hA hB θ).operationalChannel
      (adConj (controlledPhase (rectangularAlternatingAngle hA hB θ))) ≤
        diamondError P.operationalChannel (adConj (rectangularDiagonalPhase θ)) := by
  rw [P.restrictRectangularDiagonal_operationalChannel hA hB θ]
  exact diamondError_rectangularDiagonalRestrictedChannel_target_le hA hB θ _

theorem restrictRectangularDiagonal_hasMixedQuantumFootprint_iff {n : ℕ}
    (m : MixedResource ρA ρB n) (K : ℕ) :
    (P.restrictRectangularDiagonal hA hB θ).HasMixedQuantumFootprint m K ↔
      P.HasMixedQuantumFootprint m K := Iff.rfl

theorem restrictRectangularDiagonal_componentProtocol {n : ℕ}
    (m : MixedResource ρA ρB n) (k : Fin n) :
    (P.restrictRectangularDiagonal hA hB θ).componentProtocol m k =
      (P.componentProtocol m k).restrictRectangularDiagonal hA hB θ := rfl

theorem restrictRectangularDiagonal_mixedOperationalChannel {n : ℕ}
    (m : MixedResource ρA ρB n) :
    (P.restrictRectangularDiagonal hA hB θ).mixedOperationalChannel m =
      rectangularDiagonalRestrictedChannel hA hB θ (P.mixedOperationalChannel m) := by
  rw [restrictRectangularDiagonal, postcomposeLogicalOutputs_mixedOperationalChannel,
    precomposeLogicalInputs_mixedOperationalChannel, ← rectangularDiagonalDecoderChannel_eq_local_tensor]
  rfl

/-- The same whole-channel contraction holds for the common-map finite mixture;
no component is selected and no support bound replaces its Schmidt-number cap. -/
theorem restrictRectangularDiagonal_mixedDiamondError_le {n : ℕ}
    (m : MixedResource ρA ρB n) :
    diamondError ((P.restrictRectangularDiagonal hA hB θ).mixedOperationalChannel m)
      (adConj (controlledPhase (rectangularAlternatingAngle hA hB θ))) ≤
        diamondError (P.mixedOperationalChannel m) (adConj (rectangularDiagonalPhase θ)) := by
  rw [P.restrictRectangularDiagonal_mixedOperationalChannel hA hB θ m]
  exact diamondError_rectangularDiagonalRestrictedChannel_target_le hA hB θ _

end RectangularDiagonal

end FiniteClassicalProtocol

end NLQCLean.ClassicalCommunication

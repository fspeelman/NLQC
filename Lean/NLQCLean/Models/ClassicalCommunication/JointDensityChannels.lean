import NLQCLean.Models.ClassicalCommunication.CPVectorInstrument
import NLQCLean.Models.ClassicalCommunication.ChannelUniformBound
import NLQCLean.Models.ClassicalCommunication.TensorChannels
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Joint channels of integrable instrument densities

The actual tensor operation is continuous and separately linear in its two
channel slots. A measurable final channel is composed with that tensor and
the fixed input insertion channel. The resulting real-linear score is
measurable; a uniform final-channel norm bound gives product integrability
and genuine conditional-score Fubini identities.
-/

namespace NLQCLean.ClassicalCommunication

open MeasureTheory Matrix Set
open scoped MeasureTheory Matrix.Norms.Elementwise

attribute [local implicit_reducible] Matrix

noncomputable section

noncomputable local instance jointMatrixNormedAddCommGroup
    {ν : Type*} [Fintype ν] : NormedAddCommGroup (Matrix ν ν ℂ) :=
  Matrix.normedAddCommGroup

noncomputable local instance jointMatrixTopologicalSpace
    {ν : Type*} [Fintype ν] : TopologicalSpace (Matrix ν ν ℂ) :=
  (jointMatrixNormedAddCommGroup (ν := ν)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

noncomputable local instance joint_density_channels_instance_1 {ν : Type*} [Fintype ν] :
    NormedSpace ℂ (Matrix ν ν ℂ) := Matrix.normedSpace

noncomputable local instance joint_density_channels_instance_2 {ν : Type*} [Fintype ν] :
    NormedSpace ℝ (Matrix ν ν ℂ) := Matrix.normedSpace

/-- Actual continuous complex-linear operations on finite matrix systems. -/
abbrev MatrixOperation (ι κ : Type*) [Fintype ι] [Fintype κ] :=
  Matrix ι ι ℂ →L[ℂ] Matrix κ κ ℂ

noncomputable local instance joint_density_channels_instance_3 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedAddCommGroup (MatrixOperation ι κ) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance joint_density_channels_instance_4 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedSpace ℂ (MatrixOperation ι κ) := ContinuousLinearMap.toNormedSpace

noncomputable local instance joint_density_channels_instance_5 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedSpace ℝ (MatrixOperation ι κ) := ContinuousLinearMap.toNormedSpace

local instance joint_density_channels_instance_6 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    MeasurableSpace (MatrixOperation ι κ) := borel (MatrixOperation ι κ)

local instance joint_density_channels_instance_7 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    BorelSpace (MatrixOperation ι κ) := ⟨rfl⟩

private def liftMatrixOperation {ι κ : Type*} [Fintype ι] [Fintype κ] :
    (Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) →ₗ[ℂ] MatrixOperation ι κ :=
  (LinearMap.toContinuousLinearMap :
    (Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) ≃ₗ[ℂ] MatrixOperation ι κ).toLinearMap

variable {ι κ τ υ : Type*} [Fintype ι] [Fintype κ] [Fintype τ] [Fintype υ]
variable [DecidableEq ι] [DecidableEq τ]

/-- The second continuous channel slot enters the actual tensor linearly. -/
def tensorContinuousChannelsRightLinear (Φ : MatrixOperation ι κ) :
    MatrixOperation τ υ →ₗ[ℂ] MatrixOperation (ι × τ) (κ × υ) :=
  (liftMatrixOperation.comp (tensorChannelsRightLinear Φ.toLinearMap)).comp
    (ContinuousLinearMap.coeLM ℂ)

/-- The continuous tensor channel is the checked matrix-unit tensor
operation, with only finite-dimensional continuity added. -/
def tensorContinuousChannels (Φ : MatrixOperation ι κ) (Ψ : MatrixOperation τ υ) :
    MatrixOperation (ι × τ) (κ × υ) :=
  tensorContinuousChannelsRightLinear Φ Ψ

@[simp] theorem tensorContinuousChannels_toLinearMap
    (Φ : MatrixOperation ι κ) (Ψ : MatrixOperation τ υ) :
    (tensorContinuousChannels Φ Ψ).toLinearMap =
      tensorChannels Φ.toLinearMap Ψ.toLinearMap := rfl

/-- The first continuous channel slot enters the actual tensor linearly. -/
def tensorContinuousChannelsLeftLinear (Ψ : MatrixOperation τ υ) :
    MatrixOperation ι κ →ₗ[ℂ] MatrixOperation (ι × τ) (κ × υ) :=
  (liftMatrixOperation.comp (tensorChannelsLeftLinear Ψ.toLinearMap)).comp
    (ContinuousLinearMap.coeLM ℂ)

private def tensorContinuousChannelsBilinearLinear :
    MatrixOperation ι κ →ₗ[ℂ]
      (MatrixOperation τ υ →L[ℂ] MatrixOperation (ι × τ) (κ × υ)) where
  toFun Φ := (tensorContinuousChannelsRightLinear Φ).toContinuousLinearMap
  map_add' Φ Φ' := by
    apply ContinuousLinearMap.ext
    intro Ψ
    exact (tensorContinuousChannelsLeftLinear Ψ).map_add Φ Φ'
  map_smul' c Φ := by
    apply ContinuousLinearMap.ext
    intro Ψ
    exact (tensorContinuousChannelsLeftLinear Ψ).map_smul c Φ

/-- The genuine tensor channel, bundled as a continuous complex bilinear map. -/
def tensorContinuousChannelsBilinear :
    MatrixOperation ι κ →L[ℂ]
      MatrixOperation τ υ →L[ℂ] MatrixOperation (ι × τ) (κ × υ) :=
  tensorContinuousChannelsBilinearLinear.toContinuousLinearMap

@[simp] theorem tensorContinuousChannelsBilinear_apply
    (Φ : MatrixOperation ι κ) (Ψ : MatrixOperation τ υ) :
    tensorContinuousChannelsBilinear Φ Ψ = tensorContinuousChannels Φ Ψ := rfl

/-- Real linearity in both slots uses the same actual complex tensor. -/
def tensorContinuousChannelsRealBilinear :
    MatrixOperation ι κ →L[ℝ]
      MatrixOperation τ υ →L[ℝ] MatrixOperation (ι × τ) (κ × υ) :=
  tensorContinuousChannelsBilinear.bilinearRestrictScalars ℝ

@[simp] theorem tensorContinuousChannelsRealBilinear_apply
    (Φ : MatrixOperation ι κ) (Ψ : MatrixOperation τ υ) :
    tensorContinuousChannelsRealBilinear Φ Ψ = tensorContinuousChannels Φ Ψ := rfl

/-- No Kraus factor is chosen measurably: actual CP operations tensor to
an actual CP operation using their finite Kraus representations only in proof. -/
theorem tensorContinuousChannels_completelyPositive [Nonempty ι] [Nonempty τ]
    [DecidableEq κ] [DecidableEq υ]
    (Φ : MatrixOperation ι κ) (Ψ : MatrixOperation τ υ)
    (hΦ : CompletelyPositive Φ.toLinearMap) (hΨ : CompletelyPositive Ψ.toLinearMap) :
    CompletelyPositive (tensorContinuousChannels Φ Ψ).toLinearMap := by
  obtain ⟨A, hA⟩ := exists_kraus_of_completelyPositive Φ.toLinearMap hΦ
  obtain ⟨B, hB⟩ := exists_kraus_of_completelyPositive Ψ.toLinearMap hΨ
  rw [tensorContinuousChannels_toLinearMap, hA, hB, tensorChannels_krausMap]
  exact completelyPositive_krausMap _

section DecodedChannels

variable {ν χ : Type*} [Fintype ν] [Fintype χ]

/-- Genuine postcomposition by the final channel and precomposition by the
fixed resource insertion; tensor output and input factor orders are unchanged. -/
def decodedTensorChannel (D : MatrixOperation (κ × υ) χ)
    (R : MatrixOperation ν (ι × τ))
    (Φ : MatrixOperation ι κ) (Ψ : MatrixOperation τ υ) : MatrixOperation ν χ :=
  D.comp ((tensorContinuousChannels Φ Ψ).comp R)

/-- The first local operation enters the decoded physical channel real-linearly. -/
def decodedTensorChannelLeftRealLinear
    (D : MatrixOperation (κ × υ) χ) (R : MatrixOperation ν (ι × τ))
    (Ψ : MatrixOperation τ υ) : MatrixOperation ι κ →ₗ[ℝ] MatrixOperation ν χ where
  toFun Φ := decodedTensorChannel D R Φ Ψ
  map_add' Φ Φ' := by
    change D.comp (((tensorContinuousChannelsLeftLinear Ψ) (Φ + Φ')).comp R) = _
    rw [map_add, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
    rfl
  map_smul' r Φ := by
    change D.comp (((tensorContinuousChannelsRealBilinear (ι := ι) (κ := κ)
      (τ := τ) (υ := υ)).flip Ψ (r • Φ)).comp R) = _
    rw [map_smul, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    rfl

/-- The second local operation enters the decoded physical channel real-linearly. -/
def decodedTensorChannelRightRealLinear
    (D : MatrixOperation (κ × υ) χ) (R : MatrixOperation ν (ι × τ))
    (Φ : MatrixOperation ι κ) : MatrixOperation τ υ →ₗ[ℝ] MatrixOperation ν χ where
  toFun Ψ := decodedTensorChannel D R Φ Ψ
  map_add' Ψ Ψ' := by
    change D.comp (((tensorContinuousChannelsRightLinear Φ) (Ψ + Ψ')).comp R) = _
    rw [map_add, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
    rfl
  map_smul' r Ψ := by
    change D.comp (((tensorContinuousChannelsRealBilinear (ι := ι) (κ := κ)
      (τ := τ) (υ := υ)) Φ (r • Ψ)).comp R) = _
    rw [map_smul, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    rfl

private theorem continuous_decodedTensorChannel
    (R : MatrixOperation ν (ι × τ)) :
    Continuous (fun p : MatrixOperation (κ × υ) χ ×
      (MatrixOperation ι κ × MatrixOperation τ υ) =>
        decodedTensorChannel p.1 R p.2.1 p.2.2) := by
  have hT : Continuous (fun p : MatrixOperation (κ × υ) χ ×
      (MatrixOperation ι κ × MatrixOperation τ υ) =>
        tensorContinuousChannels p.2.1 p.2.2) :=
    ((tensorContinuousChannelsBilinear (ι := ι) (κ := κ) (τ := τ) (υ := υ)).continuous.comp
      (continuous_fst.comp continuous_snd)).clm_apply
        (continuous_snd.comp continuous_snd)
  exact continuous_fst.clm_comp (hT.clm_comp_const R)

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The actual joint branch score, including both unnormalized CP densities. -/
def jointDensityChannelScore
    (S : MatrixOperation ν χ →L[ℝ] ℝ) (R : MatrixOperation ν (ι × τ))
    (D : α × β → MatrixOperation (κ × υ) χ)
    (Φ : α → MatrixOperation ι κ) (Ψ : β → MatrixOperation τ υ) : α × β → ℝ :=
  fun z => S (decodedTensorChannel (D z) R (Φ z.1) (Ψ z.2))

/-- Joint Borel final channels and measurable actual local densities give
a measurable score by genuine channel composition and tensor continuity. -/
theorem measurable_jointDensityChannelScore
    (S : MatrixOperation ν χ →L[ℝ] ℝ) (R : MatrixOperation ν (ι × τ))
    (D : α × β → MatrixOperation (κ × υ) χ)
    (Φ : α → MatrixOperation ι κ) (Ψ : β → MatrixOperation τ υ)
    (hD : Measurable D) (hΦ : Measurable Φ) (hΨ : Measurable Ψ) :
    Measurable (jointDensityChannelScore S R D Φ Ψ) :=
  (S.continuous.comp (continuous_decodedTensorChannel R)).measurable.comp
    (hD.prodMk ((hΦ.comp measurable_fst).prodMk (hΨ.comp measurable_snd)))

omit [MeasurableSpace α] [MeasurableSpace β] in
/-- A uniform bound on the genuine final channel gives an explicit product
domination bound for the actual joint density score. -/
theorem norm_jointDensityChannelScore_le
    (S : MatrixOperation ν χ →L[ℝ] ℝ) (R : MatrixOperation ν (ι × τ))
    (D : α × β → MatrixOperation (κ × υ) χ)
    (Φ : α → MatrixOperation ι κ) (Ψ : β → MatrixOperation τ υ)
    {B : ℝ} (hB : 0 ≤ B) (hD : ∀ z, ‖D z‖ ≤ B) (z : α × β) :
    ‖jointDensityChannelScore S R D Φ Ψ z‖ ≤
      (‖S‖ * B * ‖R‖ * ‖tensorContinuousChannelsBilinear (ι := ι) (κ := κ)
        (τ := τ) (υ := υ)‖) * ‖Φ z.1‖ * ‖Ψ z.2‖ := by
  have hT := (tensorContinuousChannelsBilinear (ι := ι) (κ := κ)
    (τ := τ) (υ := υ)).le_opNorm₂ (Φ z.1) (Ψ z.2)
  have hcomp := (tensorContinuousChannels (Φ z.1) (Ψ z.2)).opNorm_comp_le R
  have hpost := (D z).opNorm_comp_le
    ((tensorContinuousChannels (Φ z.1) (Ψ z.2)).comp R)
  calc
    ‖jointDensityChannelScore S R D Φ Ψ z‖ ≤
        ‖S‖ * ‖decodedTensorChannel (D z) R (Φ z.1) (Ψ z.2)‖ := S.le_opNorm _
    _ ≤ ‖S‖ * (B * ((‖tensorContinuousChannelsBilinear (ι := ι) (κ := κ)
        (τ := τ) (υ := υ)‖ * ‖Φ z.1‖ * ‖Ψ z.2‖) * ‖R‖)) := by
      gcongr
      exact hpost.trans (mul_le_mul (hD z) (hcomp.trans (mul_le_mul_of_nonneg_right hT
        (norm_nonneg R))) (norm_nonneg _) hB)
    _ = _ := by ring

/-- Integrability is proved from the two local RN densities and the actual
uniform final-channel bound; it is not a score field in an instrument model. -/
theorem integrable_jointDensityChannelScore_of_norm_bound
    (μ : Measure α) (νB : Measure β)
    [SFinite μ] [SFinite νB]
    (S : MatrixOperation ν χ →L[ℝ] ℝ) (R : MatrixOperation ν (ι × τ))
    (D : α × β → MatrixOperation (κ × υ) χ)
    (Φ : α → MatrixOperation ι κ) (Ψ : β → MatrixOperation τ υ)
    (hDmeas : Measurable D) (hΦmeas : Measurable Φ) (hΨmeas : Measurable Ψ)
    (hΦ : Integrable Φ μ) (hΨ : Integrable Ψ νB)
    {B : ℝ} (hB : 0 ≤ B) (hD : ∀ z, ‖D z‖ ≤ B) :
    Integrable (jointDensityChannelScore S R D Φ Ψ) (μ.prod νB) := by
  let A := ‖S‖ * B * ‖R‖ * ‖tensorContinuousChannelsBilinear (ι := ι) (κ := κ)
    (τ := τ) (υ := υ)‖
  have hmajorant : Integrable (fun z : α × β => A * (‖Φ z.1‖ * ‖Ψ z.2‖))
      (μ.prod νB) := (hΦ.norm.mul_prod hΨ.norm).const_mul A
  apply hmajorant.mono'
    (measurable_jointDensityChannelScore S R D Φ Ψ hDmeas hΦmeas hΨmeas).aestronglyMeasurable
  filter_upwards with z
  simpa only [A, mul_assoc] using norm_jointDensityChannelScore_le S R D Φ Ψ hB hD z

/-- For genuine CP and trace-preserving jointly Borel final channels, the
uniform bound is proved from their actual Kraus normalization. No decoder
bound or score-integrability field is supplied. -/
theorem integrable_jointDensityChannelScore_of_completelyPositive_tracePreserving
    [DecidableEq κ] [DecidableEq υ] [DecidableEq χ] [Nonempty κ] [Nonempty υ]
    (μ : Measure α) (νB : Measure β) [SFinite μ] [SFinite νB]
    (S : MatrixOperation ν χ →L[ℝ] ℝ) (R : MatrixOperation ν (ι × τ))
    (D : α × β → MatrixOperation (κ × υ) χ)
    (Φ : α → MatrixOperation ι κ) (Ψ : β → MatrixOperation τ υ)
    (hDmeas : Measurable D) (hΦmeas : Measurable Φ) (hΨmeas : Measurable Ψ)
    (hΦ : Integrable Φ μ) (hΨ : Integrable Ψ νB)
    (hDCP : ∀ z, CompletelyPositive (D z).toLinearMap)
    (hDTP : ∀ z, ∀ X, (D z X).trace = X.trace) :
    Integrable (jointDensityChannelScore S R D Φ Ψ) (μ.prod νB) := by
  obtain ⟨B, hB, hnorm⟩ := exists_completelyPositive_tracePreserving_norm_bound (κ × υ) χ
  exact integrable_jointDensityChannelScore_of_norm_bound μ νB S R D Φ Ψ
    hDmeas hΦmeas hΨmeas hΦ hΨ hB (fun z => hnorm (D z) (hDCP z) (hDTP z))

/-- Genuine conditional scores are integrable almost everywhere, their
mean is integrable, and Fubini identifies it with the actual joint score. -/
theorem jointDensityChannelScore_fubini
    (μ : Measure α) (νB : Measure β) [SFinite μ] [SFinite νB]
    (S : MatrixOperation ν χ →L[ℝ] ℝ) (R : MatrixOperation ν (ι × τ))
    (D : α × β → MatrixOperation (κ × υ) χ)
    (Φ : α → MatrixOperation ι κ) (Ψ : β → MatrixOperation τ υ)
    (h : Integrable (jointDensityChannelScore S R D Φ Ψ) (μ.prod νB)) :
    (∀ᵐ x ∂μ, Integrable (fun y => jointDensityChannelScore S R D Φ Ψ (x, y)) νB) ∧
      Integrable (fun x => ∫ y, jointDensityChannelScore S R D Φ Ψ (x, y) ∂νB) μ ∧
      (∫ z, jointDensityChannelScore S R D Φ Ψ z ∂μ.prod νB) =
        ∫ x, ∫ y, jointDensityChannelScore S R D Φ Ψ (x, y) ∂νB ∂μ :=
  ⟨h.prod_right_ae, h.integral_prod_left, integral_prod _ h⟩

end DecodedChannels

end

end NLQCLean.ClassicalCommunication

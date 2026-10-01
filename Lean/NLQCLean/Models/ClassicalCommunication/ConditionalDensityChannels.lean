import NLQCLean.Models.ClassicalCommunication.JointDensityChannels

/-!
# Conditional linear scores of actual instrument densities

The uniform norm bound for genuine CP trace-preserving final channels makes
every fixed-outcome section integrable, for every operation in the other
slot. Consequently the conditional integral is an actual real-linear score
functional. Its definition does not rely on an almost-everywhere choice of
sections or assume score integrability as a model field.
-/

namespace NLQCLean.ClassicalCommunication

open MeasureTheory Matrix
open scoped MeasureTheory Matrix.Norms.Elementwise

attribute [local implicit_reducible] Matrix

noncomputable section

noncomputable local instance conditionalMatrixNormedAddCommGroup
    {ν : Type*} [Fintype ν] : NormedAddCommGroup (Matrix ν ν ℂ) :=
  Matrix.normedAddCommGroup

noncomputable local instance conditionalMatrixTopologicalSpace
    {ν : Type*} [Fintype ν] : TopologicalSpace (Matrix ν ν ℂ) :=
  (conditionalMatrixNormedAddCommGroup (ν := ν)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

noncomputable local instance conditional_density_channels_instance_1 {ν : Type*} [Fintype ν] :
    NormedSpace ℂ (Matrix ν ν ℂ) := Matrix.normedSpace

noncomputable local instance conditional_density_channels_instance_2 {ν : Type*} [Fintype ν] :
    NormedSpace ℝ (Matrix ν ν ℂ) := Matrix.normedSpace

noncomputable local instance conditional_density_channels_instance_3 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedAddCommGroup (MatrixOperation ι κ) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance conditional_density_channels_instance_4 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedSpace ℂ (MatrixOperation ι κ) := ContinuousLinearMap.toNormedSpace

noncomputable local instance conditional_density_channels_instance_5 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedSpace ℝ (MatrixOperation ι κ) := ContinuousLinearMap.toNormedSpace

local instance conditional_density_channels_instance_6 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    MeasurableSpace (MatrixOperation ι κ) := borel (MatrixOperation ι κ)

local instance conditional_density_channels_instance_7 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    BorelSpace (MatrixOperation ι κ) := ⟨rfl⟩

variable {ι κ τ υ ν χ α β : Type*}
variable [Fintype ι] [Fintype κ] [Fintype τ] [Fintype υ] [Fintype ν] [Fintype χ]
variable [DecidableEq ι] [DecidableEq τ]
variable [MeasurableSpace α] [MeasurableSpace β]

/-- Uniform domination proves integrability for every fixed first outcome
and every operation in the first slot, not just for almost every outcome. -/
theorem integrable_conditionalDensityChannelScoreLeft_of_norm_bound
    (νB : Measure β) (S : MatrixOperation ν χ →L[ℝ] ℝ)
    (R : MatrixOperation ν (ι × τ)) (D : α × β → MatrixOperation (κ × υ) χ)
    (Ψ : β → MatrixOperation τ υ)
    (hDmeas : Measurable D) (hΨmeas : Measurable Ψ) (hΨ : Integrable Ψ νB)
    {B : ℝ} (hB : 0 ≤ B) (hD : ∀ z, ‖D z‖ ≤ B)
    (x : α) (A : MatrixOperation ι κ) :
    Integrable (fun y => S (decodedTensorChannel (D (x, y)) R A (Ψ y))) νB := by
  let C := (‖S‖ * B * ‖R‖ * ‖tensorContinuousChannelsBilinear (ι := ι) (κ := κ)
    (τ := τ) (υ := υ)‖) * ‖A‖
  have hmeas : Measurable (fun y => S (decodedTensorChannel (D (x, y)) R A (Ψ y))) :=
    (measurable_jointDensityChannelScore S R D (fun _ => A) Ψ
      hDmeas measurable_const hΨmeas).comp measurable_prodMk_left
  apply (hΨ.norm.const_mul C).mono' hmeas.aestronglyMeasurable
  filter_upwards with y
  exact norm_jointDensityChannelScore_le S R D (fun _ => A) Ψ hB hD (x, y)

/-- The same every-outcome integrability follows from actual complete
positivity and trace preservation, using the proved finite-system bound. -/
theorem integrable_conditionalDensityChannelScoreLeft
    [DecidableEq κ] [DecidableEq υ] [DecidableEq χ] [Nonempty κ] [Nonempty υ]
    (νB : Measure β) (S : MatrixOperation ν χ →L[ℝ] ℝ)
    (R : MatrixOperation ν (ι × τ)) (D : α × β → MatrixOperation (κ × υ) χ)
    (Ψ : β → MatrixOperation τ υ)
    (hDmeas : Measurable D) (hΨmeas : Measurable Ψ) (hΨ : Integrable Ψ νB)
    (hDCP : ∀ z, CompletelyPositive (D z).toLinearMap)
    (hDTP : ∀ z, ∀ X, (D z X).trace = X.trace)
    (x : α) (A : MatrixOperation ι κ) :
    Integrable (fun y => S (decodedTensorChannel (D (x, y)) R A (Ψ y))) νB := by
  obtain ⟨B, hB, hnorm⟩ := exists_completelyPositive_tracePreserving_norm_bound (κ × υ) χ
  exact integrable_conditionalDensityChannelScoreLeft_of_norm_bound νB S R D Ψ
    hDmeas hΨmeas hΨ hB (fun z => hnorm (D z) (hDCP z) (hDTP z)) x A

/-- The genuine conditional integral is real-linear in the first operation
slot. Every section used to prove additivity is actually integrable. -/
def conditionalDensityChannelScoreLeft
    [DecidableEq κ] [DecidableEq υ] [DecidableEq χ] [Nonempty κ] [Nonempty υ]
    (νB : Measure β) (S : MatrixOperation ν χ →L[ℝ] ℝ)
    (R : MatrixOperation ν (ι × τ)) (D : α × β → MatrixOperation (κ × υ) χ)
    (Ψ : β → MatrixOperation τ υ)
    (hDmeas : Measurable D) (hΨmeas : Measurable Ψ) (hΨ : Integrable Ψ νB)
    (hDCP : ∀ z, CompletelyPositive (D z).toLinearMap)
    (hDTP : ∀ z, ∀ X, (D z X).trace = X.trace)
    (x : α) : MatrixOperation ι κ →ₗ[ℝ] ℝ where
  toFun A := ∫ y, S (decodedTensorChannel (D (x, y)) R A (Ψ y)) ∂νB
  map_add' A A' := by
    have heq : (fun y => S (decodedTensorChannel (D (x, y)) R (A + A') (Ψ y))) =
        fun y => S (decodedTensorChannel (D (x, y)) R A (Ψ y)) +
          S (decodedTensorChannel (D (x, y)) R A' (Ψ y)) := by
      funext y
      change S ((decodedTensorChannelLeftRealLinear (D (x, y)) R (Ψ y)) (A + A')) = _
      rw [map_add, map_add]
      rfl
    rw [heq, integral_add
      (integrable_conditionalDensityChannelScoreLeft νB S R D Ψ
        hDmeas hΨmeas hΨ hDCP hDTP x A)
      (integrable_conditionalDensityChannelScoreLeft νB S R D Ψ
        hDmeas hΨmeas hΨ hDCP hDTP x A')]
  map_smul' r A := by
    have heq : (fun y => S (decodedTensorChannel (D (x, y)) R (r • A) (Ψ y))) =
        fun y => r • S (decodedTensorChannel (D (x, y)) R A (Ψ y)) := by
      funext y
      change S ((decodedTensorChannelLeftRealLinear (D (x, y)) R (Ψ y)) (r • A)) = _
      rw [map_smul, map_smul]
      rfl
    rw [heq, integral_smul]
    rfl

/-- Evaluation is the actual conditional integral, with no chosen
almost-everywhere representative of a conditional expectation. -/
@[simp] theorem conditionalDensityChannelScoreLeft_apply
    [DecidableEq κ] [DecidableEq υ] [DecidableEq χ] [Nonempty κ] [Nonempty υ]
    (νB : Measure β) (S : MatrixOperation ν χ →L[ℝ] ℝ)
    (R : MatrixOperation ν (ι × τ)) (D : α × β → MatrixOperation (κ × υ) χ)
    (Ψ : β → MatrixOperation τ υ)
    (hDmeas : Measurable D) (hΨmeas : Measurable Ψ) (hΨ : Integrable Ψ νB)
    (hDCP : ∀ z, CompletelyPositive (D z).toLinearMap)
    (hDTP : ∀ z, ∀ X, (D z X).trace = X.trace)
    (x : α) (A : MatrixOperation ι κ) :
    conditionalDensityChannelScoreLeft νB S R D Ψ hDmeas hΨmeas hΨ hDCP hDTP x A =
      ∫ y, S (decodedTensorChannel (D (x, y)) R A (Ψ y)) ∂νB := rfl

/-- Fubini identifies the mean of the actual conditional linear functional
with the genuine joint score and proves its integrability. -/
theorem integral_conditionalDensityChannelScoreLeft
    [DecidableEq κ] [DecidableEq υ] [DecidableEq χ] [Nonempty κ] [Nonempty υ]
    (μ : Measure α) (νB : Measure β) [SFinite μ] [SFinite νB]
    (S : MatrixOperation ν χ →L[ℝ] ℝ) (R : MatrixOperation ν (ι × τ))
    (D : α × β → MatrixOperation (κ × υ) χ)
    (Φ : α → MatrixOperation ι κ) (Ψ : β → MatrixOperation τ υ)
    (hDmeas : Measurable D) (hΦmeas : Measurable Φ) (hΨmeas : Measurable Ψ)
    (hΦ : Integrable Φ μ) (hΨ : Integrable Ψ νB)
    (hDCP : ∀ z, CompletelyPositive (D z).toLinearMap)
    (hDTP : ∀ z, ∀ X, (D z X).trace = X.trace) :
    Integrable (fun x => conditionalDensityChannelScoreLeft νB S R D Ψ
      hDmeas hΨmeas hΨ hDCP hDTP x (Φ x)) μ ∧
      (∫ x, conditionalDensityChannelScoreLeft νB S R D Ψ
        hDmeas hΨmeas hΨ hDCP hDTP x (Φ x) ∂μ) =
        ∫ z, jointDensityChannelScore S R D Φ Ψ z ∂μ.prod νB := by
  have h := integrable_jointDensityChannelScore_of_completelyPositive_tracePreserving
    μ νB S R D Φ Ψ hDmeas hΦmeas hΨmeas hΦ hΨ hDCP hDTP
  exact ⟨h.integral_prod_left, (integral_prod _ h).symm⟩

end

end NLQCLean.ClassicalCommunication

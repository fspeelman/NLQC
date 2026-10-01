import NLQCLean.Models.ClassicalCommunication.DensityCompression

/-!
# Sequential actual-outcome compression of two CP densities

Alice's actual conditional score is compressed first, leaving Bob's density
and the original jointly measurable final channel fixed. Bob is then selected
inside the finite intersection of the good sections corresponding to Alice's
selected outcomes. Both finite Kraus instruments are genuinely normalized,
and the original joint integral score is preserved exactly.
-/

namespace NLQCLean.ClassicalCommunication

open MeasureTheory Matrix Set
open scoped MeasureTheory Matrix.Norms.Elementwise

attribute [local implicit_reducible] Matrix

noncomputable section

noncomputable local instance sequentialMatrixNormedAddCommGroup
    {ν : Type*} [Fintype ν] : NormedAddCommGroup (Matrix ν ν ℂ) :=
  Matrix.normedAddCommGroup

noncomputable local instance sequentialMatrixTopologicalSpace
    {ν : Type*} [Fintype ν] : TopologicalSpace (Matrix ν ν ℂ) :=
  (sequentialMatrixNormedAddCommGroup (ν := ν)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

noncomputable local instance sequential_density_compression_instance_1 {ν : Type*} [Fintype ν] :
    NormedSpace ℂ (Matrix ν ν ℂ) := Matrix.normedSpace

noncomputable local instance sequential_density_compression_instance_2 {ν : Type*} [Fintype ν] :
    NormedSpace ℝ (Matrix ν ν ℂ) := Matrix.normedSpace

noncomputable local instance sequential_density_compression_instance_3 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedAddCommGroup (MatrixOperation ι κ) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance sequential_density_compression_instance_4 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedSpace ℂ (MatrixOperation ι κ) := ContinuousLinearMap.toNormedSpace

noncomputable local instance sequential_density_compression_instance_5 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedSpace ℝ (MatrixOperation ι κ) := ContinuousLinearMap.toNormedSpace

local instance sequential_density_compression_instance_6 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    MeasurableSpace (MatrixOperation ι κ) := borel (MatrixOperation ι κ)

local instance sequential_density_compression_instance_7 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    BorelSpace (MatrixOperation ι κ) := ⟨rfl⟩

variable {α β ι κ τ υ ν χ : Type*}
variable [MeasurableSpace α] [MeasurableSpace β]
variable [Fintype ι] [Fintype κ] [Fintype τ] [Fintype υ] [Fintype ν] [Fintype χ]
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq τ] [DecidableEq υ] [DecidableEq χ]
variable [Nonempty ι] [Nonempty τ] [Nonempty κ] [Nonempty υ]

/-- Actual Alice-then-Bob outcome selection preserves the genuine joint
channel score, both original quantum systems, and the original decoder values.
The two finite alphabets have the sharp input-dimension squared-plus-one caps. -/
theorem exists_sequential_score_preserving_density_instruments
    (I_A : CPVectorInstrument α ι κ) (I_B : CPVectorInstrument β τ υ)
    (Φ : α → MatrixOperation ι κ) (Ψ : β → MatrixOperation τ υ)
    (hΦmeas : Measurable Φ) (hΨmeas : Measurable Ψ)
    (hΦ : Integrable Φ I_A.traceProbability) (hΨ : Integrable Ψ I_B.traceProbability)
    (hrepA : I_A.traceProbability.withDensityᵥ Φ = I_A.operationMeasure)
    (hrepB : I_B.traceProbability.withDensityᵥ Ψ = I_B.operationMeasure)
    (S : MatrixOperation ν χ →L[ℝ] ℝ) (R : MatrixOperation ν (ι × τ))
    (D : α × β → MatrixOperation (κ × υ) χ) (hDmeas : Measurable D)
    (hDCP : ∀ z, CompletelyPositive (D z).toLinearMap)
    (hDTP : ∀ z, ∀ X, (D z X).trace = X.trace) :
    ∃ nA : ℕ, nA ≤ Fintype.card ι ^ 2 + 1 ∧
      ∃ nB : ℕ, nB ≤ Fintype.card τ ^ 2 + 1 ∧
      ∃ (selectA : Fin nA → α) (selectB : Fin nB → β)
        (weightA : Fin nA → ℝ) (weightB : Fin nB → ℝ),
        (∀ j, 0 ≤ weightA j) ∧ (∑ j, weightA j) = 1 ∧
        (∀ k, 0 ≤ weightB k) ∧ (∑ k, weightB k) = 1 ∧
        ∃ (J_A : FiniteKrausInstrument ι κ (Fin nA) (κ × ι))
          (J_B : FiniteKrausInstrument τ υ (Fin nB) (υ × τ)),
          (∀ j, J_A.branch j = (weightA j • Φ (selectA j)).toLinearMap) ∧
          (∀ k, J_B.branch k = (weightB k • Ψ (selectB k)).toLinearMap) ∧
          (∫ z, jointDensityChannelScore S R D Φ Ψ z
            ∂I_A.traceProbability.prod I_B.traceProbability) =
            ∑ j, ∑ k, S (decodedTensorChannel (D (selectA j, selectB k)) R
              (weightA j • Φ (selectA j)) (weightB k • Ψ (selectB k))) := by
  classical
  let LA := conditionalDensityChannelScoreLeft I_B.traceProbability S R D Ψ
    hDmeas hΨmeas hΨ hDCP hDTP
  have hLA := integral_conditionalDensityChannelScoreLeft
    I_A.traceProbability I_B.traceProbability S R D Φ Ψ
    hDmeas hΦmeas hΨmeas hΦ hΨ hDCP hDTP
  obtain ⟨nA, hnA, selectA, weightA, hselectedA, hwA, hsumA, J_A, hJ_A, hscoreA⟩ :=
    I_A.exists_finite_score_preserving_density_instrument Φ hΦ hrepA LA hLA.1
      univ (Filter.Eventually.of_forall fun _ => mem_univ _)
  let A : Fin nA → MatrixOperation ι κ := fun j => weightA j • Φ (selectA j)
  let LB : β → MatrixOperation τ υ →ₗ[ℝ] ℝ := fun y =>
    ∑ j, S.toLinearMap.comp (decodedTensorChannelRightRealLinear (D (selectA j, y)) R (A j))
  have hsection (j : Fin nA) : Integrable
      (fun y => S (decodedTensorChannel (D (selectA j, y)) R (A j) (Ψ y)))
      I_B.traceProbability :=
    integrable_conditionalDensityChannelScoreLeft I_B.traceProbability S R D Ψ
      hDmeas hΨmeas hΨ hDCP hDTP (selectA j) (A j)
  have hLB : Integrable (fun y => LB y (Ψ y)) I_B.traceProbability := by
    have h : ∀ t : Finset (Fin nA), Integrable
        (fun y => ∑ j ∈ t,
          S (decodedTensorChannel (D (selectA j, y)) R (A j) (Ψ y)))
        I_B.traceProbability := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        exact integrable_zero _ _ _
      | @insert j t hj ih =>
        simp only [Finset.sum_insert hj]
        exact (hsection j).add ih
    have heq : (fun y => LB y (Ψ y)) = fun y =>
        ∑ j, S (decodedTensorChannel (D (selectA j, y)) R (A j) (Ψ y)) := by
      funext y
      simp only [LB, LinearMap.sum_apply, LinearMap.comp_apply,
        ContinuousLinearMap.coe_coe]
      rfl
    rw [heq]
    exact h Finset.univ
  obtain ⟨hgoodB, _⟩ := I_B.reconstructed_density_normalized Ψ hΨ hrepB
  -- Keep the source's finite intersection explicit. These are sections at
  -- actual selected Alice outcomes, using the same original Bob density.
  let goodSection : Fin nA → Set β := fun j => {y |
    CompletelyPositive (Φ (selectA j)).toLinearMap ∧
      (unnormalizedChoiMatrix (Φ (selectA j)).toLinearMap).trace = (Fintype.card ι : ℂ) ∧
      CompletelyPositive (Ψ y).toLinearMap ∧
      (unnormalizedChoiMatrix (Ψ y).toLinearMap).trace = (Fintype.card τ : ℂ) ∧
      CompletelyPositive (D (selectA j, y)).toLinearMap ∧
      ∀ X, (D (selectA j, y) X).trace = X.trace}
  let GB : Set β := ⋂ j, goodSection j
  have hGB : ∀ᵐ y ∂I_B.traceProbability, y ∈ GB := by
    have hsections : ∀ᵐ y ∂I_B.traceProbability, ∀ j, y ∈ goodSection j :=
      Filter.eventually_all.mpr fun j => hgoodB.mono fun y hy =>
        ⟨(hselectedA j).2.1, (hselectedA j).2.2, hy.1, hy.2,
          hDCP (selectA j, y), hDTP (selectA j, y)⟩
    exact hsections.mono fun y hy => mem_iInter.mpr hy
  obtain ⟨nB, hnB, selectB, weightB, _, hwB, hsumB, J_B, hJ_B, hscoreB⟩ :=
    I_B.exists_finite_score_preserving_density_instrument Ψ hΨ hrepB LB hLB GB hGB
  refine ⟨nA, hnA, nB, hnB, selectA, selectB, weightA, weightB,
    hwA, hsumA, hwB, hsumB, J_A, J_B, hJ_A, hJ_B, ?_⟩
  calc
    (∫ z, jointDensityChannelScore S R D Φ Ψ z
        ∂I_A.traceProbability.prod I_B.traceProbability) =
        ∫ x, LA x (Φ x) ∂I_A.traceProbability := hLA.2.symm
    _ = ∑ j, LA (selectA j) (A j) := hscoreA.symm
    _ = ∑ j, ∫ y, S (decodedTensorChannel (D (selectA j, y)) R (A j) (Ψ y))
        ∂I_B.traceProbability := rfl
    _ = ∫ y, ∑ j, S (decodedTensorChannel (D (selectA j, y)) R (A j) (Ψ y))
        ∂I_B.traceProbability :=
      (integral_finsetSum Finset.univ (fun j _ => hsection j)).symm
    _ = ∫ y, LB y (Ψ y) ∂I_B.traceProbability := by
      congr 1
      funext y
      simp only [LB, LinearMap.sum_apply, LinearMap.comp_apply,
        ContinuousLinearMap.coe_coe]
      rfl
    _ = ∑ k, LB (selectB k) (weightB k • Ψ (selectB k)) := hscoreB.symm
    _ = ∑ j, ∑ k, S (decodedTensorChannel (D (selectA j, selectB k)) R
        (weightA j • Φ (selectA j)) (weightB k • Ψ (selectB k))) := by
      simp only [LB, LinearMap.sum_apply, LinearMap.comp_apply,
        ContinuousLinearMap.coe_coe]
      exact Finset.sum_comm

end

end NLQCLean.ClassicalCommunication

import NLQCLean.Models.ClassicalCommunication.ConditionalDensityChannels
import NLQCLean.Models.ClassicalCommunication.BarycenterSupport

/-!
# Finite instruments selected from actual CP densities

An integrable density reconstructing a countably additive CP instrument has
positive normalized Choi values almost everywhere, by uniqueness of its
actual Radon--Nikodym representation. The attained-value barycenter theorem
then selects at most `card(input)² + 1` actual good outcomes preserving the
input marginal and a real-linear outcome-dependent score. Their weighted CP
operations admit a genuine normalized finite Kraus instrument.
-/

namespace NLQCLean.ClassicalCommunication

open MeasureTheory Matrix Set
open scoped MeasureTheory ComplexOrder MatrixOrder Matrix.Norms.Elementwise

attribute [local implicit_reducible] Matrix

noncomputable section

noncomputable local instance compressionMatrixNormedAddCommGroup
    {ν : Type*} [Fintype ν] : NormedAddCommGroup (Matrix ν ν ℂ) :=
  Matrix.normedAddCommGroup

noncomputable local instance compressionMatrixTopologicalSpace
    {ν : Type*} [Fintype ν] : TopologicalSpace (Matrix ν ν ℂ) :=
  (compressionMatrixNormedAddCommGroup (ν := ν)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

noncomputable local instance density_compression_instance_1 {ν : Type*} [Fintype ν] :
    NormedSpace ℂ (Matrix ν ν ℂ) := Matrix.normedSpace

noncomputable local instance density_compression_instance_2 {ν : Type*} [Fintype ν] :
    NormedSpace ℝ (Matrix ν ν ℂ) := Matrix.normedSpace

noncomputable local instance density_compression_instance_3 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedAddCommGroup (MatrixOperation ι κ) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance density_compression_instance_4 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedSpace ℂ (MatrixOperation ι κ) := ContinuousLinearMap.toNormedSpace

noncomputable local instance density_compression_instance_5 {ι κ : Type*} [Fintype ι] [Fintype κ] :
    NormedSpace ℝ (MatrixOperation ι κ) := ContinuousLinearMap.toNormedSpace

variable {α ι κ : Type*} [MeasurableSpace α]
variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Nonempty ι]

noncomputable local instance densityHermitianNormedAddCommGroup :
    NormedAddCommGroup (selfAdjoint (Matrix ι ι ℂ)) :=
  inferInstanceAs (NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix ι ι ℂ)))

noncomputable local instance density_compression_instance_6 : NormedSpace ℝ (selfAdjoint (Matrix ι ι ℂ)) :=
  inferInstanceAs (NormedSpace ℝ (selfAdjoint.submodule ℝ (Matrix ι ι ℂ)))

noncomputable local instance densityHermitianTopologicalSpace :
    TopologicalSpace (selfAdjoint (Matrix ι ι ℂ)) :=
  (densityHermitianNormedAddCommGroup (ι := ι)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

noncomputable local instance density_compression_instance_7 : ContinuousENorm (selfAdjoint (Matrix ι ι ℂ)) :=
  @SeminormedAddGroup.toContinuousENorm (selfAdjoint (Matrix ι ι ℂ))
    (@SeminormedAddCommGroup.toSeminormedAddGroup (selfAdjoint (Matrix ι ι ℂ))
      (@NormedAddCommGroup.toSeminormedAddCommGroup (selfAdjoint (Matrix ι ι ℂ))
        (densityHermitianNormedAddCommGroup (ι := ι))))

local instance density_compression_instance_8 : FiniteDimensional ℝ (selfAdjoint (Matrix ι ι ℂ)) :=
  inferInstanceAs (FiniteDimensional ℝ (selfAdjoint.submodule ℝ (Matrix ι ι ℂ)))

omit [MeasurableSpace α] [Nonempty ι] [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
private theorem density_ptraceA_isHermitian
    {C : Matrix (κ × ι) (κ × ι) ℂ} (hC : C.IsHermitian) :
    (ptraceA κ ι C).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [ptraceA_apply, star_sum]
  exact Finset.sum_congr rfl (fun k _ => hC.apply (k, i) (k, j))

omit [MeasurableSpace α] [Nonempty ι] [DecidableEq ι] [DecidableEq κ] in
private theorem density_trace_ptraceA (C : Matrix (κ × ι) (κ × ι) ℂ) :
    (ptraceA κ ι C).trace = C.trace := by
  simp only [Matrix.trace, Matrix.diag, ptraceA_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

namespace CPVectorInstrument

variable (I : CPVectorInstrument α ι κ)

/-- Every actual integrable reconstruction has the positive normalized
values and identity integrated marginal of the proved RN density. -/
theorem reconstructed_density_normalized
    (Φ : α → MatrixOperation ι κ) (hΦ : Integrable Φ I.traceProbability)
    (hrep : I.traceProbability.withDensityᵥ Φ = I.operationMeasure) :
    (∀ᵐ x ∂I.traceProbability, CompletelyPositive (Φ x).toLinearMap ∧
      (unnormalizedChoiMatrix (Φ x).toLinearMap).trace = (Fintype.card ι : ℂ)) ∧
      (∫ x, ptraceA κ ι (unnormalizedChoiMatrix (Φ x).toLinearMap)
        ∂I.traceProbability) = 1 := by
  let : FiniteDimensional ℝ (MatrixOperation ι κ) :=
    (unnormalizedChoiRealLinearEquiv (ι := ι) (κ := κ)).symm.finiteDimensional
  let : CompleteSpace (MatrixOperation ι κ) :=
    FiniteDimensional.complete ℝ (MatrixOperation ι κ)
  obtain ⟨Φ', _, hΦ', hrep', hgood', hmargin'⟩ := I.exists_positive_normalized_density
  have heq : Φ =ᵐ[I.traceProbability] Φ' :=
    hΦ.ae_eq_of_withDensityᵥ_eq hΦ' (hrep.trans hrep'.symm)
  refine ⟨?_, ?_⟩
  · filter_upwards [heq, hgood'] with x hx hgood
    rw [hx]
    exact hgood
  · exact (integral_congr_ae (heq.mono fun x hx => congrArg
      (fun A : MatrixOperation ι κ => ptraceA κ ι
        (unnormalizedChoiMatrix A.toLinearMap)) hx)).trans hmargin'

/-- At most `card(input)² + 1` actual good outcomes of a reconstructed
CP density yield a normalized finite Kraus instrument preserving an actual
outcome-dependent real-linear score exactly. Positivity, trace normalization,
and the input marginal are derived from reconstruction, not assumed fields. -/
theorem exists_finite_score_preserving_density_instrument
    (Φ : α → MatrixOperation ι κ) (hΦ : Integrable Φ I.traceProbability)
    (hrep : I.traceProbability.withDensityᵥ Φ = I.operationMeasure)
    (L : α → MatrixOperation ι κ →ₗ[ℝ] ℝ)
    (hscore : Integrable (fun x => L x (Φ x)) I.traceProbability)
    (G : Set α) (hG : ∀ᵐ x ∂I.traceProbability, x ∈ G) :
    ∃ n : ℕ, n ≤ Fintype.card ι ^ 2 + 1 ∧
      ∃ (select : Fin n → α) (weight : Fin n → ℝ),
        (∀ j, select j ∈ G ∧ CompletelyPositive (Φ (select j)).toLinearMap ∧
          (unnormalizedChoiMatrix (Φ (select j)).toLinearMap).trace =
            (Fintype.card ι : ℂ)) ∧
        (∀ j, 0 ≤ weight j) ∧ (∑ j, weight j) = 1 ∧
        ∃ J : FiniteKrausInstrument ι κ (Fin n) (κ × ι),
          (∀ j, J.branch j = (weight j • Φ (select j)).toLinearMap) ∧
          (∑ j, L (select j) (weight j • Φ (select j))) =
            ∫ x, L x (Φ x) ∂I.traceProbability := by
  classical
  let : FiniteDimensional ℝ (MatrixOperation ι κ) :=
    (unnormalizedChoiRealLinearEquiv (ι := ι) (κ := κ)).symm.finiteDimensional
  obtain ⟨hgood, hinput⟩ := I.reconstructed_density_normalized Φ hΦ hrep
  let H : Set α := {x | x ∈ G ∧ CompletelyPositive (Φ x).toLinearMap ∧
    (unnormalizedChoiMatrix (Φ x).toLinearMap).trace = (Fintype.card ι : ℂ)}
  have hH : ∀ᵐ x ∂I.traceProbability, x ∈ H := hG.and hgood
  let N := (((ptraceA κ ι).restrictScalars ℝ).comp
    (unnormalizedChoiRealLinear (ι := ι) (κ := κ))).toContinuousLinearMap
  let P := (selfAdjointPart ℝ : Matrix ι ι ℂ →ₗ[ℝ]
    selfAdjoint (Matrix ι ι ℂ)).toContinuousLinearMap
  let marginal : α → selfAdjoint (Matrix ι ι ℂ) := fun x => P (N (Φ x))
  have hmarginal : Integrable marginal I.traceProbability :=
    P.integrable_comp (N.integrable_comp hΦ)
  have hmean : (∫ x, marginal x ∂I.traceProbability) = 1 := by
    calc
      (∫ x, marginal x ∂I.traceProbability) =
          P (∫ x, N (Φ x) ∂I.traceProbability) :=
        P.integral_comp_comm (N.integrable_comp hΦ)
      _ = P 1 := congrArg P hinput
      _ = 1 := by
        apply Subtype.ext
        exact (IsSelfAdjoint.one (Matrix ι ι ℂ)).coe_selfAdjointPart_apply ℝ
  have hmargin_eq (x : H) : (marginal x : Matrix ι ι ℂ) =
      ptraceA κ ι (unnormalizedChoiMatrix (Φ x).toLinearMap) := by
    apply IsSelfAdjoint.coe_selfAdjointPart_apply ℝ
    exact density_ptraceA_isHermitian
      ((completelyPositive_iff_unnormalizedChoi_posSemidef _).mp x.property.2.1).isHermitian
  have htrace (x : H) : (marginal x : Matrix ι ι ℂ).trace.re = Fintype.card ι := by
    rw [hmargin_eq x, density_trace_ptraceA, x.property.2.2]
    simp
  have hhull := integral_mem_convexHull_image
    (fun x => (marginal x, L x (Φ x))) H (hmarginal.prodMk hscore) hH
  rw [integral_pair hmarginal hscore, hmean] at hhull
  have hrange : range (fun x : H => (marginal x, L x (Φ x))) =
      (fun x => (marginal x, L x (Φ x))) '' H := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← hrange] at hhull
  obtain ⟨n, hn, select, weight, hw, hsum, hmarg, hsc⟩ :=
    exists_normalized_hermitian_marginal_score_support
      (fun x : H => marginal x) (fun x : H => L x (Φ x))
      (∫ x, L x (Φ x) ∂I.traceProbability) htrace hhull
  have hnorm : (∑ j, weight j • N (Φ (select j))) = (1 : Matrix ι ι ℂ) := by
    have h := congrArg ((selfAdjoint (Matrix ι ι ℂ)).subtype) hmarg
    rw [map_sum] at h
    change (∑ j, ((weight j • marginal (select j) :
      selfAdjoint (Matrix ι ι ℂ)) : Matrix ι ι ℂ)) = (1 : Matrix ι ι ℂ) at h
    change (∑ j, weight j • ptraceA κ ι
      (unnormalizedChoiMatrix (Φ (select j)).toLinearMap)) = (1 : Matrix ι ι ℂ)
    simpa only [selfAdjoint.val_smul, hmargin_eq,
      selfAdjoint.val_one] using h
  let branches : Fin n → (Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :=
    fun j => (weight j • Φ (select j)).toLinearMap
  have hCP : ∀ j, CompletelyPositive (branches j) := by
    intro j
    apply (completelyPositive_iff_unnormalizedChoi_posSemidef _).mpr
    change (unnormalizedChoiRealLinear (weight j • Φ (select j))).PosSemidef
    rw [map_smul]
    exact ((completelyPositive_iff_unnormalizedChoi_posSemidef _).mp
      (select j).property.2.1).smul (hw j)
  have hTP : ∀ X : Matrix ι ι ℂ, (∑ j, branches j X).trace = X.trace := by
    have hnormalized : ptraceA κ ι (unnormalizedChoiMatrix
        (∑ j, branches j)) = 1 := by
      have hsumbranches : (∑ j, branches j) =
          (∑ j, weight j • Φ (select j)).toLinearMap :=
        (map_sum (ContinuousLinearMap.coeLM ℂ)
          (fun j => weight j • Φ (select j)) Finset.univ).symm
      rw [hsumbranches]
      change N (∑ j, weight j • Φ (select j)) = 1
      rw [map_sum]
      simpa only [map_smul] using hnorm
    have ht := (tracePreserving_iff_ptraceA_unnormalizedChoi _).mpr hnormalized
    intro X
    simpa only [LinearMap.sum_apply] using ht X
  obtain ⟨J, hJ⟩ := exists_instrument_of_completelyPositive_branches branches hCP hTP
  refine ⟨n, hn, fun j => select j, weight, fun j => (select j).property,
    hw, hsum, J, hJ, ?_⟩
  simpa only [map_smul, smul_eq_mul] using hsc

end CPVectorInstrument

end

end NLQCLean.ClassicalCommunication

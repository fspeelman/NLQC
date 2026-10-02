import NLQCLean.Geometry.DirectVolume.Assembly
import NLQCLean.Bounds.RectangularDiagonalWorstCase
import NLQCLean.Models.ChoiAlgebra

/-!
# Two-qubit diagonal gates with Choi infidelity

For two qubits, `thm:diagonal` holds with the Choi infidelity (score deficit)
in place of the diamond error. Every diagonal two-qubit gate equals, up to a
global phase, a local diagonal unitary times the controlled phase at the
alternating angle; composing the decoders with these local unitaries changes
neither the score nor the resources. Hence the controlled-phase rates hold
for almost every diagonal two-qubit gate, uniformly over budgets and over
charged, finite and standard-Borel free-classical protocols.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉ u₁₀ u₁₁ u₁₂

open Matrix MeasureTheory ClassicalCommunication
open scoped Kronecker

section ScoreCovariance

variable {ι κ κ' : Type*} [Fintype ι] [Fintype κ] [Fintype κ']
variable [DecidableEq ι] [DecidableEq κ] [DecidableEq κ']

omit [Fintype κ'] [DecidableEq κ] [DecidableEq κ'] in
/-- Output conjugation acts on the Choi matrix by `L ⊗ 1`. -/
theorem choiMatrix_adConj_comp (L : Matrix κ' κ ℂ) (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    choiMatrix ((adConj L).comp Φ) =
      (L ⊗ₖ (1 : Matrix ι ι ℂ)) * choiMatrix Φ * (L ⊗ₖ (1 : Matrix ι ι ℂ))ᴴ := by
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  ext p q
  simp only [choiMatrix_apply, LinearMap.comp_apply, adConj_apply, Matrix.mul_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply, mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

omit [DecidableEq κ'] in
/-- The unitary score is covariant under an output isometry applied to both
the target and the channel. -/
theorem scoreU_adConj_comp {L : Matrix κ' κ ℂ} (hL : IsIsometry L) (U : Matrix κ ι ℂ)
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    scoreU (L * U) ((adConj L).comp Φ) = scoreU U Φ := by
  rw [scoreU_eq_re_trace_choi_mul, scoreU_eq_re_trace_choi_mul, adConj_mul_eq_comp,
    choiMatrix_adConj_comp, choiMatrix_adConj_comp]
  have h1 : (L ⊗ₖ (1 : Matrix ι ι ℂ))ᴴ * (L ⊗ₖ (1 : Matrix ι ι ℂ)) = 1 :=
    hL.kronecker isIsometry_one
  set A := L ⊗ₖ (1 : Matrix ι ι ℂ)
  have hre : A * choiMatrix (adConj U) * Aᴴ * (A * choiMatrix Φ * Aᴴ) =
      A * (choiMatrix (adConj U) * (Aᴴ * A) * choiMatrix Φ * Aᴴ) := by
    simp only [Matrix.mul_assoc]
  rw [hre, Matrix.trace_mul_comm, h1]
  simp only [Matrix.mul_one, Matrix.mul_assoc, h1]

omit [DecidableEq κ] in
/-- A unit global phase does not change the unitary score. -/
theorem scoreU_smul_of_normSq_eq_one (c : ℂ) (hc : Complex.normSq c = 1) (U : Matrix κ ι ℂ)
    (Φ : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    scoreU (c • U) Φ = scoreU U Φ := by
  rw [scoreU_eq_re_trace_choi_mul, scoreU_eq_re_trace_choi_mul,
    adConj_smul_of_normSq_eq_one c hc U]

end ScoreCovariance

namespace PureProtocol

variable {ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype ιA'] [Fintype ιB'] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq ιA'] [DecidableEq ιB'] [DecidableEq εA] [DecidableEq εB]
variable (P : PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB)

/-- Compose both decoders with local output isometries. -/
def postcomposeLocal (LA : Matrix ιA' ιA' ℂ) (LB : Matrix ιB' ιB' ℂ)
    (hLA : IsIsometry LA) (hLB : IsIsometry LB) :
    PureProtocol ιA ιB ρA ρB κA κB μA μB ιA' ιB' εA εB :=
  { P with
    decA := (LA ⊗ₖ (1 : Matrix εA εA ℂ)) * P.decA
    decA_isometry := (hLA.kronecker isIsometry_one).mul P.decA_isometry
    decB := (LB ⊗ₖ (1 : Matrix εB εB ℂ)) * P.decB
    decB_isometry := (hLB.kronecker isIsometry_one).mul P.decB_isometry }

theorem postcomposeLocal_hasFootprint_iff (LA : Matrix ιA' ιA' ℂ) (LB : Matrix ιB' ιB' ℂ)
    (hLA : IsIsometry LA) (hLB : IsIsometry LB) (K : ℕ) :
    (P.postcomposeLocal LA LB hLA hLB).HasFootprint K ↔ P.HasFootprint K := Iff.rfl

/-- The postcomposed protocol implements the conjugated original channel. -/
theorem postcomposeLocal_operationalChannel (LA : Matrix ιA' ιA' ℂ) (LB : Matrix ιB' ιB' ℂ)
    (hLA : IsIsometry LA) (hLB : IsIsometry LB) :
    (P.postcomposeLocal LA LB hLA hLB).operationalChannel =
      (adConj (LA ⊗ₖ LB)).comp P.operationalChannel := by
  change channelOf ((NLQCLean.globalIsometry P.resource P.encA P.encB
      ((LA ⊗ₖ (1 : Matrix εA εA ℂ)) * P.decA) ((LB ⊗ₖ (1 : Matrix εB εB ℂ)) * P.decB)).submatrix
        (outputRegroup ιA' ιB' εA εB) id) = _
  have hG : NLQCLean.globalIsometry P.resource P.encA P.encB
      ((LA ⊗ₖ (1 : Matrix εA εA ℂ)) * P.decA) ((LB ⊗ₖ (1 : Matrix εB εB ℂ)) * P.decB) =
      ((LA ⊗ₖ (1 : Matrix εA εA ℂ)) ⊗ₖ (LB ⊗ₖ (1 : Matrix εB εB ℂ))) *
        NLQCLean.globalIsometry P.resource P.encA P.encB P.decA P.decB := by
    simp only [NLQCLean.globalIsometry, NLQCLean.decoder, Matrix.mul_kronecker_mul,
      Matrix.mul_assoc]
  rw [hG, ← Matrix.submatrix_mul_equiv _ _ (outputRegroup ιA' ιB' εA εB)
    (outputRegroup ιA' ιB' εA εB) id, outputRegroup_local_tensor_identity,
    channelOf_tensor_output_mul]
  rfl

end PureProtocol

/-- Charged reachability is invariant under a local output isometry and a unit
global phase. -/
theorem mem_pureReachable_of_local_phase {d K : ℕ} {ε : ℝ}
    {U V : Matrix.unitaryGroup (Fin d × Fin d) ℂ}
    (LA LB : Matrix (Fin d) (Fin d) ℂ) (hLA : IsIsometry LA) (hLB : IsIsometry LB)
    (c : ℂ) (hc : Complex.normSq c = 1)
    (hV : (V : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) =
      c • ((LA ⊗ₖ LB) * (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)))
    (hU : U ∈ pureReachable d K ε) : V ∈ pureReachable d K ε := by
  obtain ⟨s, P, hK, hs⟩ := hU
  apply (P.postcomposeLocal LA LB hLA hLB).mem_pureReachable
    ((P.postcomposeLocal_hasFootprint_iff LA LB hLA hLB K).mpr hK)
  rw [P.postcomposeLocal_operationalChannel, hV, scoreU_smul_of_normSq_eq_one c hc,
    scoreU_adConj_comp (hLA.kronecker hLB)]
  exact hs

/-- At `d = 2` the two-level restriction selects all four phases. -/
theorem restrictedRectangularAngles_two (h : 2 ≤ 2) (φ : Fin 2 × Fin 2 → ℝ) :
    restrictedRectangularAngles h h φ = φ := by
  funext p
  rfl

/-- Every diagonal two-qubit gate is, up to a unit global phase and local
diagonal unitaries, the controlled phase at its alternating angle. -/
theorem controlledPhase_eq_local_twoQubitDiagonal (φ : Fin 2 × Fin 2 → ℝ) :
    controlledPhase (rectangularAlternatingAngleMod (le_refl 2) (le_refl 2) φ) =
      qubitGlobalPhaseCorrection φ • ((qubitPhaseCorrectionA φ ⊗ₖ qubitPhaseCorrectionB φ) *
        rectangularDiagonalPhase φ) := by
  rw [controlledPhase_rectangularAlternatingAngleMod, rectangularAlternatingAngle,
    restrictedRectangularAngles_two, ← qubitDiagonalPhase_local_reduction]
  rfl

/-- **Two-qubit diagonal gates, charged reachability with Choi infidelity.**
For almost every diagonal two-qubit gate there is a threshold below which any
budget whose pure or common-map mixed charged protocols reach score `1 - ε`
satisfies `K ≥ c √log(1/ε)`. -/
theorem exists_ae_twoQubitDiagonal_resource_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ φ ∂rectangularPhaseMeasure 2 2,
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        (rectangularDiagonalPhaseUnitary φ ∈ pureReachable 2 K ε →
          c * Real.sqrt (Real.log (1 / ε)) ≤ K) ∧
        (rectangularDiagonalPhaseUnitary φ ∈ mixedReachable 2 K ε →
          c * Real.sqrt (Real.log (1 / ε)) ≤ K) := by
  obtain ⟨c, hc, hae⟩ := exists_ae_chargedControlledPhase_resource_constant_of_imageVolumeBound hGeom
  refine ⟨c, hc, ?_⟩
  have hpull := ae_rectangularAlternatingAngleMod_of_ae (le_refl 2) (le_refl 2) hae
  filter_upwards [hpull] with φ hφ
  obtain ⟨ε₀, hε₀, hε₀half, hphase⟩ := hφ
  refine ⟨ε₀, hε₀, hε₀half, fun K ε hε hee => ?_⟩
  have hLA := (qubitPhaseCorrectionA_unitary φ).1
  have hLB := (qubitPhaseCorrectionB_unitary φ).1
  have hV : ((controlledPhaseTarget (rectangularAlternatingAngleMod (le_refl 2) (le_refl 2) φ) :
      Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) =
      qubitGlobalPhaseCorrection φ • ((qubitPhaseCorrectionA φ ⊗ₖ qubitPhaseCorrectionB φ) *
        ((rectangularDiagonalPhaseUnitary φ : Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ) :
          Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) :=
    controlledPhase_eq_local_twoQubitDiagonal φ
  have hreach (h : rectangularDiagonalPhaseUnitary φ ∈ pureReachable 2 K ε) :
      controlledPhaseTarget (rectangularAlternatingAngleMod (le_refl 2) (le_refl 2) φ) ∈
        pureReachable 2 K ε :=
    mem_pureReachable_of_local_phase _ _ hLA hLB _ (normSq_qubitGlobalPhaseCorrection φ) hV h
  refine ⟨fun h => (hphase K ε hε hee).1 (hreach h), fun h => ?_⟩
  rw [mixedReachable_eq_pureReachable] at h
  exact (hphase K ε hε hee).1 (hreach h)

/-- Two-qubit diagonal gates with free standard-Borel classical messages and
Choi infidelity: `log(1/ε) ≤ C Kq¹⁰` for pure and common-map mixed protocols. -/
theorem exists_ae_borelTwoQubitDiagonal_log_bound_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ φ ∂rectangularPhaseMeasure 2 2,
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (Kq : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
          (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
          [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
          [Fintype μA] [Fintype μB]
          [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
          [DecidableEq μA] [DecidableEq μB]
          [MeasurableSpace σA] [MeasurableSpace σB]
          [StandardBorelSpace σA] [StandardBorelSpace σB],
        ∀ P : StandardBorelClassicalProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB
          σA σB (Fin 2) (Fin 2),
        (P.HasQuantumFootprint Kq →
          1 - ε ≤ scoreU (rectangularDiagonalPhase φ) P.operationalChannel.toLinearMap →
            Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10) ∧
        (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m Kq →
          1 - ε ≤ scoreU (rectangularDiagonalPhase φ) (P.mixedOperationalChannel m) →
            Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10) := by
  obtain ⟨c, hc, hae⟩ := exists_ae_twoQubitDiagonal_resource_constant_of_imageVolumeBound hGeom
  refine ⟨4096 / c ^ 2, by positivity, ?_⟩
  filter_upwards [hae] with φ hφ
  obtain ⟨ε₀, hε₀pos, hε₀half, hcharged⟩ := hφ
  refine ⟨ε₀, hε₀pos, hε₀half, ?_⟩
  intro Kq ε hε hε₀ ρA ρB κA κB μA μB σA σB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P
  have hL : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg ((one_le_div₀ hε).mpr (by linarith))
  have htransfer (hreach : rectangularDiagonalPhaseUnitary φ ∈
      pureReachable 2 (4 * 2 ^ 4 * Kq ^ 5) ε) :
      Real.log (1 / ε) ≤ (4096 / c ^ 2) * (Kq : ℝ) ^ 10 := by
    apply log_le_tenth_power_of_charged_sqrt_lower_bound hc hL
    have h := (hcharged (4 * 2 ^ 4 * Kq ^ 5) ε hε hε₀).1 hreach
    simpa only [show 4 * 2 ^ 4 = (64 : ℕ) by norm_num,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h
  exact ⟨fun hK hs => htransfer
      (P.mem_pureReachable_of_quantumFootprint (rectangularDiagonalPhaseUnitary φ)
        (by decide) hK hs),
    fun n m hK hs => htransfer
      (P.mem_pureReachable_of_mixedQuantumFootprint m (rectangularDiagonalPhaseUnitary φ)
        (by decide) hK hs)⟩

/-- Charged two-qubit Choi rate. -/
theorem exists_ae_twoQubitDiagonal_resource_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ φ ∂rectangularPhaseMeasure 2 2,
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (K : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        (rectangularDiagonalPhaseUnitary φ ∈ pureReachable 2 K ε →
          c * Real.sqrt (Real.log (1 / ε)) ≤ K) ∧
        (rectangularDiagonalPhaseUnitary φ ∈ mixedReachable 2 K ε →
          c * Real.sqrt (Real.log (1 / ε)) ≤ K) :=
  exists_ae_twoQubitDiagonal_resource_constant_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

/-- Standard-Borel two-qubit Choi rate. -/
theorem exists_ae_borelTwoQubitDiagonal_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ φ ∂rectangularPhaseMeasure 2 2,
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 2 ∧ ∀ (Kq : ℕ) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        ∀ (ρA : Type u₁) (ρB : Type u₂) (κA : Type u₃) (κB : Type u₄)
          (μA : Type u₅) (μB : Type u₆) (σA : Type u₇) (σB : Type u₈)
          [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
          [Fintype μA] [Fintype μB]
          [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
          [DecidableEq μA] [DecidableEq μB]
          [MeasurableSpace σA] [MeasurableSpace σB]
          [StandardBorelSpace σA] [StandardBorelSpace σB],
        ∀ P : StandardBorelClassicalProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB
          σA σB (Fin 2) (Fin 2),
        (P.HasQuantumFootprint Kq →
          1 - ε ≤ scoreU (rectangularDiagonalPhase φ) P.operationalChannel.toLinearMap →
            Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10) ∧
        (∀ (n : ℕ) (m : MixedResource ρA ρB n), P.HasMixedQuantumFootprint m Kq →
          1 - ε ≤ scoreU (rectangularDiagonalPhase φ) (P.mixedOperationalChannel m) →
            Real.log (1 / ε) ≤ C * (Kq : ℝ) ^ 10) :=
  exists_ae_borelTwoQubitDiagonal_log_bound_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

end NLQCLean

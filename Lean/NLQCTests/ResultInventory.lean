import NLQCLean.Results.Unitary
import NLQCLean.Results.PVM
import NLQCLean.Bounds.PVMQualitativeGap
import NLQCLean.Bounds.QualitativeDiamond
import NLQCLean.Bounds.StrongHaarConditional
import NLQCLean.Bounds.StrongUniversalResources
import NLQCLean.Bounds.SwapFloor
import NLQCLean.Approx.PVMRankFloor

/-!
# Reference result inventory

These checks freeze the public mathematical coverage. The explicit reference
theorems below
record quantifier order and conclusions independently of the production theorem
names. The printed definitions expose the protocol, footprint, error and Haar
definitions in audit output.
-/

set_option pp.deepTerms true
set_option format.width 120

namespace NLQCTests

open Matrix MeasureTheory
open NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

/-! ## Frozen unconditional conclusions -/

theorem reference_unitary_exact_impossibility (d : ℕ) (hd : 2 ≤ d) :
    ∃ U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      UnitaryTarget U ∧ NoFinitePureImplementation U ∧ NoFiniteMixedImplementation U :=
  Results.Unitary.exists_no_finite_exact_implementation d hd

theorem reference_unitary_qualitative_gap (d : ℕ) (hd : 2 ≤ d) :
    ∃ U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ, UnitaryTarget U ∧
      ∀ K : ℕ, ∃ e : ℝ, 0 < e ∧ PureScoreGap U K e ∧ MixedScoreGap U K e :=
  Results.Unitary.exists_qualitative_score_gap d hd

theorem reference_unitary_qualitative_diamond_gap (d : ℕ) (hd : 2 ≤ d) :
    ∃ U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ, UnitaryTarget U ∧
      ∀ K : ℕ, ∃ e : ℝ, 0 < e ∧ PureDiamondGap U K e ∧ MixedDiamondGap U K e :=
  Results.Unitary.exists_qualitative_diamond_gap d hd

theorem reference_pvm_qualitative_gap (d : ℕ) (hd : 2 ≤ d) :
    ∃ M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      M ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ ∧
      NoFinitePurePVMImplementation.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M ∧
      NoFiniteMixedPVMImplementation.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M ∧
      ∀ K : ℕ, ∃ e : ℝ, 0 < e ∧
        PurePVMScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e ∧
        MixedPVMScoreGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e ∧
        PurePVMTVGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e ∧
        MixedPVMTVGap.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} M K e :=
  Results.PVM.exists_qualitative_gap d hd

/-! ## Image-volume bound and strong near-SWAP conclusions -/

section ImageVolume

theorem reference_polynomial_image_volume : PolynomialImageVolumeBound :=
  DirectVolume.polynomialImageVolumeBound

theorem reference_polynomial_image_volume_constant :
    PolynomialImageVolumeBoundWith (804 * 560) :=
  DirectVolume.polynomialImageVolumeBoundWith

theorem reference_strong_restricted_haar :
    ∃ C : ℝ, 21 ≤ C ∧ StrongRestrictedHaarBound C :=
  NLQCLean.exists_strongRestrictedHaarBound

theorem reference_strong_restricted_diamond_haar :
    ∃ C : ℝ, 21 ≤ C ∧
      StrongRestrictedDiamondHaarBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} C :=
  NLQCLean.exists_strongRestrictedDiamondHaarBound

theorem reference_strong_universal_resource :
    ∃ c : ℝ, 0 < c ∧ StrongUniversalResourceBound c :=
  NLQCLean.exists_strongUniversalResourceBound

theorem reference_strong_universal_diamond_resource :
    ∃ c : ℝ, 0 < c ∧
      StrongUniversalDiamondResourceBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} c :=
  NLQCLean.exists_strongUniversalDiamondResourceBound

theorem reference_strong_universal_qubits :
    ∃ b : ℝ, 0 ≤ b ∧ StrongUniversalQubitBound b :=
  NLQCLean.exists_strongUniversalQubitBound

theorem reference_strong_universal_diamond_qubits :
    ∃ b : ℝ, 0 ≤ b ∧
      StrongUniversalDiamondQubitBound.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} b :=
  NLQCLean.exists_strongUniversalDiamondQubitBound

end ImageVolume

/-! ## Full-group and almost-every families -/

#check @Results.Unitary.exists_full_group_score_haar_bound
#check @Results.Unitary.exists_full_group_resource_bound
#check @Results.Unitary.exists_full_group_qubit_bound
#check @Results.Unitary.exists_full_group_diamond_haar_bound
#check @Results.Unitary.exists_full_group_diamond_resource_bound
#check @Results.Unitary.exists_full_group_diamond_qubit_bound
#check @Results.PVM.exists_full_group_score_haar_bound
#check @Results.PVM.exists_full_group_tv_haar_bound
#check @Results.PVM.exists_universal_resource_bound
#check @Results.PVM.exists_universal_qubit_bound

#check @Results.Unitary.exists_ae_forbidden_error_threshold
#check @Results.PVM.exists_ae_forbidden_error_threshold
#check @exists_ae_forbidden_error_constant
#check @exists_ae_resource_constant
#check @Results.Unitary.exists_ae_resource_bound
#check @Results.Unitary.exists_ae_diamond_resource_bound
#check @Results.PVM.exists_ae_resource_bound
#check @Results.PVM.exists_ae_tv_resource_bound
#check @Results.Unitary.exists_ae_physical_resource_bound
#check @Results.PVM.exists_ae_physical_resource_bound
#check @Results.Unitary.exists_ae_qubit_bound
#check @Results.Unitary.exists_ae_diamond_qubit_bound
#check @Results.PVM.exists_ae_qubit_bound
#check @Results.PVM.exists_ae_tv_qubit_bound
#check @Results.Unitary.ae_no_finite_exact_implementation
#check @Results.PVM.ae_no_finite_exact_implementation

/-! ## Unconditional floors -/

section Floors

variable {ιA ιB ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq εA] [DecidableEq εB] [Nonempty ιA] [Nonempty ιB]

theorem reference_pure_swap_footprint_floor
    (P : PureProtocol ιA ιA ρA ρB κA κB μA μB ιA ιA εA εB)
    {K : ℕ} {ε : ℝ} (hK : HasFootprint K P.resource μA μB)
    (hscore : 1 - ε ≤ scoreU (swapUnitary ιA) P.operationalChannel) :
    (Fintype.card (ιA × ιA) : ℝ) * (1 - ε) ≤ K :=
  Results.Unitary.pure_swap_footprint_floor P hK hscore

theorem reference_mixed_swap_footprint_floor {n : ℕ} (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ) (VB : Matrix (κB × μB) (ιA × ρB) ℂ)
    (DA : Matrix (ιA × εA) (κA × μB) ℂ) (DB : Matrix (ιA × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB) (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    {K R : ℕ} {ε : ℝ} (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    (hscore : 1 - ε ≤ scoreU (swapUnitary ιA) (m.mixedChannel VA VB DA DB)) :
    (Fintype.card (ιA × ιA) : ℝ) * (1 - ε) ≤ K :=
  Results.Unitary.mixed_swap_footprint_floor m VA VB DA DB hVA hVB hDA hDB hR hK hscore

theorem reference_pure_pvm_footprint_floor
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB
      (ιA × ιB) (ιA × ιB) εA εB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hM : IsIsometry M)
    {K : ℕ} {ε : ℝ} (hK : HasFootprint K P.resource μA μB)
    (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hscore : 1 - ε ≤ scorePVM M P.operationalChannel) :
    (Fintype.card (ιA × ιB) : ℝ) * (1 - ε) ^ 2 ≤ K :=
  Results.PVM.pure_footprint_floor P M hM hK hε hscore

theorem reference_mixed_pvm_footprint_floor {n : ℕ} (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (ιA × ρA) ℂ)
    (VB : Matrix (κB × μB) (ιB × ρB) ℂ)
    (DA : Matrix ((ιA × ιB) × εA) (κA × μB) ℂ)
    (DB : Matrix ((ιA × ιB) × εB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hM : IsIsometry M)
    {K R : ℕ} {ε : ℝ} (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hscore : 1 - ε ≤ scorePVM M (m.mixedChannel VA VB DA DB)) :
    (Fintype.card (ιA × ιB) : ℝ) * (1 - ε) ^ 2 ≤ K :=
  Results.PVM.mixed_footprint_floor m VA VB DA DB hVA hVB hDA hDB M hM hR hK hε hscore

end Floors


/-! ## Expanded semantic and external contracts -/

#print PureProtocol
#print MixedResource
#print HasFootprint
#print MixedResource.schmidtNumberLE
#print scoreU
#print diamondError
#print scorePVM
#print pvmTVError
#print unitaryHaar
#print pureReachable
#print mixedReachable
#print pureDiamondReachable
#print mixedDiamondReachable
#print purePVMReachable
#print mixedPVMReachable
#print purePVMTVReachable
#print mixedPVMTVReachable
#print SemialgebraicProjectionTheorem
#print PolynomialImageVolumeBound
#print StrongRestrictedHaarBound

/-! ## Axiom surface of public results -/

#print axioms reference_unitary_exact_impossibility
#print axioms reference_unitary_qualitative_gap
#print axioms reference_unitary_qualitative_diamond_gap
#print axioms reference_pvm_qualitative_gap
#print axioms reference_polynomial_image_volume
#print axioms reference_strong_restricted_haar
#print axioms reference_strong_universal_resource
#print axioms reference_pure_swap_footprint_floor
#print axioms reference_mixed_swap_footprint_floor
#print axioms reference_pure_pvm_footprint_floor
#print axioms reference_mixed_pvm_footprint_floor
#print axioms Results.Unitary.exists_full_group_score_haar_bound
#print axioms Results.PVM.exists_full_group_score_haar_bound
#print axioms exists_ae_resource_constant
#print axioms Results.Unitary.ae_no_finite_exact_implementation

end NLQCTests

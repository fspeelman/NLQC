import NLQCLean.Results.Unitary
import NLQCLean.Results.PVM
import NLQCLean.Models.ChargedProtocolExamples
import NLQCLean.Models.ClassicalCommunication.FiniteInstruments
import NLQCLean.Models.ClassicalCommunication.FiniteSupport
import NLQCLean.Models.ClassicalCommunication.HermitianMomentSupport
import NLQCLean.Arithmetic.PolynomialBoundary

/-!
# Robust companion proof boundaries

Full types expose all model, error and external premises. Guards reject new
axioms. These tests certify only the proved charged, spectral, finite-Kraus,
convexity and polynomial-boundary statements, not the incomplete LOSCC/Borel,
Haar-generic or effective-arithmetic extensions.
-/

set_option pp.deepTerms true
set_option pp.universes false
set_option format.width 120

namespace NLQCTests

open NLQCLean Matrix
open scoped Topology

set_option pp.universes true in
#check @NLQCLean.exists_unitaryScoreMaximum_protocol

/-- info: 'NLQCLean.exists_unitaryScoreMaximum_protocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_unitaryScoreMaximum_protocol

set_option pp.universes true in
#check @NLQCLean.exists_pvmScoreMaximum_protocol

/-- info: 'NLQCLean.exists_pvmScoreMaximum_protocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_pvmScoreMaximum_protocol

set_option pp.universes true in
#check @NLQCLean.unitaryScoreDeficit_eq_zero_iff

/-- info: 'NLQCLean.unitaryScoreDeficit_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.unitaryScoreDeficit_eq_zero_iff

set_option pp.universes true in
#check @NLQCLean.pvmScoreDeficit_eq_zero_iff

/-- info: 'NLQCLean.pvmScoreDeficit_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.pvmScoreDeficit_eq_zero_iff

set_option pp.universes true in
#check @NLQCLean.exists_general_target_unitary_gap_of_no_finite_exact

/-- info: 'NLQCLean.exists_general_target_unitary_gap_of_no_finite_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_general_target_unitary_gap_of_no_finite_exact

set_option pp.universes true in
#check @NLQCLean.exists_general_target_pvm_gap_of_no_finite_exact

/-- info: 'NLQCLean.exists_general_target_pvm_gap_of_no_finite_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.exists_general_target_pvm_gap_of_no_finite_exact

set_option pp.universes true in
#check @NLQCLean.ae_general_target_unitary_gap

/-- info: 'NLQCLean.ae_general_target_unitary_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ae_general_target_unitary_gap

set_option pp.universes true in
#check @NLQCLean.ae_general_target_pvm_gap

/-- info: 'NLQCLean.ae_general_target_pvm_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ae_general_target_pvm_gap

set_option pp.universes true in
#check @NLQCLean.PureProtocol.unitary_spectral_floor

/-- info: 'NLQCLean.PureProtocol.unitary_spectral_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PureProtocol.unitary_spectral_floor

set_option pp.universes true in
#check @NLQCLean.MixedResource.unitary_spectral_floor

/-- info: 'NLQCLean.MixedResource.unitary_spectral_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.MixedResource.unitary_spectral_floor

set_option pp.universes true in
#check @NLQCLean.PureProtocol.pvm_spectral_allocation

/-- info: 'NLQCLean.PureProtocol.pvm_spectral_allocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PureProtocol.pvm_spectral_allocation

set_option pp.universes true in
#check @NLQCLean.MixedResource.pvm_spectral_allocation

/-- info: 'NLQCLean.MixedResource.pvm_spectral_allocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.MixedResource.pvm_spectral_allocation

set_option pp.universes true in
#check @NLQCLean.PureProtocol.pvm_exact_schmidt_rank_floor

/-- info: 'NLQCLean.PureProtocol.pvm_exact_schmidt_rank_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PureProtocol.pvm_exact_schmidt_rank_floor

set_option pp.universes true in
#check @NLQCLean.schmidtMass_swapUnitary_eq_min

/-- info: 'NLQCLean.schmidtMass_swapUnitary_eq_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.schmidtMass_swapUnitary_eq_min

set_option pp.universes true in
#check @NLQCLean.isIsometry_generalizedBellFinMatrix

/-- info: 'NLQCLean.isIsometry_generalizedBellFinMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.isIsometry_generalizedBellFinMatrix

set_option pp.universes true in
#check @NLQCLean.PurePVMUniversalScore.cubic_qubit_floor

/-- info: 'NLQCLean.PurePVMUniversalScore.cubic_qubit_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PurePVMUniversalScore.cubic_qubit_floor

set_option pp.universes true in
#check @NLQCLean.MixedPVMUniversalScore.cubic_qubit_floor

/-- info: 'NLQCLean.MixedPVMUniversalScore.cubic_qubit_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.MixedPVMUniversalScore.cubic_qubit_floor

set_option pp.universes true in
#check @Results.PVM.pure_universal_tv_cubic_floor
set_option pp.universes true in
#check @Results.PVM.mixed_universal_tv_qubit_floor

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteKrausInstrument.channel_completelyPositive

/-- info: 'NLQCLean.ClassicalCommunication.FiniteKrausInstrument.channel_completelyPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteKrausInstrument.channel_completelyPositive

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.FiniteKrausInstrument.channel_eq_channelOf_dilation

/-- info: 'NLQCLean.ClassicalCommunication.FiniteKrausInstrument.channel_eq_channelOf_dilation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.FiniteKrausInstrument.channel_eq_channelOf_dilation

set_option pp.universes true in
#check @ClassicalCommunication.FiniteKrausInstrument.channel_ofStinespring
set_option pp.universes true in
#check @ClassicalCommunication.copyLabel_isometry

/-- info: 'NLQCLean.ClassicalCommunication.FiniteKrausInstrument.channel_ofStinespring' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClassicalCommunication.FiniteKrausInstrument.channel_ofStinespring

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.exists_finite_moment_support

/-- info: 'NLQCLean.ClassicalCommunication.exists_finite_moment_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.exists_finite_moment_support

set_option pp.universes true in
#check @ClassicalCommunication.exists_normalized_hermitian_marginal_score_support

/-- info: 'NLQCLean.ClassicalCommunication.exists_normalized_hermitian_marginal_score_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ClassicalCommunication.exists_normalized_hermitian_marginal_score_support

set_option pp.universes true in
#check @ClassicalCommunication.moment_alphabet_le_twice_square
set_option pp.universes true in
#check @ClassicalCommunication.alphabet_le_of_moment_support_bound

set_option pp.universes true in
#check @NLQCLean.ClassicalCommunication.charged_message_footprint_le

/-- info: 'NLQCLean.ClassicalCommunication.charged_message_footprint_le' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.ClassicalCommunication.charged_message_footprint_le

set_option pp.universes true in
#check @NLQCLean.PolynomialSignDNF.exists_nonzero_polynomial_zero_of_mem_frontier

/-- info: 'NLQCLean.PolynomialSignDNF.exists_nonzero_polynomial_zero_of_mem_frontier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NLQCLean.PolynomialSignDNF.exists_nonzero_polynomial_zero_of_mem_frontier

set_option pp.universes true in
#check @PolynomialSignDNF.exists_nonzero_polynomial_zero_of_measure_eq_zero

/-- info: 'NLQCLean.PolynomialSignDNF.exists_nonzero_polynomial_zero_of_measure_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PolynomialSignDNF.exists_nonzero_polynomial_zero_of_measure_eq_zero

-- A protocol witnesses the optimum.
example {d K : ℕ} (hd : 2 ≤ d) (hK : 1 ≤ K)
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    ∃ s : Fin 8 → ℕ, ∃ P : FinProtocol d s,
      P.HasFootprint K ∧ scoreU U P.operationalChannel = unitaryScoreMaximum U K :=
  Results.Unitary.exists_score_maximum_protocol hd hK U

example {d K : ℕ} (hd : 2 ≤ d) (hK : 1 ≤ K)
    (U : unitaryGroup (Fin d × Fin d) ℂ) (e : ℝ) :
    U ∈ mixedReachable d K e ↔
      1 - e ≤ unitaryScoreMaximum (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K :=
  mem_mixedReachable_iff_le_unitaryScoreMaximum hd hK U e

example {d K : ℕ} (hd : 2 ≤ d) (hK : 1 ≤ K)
    (M : unitaryGroup (Fin d × Fin d) ℂ) (e : ℝ) :
    M ∈ mixedPVMReachable d K e ↔
      1 - e ≤ pvmScoreMaximum (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) K :=
  mem_mixedPVMReachable_iff_le_pvmScoreMaximum hd hK M e

example {d : ℕ} (hd : 2 ≤ d) (e : ℝ) :
    pureReachable d 0 e = ∅ := pureReachable_zero_budget hd e

example {d : ℕ} (hd : 2 ≤ d) (e : ℝ) :
    mixedPVMReachable d 0 e = ∅ := mixedPVMReachable_zero_budget hd e

example {d : ℕ} (hd : 2 ≤ d) :
    (1 : unitaryGroup (Fin d × Fin d) ℂ) ∈ pureReachable d 1 0 :=
  identity_mem_pureReachable_one hd

example {d : ℕ} (hd : 2 ≤ d) :
    (1 : unitaryGroup (Fin d × Fin d) ℂ) ∈ mixedReachable d 1 0 :=
  identity_mem_mixedReachable_one hd

-- The saturated mass cannot grow beyond one even if K exceeds full rank.
example {K : ℕ} (hK : 4 ≤ K) :
    schmidtMass K (normalizedLabChoiMatrix (swapUnitary (Fin 2))) = 1 := by
  rw [schmidtMass_swapUnitary_eq_min]
  simp only [Fintype.card_prod, Fintype.card_fin]
  apply min_eq_right
  have hk : (4 : ℝ) ≤ K := by exact_mod_cast hK
  norm_num
  linarith

example : IsIsometry (generalizedBellFinMatrix 2) :=
  isIsometry_generalizedBellFinMatrix 2

example {K : ℕ} (h : PurePVMUniversalScore 2 K 0) : 8 ≤ K := by
  have hf := Results.PVM.pure_universal_cubic_floor (by norm_num : 0 < 2)
    (by norm_num : 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1) h
  norm_num at hf
  exact_mod_cast hf

example {n K : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (h : MixedPVMUniversalScore (2 ^ n) K ε) :
    3 * (n : ℝ) - 2 ≤ Real.logb 2 K :=
  Results.PVM.mixed_universal_qubit_floor hε0 hε h

example (d r mA mB aA aB K : ℕ) (hmA : 1 ≤ mA) (hmB : 1 ≤ mB)
    (hK : r * mA * mB ≤ K)
    (haA : aA ≤ 2 * d ^ 2 * r ^ 2) (haB : aB ≤ 2 * d ^ 2 * r ^ 2) :
    r * (mA * aA) * (mB * aB) ≤ 4 * d ^ 4 * K ^ 5 :=
  ClassicalCommunication.charged_message_footprint_le d r mA mB aA aB K
    hmA hmB hK haA haB

-- A zero defining polynomial has constant sign, never a spurious boundary root.
example (n : ℕ) (x : RealEuclidean n) :
    ∀ᶠ y in 𝓝 x,
      (PolynomialSignAtom.Holds (⟨0, .zero⟩ : PolynomialSignAtom n) y ↔
        PolynomialSignAtom.Holds (⟨0, .zero⟩ : PolynomialSignAtom n) x) :=
  PolynomialSignAtom.eventually_holds_iff ⟨0, .zero⟩ x (Or.inl rfl)

end NLQCTests

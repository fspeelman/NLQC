import NLQCLean.Models.ChargedCompactProtocols
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Raw real coordinates of sharply compressed charged protocols

The coordinate count is the real dimension of the five physical
blocks. The quadratic estimate uses the rank/message product and the sharp
private-space and discarded-environment bounds, not the larger rectangular
box of charged shapes. It is not a rational polynomial-format certificate.
-/

namespace NLQCLean

/-- Two real coordinates for each complex entry of the resource, the two
encoders and the two final isometries, in that order. -/
def physicalRawRealCoordinateCount (d : ℕ) (s : Fin 8 → ℕ) : ℕ :=
  2 * (s 0 * s 1) +
    2 * ((s 2 * s 4) * (d * s 0)) +
    2 * ((s 3 * s 5) * (d * s 1)) +
    2 * ((d * s 6) * (s 2 * s 5)) +
    2 * ((d * s 7) * (s 3 * s 4))

/-- This entry count is the dimension of the existing physical-block space,
with no ancillary witness vector or extra target coordinate included. -/
theorem finrank_physicalBlocks_eq_rawRealCoordinateCount (d : ℕ) (s : Fin 8 → ℕ) :
    Module.finrank ℝ (PhysicalBlocks d s) = physicalRawRealCoordinateCount d s := by
  rw [finrank_real_of_complex]
  simp only [PhysicalBlocks, Module.finrank_prod, Module.finrank_pi, Module.finrank_matrix,
    Module.finrank_self, Fintype.card_prod, Fintype.card_fin, physicalRawRealCoordinateCount]
  ring

/-- The decoder inputs and minimal discarded environments stay linear in the
charged product, even when the individual message dimensions differ. -/
theorem sharp_qubit_decoder_dimensions
    {K r kA kB mA mB eA eB : ℕ} (hcharge : r * mA * mB ≤ K)
    (hkA : kA ≤ 2 * r * mA) (hkB : kB ≤ 2 * r * mB)
    (heA : eA ≤ 2 * kA * mB) (heB : eB ≤ 2 * kB * mA) :
    kA * mB ≤ 2 * K ∧ kB * mA ≤ 2 * K ∧ eA ≤ 4 * K ∧ eB ≤ 4 * K := by
  have hqa : kA * mB ≤ 2 * K := by
    calc
      kA * mB ≤ (2 * r * mA) * mB := Nat.mul_le_mul_right mB hkA
      _ ≤ 2 * K := by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hcharge
  have hqb : kB * mA ≤ 2 * K := by
    calc
      kB * mA ≤ (2 * r * mB) * mA := Nat.mul_le_mul_right mA hkB
      _ ≤ 2 * K := by
        simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
          Nat.mul_le_mul_left 2 hcharge
  refine ⟨hqa, hqb, ?_, ?_⟩
  · calc
      eA ≤ 2 * (kA * mB) := by simpa only [Nat.mul_assoc] using heA
      _ ≤ 2 * (2 * K) := Nat.mul_le_mul_left 2 hqa
      _ = 4 * K := by ring
  · calc
      eB ≤ 2 * (kB * mA) := by simpa only [Nat.mul_assoc] using heB
      _ ≤ 2 * (2 * K) := Nat.mul_le_mul_left 2 hqb
      _ = 4 * K := by ring

/-- The five raw coordinate contributions are bounded by respectively
`2`, `8`, `8`, `32` and `32` times the square of the charged budget. -/
theorem sharp_qubit_rawRealCoordinateCount_le
    {K r kA kB mA mB eA eB : ℕ} (hmA : 0 < mA) (hmB : 0 < mB)
    (hcharge : r * mA * mB ≤ K)
    (hkA : kA ≤ 2 * r * mA) (hkB : kB ≤ 2 * r * mB)
    (heA : eA ≤ 2 * kA * mB) (heB : eB ≤ 2 * kB * mA) :
    physicalRawRealCoordinateCount 2 ![r, r, kA, kB, mA, mB, eA, eB] ≤ 82 * K ^ 2 := by
  have hrmA : r * mA ≤ K := (Nat.le_mul_of_pos_right _ hmB).trans hcharge
  have hrmB : r * mB ≤ K := by
    apply (Nat.le_mul_of_pos_right _ hmA).trans
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hcharge
  have hr : r ≤ K := (Nat.le_mul_of_pos_right _ hmA).trans hrmA
  obtain ⟨hqa, hqb, hea, heb⟩ := sharp_qubit_decoder_dimensions hcharge hkA hkB heA heB
  have hresource : 2 * (r * r) ≤ 2 * (K * K) :=
    Nat.mul_le_mul_left 2 (Nat.mul_le_mul hr hr)
  have hencA : 2 * ((kA * mA) * (2 * r)) ≤ 8 * (K * K) := by
    calc
      _ ≤ 2 * (((2 * r * mA) * mA) * (2 * r)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right (2 * r) (Nat.mul_le_mul_right mA hkA))
      _ = 8 * ((r * mA) * (r * mA)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 8 (Nat.mul_le_mul hrmA hrmA)
  have hencB : 2 * ((kB * mB) * (2 * r)) ≤ 8 * (K * K) := by
    calc
      _ ≤ 2 * (((2 * r * mB) * mB) * (2 * r)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right (2 * r) (Nat.mul_le_mul_right mB hkB))
      _ = 8 * ((r * mB) * (r * mB)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 8 (Nat.mul_le_mul hrmB hrmB)
  have hdecA : 2 * ((2 * eA) * (kA * mB)) ≤ 32 * (K * K) := by
    calc
      _ ≤ 2 * ((2 * (4 * K)) * (2 * K)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hea) hqa)
      _ = _ := by ring
  have hdecB : 2 * ((2 * eB) * (kB * mA)) ≤ 32 * (K * K) := by
    calc
      _ ≤ 2 * ((2 * (4 * K)) * (2 * K)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul (Nat.mul_le_mul_left 2 heb) hqb)
      _ = _ := by ring
  change 2 * (r * r) + 2 * ((kA * mA) * (2 * r)) +
    2 * ((kB * mB) * (2 * r)) + 2 * ((2 * eA) * (kA * mB)) +
    2 * ((2 * eB) * (kB * mA)) ≤ 82 * K ^ 2
  calc
    _ ≤ 2 * (K * K) + 8 * (K * K) + 8 * (K * K) +
        32 * (K * K) + 32 * (K * K) := by omega
    _ = _ := by ring

section ArbitraryRegisters

variable {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

/-- Every original qubit protocol has a channel-preserving physical
representative on at most `82 K²` raw real coordinates. The retained support
dimensions obey the sharp inequalities; the statement does not enlarge the
Schmidt rank to the original resource-register dimensions. -/
theorem PureProtocol.exists_qubit_compressed_coordinate_certificate
    (P : PureProtocol (Fin 2) (Fin 2) ρA ρB κA κB μA μB (Fin 2) (Fin 2) εA εB)
    {K : ℕ} (hK : P.HasFootprint K) :
    ∃ r kA kB eA eB : ℕ, r = schmidtRank P.resource ∧
      r * Fintype.card μA * Fintype.card μB ≤ K ∧
      kA ≤ 2 * r * Fintype.card μA ∧ kB ≤ 2 * r * Fintype.card μB ∧
      eA ≤ 2 * kA * Fintype.card μB ∧ eB ≤ 2 * kB * Fintype.card μA ∧
      ∃ Q : FinProtocol 2
        ![r, r, kA, kB, Fintype.card μA, Fintype.card μB, eA, eB],
        Q.HasFootprint K ∧ P.operationalChannel = Q.operationalChannel ∧
        Module.finrank ℝ (PhysicalBlocks 2
          ![r, r, kA, kB, Fintype.card μA, Fintype.card μB, eA, eB]) ≤ 82 * K ^ 2 := by
  obtain ⟨r, kA, kB, eA, eB, hr, hkA, hkB, heA, heB, Q, hchan⟩ :=
    P.exists_compressed_forward
  have hrpos : 0 < r := by
    have h := Q.resource_unit.card_pos
    simp only [Fintype.card_prod, Fintype.card_fin] at h
    exact Nat.pos_of_mul_pos_right h
  have hencA : 2 * r ≤ kA * Fintype.card μA := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Q.encA_isometry.card_le
  have hencB : 2 * r ≤ kB * Fintype.card μB := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Q.encB_isometry.card_le
  have hmA : 0 < Fintype.card μA :=
    Nat.pos_of_mul_pos_left ((Nat.mul_pos (by omega) hrpos).trans_le hencA)
  have hmB : 0 < Fintype.card μB :=
    Nat.pos_of_mul_pos_left ((Nat.mul_pos (by omega) hrpos).trans_le hencB)
  have hcharge : r * Fintype.card μA * Fintype.card μB ≤ K := by
    simpa only [hr] using (hasFootprint_iff K P.resource).mp hK
  let R : FinProtocol 2
      ![r, r, kA, kB, Fintype.card μA, Fintype.card μB, eA, eB] :=
    Q.reindex (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
      (Fintype.equivFin μA).symm (Fintype.equivFin μB).symm (Equiv.refl _) (Equiv.refl _)
  refine ⟨r, kA, kB, eA, eB, hr, hcharge, hkA, hkB, heA, heB, R, ?_, ?_, ?_⟩
  · exact R.hasFootprint_of_support_charge hcharge
  · exact hchan.trans (Q.operationalChannel_reindex (Equiv.refl _) (Equiv.refl _)
      (Equiv.refl _) (Equiv.refl _) (Fintype.equivFin μA).symm (Fintype.equivFin μB).symm
      (Equiv.refl _) (Equiv.refl _)).symm
  · rw [finrank_physicalBlocks_eq_rawRealCoordinateCount]
    exact sharp_qubit_rawRealCoordinateCount_le hmA hmB hcharge hkA hkB heA heB

end ArbitraryRegisters

/-- A score-maximizing protocol can be replaced by one attaining the
same score and deficit on at most `82 K²` raw real strategy coordinates.
The channel is preserved, not merely its score at the selected unitary. -/
theorem exists_qubit_unitaryScoreMaximum_coordinate_certificate
    {K : ℕ} (hK : 1 ≤ K) (U : Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ) :
    ∃ s : Fin 8 → ℕ, ∃ P : FinProtocol 2 s,
      P.HasFootprint K ∧
      scoreU (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) P.operationalChannel =
        unitaryScoreMaximum (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) K ∧
      ∃ t : Fin 8 → ℕ, ∃ Q : FinProtocol 2 t,
        Q.HasFootprint K ∧ P.operationalChannel = Q.operationalChannel ∧
        scoreU (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) Q.operationalChannel =
          unitaryScoreMaximum (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) K ∧
        unitaryScoreDeficit (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) K =
          1 - scoreU (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) Q.operationalChannel ∧
        Module.finrank ℝ (PhysicalBlocks 2 t) ≤ 82 * K ^ 2 := by
  obtain ⟨s, P, hP, hscore⟩ := exists_unitaryScoreMaximum_protocol (by decide) hK
    (U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
  obtain ⟨r, kA, kB, eA, eB, _, _, _, _, _, _, Q, hQ, hchan, hcoords⟩ :=
    P.exists_qubit_compressed_coordinate_certificate hP
  let t : Fin 8 → ℕ := ![r, r, kA, kB, Fintype.card (Fin (s 4)), Fintype.card (Fin (s 5)), eA, eB]
  refine ⟨s, P, hP, hscore, t, Q, hQ, hchan, ?_, ?_, hcoords⟩
  · rw [← hchan]
    exact hscore
  · rw [unitaryScoreDeficit, ← hscore, hchan]

end NLQCLean

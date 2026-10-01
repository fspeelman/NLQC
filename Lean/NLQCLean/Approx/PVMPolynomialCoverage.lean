import NLQCLean.Approx.PVMPolynomialWitnessFamily
import NLQCLean.Approx.PVMWitnessCoverage
import NLQCLean.Approx.PVMRankFloor

/-!
# Physical coverage by fixed-format PVM polynomial witnesses

Accurate pure and finite-mixed PVM protocols first discharge the
coordinate floor from the unconditional PVM rank bound, then enter one member
of the fixed-format polynomial witness family.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

section PhysicalCoverage

variable {d : ℕ} {ρA ρB κA κB μA μB eA eB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB]
variable [Fintype μA] [Fintype μB] [Fintype eA] [Fintype eB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq eA] [DecidableEq eB]

/-- An accurate arbitrary-finite-register pure protocol lies in a bounded
polynomial witness family.  The coordinate floor is a consequence of its
PVM score rather than an additional premise. -/
theorem PureProtocol.exists_pvm_polynomial_witness
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      (Fin d × Fin d) (Fin d × Fin d) eA eB)
    (hd : 0 < d) {K : ℕ} {ε : ℝ}
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hM : IsIsometry M) (hK : NLQCLean.HasFootprint K P.resource μA μB)
    (hε : 0 ≤ ε ∧ ε ≤ 1 / 2)
    (hscore : 1 - ε ≤ scorePVM M P.operationalChannel) :
    ∃ hfloor : d ^ 2 ≤ 4 * K, ∃ s : PVMReverseShape d K,
      ∃ y ∈ (PVMReverseBlocks.witnessFormat s hd hfloor (2 * Real.sqrt ε)).source,
        ‖(PVMReverseBlocks.coordinateRawOverlapPolynomial s hd hfloor).eval y -
            overlapOutputCoordinates d Mᴴ‖ ≤ 2 * (d : ℝ) * Real.sqrt ε := by
  let : NeZero d := ⟨by omega⟩
  have hεone : 0 ≤ ε ∧ ε ≤ 1 := ⟨hε.1, hε.2.trans (by norm_num)⟩
  have hquarter := P.quarter_card_le_of_pvm_score M hM hK hεone hε.2 hscore
  have hfloor_real : (d : ℝ) ^ 2 ≤ 4 * (K : ℝ) := by
    have hquarter' : (d : ℝ) ^ 2 / 4 ≤ (K : ℝ) := by
      simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two] using hquarter
    nlinarith
  have hfloor : d ^ 2 ≤ 4 * K := by exact_mod_cast hfloor_real
  obtain ⟨s, x, hx, _, hclose, _, _, hdef⟩ :=
    P.exists_pvm_reverse_witness_approximation hd M hM hK hεone hscore
  have hdef' :
      (d : ℝ) ^ 2 - ‖PVMReverseBlocks.overlap x‖ ^ 2 ≤
        (d : ℝ) ^ 2 * (2 * Real.sqrt ε) ^ 2 := by
    simpa only [mul_pow, Real.sq_sqrt hε.1, show (2 : ℝ) ^ 2 = 4 by norm_num] using hdef
  obtain ⟨y, hy, hdist⟩ :=
    PVMReverseBlocks.exists_mem_witnessFormat_source_approximation
      s hd hfloor (2 * Real.sqrt ε) hx hdef' Mᴴ hclose
  refine ⟨hfloor, s, y, hy, ?_⟩
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hdist

/-- Finite mixed resources obey the same polynomial coverage statement.
Component selection retains the common protocol maps and the single charged
Schmidt-number/message footprint. -/
theorem MixedResource.exists_pvm_polynomial_witness
    {n : ℕ} (m : MixedResource ρA ρB n)
    (VA : Matrix (κA × μA) (Fin d × ρA) ℂ)
    (VB : Matrix (κB × μB) (Fin d × ρB) ℂ)
    (DA : Matrix ((Fin d × Fin d) × eA) (κA × μB) ℂ)
    (DB : Matrix ((Fin d × Fin d) × eB) (κB × μA) ℂ)
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (hDA : IsIsometry DA) (hDB : IsIsometry DB)
    (hd : 0 < d) {K R : ℕ} {ε : ℝ}
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (hM : IsIsometry M)
    (hR : m.schmidtNumberLE R)
    (hK : R * Fintype.card μA * Fintype.card μB ≤ K)
    (hε : 0 ≤ ε ∧ ε ≤ 1 / 2)
    (hscore : 1 - ε ≤ scorePVM M (m.mixedChannel VA VB DA DB)) :
    ∃ hfloor : d ^ 2 ≤ 4 * K, ∃ s : PVMReverseShape d K,
      ∃ y ∈ (PVMReverseBlocks.witnessFormat s hd hfloor (2 * Real.sqrt ε)).source,
        ‖(PVMReverseBlocks.coordinateRawOverlapPolynomial s hd hfloor).eval y -
            overlapOutputCoordinates d Mᴴ‖ ≤ 2 * (d : ℝ) * Real.sqrt ε := by
  obtain ⟨k, hk⟩ := m.exists_component_scorePVM_ge VA VB DA DB M
  let P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB
      (Fin d × Fin d) (Fin d × Fin d) eA eB :=
    ⟨m.component k, m.component_unit k, VA, VB, hVA, hVB, DA, DB, hDA, hDB⟩
  have hPK : NLQCLean.HasFootprint K P.resource μA μB :=
    ⟨R, Fintype.card μA, Fintype.card μB, hK, hR k, le_rfl, le_rfl⟩
  exact P.exists_pvm_polynomial_witness hd M hM hPK hε (hscore.trans hk)

end PhysicalCoverage

end NLQCLean

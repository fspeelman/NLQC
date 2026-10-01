import NLQCLean.Approx.GenericSchmidtRank
import NLQCLean.Models.DiamondReachability

/-!
# Target-dependent generic spectral thresholds

Full Schmidt rank gives a positive lower bound on every squared Schmidt
coefficient. The resulting threshold depends only on the fixed target, before
the footprint and error are quantified. reachable sets retain arbitrary
finite original registers, both charged messages, and common-map finite mixing.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius

/-- Almost every normalized unitary Choi vector has a positive smallest weight. -/
theorem ae_unitary_pos_schmidtWeight_lower_bound (d : ℕ) [NeZero d] :
    ∀ᵐ (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
      ∃ t : ℝ, 0 < t ∧ ∀ i,
        t ≤ schmidtWeights (normalizedLabChoiMatrix
          (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) i := by
  filter_upwards [ae_unitary_operatorSchmidtRank_full d] with U hU
  apply exists_pos_schmidtWeight_lower_bound_of_full_rank
  rw [rank_normalizedLabChoiMatrix_eq]
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using hU

/-- Almost every ordered basis has one positive lower bound for all column weights. -/
theorem ae_pvm_pos_uniform_schmidtWeight_lower_bound (d : ℕ) [NeZero d] :
    ∀ᵐ (M : Matrix.unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
      ∃ t : ℝ, 0 < t ∧ ∀ i j,
        t ≤ schmidtWeights (pvmConjugateColumnMatrix
          (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) i) j := by
  filter_upwards [ae_pvmColumnSchmidtRank_full d] with M hM
  apply exists_pos_uniform_schmidtWeight_lower_bound_of_full_rank
  intro i
  simpa only [Fintype.card_fin] using hM i

/-- The unitary smallest-weight threshold in the charged reachable set. -/
theorem unitary_full_footprint_floor_of_mem_pureReachable
    {d K : ℕ} [NeZero d] (U : Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    {ε t : ℝ}
    (ht : ∀ i, t ≤ schmidtWeights (normalizedLabChoiMatrix
      (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)) i)
    (hε : ε < t) (hreach : U ∈ pureReachable d K ε) : d ^ 2 ≤ K := by
  obtain ⟨s, P, hK, hscore⟩ := hreach
  have h := P.unitary_full_spectral_floor
    (U : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (Matrix.mem_unitaryGroup_iff'.mp U.property) hK ht hε hscore
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using h

/-- The PVM smallest-weight threshold, with the source denominator `2*d²`. -/
theorem pvm_full_footprint_floor_of_mem_purePVMReachable
    {d K : ℕ} [NeZero d] (M : Matrix.unitaryGroup (Fin d × Fin d) ℂ)
    {ε t : ℝ}
    (ht : ∀ i j, t ≤ schmidtWeights (pvmConjugateColumnMatrix
      (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) i) j)
    (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hthreshold : ε < t / (2 * Fintype.card (Fin d × Fin d)))
    (hreach : M ∈ purePVMReachable d K ε) : d ^ 3 ≤ K := by
  obtain ⟨s, P, hK, hscore⟩ := hreach
  have h := P.pvm_full_spectral_floor
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (Matrix.mem_unitaryGroup_iff'.mp M.property) hK hε ht hthreshold hscore
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_succ, pow_zero, one_mul] using h

/-- One fixed-target threshold gives the full spectral floors for all eight
score and operational-error reachable sets. -/
theorem ae_full_spectral_footprint_threshold (d : ℕ) [NeZero d] :
    ∀ᵐ (T : Matrix.unitaryGroup (Fin d × Fin d) ℂ) ∂unitaryHaar (Fin d × Fin d),
      ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ (K : ℕ) (ε : ℝ), 0 ≤ ε → ε < η →
        (T ∈ pureReachable d K ε → d ^ 2 ≤ K) ∧
        (T ∈ mixedReachable d K ε → d ^ 2 ≤ K) ∧
        (T ∈ purePVMReachable d K ε → d ^ 3 ≤ K) ∧
        (T ∈ mixedPVMReachable d K ε → d ^ 3 ≤ K) ∧
        (T ∈ pureDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K ε → d ^ 2 ≤ K) ∧
        (T ∈ mixedDiamondReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K ε → d ^ 2 ≤ K) ∧
        (T ∈ purePVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K ε → d ^ 3 ≤ K) ∧
        (T ∈ mixedPVMTVReachable.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K ε → d ^ 3 ≤ K) := by
  filter_upwards [ae_unitary_pos_schmidtWeight_lower_bound d,
    ae_pvm_pos_uniform_schmidtWeight_lower_bound d] with T hU hM
  obtain ⟨tU, htU, hwU⟩ := hU
  obtain ⟨tM, htM, hwM⟩ := hM
  have hd : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  let η := min 1 (min tU (tM / (2 * (d : ℝ) ^ 2)))
  have hη : 0 < η := lt_min (by norm_num) (lt_min htU (by positivity))
  have hη1 : η ≤ 1 := min_le_left _ _
  refine ⟨η, hη, hη1, ?_⟩
  intro K ε hε0 hε
  have hε1 : ε ≤ 1 := (hε.trans_le hη1).le
  have hεU : ε < tU :=
    hε.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεM : ε < tM / (2 * Fintype.card (Fin d × Fin d)) := by
    calc
      ε < η := hε
      _ ≤ tM / (2 * (d : ℝ) ^ 2) :=
        (min_le_right _ _).trans (min_le_right _ _)
      _ = tM / (2 * Fintype.card (Fin d × Fin d)) := by
        simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two]
  have hUS : T ∈ pureReachable d K ε → d ^ 2 ≤ K :=
    unitary_full_footprint_floor_of_mem_pureReachable T hwU hεU
  have hMS : T ∈ mixedReachable d K ε → d ^ 2 ≤ K :=
    fun h => hUS (mixedReachable_subset_pureReachable d K ε h)
  have hPS : T ∈ purePVMReachable d K ε → d ^ 3 ≤ K :=
    pvm_full_footprint_floor_of_mem_purePVMReachable T hwM ⟨hε0, hε1⟩ hεM
  have hMP : T ∈ mixedPVMReachable d K ε → d ^ 3 ≤ K :=
    fun h => hPS (mixedPVMReachable_subset_purePVMReachable d K ε h)
  exact ⟨hUS, hMS, hPS, hMP,
    fun h => hUS (pureDiamondReachable_subset_pureReachable K ε h),
    fun h => hMS (mixedDiamondReachable_subset_mixedReachable K ε h),
    fun h => hPS (purePVMTVReachable_subset_purePVMReachable K ε h),
    fun h => hMP (mixedPVMTVReachable_subset_mixedPVMReachable K ε h)⟩

end NLQCLean

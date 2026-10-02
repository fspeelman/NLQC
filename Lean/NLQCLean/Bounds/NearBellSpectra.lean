import NLQCLean.Bounds.NearBellMessages
import NLQCLean.LinearAlgebra.FlatProductTail
import NLQCLean.Approx.PVMRankFloor

/-!
# Flat column spectra near a maximally entangled basis

`bellNeighborhood d` is the set of basis unitaries within normalized Frobenius
distance `1/(4 d^{3/2})` of the generalized Bell basis, that is within
Frobenius distance `1/(4√d)`. Every column of such a basis has all squared
Schmidt coefficients in `[9/(16d), 25/(16d)]`, so an accurate protocol has
footprint at least of order `d³`. The source is `lem:bell-compression` in the
revised robust companion.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

/-- Basis unitaries near the generalized Bell basis. -/
noncomputable def bellNeighborhood (d : ℕ) [NeZero d] : Set (unitaryGroup (Fin d × Fin d) ℂ) :=
  {M | ‖(M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - generalizedBellFinMatrix d‖ ≤
    1 / (4 * Real.sqrt d)}

theorem norm_pvmConjugateColumnMatrix_sub_le {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (M N : Matrix (ιA × ιB) (ιA × ιB) ℂ) (i : ιA × ιB) :
    ‖pvmConjugateColumnMatrix M i - pvmConjugateColumnMatrix N i‖ ≤ ‖M - N‖ := by
  have hsq : ‖pvmConjugateColumnMatrix M i - pvmConjugateColumnMatrix N i‖ ^ 2 ≤
      ‖M - N‖ ^ 2 := by
    rw [frobNorm_sq, frobNorm_sq]
    calc ∑ a, ∑ b, ‖(pvmConjugateColumnMatrix M i - pvmConjugateColumnMatrix N i) a b‖ ^ 2
        = ∑ q : ιA × ιB, ‖(M - N) q i‖ ^ 2 := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          simp only [pvmConjugateColumnMatrix, Matrix.sub_apply, Matrix.of_apply, Complex.star_def]
          rw [← map_sub, Complex.norm_conj]
      _ ≤ ∑ q, ∑ j, ‖(M - N) q j‖ ^ 2 :=
          Finset.sum_le_sum fun q _ => Finset.single_le_sum (fun j _ => sq_nonneg ‖(M - N) q j‖)
            (Finset.mem_univ i)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by decide : 2 ≠ 0)).mp hsq

/-- **Flat column spectra.** -/
theorem schmidtWeights_mem_of_mem_bellNeighborhood {d : ℕ} [NeZero d]
    {M : unitaryGroup (Fin d × Fin d) ℂ} (hM : M ∈ bellNeighborhood d) (i : Fin d × Fin d)
    (j : Fin d) :
    9 / (16 * d) ≤ schmidtWeights (pvmConjugateColumnMatrix (M : Matrix _ _ ℂ) i) j ∧
      schmidtWeights (pvmConjugateColumnMatrix (M : Matrix _ _ ℂ) i) j ≤ 25 / (16 * d) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  set c := 1 / Real.sqrt d with hc
  have hc0 : 0 < c := by positivity
  have hc2 : c ^ 2 = 1 / (d : ℝ) := by
    rw [hc, div_pow, Real.sq_sqrt hd.le, one_pow]
  have hW : pvmConjugateColumnMatrix (generalizedBellFinMatrix d) i *
      (pvmConjugateColumnMatrix (generalizedBellFinMatrix d) i)ᴴ =
      ((c ^ 2 : ℝ) : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
    rw [pvmConjugateColumnMatrix_generalizedBellFinMatrix_gram, hc2]
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab]
  have hsum := sum_sq_sqrt_schmidtWeights_sub_le (pvmConjugateColumnMatrix (M : Matrix _ _ ℂ) i)
    (pvmConjugateColumnMatrix (generalizedBellFinMatrix d) i) hc0.le hW
  have hdist := norm_pvmConjugateColumnMatrix_sub_le (M : Matrix _ _ ℂ)
    (generalizedBellFinMatrix d) i
  have hball : ‖(M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - generalizedBellFinMatrix d‖ ≤
      c / 4 := by
    have := hM
    simp only [bellNeighborhood, Set.mem_ofPred_eq] at this
    rw [hc]
    calc _ ≤ 1 / (4 * Real.sqrt d) := this
      _ = 1 / Real.sqrt d / 4 := by ring
  have hj : (Real.sqrt (schmidtWeights (pvmConjugateColumnMatrix (M : Matrix _ _ ℂ) i) j) - c) ^ 2 ≤
      (c / 4) ^ 2 := by
    have h1 := Finset.single_le_sum (f := fun j => (Real.sqrt (schmidtWeights
      (pvmConjugateColumnMatrix (M : Matrix _ _ ℂ) i) j) - c) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ j)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (hdist.trans hball) 2
    exact h1.trans (hsum.trans h2)
  have habs := abs_le_of_sq_le_sq' hj (by positivity)
  set p := schmidtWeights (pvmConjugateColumnMatrix (M : Matrix _ _ ℂ) i) j
  have hp0 : 0 ≤ p := schmidtWeights_nonneg _ _
  have hsq := Real.sq_sqrt hp0
  have hlo : 3 / 4 * c ≤ Real.sqrt p := by linarith [habs.1]
  have hhi : Real.sqrt p ≤ 5 / 4 * c := by linarith [habs.2]
  have hlo2 : (3 / 4 * c) ^ 2 ≤ Real.sqrt p ^ 2 := pow_le_pow_left₀ (by positivity) hlo 2
  have hhi2 : Real.sqrt p ^ 2 ≤ (5 / 4 * c) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hhi 2
  rw [hsq, mul_pow, hc2] at hlo2 hhi2
  constructor
  · calc 9 / (16 * (d : ℝ)) = (3 / 4) ^ 2 * (1 / d) := by field_simp; norm_num
      _ ≤ p := hlo2
  · calc p ≤ (5 / 4) ^ 2 * (1 / d) := hhi2
      _ = 25 / (16 * (d : ℝ)) := by field_simp; norm_num

section Protocol

variable {ιA ιB ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ιA] [Fintype ιB] [Fintype ρA] [Fintype ρB]
variable [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB] [Fintype εA] [Fintype εB]
variable [DecidableEq ιA] [DecidableEq ιB] [DecidableEq ρA] [DecidableEq ρB]
variable [DecidableEq κA] [DecidableEq κB] [DecidableEq μA] [DecidableEq μB]
variable [DecidableEq εA] [DecidableEq εB]

/-- If every column Schmidt weight is at most `β`, the squared PVM score is
at most `K β / D`. -/
theorem PureProtocol.scorePVM_sq_le_of_column_weight_le [Nonempty ιA] [Nonempty ιB]
    (P : PureProtocol ιA ιB ρA ρB κA κB μA μB (ιA × ιB) (ιA × ιB) εA εB)
    (M : Matrix (ιA × ιB) (ιA × ιB) ℂ) (hM : IsIsometry M)
    {K : ℕ} (hK : NLQCLean.HasFootprint K P.resource μA μB) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : ∀ i j, schmidtWeights (pvmConjugateColumnMatrix M i) j ≤ β) :
    (scorePVM M P.operationalChannel) ^ 2 ≤ (K : ℝ) * β / Fintype.card (ιA × ιB) := by
  refine (P.scorePVM_sq_le_schmidtMass_pvmProjected M hK).trans ?_
  rw [pvmProjectedDilation, schmidtMass_tensorChoiMatrix_flag_mul_adjoint, mul_div_assoc,
    div_eq_mul_inv]
  refine topWeightMass_le_mul K _ (mul_nonneg hβ0 (inv_nonneg.mpr (Nat.cast_nonneg _)))
    fun p => ?_
  have hA0 := schmidtWeights_nonneg (resourceMatrix (pvmEnvironment M P.globalIsometry p.2)) p.1.1
  have hA1 : schmidtWeights (resourceMatrix (pvmEnvironment M P.globalIsometry p.2)) p.1.1 ≤ 1 := by
    have hw := schmidtWeight_le_norm_sq (resourceMatrix (pvmEnvironment M P.globalIsometry p.2)) p.1.1
    have hn := pow_le_pow_left₀ (norm_nonneg _)
      (norm_resourceMatrix_pvmEnvironment_le_one P.isIsometry_globalIsometry hM p.2) 2
    rw [one_pow] at hn
    exact hw.trans hn
  have hB0 : 0 ≤ schmidtWeights (fun a b => star (M (a, b) p.2)) p.1.2 :=
    schmidtWeights_nonneg _ _
  have hB : schmidtWeights (fun a b => star (M (a, b) p.2)) p.1.2 ≤ β := hβ p.2 p.1.2
  have hD : 0 ≤ (Fintype.card (ιA × ιB) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  calc (Fintype.card (ιA × ιB) : ℝ)⁻¹ *
        (schmidtWeights (resourceMatrix (pvmEnvironment M P.globalIsometry p.2)) p.1.1 *
          schmidtWeights (fun a b => star (M (a, b) p.2)) p.1.2)
      ≤ (Fintype.card (ιA × ιB) : ℝ)⁻¹ * (1 * β) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hA1 hB hB0 zero_le_one) hD
    _ = β * (Fintype.card (ιA × ιB) : ℝ)⁻¹ := by ring

end Protocol

section Bell

variable {d : ℕ} {ρA ρB κA κB μA μB εA εB : Type*}
variable [Fintype ρA] [Fintype ρB] [Fintype κA] [Fintype κB] [Fintype μA] [Fintype μB]
variable [Fintype εA] [Fintype εB]
variable [DecidableEq ρA] [DecidableEq ρB] [DecidableEq κA] [DecidableEq κB]
variable [DecidableEq μA] [DecidableEq μB] [DecidableEq εA] [DecidableEq εB]

/-- **Cubic floor near the Bell basis**: `d³ ≤ 2K` for `ε ≤ 1/256`. -/
theorem PureProtocol.cube_le_two_mul_of_mem_bellNeighborhood [NeZero d]
    (P : PureProtocol (Fin d) (Fin d) ρA ρB κA κB μA μB (Fin d × Fin d) (Fin d × Fin d) εA εB)
    {M : unitaryGroup (Fin d × Fin d) ℂ} (hM : M ∈ bellNeighborhood d)
    {K : ℕ} (hK : NLQCLean.HasFootprint K P.resource μA μB) {ε : ℝ} (hε : ε ≤ 1 / 256)
    (hscore : 1 - ε ≤ scorePVM (M : Matrix _ _ ℂ) P.operationalChannel) :
    (d : ℝ) ^ 3 ≤ 2 * K := by
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hne : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  have hMiso : IsIsometry (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) := M.property.1
  have hβ0 : (0 : ℝ) ≤ 25 / (16 * d) := by positivity
  have h := P.scorePVM_sq_le_of_column_weight_le (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    hMiso hK hβ0
    (fun i j => (schmidtWeights_mem_of_mem_bellNeighborhood hM i j).2)
  have hcard : (Fintype.card (Fin d × Fin d) : ℝ) = (d : ℝ) ^ 2 := by simp [sq]
  rw [hcard] at h
  have hs : (1 - ε) ^ 2 ≤ (scorePVM (M : Matrix _ _ ℂ) P.operationalChannel) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hscore 2
  have h2 : (1 - ε) ^ 2 ≤ (K : ℝ) * (25 / (16 * d)) / (d : ℝ) ^ 2 := hs.trans h
  have hd3 : (0 : ℝ) ≤ (d : ℝ) ^ 3 := by positivity
  have h3 : (1 - ε) ^ 2 * (d : ℝ) ^ 3 ≤ 25 / 16 * K := by
    have h6 := mul_le_mul_of_nonneg_right h2 hd3
    have he : (K : ℝ) * (25 / (16 * d)) / (d : ℝ) ^ 2 * (d : ℝ) ^ 3 = 25 / 16 * K := by
      field_simp
    linarith only [h6, he]
  have h5 : (255 / 256 : ℝ) ^ 2 ≤ (1 - ε) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have h7 := mul_le_mul_of_nonneg_right h5 hd3
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  linarith only [h3, h7, hK0]

end Bell

end NLQCLean

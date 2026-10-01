import NLQCLean.Geometry.FiniteDimensionalNets
import NLQCLean.Geometry.OperatorNormalEmbedding
import NLQCLean.Bounds.StrongUnitaryTargets
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Full Haar mass of the SWAP neighbourhood

The volumetric net lemma in the operator-norm matrix space
(real dimension `2N`) covers `U(D)` by at most `9^(2N)` closed operator balls of radius `1/4`
centred at unitaries. Left invariance gives every such ball the same Haar mass, so each has mass
at least `9^(−2N)`. Since `‖M‖_F ≤ √D ‖M‖_op = d ‖M‖_op`, the ball around SWAP lies in `S_d`,
so `μ_d(S_d) ≥ 9^(−2N) ≥ exp(−5N)`. This is full probability Haar, not a normalized law.
-/

namespace NLQCLean

open Matrix MeasureTheory Module
open scoped ENNReal

section Net

variable (n : Type*) [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator

/-- An operator-norm `1/4`-net of the unitary group with at most `9^(2N)` unitary centres. -/
theorem exists_unitary_opNorm_net :
    ∃ F : Finset (Matrix n n ℂ), (∀ U ∈ F, U ∈ Matrix.unitaryGroup n ℂ) ∧
      (F.card : ℝ) ≤ 9 ^ (2 * Fintype.card n ^ 2) ∧
      ∀ V ∈ Matrix.unitaryGroup n ℂ, ∃ U ∈ F, opNorm (V - U) ≤ 1 / 4 := by
  obtain ⟨F, hFA, hcard, hnet⟩ := exists_finset_net_of_subset_closedBall
    (E := Matrix n n ℂ) (A := (Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ)))
    (fun V hV => show opNorm V ≤ 1 from
      (show IsIsometry V from Matrix.mem_unitaryGroup_iff'.mp hV).opNorm_le_one)
    (η := 1 / 4) (by norm_num)
  have hfin : finrank ℝ (Matrix n n ℂ) = 2 * Fintype.card n ^ 2 := by
    rw [Module.finrank_matrix, Complex.finrank_real_complex]
    ring
  rw [hfin, show (1 : ℝ) + 2 / (1 / 4) = 9 by norm_num] at hcard
  exact ⟨F, hFA, hcard, fun V hV => hnet V hV⟩

end Net

open scoped Matrix.Norms.Frobenius

section Patch

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- Unitaries within operator distance `r` of a matrix `W`. -/
def unitaryOpBall (W : Matrix n n ℂ) (r : ℝ) : Set (Matrix.unitaryGroup n ℂ) :=
  {V | opNorm ((V : Matrix n n ℂ) - W) ≤ r}

theorem measurableSet_unitaryOpBall (W : Matrix n n ℂ) (r : ℝ) :
    MeasurableSet (unitaryOpBall n W r) :=
  (isClosed_le ((continuous_opNorm n n).comp (continuous_subtype_val.sub continuous_const))
    continuous_const).measurableSet

variable {n}

theorem opNorm_mul_eq_of_isometry {W : Matrix n n ℂ} (hW : IsIsometry W) (hW' : IsIsometry Wᴴ)
    (X : Matrix n n ℂ) : opNorm (W * X) = opNorm X :=
  le_antisymm (opNorm_isometry_mul_le hW X) (by
    calc opNorm X = opNorm (Wᴴ * (W * X)) := by rw [← Matrix.mul_assoc, hW, Matrix.one_mul]
      _ ≤ opNorm (W * X) := opNorm_isometry_mul_le hW' _)

variable (n)

theorem unitaryHaar_unitaryOpBall (U : Matrix.unitaryGroup n ℂ) (r : ℝ) :
    unitaryHaar n (unitaryOpBall n (U : Matrix n n ℂ) r) = unitaryHaar n (unitaryOpBall n 1 r) := by
  have h1 : (U : Matrix n n ℂ)ᴴ * (U : Matrix n n ℂ) = 1 := U.property.1
  have h2 : IsIsometry (U : Matrix n n ℂ)ᴴ := by
    change (U : Matrix n n ℂ)ᴴᴴ * (U : Matrix n n ℂ)ᴴ = 1
    rw [Matrix.conjTranspose_conjTranspose]
    exact U.property.2
  have hpre : unitaryOpBall n (U : Matrix n n ℂ) r =
      (fun V => U⁻¹ * V) ⁻¹' unitaryOpBall n 1 r := by
    ext V
    simp only [unitaryOpBall, Set.mem_preimage, Set.mem_ofPred_eq]
    change _ ↔ opNorm (star (U : Matrix n n ℂ) * (V : Matrix n n ℂ) - 1) ≤ r
    rw [Matrix.star_eq_conjTranspose,
      show (U : Matrix n n ℂ)ᴴ * (V : Matrix n n ℂ) - 1 =
        (U : Matrix n n ℂ)ᴴ * ((V : Matrix n n ℂ) - (U : Matrix n n ℂ)) by
        rw [Matrix.mul_sub, h1],
      opNorm_mul_eq_of_isometry h2 (by rw [Matrix.conjTranspose_conjTranspose]; exact h1)]
  rw [hpre, measure_preimage_mul]

/-- Each operator `1/4`-ball around the identity has Haar mass at least `9^(−2N)`. -/
theorem inv_pow_nine_le_unitaryHaar_unitaryOpBall_one :
    ENNReal.ofReal (((9 : ℝ) ^ (2 * Fintype.card n ^ 2))⁻¹) ≤
      unitaryHaar n (unitaryOpBall n 1 (1 / 4)) := by
  obtain ⟨F, hFU, hcard, hnet⟩ := exists_unitary_opNorm_net n
  set m := unitaryHaar n (unitaryOpBall n 1 (1 / 4)) with hm
  have hcov : (Set.univ : Set (Matrix.unitaryGroup n ℂ)) ⊆ ⋃ W ∈ F, unitaryOpBall n W (1 / 4) :=
    fun V _ => by
      obtain ⟨W, hW, h⟩ := hnet V V.property
      exact Set.mem_biUnion hW h
  have hsum : ∑ W ∈ F, unitaryHaar n (unitaryOpBall n W (1 / 4)) = F.card * m := by
    rw [Finset.sum_congr rfl (fun W hW => unitaryHaar_unitaryOpBall n ⟨W, hFU W hW⟩ (1 / 4)),
      Finset.sum_const, nsmul_eq_mul]
  have h1 : 1 ≤ (F.card : ℝ≥0∞) * m := by
    calc (1 : ℝ≥0∞) = unitaryHaar n Set.univ := (measure_univ).symm
      _ ≤ unitaryHaar n (⋃ W ∈ F, unitaryOpBall n W (1 / 4)) := measure_mono hcov
      _ ≤ ∑ W ∈ F, unitaryHaar n (unitaryOpBall n W (1 / 4)) := measure_biUnion_finset_le _ _
      _ = _ := hsum
  have hpos : (0 : ℝ) < (9 : ℝ) ^ (2 * Fintype.card n ^ 2) := by positivity
  have hc : (F.card : ℝ≥0∞) ≤ ENNReal.ofReal ((9 : ℝ) ^ (2 * Fintype.card n ^ 2)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hcard
  rw [ENNReal.ofReal_inv_of_pos hpos]
  have hne : ENNReal.ofReal ((9 : ℝ) ^ (2 * Fintype.card n ^ 2)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hpos).ne'
  calc (ENNReal.ofReal ((9 : ℝ) ^ (2 * Fintype.card n ^ 2)))⁻¹
      = (ENNReal.ofReal ((9 : ℝ) ^ (2 * Fintype.card n ^ 2)))⁻¹ * 1 := (mul_one _).symm
    _ ≤ (ENNReal.ofReal ((9 : ℝ) ^ (2 * Fintype.card n ^ 2)))⁻¹ * ((F.card : ℝ≥0∞) * m) := by
        gcongr
    _ ≤ (ENNReal.ofReal ((9 : ℝ) ^ (2 * Fintype.card n ^ 2)))⁻¹ *
          (ENNReal.ofReal ((9 : ℝ) ^ (2 * Fintype.card n ^ 2)) * m) := by gcongr
    _ = m := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top, one_mul]

end Patch

theorem exp_neg_five_mul_le_inv_pow_nine (k : ℕ) :
    Real.exp (-(5 * (k : ℝ))) ≤ ((9 : ℝ) ^ (2 * k))⁻¹ := by
  have h81 : (81 : ℝ) ≤ Real.exp 5 := by
    have h := Real.exp_one_gt_d9
    have h' := pow_lt_pow_left₀ h (by norm_num) (by norm_num : (5 : ℕ) ≠ 0)
    have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h5]
    norm_num at h'
    linarith
  have hpow : (9 : ℝ) ^ (2 * k) ≤ Real.exp (5 * k) := by
    calc (9 : ℝ) ^ (2 * k) = 81 ^ k := by rw [pow_mul]; norm_num
      _ ≤ Real.exp 5 ^ k := pow_le_pow_left₀ (by norm_num) h81 k
      _ = Real.exp (5 * k) := by rw [← Real.exp_nat_mul]; congr 1; ring
  rw [Real.exp_neg]
  exact inv_anti₀ (by positivity) hpow

/-- Near-SWAP patch mass: `μ_d(S_d) ≥ exp(−5N)` for every `d ≥ 2`, with `N = d⁴`. -/
theorem strongSwapPatchMassBound_five : StrongSwapPatchMassBound 5 := by
  intro d hd
  let n := Fin d × Fin d
  have hd0 : 0 < d := by omega
  let S : Matrix.unitaryGroup n ℂ :=
    ⟨swapUnitary (Fin d), Matrix.mem_unitaryGroup_iff'.mpr (isIsometry_swapUnitary (Fin d))⟩
  have hsub : unitaryOpBall n (S : Matrix n n ℂ) (1 / 4) ⊆ swapNeighborhood d := by
    intro V hV
    rw [mem_swapNeighborhood_iff hd0]
    have hF := frobNorm_le_sqrt_card_mul_opNorm ((V : Matrix n n ℂ) - swapUnitary (Fin d))
    have hcard : Real.sqrt (Fintype.card n : ℝ) = d := by
      simp only [n, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      exact Real.sqrt_mul_self (Nat.cast_nonneg d)
    rw [hcard] at hF
    have hV' : opNorm ((V : Matrix n n ℂ) - swapUnitary (Fin d)) ≤ 1 / 4 := hV
    calc _ ≤ (d : ℝ) * opNorm ((V : Matrix n n ℂ) - swapUnitary (Fin d)) := hF
      _ ≤ (d : ℝ) * (1 / 4) := mul_le_mul_of_nonneg_left hV' (Nat.cast_nonneg d)
      _ = (d : ℝ) / 4 := by ring
  have hmass := inv_pow_nine_le_unitaryHaar_unitaryOpBall_one n
  rw [← unitaryHaar_unitaryOpBall n S] at hmass
  have hk : (Fintype.card n ^ 2 : ℕ) = d ^ 4 := by
    simp only [n, Fintype.card_prod, Fintype.card_fin]
    ring
  rw [hk] at hmass
  refine le_trans ?_ (hmass.trans (measure_mono hsub))
  apply ENNReal.ofReal_le_ofReal
  have := exp_neg_five_mul_le_inv_pow_nine (d ^ 4)
  simpa using this

end NLQCLean

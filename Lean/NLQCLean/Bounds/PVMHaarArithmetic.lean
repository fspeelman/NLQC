import NLQCLean.Approx.PVMCoordinateCount
import NLQCLean.Bounds.HaarArithmetic

/-!
# Arithmetic estimates for the PVM Haar bound

The PVM coordinate budget is `P = 1024 d² K²`.  These estimates
absorb the doubled freezing residual, the finite rank-allocation cover, and
the transverse dimension factors without introducing a `log K` source cost.
-/

namespace NLQCLean

/-- The PVM coordinate budget dominates the sixth power of the local dimension. -/
theorem pvm_sixth_power_le_coordinateBudget {d K : ℕ}
    (hK : (d : ℝ) ^ 2 / 4 ≤ K) :
    (d : ℝ) ^ 6 ≤ pvmWitnessCoordinateBudget d K := by
  have h : (d : ℝ) ^ 2 ≤ 4 * K := by linarith
  have hs := pow_le_pow_left₀ (sq_nonneg (d : ℝ)) h 2
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (d : ℝ))
  unfold pvmWitnessCoordinateBudget
  push_cast
  nlinarith [sq_nonneg (K : ℝ)]

/-- The real target dimension `d⁴` fits inside the PVM coordinate budget. -/
theorem pvm_fourth_power_le_coordinateBudget {d K : ℕ} (hd : 2 ≤ d)
    (hK : (d : ℝ) ^ 2 / 4 ≤ K) :
    (d : ℝ) ^ 4 ≤ pvmWitnessCoordinateBudget d K := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  exact (pow_le_pow_right₀ hd1 (by decide : 4 ≤ 6)).trans
    (pvm_sixth_power_le_coordinateBudget hK)

/-- The PVM coordinate budget is at least one under the physical floor. -/
theorem pvm_one_le_coordinateBudget_of_quarter {d K : ℕ} (hd : 2 ≤ d)
    (hK : (d : ℝ) ^ 2 / 4 ≤ K) :
    (1 : ℝ) ≤ pvmWitnessCoordinateBudget d K := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  exact (one_le_pow₀ hd1).trans (pvm_sixth_power_le_coordinateBudget hK)

/-- The target dimension and its logarithmic factor cost at most twice the
PVM coordinate budget. -/
theorem pvm_witnessDimension_mul_one_add_log_le {d K : ℕ} (hd : 2 ≤ d)
    (hK : (d : ℝ) ^ 2 / 4 ≤ K) :
    (d : ℝ) ^ 4 * (1 + Real.log (pvmWitnessCoordinateBudget d K : ℝ)) ≤
      2 * pvmWitnessCoordinateBudget d K := by
  have hP : (1 : ℝ) ≤ pvmWitnessCoordinateBudget d K :=
    pvm_one_le_coordinateBudget_of_quarter hd hK
  apply mul_one_add_log_le_twice_of_cube_le hP (by positivity)
  have hpow := pow_le_pow_left₀
    (by positivity : 0 ≤ (d : ℝ) ^ 6)
    (pvm_sixth_power_le_coordinateBudget hK) 2
  nlinarith only [hpow]

/-- The sum of the output approximation radius and the coordinate-thickening
radius for the doubled PVM freezing residual. -/
noncomputable def pvmWitnessTubeRadius (d K : ℕ) (e : ℝ) : ℝ :=
  (d : ℝ) * (2 * Real.sqrt e) +
    (2 * Real.sqrt e) * pvmWitnessCoordinateBudget d K

/-- The PVM witness tube has the coarse radius used in both Haar regimes. -/
theorem pvm_witnessTubeRadius_le {d K : ℕ} (hd : 2 ≤ d)
    (hK : (d : ℝ) ^ 2 / 4 ≤ K) {e : ℝ} (_he : 0 ≤ e) :
    pvmWitnessTubeRadius d K e ≤
      4 * pvmWitnessCoordinateBudget d K * Real.sqrt e := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hd6 : (d : ℝ) ≤ (d : ℝ) ^ 6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hd1 (by decide : 1 ≤ 6)
  have hdP : (d : ℝ) ≤ pvmWitnessCoordinateBudget d K :=
    hd6.trans (pvm_sixth_power_le_coordinateBudget hK)
  have hs := mul_le_mul_of_nonneg_right hdP (Real.sqrt_nonneg e)
  unfold pvmWitnessTubeRadius
  nlinarith

/-- A PVM tube radius above one half forces the recalculated error lower bound. -/
theorem pvm_error_lower_of_large_radius {P r e : ℝ} (_hP : 0 < P) (he : 0 < e)
    (hr : 1 / 2 < r) (hrP : r ≤ 4 * P * Real.sqrt e) :
    1 < 64 * P ^ 2 * e := by
  have hs : (4 * P * Real.sqrt e) ^ 2 = 16 * P ^ 2 * e := by
    calc
      _ = 16 * P ^ 2 * (Real.sqrt e) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt he.le]
  have hhalf : 1 / 2 < 4 * P * Real.sqrt e := hr.trans_le hrP
  nlinarith

/-- The Haar exponential prefactor is at least one in the large PVM-radius
regime, with residual factor `64`. -/
theorem pvm_one_le_large_radius_rhs {N k : ℕ} (hk : k ≤ N) {C P r e : ℝ}
    (hC : 1 ≤ C) (hP : 1 ≤ P) (hNP : (N : ℝ) ≤ P)
    (hlog : (N : ℝ) * (1 + Real.log P) ≤ 2 * P)
    (he : 0 < e) (he1 : e ≤ 1) (hr : 1 / 2 < r)
    (hrP : r ≤ 4 * P * Real.sqrt e) :
    1 ≤ Real.exp (16 * C * P) *
      Real.exp ((k : ℝ) / 2 * Real.log e) := by
  have hP0 : 0 < P := by linarith
  have hlow := (pvm_error_lower_of_large_radius hP0 he hr hrP).le
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1) hlow
  rw [Real.log_one, Real.log_mul (by positivity) he.ne',
    Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hlog64 : Real.log (64 : ℝ) ≤ 6 := by
    calc
      _ = Real.log ((2 : ℝ) ^ 6) := by norm_num
      _ = 6 * Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ _ := by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hloge : Real.log e ≤ 0 := Real.log_nonpos he.le he1
  have hkR : (k : ℝ) ≤ N := by exact_mod_cast hk
  have hkn := mul_le_mul_of_nonneg_right hkR (neg_nonneg.mpr hloge)
  have hn := mul_le_mul_of_nonneg_left
    (show -Real.log e ≤ 6 + 2 * Real.log P by linarith)
    (Nat.cast_nonneg N)
  have hCP : P ≤ C * P := by nlinarith
  rw [← Real.exp_add, Real.one_le_exp_iff]
  nlinarith

/-- The complete PVM witness-family count costs at most `exp(3P)`. -/
theorem PVMReverseShape.card_le_exp_coordinateBudget {d K : ℕ} (hd : 0 < d) :
    (Fintype.card (PVMReverseShape d K) : ℝ) ≤
      Real.exp (3 * (pvmWitnessCoordinateBudget d K : ℝ)) := by
  by_cases hK0 : K = 0
  · subst K
    have hc_le : Fintype.card (PVMReverseShape d 0) ≤ 0 := by
      simpa using PVMReverseShape.card_le d 0
    have hc : Fintype.card (PVMReverseShape d 0) = 0 :=
      Nat.eq_zero_of_le_zero hc_le
    rw [hc]
    norm_num only [Nat.cast_zero]
    exact (Real.exp_pos _).le
  have hK : 0 < K := Nat.pos_of_ne_zero hK0
  let P : ℝ := pvmWitnessCoordinateBudget d K
  have hKPnat : K ≤ pvmWitnessCoordinateBudget d K :=
    K_le_pvmWitnessCoordinateBudget hd hK
  have hdPnat : d ^ 2 ≤ pvmWitnessCoordinateBudget d K := by
    unfold pvmWitnessCoordinateBudget
    have hd2 : 1 ≤ d ^ 2 := pow_pos hd 2
    have hK2 : 1 ≤ K ^ 2 := pow_pos hK 2
    nlinarith
  have h3Knat : 3 * K ≤ pvmWitnessCoordinateBudget d K := by
    unfold pvmWitnessCoordinateBudget
    have hd2 : 1 ≤ d ^ 2 := pow_pos hd 2
    have hK2 : K ≤ K ^ 2 := by
      simpa only [pow_two] using Nat.le_mul_of_pos_left K hK
    nlinarith
  have hKexp : (K : ℝ) ^ 3 ≤ Real.exp P := by
    have hbase : (K : ℝ) ≤ Real.exp (K : ℝ) := by
      have h := Real.add_one_le_exp (K : ℝ)
      linarith
    have hcub := pow_le_pow_left₀ (Nat.cast_nonneg K) hbase 3
    have h3KR : ((3 * K : ℕ) : ℝ) ≤
        (pvmWitnessCoordinateBudget d K : ℝ) := by
      exact_mod_cast h3Knat
    calc
      (K : ℝ) ^ 3 ≤ (Real.exp (K : ℝ)) ^ 3 := hcub
      _ = Real.exp (3 * K) := by
        simp only [← Real.exp_nat_mul, Nat.cast_ofNat]
      _ ≤ Real.exp P := Real.exp_le_exp.mpr (by
        dsimp only [P]
        push_cast at h3KR
        exact h3KR)
  have htwo : (2 : ℝ) ^ (K + d ^ 2) ≤ Real.exp (2 * P) := by
    have hbase : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      norm_num at h ⊢
      exact h
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hbase (K + d ^ 2)
    calc
      (2 : ℝ) ^ (K + d ^ 2) ≤ (Real.exp 1) ^ (K + d ^ 2) := hp
      _ = Real.exp ((K + d ^ 2 : ℕ) : ℝ) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ Real.exp (2 * P) := Real.exp_le_exp.mpr (by
        have hKP : (K : ℝ) ≤ (pvmWitnessCoordinateBudget d K : ℝ) := by
          exact_mod_cast hKPnat
        have hdP : ((d ^ 2 : ℕ) : ℝ) ≤
            (pvmWitnessCoordinateBudget d K : ℝ) := by
          exact_mod_cast hdPnat
        dsimp only [P]
        push_cast at hdP ⊢
        linarith)
  have hcard : (Fintype.card (PVMReverseShape d K) : ℝ) ≤
      (K : ℝ) ^ 3 * (2 : ℝ) ^ (K + d ^ 2) := by
    exact_mod_cast PVMReverseShape.card_le d K
  calc
    (Fintype.card (PVMReverseShape d K) : ℝ) ≤
        (K : ℝ) ^ 3 * (2 : ℝ) ^ (K + d ^ 2) := hcard
    _ ≤ Real.exp P * Real.exp (2 * P) :=
      mul_le_mul hKexp htwo (by positivity) (by positivity)
    _ = Real.exp (3 * P) := by rw [← Real.exp_add]; congr 1; ring
    _ = _ := rfl

end NLQCLean

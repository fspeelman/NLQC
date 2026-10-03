import NLQCLean.Geometry.PVMWitnessBarrierVolume
import NLQCLean.Bounds.NearBellUniversal
import NLQCLean.Bounds.StrongUniversalExplicit

/-!
# Explicit constants for universal measurement approximation (Theorem B(ii))

Near the generalized Bell basis, the following three inputs give an explicit estimate:

* the slim witnesses with budget `P = 42 K²` (`d³ ≤ 2K`);
* the barrier image-volume bound at the actual witness degrees (base `2·82 = 164` per source
  coordinate);
* the transverse error exponent `(N − t)/2`, with `t = 3d² − 2` and `N = d⁴`.

The estimate is

  `μ(B_d ∩ Reach) ≤ K³ 2^(K+d²) · 16ᴺ 2^(P+2N) 82^(P+4N) 10ᴺ (2P)^t 9ᴺ r^(N−t)`,

at tube radius `r = √(50ε/9) P ≤ 1/2`. Against the patch mass `(1 + 8 d^(3/2))^(−2N)` it gives
`((N − t)/2) ln(1/ε) ≤ 239 K²` once `K ≥ (19/20) d³`. With the cubic floor
`K ≥ d³(1 − ε)²` this yields, for universal pure or common-map mixed PVM approximation in
score or worst-case joint total variation:

* `K ≥ max(d³(1 − ε)², d² √ln(1/ε) / 36)` for every `d ≥ 2`;
* `K ≥ max(d³(1 − ε)², d² √ln(1/ε) / 27)` for every `d ≥ 3`;
* `log₂ K ≥ max(3n − 2, 2n + ½ log₂ ln(1/ε) − 6)` at `d = 2ⁿ`, and `− 5` once `n ≥ 2`.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix MeasureTheory
open scoped ENNReal Matrix.Norms.Frobenius

/-- Elementary powers for `d ≥ 2`. -/
theorem pow_facts_of_two_le {d : ℝ} (hd : 2 ≤ d) :
    4 * d ≤ d ^ 3 ∧ 8 ≤ d ^ 3 ∧ 16 * d ^ 2 ≤ d ^ 6 ∧ 4 * d ^ 4 ≤ d ^ 6 ∧ 2 * d ^ 5 ≤ d ^ 6 ∧
      16 ≤ d ^ 4 := by
  have hd0 : 0 ≤ d := by linarith
  have h2 : 4 ≤ d ^ 2 := by nlinarith
  have h3 : 4 * d ≤ d ^ 3 := by
    have := mul_le_mul_of_nonneg_right h2 hd0
    calc 4 * d ≤ d ^ 2 * d := by linarith
      _ = d ^ 3 := by ring
  have h4 : 16 ≤ d ^ 4 := by
    have := mul_le_mul h2 h2 (by norm_num) (by positivity)
    calc (16 : ℝ) = 4 * 4 := by norm_num
      _ ≤ d ^ 2 * d ^ 2 := this
      _ = d ^ 4 := by ring
  refine ⟨h3, by linarith, ?_, ?_, ?_, h4⟩
  · have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ d ^ 2)
    calc 16 * d ^ 2 = d ^ 2 * 16 := by ring
      _ ≤ d ^ 2 * d ^ 4 := this
      _ = d ^ 6 := by ring
  · have := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ d ^ 4)
    calc 4 * d ^ 4 ≤ d ^ 2 * d ^ 4 := this
      _ = d ^ 6 := by ring
  · have := mul_le_mul_of_nonneg_right hd (by positivity : (0 : ℝ) ≤ d ^ 5)
    calc 2 * d ^ 5 ≤ d * d ^ 5 := this
      _ = d ^ 6 := by ring

/-! ### The slim near-Bell budget `42 K²` -/

/-- The budget `42 K²` is admissible for near-Bell shapes once `d³ ≤ 2K`. -/
theorem PVMReverseShape.admissibleBudget_nearBell_sharp {d K : ℕ} (s : PVMReverseShape d K)
    (hd : 2 ≤ d) (hs : s.IsNearBell) (hd3 : (d : ℝ) ^ 3 ≤ 2 * K) :
    s.AdmissibleBudget (42 * K ^ 2) := by
  have hres := hs.resource_le
  obtain ⟨hA, hB, hS⟩ := hs
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hKR : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hfoot : ((s.1.r * s.1.mA * s.1.mB : ℕ) : ℝ) ≤ K := by exact_mod_cast s.1.footprint
  push_cast at hfoot
  have hmA : (1 : ℝ) ≤ s.1.mA := by exact_mod_cast s.1.messageA_pos
  have hmB : (1 : ℝ) ≤ s.1.mB := by exact_mod_cast s.1.messageB_pos
  set r : ℝ := (s.1.r : ℝ)
  set a : ℝ := (s.1.mA : ℝ)
  set b : ℝ := (s.1.mB : ℝ)
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  obtain ⟨hd4, h8, -⟩ := pow_facts_of_two_le hdR
  have hdK : (d : ℝ) ≤ K / 2 := by linarith
  have hK4 : (4 : ℝ) ≤ K := by linarith
  -- support size: `d S ≤ 3K + d ≤ (7/2) K`
  have hSR : (d : ℝ) * s.supportSize ≤ 7 / 2 * K := by
    have h1 : ((s.supportSize : ℕ) : ℝ) ≤ (((K + d - 1) / d : ℕ) : ℝ) + (d : ℝ) ^ 2 := by
      exact_mod_cast hS
    have h2 : (d : ℝ) * (((K + d - 1) / d : ℕ) : ℝ) ≤ K + d := by
      have h := Nat.mul_div_le (K + d - 1) d
      have h' : d * ((K + d - 1) / d) ≤ K + d := by omega
      exact_mod_cast h'
    have h3 := mul_le_mul_of_nonneg_left h1 hdpos.le
    have h4 : (d : ℝ) * (d : ℝ) ^ 2 = (d : ℝ) ^ 3 := by ring
    linarith
  have hab : (r * a * b) ^ 2 ≤ (K : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hfoot 2
  have hrA : (d : ℝ) ^ 2 * (r * a) ^ 2 ≤ 2 * (K : ℝ) ^ 2 := by
    have h1 : (d : ℝ) ^ 2 * (r * a) ^ 2 ≤ 2 * b ^ 2 * (r * a) ^ 2 :=
      mul_le_mul_of_nonneg_right hB (sq_nonneg _)
    have h2 : 2 * b ^ 2 * (r * a) ^ 2 = 2 * (r * a * b) ^ 2 := by ring
    linarith
  have hrB : (d : ℝ) ^ 2 * (r * b) ^ 2 ≤ 2 * (K : ℝ) ^ 2 := by
    have h1 : (d : ℝ) ^ 2 * (r * b) ^ 2 ≤ 2 * a ^ 2 * (r * b) ^ 2 :=
      mul_le_mul_of_nonneg_right hA (sq_nonneg _)
    have h2 : 2 * a ^ 2 * (r * b) ^ 2 = 2 * (r * a * b) ^ 2 := by ring
    linarith
  have hr2 : r ^ 2 ≤ (K : ℝ) ^ 2 / 4 := by
    have hd2' : (4 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
    have h4r : 4 * r ≤ 2 * K := by
      have := mul_le_mul_of_nonneg_left hd2' hr0
      linarith
    have hrK : r ≤ K / 2 := by linarith
    have := mul_le_mul hrK hrK hr0 (by linarith)
    nlinarith
  constructor
  · have hf := PVMReverseBlocks.finrank_real s
    have hsq : (∑ i, s.2.rank i ^ 2) ≤ s.supportSize ^ 2 := by
      simpa only [PVMReverseShape.supportSize] using
        (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := s.2.rank)
          (fun _ _ => Nat.zero_le _))
    have hsqR : ∑ i, ((s.2.rank i : ℕ) : ℝ) ^ 2 ≤ (s.supportSize : ℝ) ^ 2 := by
      exact_mod_cast hsq
    set S : ℝ := (s.supportSize : ℝ) with hSdef
    have hS0 : 0 ≤ S := Nat.cast_nonneg _
    have h2S : 2 * S ≤ 7 / 2 * K := by
      have := mul_le_mul_of_nonneg_right hdR hS0
      linarith
    have hS2 : S ^ 2 ≤ 49 / 16 * (K : ℝ) ^ 2 := by
      have hSK : S ≤ 7 / 4 * K := by linarith
      have := mul_le_mul hSK hSK hS0 (by positivity)
      nlinarith
    have hdKS : (d : ℝ) * K * S ≤ 7 / 2 * (K : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hSR hKR
      have e1 : (d : ℝ) * K * S = K * ((d : ℝ) * S) := by ring
      have e2 : (K : ℝ) * (7 / 2 * K) = 7 / 2 * (K : ℝ) ^ 2 := by ring
      linarith
    rw [← Nat.cast_le (α := ℝ), hf]
    push_cast
    change 2 * r ^ 2 + 2 * (∑ x, ((s.2.rank x : ℕ) : ℝ) ^ 2) + 2 * (d : ℝ) ^ 2 * (r * a) ^ 2 +
      2 * (d : ℝ) ^ 2 * (r * b) ^ 2 + 4 * ((d : ℝ) * K + S) * S ≤ 42 * (K : ℝ) ^ 2
    have key : ∀ T : ℝ, T ≤ S ^ 2 → 2 * r ^ 2 + 2 * T + 2 * (d : ℝ) ^ 2 * (r * a) ^ 2 +
        2 * (d : ℝ) ^ 2 * (r * b) ^ 2 + 4 * ((d : ℝ) * K + S) * S ≤ 42 * (K : ℝ) ^ 2 := by
      intro T hT
      linear_combination 2 * hr2 + 2 * hT + 2 * hrA + 2 * hrB + 4 * hdKS + 6 * hS2 +
        (9 / 8) * sq_nonneg (K : ℝ)
    exact key _ hsqR
  · have h1 : (d : ℝ) * Real.sqrt (10 * d * K) = Real.sqrt (10 * (d : ℝ) ^ 3 * K) := by
      rw [show (10 : ℝ) * (d : ℝ) ^ 3 * K = (d : ℝ) ^ 2 * (10 * d * K) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hdpos.le]
    have h2 : Real.sqrt (10 * (d : ℝ) ^ 3 * K) ≤ 5 * K := by
      rw [Real.sqrt_le_left (by positivity)]
      have := mul_le_mul_of_nonneg_right hd3 hKR
      nlinarith
    have h5 : 5 * (K : ℝ) ≤ 42 * (K : ℝ) ^ 2 := by nlinarith
    push_cast
    rw [h1]
    linarith

/-! ### The Haar estimate at the sharp budget -/

/-- Every accurate target near the Bell basis is the inverse of a slim witness target at the
budget `42 K²`. -/
theorem nearBell_mem_inv_witnessTargets_sharp {d : ℕ} [NeZero d] (hd2 : 2 ≤ d) {K : ℕ}
    (hd3 : (d : ℝ) ^ 3 ≤ 2 * K) (hfloor : d ^ 2 ≤ 4 * K) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 256) {M : unitaryGroup (Fin d × Fin d) ℂ} (hM : M ∈ bellNeighborhood d)
    (hR : M ∈ purePVMReachable d K ε) :
    ∃ s : PVMReverseShape d K, ∃ hs : s.IsNearBell,
      M⁻¹ ∈ PVMReverseBlocks.witnessTargets s (by omega) hfloor
        (s.admissibleBudget_nearBell_sharp hd2 hs hd3) (Real.sqrt (50 / 9 * ε))
        ((d : ℝ) * (Real.sqrt (50 / 9 * ε))) := by
  obtain ⟨t, P, hK, hscore⟩ := hR
  obtain ⟨s, hs, x, hx, hclose⟩ := P.exists_pvm_reverse_witness_nearBell hd2 hM hK hε0 hε hscore
  have hη : 0 ≤ (d : ℝ) * (Real.sqrt (50 / 9 * ε)) := by positivity
  obtain ⟨hov, -, -, hleak⟩ := PVMReverseBlocks.IsValid.approximation hx
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ hη hclose
  have hdef : (d : ℝ) ^ 2 - ‖PVMReverseBlocks.overlap x‖ ^ 2 ≤
      (d : ℝ) ^ 2 * (Real.sqrt (50 / 9 * ε)) ^ 2 := by
    simpa only [mul_pow] using hleak
  obtain ⟨y, hy, hdist⟩ := PVMReverseBlocks.exists_mem_witnessFormat_source_approximation s
    (by omega) hfloor (s.admissibleBudget_nearBell_sharp hd2 hs hd3) (Real.sqrt (50 / 9 * ε)) hx
    hdef (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ hov
  refine ⟨s, hs, y, hy, ?_⟩
  rw [PVMReverseBlocks.coordinateOverlapPolynomial_eq_raw_of_mem s (by omega) hfloor
    (s.admissibleBudget_nearBell_sharp hd2 hs hd3) hy, dist_comm, dist_eq_norm,
    PVMReverseBlocks.coe_unitary_inv_eq_conjTranspose]
  exact hdist

/-- **Near-Bell Haar estimate with explicit factors.** For `d ≥ 2`, `d³ ≤ 2K`,
`0 < ε ≤ 1/256` and tube radius `r = √(50ε/9)·42K² ≤ 1/2`,
`μ(B_d ∩ Reach) ≤ K³ 2^(K+d²) · 16ᴺ 2^(P+2N) 82^(P+4N) √10^(2N) (2P)^t 9ᴺ r^(N−t)`. -/
theorem nearBell_haar_le_sharp {d K : ℕ} [NeZero d] (hd2 : 2 ≤ d) (hd3 : (d : ℝ) ^ 3 ≤ 2 * K)
    {ε : ℝ} (hε : 0 < ε) (hε256 : ε ≤ 1 / 256)
    (hrad : Real.sqrt (50 / 9 * ε) * ((42 * K ^ 2 : ℕ) : ℝ) ≤ 1 / 2) :
    unitaryHaar (Fin d × Fin d) (bellNeighborhood d ∩ purePVMReachable d K ε) ≤
      ENNReal.ofReal (((K ^ 3 * 2 ^ (K + d ^ 2) : ℕ) : ℝ) *
        (16 ^ (d ^ 4) * ((((2 ^ (42 * K ^ 2 + 2 * d ^ 4) * 82 ^ (42 * K ^ 2 + 4 * d ^ 4) : ℕ)) : ℝ) *
          Real.sqrt 10 ^ (2 * d ^ 4)) *
        ((2 * ((42 * K ^ 2 : ℕ) : ℝ)) ^ (3 * d ^ 2 - 2) * 9 ^ (d ^ 4) *
          (Real.sqrt (50 / 9 * ε) * ((42 * K ^ 2 : ℕ) : ℝ)) ^ (d ^ 4 - (3 * d ^ 2 - 2))))) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd2
  have hK1 := one_le_of_cube_le hdR hd3
  have hfloorR : (d : ℝ) ^ 2 ≤ 4 * K := by nlinarith [sq_le_of_cube_le hdR hd3]
  have hfloor : d ^ 2 ≤ 4 * K := by exact_mod_cast hfloorR
  have hd0 : 0 < d := by omega
  set δ := Real.sqrt (50 / 9 * ε) with hδ
  set B : ℕ := 42 * K ^ 2 with hB
  set r := δ * B with hr
  have hδ1 : δ ≤ 1 := by
    have : Real.sqrt ε ≤ 1 / 16 := by
      rw [Real.sqrt_le_left (by norm_num)]
      linarith
    rw [hδ]
    linarith [sqrt_fifty_ninths_mul_le hε.le]
  have hδ0 : 0 ≤ δ := by positivity
  have hr0 : 0 < r := by
    rw [hr]
    have : 0 < δ := by rw [hδ]; have := Real.sqrt_pos.mpr hε; positivity
    have hB0 : (0 : ℝ) < B := by rw [hB]; push_cast; positivity
    positivity
  have hρ : (d : ℝ) * δ ≤ r := by
    rw [hr, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ hδ0
    rw [hB]
    push_cast
    nlinarith [sq_le_of_cube_le hdR hd3]
  classical
  let T : PVMReverseShape d K → Set (unitaryGroup (Fin d × Fin d) ℂ) := fun s =>
    if hs : s.IsNearBell then
      PVMReverseBlocks.witnessTargets s hd0 hfloor (s.admissibleBudget_nearBell_sharp hd2 hs hd3) δ
        ((d : ℝ) * δ)
    else ∅
  have hcover : bellNeighborhood d ∩ purePVMReachable d K ε ⊆ Inv.inv ⁻¹' ⋃ s, T s := by
    rintro M ⟨hM, hR⟩
    obtain ⟨s, hs, hmem⟩ := nearBell_mem_inv_witnessTargets_sharp hd2 hd3 hfloor hε.le hε256 hM hR
    exact Set.mem_iUnion.mpr ⟨s, by simp only [T, dite_eq_left hs]; exact hmem⟩
  set Bnd := 16 ^ (d ^ 4) * ((((2 ^ (B + 2 * d ^ 4) * 82 ^ (B + 4 * d ^ 4) : ℕ)) : ℝ) *
      Real.sqrt 10 ^ (2 * d ^ 4)) *
    ((2 * (B : ℝ)) ^ (3 * d ^ 2 - 2) * 9 ^ (d ^ 4) * r ^ (d ^ 4 - (3 * d ^ 2 - 2))) with hBnd
  have hT : ∀ s, unitaryHaar (Fin d × Fin d) (T s) ≤ ENNReal.ofReal Bnd := by
    intro s
    by_cases hs : s.IsNearBell
    · simp only [T, dite_eq_left hs]
      exact PVMReverseBlocks.witness_haar_le_barrier s hd0 hfloor
        (s.admissibleBudget_nearBell_sharp hd2 hs hd3) hd2 hδ0 hδ1 hr0 hrad le_rfl hρ
        (PVMReverseBlocks.measurableSet_witnessTargets s hd0 hfloor _ δ _) (fun U hU => hU)
    · simp only [T, dite_eq_right hs, measure_empty]
      exact zero_le
  calc _ ≤ unitaryHaar (Fin d × Fin d) (Inv.inv ⁻¹' ⋃ s, T s) := measure_mono hcover
    _ = unitaryHaar (Fin d × Fin d) (⋃ s, T s) := unitaryHaar_preimage_inv _ _
    _ ≤ ∑ s, unitaryHaar (Fin d × Fin d) (T s) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _s : PVMReverseShape d K, ENNReal.ofReal Bnd := Finset.sum_le_sum fun s _ => hT s
    _ = (Fintype.card (PVMReverseShape d K) : ℝ≥0∞) * ENNReal.ofReal Bnd := by simp
    _ ≤ ((K ^ 3 * 2 ^ (K + d ^ 2) : ℕ) : ℝ≥0∞) * ENNReal.ofReal Bnd := by
        gcongr
        exact_mod_cast PVMReverseShape.card_le d K
    _ = ENNReal.ofReal (((K ^ 3 * 2 ^ (K + d ^ 2) : ℕ) : ℝ) * Bnd) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-! ### Arithmetic -/

theorem explicit_pvm_numeric_bounds :
    (260422133760 : ℝ) ≤ Real.exp 27 ∧ Real.log 42 ≤ 15 / 4 ∧ (50 / 9 : ℝ) ≤ Real.exp 2 ∧
      Real.log 39200 ≤ 11 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := le_exp_div_of_pow_le (x := 260422133760) (by norm_num) (k := 27) (n := 1)
      (by norm_num) (by norm_num)
    norm_num at h
    exact h
  · rw [Real.log_le_iff_le_exp (by norm_num)]
    have h := le_exp_div_of_pow_le (x := 42) (by norm_num) (k := 15) (n := 4) (by norm_num)
      (by norm_num)
    norm_num at h
    exact h
  · have h := le_exp_div_of_pow_le (x := 50 / 9) (by norm_num) (k := 2) (n := 1) (by norm_num)
      (by norm_num)
    norm_num at h
    exact h
  · rw [Real.log_le_iff_le_exp (by norm_num)]
    have h := le_exp_div_of_pow_le (x := 39200) (by norm_num) (k := 11) (n := 1) (by norm_num)
      (by norm_num)
    norm_num at h
    exact h

/-- `log(1 + 8 d √d) ≤ 3 + 2d`. -/
theorem log_one_add_eight_mul_sqrt_le {d : ℕ} (hd : 1 ≤ d) :
    Real.log (1 + 8 * (d : ℝ) * Real.sqrt d) ≤ 3 + 2 * d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hsq : Real.sqrt d ≤ d := by
    rw [Real.sqrt_le_left hd0.le]
    nlinarith
  have hbase : 1 + 8 * (d : ℝ) * Real.sqrt d ≤ 9 * (d : ℝ) ^ 2 := by
    nlinarith [Real.sqrt_nonneg (d : ℝ)]
  have h1 := Real.log_le_log (by positivity) hbase
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
  have h9 : Real.log 9 ≤ 3 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    obtain ⟨h18, -, -⟩ := strong_numeric_exp_bounds
    linarith
  have hld : Real.log d ≤ d := by
    have := Real.log_le_sub_one_of_pos hd0
    linarith
  push_cast at h1
  linarith

/-- `d⁴ ln K ≤ dK + 3d⁵`. -/
theorem fourth_mul_log_le {d : ℕ} (hd : 1 ≤ d) {K : ℝ} (hK : 0 < K) :
    (d : ℝ) ^ 4 * Real.log K ≤ (d : ℝ) * K + 3 * (d : ℝ) ^ 5 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h3 : (0 : ℝ) < (d : ℝ) ^ 3 := by positivity
  have hsplit : Real.log K = Real.log (K / (d : ℝ) ^ 3) + 3 * Real.log d := by
    rw [Real.log_div hK.ne' h3.ne', Real.log_pow]
    push_cast
    ring
  have h1 : Real.log (K / (d : ℝ) ^ 3) ≤ K / (d : ℝ) ^ 3 := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < K / (d : ℝ) ^ 3)
    linarith
  have h2 : Real.log d ≤ d := by
    have := Real.log_le_sub_one_of_pos hd0
    linarith
  have hd4 : (0 : ℝ) ≤ (d : ℝ) ^ 4 := by positivity
  have hdiv : (d : ℝ) ^ 4 * (K / (d : ℝ) ^ 3) = (d : ℝ) * K := by
    field_simp
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_left h1 hd4, mul_le_mul_of_nonneg_left h2 hd4]

/-- The lower-order terms are at most `22 K²` once `K ≥ (19/20) d³`. -/
theorem nearBell_lower_order_le {d : ℕ} (hd : 2 ≤ d) {K : ℝ} (hK : 19 / 20 * (d : ℝ) ^ 3 ≤ K) :
    4 * K + 2 * (d : ℝ) * K + 4 * (d : ℝ) ^ 2 + 151 / 4 * (d : ℝ) ^ 4 + 10 * (d : ℝ) ^ 5 ≤
      22 * K ^ 2 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hd4, h3, h2, h4, h5, -⟩ := pow_facts_of_two_le hdR
  have hK76 : 38 / 5 ≤ K := by linarith
  have hK0 : 0 ≤ K := by linarith
  have h6 : (d : ℝ) ^ 6 ≤ 400 / 361 * K ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity) hK 2
    have e : (19 / 20 * (d : ℝ) ^ 3) ^ 2 = 361 / 400 * (d : ℝ) ^ 6 := by ring
    linarith
  have hdK : 19 / 5 * (d : ℝ) ≤ K := by linarith
  have hdKK : 2 * (d : ℝ) * K ≤ 10 / 19 * K ^ 2 := by
    have := mul_le_mul_of_nonneg_right hdK hK0
    nlinarith
  have h4K : 4 * K ≤ 10 / 19 * K ^ 2 := by
    have := mul_le_mul_of_nonneg_right hK76 hK0
    nlinarith
  linarith

/-- The tube factors split into the fixed part, the coordinate part `164^P`, `2^t`, `P^N` and
the leakage power `δⁿ`. -/
theorem nearBell_tube_factor_eq (P N t n : ℕ) (htn : t + n = N) (a δ : ℝ) :
    a * (16 ^ N * ((((2 ^ (P + 2 * N) * 82 ^ (P + 4 * N) : ℕ)) : ℝ) * Real.sqrt 10 ^ (2 * N)) *
        ((2 * (P : ℝ)) ^ t * 9 ^ N * (δ * P) ^ n)) =
      a * ((16 ^ N * 9 ^ N * (2 ^ (2 * N) * 82 ^ (4 * N) * 10 ^ N)) * ((2 : ℝ) ^ P * 82 ^ P) *
        (2 : ℝ) ^ t * (P : ℝ) ^ N * δ ^ n) := by
  have h10 : Real.sqrt 10 ^ (2 * N) = (10 : ℝ) ^ N := by
    rw [pow_mul, Real.sq_sqrt (by norm_num)]
  have hPtn : (P : ℝ) ^ t * (P : ℝ) ^ n = (P : ℝ) ^ N := by
    rw [← pow_add, htn]
  rw [h10, ← hPtn]
  push_cast
  rw [pow_add, pow_add, mul_pow, mul_pow]
  ring

/-- The tube factors are at most `exp(27N + (31/6)P + t + N ln P + N) ε^(n/2)`. -/
theorem nearBell_tube_factor_le (P N t n : ℕ) (htn : t + n = N) (hP : 0 < P) {a ε : ℝ}
    (ha : 0 ≤ a) (hε : 0 < ε) :
    a * (16 ^ N * ((((2 ^ (P + 2 * N) * 82 ^ (P + 4 * N) : ℕ)) : ℝ) * Real.sqrt 10 ^ (2 * N)) *
        ((2 * (P : ℝ)) ^ t * 9 ^ N * (Real.sqrt (50 / 9 * ε) * P) ^ n)) ≤
      a * (Real.exp (27 * (N : ℝ) + 31 / 6 * (P : ℝ) + t + (N : ℝ) * Real.log P + N) *
        ε ^ ((n : ℝ) / 2)) := by
  obtain ⟨hM, -, h509, -⟩ := explicit_pvm_numeric_bounds
  obtain ⟨h164, -⟩ := explicit_numeric_bounds
  rw [nearBell_tube_factor_eq P N t n htn]
  refine mul_le_mul_of_nonneg_left ?_ ha
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hfix : (16 : ℝ) ^ N * 9 ^ N * (2 ^ (2 * N) * 82 ^ (4 * N) * 10 ^ N) ≤
      Real.exp (27 * (N : ℝ)) := by
    have he : (16 : ℝ) ^ N * 9 ^ N * (2 ^ (2 * N) * 82 ^ (4 * N) * 10 ^ N) =
        260422133760 ^ N := by
      rw [show (260422133760 : ℝ) = 16 * 9 * (2 ^ 2 * 82 ^ 4 * 10) by norm_num,
        mul_pow, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    rw [he]
    calc (260422133760 : ℝ) ^ N ≤ Real.exp 27 ^ N := pow_le_pow_left₀ (by norm_num) hM N
      _ = _ := by rw [← Real.exp_nat_mul]; ring_nf
  have hcoord : (2 : ℝ) ^ P * 82 ^ P ≤ Real.exp (31 / 6 * (P : ℝ)) := by
    rw [← mul_pow]
    calc ((2 : ℝ) * 82) ^ P ≤ Real.exp (31 / 6) ^ P :=
          pow_le_pow_left₀ (by norm_num) (by norm_num at h164 ⊢; exact h164) P
      _ = _ := by rw [← Real.exp_nat_mul]; ring_nf
  have h2t : (2 : ℝ) ^ t ≤ Real.exp (t : ℝ) := by
    calc (2 : ℝ) ^ t ≤ Real.exp 1 ^ t :=
          pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) t
      _ = Real.exp (t : ℝ) := by rw [← Real.exp_nat_mul]; ring_nf
  have hPN : (P : ℝ) ^ N = Real.exp ((N : ℝ) * Real.log P) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hδn : Real.sqrt (50 / 9 * ε) ^ n ≤ Real.exp (N : ℝ) * ε ^ ((n : ℝ) / 2) := by
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (show n ≤ N by omega)
    calc Real.sqrt (50 / 9 * ε) ^ n = (50 / 9 * ε) ^ ((n : ℝ) / 2) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          ring_nf
      _ = (50 / 9 : ℝ) ^ ((n : ℝ) / 2) * ε ^ ((n : ℝ) / 2) := Real.mul_rpow (by norm_num) hε.le
      _ ≤ Real.exp (N : ℝ) * ε ^ ((n : ℝ) / 2) := by
          gcongr
          calc (50 / 9 : ℝ) ^ ((n : ℝ) / 2) ≤ Real.exp 2 ^ ((n : ℝ) / 2) :=
                Real.rpow_le_rpow (by norm_num) h509 (by positivity)
            _ = Real.exp (n : ℝ) := by rw [← Real.exp_mul]; ring_nf
            _ ≤ _ := Real.exp_le_exp.mpr hnN
  rw [hPN]
  calc 16 ^ N * 9 ^ N * (2 ^ (2 * N) * 82 ^ (4 * N) * 10 ^ N) * ((2 : ℝ) ^ P * 82 ^ P) *
        (2 : ℝ) ^ t * Real.exp ((N : ℝ) * Real.log P) * Real.sqrt (50 / 9 * ε) ^ n
      ≤ Real.exp (27 * (N : ℝ)) * Real.exp (31 / 6 * (P : ℝ)) * Real.exp (t : ℝ) *
        Real.exp ((N : ℝ) * Real.log P) * (Real.exp (N : ℝ) * ε ^ ((n : ℝ) / 2)) := by
        gcongr
    _ = _ := by simp only [Real.exp_add]; ring

/-- `|S_d| ≤ K³ 2^(K+d²) ≤ exp(4K + d²)`. -/
theorem card_shapes_le_exp_sharp (d K : ℕ) :
    ((K ^ 3 * 2 ^ (K + d ^ 2) : ℕ) : ℝ) ≤ Real.exp (4 * K + (d : ℝ) ^ 2) := by
  push_cast
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h1 : (K : ℝ) ^ 3 ≤ Real.exp (3 * K) := by
    have hKe : (K : ℝ) ≤ Real.exp K := by linarith [Real.add_one_le_exp (K : ℝ)]
    calc (K : ℝ) ^ 3 ≤ Real.exp K ^ 3 := pow_le_pow_left₀ hK0 hKe 3
      _ = Real.exp (3 * K) := by rw [← Real.exp_nat_mul]; norm_num
  have h2 : (2 : ℝ) ^ (K + d ^ 2) ≤ Real.exp ((K : ℝ) + (d : ℝ) ^ 2) := by
    have h22 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc (2 : ℝ) ^ (K + d ^ 2) ≤ Real.exp 1 ^ (K + d ^ 2) :=
          pow_le_pow_left₀ (by norm_num) h22 _
      _ = Real.exp ((K : ℝ) + (d : ℝ) ^ 2) := by
          rw [← Real.exp_nat_mul]; push_cast; ring_nf
  calc (K : ℝ) ^ 3 * 2 ^ (K + d ^ 2) ≤ Real.exp (3 * K) * Real.exp ((K : ℝ) + (d : ℝ) ^ 2) :=
        mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; ring_nf

/-- The patch mass is at least `exp(−2N(3 + 2d))`. -/
theorem exp_le_bell_patch {d : ℕ} (hd : 1 ≤ d) :
    Real.exp (-(2 * (d : ℝ) ^ 4 * (3 + 2 * d))) ≤ ((1 + 8 * d * Real.sqrt d) ^ (2 * d ^ 4))⁻¹ := by
  have hlog := log_one_add_eight_mul_sqrt_le hd
  have hpos : (0 : ℝ) < 1 + 8 * d * Real.sqrt d := by positivity
  rw [← Real.exp_log (by positivity : (0 : ℝ) < ((1 + 8 * d * Real.sqrt d) ^ (2 * d ^ 4))⁻¹),
    Real.log_inv, Real.log_pow, Real.exp_le_exp]
  push_cast
  have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ) ^ 4)
  linarith

/-- **Patch against the near-Bell estimate.** If the Bell patch mass is at most the explicit
near-Bell estimate and `K ≥ (19/20) d³`, then `((N − t)/2) ln(1/ε) ≤ 239 K²`. -/
theorem nearBell_log_le {d K : ℕ} (hd : 2 ≤ d) (hK : 19 / 20 * (d : ℝ) ^ 3 ≤ K) {ε : ℝ}
    (hε : 0 < ε)
    (h : ((1 + 8 * d * Real.sqrt d) ^ (2 * d ^ 4))⁻¹ ≤
      ((K ^ 3 * 2 ^ (K + d ^ 2) : ℕ) : ℝ) *
        (16 ^ (d ^ 4) * ((((2 ^ (42 * K ^ 2 + 2 * d ^ 4) * 82 ^ (42 * K ^ 2 + 4 * d ^ 4) : ℕ)) : ℝ) *
          Real.sqrt 10 ^ (2 * d ^ 4)) *
        ((2 * ((42 * K ^ 2 : ℕ) : ℝ)) ^ (3 * d ^ 2 - 2) * 9 ^ (d ^ 4) *
          (Real.sqrt (50 / 9 * ε) * ((42 * K ^ 2 : ℕ) : ℝ)) ^ (d ^ 4 - (3 * d ^ 2 - 2))))) :
    ((d ^ 4 - (3 * d ^ 2 - 2) : ℕ) : ℝ) / 2 * Real.log (1 / ε) ≤ 239 * (K : ℝ) ^ 2 := by
  obtain ⟨-, hl42, -, -⟩ := explicit_pvm_numeric_bounds
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨-, h8, -⟩ := pow_facts_of_two_le hdR
  have hKR : (0 : ℝ) < K := by linarith
  have htN := PVMReverseBlocks.pvmMotionRank_le_unitaryDimension hd
  have hP : 0 < 42 * K ^ 2 := by
    have : 0 < K := by exact_mod_cast hKR
    positivity
  have hle := h.trans (nearBell_tube_factor_le (42 * K ^ 2) (d ^ 4) (3 * d ^ 2 - 2)
    (d ^ 4 - (3 * d ^ 2 - 2)) (Nat.add_sub_cancel' htN) hP (Nat.cast_nonneg _) hε)
  have hall := (exp_le_bell_patch (by omega : 1 ≤ d)).trans (hle.trans
    (mul_le_mul_of_nonneg_right (card_shapes_le_exp_sharp d K) (by positivity)))
  rw [Real.rpow_def_of_pos hε, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp] at hall
  have htR : (((3 * d ^ 2 - 2 : ℕ)) : ℝ) ≤ 3 * (d : ℝ) ^ 2 := by
    have : 3 * d ^ 2 - 2 ≤ 3 * d ^ 2 := Nat.sub_le _ _
    exact_mod_cast this
  have hlogP : Real.log (((42 * K ^ 2 : ℕ)) : ℝ) ≤ 15 / 4 + 2 * Real.log K := by
    push_cast
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    linarith
  have hNlogP := mul_le_mul_of_nonneg_left hlogP (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 4)
  have hlogK := fourth_mul_log_le (d := d) (by omega) hKR
  have hlow := nearBell_lower_order_le hd hK
  have hL : Real.log (1 / ε) = -Real.log ε := by rw [one_div, Real.log_inv]
  rw [hL]
  push_cast at hall hNlogP ⊢
  nlinarith

/-! ### Explicit universal measurement bounds -/

/-- A large tube radius forces `ln(1/ε) ≤ 11 + 4 ln K`, hence `d⁴ ln(1/ε) ≤ 11 K²` once
`K ≥ (19/20) d³`. -/
theorem pvm_large_radius_log_le {d K : ℕ} (hd : 2 ≤ d) (hK19 : 19 / 20 * (d : ℝ) ^ 3 ≤ K)
    {e : ℝ} (he : 0 < e) (hrad : ¬ Real.sqrt (50 / 9 * e) * ((42 * K ^ 2 : ℕ) : ℝ) ≤ 1 / 2) :
    (d : ℝ) ^ 4 * Real.log (1 / e) ≤ 11 * (K : ℝ) ^ 2 := by
  obtain ⟨-, -, -, hl392⟩ := explicit_pvm_numeric_bounds
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hd4, h8, -, h4, h5, -⟩ := pow_facts_of_two_le hdR
  have hKR : (0 : ℝ) < K := by linarith
  have h6 : (d : ℝ) ^ 6 ≤ 400 / 361 * (K : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity) hK19 2
    have e : (19 / 20 * (d : ℝ) ^ 3) ^ 2 = 361 / 400 * (d : ℝ) ^ 6 := by ring
    linarith
  have hdK : 19 / 5 * (d : ℝ) ≤ K := by linarith
  have hlogK := fourth_mul_log_le (d := d) (by omega) hKR
  have hrad' : 1 / 2 < Real.sqrt (50 / 9 * e) * (42 * (K : ℝ) ^ 2) := by
    have := not_le.mp hrad
    push_cast at this
    exact this
  have hsq : (1 / 2 : ℝ) ^ 2 < 50 / 9 * e * (42 * (K : ℝ) ^ 2) ^ 2 := by
    have h := pow_lt_pow_left₀ hrad' (by norm_num) (by norm_num : (2 : ℕ) ≠ 0)
    rwa [mul_pow, Real.sq_sqrt (by positivity)] at h
  have hinv : 1 / e < 39200 * (K : ℝ) ^ 4 := by
    rw [div_lt_iff₀ he]
    have e1 : 50 / 9 * e * (42 * (K : ℝ) ^ 2) ^ 2 = 9800 * (e * (K : ℝ) ^ 4) := by ring
    have e2 : 39200 * (K : ℝ) ^ 4 * e = 4 * (9800 * (e * (K : ℝ) ^ 4)) := by ring
    rw [e1] at hsq
    rw [e2]
    linarith
  have hLK : Real.log (1 / e) ≤ 11 + 4 * Real.log K := by
    have h1 := Real.log_lt_log (by positivity) hinv
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
    push_cast at h1
    linarith
  have hmul := mul_le_mul_of_nonneg_left hLK (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 4)
  have hexp : (d : ℝ) ^ 4 * (11 + 4 * Real.log K) = 11 * (d : ℝ) ^ 4 +
      4 * ((d : ℝ) ^ 4 * Real.log K) := by ring
  have hdKK : (d : ℝ) * K ≤ 5 / 19 * (K : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hdK hKR.le
    linear_combination (5 / 19) * this
  linear_combination hmul + hexp + 4 * hlogK + (11 / 4) * h4 + 6 * h5 + (35 / 4) * h6 +
    4 * hdKK + (91 / 361) * sq_nonneg (K : ℝ)

/-- The precision term from the near-Bell estimate and the cubic floor: if `c² ≤ 1/24`,
`11 c² ≤ 1`, `239 c² ≤ κ` and `2κN ≤ N − t`, then `c d² √ln(1/ε) ≤ K`. -/
theorem PurePVMUniversalScore.precision_le {d K : ℕ} (hd : 2 ≤ d) {e : ℝ} (he : 0 < e)
    (he2 : e ≤ 1 / 2) (hu : PurePVMUniversalScore d K e) {c κ : ℝ} (hc : 0 ≤ c) (hκ : 0 < κ)
    (hc24 : c ^ 2 ≤ 1 / 24) (hc11 : 11 * c ^ 2 ≤ 1) (hcκ : 239 * c ^ 2 ≤ κ)
    (hrank : 2 * κ * (d : ℝ) ^ 4 ≤ ((d ^ 4 - (3 * d ^ 2 - 2) : ℕ) : ℝ)) :
    c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K := by
  obtain ⟨-, -, -, -, h403⟩ := explicit_numeric_bounds
  have : NeZero d := ⟨by omega⟩
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hfl := hu.cubic_floor (by omega) ⟨he.le, by linarith⟩
  have hL0 : 0 ≤ Real.log (1 / e) := Real.log_nonneg ((one_le_div₀ he).mpr (by linarith))
  set L := Real.log (1 / e) with hLdef
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hX0 : 0 ≤ c * (d : ℝ) ^ 2 * Real.sqrt L := by positivity
  apply (pow_le_pow_iff_left₀ hX0 hK0 (by norm_num : (2 : ℕ) ≠ 0)).mp
  have hX2 : (c * (d : ℝ) ^ 2 * Real.sqrt L) ^ 2 = c ^ 2 * (d : ℝ) ^ 4 * L := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hL0]; ring
  rw [hX2]
  have hfl2 : ((d : ℝ) ^ 3 * (1 - e) ^ 2) ^ 2 ≤ (K : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hfl 2
  by_cases hcase : c ^ 2 * L ≤ (d : ℝ) ^ 2 * (1 - e) ^ 4
  · calc c ^ 2 * (d : ℝ) ^ 4 * L = (c ^ 2 * L) * (d : ℝ) ^ 4 := by ring
      _ ≤ (d : ℝ) ^ 2 * (1 - e) ^ 4 * (d : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_right hcase (by positivity)
      _ = ((d : ℝ) ^ 3 * (1 - e) ^ 2) ^ 2 := by ring
      _ ≤ _ := hfl2
  · -- the precision term dominates: `ε < 1/403` and `K ≥ (19/20) d³`
    have h116 : (1 / 16 : ℝ) ≤ (1 - e) ^ 4 := by
      have : (1 / 2 : ℝ) ≤ 1 - e := by linarith
      have := pow_le_pow_left₀ (by norm_num) this 4
      norm_num at this ⊢
      linarith
    have hL6 : 6 < L := by
      by_contra hle
      have h1 : c ^ 2 * L ≤ 1 / 24 * 6 := mul_le_mul hc24 (not_lt.mp hle) hL0 (by norm_num)
      have h2 : (1 / 4 : ℝ) ≤ (d : ℝ) ^ 2 * (1 - e) ^ 4 := by nlinarith
      exact hcase (by linarith)
    have he403 : e < 1 / 403 := by
      have h1 : Real.exp 6 < 1 / e := (Real.lt_log_iff_exp_lt (by positivity)).mp hL6
      have h2 : (403 : ℝ) < 1 / e := lt_of_le_of_lt h403 h1
      rw [lt_div_iff₀ he] at h2
      rw [lt_div_iff₀ (by norm_num)]
      linarith
    obtain ⟨-, h8, -⟩ := pow_facts_of_two_le hdR
    have hK19 : 19 / 20 * (d : ℝ) ^ 3 ≤ K := by
      have h19 : (19 / 20 : ℝ) ≤ (1 - e) ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_left h19 (by positivity : (0 : ℝ) ≤ (d : ℝ) ^ 3)
      linarith
    have hd3 : (d : ℝ) ^ 3 ≤ 2 * K := by linarith
    have hKR : (0 : ℝ) < K := by linarith
    by_cases hrad : Real.sqrt (50 / 9 * e) * ((42 * K ^ 2 : ℕ) : ℝ) ≤ 1 / 2
    · have hm := nearBell_haar_le_sharp hd hd3 he (by linarith) hrad
      rw [hu.reachable_eq_univ, Set.inter_univ] at hm
      have hle := (bellNeighborhood_mass_ge d).trans hm
      rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
      have hlog := nearBell_log_le hd hK19 he hle
      have hκN : κ * ((d : ℝ) ^ 4 * L) ≤ ((d ^ 4 - (3 * d ^ 2 - 2) : ℕ) : ℝ) / 2 * L := by
        have := mul_le_mul_of_nonneg_right hrank hL0
        have e1 : 2 * κ * (d : ℝ) ^ 4 * L = 2 * (κ * ((d : ℝ) ^ 4 * L)) := by ring
        have e2 : ((d ^ 4 - (3 * d ^ 2 - 2) : ℕ) : ℝ) * L =
            2 * (((d ^ 4 - (3 * d ^ 2 - 2) : ℕ) : ℝ) / 2 * L) := by ring
        linarith
      have hNL : κ * ((d : ℝ) ^ 4 * L) ≤ 239 * (K : ℝ) ^ 2 := hκN.trans hlog
      have hκX : κ * (c ^ 2 * (d : ℝ) ^ 4 * L) ≤ κ * (K : ℝ) ^ 2 := by
        calc κ * (c ^ 2 * (d : ℝ) ^ 4 * L) = c ^ 2 * (κ * ((d : ℝ) ^ 4 * L)) := by ring
          _ ≤ c ^ 2 * (239 * (K : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hNL (sq_nonneg c)
          _ = (239 * c ^ 2) * (K : ℝ) ^ 2 := by ring
          _ ≤ κ * (K : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hcκ (sq_nonneg _)
      exact le_of_mul_le_mul_left hκX hκ
    · have hd4L := pvm_large_radius_log_le hd hK19 he hrad
      calc c ^ 2 * (d : ℝ) ^ 4 * L = c ^ 2 * ((d : ℝ) ^ 4 * L) := by ring
        _ ≤ c ^ 2 * (11 * (K : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hd4L (sq_nonneg c)
        _ = (11 * c ^ 2) * (K : ℝ) ^ 2 := by ring
        _ ≤ 1 * (K : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hc11 (sq_nonneg _)
        _ = _ := one_mul _

/-- `N − t ≥ 3N/8` for every `d ≥ 2`. -/
theorem two_mul_pvm_kappa_le_of_two {d : ℕ} (hd : 2 ≤ d) :
    2 * (3 / 16 : ℝ) * (d : ℝ) ^ 4 ≤ ((d ^ 4 - (3 * d ^ 2 - 2) : ℕ) : ℝ) := by
  have ht := PVMReverseBlocks.pvmMotionRank_le_unitaryDimension hd
  rw [Nat.cast_sub ht]
  have hD : 4 ≤ d ^ 2 := by nlinarith
  have h2 : 2 ≤ 3 * d ^ 2 := by omega
  rw [Nat.cast_sub h2]
  push_cast
  have hDR : (4 : ℝ) ≤ (d : ℝ) ^ 2 := by exact_mod_cast hD
  nlinarith

/-- `N − t ≥ 2N/3` for every `d ≥ 3`. -/
theorem two_mul_pvm_kappa_le_of_three {d : ℕ} (hd : 3 ≤ d) :
    2 * (1 / 3 : ℝ) * (d : ℝ) ^ 4 ≤ ((d ^ 4 - (3 * d ^ 2 - 2) : ℕ) : ℝ) := by
  have ht := PVMReverseBlocks.pvmMotionRank_le_unitaryDimension (by omega : 2 ≤ d)
  rw [Nat.cast_sub ht]
  have hD : 9 ≤ d ^ 2 := by nlinarith
  have h2 : 2 ≤ 3 * d ^ 2 := by omega
  rw [Nat.cast_sub h2]
  push_cast
  have hDR : (9 : ℝ) ≤ (d : ℝ) ^ 2 := by exact_mod_cast hD
  nlinarith

/-- **Explicit universal PVM bound, every `d ≥ 2`.**
`K ≥ max(d³(1 − ε)², d² √ln(1/ε) / 36)`. -/
theorem PurePVMUniversalScore.explicit_resource_bound {d K : ℕ} (hd : 2 ≤ d) {e : ℝ}
    (he : 0 < e) (he2 : e ≤ 1 / 2) (hu : PurePVMUniversalScore d K e) :
    max ((d : ℝ) ^ 3 * (1 - e) ^ 2) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) / 36) ≤ (K : ℝ) := by
  refine max_le (hu.cubic_floor (by omega) ⟨he.le, by linarith⟩) ?_
  have h := hu.precision_le hd he he2 (c := 1 / 36) (κ := 3 / 16) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (two_mul_pvm_kappa_le_of_two hd)
  linarith

/-- **Explicit universal PVM bound, every `d ≥ 3`.**
`K ≥ max(d³(1 − ε)², d² √ln(1/ε) / 27)`. -/
theorem PurePVMUniversalScore.explicit_resource_bound_of_three {d K : ℕ} (hd : 3 ≤ d) {e : ℝ}
    (he : 0 < e) (he2 : e ≤ 1 / 2) (hu : PurePVMUniversalScore d K e) :
    max ((d : ℝ) ^ 3 * (1 - e) ^ 2) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) / 27) ≤ (K : ℝ) := by
  refine max_le (hu.cubic_floor (by omega) ⟨he.le, by linarith⟩) ?_
  have h := hu.precision_le (by omega) he he2 (c := 1 / 27) (κ := 1 / 3) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (two_mul_pvm_kappa_le_of_three hd)
  linarith

/-- The explicit universal PVM bound for pure and common-map mixed resources, in PVM score
and worst-case joint total variation. -/
theorem pvmUniversal_explicit (d K : ℕ) (hd : 2 ≤ d) (e : ℝ) (he : 0 < e) (he2 : e ≤ 1 / 2) :
    (PurePVMUniversalScore d K e →
      max ((d : ℝ) ^ 3 * (1 - e) ^ 2) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) / 36) ≤ (K : ℝ)) ∧
    (MixedPVMUniversalScore d K e →
      max ((d : ℝ) ^ 3 * (1 - e) ^ 2) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) / 36) ≤ (K : ℝ)) ∧
    (PurePVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
      max ((d : ℝ) ^ 3 * (1 - e) ^ 2) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) / 36) ≤ (K : ℝ)) ∧
    (MixedPVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
      max ((d : ℝ) ^ 3 * (1 - e) ^ 2) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) / 36) ≤ (K : ℝ)) := by
  have hd0 : 0 < d := by omega
  have hpure (hu : PurePVMUniversalScore d K e) := hu.explicit_resource_bound hd he he2
  have hmixed (hm : MixedPVMUniversalScore d K e) :=
    hpure ((mixedPVMUniversalScore_iff_pure d K e).mp hm)
  exact ⟨hpure, hmixed, fun h => hpure (h.score hd0), fun h => hmixed (h.score hd0)⟩

/-- The `d ≥ 3` explicit universal PVM bound. -/
theorem pvmUniversal_explicit_of_three (d K : ℕ) (hd : 3 ≤ d) (e : ℝ) (he : 0 < e)
    (he2 : e ≤ 1 / 2) :
    (PurePVMUniversalScore d K e →
      max ((d : ℝ) ^ 3 * (1 - e) ^ 2) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) / 27) ≤ (K : ℝ)) ∧
    (MixedPVMUniversalScore d K e →
      max ((d : ℝ) ^ 3 * (1 - e) ^ 2) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) / 27) ≤ (K : ℝ)) ∧
    (PurePVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
      max ((d : ℝ) ^ 3 * (1 - e) ^ 2) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) / 27) ≤ (K : ℝ)) ∧
    (MixedPVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
      max ((d : ℝ) ^ 3 * (1 - e) ^ 2) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) / 27) ≤ (K : ℝ)) := by
  have hd0 : 0 < d := by omega
  have hpure (hu : PurePVMUniversalScore d K e) := hu.explicit_resource_bound_of_three hd he he2
  have hmixed (hm : MixedPVMUniversalScore d K e) :=
    hpure ((mixedPVMUniversalScore_iff_pure d K e).mp hm)
  exact ⟨hpure, hmixed, fun h => hpure (h.score hd0), fun h => hmixed (h.score hd0)⟩

/-- Theorem B(ii) in its displayed form with `c = 1/36`:
`K ≥ (1/36) max(d³, d² √ln(1/ε))`. -/
theorem pvmUniversal_max_explicit (d K : ℕ) (hd : 2 ≤ d) (e : ℝ) (he : 0 < e)
    (he2 : e ≤ 1 / 2) :
    (PurePVMUniversalScore d K e →
      1 / 36 * max ((d : ℝ) ^ 3) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e))) ≤ K) ∧
    (MixedPVMUniversalScore d K e →
      1 / 36 * max ((d : ℝ) ^ 3) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e))) ≤ K) ∧
    (PurePVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
      1 / 36 * max ((d : ℝ) ^ 3) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e))) ≤ K) ∧
    (MixedPVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
      1 / 36 * max ((d : ℝ) ^ 3) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e))) ≤ K) := by
  have hconv (h : max ((d : ℝ) ^ 3 * (1 - e) ^ 2)
      ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) / 36) ≤ (K : ℝ)) :
      1 / 36 * max ((d : ℝ) ^ 3) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e))) ≤ K := by
    have h1 := (le_max_left _ _).trans h
    have h2 := (le_max_right _ _).trans h
    have hq : (1 / 4 : ℝ) ≤ (1 - e) ^ 2 := by nlinarith
    have hd3 : (0 : ℝ) ≤ (d : ℝ) ^ 3 := by positivity
    rw [mul_max_of_nonneg _ _ (by norm_num)]
    refine max_le ?_ (by linarith)
    nlinarith
  obtain ⟨hp, hm, htp, htm⟩ := pvmUniversal_explicit d K hd e he he2
  exact ⟨fun h => hconv (hp h), fun h => hconv (hm h), fun h => hconv (htp h),
    fun h => hconv (htm h)⟩

/-- Theorem B(ii), qubit form with explicit offset: at `d = 2ⁿ`,
`log₂ K ≥ max(3n − 2, 2n + ½ log₂ ln(1/ε) − 6)`. -/
theorem pvmUniversal_qubit_explicit (n K : ℕ) (hn : 1 ≤ n) (e : ℝ) (he : 0 < e)
    (he2 : e ≤ 1 / 2) :
    (PurePVMUniversalScore (2 ^ n) K e →
      max (3 * (n : ℝ) - 2) (2 * (n : ℝ) + 1 / 2 * Real.logb 2 (Real.log (1 / e)) - 6) ≤
        Real.logb 2 K) ∧
    (MixedPVMUniversalScore (2 ^ n) K e →
      max (3 * (n : ℝ) - 2) (2 * (n : ℝ) + 1 / 2 * Real.logb 2 (Real.log (1 / e)) - 6) ≤
        Real.logb 2 K) := by
  have hd : 2 ≤ 2 ^ n := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) hn
  have hpure (hu : PurePVMUniversalScore (2 ^ n) K e) :
      max (3 * (n : ℝ) - 2) (2 * (n : ℝ) + 1 / 2 * Real.logb 2 (Real.log (1 / e)) - 6) ≤
        Real.logb 2 K := by
    refine max_le (hu.cubic_qubit_floor he.le he2) ?_
    have hb := (le_max_right _ _).trans (hu.explicit_resource_bound hd he he2)
    have h' : 1 / 2 ^ 6 * (((2 ^ n : ℕ) : ℝ)) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K := by
      have hs := Real.sqrt_nonneg (Real.log (1 / e))
      have hp : (0 : ℝ) ≤ (((2 ^ n : ℕ) : ℝ)) ^ 2 * Real.sqrt (Real.log (1 / e)) := by positivity
      linarith
    have hq := strong_qubit_of_resource (c := 1 / 2 ^ 6) (by norm_num) he he2 n h'
    rwa [logb_two_inv_two_pow 6] at hq
  exact ⟨hpure, fun hm => hpure ((mixedPVMUniversalScore_iff_pure _ K e).mp hm)⟩

/-- Theorem B(ii), qubit form with offset `5` once `n ≥ 2`. -/
theorem pvmUniversal_qubit_explicit_of_two (n K : ℕ) (hn : 2 ≤ n) (e : ℝ) (he : 0 < e)
    (he2 : e ≤ 1 / 2) :
    (PurePVMUniversalScore (2 ^ n) K e →
      max (3 * (n : ℝ) - 2) (2 * (n : ℝ) + 1 / 2 * Real.logb 2 (Real.log (1 / e)) - 5) ≤
        Real.logb 2 K) ∧
    (MixedPVMUniversalScore (2 ^ n) K e →
      max (3 * (n : ℝ) - 2) (2 * (n : ℝ) + 1 / 2 * Real.logb 2 (Real.log (1 / e)) - 5) ≤
        Real.logb 2 K) := by
  have hd : 3 ≤ 2 ^ n := by
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  have hpure (hu : PurePVMUniversalScore (2 ^ n) K e) :
      max (3 * (n : ℝ) - 2) (2 * (n : ℝ) + 1 / 2 * Real.logb 2 (Real.log (1 / e)) - 5) ≤
        Real.logb 2 K := by
    refine max_le (hu.cubic_qubit_floor he.le he2) ?_
    have hb := (le_max_right _ _).trans (hu.explicit_resource_bound_of_three hd he he2)
    have h' : 1 / 2 ^ 5 * (((2 ^ n : ℕ) : ℝ)) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K := by
      have hp : (0 : ℝ) ≤ (((2 ^ n : ℕ) : ℝ)) ^ 2 * Real.sqrt (Real.log (1 / e)) := by positivity
      linarith
    have hq := strong_qubit_of_resource (c := 1 / 2 ^ 5) (by norm_num) he he2 n h'
    rwa [logb_two_inv_two_pow 5] at hq
  exact ⟨hpure, fun hm => hpure ((mixedPVMUniversalScore_iff_pure _ K e).mp hm)⟩

end NLQCLean

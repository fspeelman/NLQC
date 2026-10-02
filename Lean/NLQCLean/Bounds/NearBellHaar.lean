import NLQCLean.Bounds.NearBellWitnessCover
import NLQCLean.Bounds.NearBellHaarArithmetic
import NLQCLean.Geometry.PVMPolynomialTubeConditional
import NLQCLean.Geometry.UnitaryHaarInverse
import NLQCLean.Models.PVMMixedReachability
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Haar volume near a maximally entangled basis (`thm:bell-haar`)

For `d ≥ 2`, `K ≥ d³/4` and `0 < ε ≤ 1/2`, the bases near the generalized
Bell basis that some protocol of footprint at most `K` approximates with PVM
score deficit at most `ε` have Haar measure at most
`min 1 (exp(C K²) ε^{d⁴/16})`, for one constant `C` depending only on the
geometry input. The witnesses have `O(K²)` coordinates (slim near-Bell
shapes), so the existing PVM tube estimate with the slim budget `256 K²`
applies; the condition `K ≥ d³/4` absorbs the polynomial prefactors.
-/

namespace NLQCLean

open MeasureTheory Matrix
open scoped ENNReal Matrix.Norms.Frobenius

section Arithmetic

theorem card_shapes_le_exp {d K : ℕ} (hd : 2 ≤ d) (hd3 : (d : ℝ) ^ 3 ≤ 2 * K) :
    ((K ^ 3 * 2 ^ (K + d ^ 2) : ℕ) : ℝ) ≤ Real.exp (6 * (K : ℝ) ^ 2) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hK1 := one_le_of_cube_le hdR hd3
  have hd2 := sq_le_of_cube_le hdR hd3
  push_cast
  have hKe : (K : ℝ) ≤ Real.exp K := by
    have := Real.add_one_le_exp (K : ℝ)
    linarith
  have h1 : (K : ℝ) ^ 3 ≤ Real.exp (3 * K) := by
    rw [show (3 : ℝ) * K = K + K + K by ring, Real.exp_add, Real.exp_add]
    have h0 : (0 : ℝ) ≤ K := by linarith
    calc (K : ℝ) ^ 3 = K * K * K := by ring
      _ ≤ Real.exp K * Real.exp K * Real.exp K :=
        mul_le_mul (mul_le_mul hKe hKe h0 (Real.exp_pos _).le) hKe h0 (by positivity)
  have h2 : (2 : ℝ) ^ (K + d ^ 2) ≤ Real.exp ((K : ℝ) + (d : ℝ) ^ 2) := by
    have h22 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    calc (2 : ℝ) ^ (K + d ^ 2) ≤ Real.exp 1 ^ (K + d ^ 2) :=
          pow_le_pow_left₀ (by norm_num) h22 _
      _ = Real.exp ((K : ℝ) + (d : ℝ) ^ 2) := by
          rw [← Real.exp_nat_mul]
          push_cast
          ring_nf
  calc (K : ℝ) ^ 3 * 2 ^ (K + d ^ 2) ≤ Real.exp (3 * K) * Real.exp ((K : ℝ) + (d : ℝ) ^ 2) :=
        mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
    _ = Real.exp (4 * K + (d : ℝ) ^ 2) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (6 * (K : ℝ) ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith

/-- The near-Bell witness distance `√(50ε/9)` is at most `(8/3)√ε`. -/
theorem sqrt_fifty_ninths_mul_le {ε : ℝ} (hε : 0 ≤ ε) :
    Real.sqrt (50 / 9 * ε) ≤ 8 / 3 * Real.sqrt ε := by
  rw [show (8 / 3 : ℝ) * Real.sqrt ε = Real.sqrt (64 / 9 * ε) by
    rw [Real.sqrt_mul (by norm_num), show (64 / 9 : ℝ) = (8 / 3) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by nlinarith)

/-- The tube prefactors are absorbed into `exp(C K²) ε^{d⁴/16}`. -/
theorem nearBell_tube_rhs_le {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {d K : ℕ} (hd : 2 ≤ d)
    (hd3 : (d : ℝ) ^ 3 ≤ 2 * K) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ((K ^ 3 * 2 ^ (K + d ^ 2) : ℕ) : ℝ) *
        (Real.exp (C₀ * (((256 * K ^ 2 : ℕ) : ℝ) + (d : ℝ) ^ 4)) *
          (C₀ * ((256 * K ^ 2 : ℕ) : ℝ)) ^ (3 * d ^ 2 - 2) *
          (C₀ * (Real.sqrt (50 / 9 * ε) * ((256 * K ^ 2 : ℕ) : ℝ))) ^ (d ^ 4 - (3 * d ^ 2 - 2))) ≤
      Real.exp ((300 * C₀ + 4 * Real.log (683 * C₀) + 30) * (K : ℝ) ^ 2) *
        ε ^ ((d : ℝ) ^ 4 / 16) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hK1 := one_le_of_cube_le hdR hd3
  have hN := fourth_le_of_cube_le hdR hd3
  have hC0 : 0 ≤ C₀ := by linarith
  set a : ℝ := 683 * C₀ with ha
  have ha1 : 1 ≤ a := by linarith
  have hs0 := Real.sqrt_nonneg ε
  have hs1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε1
  set t := 3 * d ^ 2 - 2 with ht
  set n := d ^ 4 - t with hn
  have htN : t ≤ d ^ 4 := PVMReverseBlocks.pvmMotionRank_le_unitaryDimension hd
  have hnt : n + t = d ^ 4 := by omega
  push_cast
  -- the two power factors
  have hpow1 : (C₀ * (256 * (K : ℝ) ^ 2)) ^ t ≤ (a * (K : ℝ) ^ 2) ^ t :=
    pow_le_pow_left₀ (by positivity) (by nlinarith [sq_nonneg (K : ℝ)]) _
  have hpow2 : (C₀ * (Real.sqrt (50 / 9 * ε) * (256 * (K : ℝ) ^ 2))) ^ n ≤
      (a * (K : ℝ) ^ 2) ^ n * Real.sqrt ε ^ n := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have h83 := sqrt_fifty_ninths_mul_le hε0.le
    have he : C₀ * (8 / 3 * Real.sqrt ε * (256 * (K : ℝ) ^ 2)) =
        (2048 / 3 * C₀) * (K : ℝ) ^ 2 * Real.sqrt ε := by ring
    calc C₀ * (Real.sqrt (50 / 9 * ε) * (256 * (K : ℝ) ^ 2))
        ≤ C₀ * (8 / 3 * Real.sqrt ε * (256 * (K : ℝ) ^ 2)) := by gcongr
      _ ≤ a * (K : ℝ) ^ 2 * Real.sqrt ε := by
        rw [he, ha]
        have hk : 0 ≤ C₀ * (K : ℝ) ^ 2 * Real.sqrt ε := by positivity
        nlinarith
  have hcomb : (a * (K : ℝ) ^ 2) ^ t * (a * (K : ℝ) ^ 2) ^ n = (a * (K : ℝ) ^ 2) ^ ((d : ℝ) ^ 4) := by
    rw [← pow_add, add_comm, hnt, ← Real.rpow_natCast]
    push_cast
    rfl
  have hbig := pow_sq_le_exp_of_cube_le hdR hd3 ha1
  -- the epsilon power
  have hn8 : (d : ℝ) ^ 4 / 16 ≤ (n : ℝ) / 2 := by
    have hcast : (n : ℝ) = (d : ℝ) ^ 4 - t := by
      rw [hn, Nat.cast_sub htN]
      push_cast
      ring
    have htR : (t : ℝ) ≤ 3 * (d : ℝ) ^ 2 := by
      rw [ht]
      have : 3 * d ^ 2 - 2 ≤ 3 * d ^ 2 := Nat.sub_le _ _
      exact_mod_cast this
    rw [hcast]
    have hd2 : (4 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
    have h4 : 4 * (d : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 * (d : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hd2 (sq_nonneg _)
    nlinarith
  have heps : Real.sqrt ε ^ n ≤ ε ^ ((d : ℝ) ^ 4 / 16) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hε0.le]
    exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (by linarith)
  have hexp1 : Real.exp (C₀ * (256 * (K : ℝ) ^ 2 + (d : ℝ) ^ 4)) ≤ Real.exp (260 * C₀ * (K : ℝ) ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hcard := card_shapes_le_exp hd hd3
  push_cast at hcard
  have hlog : 0 ≤ Real.log a := Real.log_nonneg ha1
  calc (K : ℝ) ^ 3 * 2 ^ (K + d ^ 2) *
        (Real.exp (C₀ * (256 * (K : ℝ) ^ 2 + (d : ℝ) ^ 4)) * (C₀ * (256 * (K : ℝ) ^ 2)) ^ t *
          (C₀ * (Real.sqrt (50 / 9 * ε) * (256 * (K : ℝ) ^ 2))) ^ n)
      ≤ Real.exp (6 * (K : ℝ) ^ 2) *
          (Real.exp (260 * C₀ * (K : ℝ) ^ 2) * (a * (K : ℝ) ^ 2) ^ t *
            ((a * (K : ℝ) ^ 2) ^ n * Real.sqrt ε ^ n)) := by
        refine mul_le_mul hcard (mul_le_mul (mul_le_mul hexp1 hpow1 (by positivity)
          (Real.exp_pos _).le) hpow2 (by positivity) (by positivity)) (by positivity)
          (Real.exp_pos _).le
    _ = Real.exp (6 * (K : ℝ) ^ 2) * Real.exp (260 * C₀ * (K : ℝ) ^ 2) *
          ((a * (K : ℝ) ^ 2) ^ t * (a * (K : ℝ) ^ 2) ^ n) * Real.sqrt ε ^ n := by ring
    _ ≤ Real.exp (6 * (K : ℝ) ^ 2) * Real.exp (260 * C₀ * (K : ℝ) ^ 2) *
          Real.exp ((4 * Real.log a + 12) * (K : ℝ) ^ 2) * ε ^ ((d : ℝ) ^ 4 / 16) := by
        rw [hcomb]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hbig (by positivity)) heps (by positivity)
          (by positivity)
    _ = Real.exp ((18 + 260 * C₀ + 4 * Real.log a) * (K : ℝ) ^ 2) * ε ^ ((d : ℝ) ^ 4 / 16) := by
        rw [← Real.exp_add, ← Real.exp_add]
        ring_nf
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))) (by positivity)
        linarith

/-- Small exponent: the bound is trivial once `(d⁴/16) log(1/ε) ≤ C K²`. -/
theorem one_le_exp_mul_rpow {C L ε N : ℝ} (hε : 0 < ε) (hL : Real.log (1 / ε) ≤ L)
    (hN : 0 ≤ N) (h : N / 16 * L ≤ C) : 1 ≤ Real.exp C * ε ^ (N / 16) := by
  rw [Real.rpow_def_of_pos hε, ← Real.exp_add]
  apply Real.one_le_exp
  have hl : Real.log ε = -Real.log (1 / ε) := by
    rw [one_div, Real.log_inv, neg_neg]
  rw [hl]
  nlinarith

end Arithmetic


section Haar

variable {d : ℕ}

/-- Every accurate target near the Bell basis is the inverse of a slim
witness target. -/
theorem nearBell_mem_inv_witnessTargets [NeZero d] (hd2 : 2 ≤ d) {K : ℕ}
    (hd3 : (d : ℝ) ^ 3 ≤ 2 * K) (hfloor : d ^ 2 ≤ 4 * K) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 256) {M : unitaryGroup (Fin d × Fin d) ℂ} (hM : M ∈ bellNeighborhood d)
    (hR : M ∈ purePVMReachable d K ε) :
    ∃ s : PVMReverseShape d K, ∃ hs : s.IsNearBell,
      M⁻¹ ∈ PVMReverseBlocks.witnessTargets s (by omega) hfloor
        (s.admissibleBudget_nearBell hd2 hs hd3) (Real.sqrt (50 / 9 * ε))
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
    (by omega) hfloor (s.admissibleBudget_nearBell hd2 hs hd3) (Real.sqrt (50 / 9 * ε)) hx hdef
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᴴ hov
  refine ⟨s, hs, y, hy, ?_⟩
  rw [PVMReverseBlocks.coordinateOverlapPolynomial_eq_raw_of_mem s (by omega) hfloor
    (s.admissibleBudget_nearBell hd2 hs hd3) hy, dist_comm, dist_eq_norm,
    PVMReverseBlocks.coe_unitary_inv_eq_conjTranspose]
  exact hdist

theorem min_one_of_one_le {μ : ℝ≥0∞} (hμ : μ ≤ 1) {X : ℝ} (hX : 1 ≤ X) :
    μ ≤ min 1 (ENNReal.ofReal X) :=
  le_min hμ (hμ.trans (ENNReal.one_le_ofReal.mpr hX))

/-- **`thm:bell-haar`**, conditional on the polynomial image-volume property. -/
theorem exists_nearBell_haar_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d K : ℕ) [NeZero d], 2 ≤ d → (d : ℝ) ^ 3 ≤ 4 * K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        unitaryHaar (Fin d × Fin d) (bellNeighborhood d ∩ purePVMReachable d K ε) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (K : ℝ) ^ 2) * ε ^ ((d : ℝ) ^ 4 / 16))) := by
  obtain ⟨C₀, hC₀, hbound⟩ := PVMReverseBlocks.exists_witness_haar_constant_of_budget hGeom
  have hlog0 : 0 ≤ Real.log (683 * C₀) := Real.log_nonneg (by linarith)
  refine ⟨300 * C₀ + 4 * Real.log (683 * C₀) + 30, by linarith, ?_⟩
  intro d K _ hd2 hd34 ε hε hε2
  set C := 300 * C₀ + 4 * Real.log (683 * C₀) + 30 with hC
  have hC30 : 30 ≤ C := by linarith
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd2
  have hprob : unitaryHaar (Fin d × Fin d) (bellNeighborhood d ∩ purePVMReachable d K ε) ≤ 1 :=
    prob_le_one
  have hl2 := Real.log_two_lt_d9
  -- large errors make the bound trivial
  have hN16 : (d : ℝ) ^ 4 ≤ 16 * (K : ℝ) ^ 2 := by
    have h := fourth_le_of_cube_le (K := 2 * (K : ℝ)) hdR (by linarith)
    nlinarith
  by_cases hsmall : ε ≤ 1 / 256
  swap
  · refine min_one_of_one_le hprob (one_le_exp_mul_rpow hε (L := 6) ?_ (by positivity) ?_)
    · have h1 : 1 / ε ≤ 256 := by
        rw [div_le_iff₀ hε]
        linarith
      calc Real.log (1 / ε) ≤ Real.log 256 := Real.log_le_log (by positivity) h1
        _ = 8 * Real.log 2 := by
            rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]
            norm_num
        _ ≤ 6 := by linarith
    · nlinarith [sq_nonneg (K : ℝ)]
  by_cases hd3 : (d : ℝ) ^ 3 ≤ 2 * K
  swap
  · have hempty : bellNeighborhood d ∩ purePVMReachable d K ε = ∅ := by
      ext M
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hM hR
      obtain ⟨t, P, hK, hscore⟩ := hR
      exact hd3 (P.cube_le_two_mul_of_mem_bellNeighborhood hM hK hsmall hscore)
    rw [hempty, measure_empty]
    exact zero_le
  have hK1 := one_le_of_cube_le hdR hd3
  have hN4 := fourth_le_of_cube_le hdR hd3
  have hNlog := fourth_mul_log_le_of_cube_le hdR hd3
  set δ := Real.sqrt (50 / 9 * ε) with hδ
  set B : ℕ := 256 * K ^ 2 with hB
  set r := δ * B with hr
  have hs0 := Real.sqrt_nonneg ε
  by_cases hrad : r ≤ 1 / 2
  swap
  · -- the radius condition fails only for errors at least `c / K⁴`
    refine min_one_of_one_le hprob
      (one_le_exp_mul_rpow hε (L := 17 + 4 * Real.log K) ?_ (by positivity) ?_)
    · have hsq : 3 / (4096 * (K : ℝ) ^ 2) < Real.sqrt ε := by
        rw [div_lt_iff₀ (by positivity)]
        have : r ≤ 2048 / 3 * (K : ℝ) ^ 2 * Real.sqrt ε := by
          rw [hr, hδ, hB]
          push_cast
          have h83 := sqrt_fifty_ninths_mul_le hε.le
          nlinarith [sq_nonneg (K : ℝ)]
        nlinarith
      have hε' : 9 / (4096 ^ 2 * (K : ℝ) ^ 4) < ε := by
        have h1 := pow_lt_pow_left₀ hsq (by positivity) (by norm_num : (2 : ℕ) ≠ 0)
        rw [Real.sq_sqrt hε.le, div_pow] at h1
        calc 9 / (4096 ^ 2 * (K : ℝ) ^ 4) = 3 ^ 2 / (4096 * (K : ℝ) ^ 2) ^ 2 := by ring
          _ < ε := h1
      have h1 : 1 / ε ≤ 4096 ^ 2 * (K : ℝ) ^ 4 := by
        rw [div_le_iff₀ hε]
        rw [div_lt_iff₀ (by positivity)] at hε'
        nlinarith
      calc Real.log (1 / ε) ≤ Real.log (4096 ^ 2 * (K : ℝ) ^ 4) :=
            Real.log_le_log (by positivity) h1
        _ = 24 * Real.log 2 + 4 * Real.log K := by
            rw [show (4096 : ℝ) ^ 2 * (K : ℝ) ^ 4 = 2 ^ 24 * (K : ℝ) ^ 4 by norm_num,
              Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
            push_cast
            ring
        _ ≤ 17 + 4 * Real.log K := by linarith
    · nlinarith [sq_nonneg (K : ℝ)]
  -- the main case
  have hfloorR : (d : ℝ) ^ 2 ≤ 4 * K := by nlinarith [sq_le_of_cube_le hdR hd3]
  have hfloor : d ^ 2 ≤ 4 * K := by exact_mod_cast hfloorR
  have hd0 : 0 < d := by omega
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
      PVMReverseBlocks.witnessTargets s hd0 hfloor (s.admissibleBudget_nearBell hd2 hs hd3) δ
        ((d : ℝ) * δ)
    else ∅
  have hcover : bellNeighborhood d ∩ purePVMReachable d K ε ⊆ Inv.inv ⁻¹' ⋃ s, T s := by
    rintro M ⟨hM, hR⟩
    obtain ⟨s, hs, hmem⟩ := nearBell_mem_inv_witnessTargets hd2 hd3 hfloor hε.le hsmall hM hR
    exact Set.mem_iUnion.mpr ⟨s, by simp only [T, dite_eq_left hs]; exact hmem⟩
  set Bnd := Real.exp (C₀ * ((B : ℝ) + (d : ℝ) ^ 4)) * (C₀ * (B : ℝ)) ^ (3 * d ^ 2 - 2) *
    (C₀ * r) ^ (d ^ 4 - (3 * d ^ 2 - 2)) with hBnd
  have hT : ∀ s, unitaryHaar (Fin d × Fin d) (T s) ≤ ENNReal.ofReal Bnd := by
    intro s
    by_cases hs : s.IsNearBell
    · simp only [T, dite_eq_left hs]
      exact hbound d K s hd0 hfloor B (s.admissibleBudget_nearBell hd2 hs hd3) hd2 δ r
        ((d : ℝ) * δ) hδ0 hδ1 hr0 hrad le_rfl hρ _
        (PVMReverseBlocks.measurableSet_witnessTargets s hd0 hfloor _ δ _) (fun U hU => hU)
    · simp only [T, dite_eq_right hs, measure_empty]
      exact zero_le
  have harith := nearBell_tube_rhs_le hC₀ hd2 hd3 hε (by linarith)
  have hBnd0 : 0 ≤ Bnd := by positivity
  have hmain : unitaryHaar (Fin d × Fin d) (bellNeighborhood d ∩ purePVMReachable d K ε) ≤
      ENNReal.ofReal (Real.exp (C * (K : ℝ) ^ 2) * ε ^ ((d : ℝ) ^ 4 / 16)) := by
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
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          have hrB : r = Real.sqrt (50 / 9 * ε) * ((256 * K ^ 2 : ℕ) : ℝ) := by rw [hr, hδ, hB]
          rw [hBnd, hrB, hB]
          exact harith
  exact le_min hprob hmain

end Haar

end NLQCLean

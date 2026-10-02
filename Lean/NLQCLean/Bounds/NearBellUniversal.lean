import NLQCLean.Geometry.DirectVolume.Assembly
import NLQCLean.Bounds.NearBellHaar
import NLQCLean.Bounds.SwapNeighborhoodHaar
import NLQCLean.Bounds.StrongUniversalResources
import NLQCLean.Models.PVMUniversalReachability
import NLQCLean.Bounds.Quantitative

/-!
# Universal measurement approximation (`cor:universal-pvm`, Theorem B(ii))

The ball of bases around the generalized Bell basis has Haar mass at least
`(1 + 8 d^{3/2})^{-2N}`: an operator-norm net argument at radius
`1/(4 d^{3/2})`. Every universal PVM footprint makes the ball reachable and has
`K ≥ d³/4`, so comparing with `thm:bell-haar` gives
`K ≥ c d² √log(1/ε)`; with the cubic floor this is `K ≥ c max(d³, d² √log(1/ε))`.
-/

namespace NLQCLean

universe u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

open Matrix MeasureTheory Module
open scoped ENNReal

section Patch

variable (n : Type*) [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.L2Operator in
/-- An operator-norm `η`-net of the unitary group with at most `(1 + 2/η)^(2N)` centres. -/
theorem exists_unitary_opNorm_net_of_pos {η : ℝ} (hη : 0 < η) :
    ∃ F : Finset (Matrix n n ℂ), (∀ U ∈ F, U ∈ Matrix.unitaryGroup n ℂ) ∧
      (F.card : ℝ) ≤ (1 + 2 / η) ^ (2 * Fintype.card n ^ 2) ∧
      ∀ V ∈ Matrix.unitaryGroup n ℂ, ∃ U ∈ F, opNorm (V - U) ≤ η := by
  obtain ⟨F, hFA, hcard, hnet⟩ := exists_finset_net_of_subset_closedBall
    (E := Matrix n n ℂ) (A := (Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ)))
    (fun V hV => show opNorm V ≤ 1 from
      (show IsIsometry V from Matrix.mem_unitaryGroup_iff'.mp hV).opNorm_le_one) hη
  have hfin : finrank ℝ (Matrix n n ℂ) = 2 * Fintype.card n ^ 2 := by
    rw [Module.finrank_matrix, Complex.finrank_real_complex]
    ring
  rw [hfin] at hcard
  exact ⟨F, hFA, hcard, fun V hV => hnet V hV⟩

/-- Each operator `η`-ball around the identity has Haar mass at least `(1+2/η)^(−2N)`. -/
theorem inv_pow_le_unitaryHaar_unitaryOpBall_one {η : ℝ} (hη : 0 < η) :
    ENNReal.ofReal (((1 + 2 / η) ^ (2 * Fintype.card n ^ 2))⁻¹) ≤
      unitaryHaar n (unitaryOpBall n 1 η) := by
  obtain ⟨F, hFU, hcard, hnet⟩ := exists_unitary_opNorm_net_of_pos n hη
  set m := unitaryHaar n (unitaryOpBall n 1 η) with hm
  have hcov : (Set.univ : Set (Matrix.unitaryGroup n ℂ)) ⊆ ⋃ W ∈ F, unitaryOpBall n W η :=
    fun V _ => by
      obtain ⟨W, hW, h⟩ := hnet V V.property
      exact Set.mem_biUnion hW h
  have hsum : ∑ W ∈ F, unitaryHaar n (unitaryOpBall n W η) = F.card * m := by
    rw [Finset.sum_congr rfl (fun W hW => unitaryHaar_unitaryOpBall n ⟨W, hFU W hW⟩ η),
      Finset.sum_const, nsmul_eq_mul]
  have h1 : 1 ≤ (F.card : ℝ≥0∞) * m := by
    calc (1 : ℝ≥0∞) = unitaryHaar n Set.univ := (measure_univ).symm
      _ ≤ unitaryHaar n (⋃ W ∈ F, unitaryOpBall n W η) := measure_mono hcov
      _ ≤ ∑ W ∈ F, unitaryHaar n (unitaryOpBall n W η) := measure_biUnion_finset_le _ _
      _ = _ := hsum
  have hpos : (0 : ℝ) < (1 + 2 / η) ^ (2 * Fintype.card n ^ 2) := by positivity
  have hc : (F.card : ℝ≥0∞) ≤ ENNReal.ofReal ((1 + 2 / η) ^ (2 * Fintype.card n ^ 2)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hcard
  rw [ENNReal.ofReal_inv_of_pos hpos]
  have hne : ENNReal.ofReal ((1 + 2 / η) ^ (2 * Fintype.card n ^ 2)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hpos).ne'
  calc (ENNReal.ofReal ((1 + 2 / η) ^ (2 * Fintype.card n ^ 2)))⁻¹
      = (ENNReal.ofReal ((1 + 2 / η) ^ (2 * Fintype.card n ^ 2)))⁻¹ * 1 := (mul_one _).symm
    _ ≤ (ENNReal.ofReal ((1 + 2 / η) ^ (2 * Fintype.card n ^ 2)))⁻¹ * ((F.card : ℝ≥0∞) * m) := by
        gcongr
    _ ≤ (ENNReal.ofReal ((1 + 2 / η) ^ (2 * Fintype.card n ^ 2)))⁻¹ *
          (ENNReal.ofReal ((1 + 2 / η) ^ (2 * Fintype.card n ^ 2)) * m) := by gcongr
    _ = m := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top, one_mul]

end Patch

open scoped Matrix.Norms.Frobenius

/-- **Near-Bell patch mass**: `μ(bellNeighborhood d) ≥ (1 + 8 d √d)^(−2 d⁴)`. -/
theorem bellNeighborhood_mass_ge (d : ℕ) [NeZero d] :
    ENNReal.ofReal (((1 + 8 * d * Real.sqrt d) ^ (2 * d ^ 4))⁻¹) ≤
      unitaryHaar (Fin d × Fin d) (bellNeighborhood d) := by
  let n := Fin d × Fin d
  have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  set η : ℝ := 1 / (4 * d * Real.sqrt d) with hη
  have hη0 : 0 < η := by positivity
  let B : Matrix.unitaryGroup n ℂ :=
    ⟨generalizedBellFinMatrix d,
      Matrix.mem_unitaryGroup_iff'.mpr (isIsometry_generalizedBellFinMatrix d)⟩
  have hsub : unitaryOpBall n (B : Matrix n n ℂ) η ⊆ bellNeighborhood d := by
    intro V hV
    simp only [bellNeighborhood]
    have hF := frobNorm_le_sqrt_card_mul_opNorm ((V : Matrix n n ℂ) - generalizedBellFinMatrix d)
    have hcard : Real.sqrt (Fintype.card n : ℝ) = d := by
      simp only [n, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
      exact Real.sqrt_mul_self (Nat.cast_nonneg d)
    rw [hcard] at hF
    have hV' : opNorm ((V : Matrix n n ℂ) - generalizedBellFinMatrix d) ≤ η := hV
    calc _ ≤ (d : ℝ) * opNorm ((V : Matrix n n ℂ) - generalizedBellFinMatrix d) := hF
      _ ≤ (d : ℝ) * η := mul_le_mul_of_nonneg_left hV' (Nat.cast_nonneg d)
      _ = 1 / (4 * Real.sqrt d) := by rw [hη]; field_simp
  have hmass := inv_pow_le_unitaryHaar_unitaryOpBall_one n hη0
  rw [← unitaryHaar_unitaryOpBall n B η] at hmass
  have hη2 : 2 / η = 8 * d * Real.sqrt d := by rw [hη]; field_simp; ring
  have hcardn : Fintype.card n ^ 2 = d ^ 4 := by
    simp only [n, Fintype.card_prod, Fintype.card_fin]
    ring
  rw [hη2, hcardn] at hmass
  exact hmass.trans (measure_mono hsub)

/-- The logarithmic comparison of the patch mass with the restricted bound. -/
theorem nearBell_resource_of_patch {C : ℝ} (hC : 0 ≤ C) {d K : ℕ} (hd : 2 ≤ d)
    (hK : (d : ℝ) ^ 3 / 4 ≤ K) {e : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    (h : ((1 + 8 * d * Real.sqrt d) ^ (2 * d ^ 4))⁻¹ ≤
      Real.exp (C * (K : ℝ) ^ 2) * e ^ ((d : ℝ) ^ 4 / 16)) :
    1 / (4 * Real.sqrt (C + 160)) * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hd34 : (d : ℝ) ^ 3 ≤ 4 * K := by linarith
  have hN : (d : ℝ) ^ 4 ≤ 16 * (K : ℝ) ^ 2 := by
    have h := fourth_le_of_cube_le (K := 2 * (K : ℝ)) hdR (by linarith)
    nlinarith
  have hN5 : (d : ℝ) ^ 5 ≤ 16 * (K : ℝ) ^ 2 := by
    have h6 : (d : ℝ) ^ 6 ≤ 16 * (K : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hd34 2
      nlinarith
    have : (d : ℝ) ^ 5 ≤ (d : ℝ) ^ 6 := by
      have h1 : (1 : ℝ) ≤ d := by linarith
      calc (d : ℝ) ^ 5 = (d : ℝ) ^ 5 * 1 := (mul_one _).symm
        _ ≤ (d : ℝ) ^ 5 * d := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (d : ℝ) ^ 6 := by ring
    linarith
  -- the patch logarithm
  have hsq : Real.sqrt d ≤ d := by
    rw [Real.sqrt_le_left hd0.le]
    nlinarith
  have hbase : 1 + 8 * (d : ℝ) * Real.sqrt d ≤ 9 * (d : ℝ) ^ 2 := by nlinarith
  have hlogbase : Real.log (1 + 8 * (d : ℝ) * Real.sqrt d) ≤ 3 + 2 * d := by
    have h1 := Real.log_le_log (by positivity) hbase
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
    have h3 : (9 : ℝ) ≤ Real.exp 3 := by
      have he1 := Real.exp_one_gt_d9
      have h' : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h']
      nlinarith [pow_le_pow_left₀ (by norm_num) he1.le 3]
    have h9 : Real.log 9 ≤ 3 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      exact h3
    have hld : Real.log d ≤ d := by
      have := Real.log_le_sub_one_of_pos hd0
      linarith
    push_cast at h1
    linarith
  set L := Real.log (1 / e) with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg ((one_le_div₀ he).mpr he1)
  have hlog : (d : ℝ) ^ 4 / 16 * L ≤ (C + 160) * (K : ℝ) ^ 2 := by
    have hpos : (0 : ℝ) < (1 + 8 * d * Real.sqrt d) ^ (2 * d ^ 4) := by positivity
    rw [Real.rpow_def_of_pos he, ← Real.exp_add] at h
    have h' : -(((2 * d ^ 4 : ℕ) : ℝ) * Real.log (1 + 8 * d * Real.sqrt d)) ≤
        C * (K : ℝ) ^ 2 + Real.log e * ((d : ℝ) ^ 4 / 16) := by
      rw [← Real.exp_le_exp, Real.exp_neg, ← Real.log_pow, Real.exp_log hpos]
      exact h
    rw [hLdef, one_div, Real.log_inv]
    push_cast at h'
    have h2 : 2 * (d : ℝ) ^ 4 * Real.log (1 + 8 * d * Real.sqrt d) ≤
        2 * (d : ℝ) ^ 4 * (3 + 2 * d) :=
      mul_le_mul_of_nonneg_left hlogbase (by positivity)
    have h3 : 2 * (d : ℝ) ^ 4 * (3 + 2 * d) = 6 * (d : ℝ) ^ 4 + 4 * (d : ℝ) ^ 5 := by ring
    nlinarith
  have hC160 : 0 < C + 160 := by linarith
  set x := 1 / (4 * Real.sqrt (C + 160)) * (d : ℝ) ^ 2 * Real.sqrt L with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hx2 : x ^ 2 = (d : ℝ) ^ 4 * L / (16 * (C + 160)) := by
    rw [hxdef, mul_pow, mul_pow, div_pow, mul_pow, Real.sq_sqrt hC160.le, Real.sq_sqrt hL0]
    ring
  have hxK : x ^ 2 ≤ (K : ℝ) ^ 2 := by
    rw [hx2, div_le_iff₀ (by positivity)]
    linarith
  by_contra hlt
  have := pow_lt_pow_left₀ (not_le.mp hlt) hK0 (by norm_num : (2 : ℕ) ≠ 0)
  linarith

/-- **`cor:universal-pvm`, precision part**: universal PVM approximation needs
`K ≥ c d² √log(1/ε)`, for pure and common-map mixed resources. -/
theorem exists_nearBell_universal_resource_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d K : ℕ), 2 ≤ d → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PurePVMUniversalScore d K e → c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) ∧
      (MixedPVMUniversalScore d K e → c * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K) := by
  obtain ⟨C, hC, hH⟩ := exists_nearBell_haar_constant_of_imageVolumeBound hGeom
  refine ⟨1 / (4 * Real.sqrt (C + 160)), by positivity, ?_⟩
  intro d K hd e he he2
  have : NeZero d := ⟨by omega⟩
  have hpure (hu : PurePVMUniversalScore d K e) :
      1 / (4 * Real.sqrt (C + 160)) * (d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)) ≤ K := by
    have hK := hu.cubic_quarter_floor (by omega) he.le he2
    have hm := hH d K hd (by linarith) e he he2
    rw [hu.reachable_eq_univ, Set.inter_univ] at hm
    have hpatch := bellNeighborhood_mass_ge d
    have hle := (hpatch.trans hm).trans (min_le_right _ _)
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
    exact nearBell_resource_of_patch (by linarith) hd hK he (by linarith) hle
  exact ⟨hpure, fun hm => hpure ((mixedPVMUniversalScore_iff_pure d K e).mp hm)⟩


/-- **Theorem B(ii)**: universal PVM approximation needs
`K ≥ c max(d³, d² √log(1/ε))`, for pure and common-map mixed resources, in PVM
score or worst-case joint total variation. -/
theorem exists_nearBell_universal_max_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ (d K : ℕ), 2 ≤ d → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PurePVMUniversalScore d K e →
        c * max ((d : ℝ) ^ 3) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e))) ≤ K) ∧
      (MixedPVMUniversalScore d K e →
        c * max ((d : ℝ) ^ 3) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e))) ≤ K) ∧
      (PurePVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        c * max ((d : ℝ) ^ 3) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e))) ≤ K) ∧
      (MixedPVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        c * max ((d : ℝ) ^ 3) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e))) ≤ K) := by
  obtain ⟨c, hc, hres⟩ := exists_nearBell_universal_resource_constant hGeom
  refine ⟨min (1 / 4) c, lt_min (by norm_num) hc, ?_⟩
  intro d K hd e he he2
  have hd0 : 0 < d := by omega
  have hpure (hu : PurePVMUniversalScore d K e) :
      min (1 / 4) c * max ((d : ℝ) ^ 3) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e))) ≤ K := by
    have h1 := hu.cubic_quarter_floor hd0 he.le he2
    have h2 := (hres d K hd e he he2).1 hu
    rcases le_total ((d : ℝ) ^ 3) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e))) with h | h
    · rw [max_eq_right h]
      calc min (1 / 4) c * ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e)))
          ≤ c * ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e))) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        _ ≤ K := by linarith
    · rw [max_eq_left h]
      calc min (1 / 4) c * (d : ℝ) ^ 3 ≤ 1 / 4 * (d : ℝ) ^ 3 :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
        _ ≤ K := by linarith
  have hmixed (hm : MixedPVMUniversalScore d K e) := hpure ((mixedPVMUniversalScore_iff_pure d K e).mp hm)
  exact ⟨hpure, hmixed, fun h => hpure (h.score hd0), fun h => hmixed (h.score hd0)⟩

/-- **Theorem B(ii), qubit form**: at `d = 2ⁿ`,
`log₂ K ≥ max(3n − 2, 2n + ½ log₂ log(1/ε) − b)`. -/
theorem exists_nearBell_universal_qubit_constant_of_imageVolumeBound (hGeom : PolynomialImageVolumeBound) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (n K : ℕ), 1 ≤ n → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PurePVMUniversalScore (2 ^ n) K e →
        max (3 * (n : ℝ) - 2) (2 * (n : ℝ) + 1 / 2 * Real.logb 2 (Real.log (1 / e)) - b) ≤
          Real.logb 2 K) ∧
      (MixedPVMUniversalScore (2 ^ n) K e →
        max (3 * (n : ℝ) - 2) (2 * (n : ℝ) + 1 / 2 * Real.logb 2 (Real.log (1 / e)) - b) ≤
          Real.logb 2 K) := by
  obtain ⟨c, hc, hres⟩ := exists_nearBell_universal_resource_constant hGeom
  refine ⟨max 0 (-Real.logb 2 c), le_max_left _ _, ?_⟩
  intro n K hn e he he2
  have hd : 2 ≤ 2 ^ n := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) hn
  have hpure (hu : PurePVMUniversalScore (2 ^ n) K e) :
      max (3 * (n : ℝ) - 2) (2 * (n : ℝ) + 1 / 2 * Real.logb 2 (Real.log (1 / e)) -
        max 0 (-Real.logb 2 c)) ≤ Real.logb 2 K :=
    max_le (hu.cubic_qubit_floor he.le he2)
      (strong_qubit_of_resource hc he he2 n ((hres (2 ^ n) K hd e he he2).1 hu))
  exact ⟨hpure, fun hm => hpure ((mixedPVMUniversalScore_iff_pure _ K e).mp hm)⟩

/-- `thm:bell-haar`. -/
theorem exists_nearBell_haar_constant :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d K : ℕ) [NeZero d], 2 ≤ d → (d : ℝ) ^ 3 ≤ 4 * K →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        unitaryHaar (Fin d × Fin d) (bellNeighborhood d ∩ purePVMReachable d K ε) ≤
          min 1 (ENNReal.ofReal (Real.exp (C * (K : ℝ) ^ 2) * ε ^ ((d : ℝ) ^ 4 / 16))) :=
  exists_nearBell_haar_constant_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

/-- Theorem B(ii). -/
theorem exists_nearBell_universal_max_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ (d K : ℕ), 2 ≤ d → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PurePVMUniversalScore d K e →
        c * max ((d : ℝ) ^ 3) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e))) ≤ K) ∧
      (MixedPVMUniversalScore d K e →
        c * max ((d : ℝ) ^ 3) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e))) ≤ K) ∧
      (PurePVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        c * max ((d : ℝ) ^ 3) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e))) ≤ K) ∧
      (MixedPVMUniversalTV.{u₁, u₂, u₃, u₄, u₅, u₆, u₇, u₈} d K e →
        c * max ((d : ℝ) ^ 3) ((d : ℝ) ^ 2 * Real.sqrt (Real.log (1 / e))) ≤ K) :=
  exists_nearBell_universal_max_constant_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

/-- Theorem B(ii), qubit form. -/
theorem exists_nearBell_universal_qubit_constant :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (n K : ℕ), 1 ≤ n → ∀ e : ℝ, 0 < e → e ≤ 1 / 2 →
      (PurePVMUniversalScore (2 ^ n) K e →
        max (3 * (n : ℝ) - 2) (2 * (n : ℝ) + 1 / 2 * Real.logb 2 (Real.log (1 / e)) - b) ≤
          Real.logb 2 K) ∧
      (MixedPVMUniversalScore (2 ^ n) K e →
        max (3 * (n : ℝ) - 2) (2 * (n : ℝ) + 1 / 2 * Real.logb 2 (Real.log (1 / e)) - b) ≤
          Real.logb 2 K) :=
  exists_nearBell_universal_qubit_constant_of_imageVolumeBound
    (DirectVolume.polynomialImageVolumeBound)

end NLQCLean

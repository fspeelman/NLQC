import NLQCLean.Approx.SlimWitnessDifferential
import NLQCLean.Geometry.ScaledUnitaryNormalVolume
import NLQCLean.Geometry.UnitaryWitnessTube
import NLQCLean.Geometry.PolynomialTubeConditional

/-!
# The strong polynomial tube estimate

For the slim witness family with its rank/error split, thickened by `2u`,
the only geometric premise is `PolynomialImageVolumeBoundWith C`
(source dimension `P + 2N`, target `2N`). With `Λ = (4 + 32δ)√K/d`, `λ = 32δ√K/d`,
`b = strongUncontrolledRank d`, and every Borel `S` covered by the slim targets at normalized
distance `ρ`, whenever `ρ ≤ u`, `λ ≤ u`, `0 < u ≤ 1/64`:

  `μ(S) ≤ exp(36864 C⁴ (P + N)) (Λ + 2u)^b u^(N − b)`.

The lower side is the normal-coordinate tube bound at radius `d u`, rescaled to the normalized output
coordinates `H/d` (volume factor `d^(−2N)`); ball factors cancel via `ω_2N ≤ ω_N²`.
-/

namespace NLQCLean

open MeasureTheory
open scoped ENNReal Pointwise

/-- The open `u`-tube around `S` in the normalized output coordinates `H/d`. -/
def normalizedWitnessTube (d : ℕ) (u : ℝ) (S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ)) :
    Set (RealEuclidean (2 * d ^ 4)) :=
  {y | ∃ U ∈ S, dist y (normalizedOutputCoordinates d (U : Matrix _ _ ℂ)) < u}

theorem normalizedWitnessTube_eq_smul {d : ℕ} (hd : 0 < d) (u : ℝ)
    (S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ)) :
    normalizedWitnessTube d u S = (1 / (d : ℝ)) • unitaryWitnessTube d (d * u) S := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (by positivity : (1 / (d : ℝ)) ≠ 0)]
  simp only [normalizedWitnessTube, unitaryWitnessTube, Set.mem_ofPred_eq]
  refine exists_congr fun U => and_congr_right fun _ => ?_
  have hcoord : normalizedOutputCoordinates d (U : Matrix _ _ ℂ) =
      (d : ℝ)⁻¹ • overlapOutputCoordinates d (U : Matrix _ _ ℂ) := by
    simp [normalizedOutputCoordinates]
  have hdist : dist ((1 / (d : ℝ))⁻¹ • y) (overlapOutputCoordinates d (U : Matrix _ _ ℂ)) =
      d * dist y (normalizedOutputCoordinates d (U : Matrix _ _ ℂ)) := by
    have hX : overlapOutputCoordinates d (U : Matrix _ _ ℂ) =
        (d : ℝ) • ((d : ℝ)⁻¹ • overlapOutputCoordinates d (U : Matrix _ _ ℂ)) := by
      rw [smul_smul, mul_inv_cancel₀ hdR.ne', one_smul]
    rw [hcoord, one_div, inv_inv]
    conv_lhs => rw [hX]
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hdR]
  rw [hdist]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

theorem volume_normalizedWitnessTube {d : ℕ} (hd : 0 < d) (u : ℝ)
    (S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ)) :
    volume (normalizedWitnessTube d u S) =
      ENNReal.ofReal ((1 / (d : ℝ)) ^ (2 * d ^ 4)) * volume (unitaryWitnessTube d (d * u) S) := by
  rw [normalizedWitnessTube_eq_smul hd, Measure.addHaar_smul_of_nonneg volume (by positivity),
    finrank_euclideanSpace_fin]

/-- In normalized output coordinates: `0 < u ≤ 1/64`. -/
theorem strong_normalizedWitnessTube_volume_lower {d : ℕ} (hd : 2 ≤ d) {u : ℝ} (hu : 0 < u)
    (hu' : u ≤ 1 / 64) {S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ)} (hS : MeasurableSet S) :
    ENNReal.ofReal ((1 / 4 : ℝ) * (1 / 1024 : ℝ) ^ (d ^ 4)) * euclideanUnitBallVolume (d ^ 4) ^ 2 *
      ENNReal.ofReal u ^ (d ^ 4) * unitaryHaar (Fin d × Fin d) S ≤
        volume (normalizedWitnessTube d u S) := by
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hsqrt : Real.sqrt (Fintype.card (Fin d × Fin d) : ℝ) = d := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    exact Real.sqrt_mul_self hdR.le
  have hN : Fintype.card (Fin d × Fin d) ^ 2 = d ^ 4 := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    ring
  have hs : 0 < (d : ℝ) * u := by positivity
  have hsD : (d : ℝ) * u ≤ Real.sqrt (Fintype.card (Fin d × Fin d) : ℝ) / 64 := by
    rw [hsqrt]
    nlinarith
  have hlow := unitaryHaar_tube_volume_lower_strong (Fin d × Fin d) hs hsD hS
  rw [volume_normalizedWitnessTube hd0, volume_unitaryWitnessTube]
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hlow zero_le)
  unfold strongNormalLowerFactor
  rw [hsqrt, hN]
  set N := d ^ 4
  set ω := euclideanUnitBallVolume N
  have h2 : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  have hmerge : ENNReal.ofReal ((1 / 4 : ℝ) * (1 / 1024 : ℝ) ^ N) * ENNReal.ofReal (u ^ N) =
      ENNReal.ofReal ((1 / (d : ℝ)) ^ (2 * N)) * ENNReal.ofReal ((1 / 16 : ℝ) ^ N) *
        ENNReal.ofReal (1 / 2) * ENNReal.ofReal (((d : ℝ) * u) ^ N) * ENNReal.ofReal (1 / 2) *
          ENNReal.ofReal (((d : ℝ) / 64) ^ N) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hd' : (d : ℝ) ≠ 0 := hdR.ne'
    have h1024 : (1 / 1024 : ℝ) ^ N = (1 / 16) ^ N * (1 / 64) ^ N := by
      rw [← mul_pow]; norm_num
    have hd64 : ((d : ℝ) / 64) ^ N = (d : ℝ) ^ N * (1 / 64) ^ N := by
      rw [← mul_pow]; ring
    have hdd : (1 / (d : ℝ)) ^ N * (d : ℝ) ^ N = 1 := by
      rw [← mul_pow, one_div_mul_cancel hd', one_pow]
    rw [h1024, hd64, mul_pow, pow_mul']
    linear_combination (-(1 / 4) * (1 / 16 : ℝ) ^ N * (1 / 64) ^ N * u ^ N *
      ((d : ℝ) ^ N * (1 / (d : ℝ)) ^ N + 1)) * hdd
  calc ENNReal.ofReal ((1 / 4 : ℝ) * (1 / 1024 : ℝ) ^ N) * ω ^ 2 * ENNReal.ofReal u ^ N *
        unitaryHaar (Fin d × Fin d) S
      = (ENNReal.ofReal ((1 / 4 : ℝ) * (1 / 1024 : ℝ) ^ N) * ENNReal.ofReal (u ^ N)) * ω ^ 2 *
          unitaryHaar (Fin d × Fin d) S := by
        rw [ENNReal.ofReal_pow hu.le]; ring
    _ = _ := by
        rw [hmerge, h2, ENNReal.ofReal_pow hs.le, ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ d / 64)]
        ring

theorem strongJacobian_le {N b : ℕ} (hb : b ≤ N) {Λ μ u : ℝ} (hΛ : 0 ≤ Λ) (hμ : 0 ≤ μ)
    (hμu : μ ≤ u) :
    (Λ + 2 * u) ^ b * (μ + 2 * u) ^ (2 * N - b) ≤ u ^ N * ((Λ + 2 * u) ^ b * 9 ^ N * u ^ (N - b)) := by
  have hu : 0 ≤ u := hμ.trans hμu
  have hμ' : μ + 2 * u ≤ 3 * u := by linarith
  have hexp : 2 * N - b = N + (N - b) := by omega
  calc
    _ ≤ (Λ + 2 * u) ^ b * (3 * u) ^ (2 * N - b) := by gcongr
    _ = (Λ + 2 * u) ^ b * (3 ^ (2 * N - b) * u ^ (2 * N - b)) := by rw [mul_pow (3 : ℝ) u]
    _ ≤ (Λ + 2 * u) ^ b * (3 ^ (2 * N) * u ^ (2 * N - b)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (Nat.sub_le _ _))
        (pow_nonneg hu _)) (pow_nonneg (by linarith) _)
    _ = _ := by rw [hexp, pow_add, pow_mul]; norm_num; ring

theorem strong_fixed_base_le_exp {C : ℝ} (hC : 1 ≤ C) (P N : ℕ) (hN : 1 ≤ N) :
    4 * 1024 ^ N * 9 ^ N * C ^ (P + 4 * N) ≤ Real.exp ((36864 * C ^ 4) * ((P : ℝ) + N)) := by
  have hC0 : 0 ≤ C := by linarith
  calc
    _ ≤ 4 ^ N * 1024 ^ N * 9 ^ N * C ^ (P + 4 * N) := by
        gcongr
        exact le_self_pow₀ (by norm_num) (by omega)
    _ = 36864 ^ N * C ^ (P + 4 * N) := by
        rw [← mul_pow, ← mul_pow]
        norm_num
    _ ≤ 36864 ^ (P + N) * C ^ (4 * (P + N)) :=
      mul_le_mul (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 36864) (by omega))
        (pow_le_pow_right₀ hC (by omega)) (by positivity) (by positivity)
    _ = (36864 * C ^ 4) ^ (P + N) := by rw [mul_pow, ← pow_mul]
    _ ≤ (Real.exp (36864 * C ^ 4)) ^ (P + N) := by
        gcongr
        linarith [Real.add_one_le_exp (36864 * C ^ 4)]
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

theorem cancel_strong_tube_volume {N : ℕ} {u a A B : ℝ} (hu : 0 < u) (ha : 0 < a) (hA : 0 ≤ A)
    {h : ℝ≥0∞}
    (hh : ENNReal.ofReal a * euclideanUnitBallVolume N ^ 2 * ENNReal.ofReal u ^ N * h ≤
      ENNReal.ofReal A * euclideanUnitBallVolume N ^ 2 * ENNReal.ofReal (u ^ N * B)) :
    h ≤ ENNReal.ofReal (A * B / a) := by
  have hw0 : euclideanUnitBallVolume N ≠ 0 :=
    (Metric.measure_ball_pos volume (0 : RealEuclidean N) zero_lt_one).ne'
  have hwt : euclideanUnitBallVolume N ≠ ∞ := measure_ball_lt_top.ne
  have hf0 : euclideanUnitBallVolume N ^ 2 * ENNReal.ofReal u ^ N ≠ 0 := by
    have hwpos : 0 < euclideanUnitBallVolume N := pos_iff_ne_zero.mpr hw0
    positivity
  have hft : euclideanUnitBallVolume N ^ 2 * ENNReal.ofReal u ^ N ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top hwt) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  have hc0 : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.mpr ha).ne'
  have he : ENNReal.ofReal a * ENNReal.ofReal (A * B / a) = ENNReal.ofReal A * ENNReal.ofReal B := by
    rw [← ENNReal.ofReal_mul ha.le, ← ENNReal.ofReal_mul hA]
    congr 1
    field_simp
  apply (ENNReal.mul_le_mul_iff_right hc0 ENNReal.ofReal_ne_top).mp
  rw [he]
  apply (ENNReal.mul_le_mul_iff_left hf0 hft).mp
  calc
    _ = ENNReal.ofReal a * euclideanUnitBallVolume N ^ 2 * ENNReal.ofReal u ^ N * h := by ring
    _ ≤ _ := hh
    _ = _ := by rw [ENNReal.ofReal_mul (pow_nonneg hu.le _), ENNReal.ofReal_pow hu.le]; ring

namespace SlimReverseBlocks

variable {d K : ℕ} (s : SlimReverseShape d K) (hd : 2 ≤ d)

theorem strongUncontrolledRank_le_two_mul (hd : 2 ≤ d) : strongUncontrolledRank d ≤ 2 * d ^ 4 := by
  have := eight_mul_strongUncontrolledRank_le hd
  omega

/-- The image-volume property applied to the thickened slim family with the transverse derivative split. -/
theorem strong_thickenedWitness_image_volume_le {C : ℝ} (hGeom : PolynomialImageVolumeBoundWith C)
    {δ c : ℝ} (hδ : 0 ≤ δ) (hc : 0 ≤ c) :
    volume ((thickenedWitnessPolynomial s hd c).eval '' (thickenedWitnessFormat s hd δ).source) ≤
      ENNReal.ofReal (C ^ (slimCoordinateBudget K + 2 * d ^ 4 + 2 * d ^ 4)) *
        euclideanUnitBallVolume (2 * d ^ 4) *
        ENNReal.ofReal (((4 + 32 * δ) * Real.sqrt K / d + c) ^ strongUncontrolledRank d *
          (32 * δ * Real.sqrt K / d + c) ^ (2 * d ^ 4 - strongUncontrolledRank d)) := by
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have h4 : 1 ≤ d ^ 4 := Nat.one_le_pow _ _ hd0
  have hsq := Real.sqrt_nonneg (K : ℝ)
  exact hGeom _ _ (by omega) (by omega) (thickenedWitnessFormat s hd δ)
    (thickenedWitnessPolynomial s hd c) (isCompact_thickenedWitnessFormat_source s hd δ)
    (thickenedWitnessFormat_source_radius s hd δ) _ (by positivity)
    (fun z hz => by
      rw [(hasFDerivAt_thickenedWitnessPolynomial s hd c z).fderiv]
      have hx := (((witnessFormat s hd δ).mem_thicken_source _ z).mp hz).1
      obtain ⟨T, R, hdec, hrank, hnorm, hR⟩ := witnessFormat_sharp_rank_error s hd hδ hx
      exact topRealJacobian_thickenedLinearMap_le _ T R hdec (by positivity)
        (by rw [div_le_div_iff_of_pos_right hdR]; nlinarith)
        hc (hnorm.trans (by rw [div_le_div_iff_of_pos_right hdR]; nlinarith)) hR hrank
        (strongUncontrolledRank_le_two_mul hd))

theorem normalizedWitnessTube_subset_imageTube {δ ρ u : ℝ} (hρ : ρ ≤ u)
    {S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ)} (hcover : S ⊆ witnessTargets s hd δ ρ) :
    normalizedWitnessTube d u S ⊆
      {y | ∃ x ∈ (witnessFormat s hd δ).source,
        dist y ((coordinateOverlapPolynomial s hd).eval x) < 2 * u} := by
  rintro y ⟨U, hU, hy⟩
  obtain ⟨x, hx, hdist⟩ := hcover hU
  refine ⟨x, hx, ?_⟩
  have htri := dist_triangle y (normalizedOutputCoordinates d (U : Matrix _ _ ℂ))
    ((coordinateOverlapPolynomial s hd).eval x)
  linarith

/-- The strong tube estimate, with the geometry constant `C` displayed. -/
theorem strong_witness_haar_le {C : ℝ} (hC : 1 ≤ C) (hGeom : PolynomialImageVolumeBoundWith C)
    {δ ρ u : ℝ} (hδ : 0 ≤ δ) (hu : 0 < u) (hu' : u ≤ 1 / 64)
    (hlam : 32 * δ * Real.sqrt K / d ≤ u) (hρ : ρ ≤ u)
    {S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ)} (hS : MeasurableSet S)
    (hcover : S ⊆ witnessTargets s hd δ ρ) :
    unitaryHaar (Fin d × Fin d) S ≤
      ENNReal.ofReal (Real.exp ((36864 * C ^ 4) * ((slimCoordinateBudget K : ℝ) + d ^ 4)) *
        ((4 + 32 * δ) * Real.sqrt K / d + 2 * u) ^ strongUncontrolledRank d *
        u ^ (d ^ 4 - strongUncontrolledRank d)) := by
  have hd0 : 0 < d := by omega
  have hbN : strongUncontrolledRank d ≤ d ^ 4 := by
    have := eight_mul_strongUncontrolledRank_le hd
    omega
  have hN1 : 1 ≤ d ^ 4 := Nat.one_le_pow _ _ hd0
  have hC0 : 0 ≤ C := by linarith
  have hsq := Real.sqrt_nonneg (K : ℝ)
  have hΛ0 : 0 ≤ (4 + 32 * δ) * Real.sqrt K / d := by positivity
  have hμ0 : 0 ≤ 32 * δ * Real.sqrt K / d := by positivity
  have hlow := strong_normalizedWitnessTube_volume_lower hd hu hu' hS
  have hincl : normalizedWitnessTube d u S ⊆
      (thickenedWitnessPolynomial s hd (2 * u)).eval '' (thickenedWitnessFormat s hd δ).source :=
    (normalizedWitnessTube_subset_imageTube s hd hρ hcover).trans
      ((coordinateOverlapPolynomial s hd).tube_subset_thicken_image (witnessFormat s hd δ)
        (by change 7 + 1 + 1 ≤ 20; decide) (by positivity))
  have hup := (measure_mono hincl).trans
    (strong_thickenedWitness_image_volume_le s hd hGeom hδ (by positivity : (0 : ℝ) ≤ 2 * u))
  have hJ := strongJacobian_le hbN hΛ0 hμ0 hlam
  have hchain : ENNReal.ofReal ((1 / 4 : ℝ) * (1 / 1024 : ℝ) ^ (d ^ 4)) *
      euclideanUnitBallVolume (d ^ 4) ^ 2 * ENNReal.ofReal u ^ (d ^ 4) *
        unitaryHaar (Fin d × Fin d) S ≤
      ENNReal.ofReal (C ^ (slimCoordinateBudget K + 4 * d ^ 4)) * euclideanUnitBallVolume (d ^ 4) ^ 2 *
        ENNReal.ofReal (u ^ (d ^ 4) * (((4 + 32 * δ) * Real.sqrt K / d + 2 * u) ^ strongUncontrolledRank d *
          9 ^ (d ^ 4) * u ^ (d ^ 4 - strongUncontrolledRank d))) := by
    refine hlow.trans (hup.trans ?_)
    have hexp : slimCoordinateBudget K + 2 * d ^ 4 + 2 * d ^ 4 = slimCoordinateBudget K + 4 * d ^ 4 := by
      omega
    rw [hexp]
    exact mul_le_mul (mul_le_mul_right (euclideanUnitBallVolume_twice_le_sq (d ^ 4)) _)
      (ENNReal.ofReal_le_ofReal hJ) zero_le zero_le
  have hcancel := cancel_strong_tube_volume hu (by positivity) (pow_nonneg hC0 _) hchain
  refine hcancel.trans (ENNReal.ofReal_le_ofReal ?_)
  set X := (4 + 32 * δ) * Real.sqrt K / d + 2 * u
  set N := d ^ 4
  set b := strongUncontrolledRank d
  set P := slimCoordinateBudget K
  have hinv : ((1 / 4 : ℝ) * (1 / 1024 : ℝ) ^ N)⁻¹ = 4 * 1024 ^ N := by
    simp only [one_div, mul_inv, inv_pow, inv_inv]
  have hX : 0 ≤ X := by positivity
  calc C ^ (P + 4 * N) * (X ^ b * 9 ^ N * u ^ (N - b)) / ((1 / 4 : ℝ) * (1 / 1024 : ℝ) ^ N)
      = (4 * 1024 ^ N * 9 ^ N * C ^ (P + 4 * N)) * (X ^ b * u ^ (N - b)) := by
        rw [div_eq_mul_inv, hinv]; ring
    _ ≤ Real.exp ((36864 * C ^ 4) * ((P : ℝ) + N)) * (X ^ b * u ^ (N - b)) :=
        mul_le_mul_of_nonneg_right (strong_fixed_base_le_exp hC P N hN1) (by positivity)
    _ = _ := by simp only [N, Nat.cast_pow]; ring

end SlimReverseBlocks

/-- Slim witness tube bound: one geometry constant precedes `d, K`, the slim shape, `δ, ρ, u` and `S`. -/
theorem exists_strong_witness_haar_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (d K : ℕ) (s : SlimReverseShape d K) (hd : 2 ≤ d),
      ∀ δ ρ u : ℝ, 0 ≤ δ → 0 < u → u ≤ 1 / 64 → 32 * δ * Real.sqrt K / d ≤ u → ρ ≤ u →
      ∀ S : Set (Matrix.unitaryGroup (Fin d × Fin d) ℂ), MeasurableSet S →
        S ⊆ SlimReverseBlocks.witnessTargets s hd δ ρ →
        unitaryHaar (Fin d × Fin d) S ≤
          ENNReal.ofReal (Real.exp (C * ((slimCoordinateBudget K : ℝ) + d ^ 4)) *
            ((4 + 32 * δ) * Real.sqrt K / d + 2 * u) ^ strongUncontrolledRank d *
            u ^ (d ^ 4 - strongUncontrolledRank d)) := by
  obtain ⟨C, hC, hbound⟩ := hGeom
  have hC4 : (1 : ℝ) ≤ C ^ 4 := one_le_pow₀ hC
  refine ⟨36864 * C ^ 4, by linarith, ?_⟩
  intro d K s hd δ ρ u hδ hu hu' hlam hρ S hS hcover
  exact SlimReverseBlocks.strong_witness_haar_le s hd hC hbound hδ hu hu' hlam hρ hS hcover

end NLQCLean

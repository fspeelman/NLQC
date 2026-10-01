import NLQCLean.Invariants.ControlledPhase
import NLQCLean.Approx.ScalarPurityWitness
import NLQCLean.Bounds.ProvedProjection
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Scalar image-volume estimates for the charged two-qubit witnesses

The geometry inputs are used only after checking the exact source format,
degree, radius, and full ambient derivative bound. Conversion from invariant
image volume to length in an angle interval is a separate theorem boundary.
-/

namespace NLQCLean

open MeasureTheory
open scoped ENNReal

/-- The one-coordinate scalar representation preserves Lebesgue outer measure. -/
noncomputable def scalarEuclideanEquiv : ℝ ≃ₗᵢ[ℝ] RealEuclidean 1 where
  toLinearEquiv :=
    { toLinearMap := scalarEuclidean
      invFun := fun x => x 0
      left_inv := fun _ => rfl
      right_inv := fun x => by ext i; have hi : i = 0 := Subsingleton.elim _ _; subst i; rfl }
  norm_map' := norm_scalarEuclidean

theorem volume_scalarEuclidean_image (S : Set ℝ) : volume (scalarEuclidean '' S) = volume S := by
  have h := scalarEuclideanEquiv.measurePreserving.measure_preimage_emb
    scalarEuclideanEquiv.toHomeomorph.measurableEmbedding (scalarEuclideanEquiv '' S)
  rw [Set.preimage_image_eq _ scalarEuclideanEquiv.injective] at h
  exact h.symm

theorem euclideanUnitBallVolume_one : euclideanUnitBallVolume 1 = 2 := by
  have h := scalarEuclideanEquiv.measurePreserving.measure_preimage_emb
    scalarEuclideanEquiv.toHomeomorph.measurableEmbedding (Metric.ball (0 : RealEuclidean 1) 1)
  have he : scalarEuclideanEquiv ⁻¹' Metric.ball (0 : RealEuclidean 1) 1 =
      Metric.ball (0 : ℝ) 1 := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right]
    rw [scalarEuclideanEquiv.norm_map]
  rw [he] at h
  simpa [euclideanUnitBallVolume, Real.volume_ball] using h.symm

/-- Restricted inverse Lipschitz control gives an outer-measure bound even
when the angle set has not been proved measurable. -/
theorem volume_le_inverse_lipschitz_image {f : ℝ → ℝ} {S J : Set ℝ}
    (hSJ : S ⊆ J) {m : ℝ} (hm : 0 < m)
    (hinverse : ∀ x ∈ J, ∀ y ∈ J, |x - y| ≤ m⁻¹ * |f x - f y|) :
    volume S ≤ ENNReal.ofReal m⁻¹ * volume (f '' S) := by
  have hinj : Set.InjOn f J := by
    intro x hx y hy he
    have h := hinverse x hx y hy
    rw [he, sub_self, abs_zero, mul_zero] at h
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
  let L : NNReal := NNReal.mk m⁻¹ (inv_nonneg.mpr hm.le)
  have hLip : LipschitzOnWith L (Function.invFunOn f J) (f '' S) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro u ⟨x, hx, rfl⟩ v ⟨y, hy, rfl⟩
    rw [hinj.leftInvOn_invFunOn (hSJ hx), hinj.leftInvOn_invFunOn (hSJ hy)]
    change dist x y ≤ m⁻¹ * dist (f x) (f y)
    simpa only [dist_eq_norm, Real.norm_eq_abs] using hinverse x (hSJ hx) y (hSJ hy)
  have h := hLip.hausdorffMeasure_image_le (d := 1) (by norm_num)
  rw [hinj.invFunOn_image hSJ, MeasureTheory.hausdorffMeasure_real, ENNReal.rpow_one] at h
  rw [ENNReal.ofReal_eq_coe_nnreal (inv_nonneg.mpr hm.le)]
  exact h

/-- The finite union of scalar witness images at a charged budget. -/
noncomputable def scalarPurityWitnessImage (K : ℕ) (δ : ℝ) : Set (RealEuclidean 1) :=
  ⋃ s : ReverseShape 2 K,
    (ReverseBlocks.thickenedScalarPurityPolynomial s (8 * δ)).eval ''
      (ReverseBlocks.scalarPurityWitnessFormat s δ).source

/-- The target uses the standard computational-basis controlled phase. -/
noncomputable def controlledPhaseTarget (θ : ℝ) : Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ :=
  ⟨controlledPhase θ, controlledPhase_unitary θ⟩

/-- Angle reachability at the original charged footprint and Choi-score error. -/
def chargedControlledPhaseAngles (K : ℕ) (ε : ℝ) (J : Set ℝ) : Set ℝ :=
  {θ | θ ∈ J ∧ controlledPhaseTarget θ ∈ pureReachable 2 K ε}

/-- Common-map finite-mixed semantics give exactly the same angle set. -/
theorem chargedControlledPhaseAngles_eq_mixed (K : ℕ) (ε : ℝ) (J : Set ℝ) :
    chargedControlledPhaseAngles K ε J =
      {θ | θ ∈ J ∧ controlledPhaseTarget θ ∈ mixedReachable 2 K ε} := by
  rw [mixedReachable_eq_pureReachable]
  rfl

/-- Scalar coverage and inverse control transfer to the angle set. -/
theorem chargedControlledPhaseAngles_volume_le_scalarImage {K : ℕ} {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) {J : Set ℝ} {m : ℝ} (hm : 0 < m)
    (hinverse : ∀ x ∈ J, ∀ y ∈ J,
      |x - y| ≤ m⁻¹ * |phasePurityValue x - phasePurityValue y|) :
    volume (chargedControlledPhaseAngles K ε J) ≤
      ENNReal.ofReal m⁻¹ * volume (scalarPurityWitnessImage K (Real.sqrt (2 * ε))) := by
  have h := volume_le_inverse_lipschitz_image
    (show chargedControlledPhaseAngles K ε J ⊆ J from fun _ hθ => hθ.1) hm hinverse
  have hImage : scalarEuclidean '' (phasePurityValue '' chargedControlledPhaseAngles K ε J) ⊆
      scalarPurityWitnessImage K (Real.sqrt (2 * ε)) := by
    rintro y ⟨v, ⟨θ, hθ, rfl⟩, rfl⟩
    have hc := pureReachable_purity_mem_scalarWitness hε0 hε1 hθ.2
    change scalarEuclidean (purity (1 / 16) (controlledPhase θ)) ∈
      scalarPurityWitnessImage K (Real.sqrt (2 * ε)) at hc
    rw [purity_controlledPhase] at hc
    exact hc
  rw [← volume_scalarEuclidean_image (phasePurityValue '' chargedControlledPhaseAngles K ε J)] at h
  exact h.trans (mul_le_mul le_rfl (measure_mono hImage) zero_le zero_le)

/-- One universal geometric constant bounds every scalar witness image. -/
theorem exists_scalarPurityWitness_volume_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (K : ℕ) (s : ReverseShape 2 K) (δ : ℝ), 0 ≤ δ →
      volume ((ReverseBlocks.thickenedScalarPurityPolynomial s (8 * δ)).eval ''
        (ReverseBlocks.scalarPurityWitnessFormat s δ).source) ≤
      ENNReal.ofReal (C ^ (witnessCoordinateBudget 2 K + 2)) * euclideanUnitBallVolume 1 *
        ENNReal.ofReal (δ * (2 * (witnessCoordinateBudget 2 K : ℝ) + 8)) := by
  obtain ⟨C, hC, hvolume⟩ := hGeom
  refine ⟨C, hC, ?_⟩
  intro K s δ hδ
  apply hvolume (witnessCoordinateBudget 2 K + 1) 1 (by omega) (by decide)
    (ReverseBlocks.scalarPurityWitnessFormat s δ)
    (ReverseBlocks.thickenedScalarPurityPolynomial s (8 * δ))
    (ReverseBlocks.isCompact_scalarPurityWitnessFormat_source s δ)
    (ReverseBlocks.scalarPurityWitnessFormat_source_radius s δ) _ (by positivity)
  intro z hz
  exact (ReverseBlocks.thickenedScalarPurityPolynomial_jacobian_le s hδ (by positivity) hz).trans_eq
    (by ring)

/-- Summation uses the finite charged shape count. -/
theorem exists_scalarPurityWitness_union_volume_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (K : ℕ) (δ : ℝ), 0 ≤ δ →
      volume (scalarPurityWitnessImage K δ) ≤
      (K : ℝ≥0∞) ^ 3 * ENNReal.ofReal (C ^ (witnessCoordinateBudget 2 K + 2)) *
        euclideanUnitBallVolume 1 *
        ENNReal.ofReal (δ * (2 * (witnessCoordinateBudget 2 K : ℝ) + 8)) := by
  obtain ⟨C, hC, hvolume⟩ := exists_scalarPurityWitness_volume_constant hGeom
  refine ⟨C, hC, ?_⟩
  intro K δ hδ
  calc
    volume (scalarPurityWitnessImage K δ) ≤
        ∑ s : ReverseShape 2 K,
          volume ((ReverseBlocks.thickenedScalarPurityPolynomial s (8 * δ)).eval ''
            (ReverseBlocks.scalarPurityWitnessFormat s δ).source) :=
      measure_iUnion_fintype_le volume _
    _ ≤ ∑ _s : ReverseShape 2 K,
        ENNReal.ofReal (C ^ (witnessCoordinateBudget 2 K + 2)) * euclideanUnitBallVolume 1 *
          ENNReal.ofReal (δ * (2 * (witnessCoordinateBudget 2 K : ℝ) + 8)) :=
      Finset.sum_le_sum (fun s _ => hvolume K s δ hδ)
    _ = (Fintype.card (ReverseShape 2 K) : ℝ≥0∞) *
        (ENNReal.ofReal (C ^ (witnessCoordinateBudget 2 K + 2)) * euclideanUnitBallVolume 1 *
          ENNReal.ofReal (δ * (2 * (witnessCoordinateBudget 2 K : ℝ) + 8))) := by
      simp
    _ ≤ (K : ℝ≥0∞) ^ 3 *
        (ENNReal.ofReal (C ^ (witnessCoordinateBudget 2 K + 2)) * euclideanUnitBallVolume 1 *
          ENNReal.ofReal (δ * (2 * (witnessCoordinateBudget 2 K : ℝ) + 8))) := by
      gcongr
      exact_mod_cast ReverseShape.card_le_cube 2 K
    _ = _ := by ring

/-- Polynomial charged-budget factors are absorbed into a fixed exponential. -/
theorem scalarPurity_budget_le_exp {C : ℝ} (hC : 1 ≤ C) {K : ℕ} (hK : 1 ≤ K) :
    (K : ℝ) ^ 3 * C ^ (witnessCoordinateBudget 2 K + 2) * 2 *
        (2 * (witnessCoordinateBudget 2 K : ℝ) + 8) ≤
      20 * Real.exp ((128 * (4 + 2 * C)) * (K : ℝ) ^ 2) := by
  let P := witnessCoordinateBudget 2 K
  have hC0 : 0 ≤ C := by linarith
  have hP : (2 : ℝ) ≤ P := by
    have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hKs : (1 : ℝ) ≤ (K : ℝ) ^ 2 := one_le_pow₀ hKr
    dsimp only [P, witnessCoordinateBudget]
    push_cast
    nlinarith
  have hpower : C ^ (P + 2) ≤ Real.exp (2 * C * P) := by
    calc
      _ ≤ (Real.exp C) ^ (P + 2) := by
        gcongr
        linarith [Real.add_one_le_exp C]
      _ = Real.exp ((P + 2 : ℕ) * C) := by rw [Real.exp_nat_mul]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith
  have hlinear : 2 * (P : ℝ) + 8 ≤ 10 * Real.exp P := by
    nlinarith [Real.add_one_le_exp (P : ℝ)]
  have hcube : (K : ℝ) ^ 3 ≤ Real.exp (3 * (P : ℝ)) :=
    cube_budget_le_exp_coordinateBudget (by decide : 0 < 2)
  calc
    _ ≤ Real.exp (3 * (P : ℝ)) * Real.exp (2 * C * P) * 2 *
        (10 * Real.exp P) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_right
          (mul_le_mul hcube hpower (by positivity) (by positivity)) (by norm_num))
        hlinear (by linarith) (by positivity)
    _ = 20 * (Real.exp (3 * (P : ℝ)) * Real.exp (2 * C * P) * Real.exp P) := by ring
    _ = 20 * Real.exp ((128 * (4 + 2 * C)) * (K : ℝ) ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      dsimp only [P, witnessCoordinateBudget]
      push_cast
      ring

/-- One universal constant controls all finite charged scalar witness unions. -/
theorem exists_scalarPurityWitness_exponential_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (K : ℕ), 1 ≤ K → ∀ (δ : ℝ), 0 ≤ δ →
      volume (scalarPurityWitnessImage K δ) ≤
        ENNReal.ofReal (20 * Real.exp (C * (K : ℝ) ^ 2) * δ) := by
  obtain ⟨C₀, hC₀, hvolume⟩ := exists_scalarPurityWitness_union_volume_constant hGeom
  refine ⟨128 * (4 + 2 * C₀), by linarith, ?_⟩
  intro K hK δ hδ
  refine (hvolume K δ hδ).trans ?_
  rw [euclideanUnitBallVolume_one]
  have he : (K : ℝ≥0∞) ^ 3 * ENNReal.ofReal (C₀ ^ (witnessCoordinateBudget 2 K + 2)) * 2 *
      ENNReal.ofReal (δ * (2 * (witnessCoordinateBudget 2 K : ℝ) + 8)) =
        ENNReal.ofReal ((K : ℝ) ^ 3 * C₀ ^ (witnessCoordinateBudget 2 K + 2) * 2 *
          (δ * (2 * (witnessCoordinateBudget 2 K : ℝ) + 8))) := by
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (K : ℝ) ^ 3 *
          C₀ ^ (witnessCoordinateBudget 2 K + 2) * 2),
      ENNReal.ofReal_mul (by positivity : 0 ≤ (K : ℝ) ^ 3 * C₀ ^ (witnessCoordinateBudget 2 K + 2)),
      ENNReal.ofReal_mul (by positivity : 0 ≤ (K : ℝ) ^ 3),
      ENNReal.ofReal_pow (by positivity : 0 ≤ (K : ℝ))]
    norm_num
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = ((K : ℝ) ^ 3 * C₀ ^ (witnessCoordinateBudget 2 K + 2) * 2 *
        (2 * (witnessCoordinateBudget 2 K : ℝ) + 8)) * δ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (scalarPurity_budget_le_exp hC₀ hK) hδ

/-- The same universal exponential constant works on both open semicircles.
The interval constant is chosen only after its endpoints, and the conclusion
is Lebesgue outer measure at the original charged footprint. -/
theorem exists_chargedControlledPhase_length_constant (hGeom : PolynomialImageVolumeBound) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (a b : ℝ), a ≤ b →
      ((0 < a ∧ b < Real.pi) ∨ (Real.pi < a ∧ b < 2 * Real.pi)) →
      ∃ C_J : ℝ, 0 < C_J ∧ ∀ (K : ℕ), 1 ≤ K → ∀ (ε : ℝ), 0 < ε →
        volume (chargedControlledPhaseAngles K ε (Set.Icc a b)) ≤
          ENNReal.ofReal (C_J * Real.exp (C * (K : ℝ) ^ 2) * Real.sqrt ε) := by
  obtain ⟨C, hC, hvolume⟩ := exists_scalarPurityWitness_exponential_constant hGeom
  refine ⟨C, hC, ?_⟩
  intro a b hab hsemicircle
  obtain ⟨m, hm, hinverse⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |x - y| ≤ m⁻¹ * |phasePurityValue x - phasePurityValue y| := by
    rcases hsemicircle with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact exists_phasePurity_inverse_lipschitz_upper hab ha hb
    · exact exists_phasePurity_inverse_lipschitz_lower hab ha hb
  let A := 20 * Real.sqrt 2 * m⁻¹
  let C_J := A + |b - a|
  have hA : 0 < A := by dsimp only [A]; positivity
  have hCJ : 0 < C_J := by dsimp only [C_J]; linarith [abs_nonneg (b - a)]
  have hA_le : A ≤ C_J := by dsimp only [C_J]; linarith [abs_nonneg (b - a)]
  have hlength : b - a ≤ C_J := by
    dsimp only [C_J]
    linarith [le_abs_self (b - a)]
  refine ⟨C_J, hCJ, ?_⟩
  intro K hK ε hε
  by_cases hε1 : ε < 1
  · have h := chargedControlledPhaseAngles_volume_le_scalarImage (K := K) hε hε1 hm hinverse
    refine h.trans ?_
    calc
      _ ≤ ENNReal.ofReal m⁻¹ *
          ENNReal.ofReal (20 * Real.exp (C * (K : ℝ) ^ 2) * Real.sqrt (2 * ε)) :=
        mul_le_mul le_rfl (hvolume K hK _ (Real.sqrt_nonneg _)) zero_le zero_le
      _ = ENNReal.ofReal (m⁻¹ * (20 * Real.exp (C * (K : ℝ) ^ 2) * Real.sqrt (2 * ε))) :=
        (ENNReal.ofReal_mul (inv_nonneg.mpr hm.le)).symm
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        calc
          _ = A * Real.exp (C * (K : ℝ) ^ 2) * Real.sqrt ε := by dsimp only [A]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hA_le (Real.exp_pos _).le) (Real.sqrt_nonneg _)
  · have hset : chargedControlledPhaseAngles K ε (Set.Icc a b) ⊆ Set.Icc a b :=
      fun _ hθ => hθ.1
    refine (measure_mono hset).trans ?_
    rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    have hεge : 1 ≤ ε := le_of_not_gt hε1
    have hsqrt : 1 ≤ Real.sqrt ε := by
      simpa using Real.sqrt_le_sqrt hεge
    have hexp : 1 ≤ Real.exp (C * (K : ℝ) ^ 2) := Real.one_le_exp (by positivity)
    calc
      b - a ≤ C_J := hlength
      _ ≤ C_J * Real.exp (C * (K : ℝ) ^ 2) := le_mul_of_one_le_right hCJ.le hexp
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hsqrt

/-- Exactly the current three external inputs, with projection supplied by its proof. -/
theorem exists_chargedControlledPhase_length_constant_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (a b : ℝ), a ≤ b →
      ((0 < a ∧ b < Real.pi) ∨ (Real.pi < a ∧ b < 2 * Real.pi)) →
      ∃ C_J : ℝ, 0 < C_J ∧ ∀ (K : ℕ), 1 ≤ K → ∀ (ε : ℝ), 0 < ε →
        volume (chargedControlledPhaseAngles K ε (Set.Icc a b)) ≤
          ENNReal.ofReal (C_J * Real.exp (C * (K : ℝ) ^ 2) * Real.sqrt ε) :=
  exists_chargedControlledPhase_length_constant
    (ProvedProjection.polynomialImageVolumeBound_of_external hLRT hStratification hComponents)

/-- The scalar per-shape volume bound with the same three external inputs. -/
theorem exists_scalarPurityWitness_volume_constant_of_external
    (hLRT : LRTTheorem44)
    (hStratification : SemialgebraicSmoothStratificationTheorem)
    (hComponents : SemialgebraicComponentBoundTheorem) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (K : ℕ) (s : ReverseShape 2 K) (δ : ℝ), 0 ≤ δ →
      volume ((ReverseBlocks.thickenedScalarPurityPolynomial s (8 * δ)).eval ''
        (ReverseBlocks.scalarPurityWitnessFormat s δ).source) ≤
      ENNReal.ofReal (C ^ (witnessCoordinateBudget 2 K + 2)) * euclideanUnitBallVolume 1 *
        ENNReal.ofReal (δ * (2 * (witnessCoordinateBudget 2 K : ℝ) + 8)) :=
  exists_scalarPurityWitness_volume_constant
    (ProvedProjection.polynomialImageVolumeBound_of_external hLRT hStratification hComponents)

end NLQCLean

import NLQCLean.Approx.SlimNormalizedCubic
import NLQCLean.Approx.WitnessNormalization

/-!
# Common Euclidean coordinates for slim witnesses

The entries of the six slim blocks are enumerated, split into real and imaginary
parts, and embedded in the common source `ℝ^(64 K²)`; the embedding depends only on the slim
shape. Encoder blocks are divided by `√(d r)` and reverse completions by `√(d s)`, so every
padded valid source point has norm `√6`. The output is the overlap matrix in real Frobenius
coordinates scaled by `1/d` (normalized target distance).
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Common slim source dimension `P = 64 K²`. -/
def slimCoordinateBudget (K : ℕ) : ℕ := 64 * K ^ 2

/-- Normalized Frobenius output coordinates `H ↦ H/d` in `ℝ^(2d⁴)`. -/
noncomputable def normalizedOutputCoordinates (d : ℕ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℝ] RealEuclidean (2 * d ^ 4) :=
  (1 / (d : ℝ)) • (overlapOutputCoordinates d).toLinearMap

theorem normalizedOutputCoordinates_apply (d : ℕ) (H : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    normalizedOutputCoordinates d H = overlapOutputCoordinates d ((1 / (d : ℝ)) • H) := by
  simp [normalizedOutputCoordinates]

theorem norm_normalizedOutputCoordinates {d : ℕ} (hd : 0 < d)
    (H : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    ‖normalizedOutputCoordinates d H‖ = ‖H‖ / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  simp only [normalizedOutputCoordinates, LinearMap.smul_apply, LinearEquiv.coe_coe, norm_smul,
    norm_overlapOutputCoordinates, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hdR)]
  ring

namespace SlimReverseBlocks

variable {d K : ℕ}

abbrev ComplexEntry (s : SlimReverseShape d K) :=
  (Fin s.1.r × Fin s.1.r) ⊕ (Fin (frozenSupport d K) × Fin (frozenSupport d K)) ⊕
    ((Fin (d * s.1.r * s.1.mA) × Fin s.1.mA) × (Fin d × Fin s.1.r)) ⊕
    ((Fin (d * s.1.r * s.1.mB) × Fin s.1.mB) × (Fin d × Fin s.1.r)) ⊕
    (Fin (d * (K + frozenSupport d K)) × (Fin d × Fin (frozenSupport d K))) ⊕
    (Fin (d * (K + frozenSupport d K)) × (Fin d × Fin (frozenSupport d K)))

abbrev RealEntry (s : SlimReverseShape d K) := ComplexEntry s × Fin 2

noncomputable def complexEntryEquiv (s : SlimReverseShape d K) :
    SlimReverseBlocks s ≃ₗ[ℝ] (ComplexEntry s → ℂ) where
  toFun x := Sum.elim x.1 (Sum.elim x.2.1
    (Sum.elim (matrixEntryEquiv _ _ x.2.2.1)
      (Sum.elim (matrixEntryEquiv _ _ x.2.2.2.1)
        (Sum.elim (matrixEntryEquiv _ _ x.2.2.2.2.1) (matrixEntryEquiv _ _ x.2.2.2.2.2)))))
  invFun z := (fun i => z (.inl i), fun i => z (.inr (.inl i)),
    Matrix.of fun i j => z (.inr (.inr (.inl (i, j)))),
    Matrix.of fun i j => z (.inr (.inr (.inr (.inl (i, j))))),
    Matrix.of fun i j => z (.inr (.inr (.inr (.inr (.inl (i, j)))))),
    Matrix.of fun i j => z (.inr (.inr (.inr (.inr (.inr (i, j)))))))
  left_inv _ := rfl
  right_inv z := by funext i; rcases i with i | i | i | i | i | i <;> rfl
  map_add' _ _ := by funext i; rcases i with i | i | i | i | i | i <;> rfl
  map_smul' _ _ := by funext i; rcases i with i | i | i | i | i | i <;> rfl

theorem norm_complexEntryEquiv (s : SlimReverseShape d K) (x : SlimReverseBlocks s) :
    ‖WithLp.toLp 2 (complexEntryEquiv s x)‖ = euclideanNorm x := by
  have hs : ‖WithLp.toLp 2 (complexEntryEquiv s x)‖ ^ 2 = ∑ i, blockNorms x i ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, complexEntryEquiv, Fintype.sum_sum_type,
      Fintype.sum_prod_type, blockNorms, Fin.sum_univ_succ, frobNorm_sq,
      matrixEntryEquiv]
    rfl
  rw [euclideanNorm, ← hs, Real.sqrt_sq (norm_nonneg _)]

noncomputable def realEntryEquiv (s : SlimReverseShape d K) :
    SlimReverseBlocks s ≃ₗ[ℝ] (RealEntry s → ℝ) :=
  (complexEntryEquiv s).trans (complexRealCoordEquiv (ComplexEntry s))

noncomputable def euclideanCoordEquiv (s : SlimReverseShape d K) :
    SlimReverseBlocks s ≃ₗ[ℝ] EuclideanSpace ℝ (RealEntry s) :=
  (realEntryEquiv s).trans (WithLp.linearEquiv 2 ℝ (RealEntry s → ℝ)).symm

theorem norm_euclideanCoordEquiv (s : SlimReverseShape d K) (x : SlimReverseBlocks s) :
    ‖euclideanCoordEquiv s x‖ = euclideanNorm x :=
  (norm_complexRealCoordEquiv (complexEntryEquiv s x)).trans (norm_complexEntryEquiv s x)

theorem card_realEntry (s : SlimReverseShape d K) :
    Fintype.card (RealEntry s) = Module.finrank ℝ (SlimReverseBlocks s) := by
  have h := (realEntryEquiv s).finrank_eq
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one] using h.symm

theorem card_realEntry_le_budget (s : SlimReverseShape d K) (hd : 2 ≤ d) :
    Fintype.card (RealEntry s) ≤ slimCoordinateBudget K := by
  rw [card_realEntry]
  exact finrank_real_le s hd

noncomputable def coordinateEmbedding (s : SlimReverseShape d K) (hd : 2 ≤ d) :
    RealEntry s ↪ Fin (slimCoordinateBudget K) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_fin] using card_realEntry_le_budget s hd))

noncomputable def decodeCoordinates (s : SlimReverseShape d K) (hd : 2 ≤ d) :
    RealEuclidean (slimCoordinateBudget K) →ₗ[ℝ] SlimReverseBlocks s :=
  (euclideanCoordEquiv s).symm.toLinearMap.comp (euclideanRestrict (coordinateEmbedding s hd))

theorem euclideanNorm_decodeCoordinates_le (s : SlimReverseShape d K) (hd : 2 ≤ d)
    (x : RealEuclidean (slimCoordinateBudget K)) :
    euclideanNorm (decodeCoordinates s hd x) ≤ ‖x‖ := by
  rw [← norm_euclideanCoordEquiv s]
  simpa only [decodeCoordinates, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using norm_euclideanRestrict_le (coordinateEmbedding s hd) x

noncomputable def encodeCoordinates (s : SlimReverseShape d K) (hd : 2 ≤ d) :
    SlimReverseBlocks s →ₗ[ℝ] RealEuclidean (slimCoordinateBudget K) :=
  (euclideanExtend (coordinateEmbedding s hd)).comp (euclideanCoordEquiv s).toLinearMap

theorem decode_encodeCoordinates (s : SlimReverseShape d K) (hd : 2 ≤ d)
    (x : SlimReverseBlocks s) : decodeCoordinates s hd (encodeCoordinates s hd x) = x := by
  simp only [decodeCoordinates, encodeCoordinates, LinearMap.comp_apply,
    euclideanRestrict_extend, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

theorem norm_encodeCoordinates (s : SlimReverseShape d K) (hd : 2 ≤ d)
    (x : SlimReverseBlocks s) : ‖encodeCoordinates s hd x‖ = euclideanNorm x :=
  (norm_euclideanExtend (coordinateEmbedding s hd) (euclideanCoordEquiv s x)).trans
    (norm_euclideanCoordEquiv s x)

theorem encodeCoordinates_zero_padding (s : SlimReverseShape d K) (hd : 2 ≤ d)
    (x : SlimReverseBlocks s) {j : Fin (slimCoordinateBudget K)}
    (hj : j ∉ Set.range (coordinateEmbedding s hd)) : (encodeCoordinates s hd x) j = 0 :=
  euclideanExtend_apply_of_not_mem _ _ hj

theorem encode_decodeCoordinates_of_padding (s : SlimReverseShape d K) (hd : 2 ≤ d)
    (x : RealEuclidean (slimCoordinateBudget K))
    (hx : ∀ j ∉ Set.range (coordinateEmbedding s hd), x j = 0) :
    encodeCoordinates s hd (decodeCoordinates s hd x) = x := by
  simp only [encodeCoordinates, decodeCoordinates, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  ext j
  by_cases hj : j ∈ Set.range (coordinateEmbedding s hd)
  · obtain ⟨i, rfl⟩ := hj
    rw [euclideanExtend_apply]
    rfl
  · rw [euclideanExtend_apply_of_not_mem _ _ hj, hx j hj]

variable {s : SlimReverseShape d K}

/-- Inverse of the column-count rescaling on all six slim blocks. -/
noncomputable def normalizeBlocks : SlimReverseBlocks s →ₗ[ℝ] SlimReverseBlocks s where
  toFun x := (x.1, x.2.1, (Real.sqrt (d * s.1.r : ℝ))⁻¹ • x.2.2.1,
    (Real.sqrt (d * s.1.r : ℝ))⁻¹ • x.2.2.2.1,
    (Real.sqrt (d * frozenSupport d K : ℝ))⁻¹ • x.2.2.2.2.1,
    (Real.sqrt (d * frozenSupport d K : ℝ))⁻¹ • x.2.2.2.2.2)
  map_add' x y := by ext <;> simp [smul_add]
  map_smul' c x := by ext <;> simp [smul_comm c]

theorem rescale_normalizeBlocks (hd : 0 < d) (x : SlimReverseBlocks s) :
    rescaleBlocks (normalizeBlocks x) = x := by
  have hdr := pos_d_mul_r (s := s) hd
  have hdK := pos_d_mul_support (s := s) hd
  simp only [rescaleBlocks, normalizeBlocks, LinearMap.coe_mk, AddHom.coe_mk, smul_smul,
    mul_inv_cancel₀ (Real.sqrt_pos.mpr hdr).ne', mul_inv_cancel₀ (Real.sqrt_pos.mpr hdK).ne',
    one_smul]

theorem blockNorms_eq_one_of_valid {x : SlimReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) (i : Fin 6) : blockNorms x i = 1 := by
  have hdr := pos_d_mul_r (s := s) hd
  have hdK := pos_d_mul_support (s := s) hd
  have ha := norm_rescaled_isometry_eq_one hdr (by simp) hx.2.2.1
  have hb := norm_rescaled_isometry_eq_one hdr (by simp) hx.2.2.2.1
  have hta := norm_rescaled_isometry_eq_one hdK (by simp) hx.2.2.2.2.1
  have htb := norm_rescaled_isometry_eq_one hdK (by simp) hx.2.2.2.2.2
  fin_cases i
  · exact norm_euclidean_of_isUnitVector hx.1
  · exact norm_euclidean_of_isUnitVector hx.2.1
  · exact ha
  · exact hb
  · exact hta
  · exact htb

theorem euclideanNorm_eq_sqrt_six {x : SlimReverseBlocks s}
    (hx : IsValid (rescaleBlocks x)) (hd : 0 < d) : euclideanNorm x = Real.sqrt 6 := by
  simp [euclideanNorm, blockNorms_eq_one_of_valid hx hd]

theorem norm_padded_valid_eq_sqrt_six (s : SlimReverseShape d K) (hd : 2 ≤ d)
    {x : RealEuclidean (slimCoordinateBudget K)}
    (hx : IsValid (rescaleBlocks (decodeCoordinates s hd x)))
    (hpad : ∀ j ∉ Set.range (coordinateEmbedding s hd), x j = 0) : ‖x‖ = Real.sqrt 6 := by
  rw [← encode_decodeCoordinates_of_padding s hd x hpad, norm_encodeCoordinates]
  exact euclideanNorm_eq_sqrt_six hx (by omega)

variable (s) (hd : 2 ≤ d)

/-- The normalized raw overlap in common Euclidean source/output coordinates. -/
noncomputable def coordinateRawOverlap (x : RealEuclidean (slimCoordinateBudget K)) :
    RealEuclidean (2 * d ^ 4) :=
  normalizedOutputCoordinates d (overlap (rescaleBlocks (decodeCoordinates s hd x)))

noncomputable def coordinateCubic (x : RealEuclidean (slimCoordinateBudget K)) :
    RealEuclidean (slimCoordinateBudget K) :=
  encodeCoordinates s hd (normalizedCubicBlocks (decodeCoordinates s hd x))

/-- The global cubic overlap extension, normalized by `1/d`, in Euclidean coordinates. -/
noncomputable def coordinateOverlap (x : RealEuclidean (slimCoordinateBudget K)) :
    RealEuclidean (2 * d ^ 4) :=
  normalizedOutputCoordinates d (extendedOverlap (decodeCoordinates s hd x))

theorem coordinateOverlap_eq_raw_comp_cubic (x : RealEuclidean (slimCoordinateBudget K)) :
    coordinateOverlap s hd x = coordinateRawOverlap s hd (coordinateCubic s hd x) := by
  simp only [coordinateOverlap, coordinateRawOverlap, coordinateCubic,
    decode_encodeCoordinates, extendedOverlap]

theorem coordinateOverlap_eq_raw {x : RealEuclidean (slimCoordinateBudget K)}
    (hx : IsValid (rescaleBlocks (decodeCoordinates s hd x))) :
    coordinateOverlap s hd x = coordinateRawOverlap s hd x := by
  rw [coordinateOverlap, extendedOverlap_eq_overlap hx (by omega)]
  rfl

theorem contDiff_coordinateOverlap : ContDiff ℝ ∞ (coordinateOverlap s hd) := by
  let O := (normalizedOutputCoordinates d).toContinuousLinearMap
  let D := (decodeCoordinates s hd).toContinuousLinearMap
  exact O.contDiff.comp (contDiff_extendedOverlap.comp D.contDiff)

theorem fderiv_coordinateOverlap_apply (x v : RealEuclidean (slimCoordinateBudget K)) :
    fderiv ℝ (coordinateOverlap s hd) x v =
      normalizedOutputCoordinates d
        (fderiv ℝ extendedOverlap (decodeCoordinates s hd x) (decodeCoordinates s hd v)) := by
  let O := (normalizedOutputCoordinates d).toContinuousLinearMap
  let D := (decodeCoordinates s hd).toContinuousLinearMap
  have hH := (contDiff_extendedOverlap.differentiable (by simp)).differentiableAt
    (x := decodeCoordinates s hd x)
  have h := congrArg (fun L => L v)
    (O.hasFDerivAt.comp x (hH.hasFDerivAt.comp x D.hasFDerivAt)).fderiv
  convert h using 1 <;> rfl

noncomputable def coordinateLocalTerm (x : RealEuclidean (slimCoordinateBudget K)) :
    RealEuclidean (slimCoordinateBudget K) →L[ℝ] RealEuclidean (2 * d ^ 4) :=
  ((normalizedOutputCoordinates d).comp
    ((extendedLocalTerm (decodeCoordinates s hd x)).comp
      (decodeCoordinates s hd))).toContinuousLinearMap

noncomputable def coordinateResidual (x : RealEuclidean (slimCoordinateBudget K)) :
    RealEuclidean (slimCoordinateBudget K) →L[ℝ] RealEuclidean (2 * d ^ 4) :=
  ((normalizedOutputCoordinates d).comp
    ((extendedResidual (decodeCoordinates s hd x)).comp
      (decodeCoordinates s hd))).toContinuousLinearMap

theorem fderiv_coordinateOverlap_decomposition (x : RealEuclidean (slimCoordinateBudget K)) :
    fderiv ℝ (coordinateOverlap s hd) x =
      coordinateLocalTerm s hd x + coordinateResidual s hd x := by
  apply ContinuousLinearMap.ext
  intro v
  rw [fderiv_coordinateOverlap_apply]
  change normalizedOutputCoordinates d (fderiv ℝ extendedOverlap (decodeCoordinates s hd x)
    (decodeCoordinates s hd v)) =
      normalizedOutputCoordinates d
          (extendedLocalTerm (decodeCoordinates s hd x) (decodeCoordinates s hd v)) +
        normalizedOutputCoordinates d
          (extendedResidual (decodeCoordinates s hd x) (decodeCoordinates s hd v))
  rw [← map_add]
  congr 1
  exact congrArg (fun L => L (decodeCoordinates s hd v))
    (fderiv_extendedOverlap_decomposition (decodeCoordinates s hd x))

theorem finrank_coordinateLocalTerm_le {x : RealEuclidean (slimCoordinateBudget K)}
    (hx : IsValid (rescaleBlocks (decodeCoordinates s hd x))) :
    Module.finrank ℝ (LinearMap.range (coordinateLocalTerm s hd x).toLinearMap) ≤
      4 * d ^ 2 - 3 := by
  change Module.finrank ℝ (LinearMap.range ((normalizedOutputCoordinates d).comp
    ((extendedLocalTerm (decodeCoordinates s hd x)).comp (decodeCoordinates s hd)))) ≤ _
  rw [LinearMap.range_comp]
  exact (Submodule.finrank_map_le _ _).trans
    ((Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)).trans
      (finrank_extendedLocalTerm_le hx (by omega)))

/-- Every valid slim witness has a padded normalized representative of norm `√6` with its
normalized raw overlap unchanged. -/
theorem exists_normalized_coordinate_witness {x : SlimReverseBlocks s} (hx : IsValid x) :
    ∃ y : RealEuclidean (slimCoordinateBudget K),
      rescaleBlocks (decodeCoordinates s hd y) = x ∧
      (∀ j ∉ Set.range (coordinateEmbedding s hd), y j = 0) ∧
      ‖y‖ = Real.sqrt 6 ∧
      coordinateRawOverlap s hd y = normalizedOutputCoordinates d (overlap x) := by
  let y := encodeCoordinates s hd (normalizeBlocks x)
  have hy : rescaleBlocks (decodeCoordinates s hd y) = x := by
    dsimp only [y]
    rw [decode_encodeCoordinates, rescale_normalizeBlocks (by omega)]
  have hpad : ∀ j ∉ Set.range (coordinateEmbedding s hd), y j = 0 :=
    fun _ hj => encodeCoordinates_zero_padding s hd _ hj
  refine ⟨y, hy, hpad, norm_padded_valid_eq_sqrt_six s hd (hy.symm ▸ hx) hpad, ?_⟩
  rw [coordinateRawOverlap, hy]

end SlimReverseBlocks
end NLQCLean

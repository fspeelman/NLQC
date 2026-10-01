import NLQCLean.Approx.PVMCoordinateCount
import NLQCLean.Approx.PVMBlockNormalization
import NLQCLean.Approx.WitnessEuclideanCoordinates

/-!
# Padded real coordinates for the PVM six-block witness

The garbage entries use a dependent sum of the per-label
Schmidt-support squares. Encode into the common integral budget, preserving
the Euclidean sum of all six block norms and setting dummy coordinates to zero.
-/

namespace NLQCLean
namespace PVMReverseBlocks

open Matrix
open scoped Matrix.Norms.Frobenius

variable {d K : ℕ}

/-- Each summand enumerates the entries of one independent complex block. -/
abbrev ComplexEntry (s : PVMReverseShape d K) :=
  (Fin s.1.r × Fin s.1.r) ⊕ (Σ i : Fin d × Fin d, Fin (s.2.rank i) × Fin (s.2.rank i)) ⊕
    ((Fin (d * s.1.r * s.1.mA) × Fin s.1.mA) × (Fin d × Fin s.1.r)) ⊕
    ((Fin (d * s.1.r * s.1.mB) × Fin s.1.mB) × (Fin d × Fin s.1.r)) ⊕
    (Fin (d * K + s.supportSize) × s.Support) ⊕ (Fin (d * K + s.supportSize) × s.Support)

abbrev RealEntry (s : PVMReverseShape d K) := ComplexEntry s × Fin 2

/-- The entry list is a real-linear equivalence, with an explicit inverse. -/
noncomputable def complexEntryEquiv (s : PVMReverseShape d K) : PVMReverseBlocks s ≃ₗ[ℝ] (ComplexEntry s → ℂ) where
  toFun x := Sum.elim x.1 (Sum.elim (fun i => x.2.1 i.1 i.2)
    (Sum.elim (matrixEntryEquiv _ _ x.2.2.1)
      (Sum.elim (matrixEntryEquiv _ _ x.2.2.2.1)
        (Sum.elim (matrixEntryEquiv _ _ x.2.2.2.2.1) (matrixEntryEquiv _ _ x.2.2.2.2.2)))))
  invFun z := (fun i => z (.inl i), fun i j => z (.inr (.inl ⟨i,j⟩)),
    Matrix.of fun i j => z (.inr (.inr (.inl (i, j)))),
    Matrix.of fun i j => z (.inr (.inr (.inr (.inl (i, j))))),
    Matrix.of fun i j => z (.inr (.inr (.inr (.inr (.inl (i, j)))))),
    Matrix.of fun i j => z (.inr (.inr (.inr (.inr (.inr (i, j)))))))
  left_inv _ := rfl
  right_inv z := by funext i; rcases i with i | ⟨i,j⟩ | i | i | i | i <;> rfl
  map_add' _ _ := by funext i; rcases i with i | ⟨i,j⟩ | i | i | i | i <;> rfl
  map_smul' _ _ := by funext i; rcases i with i | ⟨i,j⟩ | i | i | i | i <;> rfl

theorem norm_complexEntryEquiv (s : PVMReverseShape d K) (x : PVMReverseBlocks s) :
    ‖WithLp.toLp 2 (complexEntryEquiv s x)‖ = euclideanNorm x := by
  have hg : (Real.sqrt (∑ i, ‖WithLp.toLp 2 (x.2.1 i)‖ ^ 2)) ^ 2 =
      ∑ i, ‖WithLp.toLp 2 (x.2.1 i)‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hs : ‖WithLp.toLp 2 (complexEntryEquiv s x)‖ ^ 2 = ∑ i, blockNorms x i ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, complexEntryEquiv, Fintype.sum_sum_type,
      Fintype.sum_prod_type, Fintype.sum_sigma, blockNorms, Fin.sum_univ_succ, frobNorm_sq,
      matrixEntryEquiv]
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type] at hg
    rw [hg]
    rfl
  rw [euclideanNorm, ← hs, Real.sqrt_sq (norm_nonneg _)]

noncomputable def realEntryEquiv (s : PVMReverseShape d K) : PVMReverseBlocks s ≃ₗ[ℝ] (RealEntry s → ℝ) :=
  (complexEntryEquiv s).trans (complexRealCoordEquiv (ComplexEntry s))

/-- The six-block space with its required Euclidean, rather than product, norm. -/
noncomputable def euclideanCoordEquiv (s : PVMReverseShape d K) :
    PVMReverseBlocks s ≃ₗ[ℝ] EuclideanSpace ℝ (RealEntry s) :=
  (realEntryEquiv s).trans (WithLp.linearEquiv 2 ℝ (RealEntry s → ℝ)).symm

theorem norm_euclideanCoordEquiv (s : PVMReverseShape d K) (x : PVMReverseBlocks s) :
    ‖euclideanCoordEquiv s x‖ = euclideanNorm x :=
  (norm_complexRealCoordEquiv (complexEntryEquiv s x)).trans (norm_complexEntryEquiv s x)

theorem card_realEntry (s : PVMReverseShape d K) :
    Fintype.card (RealEntry s) = Module.finrank ℝ (PVMReverseBlocks s) := by
  have h := (realEntryEquiv s).finrank_eq
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one] using h.symm

theorem card_realEntry_le_budget (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) :
    Fintype.card (RealEntry s) ≤ pvmWitnessCoordinateBudget d K := by
  rw [card_realEntry]
  exact finrank_real_le_budget s hd hfloor

/-- A fixed coordinate embedding depending only on the charged shape. -/
noncomputable def coordinateEmbedding (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) :
    RealEntry s ↪ Fin (pvmWitnessCoordinateBudget d K) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_fin] using card_realEntry_le_budget s hd hfloor))

/-- Decode the common source by restricting to the shape's entry coordinates. -/
noncomputable def decodeCoordinates (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) :
    RealEuclidean (pvmWitnessCoordinateBudget d K) →ₗ[ℝ] PVMReverseBlocks s :=
  (euclideanCoordEquiv s).symm.toLinearMap.comp (euclideanRestrict (coordinateEmbedding s hd hfloor))

theorem euclideanNorm_decodeCoordinates_le (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K)
    (x : RealEuclidean (pvmWitnessCoordinateBudget d K)) :
    euclideanNorm (decodeCoordinates s hd hfloor x) ≤ ‖x‖ := by
  rw [← norm_euclideanCoordEquiv s]
  simpa only [decodeCoordinates, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using norm_euclideanRestrict_le (coordinateEmbedding s hd hfloor) x

/-- Encode all entries and set every unused coordinate to zero. -/
noncomputable def encodeCoordinates (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) :
    PVMReverseBlocks s →ₗ[ℝ] RealEuclidean (pvmWitnessCoordinateBudget d K) :=
  (euclideanExtend (coordinateEmbedding s hd hfloor)).comp (euclideanCoordEquiv s).toLinearMap

theorem decode_encodeCoordinates (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) (x : PVMReverseBlocks s) :
    decodeCoordinates s hd hfloor (encodeCoordinates s hd hfloor x) = x := by
  simp only [decodeCoordinates, encodeCoordinates, LinearMap.comp_apply,
    euclideanRestrict_extend, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

theorem norm_encodeCoordinates (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) (x : PVMReverseBlocks s) :
    ‖encodeCoordinates s hd hfloor x‖ = euclideanNorm x :=
  (norm_euclideanExtend (coordinateEmbedding s hd hfloor) (euclideanCoordEquiv s x)).trans
    (norm_euclideanCoordEquiv s x)

theorem encodeCoordinates_zero_padding (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K) (x : PVMReverseBlocks s)
    {j : Fin (pvmWitnessCoordinateBudget d K)} (hj : j ∉ Set.range (coordinateEmbedding s hd hfloor)) :
    (encodeCoordinates s hd hfloor x) j = 0 :=
  euclideanExtend_apply_of_not_mem _ _ hj

/-- Zero padding characterizes the image of the coordinate encoding. -/
theorem encode_decodeCoordinates_of_padding (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K)
    (x : RealEuclidean (pvmWitnessCoordinateBudget d K))
    (hx : ∀ j ∉ Set.range (coordinateEmbedding s hd hfloor), x j = 0) :
    encodeCoordinates s hd hfloor (decodeCoordinates s hd hfloor x) = x := by
  simp only [encodeCoordinates, decodeCoordinates, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  ext j
  by_cases hj : j ∈ Set.range (coordinateEmbedding s hd hfloor)
  · obtain ⟨i, rfl⟩ := hj
    rw [euclideanExtend_apply]
    rfl
  · rw [euclideanExtend_apply_of_not_mem _ _ hj, hx j hj]

/-- The raw overlap in common Euclidean input and output coordinates. -/
noncomputable def coordinateRawOverlap (s : PVMReverseShape d K) (hd : 0 < d)
    (hfloor : d ^ 2 ≤ 4 * K) (x : RealEuclidean (pvmWitnessCoordinateBudget d K)) :
    RealEuclidean (2 * d ^ 4) :=
  overlapOutputCoordinates d (overlap (rescaleBlocks (decodeCoordinates s hd hfloor x)))

theorem norm_padded_valid_eq_sqrt_six (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K)
    {x : RealEuclidean (pvmWitnessCoordinateBudget d K)}
    (hx : IsValid (rescaleBlocks (decodeCoordinates s hd hfloor x)))
    (hpad : ∀ j ∉ Set.range (coordinateEmbedding s hd hfloor), x j = 0) : ‖x‖ = Real.sqrt 6 := by
  rw [← encode_decodeCoordinates_of_padding s hd hfloor x hpad, norm_encodeCoordinates]
  exact euclideanNorm_eq_sqrt_six hx hd

/-- Every original valid witness has a padded normalized representative of
the exact required radius, with its raw overlap unchanged. -/
theorem exists_normalized_coordinate_witness (s : PVMReverseShape d K) (hd : 0 < d) (hfloor : d ^ 2 ≤ 4 * K)
    {x : PVMReverseBlocks s} (hx : IsValid x) :
    ∃ y : RealEuclidean (pvmWitnessCoordinateBudget d K),
      rescaleBlocks (decodeCoordinates s hd hfloor y) = x ∧
      (∀ j ∉ Set.range (coordinateEmbedding s hd hfloor), y j = 0) ∧
      ‖y‖ = Real.sqrt 6 ∧ coordinateRawOverlap s hd hfloor y = overlapOutputCoordinates d (overlap x) := by
  let y := encodeCoordinates s hd hfloor (normalizeBlocks x)
  have hy : rescaleBlocks (decodeCoordinates s hd hfloor y) = x := by
    dsimp only [y]
    rw [decode_encodeCoordinates, rescale_normalizeBlocks hd]
  have hpad : ∀ j ∉ Set.range (coordinateEmbedding s hd hfloor), y j = 0 :=
    fun _ hj => encodeCoordinates_zero_padding s hd hfloor _ hj
  refine ⟨y, hy, hpad, norm_padded_valid_eq_sqrt_six s hd hfloor (hy.symm ▸ hx) hpad, ?_⟩
  rw [coordinateRawOverlap, hy]

end PVMReverseBlocks
end NLQCLean

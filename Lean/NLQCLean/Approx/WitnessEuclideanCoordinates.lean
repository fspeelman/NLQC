import NLQCLean.LinearAlgebra.EuclideanCoordinates
import NLQCLean.Rigidity.ExtendedWitnessDifferential
import NLQCLean.Geometry.PolynomialImageVolumeHypothesis

/-!
# Real Euclidean coordinates for the six-block witness

Enumerate precisely the entries of the six independent complex blocks,
split real and imaginary parts, and embed their coordinates in the common
integral budget P=32d²K². The coordinate norm is the explicit block l2 norm.
-/

namespace NLQCLean
namespace ReverseBlocks

open Matrix
open scoped Matrix.Norms.Frobenius

variable {d K : ℕ}

/-- Each summand enumerates the entries of one independent complex block. -/
abbrev ComplexEntry (s : ReverseShape d K) :=
  (Fin s.r × Fin s.r) ⊕ (Fin K × Fin K) ⊕
    ((Fin (d * s.r * s.mA) × Fin s.mA) × (Fin d × Fin s.r)) ⊕
    ((Fin (d * s.r * s.mB) × Fin s.mB) × (Fin d × Fin s.r)) ⊕
    (Fin (2 * d * K) × (Fin d × Fin K)) ⊕ (Fin (2 * d * K) × (Fin d × Fin K))

abbrev RealEntry (s : ReverseShape d K) := ComplexEntry s × Fin 2

/-- The entry list is a real-linear equivalence, with an explicit inverse. -/
noncomputable def complexEntryEquiv (s : ReverseShape d K) : ReverseBlocks s ≃ₗ[ℝ] (ComplexEntry s → ℂ) where
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

theorem norm_complexEntryEquiv (s : ReverseShape d K) (x : ReverseBlocks s) :
    ‖WithLp.toLp 2 (complexEntryEquiv s x)‖ = euclideanNorm x := by
  have hs : ‖WithLp.toLp 2 (complexEntryEquiv s x)‖ ^ 2 = ∑ i, blockNorms x i ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq, complexEntryEquiv, Fintype.sum_sum_type,
      Fintype.sum_prod_type, blockNorms, Fin.sum_univ_succ, frobNorm_sq,
      matrixEntryEquiv]
    rfl
  rw [euclideanNorm, ← hs, Real.sqrt_sq (norm_nonneg _)]

noncomputable def realEntryEquiv (s : ReverseShape d K) : ReverseBlocks s ≃ₗ[ℝ] (RealEntry s → ℝ) :=
  (complexEntryEquiv s).trans (complexRealCoordEquiv (ComplexEntry s))

/-- The six-block space with its required Euclidean, rather than product, norm. -/
noncomputable def euclideanCoordEquiv (s : ReverseShape d K) :
    ReverseBlocks s ≃ₗ[ℝ] EuclideanSpace ℝ (RealEntry s) :=
  (realEntryEquiv s).trans (WithLp.linearEquiv 2 ℝ (RealEntry s → ℝ)).symm

theorem norm_euclideanCoordEquiv (s : ReverseShape d K) (x : ReverseBlocks s) :
    ‖euclideanCoordEquiv s x‖ = euclideanNorm x :=
  (norm_complexRealCoordEquiv (complexEntryEquiv s x)).trans (norm_complexEntryEquiv s x)

theorem card_realEntry (s : ReverseShape d K) :
    Fintype.card (RealEntry s) = Module.finrank ℝ (ReverseBlocks s) := by
  have h := (realEntryEquiv s).finrank_eq
  simpa only [Module.finrank_pi, Module.finrank_self, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one] using h.symm

theorem card_realEntry_le_budget (s : ReverseShape d K) (hd : 0 < d) :
    Fintype.card (RealEntry s) ≤ witnessCoordinateBudget d K := by
  rw [card_realEntry]
  exact (finrank_real_le s hd).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 16 ≤ 32)))

/-- A fixed coordinate embedding depending only on the charged shape. -/
noncomputable def coordinateEmbedding (s : ReverseShape d K) (hd : 0 < d) :
    RealEntry s ↪ Fin (witnessCoordinateBudget d K) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_fin] using card_realEntry_le_budget s hd))

/-- Decode the common source by restricting to the shape's entry coordinates. -/
noncomputable def decodeCoordinates (s : ReverseShape d K) (hd : 0 < d) :
    RealEuclidean (witnessCoordinateBudget d K) →ₗ[ℝ] ReverseBlocks s :=
  (euclideanCoordEquiv s).symm.toLinearMap.comp (euclideanRestrict (coordinateEmbedding s hd))

theorem euclideanNorm_decodeCoordinates_le (s : ReverseShape d K) (hd : 0 < d)
    (x : RealEuclidean (witnessCoordinateBudget d K)) :
    euclideanNorm (decodeCoordinates s hd x) ≤ ‖x‖ := by
  rw [← norm_euclideanCoordEquiv s]
  simpa only [decodeCoordinates, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] using norm_euclideanRestrict_le (coordinateEmbedding s hd) x

/-- Encode all entries and set every unused coordinate to zero. -/
noncomputable def encodeCoordinates (s : ReverseShape d K) (hd : 0 < d) :
    ReverseBlocks s →ₗ[ℝ] RealEuclidean (witnessCoordinateBudget d K) :=
  (euclideanExtend (coordinateEmbedding s hd)).comp (euclideanCoordEquiv s).toLinearMap

theorem decode_encodeCoordinates (s : ReverseShape d K) (hd : 0 < d) (x : ReverseBlocks s) :
    decodeCoordinates s hd (encodeCoordinates s hd x) = x := by
  simp only [decodeCoordinates, encodeCoordinates, LinearMap.comp_apply,
    euclideanRestrict_extend, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]

theorem norm_encodeCoordinates (s : ReverseShape d K) (hd : 0 < d) (x : ReverseBlocks s) :
    ‖encodeCoordinates s hd x‖ = euclideanNorm x :=
  (norm_euclideanExtend (coordinateEmbedding s hd) (euclideanCoordEquiv s x)).trans
    (norm_euclideanCoordEquiv s x)

theorem encodeCoordinates_zero_padding (s : ReverseShape d K) (hd : 0 < d) (x : ReverseBlocks s)
    {j : Fin (witnessCoordinateBudget d K)} (hj : j ∉ Set.range (coordinateEmbedding s hd)) :
    (encodeCoordinates s hd x) j = 0 :=
  euclideanExtend_apply_of_not_mem _ _ hj

/-- Zero padding characterizes the image of the coordinate encoding. -/
theorem encode_decodeCoordinates_of_padding (s : ReverseShape d K) (hd : 0 < d)
    (x : RealEuclidean (witnessCoordinateBudget d K))
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

end ReverseBlocks

open scoped Matrix.Norms.Frobenius

/-- Fixed entry order for the complex d² by d² overlap output. -/
noncomputable def overlapOutputIndex (d : ℕ) :
    (((Fin d × Fin d) × (Fin d × Fin d)) × Fin 2) ≃ Fin (2 * d ^ 4) :=
  Fintype.equivOfCardEq (by simp only [Fintype.card_prod, Fintype.card_fin]; ring)

/-- The output is identified with R^(2d^4), preserving the Frobenius norm. -/
noncomputable def overlapOutputCoordinates (d : ℕ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ ≃ₗ[ℝ] RealEuclidean (2 * d ^ 4) :=
  (matrixEuclideanCoordEquiv _ _).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (overlapOutputIndex d)).toLinearEquiv

theorem norm_overlapOutputCoordinates {d : ℕ} (H : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    ‖overlapOutputCoordinates d H‖ = ‖H‖ := by
  exact ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (overlapOutputIndex d)).norm_map _).trans
    (norm_matrixEuclideanCoordEquiv H)

end NLQCLean

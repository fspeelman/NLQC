import NLQCLean.Geometry.UnitaryNormalCoordinates
import NLQCLean.Approx.WitnessDifferentialBounds
import NLQCLean.LinearAlgebra.TensorOperatorNorm

/-!
# The operator-norm unitary normal embedding

The compact normal domain consists of a
unitary `U` and a Hermitian `Q` with `‖Q‖_op ≤ 1/2`; it is bounded in Frobenius norm by
`√D/2`. The map `(U,Q) ↦ U(I+Q)` is injective by the mixed Frobenius/operator version of the
cancellation argument in `UnitaryNormalEmbedding`.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `A ↦ toCLM A` as a complex-linear map. -/
noncomputable def toCLMLinear (m n : Type*) [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] : Matrix m n ℂ →ₗ[ℂ] (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m) where
  toFun := toCLM
  map_add' A B := by
    ext x i
    simp [toCLM_apply, Matrix.add_mulVec]
  map_smul' c A := by
    ext x i
    simp [toCLM_apply, Matrix.smul_mulVec]

theorem continuous_opNorm (m n : Type*) [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] : Continuous (fun A : Matrix m n ℂ => opNorm A) :=
  continuous_norm.comp (LinearMap.continuous_of_finiteDimensional (toCLMLinear m n))

theorem eq_of_one_add_sq_eq_of_opNorm_le_half (Q R : Matrix n n ℂ)
    (hQ : opNorm Q ≤ 1 / 2) (hR : opNorm R ≤ 1 / 2)
    (he : (1 + Q) ^ 2 = (1 + R) ^ 2) : Q = R := by
  have hz : (2 : ℝ) • (Q - R) + (Q * (Q - R) + (Q - R) * R) = 0 := by
    calc
      _ = (1 + Q) ^ 2 - (1 + R) ^ 2 := by rw [two_smul]; noncomm_ring
      _ = 0 := sub_eq_zero.mpr he
  have hn : 2 * ‖Q - R‖ ≤ opNorm Q * ‖Q - R‖ + ‖Q - R‖ * opNorm R := by
    calc
      _ = ‖(2 : ℝ) • (Q - R)‖ := by simp [norm_smul]
      _ = ‖Q * (Q - R) + (Q - R) * R‖ := by
        rw [eq_neg_of_add_eq_zero_left hz, norm_neg]
      _ ≤ ‖Q * (Q - R)‖ + ‖(Q - R) * R‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (frobNorm_mul_le _ _) (frobNorm_mul_le' _ _)
  have h₁ := mul_le_mul_of_nonneg_right hQ (norm_nonneg (Q - R))
  have h₂ := mul_le_mul_of_nonneg_left hR (norm_nonneg (Q - R))
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (Q - R)]

theorem eq_of_mul_one_add_eq_of_opNorm_le_half (X Y Q : Matrix n n ℂ)
    (hQ : opNorm Q ≤ 1 / 2) (he : X * (1 + Q) = Y * (1 + Q)) : X = Y := by
  have hz : (X - Y) + (X - Y) * Q = 0 := by
    calc
      _ = X * (1 + Q) - Y * (1 + Q) := by noncomm_ring
      _ = 0 := sub_eq_zero.mpr he
  have hn : ‖X - Y‖ ≤ ‖X - Y‖ * opNorm Q := by
    calc
      _ = ‖-((X - Y) * Q)‖ := congrArg norm (eq_neg_of_add_eq_zero_left hz)
      _ = ‖(X - Y) * Q‖ := norm_neg _
      _ ≤ _ := frobNorm_mul_le' _ _
  have h := mul_le_mul_of_nonneg_left hQ (norm_nonneg (X - Y))
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (X - Y)]

/-- Equality of two operator-normal images determines both coordinates. -/
theorem unitary_opNormal_eq_iff (U V Q R : Matrix n n ℂ)
    (hU : IsIsometry U) (hV : IsIsometry V) (hQ : Q.IsHermitian) (hR : R.IsHermitian)
    (hQn : opNorm Q ≤ 1 / 2) (hRn : opNorm R ≤ 1 / 2) :
    U * (1 + Q) = V * (1 + R) ↔ U = V ∧ Q = R := by
  constructor
  · intro he
    have hg (W S : Matrix n n ℂ) (hW : IsIsometry W) (hS : S.IsHermitian) :
        (W * (1 + S))ᴴ * (W * (1 + S)) = (1 + S) ^ 2 := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_add, Matrix.conjTranspose_one, hS.eq]
      calc
        _ = (1 + S) * (Wᴴ * W) * (1 + S) := by noncomm_ring
        _ = (1 + S) ^ 2 := by rw [hW, Matrix.mul_one, pow_two]
    have hs : (1 + Q) ^ 2 = (1 + R) ^ 2 := by
      rw [← hg U Q hU hQ, he, hg V R hV hR]
    have hQR := eq_of_one_add_sq_eq_of_opNorm_le_half Q R hQn hRn hs
    subst R
    exact ⟨eq_of_mul_one_add_eq_of_opNorm_le_half U V Q hQn he, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The Hermitian operator half-ball, with the Frobenius topology. -/
abbrev HermitianOpHalfBall (n : Type*) [Fintype n] [DecidableEq n] :=
  {Q : Matrix n n ℂ // Q.IsHermitian ∧ opNorm Q ≤ (1 / 2 : ℝ)}

instance compactSpace_hermitianOpHalfBall (n : Type*) [Fintype n] [DecidableEq n] :
    CompactSpace (HermitianOpHalfBall n) := by
  apply isCompact_iff_compactSpace.mp
  have hh : IsClosed {Q : Matrix n n ℂ | Q.IsHermitian} :=
    isClosed_eq (conjTransposeCLM (𝕜 := ℂ) (m := n) (n := n)).continuous continuous_id
  have ho : IsClosed {Q : Matrix n n ℂ | opNorm Q ≤ (1 / 2 : ℝ)} :=
    isClosed_le (continuous_opNorm n n) continuous_const
  refine (isCompact_closedBall (0 : Matrix n n ℂ) (Real.sqrt (Fintype.card n) / 2)).of_isClosed_subset
    (hh.inter ho) ?_
  rintro Q ⟨-, hQ⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖Q‖ ≤ Real.sqrt (Fintype.card n) * opNorm Q := frobNorm_le_sqrt_card_mul_opNorm Q
    _ ≤ Real.sqrt (Fintype.card n) * (1 / 2) :=
        mul_le_mul_of_nonneg_left hQ (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- The compact operator-normal domain. -/
abbrev OpNormalDomain (n : Type*) [Fintype n] [DecidableEq n] :=
  Matrix.unitaryGroup n ℂ × HermitianOpHalfBall n

noncomputable def opNormalMap (n : Type*) [Fintype n] [DecidableEq n]
    (z : OpNormalDomain n) : Matrix n n ℂ :=
  (z.1 : Matrix n n ℂ) * (1 + z.2.1)

theorem continuous_opNormalMap (n : Type*) [Fintype n] [DecidableEq n] :
    Continuous (opNormalMap n) := by
  unfold opNormalMap
  fun_prop

theorem injective_opNormalMap (n : Type*) [Fintype n] [DecidableEq n] :
    Function.Injective (opNormalMap n) := by
  intro z w he
  have h := (unitary_opNormal_eq_iff (z.1 : Matrix n n ℂ) (w.1 : Matrix n n ℂ)
    (z.2.1 : Matrix n n ℂ) (w.2.1 : Matrix n n ℂ)
    (Matrix.mem_unitaryGroup_iff'.mp z.1.property) (Matrix.mem_unitaryGroup_iff'.mp w.1.property)
    z.2.property.1 w.2.property.1 z.2.property.2 w.2.property.2).mp he
  apply Prod.ext
  · exact Subtype.ext h.1
  · exact Subtype.ext h.2

noncomputable def opNormalEuclideanMap (n : Type*) [Fintype n] [DecidableEq n]
    (z : OpNormalDomain n) : EuclideanSpace ℝ ((n × n) × Fin 2) :=
  matrixFrobeniusCoordinates n n (opNormalMap n z)

theorem continuous_opNormalEuclideanMap (n : Type*) [Fintype n] [DecidableEq n] :
    Continuous (opNormalEuclideanMap n) :=
  (matrixFrobeniusCoordinates n n).continuous.comp (continuous_opNormalMap n)

theorem isClosedEmbedding_opNormalEuclideanMap (n : Type*) [Fintype n] [DecidableEq n] :
    Topology.IsClosedEmbedding (opNormalEuclideanMap n) :=
  (matrixFrobeniusCoordinates n n).toHomeomorph.isClosedEmbedding.comp
    ((continuous_opNormalMap n).isClosedEmbedding (injective_opNormalMap n))

theorem measurableEmbedding_opNormalEuclideanMap (n : Type*) [Fintype n] [DecidableEq n] :
    MeasurableEmbedding (opNormalEuclideanMap n) :=
  (isClosedEmbedding_opNormalEuclideanMap n).measurableEmbedding

theorem isCompact_range_opNormalEuclideanMap (n : Type*) [Fintype n] [DecidableEq n] :
    IsCompact (Set.range (opNormalEuclideanMap n)) :=
  isCompact_range (continuous_opNormalEuclideanMap n)

theorem opNormalEuclideanMap_left_mul (U : Matrix.unitaryGroup n ℂ) (z : OpNormalDomain n) :
    opNormalEuclideanMap n (U * z.1, z.2) = unitaryLeftEuclidean U (opNormalEuclideanMap n z) := by
  rw [opNormalEuclideanMap, opNormalEuclideanMap, unitaryLeftEuclidean_coordinates]
  congr 1
  change ((U : Matrix n n ℂ) * (z.1 : Matrix n n ℂ)) * (1 + z.2.1) =
    (U : Matrix n n ℂ) * ((z.1 : Matrix n n ℂ) * (1 + z.2.1))
  exact Matrix.mul_assoc _ _ _

theorem norm_opNormalEuclideanMap_sub (z : OpNormalDomain n) :
    ‖opNormalEuclideanMap n z - matrixFrobeniusCoordinates n n (z.1 : Matrix n n ℂ)‖ = ‖z.2.1‖ := by
  rw [opNormalEuclideanMap, ← map_sub, LinearIsometryEquiv.norm_map]
  have he : opNormalMap n z - (z.1 : Matrix n n ℂ) = (z.1 : Matrix n n ℂ) * z.2.1 := by
    simp only [opNormalMap, Matrix.mul_add, Matrix.mul_one, add_sub_cancel_left]
  rw [he]
  exact (show IsIsometry (z.1 : Matrix n n ℂ) from z.1.property.1).frobNorm_mul_eq _

end NLQCLean

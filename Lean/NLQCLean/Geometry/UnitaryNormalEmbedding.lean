import NLQCLean.Models.CompactForward
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# The compact unitary normal embedding

Injectivity of `U(I+Q)` for Hermitian Q of Frobenius norm at most 1/2.
The proof uses norm estimates and does not assume a polar decomposition.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Matrix geometry uses the Borel sigma algebra of its existing topology. -/
noncomputable instance complexMatrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  borel _

instance complexMatrixBorelSpace (m n : Type*) : BorelSpace (Matrix m n ℂ) := ⟨rfl⟩

instance complexMatrixSecondCountable (m n : Type*) [Countable m] [Countable n] :
    SecondCountableTopology (Matrix m n ℂ) :=
  inferInstanceAs (SecondCountableTopology (m → n → ℂ))

instance complexMatrixSubtypeSecondCountable (m n : Type*) [Countable m] [Countable n]
    (p : Matrix m n ℂ → Prop) : SecondCountableTopology {M // p M} :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology

theorem eq_of_one_add_sq_eq_of_norm_le_half (Q R : Matrix n n ℂ)
    (hQ : ‖Q‖ ≤ 1 / 2) (hR : ‖R‖ ≤ 1 / 2)
    (he : (1 + Q) ^ 2 = (1 + R) ^ 2) : Q = R := by
  have hz : (2 : ℝ) • (Q - R) + (Q * (Q - R) + (Q - R) * R) = 0 := by
    calc
      _ = (1 + Q) ^ 2 - (1 + R) ^ 2 := by rw [two_smul]; noncomm_ring
      _ = 0 := sub_eq_zero.mpr he
  have hn : 2 * ‖Q - R‖ ≤ ‖Q‖ * ‖Q - R‖ + ‖Q - R‖ * ‖R‖ := by
    calc
      _ = ‖(2 : ℝ) • (Q - R)‖ := by simp [norm_smul]
      _ = ‖Q * (Q - R) + (Q - R) * R‖ := by
        rw [eq_neg_of_add_eq_zero_left hz, norm_neg]
      _ ≤ ‖Q * (Q - R)‖ + ‖(Q - R) * R‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (Matrix.frobenius_norm_mul _ _) (Matrix.frobenius_norm_mul _ _)
  have h₁ := mul_le_mul_of_nonneg_right hQ (norm_nonneg (Q - R))
  have h₂ := mul_le_mul_of_nonneg_left hR (norm_nonneg (Q - R))
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (Q - R)]

theorem eq_of_mul_one_add_eq_of_norm_le_half (X Y Q : Matrix n n ℂ)
    (hQ : ‖Q‖ ≤ 1 / 2) (he : X * (1 + Q) = Y * (1 + Q)) : X = Y := by
  have hz : (X - Y) + (X - Y) * Q = 0 := by
    calc
      _ = X * (1 + Q) - Y * (1 + Q) := by noncomm_ring
      _ = 0 := sub_eq_zero.mpr he
  have hn : ‖X - Y‖ ≤ ‖X - Y‖ * ‖Q‖ := by
    calc
      _ = ‖-((X - Y) * Q)‖ := congrArg norm (eq_neg_of_add_eq_zero_left hz)
      _ = ‖(X - Y) * Q‖ := norm_neg _
      _ ≤ _ := Matrix.frobenius_norm_mul _ _
  have h := mul_le_mul_of_nonneg_left hQ (norm_nonneg (X - Y))
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg (X - Y)]

/-- Equality of two normal images determines both the unitary and the normal coordinate. -/
theorem unitary_normal_eq_iff (U V Q R : Matrix n n ℂ)
    (hU : IsIsometry U) (hV : IsIsometry V) (hQ : Q.IsHermitian) (hR : R.IsHermitian)
    (hQn : ‖Q‖ ≤ 1 / 2) (hRn : ‖R‖ ≤ 1 / 2) :
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
    have hQR := eq_of_one_add_sq_eq_of_norm_le_half Q R hQn hRn hs
    subst R
    exact ⟨eq_of_mul_one_add_eq_of_norm_le_half U V Q hQn he, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem isCompact_unitaryGroup (n : Type*) [Fintype n] [DecidableEq n] :
    IsCompact (Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ)) := by
  have he : (Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ)) = {U | IsIsometry U} := by
    ext U
    exact Matrix.mem_unitaryGroup_iff'
  rw [he]
  exact isCompact_isometries n n

instance compactSpace_unitaryGroup (n : Type*) [Fintype n] [DecidableEq n] :
    CompactSpace (Matrix.unitaryGroup n ℂ) :=
  isCompact_iff_compactSpace.mp (isCompact_unitaryGroup n)

/-- The closed Hermitian half-ball in its Frobenius topology. -/
abbrev HermitianHalfBall (n : Type*) [Fintype n] :=
  {Q : Matrix n n ℂ // Q.IsHermitian ∧ ‖Q‖ ≤ (1 / 2 : ℝ)}

instance compactSpace_hermitianHalfBall (n : Type*) [Fintype n] [DecidableEq n] :
    CompactSpace (HermitianHalfBall n) := by
  apply isCompact_iff_compactSpace.mp
  have hh : IsClosed {Q : Matrix n n ℂ | Q.IsHermitian} :=
    isClosed_eq (conjTransposeCLM (𝕜 := ℂ) (m := n) (n := n)).continuous continuous_id
  have hc := (isCompact_closedBall (0 : Matrix n n ℂ) (1 / 2 : ℝ)).inter_left hh
  convert! hc using 1
  simp only [Set.inter_def, Metric.mem_closedBall, dist_zero_right, Set.mem_ofPred_eq]
  rfl

/-- The compact normal domain. Only its topology is used here. -/
abbrev UnitaryNormalDomain (n : Type*) [Fintype n] [DecidableEq n] :=
  Matrix.unitaryGroup n ℂ × HermitianHalfBall n

noncomputable def unitaryNormalMap (n : Type*) [Fintype n] [DecidableEq n]
    (z : UnitaryNormalDomain n) : Matrix n n ℂ :=
  (z.1 : Matrix n n ℂ) * (1 + z.2.1)

theorem continuous_unitaryNormalMap (n : Type*) [Fintype n] [DecidableEq n] :
    Continuous (unitaryNormalMap n) := by
  unfold unitaryNormalMap
  fun_prop

theorem injective_unitaryNormalMap (n : Type*) [Fintype n] [DecidableEq n] :
    Function.Injective (unitaryNormalMap n) := by
  intro z w he
  have h := (unitary_normal_eq_iff (z.1 : Matrix n n ℂ) (w.1 : Matrix n n ℂ)
    (z.2.1 : Matrix n n ℂ) (w.2.1 : Matrix n n ℂ)
    (Matrix.mem_unitaryGroup_iff'.mp z.1.property) (Matrix.mem_unitaryGroup_iff'.mp w.1.property)
    z.2.property.1 w.2.property.1 z.2.property.2 w.2.property.2).mp he
  apply Prod.ext
  · exact Subtype.ext h.1
  · exact Subtype.ext h.2

theorem isClosedEmbedding_unitaryNormalMap (n : Type*) [Fintype n] [DecidableEq n] :
    Topology.IsClosedEmbedding (unitaryNormalMap n) :=
  (continuous_unitaryNormalMap n).isClosedEmbedding (injective_unitaryNormalMap n)

theorem measurableEmbedding_unitaryNormalMap (n : Type*) [Fintype n] [DecidableEq n] :
    MeasurableEmbedding (unitaryNormalMap n) :=
  (isClosedEmbedding_unitaryNormalMap n).measurableEmbedding

end NLQCLean

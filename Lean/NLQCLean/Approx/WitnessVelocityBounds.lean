import NLQCLean.LinearAlgebra.TensorOperatorNorm
import NLQCLean.Rigidity.QuantitativeDifferential

/-!
# Six-block velocity bounds

The vector factors use their Euclidean norms and matrix
velocities use Frobenius norms. The block Euclidean norm is stated explicitly;
it is not the default max norm on the product parameter space.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

theorem sqNorm_eq_euclidean_norm_sq {ε : Type*} [Fintype ε] (z : ε → ℂ) :
    sqNorm z = ‖WithLp.toLp 2 z‖ ^ 2 := by
  simp [sqNorm, EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq]

section Insertion

variable {a b rA rB lA lB : Type*}
variable [Fintype a] [Fintype b] [Fintype rA] [Fintype rB] [Fintype lA] [Fintype lB]
variable [DecidableEq a] [DecidableEq b] [DecidableEq rA] [DecidableEq rB]
variable [DecidableEq lA] [DecidableEq lB]

omit [DecidableEq rA] [DecidableEq rB] in
theorem opNorm_insertResource_le (η : rA × rB → ℂ) :
    opNorm (insertResource a b η) ≤ ‖WithLp.toLp 2 η‖ := by
  apply opNorm_le_of_gram_scalar (norm_nonneg _)
  rw [insertResource_gram, vecInner_self, sqNorm_eq_euclidean_norm_sq, Complex.coe_smul]

omit [DecidableEq lA] in
theorem opNorm_tensorInsertionVelocity_le
    {η : rA × rB → ℂ} (hη : IsUnitVector η) (η' : rA × rB → ℂ)
    {CA : Matrix lA (a × rA) ℂ} {CB : Matrix lB (b × rB) ℂ}
    (hCA : IsIsometry CA) (hCB : IsIsometry CB)
    (CA' : Matrix lA (a × rA) ℂ) (CB' : Matrix lB (b × rB) ℂ) :
    opNorm (tensorInsertionVelocity η η' CA CA' CB CB') ≤
      opNorm CA' + opNorm CB' + ‖WithLp.toLp 2 η'‖ := by
  have h1 : opNorm (CA ⊗ₖ CB') ≤ opNorm CB' :=
    (opNorm_kronecker_le CA CB').trans (by
      simpa using mul_le_mul_of_nonneg_right hCA.opNorm_le_one (opNorm_nonneg CB'))
  have h2 : opNorm (CA' ⊗ₖ CB) ≤ opNorm CA' :=
    (opNorm_kronecker_le CA' CB).trans (by
      simpa using mul_le_mul_of_nonneg_left hCB.opNorm_le_one (opNorm_nonneg CA'))
  rw [tensorInsertionVelocity]
  calc
    _ ≤ opNorm ((CA ⊗ₖ CB' + CA' ⊗ₖ CB) * insertResource a b η) +
        opNorm ((CA ⊗ₖ CB) * insertResource a b η') := opNorm_add_le _ _
    _ ≤ opNorm (CA ⊗ₖ CB' + CA' ⊗ₖ CB) + opNorm (insertResource a b η') :=
      add_le_add (opNorm_mul_isometry_le _ (isIsometry_insertResource η hη))
        (opNorm_isometry_mul_le (hCA.kronecker hCB) _)
    _ ≤ (opNorm (CA ⊗ₖ CB') + opNorm (CA' ⊗ₖ CB)) + ‖WithLp.toLp 2 η'‖ :=
      add_le_add (opNorm_add_le _ _) (opNorm_insertResource_le η')
    _ ≤ _ := by linarith

end Insertion

theorem opNorm_encodedStateVelocity_le
    {a b rA rB kA kB mA mB : Type*}
    [Fintype a] [Fintype b] [Fintype rA] [Fintype rB]
    [Fintype kA] [Fintype kB] [Fintype mA] [Fintype mB]
    [DecidableEq a] [DecidableEq b] [DecidableEq rA] [DecidableEq rB]
    [DecidableEq kA] [DecidableEq kB] [DecidableEq mA] [DecidableEq mB]
    {η : rA × rB → ℂ} (hη : IsUnitVector η) (η' : rA × rB → ℂ)
    {VA : Matrix (kA × mA) (a × rA) ℂ} {VB : Matrix (kB × mB) (b × rB) ℂ}
    (hVA : IsIsometry VA) (hVB : IsIsometry VB)
    (VA' : Matrix (kA × mA) (a × rA) ℂ) (VB' : Matrix (kB × mB) (b × rB) ℂ) :
    opNorm (encodedStateVelocity η η' VA VA' VB VB') ≤
      opNorm VA' + opNorm VB' + ‖WithLp.toLp 2 η'‖ :=
  (opNorm_isometry_mul_le (isIsometry_exchangeMatrix kA mA kB mB) _).trans
    (opNorm_tensorInsertionVelocity_le hη η' hVA hVB VA' VB')

namespace ReverseBlocks

variable {d K : ℕ} {s : ReverseShape d K}

/-- The six Euclidean block norms, before combining them by an l2 sum. -/
noncomputable def blockNorms (v : ReverseBlocks s) : Fin 6 → ℝ :=
  ![‖WithLp.toLp 2 v.1‖, ‖WithLp.toLp 2 v.2.1‖, ‖v.2.2.1‖, ‖v.2.2.2.1‖,
    ‖v.2.2.2.2.1‖, ‖v.2.2.2.2.2‖]

noncomputable def euclideanNorm (v : ReverseBlocks s) : ℝ :=
  Real.sqrt (∑ i, blockNorms v i ^ 2)

theorem euclideanNorm_nonneg (v : ReverseBlocks s) : 0 ≤ euclideanNorm v := Real.sqrt_nonneg _

/-- Undo the matrix normalization by sqrt(number of columns), leaving the
two resource vectors unchanged. This is a real-linear map on all blocks. -/
noncomputable def rescaleBlocks : ReverseBlocks s →ₗ[ℝ] ReverseBlocks s where
  toFun v := (v.1, v.2.1, Real.sqrt (d * s.r : ℝ) • v.2.2.1,
    Real.sqrt (d * s.r : ℝ) • v.2.2.2.1, Real.sqrt (d * K : ℝ) • v.2.2.2.2.1,
    Real.sqrt (d * K : ℝ) • v.2.2.2.2.2)
  map_add' u v := by ext <;> simp [smul_add]
  map_smul' c v := by ext <;> simp [smul_comm c]

theorem IsValid.opNorm_forwardVelocity_le {x : ReverseBlocks s} (hx : IsValid x) (v : ReverseBlocks s) :
    opNorm (forwardVelocity x v) ≤ ‖v.2.2.1‖ + ‖v.2.2.2.1‖ + ‖WithLp.toLp 2 v.1‖ := by
  have hE := s.isIsometry_rowEmbeddingA.kronecker s.isIsometry_rowEmbeddingB
  exact ((opNorm_isometry_mul_le hE _).trans
    (opNorm_encodedStateVelocity_le hx.1 v.1 hx.2.2.1 hx.2.2.2.1 v.2.2.1 v.2.2.2.1)).trans
      (add_le_add (add_le_add (opNorm_le_frobNorm _) (opNorm_le_frobNorm _)) le_rfl)

theorem IsValid.opNorm_reverseVelocity_le {x : ReverseBlocks s} (hx : IsValid x) (v : ReverseBlocks s) :
    opNorm (reverseVelocity x v) ≤ ‖v.2.2.2.2.1‖ + ‖v.2.2.2.2.2‖ + ‖WithLp.toLp 2 v.2.1‖ :=
  (opNorm_tensorInsertionVelocity_le hx.2.1 v.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2
    v.2.2.2.2.1 v.2.2.2.2.2).trans
    (add_le_add (add_le_add (opNorm_le_frobNorm _) (opNorm_le_frobNorm _)) le_rfl)

/-- The exact Cauchy--Schwarz coefficient for the six rescaled blocks.
The estimate holds for all velocities, before imposing tangent constraints. -/
theorem IsValid.rescaled_speed_le {x : ReverseBlocks s} (hx : IsValid x) (v : ReverseBlocks s) :
    opNorm (forwardVelocity x (rescaleBlocks v)) + opNorm (reverseVelocity x (rescaleBlocks v)) ≤
      Real.sqrt (2 * (d * s.r : ℝ) + 2 * (d * K : ℝ) + 2) * euclideanNorm v := by
  let weights : Fin 6 → ℝ := ![1, 1, Real.sqrt (d * s.r : ℝ), Real.sqrt (d * s.r : ℝ),
    Real.sqrt (d * K : ℝ), Real.sqrt (d * K : ℝ)]
  have hb : opNorm (forwardVelocity x (rescaleBlocks v)) +
      opNorm (reverseVelocity x (rescaleBlocks v)) ≤ ∑ i, weights i * blockNorms v i := by
    have h := add_le_add (hx.opNorm_forwardVelocity_le (rescaleBlocks v))
      (hx.opNorm_reverseVelocity_le (rescaleBlocks v))
    simpa [rescaleBlocks, blockNorms, weights, Fin.sum_univ_succ, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), add_comm, add_left_comm, add_assoc] using h
  have hw : ∑ i, weights i ^ 2 = 2 * (d * s.r : ℝ) + 2 * (d * K : ℝ) + 2 := by
    simp [weights, Fin.sum_univ_succ, mul_pow, Real.sq_sqrt (Nat.cast_nonneg d),
      Real.sq_sqrt (Nat.cast_nonneg s.r), Real.sq_sqrt (Nat.cast_nonneg K)]
    ring
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ weights (blockNorms v)
  rw [hw] at h
  exact hb.trans h

/-- C:speed with the source coefficient sqrt(5 d K). -/
theorem IsValid.rescaled_speed_le_sqrt_five {x : ReverseBlocks s} (hx : IsValid x)
    (hd : 2 ≤ d) (v : ReverseBlocks s) :
    opNorm (forwardVelocity x (rescaleBlocks v)) + opNorm (reverseVelocity x (rescaleBlocks v)) ≤
      Real.sqrt (5 * d * K : ℝ) * euclideanNorm v := by
  have hr : s.r ≤ K := (Nat.le_mul_of_pos_right _ s.messageA_pos).trans
    ((Nat.le_mul_of_pos_right _ s.messageB_pos).trans s.footprint)
  have hK : 1 ≤ K := s.resource_pos.trans_le hr
  have hrR : (s.r : ℝ) ≤ K := by exact_mod_cast hr
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hc : 2 * (d * s.r : ℝ) + 2 * (d * K : ℝ) + 2 ≤ 5 * d * K := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ (d : ℝ)) (sub_nonneg.mpr hrR)]
  exact (hx.rescaled_speed_le v).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hc) (euclideanNorm_nonneg v))

end ReverseBlocks

end NLQCLean

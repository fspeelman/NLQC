import NLQCLean.Approx.ReverseWitness
import NLQCLean.Rigidity.ForwardExactDifferential
import NLQCLean.Rigidity.CrossGram

/-!
# Quantitative cross-Gram differential

All velocities below are algebraic velocities
at a single point satisfying the linearized constraints. The residual uses
Frobenius leakage and operator norms of the velocities, with no dimension
loss from swapping those two norms.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

/-- The derivative of the polynomial cross-Gram product, in its two velocities. -/
def crossGramVelocity {m n : Type*} [Fintype m]
    (A B A' B' : Matrix m n ℂ) : Matrix n n ℂ := B'ᴴ * A + Bᴴ * A'

/-- The existing residual equals the two explicit leakage products of TP6.1. -/
theorem crossGramResidual_eq_leakage {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A B A' B' : Matrix m n ℂ) :
    crossGramResidual A B A' B' =
      B'ᴴ * (A - B * (Bᴴ * A)) + (B - A * (Bᴴ * A)ᴴ)ᴴ * A' := by
  simp only [crossGramResidual, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_assoc]

/-- TP6.1 holds at a single linearized isometry constraint, without a path. -/
theorem crossGramVelocity_decomposition {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A B A' B' : Matrix m n ℂ) (hB' : Bᴴ * B' + B'ᴴ * B = 0) :
    crossGramVelocity A B A' B' =
      -(Bᴴ * B') * (Bᴴ * A) + (Bᴴ * A) * (Aᴴ * A') + crossGramResidual A B A' B' := by
  have hz : (Bᴴ * B' + B'ᴴ * B) * (Bᴴ * A) = 0 := by rw [hB', Matrix.zero_mul]
  simp only [crossGramVelocity, crossGramResidual_eq_leakage, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.neg_mul, Matrix.add_mul, Matrix.mul_assoc] at hz ⊢
  linear_combination (norm := module) hz

/-- TP6.2: Frobenius leakage multiplies operator-norm velocities. -/
theorem norm_crossGramResidual_le_of_frob_leakage {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A B A' B' : Matrix m n ℂ) {L : ℝ}
    (hleft : ‖A - B * (Bᴴ * A)‖ ≤ L) (hright : ‖B - A * (Bᴴ * A)ᴴ‖ ≤ L) :
    ‖crossGramResidual A B A' B'‖ ≤ L * (opNorm A' + opNorm B') := by
  rw [crossGramResidual_eq_leakage]
  calc
    _ ≤ ‖B'ᴴ * (A - B * (Bᴴ * A))‖ + ‖(B - A * (Bᴴ * A)ᴴ)ᴴ * A'‖ := norm_add_le _ _
    _ ≤ opNorm B' * ‖A - B * (Bᴴ * A)‖ + ‖B - A * (Bᴴ * A)ᴴ‖ * opNorm A' := by
      simpa only [opNorm_conjTranspose, Matrix.frobenius_norm_conjTranspose] using
        add_le_add (frobNorm_mul_le B'ᴴ (A - B * (Bᴴ * A)))
          (frobNorm_mul_le' (B - A * (Bᴴ * A)ᴴ)ᴴ A')
    _ ≤ opNorm B' * L + L * opNorm A' :=
      add_le_add (mul_le_mul_of_nonneg_left hleft (opNorm_nonneg _))
        (mul_le_mul_of_nonneg_right hright (opNorm_nonneg _))
    _ = _ := by ring

/-- The single scalar leakage constraint controls both Frobenius residuals. -/
theorem norm_crossGramResidual_le_of_defect_sq {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A B A' B' : Matrix m n ℂ) (hA : IsIsometry A) (hB : IsIsometry B)
    {L : ℝ} (hL : 0 ≤ L) (hdef : (Fintype.card n : ℝ) - ‖Bᴴ * A‖ ^ 2 ≤ L ^ 2) :
    ‖crossGramResidual A B A' B'‖ ≤ L * (opNorm A' + opNorm B') := by
  obtain ⟨hl, hr⟩ := crossGram_residuals_sq A B hA hB
  apply norm_crossGramResidual_le_of_frob_leakage
  · exact (sq_le_sq₀ (norm_nonneg _) hL).mp (hl.le.trans hdef)
  · exact (sq_le_sq₀ (norm_nonneg _) hL).mp (hr.le.trans hdef)

section TensorInsertion

variable {a b rA rB lA lB : Type*}
variable [Fintype a] [Fintype b] [Fintype rA] [Fintype rB] [Fintype lA] [Fintype lB]
variable [DecidableEq a] [DecidableEq b] [DecidableEq rA] [DecidableEq rB]
variable [DecidableEq lA] [DecidableEq lB]

/-- Product-rule velocity of two local isometries acting on an inserted vector. -/
def tensorInsertionVelocity (η η' : rA × rB → ℂ)
    (CA CA' : Matrix lA (a × rA) ℂ) (CB CB' : Matrix lB (b × rB) ℂ) :
    Matrix (lA × lB) (a × b) ℂ :=
  (CA ⊗ₖ CB' + CA' ⊗ₖ CB) * insertResource a b η +
    (CA ⊗ₖ CB) * insertResource a b η'

omit [DecidableEq lA] in
theorem tensorInsertion_conjTranspose_mul_velocity
    (η η' : rA × rB → ℂ)
    (CA CA' : Matrix lA (a × rA) ℂ) (CB CB' : Matrix lB (b × rB) ℂ)
    (hCA : IsIsometry CA) (hCB : IsIsometry CB) :
    ((CA ⊗ₖ CB) * insertResource a b η)ᴴ * tensorInsertionVelocity η η' CA CA' CB CB' =
      (insertResource a b η)ᴴ *
        (ampLeft (a × rA) (b × rB) (CAᴴ * CA') + ampRight (a × rA) (b × rB) (CBᴴ * CB')) *
          insertResource a b η + vecInner η η' • (1 : Matrix (a × b) (a × b) ℂ) := by
  have k1 : (CA ⊗ₖ CB)ᴴ * (CA ⊗ₖ CB') = ampRight (a × rA) (b × rB) (CBᴴ * CB') := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      hCA.conjTranspose_mul_self, ampRight_apply]
  have k2 : (CA ⊗ₖ CB)ᴴ * (CA' ⊗ₖ CB) = ampLeft (a × rA) (b × rB) (CAᴴ * CA') := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      hCB.conjTranspose_mul_self, ampLeft_apply]
  have k3 : (CA ⊗ₖ CB)ᴴ * (CA ⊗ₖ CB) = 1 := (hCA.kronecker hCB).conjTranspose_mul_self
  rw [tensorInsertionVelocity, Matrix.conjTranspose_mul, Matrix.mul_add]
  congr 1
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((CA ⊗ₖ CB)ᴴ), Matrix.mul_add, k1, k2,
      add_comm, ← Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((CA ⊗ₖ CB)ᴴ), k3, Matrix.one_mul,
      insertResource_gram]

omit [DecidableEq lA] in
/-- D:local for the completed reverse matrices; no physical decoder is needed. -/
theorem tensorInsertion_velocity_mem_localSkew
    (η η' : rA × rB → ℂ)
    (CA CA' : Matrix lA (a × rA) ℂ) (CB CB' : Matrix lB (b × rB) ℂ)
    (hCA : IsIsometry CA) (hCB : IsIsometry CB)
    (hCA' : CAᴴ * CA' + CA'ᴴ * CA = 0) (hCB' : CBᴴ * CB' + CB'ᴴ * CB = 0)
    (hη' : (vecInner η η').re = 0) :
    ((CA ⊗ₖ CB) * insertResource a b η)ᴴ * tensorInsertionVelocity η η' CA CA' CB CB'
      ∈ localSkew a b := by
  rw [tensorInsertion_conjTranspose_mul_velocity η η' CA CA' CB CB' hCA hCB]
  exact compressed_pair_add_scalar_mem_localSkew η
    (conjTranspose_mul_skew hCA') (conjTranspose_mul_skew hCB') hη'

end TensorInsertion

namespace ReverseBlocks

variable {d K : ℕ} {s : ReverseShape d K}

/-- The six linearized constraints, at one point and for arbitrary velocities. -/
def IsTangent (x v : ReverseBlocks s) : Prop :=
  (vecInner x.1 v.1).re = 0 ∧ (vecInner x.2.1 v.2.1).re = 0 ∧
    x.2.2.1ᴴ * v.2.2.1 + v.2.2.1ᴴ * x.2.2.1 = 0 ∧
    x.2.2.2.1ᴴ * v.2.2.2.1 + v.2.2.2.1ᴴ * x.2.2.2.1 = 0 ∧
    x.2.2.2.2.1ᴴ * v.2.2.2.2.1 + v.2.2.2.2.1ᴴ * x.2.2.2.2.1 = 0 ∧
    x.2.2.2.2.2ᴴ * v.2.2.2.2.2 + v.2.2.2.2.2ᴴ * x.2.2.2.2.2 = 0

noncomputable def forwardVelocity (x v : ReverseBlocks s) :
    Matrix (Fin (2 * d * K) × Fin (2 * d * K)) (Fin d × Fin d) ℂ :=
  (s.rowEmbeddingA ⊗ₖ s.rowEmbeddingB) *
    encodedStateVelocity x.1 v.1 x.2.2.1 v.2.2.1 x.2.2.2.1 v.2.2.2.1

def reverseVelocity (x v : ReverseBlocks s) :
    Matrix (Fin (2 * d * K) × Fin (2 * d * K)) (Fin d × Fin d) ℂ :=
  tensorInsertionVelocity x.2.1 v.2.1 x.2.2.2.2.1 v.2.2.2.2.1 x.2.2.2.2.2 v.2.2.2.2.2

noncomputable def overlapVelocity (x v : ReverseBlocks s) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  crossGramVelocity (forward x) (reverse x) (forwardVelocity x v) (reverseVelocity x v)

theorem IsValid.forward_generator_mem_localSkew {x v : ReverseBlocks s}
    (hx : IsValid x) (hv : IsTangent x v) :
    (forward x)ᴴ * forwardVelocity x v ∈ localSkew (Fin d) (Fin d) := by
  have hE := s.isIsometry_rowEmbeddingA.kronecker s.isIsometry_rowEmbeddingB
  rw [forward, forwardVelocity, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (s.rowEmbeddingA ⊗ₖ s.rowEmbeddingB)ᴴ,
    hE.conjTranspose_mul_self, Matrix.one_mul]
  exact encodedState_velocity_mem_localSkew hx.2.2.1 hx.2.2.2.1 x.1 v.1
    hv.2.2.1 hv.2.2.2.1 hv.1

theorem IsValid.reverse_generator_mem_localSkew {x v : ReverseBlocks s}
    (hx : IsValid x) (hv : IsTangent x v) :
    (reverse x)ᴴ * reverseVelocity x v ∈ localSkew (Fin d) (Fin d) :=
  tensorInsertion_velocity_mem_localSkew x.2.1 v.2.1
    x.2.2.2.2.1 v.2.2.2.2.1 x.2.2.2.2.2 v.2.2.2.2.2
    hx.2.2.2.2.1 hx.2.2.2.2.2 hv.2.2.2.2.1 hv.2.2.2.2.2 hv.2.1

/-- TP6.1--TP6.2 and D:local for every valid six-block witness. The rank
estimate and identification with the ambient derivative are subsequent steps. -/
theorem IsValid.local_velocity_decomposition {x v : ReverseBlocks s}
    (hx : IsValid x) (hv : IsTangent x v) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdef : (d : ℝ) ^ 2 - ‖overlap x‖ ^ 2 ≤ (d : ℝ) ^ 2 * δ ^ 2) :
    ∃ a b : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      a ∈ localSkew (Fin d) (Fin d) ∧ b ∈ localSkew (Fin d) (Fin d) ∧
      overlapVelocity x v = -b * overlap x + overlap x * a +
        crossGramResidual (forward x) (reverse x) (forwardVelocity x v) (reverseVelocity x v) ∧
      ‖crossGramResidual (forward x) (reverse x) (forwardVelocity x v) (reverseVelocity x v)‖ ≤
        ((d : ℝ) * δ) * (opNorm (forwardVelocity x v) + opNorm (reverseVelocity x v)) := by
  have ha := hx.forward_generator_mem_localSkew hv
  have hb := hx.reverse_generator_mem_localSkew hv
  refine ⟨(forward x)ᴴ * forwardVelocity x v, (reverse x)ᴴ * reverseVelocity x v, ha, hb, ?_, ?_⟩
  · apply crossGramVelocity_decomposition
    have h := mem_skewHermitian_iff.mp (localSkew_le_skewHermitian hb)
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at h
    rw [h, add_neg_cancel]
  · apply norm_crossGramResidual_le_of_defect_sq _ _ _ _
      hx.isIsometry_forward hx.isIsometry_reverse (mul_nonneg (Nat.cast_nonneg _) hδ)
    have hD : (Fintype.card (Fin d × Fin d) : ℝ) = (d : ℝ) ^ 2 := by simp [pow_two]
    simpa only [hD, mul_pow, overlap] using hdef

end ReverseBlocks

end NLQCLean

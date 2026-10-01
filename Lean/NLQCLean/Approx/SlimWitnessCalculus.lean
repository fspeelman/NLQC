import NLQCLean.Approx.SlimReverseWitness
import NLQCLean.Rigidity.ReverseWitnessCalculus
import NLQCLean.Approx.WitnessVelocityBounds

/-!
# Ambient calculus of slim reverse witnesses

The algebraic velocities of the slim forward and
reverse maps and of their overlap are the Fréchet derivatives on the whole slim block
space; the local-generator memberships hold at every valid point and tangent velocity. The
block Euclidean norm and the column-count rescaling use `d r` for the encoders and `d s`
(with `s = frozenSupport d K`) for the completed reverse isometries.
-/

namespace NLQCLean
namespace SlimReverseBlocks

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

variable {d K : ℕ} {s : SlimReverseShape d K}

/-- The six linearized constraints, at one point and for arbitrary velocities. -/
def IsTangent (x v : SlimReverseBlocks s) : Prop :=
  (vecInner x.1 v.1).re = 0 ∧ (vecInner x.2.1 v.2.1).re = 0 ∧
    x.2.2.1ᴴ * v.2.2.1 + v.2.2.1ᴴ * x.2.2.1 = 0 ∧
    x.2.2.2.1ᴴ * v.2.2.2.1 + v.2.2.2.1ᴴ * x.2.2.2.1 = 0 ∧
    x.2.2.2.2.1ᴴ * v.2.2.2.2.1 + v.2.2.2.2.1ᴴ * x.2.2.2.2.1 = 0 ∧
    x.2.2.2.2.2ᴴ * v.2.2.2.2.2 + v.2.2.2.2.2ᴴ * x.2.2.2.2.2 = 0

noncomputable def forwardVelocity (x v : SlimReverseBlocks s) :
    Matrix (Fin (d * (K + frozenSupport d K)) × Fin (d * (K + frozenSupport d K)))
      (Fin d × Fin d) ℂ :=
  (s.rowEmbeddingA ⊗ₖ s.rowEmbeddingB) *
    encodedStateVelocity x.1 v.1 x.2.2.1 v.2.2.1 x.2.2.2.1 v.2.2.2.1

def reverseVelocity (x v : SlimReverseBlocks s) :
    Matrix (Fin (d * (K + frozenSupport d K)) × Fin (d * (K + frozenSupport d K)))
      (Fin d × Fin d) ℂ :=
  tensorInsertionVelocity x.2.1 v.2.1 x.2.2.2.2.1 v.2.2.2.2.1 x.2.2.2.2.2 v.2.2.2.2.2

noncomputable def overlapVelocity (x v : SlimReverseBlocks s) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  crossGramVelocity (forward x) (reverse x) (forwardVelocity x v) (reverseVelocity x v)

theorem IsValid.forward_generator_mem_localSkew {x v : SlimReverseBlocks s}
    (hx : IsValid x) (hv : IsTangent x v) :
    (forward x)ᴴ * forwardVelocity x v ∈ localSkew (Fin d) (Fin d) := by
  have hE := s.isIsometry_rowEmbeddingA.kronecker s.isIsometry_rowEmbeddingB
  rw [forward, forwardVelocity, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (s.rowEmbeddingA ⊗ₖ s.rowEmbeddingB)ᴴ,
    hE.conjTranspose_mul_self, Matrix.one_mul]
  exact encodedState_velocity_mem_localSkew hx.2.2.1 hx.2.2.2.1 x.1 v.1
    hv.2.2.1 hv.2.2.2.1 hv.1

theorem IsValid.reverse_generator_mem_localSkew {x v : SlimReverseBlocks s}
    (hx : IsValid x) (hv : IsTangent x v) :
    (reverse x)ᴴ * reverseVelocity x v ∈ localSkew (Fin d) (Fin d) :=
  tensorInsertion_velocity_mem_localSkew x.2.1 v.2.1
    x.2.2.2.2.1 v.2.2.2.2.1 x.2.2.2.2.2 v.2.2.2.2.2
    hx.2.2.2.2.1 hx.2.2.2.2.2 hv.2.2.2.2.1 hv.2.2.2.2.2 hv.2.1

theorem contDiff_forward : ContDiff ℝ ∞ (forward : SlimReverseBlocks s → _) := by
  have hη : ContDiff ℝ ∞ (fun x : SlimReverseBlocks s => x.1) := contDiff_fst
  have hVA : ContDiff ℝ ∞ (fun x : SlimReverseBlocks s => x.2.2.1) := contDiff_fst.snd'.snd'
  have hVB : ContDiff ℝ ∞ (fun x : SlimReverseBlocks s => x.2.2.2.1) :=
    contDiff_fst.snd'.snd'.snd'
  exact ContDiff.matrixMul contDiff_const (ContDiff.matrixMul contDiff_const
    (ContDiff.matrixMul (ContDiff.matrixKronecker hVA hVB) (ContDiff.insertResource hη)))

theorem contDiff_reverse : ContDiff ℝ ∞ (reverse : SlimReverseBlocks s → _) := by
  have hg : ContDiff ℝ ∞ (fun x : SlimReverseBlocks s => x.2.1) := contDiff_fst.snd'
  have hTA : ContDiff ℝ ∞ (fun x : SlimReverseBlocks s => x.2.2.2.2.1) :=
    contDiff_fst.snd'.snd'.snd'.snd'
  have hTB : ContDiff ℝ ∞ (fun x : SlimReverseBlocks s => x.2.2.2.2.2) :=
    contDiff_snd.snd'.snd'.snd'.snd'
  exact ContDiff.matrixMul (ContDiff.matrixKronecker hTA hTB) (ContDiff.insertResource hg)

theorem contDiff_overlap : ContDiff ℝ ∞ (overlap : SlimReverseBlocks s → _) :=
  ContDiff.matrixMul (ContDiff.matrixConjTranspose contDiff_reverse) contDiff_forward

theorem hasDerivAt_forward_line (x v : SlimReverseBlocks s) :
    HasDerivAt (fun t : ℝ => forward (x + t • v)) (forwardVelocity x v) 0 := by
  have hl := hasDerivAt_line x v
  have hE := hasDerivAt_encodedState hl.fst hl.snd.snd.fst hl.snd.snd.snd.fst
  have h := HasDerivAt.matrixMul
    (hasDerivAt_const (0 : ℝ) (s.rowEmbeddingA ⊗ₖ s.rowEmbeddingB)) hE
  simpa only [forward, forwardVelocity, zero_smul, add_zero, Matrix.zero_mul] using h

theorem hasDerivAt_reverse_line (x v : SlimReverseBlocks s) :
    HasDerivAt (fun t : ℝ => reverse (x + t • v)) (reverseVelocity x v) 0 := by
  have hl := hasDerivAt_line x v
  have hT := HasDerivAt.matrixKronecker hl.snd.snd.snd.snd.fst hl.snd.snd.snd.snd.snd
  have hg := HasDerivAt.insertResource (ιA := Fin d) (ιB := Fin d) hl.snd.fst
  have h := HasDerivAt.matrixMul hT hg
  simpa only [reverse, reverseVelocity, tensorInsertionVelocity, zero_smul, add_zero,
    add_comm] using h

theorem hasDerivAt_overlap_line (x v : SlimReverseBlocks s) :
    HasDerivAt (fun t : ℝ => overlap (x + t • v)) (overlapVelocity x v) 0 := by
  have h := HasDerivAt.matrixMul
    (HasDerivAt.matrixConjTranspose (hasDerivAt_reverse_line x v)) (hasDerivAt_forward_line x v)
  simpa only [overlap, overlapVelocity, crossGramVelocity, zero_smul, add_zero, add_comm] using h

theorem fderiv_forward_apply (x v : SlimReverseBlocks s) :
    fderiv ℝ forward x v = forwardVelocity x v :=
  fderiv_apply_eq_of_hasDerivAt_line (contDiff_forward.differentiable (by simp)).differentiableAt
    (hasDerivAt_forward_line x v)

theorem fderiv_reverse_apply (x v : SlimReverseBlocks s) :
    fderiv ℝ reverse x v = reverseVelocity x v :=
  fderiv_apply_eq_of_hasDerivAt_line (contDiff_reverse.differentiable (by simp)).differentiableAt
    (hasDerivAt_reverse_line x v)

theorem fderiv_overlap_apply (x v : SlimReverseBlocks s) :
    fderiv ℝ overlap x v = overlapVelocity x v :=
  fderiv_apply_eq_of_hasDerivAt_line (contDiff_overlap.differentiable (by simp)).differentiableAt
    (hasDerivAt_overlap_line x v)

/-- The six Euclidean block norms, before combining them by an l2 sum. -/
noncomputable def blockNorms (v : SlimReverseBlocks s) : Fin 6 → ℝ :=
  ![‖WithLp.toLp 2 v.1‖, ‖WithLp.toLp 2 v.2.1‖, ‖v.2.2.1‖, ‖v.2.2.2.1‖,
    ‖v.2.2.2.2.1‖, ‖v.2.2.2.2.2‖]

noncomputable def euclideanNorm (v : SlimReverseBlocks s) : ℝ :=
  Real.sqrt (∑ i, blockNorms v i ^ 2)

theorem euclideanNorm_nonneg (v : SlimReverseBlocks s) : 0 ≤ euclideanNorm v :=
  Real.sqrt_nonneg _

theorem blockNorms_nonneg (v : SlimReverseBlocks s) (i : Fin 6) : 0 ≤ blockNorms v i := by
  fin_cases i <;> simp [blockNorms]

/-- Undo the normalization by `√(number of columns)`: `√(d r)` on the encoders and `√(d s)` on
the completed reverse isometries; the two vectors are unchanged. -/
noncomputable def rescaleBlocks : SlimReverseBlocks s →ₗ[ℝ] SlimReverseBlocks s where
  toFun v := (v.1, v.2.1, Real.sqrt (d * s.1.r : ℝ) • v.2.2.1,
    Real.sqrt (d * s.1.r : ℝ) • v.2.2.2.1,
    Real.sqrt (d * frozenSupport d K : ℝ) • v.2.2.2.2.1,
    Real.sqrt (d * frozenSupport d K : ℝ) • v.2.2.2.2.2)
  map_add' u v := by ext <;> simp [smul_add]
  map_smul' c v := by ext <;> simp [smul_comm c]

theorem pos_d_mul_r (hd : 0 < d) : 0 < (d * s.1.r : ℝ) :=
  mul_pos (by exact_mod_cast hd) (by exact_mod_cast s.1.resource_pos)

theorem pos_d_mul_support (s : SlimReverseShape d K) (hd : 0 < d) :
    0 < (d * frozenSupport d K : ℝ) :=
  mul_pos (by exact_mod_cast hd)
    (by exact_mod_cast one_le_frozenSupport hd s.1.one_le_budget)

end SlimReverseBlocks
end NLQCLean

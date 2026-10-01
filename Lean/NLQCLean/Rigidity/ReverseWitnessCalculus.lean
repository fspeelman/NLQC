import NLQCLean.Rigidity.QuantitativeDifferential
import NLQCLean.Rigidity.ForwardWitnessCalculus
import NLQCLean.Geometry.CubicProjection

/-!
# Ambient calculus of the reverse witness

The algebraic velocities of A, B, and H are their actual
Fréchet derivatives on the entire six-block space. No constraint, physical
parameter choice, or curve realization hypothesis is needed for these facts.
-/

namespace NLQCLean
namespace ReverseBlocks

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

variable {d K : ℕ} {s : ReverseShape d K}

theorem contDiff_forward : ContDiff ℝ ∞ (forward : ReverseBlocks s → _) := by
  have hη : ContDiff ℝ ∞ (fun x : ReverseBlocks s => x.1) := contDiff_fst
  have hVA : ContDiff ℝ ∞ (fun x : ReverseBlocks s => x.2.2.1) := contDiff_fst.snd'.snd'
  have hVB : ContDiff ℝ ∞ (fun x : ReverseBlocks s => x.2.2.2.1) := contDiff_fst.snd'.snd'.snd'
  exact ContDiff.matrixMul contDiff_const (ContDiff.matrixMul contDiff_const
    (ContDiff.matrixMul (ContDiff.matrixKronecker hVA hVB) (ContDiff.insertResource hη)))

theorem contDiff_reverse : ContDiff ℝ ∞ (reverse : ReverseBlocks s → _) := by
  have hg : ContDiff ℝ ∞ (fun x : ReverseBlocks s => x.2.1) := contDiff_fst.snd'
  have hTA : ContDiff ℝ ∞ (fun x : ReverseBlocks s => x.2.2.2.2.1) :=
    contDiff_fst.snd'.snd'.snd'.snd'
  have hTB : ContDiff ℝ ∞ (fun x : ReverseBlocks s => x.2.2.2.2.2) :=
    contDiff_snd.snd'.snd'.snd'.snd'
  exact ContDiff.matrixMul (ContDiff.matrixKronecker hTA hTB) (ContDiff.insertResource hg)

theorem contDiff_overlap : ContDiff ℝ ∞ (overlap : ReverseBlocks s → _) :=
  ContDiff.matrixMul (ContDiff.matrixConjTranspose contDiff_reverse) contDiff_forward

theorem hasDerivAt_forward_line (x v : ReverseBlocks s) :
    HasDerivAt (fun t : ℝ => forward (x + t • v)) (forwardVelocity x v) 0 := by
  have hl := hasDerivAt_line x v
  have hE := hasDerivAt_encodedState hl.fst hl.snd.snd.fst hl.snd.snd.snd.fst
  have h := HasDerivAt.matrixMul
    (hasDerivAt_const (0 : ℝ) (s.rowEmbeddingA ⊗ₖ s.rowEmbeddingB)) hE
  simpa only [forward, forwardVelocity, zero_smul, add_zero, Matrix.zero_mul] using h

theorem hasDerivAt_reverse_line (x v : ReverseBlocks s) :
    HasDerivAt (fun t : ℝ => reverse (x + t • v)) (reverseVelocity x v) 0 := by
  have hl := hasDerivAt_line x v
  have hT := HasDerivAt.matrixKronecker hl.snd.snd.snd.snd.fst hl.snd.snd.snd.snd.snd
  have hg := HasDerivAt.insertResource (ιA := Fin d) (ιB := Fin d) hl.snd.fst
  have h := HasDerivAt.matrixMul hT hg
  simpa only [reverse, reverseVelocity, tensorInsertionVelocity, zero_smul, add_zero,
    add_comm] using h

theorem hasDerivAt_overlap_line (x v : ReverseBlocks s) :
    HasDerivAt (fun t : ℝ => overlap (x + t • v)) (overlapVelocity x v) 0 := by
  have h := HasDerivAt.matrixMul
    (HasDerivAt.matrixConjTranspose (hasDerivAt_reverse_line x v)) (hasDerivAt_forward_line x v)
  simpa only [overlap, overlapVelocity, crossGramVelocity, zero_smul, add_zero, add_comm] using h

/-- The forward algebraic velocity is the full ambient Fréchet derivative. -/
theorem fderiv_forward_apply (x v : ReverseBlocks s) :
    fderiv ℝ forward x v = forwardVelocity x v :=
  fderiv_apply_eq_of_hasDerivAt_line (contDiff_forward.differentiable (by simp)).differentiableAt
    (hasDerivAt_forward_line x v)

theorem fderiv_reverse_apply (x v : ReverseBlocks s) :
    fderiv ℝ reverse x v = reverseVelocity x v :=
  fderiv_apply_eq_of_hasDerivAt_line (contDiff_reverse.differentiable (by simp)).differentiableAt
    (hasDerivAt_reverse_line x v)

theorem fderiv_overlap_apply (x v : ReverseBlocks s) :
    fderiv ℝ overlap x v = overlapVelocity x v :=
  fderiv_apply_eq_of_hasDerivAt_line (contDiff_overlap.differentiable (by simp)).differentiableAt
    (hasDerivAt_overlap_line x v)

end ReverseBlocks
end NLQCLean

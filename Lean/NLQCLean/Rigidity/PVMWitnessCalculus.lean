import NLQCLean.Approx.PVMReverseWitness
import NLQCLean.Rigidity.QuantitativeDifferential
import NLQCLean.Rigidity.ReverseWitnessCalculus

/-!
# Ambient calculus of compressed PVM reverse witnesses

The algebraic velocities of the compressed
forward witness, flagged reverse witness, and their cross-Gram overlap are
the actual Frechet derivatives on the full six-block ambient space.  These
statements impose no sphere or isometry constraints.

The dependent compressed flag is exposed as an explicit real linear map.
Its fixed-label tests and dependent casts therefore contribute no derivative;
only the selected garbage coordinate moves.
-/

namespace NLQCLean
namespace PVMReverseBlocks

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

variable {d K : ℕ} {s : PVMReverseShape d K}

/-- The compressed dependent flag as a real linear map.  The label tests and
casts are fixed by the row and column indices. -/
def compressedFlagLinearMap :
    ((i : Fin d × Fin d) → Fin (s.2.rank i) × Fin (s.2.rank i) → ℂ) →ₗ[ℝ]
      Matrix (s.Support × s.Support) (Fin d × Fin d) ℂ where
  toFun := compressedFlag
  map_add' g h := by
    classical
    ext p i
    simp only [compressedFlag, Pi.add_apply, Matrix.add_apply]
    split_ifs <;> simp
  map_smul' c g := by
    classical
    ext p i
    simp only [compressedFlag, Pi.smul_apply, Matrix.smul_apply]
    split_ifs <;> simp

@[simp] theorem compressedFlagLinearMap_apply
    (g : (i : Fin d × Fin d) → Fin (s.2.rank i) × Fin (s.2.rank i) → ℂ) :
    compressedFlagLinearMap (s := s) g = compressedFlag g := rfl

/-- The six linearized constraints at a compressed PVM witness.  Each
garbage vector has its own sphere tangent condition. -/
def IsTangent (x v : PVMReverseBlocks s) : Prop :=
  (vecInner x.1 v.1).re = 0 ∧
    (∀ i, (vecInner (x.2.1 i) (v.2.1 i)).re = 0) ∧
    x.2.2.1ᴴ * v.2.2.1 + v.2.2.1ᴴ * x.2.2.1 = 0 ∧
    x.2.2.2.1ᴴ * v.2.2.2.1 + v.2.2.2.1ᴴ * x.2.2.2.1 = 0 ∧
    x.2.2.2.2.1ᴴ * v.2.2.2.2.1 + v.2.2.2.2.1ᴴ * x.2.2.2.2.1 = 0 ∧
    x.2.2.2.2.2ᴴ * v.2.2.2.2.2 + v.2.2.2.2.2ᴴ * x.2.2.2.2.2 = 0

/-- Product-rule velocity of the padded encoded state. -/
noncomputable def forwardVelocity (x v : PVMReverseBlocks s) :
    Matrix (Fin (d * K + s.supportSize) × Fin (d * K + s.supportSize))
      (Fin d × Fin d) ℂ :=
  (s.rowEmbeddingA ⊗ₖ s.rowEmbeddingB) *
    encodedStateVelocity x.1 v.1 x.2.2.1 v.2.2.1 x.2.2.2.1 v.2.2.2.1

/-- Product-rule velocity of the two reverse maps applied to the compressed
flagged garbage family. -/
def reverseVelocity (x v : PVMReverseBlocks s) :
    Matrix (Fin (d * K + s.supportSize) × Fin (d * K + s.supportSize))
      (Fin d × Fin d) ℂ :=
  (x.2.2.2.2.1 ⊗ₖ v.2.2.2.2.2 + v.2.2.2.2.1 ⊗ₖ x.2.2.2.2.2) *
      compressedFlag x.2.1 +
    (x.2.2.2.2.1 ⊗ₖ x.2.2.2.2.2) * compressedFlag v.2.1

/-- Product-rule velocity of the cross-Gram overlap. -/
noncomputable def overlapVelocity (x v : PVMReverseBlocks s) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  crossGramVelocity (forward x) (reverse x) (forwardVelocity x v) (reverseVelocity x v)

theorem contDiff_compressedFlag : ContDiff ℝ ∞
    (compressedFlag :
      ((i : Fin d × Fin d) → Fin (s.2.rank i) × Fin (s.2.rank i) → ℂ) →
        Matrix (s.Support × s.Support) (Fin d × Fin d) ℂ) :=
  ContDiff.linearMapFD (compressedFlagLinearMap (s := s)) contDiff_id

theorem contDiff_forward : ContDiff ℝ ∞ (forward : PVMReverseBlocks s → _) := by
  have hη : ContDiff ℝ ∞ (fun x : PVMReverseBlocks s => x.1) := contDiff_fst
  have hVA : ContDiff ℝ ∞ (fun x : PVMReverseBlocks s => x.2.2.1) :=
    contDiff_fst.snd'.snd'
  have hVB : ContDiff ℝ ∞ (fun x : PVMReverseBlocks s => x.2.2.2.1) :=
    contDiff_fst.snd'.snd'.snd'
  exact ContDiff.matrixMul contDiff_const (ContDiff.matrixMul contDiff_const
    (ContDiff.matrixMul (ContDiff.matrixKronecker hVA hVB) (ContDiff.insertResource hη)))

theorem contDiff_reverse : ContDiff ℝ ∞ (reverse : PVMReverseBlocks s → _) := by
  have hg : ContDiff ℝ ∞ (fun x : PVMReverseBlocks s => x.2.1) := contDiff_fst.snd'
  have hflag : ContDiff ℝ ∞ (fun x : PVMReverseBlocks s => compressedFlag x.2.1) :=
    contDiff_compressedFlag.comp hg
  have hTA : ContDiff ℝ ∞ (fun x : PVMReverseBlocks s => x.2.2.2.2.1) :=
    contDiff_fst.snd'.snd'.snd'.snd'
  have hTB : ContDiff ℝ ∞ (fun x : PVMReverseBlocks s => x.2.2.2.2.2) :=
    contDiff_snd.snd'.snd'.snd'.snd'
  exact ContDiff.matrixMul (ContDiff.matrixKronecker hTA hTB) hflag

theorem contDiff_overlap : ContDiff ℝ ∞ (overlap : PVMReverseBlocks s → _) :=
  ContDiff.matrixMul (ContDiff.matrixConjTranspose contDiff_reverse) contDiff_forward

theorem hasDerivAt_compressedFlag
    {g : ℝ → (i : Fin d × Fin d) → Fin (s.2.rank i) × Fin (s.2.rank i) → ℂ}
    {g' : (i : Fin d × Fin d) → Fin (s.2.rank i) × Fin (s.2.rank i) → ℂ}
    {t : ℝ} (h : HasDerivAt g g' t) :
    HasDerivAt (fun u => compressedFlag (g u)) (compressedFlag g') t :=
  HasDerivAt.ofLinearMap (compressedFlagLinearMap (s := s)) h

theorem hasDerivAt_compressedFlag_line
    (g h : (i : Fin d × Fin d) → Fin (s.2.rank i) × Fin (s.2.rank i) → ℂ) :
    HasDerivAt (fun t : ℝ => compressedFlag (g + t • h)) (compressedFlag h) 0 := by
  exact hasDerivAt_compressedFlag (s := s) (hasDerivAt_line g h)

theorem fderiv_compressedFlag_apply
    (g h : (i : Fin d × Fin d) → Fin (s.2.rank i) × Fin (s.2.rank i) → ℂ) :
    fderiv ℝ compressedFlag g h = compressedFlag h :=
  fderiv_apply_eq_of_hasDerivAt_line
    (contDiff_compressedFlag.differentiable (by simp)).differentiableAt
    (hasDerivAt_compressedFlag_line g h)

theorem hasDerivAt_forward_line (x v : PVMReverseBlocks s) :
    HasDerivAt (fun t : ℝ => forward (x + t • v)) (forwardVelocity x v) 0 := by
  have hl := hasDerivAt_line x v
  have hE := hasDerivAt_encodedState hl.fst hl.snd.snd.fst hl.snd.snd.snd.fst
  have h := HasDerivAt.matrixMul
    (hasDerivAt_const (0 : ℝ) (s.rowEmbeddingA ⊗ₖ s.rowEmbeddingB)) hE
  simpa only [forward, forwardVelocity, zero_smul, add_zero, Matrix.zero_mul] using h

theorem hasDerivAt_reverse_line (x v : PVMReverseBlocks s) :
    HasDerivAt (fun t : ℝ => reverse (x + t • v)) (reverseVelocity x v) 0 := by
  have hl := hasDerivAt_line x v
  have hT := HasDerivAt.matrixKronecker hl.snd.snd.snd.snd.fst
    hl.snd.snd.snd.snd.snd
  have hg := hasDerivAt_compressedFlag (s := s) hl.snd.fst
  have h := HasDerivAt.matrixMul hT hg
  simpa only [reverse, reverseVelocity, zero_smul, add_zero, add_comm] using h

theorem hasDerivAt_overlap_line (x v : PVMReverseBlocks s) :
    HasDerivAt (fun t : ℝ => overlap (x + t • v)) (overlapVelocity x v) 0 := by
  have h := HasDerivAt.matrixMul
    (HasDerivAt.matrixConjTranspose (hasDerivAt_reverse_line x v))
    (hasDerivAt_forward_line x v)
  simpa only [overlap, overlapVelocity, crossGramVelocity, zero_smul, add_zero, add_comm] using h

/-- The forward algebraic velocity is the full ambient Frechet derivative. -/
theorem fderiv_forward_apply (x v : PVMReverseBlocks s) :
    fderiv ℝ forward x v = forwardVelocity x v :=
  fderiv_apply_eq_of_hasDerivAt_line
    (contDiff_forward.differentiable (by simp)).differentiableAt
    (hasDerivAt_forward_line x v)

theorem fderiv_reverse_apply (x v : PVMReverseBlocks s) :
    fderiv ℝ reverse x v = reverseVelocity x v :=
  fderiv_apply_eq_of_hasDerivAt_line
    (contDiff_reverse.differentiable (by simp)).differentiableAt
    (hasDerivAt_reverse_line x v)

theorem fderiv_overlap_apply (x v : PVMReverseBlocks s) :
    fderiv ℝ overlap x v = overlapVelocity x v :=
  fderiv_apply_eq_of_hasDerivAt_line
    (contDiff_overlap.differentiable (by simp)).differentiableAt
    (hasDerivAt_overlap_line x v)

/-- Tangency of the resource and encoder blocks makes the forward generator
an input-local skew-Hermitian motion. -/
theorem IsValid.forward_generator_mem_localSkew {x v : PVMReverseBlocks s}
    (hx : IsValid x) (hv : IsTangent x v) :
    (forward x)ᴴ * forwardVelocity x v ∈ localSkew (Fin d) (Fin d) := by
  have hE := s.isIsometry_rowEmbeddingA.kronecker s.isIsometry_rowEmbeddingB
  rw [forward, forwardVelocity, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (s.rowEmbeddingA ⊗ₖ s.rowEmbeddingB)ᴴ,
    hE.conjTranspose_mul_self, Matrix.one_mul]
  exact encodedState_velocity_mem_localSkew hx.2.2.1 hx.2.2.2.1 x.1 v.1
    hv.2.2.1 hv.2.2.2.1 hv.1

end PVMReverseBlocks
end NLQCLean

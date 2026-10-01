import NLQCLean.Approx.PVMBlockNormalization
import NLQCLean.Geometry.MatrixPolynomialDegree

/-!
# Polynomial degrees of PVM reverse witnesses

The garbage block is a dependent family with one unit-vector
constraint for every ordered PVM label.  Its compressed flag is nevertheless
linear entrywise, so the PVM forward and reverse witnesses retain the same
degree-three and degree-six bounds as the common six-block construction.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

namespace PVMReverseBlocks

variable {a d K D : ℕ} {s : PVMReverseShape d K}

/-- One degree bound for every coordinate of the six independent PVM blocks.
The second block is dependent: both its label and its within-support pair are
quantified separately. -/
def PolynomialDegreeLE (D : ℕ) (f : RealEuclidean a → PVMReverseBlocks s) : Prop :=
  (∀ i, ComplexPolynomialDegreeLE D (fun x ↦ (f x).1 i)) ∧
  (∀ i j, ComplexPolynomialDegreeLE D (fun x ↦ (f x).2.1 i j)) ∧
  MatrixPolynomialDegreeLE D (fun x ↦ (f x).2.2.1) ∧
  MatrixPolynomialDegreeLE D (fun x ↦ (f x).2.2.2.1) ∧
  MatrixPolynomialDegreeLE D (fun x ↦ (f x).2.2.2.2.1) ∧
  MatrixPolynomialDegreeLE D (fun x ↦ (f x).2.2.2.2.2)

namespace PolynomialDegreeLE

variable {f : RealEuclidean a → PVMReverseBlocks s}

theorem linear (L : RealEuclidean a →ₗ[ℝ] PVMReverseBlocks s) :
    PolynomialDegreeLE 1 (fun x ↦ L x) := by
  let Lη := (LinearMap.fst ℝ _ _).comp L
  let L1 := (LinearMap.snd ℝ _ _).comp L
  let Lg := (LinearMap.fst ℝ _ _).comp L1
  let L2 := (LinearMap.snd ℝ _ _).comp L1
  let LA := (LinearMap.fst ℝ _ _).comp L2
  let L3 := (LinearMap.snd ℝ _ _).comp L2
  let LB := (LinearMap.fst ℝ _ _).comp L3
  let L4 := (LinearMap.snd ℝ _ _).comp L3
  let LTA := (LinearMap.fst ℝ _ _).comp L4
  let LTB := (LinearMap.snd ℝ _ _).comp L4
  exact ⟨fun i ↦ ComplexPolynomialDegreeLE.linear ((LinearMap.proj i).comp Lη),
    fun i j ↦ ComplexPolynomialDegreeLE.linear
      ((LinearMap.proj j).comp ((LinearMap.proj i).comp Lg)),
    MatrixPolynomialDegreeLE.linear LA, MatrixPolynomialDegreeLE.linear LB,
    MatrixPolynomialDegreeLE.linear LTA, MatrixPolynomialDegreeLE.linear LTB⟩

theorem rescale (hf : PolynomialDegreeLE D f) :
    PolynomialDegreeLE D (fun x ↦ rescaleBlocks (f x)) :=
  ⟨hf.1, fun i j ↦ (hf.2.1 i j).real_smul _,
    hf.2.2.1.real_smul _, hf.2.2.2.1.real_smul _,
    hf.2.2.2.2.1.real_smul _, hf.2.2.2.2.2.real_smul _⟩

/-- Every entry of the compressed dependent flag is either one fixed garbage
coordinate or zero, so compression does not increase polynomial degree. -/
theorem compressedFlag
    {g : RealEuclidean a →
      (i : Fin d × Fin d) → Fin (s.2.rank i) × Fin (s.2.rank i) → ℂ}
    (hg : ∀ i j, ComplexPolynomialDegreeLE D (fun x ↦ g x i j)) :
    MatrixPolynomialDegreeLE D (fun x ↦ NLQCLean.compressedFlag (g x)) := by
  classical
  intro p i
  simp only [NLQCLean.compressedFlag]
  split
  next hA =>
    split
    next hB => exact hg i _
    next => exact (ComplexPolynomialDegreeLE.const 0).mono (Nat.zero_le D)
  next => exact (ComplexPolynomialDegreeLE.const 0).mono (Nat.zero_le D)

theorem forward (hf : PolynomialDegreeLE D f) :
    MatrixPolynomialDegreeLE (3 * D) (fun x ↦ PVMReverseBlocks.forward (f x)) := by
  have hJ := polynomialDegree_insertResource (ιA := Fin d) (ιB := Fin d) hf.1
  have h := (MatrixPolynomialDegreeLE.const (s.rowEmbeddingA ⊗ₖ s.rowEmbeddingB)).mul
    ((MatrixPolynomialDegreeLE.const
      (exchangeMatrix (Fin (d * s.1.r * s.1.mA)) (Fin s.1.mA)
        (Fin (d * s.1.r * s.1.mB)) (Fin s.1.mB))).mul
      ((hf.2.2.1.kronecker hf.2.2.2.1).mul hJ))
  exact h.mono (by omega)

theorem reverse (hf : PolynomialDegreeLE D f) :
    MatrixPolynomialDegreeLE (3 * D) (fun x ↦ PVMReverseBlocks.reverse (f x)) := by
  exact ((hf.2.2.2.2.1.kronecker hf.2.2.2.2.2).mul
    (compressedFlag hf.2.1)).mono (by omega)

theorem overlap (hf : PolynomialDegreeLE D f) :
    MatrixPolynomialDegreeLE (6 * D) (fun x ↦ PVMReverseBlocks.overlap (f x)) :=
  (hf.reverse.conjTranspose.mul hf.forward).mono (by omega)

end PolynomialDegreeLE

end PVMReverseBlocks

/-- One polynomial equality simultaneously enforces all individual PVM
garbage-vector normalizations. -/
noncomputable def pvmGarbageDefect {i : Type*} [Fintype i]
    {gdim : i → Type*} [∀ j, Fintype (gdim j)]
    (n : ℝ) (g : ∀ j, gdim j → ℂ) : ℝ :=
  ∑ j, (n * sqNorm (g j) - 1) ^ 2

theorem pvmGarbageDefect_eq_zero_iff {i : Type*} [Fintype i]
    {gdim : i → Type*} [∀ j, Fintype (gdim j)]
    (n : ℝ) (hn : 0 ≤ n) (g : ∀ j, gdim j → ℂ) :
    pvmGarbageDefect n g = 0 ↔
      ∀ j, IsUnitVector (Real.sqrt n • g j) := by
  classical
  rw [pvmGarbageDefect,
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ sq_nonneg _)]
  simp only [Finset.mem_univ, true_implies, sq_eq_zero_iff, sub_eq_zero]
  apply forall_congr'
  intro j
  have hscale : sqNorm (Real.sqrt n • g j) = n * sqNorm (g j) := by
    simp only [sqNorm, Pi.smul_apply, Complex.real_smul, Complex.normSq_mul,
      Complex.normSq_ofReal, Real.mul_self_sqrt hn, ← Finset.mul_sum]
  rw [← hscale]
  rfl

theorem polynomialDegree_pvmGarbageDefect
    {a D : ℕ} {i : Type*} [Fintype i]
    {gdim : i → Type*} [∀ j, Fintype (gdim j)]
    {f : RealEuclidean a → ∀ j, gdim j → ℂ}
    (hf : ∀ i j, ComplexPolynomialDegreeLE D (fun x ↦ f x i j)) (n : ℝ) :
    RealPolynomialDegreeLE (4 * D) (fun x ↦ pvmGarbageDefect n (f x)) := by
  classical
  apply RealPolynomialDegreeLE.sum Finset.univ
  intro i _
  have hs := (((polynomialDegree_sqNorm (hf i)).const_mul n).sub
    (RealPolynomialDegreeLE.const 1)).sq
  exact hs.mono (by omega)

end NLQCLean

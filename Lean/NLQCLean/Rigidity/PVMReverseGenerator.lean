import NLQCLean.Rigidity.PVMWitnessCalculus

/-!
# Diagonal output generator of a compressed PVM reverse witness

The two reverse-isometry velocities compress through
the duplicated outcome flag to a diagonal skew-Hermitian matrix.  The
independent garbage velocity contributes a second diagonal skew-Hermitian
cross-Gram term.  The proof is algebraic at one point and assumes no curve
realizing the tangent velocity.
-/

namespace NLQCLean

open Matrix
open scoped Matrix.Norms.Frobenius Kronecker

section DependentFlagCompression

variable {δ : Type*} [Fintype δ] [DecidableEq δ]
variable {s : δ → ℕ}

/-- Compression of an Alice-local matrix through two dependent flagged
families is diagonal.  Equality of Bob's support indices forces equality of
the duplicated outcome labels. -/
theorem compressedFlag_compression_mem_diagonal
    (g h : ∀ i, Fin (s i) × Fin (s i) → ℂ)
    (Z : Matrix (FlagSupport s) (FlagSupport s) ℂ) :
    (compressedFlag g)ᴴ * ampLeft (FlagSupport s) (FlagSupport s) Z * compressedFlag h
      ∈ diagonalSubmodule δ := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun p' _ => ?_
  rcases eq_or_ne p'.2.1 j with hj | hj
  · rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun p _ => ?_
    rcases eq_or_ne p.2 p'.2 with h2 | h2
    · have hne : ¬(p.2.1 = i) := by
        rw [h2, hj]
        exact fun hji => hij hji.symm
      simp [compressedFlag, hne]
    · simp [ampLeft_apply, Matrix.kroneckerMap_apply, h2]
  · simp [compressedFlag, hj]

/-- The Bob-local mirror of `compressedFlag_compression_mem_diagonal`. -/
theorem compressedFlag_compression_right_mem_diagonal
    (g h : ∀ i, Fin (s i) × Fin (s i) → ℂ)
    (Z : Matrix (FlagSupport s) (FlagSupport s) ℂ) :
    (compressedFlag g)ᴴ * ampRight (FlagSupport s) (FlagSupport s) Z * compressedFlag h
      ∈ diagonalSubmodule δ := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun p' _ => ?_
  rcases eq_or_ne p'.1.1 j with hj | hj
  · rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun p _ => ?_
    rcases eq_or_ne p.1 p'.1 with h1 | h1
    · have hne : ¬(p.1.1 = i) := by
        rw [h1, hj]
        exact fun hji => hij hji.symm
      simp [compressedFlag, hne]
    · simp [ampRight_apply, Matrix.kroneckerMap_apply, h1]
  · simp [compressedFlag, hj]

/-- Cross-Grams of two dependent compressed flags are diagonal, even when
the two garbage families differ. -/
theorem compressedFlag_conjTranspose_mul_mem_diagonal
    (g h : ∀ i, Fin (s i) × Fin (s i) → ℂ) :
    (compressedFlag g)ᴴ * compressedFlag h ∈ diagonalSubmodule δ := by
  have hz := compressedFlag_compression_mem_diagonal g h
    (1 : Matrix (FlagSupport s) (FlagSupport s) ℂ)
  simpa only [ampLeft_apply, Matrix.one_kronecker_one, Matrix.mul_one] using hz

/-- A diagonal entry of the compressed-flag cross-Gram is the inner product
of the corresponding dependent garbage vectors. -/
theorem compressedFlag_conjTranspose_mul_apply_self
    (g h : ∀ i, Fin (s i) × Fin (s i) → ℂ) (i : δ) :
    ((compressedFlag g)ᴴ * compressedFlag h) i i = vecInner (g i) (h i) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Fintype.sum_sigma, Matrix.conjTranspose_apply]
  simp [compressedFlag, vecInner, Fintype.sum_prod_type]

/-- Pointwise sphere tangency makes the compressed-flag cross-Gram
skew-Hermitian as well as diagonal. -/
theorem compressedFlag_conjTranspose_mul_mem_diagSkew
    (g h : ∀ i, Fin (s i) × Fin (s i) → ℂ)
    (hh : ∀ i, (vecInner (g i) (h i)).re = 0) :
    (compressedFlag g)ᴴ * compressedFlag h ∈ diagSkew δ := by
  rw [mem_diagSkew_iff]
  refine ⟨compressedFlag_conjTranspose_mul_mem_diagonal g h, ?_⟩
  apply conjTranspose_mul_skew
  ext i j
  rw [Matrix.add_apply, Matrix.zero_apply]
  by_cases hij : i = j
  · subst j
    rw [compressedFlag_conjTranspose_mul_apply_self,
      compressedFlag_conjTranspose_mul_apply_self]
    have hc : vecInner (h i) (g i) = star (vecInner (g i) (h i)) := by
      rw [vecInner, vecInner, star_sum]
      exact Finset.sum_congr rfl fun e _ => by rw [star_mul', star_star]; ring
    rw [hc]
    apply Complex.ext <;> simp [hh i]
  · have hgh := compressedFlag_conjTranspose_mul_mem_diagonal g h i j hij
    have hhg := compressedFlag_conjTranspose_mul_mem_diagonal h g i j hij
    rw [hgh, hhg, add_zero]

/-- Compression of a local skew-Hermitian generator through the dependent
duplicated flag lies in the diagonal skew-Hermitian algebra. -/
theorem compressedFlag_local_compression_mem_diagSkew
    (g : ∀ i, Fin (s i) × Fin (s i) → ℂ)
    {XA XB : Matrix (FlagSupport s) (FlagSupport s) ℂ}
    (hXA : XAᴴ = -XA) (hXB : XBᴴ = -XB) :
    (compressedFlag g)ᴴ *
        (ampLeft (FlagSupport s) (FlagSupport s) XA +
          ampRight (FlagSupport s) (FlagSupport s) XB) * compressedFlag g
      ∈ diagSkew δ := by
  rw [mem_diagSkew_iff]
  constructor
  · rw [Matrix.mul_add, Matrix.add_mul]
    exact Submodule.add_mem _
      (compressedFlag_compression_mem_diagonal g g XA)
      (compressedFlag_compression_right_mem_diagonal g g XB)
  · have hlocal :
        ampLeft (FlagSupport s) (FlagSupport s) XA +
            ampRight (FlagSupport s) (FlagSupport s) XB
          ∈ localSkew (FlagSupport s) (FlagSupport s) :=
      mem_localSkew_iff.mpr ⟨XA, hXA, XB, hXB, rfl⟩
    have hskew := mem_skewHermitian_iff.mp (localSkew_le_skewHermitian hlocal)
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hskew,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]

end DependentFlagCompression

namespace PVMReverseBlocks

variable {d K : ℕ} {s : PVMReverseShape d K}

/-- The exact generator identity for the compressed PVM reverse witness. -/
theorem compressedFlag_tensor_conjTranspose_mul_velocity
    (g g' : (i : Fin d × Fin d) → Fin (s.2.rank i) × Fin (s.2.rank i) → ℂ)
    (TA TA' TB TB' : Matrix (Fin (d * K + s.supportSize)) s.Support ℂ)
    (hTA : IsIsometry TA) (hTB : IsIsometry TB) :
    ((TA ⊗ₖ TB) * compressedFlag g)ᴴ *
        ((TA ⊗ₖ TB' + TA' ⊗ₖ TB) * compressedFlag g +
          (TA ⊗ₖ TB) * compressedFlag g') =
      (compressedFlag g)ᴴ *
          (ampLeft s.Support s.Support (TAᴴ * TA') +
            ampRight s.Support s.Support (TBᴴ * TB')) * compressedFlag g +
        (compressedFlag g)ᴴ * compressedFlag g' := by
  have k1 : (TA ⊗ₖ TB)ᴴ * (TA ⊗ₖ TB') =
      ampRight s.Support s.Support (TBᴴ * TB') := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      hTA.conjTranspose_mul_self, ampRight_apply]
  have k2 : (TA ⊗ₖ TB)ᴴ * (TA' ⊗ₖ TB) =
      ampLeft s.Support s.Support (TAᴴ * TA') := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      hTB.conjTranspose_mul_self, ampLeft_apply]
  have k3 : (TA ⊗ₖ TB)ᴴ * (TA ⊗ₖ TB) = 1 :=
    (hTA.kronecker hTB).conjTranspose_mul_self
  rw [Matrix.conjTranspose_mul, Matrix.mul_add]
  congr 1
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((TA ⊗ₖ TB)ᴴ), Matrix.mul_add,
      k1, k2, add_comm, ← Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((TA ⊗ₖ TB)ᴴ), k3, Matrix.one_mul]

/-- PP5's output-side generator: every algebraic tangent velocity of a valid
compressed PVM reverse witness produces a diagonal skew-Hermitian motion. -/
theorem IsValid.reverse_generator_mem_diagSkew {x v : PVMReverseBlocks s}
    (hx : IsValid x) (hv : IsTangent x v) :
    (reverse x)ᴴ * reverseVelocity x v ∈ diagSkew (Fin d × Fin d) := by
  rw [reverse, reverseVelocity,
    compressedFlag_tensor_conjTranspose_mul_velocity x.2.1 v.2.1
      x.2.2.2.2.1 v.2.2.2.2.1 x.2.2.2.2.2 v.2.2.2.2.2
      hx.2.2.2.2.1 hx.2.2.2.2.2]
  exact Submodule.add_mem _
    (compressedFlag_local_compression_mem_diagSkew x.2.1
      (conjTranspose_mul_skew hv.2.2.2.2.1)
      (conjTranspose_mul_skew hv.2.2.2.2.2))
    (compressedFlag_conjTranspose_mul_mem_diagSkew x.2.1 v.2.1 hv.2.1)

end PVMReverseBlocks
end NLQCLean

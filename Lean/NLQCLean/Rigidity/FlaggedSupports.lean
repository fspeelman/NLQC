import NLQCLean.Approx.PVMBlockSpectrum
import NLQCLean.Models.ForwardCompression

/-!
# Flagged direct sums of Schmidt supports

The construction compresses each normalized flagged environment vector on its own
Schmidt support.  The outcome flag makes these supports orthogonal even when
their images in the original environment overlap.  This file packages the
dependent direct sum, its local inclusions, and the compressed flag isometry.
-/

namespace NLQCLean

open Matrix
open scoped Kronecker

/-- The direct sum of outcome-dependent finite support spaces. -/
abbrev FlagSupport {δ : Type*} (s : δ → ℕ) := Σ i, Fin (s i)

section Basic

variable {δ ε εA εB : Type*} [Fintype δ] [Fintype ε]
variable [Fintype εA] [Fintype εB]
variable [DecidableEq δ] [DecidableEq ε] [DecidableEq εA] [DecidableEq εB]
variable {s : δ → ℕ}

/-- The local flagged inclusion.  The block at outcome `i` is the chosen
support isometry `J i`; different blocks are orthogonal because their physical
rows carry different outcome flags. -/
def localFlagInclusion (J : ∀ i, Matrix ε (Fin (s i)) ℂ) :
    Matrix (δ × ε) (FlagSupport s) ℂ :=
  (Matrix.blockDiagonal' J).submatrix (Equiv.sigmaEquivProd δ ε).symm id

omit [Fintype δ] [Fintype ε] [DecidableEq ε] in
@[simp] theorem localFlagInclusion_apply
    (J : ∀ i, Matrix ε (Fin (s i)) ℂ) (p : δ × ε) (q : FlagSupport s) :
    localFlagInclusion J p q =
      if h : p.1 = q.1 then J p.1 p.2 (cast (congrArg (fun i ↦ Fin (s i)) h.symm) q.2)
      else 0 := by
  rfl

omit [DecidableEq δ] in
/-- The exact dimension of the dependent flagged direct sum. -/
@[simp] theorem card_flagSupport (s : δ → ℕ) :
    Fintype.card (FlagSupport s) = ∑ i, s i := by
  simp

omit [DecidableEq ε] in
/-- A block diagonal family of isometries remains isometric after its
constant row Sigma type is identified with the physical product type. -/
theorem isIsometry_localFlagInclusion (J : ∀ i, Matrix ε (Fin (s i)) ℂ)
    (hJ : ∀ i, IsIsometry (J i)) : IsIsometry (localFlagInclusion J) := by
  have hblock : IsIsometry (Matrix.blockDiagonal' J) := by
    rw [IsIsometry, Matrix.blockDiagonal'_conjTranspose,
      ← Matrix.blockDiagonal'_mul]
    have hblocks : (fun i ↦ (J i)ᴴ * J i) =
        (1 : ∀ i, Matrix (Fin (s i)) (Fin (s i)) ℂ) := by
      funext i
      exact hJ i
    rw [hblocks, Matrix.blockDiagonal'_one]
  exact hblock.submatrix_equiv (Equiv.sigmaEquivProd δ ε).symm
    (Equiv.refl (FlagSupport s))

/-- The compressed flagged vector.  Column `i` contains `g i` in the
`(i,i)` support block and vanishes on every other pair of summands. -/
def compressedFlag (g : ∀ i, Fin (s i) × Fin (s i) → ℂ) :
    Matrix (FlagSupport s × FlagSupport s) δ ℂ :=
  fun p i =>
    if hA : p.1.1 = i then
      if hB : p.2.1 = i then
        g i
          (cast (congrArg (fun j ↦ Fin (s j)) hA) p.1.2,
            cast (congrArg (fun j ↦ Fin (s j)) hB) p.2.2)
      else 0
    else 0

omit [Fintype δ] in
@[simp] theorem compressedFlag_same (g : ∀ i, Fin (s i) × Fin (s i) → ℂ)
    (i : δ) (a b : Fin (s i)) :
    compressedFlag g (⟨i, a⟩, ⟨i, b⟩) i = g i (a, b) := by
  simp [compressedFlag]

set_option maxHeartbeats 800000 in
theorem isIsometry_compressedFlag (g : ∀ i, Fin (s i) × Fin (s i) → ℂ)
    (hg : ∀ i, IsUnitVector (g i)) : IsIsometry (compressedFlag g) := by
  rw [IsIsometry]
  ext i j
  rw [Matrix.mul_apply]
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.one_apply_eq]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_sigma, Matrix.conjTranspose_apply]
    have hunit := (isUnitVector_iff_sum (g i)).mp (hg i)
    rw [Fintype.sum_prod_type] at hunit
    simpa [compressedFlag, mul_comm] using hunit
  · rw [Matrix.one_apply_ne hij]
    refine Finset.sum_eq_zero fun p _ ↦ ?_
    rcases p with ⟨⟨k, a⟩, ⟨l, b⟩⟩
    simp only [Matrix.conjTranspose_apply, compressedFlag]
    by_cases hki : k = i
    · by_cases hli : l = i
      · subst k
        subst l
        simp [hij]
      · simp [hki, hli]
    · simp [hki]

omit [Fintype εA] [Fintype εB] [DecidableEq εA] [DecidableEq εB] in
/-- The two local flagged inclusions wire the compressed flag back to the
original flagged family exactly. -/
theorem localFlagInclusion_kronecker_mul_compressedFlag
    (JA : ∀ i, Matrix εA (Fin (s i)) ℂ)
    (JB : ∀ i, Matrix εB (Fin (s i)) ℂ)
    (g : ∀ i, Fin (s i) × Fin (s i) → ℂ)
    (u : δ → εA × εB → ℂ)
    (hu : ∀ i, u i = (JA i ⊗ₖ JB i) *ᵥ g i) :
    (localFlagInclusion JA ⊗ₖ localFlagInclusion JB) * compressedFlag g =
      flagIsometry u := by
  ext ⟨⟨i, a⟩, ⟨j, b⟩⟩ k
  by_cases hik : i = k
  · subst i
    by_cases hjk : j = k
    · subst j
      have hcoeff := congrFun (hu k) (a, b)
      simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
        Fintype.sum_prod_type] at hcoeff
      simpa [Matrix.mul_apply, Matrix.kroneckerMap_apply, localFlagInclusion,
        compressedFlag, flagIsometry_apply, Fintype.sum_prod_type,
        Fintype.sum_sigma] using hcoeff.symm
    · simp [Matrix.mul_apply, Matrix.kroneckerMap_apply, localFlagInclusion,
        compressedFlag, flagIsometry_apply, Fintype.sum_prod_type,
        Fintype.sum_sigma, Matrix.blockDiagonal'_apply, hjk]
  · simp [Matrix.mul_apply, Matrix.kroneckerMap_apply, localFlagInclusion,
      compressedFlag, flagIsometry_apply, Fintype.sum_prod_type,
      Fintype.sum_sigma, Matrix.blockDiagonal'_apply, hik]

end Basic

section SchmidtFamily

variable {δ εA εB : Type*} [Fintype δ] [Fintype εA] [Fintype εB]
variable [DecidableEq δ] [DecidableEq εA] [DecidableEq εB]

/-- A normalized bipartite vector has positive Schmidt rank. -/
theorem IsUnitVector.schmidtRank_pos {v : εA × εB → ℂ} (hv : IsUnitVector v) :
    0 < schmidtRank v := by
  obtain ⟨JA, JB, g, hJA, hJB, hg, hv⟩ :=
    exists_resource_support_factorization v hv
  have hcard := hg.card_pos
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  exact Nat.pos_of_mul_pos_left hcard

/-- Simultaneously choose the exact Schmidt supports of a finite family of
normalized flagged vectors.  The returned direct-sum inclusions and compressed
flag are isometries, and their product is literally `flagIsometry u`. -/
theorem exists_flagged_support_factorization
    (u : δ → εA × εB → ℂ) (hu : ∀ i, IsUnitVector (u i)) :
    ∃ JA : ∀ i, Matrix εA (Fin (schmidtRank (u i))) ℂ,
      ∃ JB : ∀ i, Matrix εB (Fin (schmidtRank (u i))) ℂ,
        ∃ g : ∀ i, Fin (schmidtRank (u i)) × Fin (schmidtRank (u i)) → ℂ,
          (∀ i, IsIsometry (JA i)) ∧
          (∀ i, IsIsometry (JB i)) ∧
          (∀ i, IsUnitVector (g i)) ∧
          (∀ i, u i = (JA i ⊗ₖ JB i) *ᵥ g i) ∧
          IsIsometry (localFlagInclusion JA) ∧
          IsIsometry (localFlagInclusion JB) ∧
          IsIsometry (compressedFlag g) ∧
          (localFlagInclusion JA ⊗ₖ localFlagInclusion JB) * compressedFlag g =
            flagIsometry u := by
  choose JA JB g hJA hJB hg hfac using
    fun i ↦ exists_resource_support_factorization (u i) (hu i)
  refine ⟨JA, JB, g, hJA, hJB, hg, hfac,
    isIsometry_localFlagInclusion JA hJA,
    isIsometry_localFlagInclusion JB hJB,
    isIsometry_compressedFlag g hg, ?_⟩
  exact localFlagInclusion_kronecker_mul_compressedFlag JA JB g u hfac

omit [Fintype εA] [DecidableEq δ] [DecidableEq εA] [DecidableEq εB] in
/-- The rank-sum bound is exactly the physical dimension bound for the
dependent flagged support. -/
theorem card_flagSupport_schmidtRank_le (u : δ → εA × εB → ℂ) {K : ℕ}
    (hK : ∑ i, schmidtRank (u i) ≤ K + Fintype.card δ) :
    Fintype.card (FlagSupport fun i ↦ schmidtRank (u i)) ≤
      K + Fintype.card δ := by
  simpa using hK

end SchmidtFamily

end NLQCLean
